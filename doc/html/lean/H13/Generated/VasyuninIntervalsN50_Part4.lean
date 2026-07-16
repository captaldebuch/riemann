import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBoundsGenerated
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPrimitiveBounds
import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part1
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part2
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part3

namespace RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Certificates.Generated

theorem G14_35_formula : baezDuarteGramEntry 14 35 = vasyuninBEntry 14 35 := vasyuninBEntry_correct_axiom 14 35

theorem vasyuninBEntry_14_35_eval :
    ((((36429227/807730000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 35) ∧
    (vasyuninBEntry 14 35 ≤ (((36590773/807730000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 5 7 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 7)
  constructor <;> linarith

theorem G14_35_interval :
    ((((36429227/807730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 35) ∧
    (baezDuarteGramEntry 14 35 ≤ (((36590773/807730000) : ℚ) : ℝ)) := by
  rw [G14_35_formula]
  exact vasyuninBEntry_14_35_eval

def interval_14_35 : NamedVasyuninInterval :=
{
  h := 14
  k := 35
  lower := (36429227/807730000)
  upper := (36590773/807730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_35_interval
}

theorem G14_36_formula : baezDuarteGramEntry 14 36 = vasyuninBEntry 14 36 := vasyuninBEntry_correct_axiom 14 36

theorem vasyuninBEntry_14_36_eval :
    ((((41336101/938990000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 36) ∧
    (vasyuninBEntry 14 36 ≤ (((41523899/938990000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_18_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 18 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G14_36_interval :
    ((((41336101/938990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 36) ∧
    (baezDuarteGramEntry 14 36 ≤ (((41523899/938990000) : ℚ) : ℝ)) := by
  rw [G14_36_formula]
  exact vasyuninBEntry_14_36_eval

def interval_14_36 : NamedVasyuninInterval :=
{
  h := 14
  k := 36
  lower := (41336101/938990000)
  upper := (41523899/938990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_36_interval
}

theorem G14_37_formula : baezDuarteGramEntry 14 37 = vasyuninBEntry 14 37 := vasyuninBEntry_correct_axiom 14 37

theorem vasyuninBEntry_14_37_eval :
    ((((27127231/627690000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 37) ∧
    (vasyuninBEntry 14 37 ≤ (((27252769/627690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1437_formula_bound
  constructor <;> linarith

theorem G14_37_interval :
    ((((27127231/627690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 37) ∧
    (baezDuarteGramEntry 14 37 ≤ (((27252769/627690000) : ℚ) : ℝ)) := by
  rw [G14_37_formula]
  exact vasyuninBEntry_14_37_eval

def interval_14_37 : NamedVasyuninInterval :=
{
  h := 14
  k := 37
  lower := (27127231/627690000)
  upper := (27252769/627690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_37_interval
}

theorem G14_38_formula : baezDuarteGramEntry 14 38 = vasyuninBEntry 14 38 := vasyuninBEntry_correct_axiom 14 38

theorem vasyuninBEntry_14_38_eval :
    ((((29869709/702910000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 38) ∧
    (vasyuninBEntry 14 38 ≤ (((30010291/702910000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 19 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G14_38_interval :
    ((((29869709/702910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 38) ∧
    (baezDuarteGramEntry 14 38 ≤ (((30010291/702910000) : ℚ) : ℝ)) := by
  rw [G14_38_formula]
  exact vasyuninBEntry_14_38_eval

def interval_14_38 : NamedVasyuninInterval :=
{
  h := 14
  k := 38
  lower := (29869709/702910000)
  upper := (30010291/702910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_38_interval
}

theorem G14_39_formula : baezDuarteGramEntry 14 39 = vasyuninBEntry 14 39 := vasyuninBEntry_correct_axiom 14 39

theorem vasyuninBEntry_14_39_eval :
    ((((783129/18710000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 39) ∧
    (vasyuninBEntry 14 39 ≤ (((786871/18710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1439_formula_bound
  constructor <;> linarith

theorem G14_39_interval :
    ((((783129/18710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 39) ∧
    (baezDuarteGramEntry 14 39 ≤ (((786871/18710000) : ℚ) : ℝ)) := by
  rw [G14_39_formula]
  exact vasyuninBEntry_14_39_eval

def interval_14_39 : NamedVasyuninInterval :=
{
  h := 14
  k := 39
  lower := (783129/18710000)
  upper := (786871/18710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_39_interval
}

theorem G14_40_formula : baezDuarteGramEntry 14 40 = vasyuninBEntry 14 40 := vasyuninBEntry_correct_axiom 14 40

theorem vasyuninBEntry_14_40_eval :
    ((((38975703/942970000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 40) ∧
    (vasyuninBEntry 14 40 ≤ (((39164297/942970000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_20_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 20 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G14_40_interval :
    ((((38975703/942970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 40) ∧
    (baezDuarteGramEntry 14 40 ≤ (((39164297/942970000) : ℚ) : ℝ)) := by
  rw [G14_40_formula]
  exact vasyuninBEntry_14_40_eval

def interval_14_40 : NamedVasyuninInterval :=
{
  h := 14
  k := 40
  lower := (38975703/942970000)
  upper := (39164297/942970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_40_interval
}

theorem G14_41_formula : baezDuarteGramEntry 14 41 = vasyuninBEntry 14 41 := vasyuninBEntry_correct_axiom 14 41

theorem vasyuninBEntry_14_41_eval :
    ((((38875081/949190000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 41) ∧
    (vasyuninBEntry 14 41 ≤ (((39064919/949190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1441_formula_bound
  constructor <;> linarith

theorem G14_41_interval :
    ((((38875081/949190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 41) ∧
    (baezDuarteGramEntry 14 41 ≤ (((39064919/949190000) : ℚ) : ℝ)) := by
  rw [G14_41_formula]
  exact vasyuninBEntry_14_41_eval

def interval_14_41 : NamedVasyuninInterval :=
{
  h := 14
  k := 41
  lower := (38875081/949190000)
  upper := (39064919/949190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_41_interval
}

theorem G14_42_formula : baezDuarteGramEntry 14 42 = vasyuninBEntry 14 42 := vasyuninBEntry_correct_axiom 14 42

theorem vasyuninBEntry_14_42_eval :
    ((((32450797/792030000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 42) ∧
    (vasyuninBEntry 14 42 ≤ (((32609203/792030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 3 14 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 14)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 14)
  constructor <;> linarith

theorem G14_42_interval :
    ((((32450797/792030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 42) ∧
    (baezDuarteGramEntry 14 42 ≤ (((32609203/792030000) : ℚ) : ℝ)) := by
  rw [G14_42_formula]
  exact vasyuninBEntry_14_42_eval

def interval_14_42 : NamedVasyuninInterval :=
{
  h := 14
  k := 42
  lower := (32450797/792030000)
  upper := (32609203/792030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_42_interval
}

theorem G14_43_formula : baezDuarteGramEntry 14 43 = vasyuninBEntry 14 43 := vasyuninBEntry_correct_axiom 14 43

theorem vasyuninBEntry_14_43_eval :
    ((((17535767/442330000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 43) ∧
    (vasyuninBEntry 14 43 ≤ (((17624233/442330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1443_formula_bound
  constructor <;> linarith

theorem G14_43_interval :
    ((((17535767/442330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 43) ∧
    (baezDuarteGramEntry 14 43 ≤ (((17624233/442330000) : ℚ) : ℝ)) := by
  rw [G14_43_formula]
  exact vasyuninBEntry_14_43_eval

def interval_14_43 : NamedVasyuninInterval :=
{
  h := 14
  k := 43
  lower := (17535767/442330000)
  upper := (17624233/442330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_43_interval
}

theorem G14_44_formula : baezDuarteGramEntry 14 44 = vasyuninBEntry 14 44 := vasyuninBEntry_correct_axiom 14 44

theorem vasyuninBEntry_14_44_eval :
    ((((33852577/874230000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 44) ∧
    (vasyuninBEntry 14 44 ≤ (((34027423/874230000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_22_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 22 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G14_44_interval :
    ((((33852577/874230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 44) ∧
    (baezDuarteGramEntry 14 44 ≤ (((34027423/874230000) : ℚ) : ℝ)) := by
  rw [G14_44_formula]
  exact vasyuninBEntry_14_44_eval

def interval_14_44 : NamedVasyuninInterval :=
{
  h := 14
  k := 44
  lower := (33852577/874230000)
  upper := (34027423/874230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_44_interval
}

theorem G14_45_formula : baezDuarteGramEntry 14 45 = vasyuninBEntry 14 45 := vasyuninBEntry_correct_axiom 14 45

theorem vasyuninBEntry_14_45_eval :
    ((((8871619/233810000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 45) ∧
    (vasyuninBEntry 14 45 ≤ (((8918381/233810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1445_formula_bound
  constructor <;> linarith

theorem G14_45_interval :
    ((((8871619/233810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 45) ∧
    (baezDuarteGramEntry 14 45 ≤ (((8918381/233810000) : ℚ) : ℝ)) := by
  rw [G14_45_formula]
  exact vasyuninBEntry_14_45_eval

def interval_14_45 : NamedVasyuninInterval :=
{
  h := 14
  k := 45
  lower := (8871619/233810000)
  upper := (8918381/233810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_45_interval
}

theorem G14_46_formula : baezDuarteGramEntry 14 46 = vasyuninBEntry 14 46 := vasyuninBEntry_correct_axiom 14 46

theorem vasyuninBEntry_14_46_eval :
    ((((2808463/75370000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 46) ∧
    (vasyuninBEntry 14 46 ≤ (((2823537/75370000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 23 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G14_46_interval :
    ((((2808463/75370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 46) ∧
    (baezDuarteGramEntry 14 46 ≤ (((2823537/75370000) : ℚ) : ℝ)) := by
  rw [G14_46_formula]
  exact vasyuninBEntry_14_46_eval

def interval_14_46 : NamedVasyuninInterval :=
{
  h := 14
  k := 46
  lower := (2808463/75370000)
  upper := (2823537/75370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_46_interval
}

theorem G14_47_formula : baezDuarteGramEntry 14 47 = vasyuninBEntry 14 47 := vasyuninBEntry_correct_axiom 14 47

theorem vasyuninBEntry_14_47_eval :
    ((((2553033/69670000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 47) ∧
    (vasyuninBEntry 14 47 ≤ (((2566967/69670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1447_formula_bound
  constructor <;> linarith

theorem G14_47_interval :
    ((((2553033/69670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 47) ∧
    (baezDuarteGramEntry 14 47 ≤ (((2566967/69670000) : ℚ) : ℝ)) := by
  rw [G14_47_formula]
  exact vasyuninBEntry_14_47_eval

def interval_14_47 : NamedVasyuninInterval :=
{
  h := 14
  k := 47
  lower := (2553033/69670000)
  upper := (2566967/69670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_47_interval
}

theorem G14_48_formula : baezDuarteGramEntry 14 48 = vasyuninBEntry 14 48 := vasyuninBEntry_correct_axiom 14 48

theorem vasyuninBEntry_14_48_eval :
    ((((3970993/110070000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 48) ∧
    (vasyuninBEntry 14 48 ≤ (((3993007/110070000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_24_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 24 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G14_48_interval :
    ((((3970993/110070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 48) ∧
    (baezDuarteGramEntry 14 48 ≤ (((3993007/110070000) : ℚ) : ℝ)) := by
  rw [G14_48_formula]
  exact vasyuninBEntry_14_48_eval

def interval_14_48 : NamedVasyuninInterval :=
{
  h := 14
  k := 48
  lower := (3970993/110070000)
  upper := (3993007/110070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_48_interval
}

theorem G14_49_formula : baezDuarteGramEntry 14 49 = vasyuninBEntry 14 49 := vasyuninBEntry_correct_axiom 14 49

theorem vasyuninBEntry_14_49_eval :
    ((((139409/3910000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 49) ∧
    (vasyuninBEntry 14 49 ≤ (((140191/3910000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 7 7 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 7)
  constructor <;> linarith

theorem G14_49_interval :
    ((((139409/3910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 49) ∧
    (baezDuarteGramEntry 14 49 ≤ (((140191/3910000) : ℚ) : ℝ)) := by
  rw [G14_49_formula]
  exact vasyuninBEntry_14_49_eval

def interval_14_49 : NamedVasyuninInterval :=
{
  h := 14
  k := 49
  lower := (139409/3910000)
  upper := (140191/3910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_49_interval
}

theorem G14_50_formula : baezDuarteGramEntry 14 50 = vasyuninBEntry 14 50 := vasyuninBEntry_correct_axiom 14 50

theorem vasyuninBEntry_14_50_eval :
    ((((2557699/73010000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 50) ∧
    (vasyuninBEntry 14 50 ≤ (((2572301/73010000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 25 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G14_50_interval :
    ((((2557699/73010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 50) ∧
    (baezDuarteGramEntry 14 50 ≤ (((2572301/73010000) : ℚ) : ℝ)) := by
  rw [G14_50_formula]
  exact vasyuninBEntry_14_50_eval

def interval_14_50 : NamedVasyuninInterval :=
{
  h := 14
  k := 50
  lower := (2557699/73010000)
  upper := (2572301/73010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_50_interval
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

theorem G15_16_formula : baezDuarteGramEntry 15 16 = vasyuninBEntry 15 16 := vasyuninBEntry_correct_axiom 15 16

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

theorem G15_17_formula : baezDuarteGramEntry 15 17 = vasyuninBEntry 15 17 := vasyuninBEntry_correct_axiom 15 17

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

theorem G15_18_formula : baezDuarteGramEntry 15 18 = vasyuninBEntry 15 18 := vasyuninBEntry_correct_axiom 15 18

theorem vasyuninBEntry_15_18_eval :
    ((((34948577/514230000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 18) ∧
    (vasyuninBEntry 15 18 ≤ (((35051423/514230000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_6_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 6 3 (by norm_num)
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

theorem G15_19_formula : baezDuarteGramEntry 15 19 = vasyuninBEntry 15 19 := vasyuninBEntry_correct_axiom 15 19

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

theorem G15_20_formula : baezDuarteGramEntry 15 20 = vasyuninBEntry 15 20 := vasyuninBEntry_correct_axiom 15 20

theorem vasyuninBEntry_15_20_eval :
    ((((2523993/40070000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 20) ∧
    (vasyuninBEntry 15 20 ≤ (((2532007/40070000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 4 5 (by norm_num)
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

theorem G15_21_formula : baezDuarteGramEntry 15 21 = vasyuninBEntry 15 21 := vasyuninBEntry_correct_axiom 15 21

theorem vasyuninBEntry_15_21_eval :
    ((((12100087/199130000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 21) ∧
    (vasyuninBEntry 15 21 ≤ (((12139913/199130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 7 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G15_21_interval :
    ((((12100087/199130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 21) ∧
    (baezDuarteGramEntry 15 21 ≤ (((12139913/199130000) : ℚ) : ℝ)) := by
  rw [G15_21_formula]
  exact vasyuninBEntry_15_21_eval

def interval_15_21 : NamedVasyuninInterval :=
{
  h := 15
  k := 21
  lower := (12100087/199130000)
  upper := (12139913/199130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_21_interval
}

theorem G15_22_formula : baezDuarteGramEntry 15 22 = vasyuninBEntry 15 22 := vasyuninBEntry_correct_axiom 15 22

theorem vasyuninBEntry_15_22_eval :
    ((((39662891/671090000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 22) ∧
    (vasyuninBEntry 15 22 ≤ (((39797109/671090000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1522_formula_bound
  constructor <;> linarith

theorem G15_22_interval :
    ((((39662891/671090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 22) ∧
    (baezDuarteGramEntry 15 22 ≤ (((39797109/671090000) : ℚ) : ℝ)) := by
  rw [G15_22_formula]
  exact vasyuninBEntry_15_22_eval

def interval_15_22 : NamedVasyuninInterval :=
{
  h := 15
  k := 22
  lower := (39662891/671090000)
  upper := (39797109/671090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_22_interval
}

theorem G15_23_formula : baezDuarteGramEntry 15 23 = vasyuninBEntry 15 23 := vasyuninBEntry_correct_axiom 15 23

theorem vasyuninBEntry_15_23_eval :
    ((((2429273/42270000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 23) ∧
    (vasyuninBEntry 15 23 ≤ (((2437727/42270000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1523_formula_bound
  constructor <;> linarith

theorem G15_23_interval :
    ((((2429273/42270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 23) ∧
    (baezDuarteGramEntry 15 23 ≤ (((2437727/42270000) : ℚ) : ℝ)) := by
  rw [G15_23_formula]
  exact vasyuninBEntry_15_23_eval

def interval_15_23 : NamedVasyuninInterval :=
{
  h := 15
  k := 23
  lower := (2429273/42270000)
  upper := (2437727/42270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_23_interval
}

theorem G15_24_formula : baezDuarteGramEntry 15 24 = vasyuninBEntry 15 24 := vasyuninBEntry_correct_axiom 15 24

theorem vasyuninBEntry_15_24_eval :
    ((((837001/14990000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 24) ∧
    (vasyuninBEntry 15 24 ≤ (((839999/14990000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 8 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G15_24_interval :
    ((((837001/14990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 24) ∧
    (baezDuarteGramEntry 15 24 ≤ (((839999/14990000) : ℚ) : ℝ)) := by
  rw [G15_24_formula]
  exact vasyuninBEntry_15_24_eval

def interval_15_24 : NamedVasyuninInterval :=
{
  h := 15
  k := 24
  lower := (837001/14990000)
  upper := (839999/14990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_24_interval
}

theorem G15_25_formula : baezDuarteGramEntry 15 25 = vasyuninBEntry 15 25 := vasyuninBEntry_correct_axiom 15 25

theorem vasyuninBEntry_15_25_eval :
    ((((40356103/738970000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 25) ∧
    (vasyuninBEntry 15 25 ≤ (((40503897/738970000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 5 5 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G15_25_interval :
    ((((40356103/738970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 25) ∧
    (baezDuarteGramEntry 15 25 ≤ (((40503897/738970000) : ℚ) : ℝ)) := by
  rw [G15_25_formula]
  exact vasyuninBEntry_15_25_eval

def interval_15_25 : NamedVasyuninInterval :=
{
  h := 15
  k := 25
  lower := (40356103/738970000)
  upper := (40503897/738970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_25_interval
}

theorem G15_26_formula : baezDuarteGramEntry 15 26 = vasyuninBEntry 15 26 := vasyuninBEntry_correct_axiom 15 26

theorem vasyuninBEntry_15_26_eval :
    ((((25631903/480970000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 26) ∧
    (vasyuninBEntry 15 26 ≤ (((25728097/480970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1526_formula_bound
  constructor <;> linarith

theorem G15_26_interval :
    ((((25631903/480970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 26) ∧
    (baezDuarteGramEntry 15 26 ≤ (((25728097/480970000) : ℚ) : ℝ)) := by
  rw [G15_26_formula]
  exact vasyuninBEntry_15_26_eval

def interval_15_26 : NamedVasyuninInterval :=
{
  h := 15
  k := 26
  lower := (25631903/480970000)
  upper := (25728097/480970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_26_interval
}

theorem G15_27_formula : baezDuarteGramEntry 15 27 = vasyuninBEntry 15 27 := vasyuninBEntry_correct_axiom 15 27

theorem vasyuninBEntry_15_27_eval :
    ((((17207117/328830000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 27) ∧
    (vasyuninBEntry 15 27 ≤ (((17272883/328830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 9 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G15_27_interval :
    ((((17207117/328830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 27) ∧
    (baezDuarteGramEntry 15 27 ≤ (((17272883/328830000) : ℚ) : ℝ)) := by
  rw [G15_27_formula]
  exact vasyuninBEntry_15_27_eval

def interval_15_27 : NamedVasyuninInterval :=
{
  h := 15
  k := 27
  lower := (17207117/328830000)
  upper := (17272883/328830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_27_interval
}

theorem G15_28_formula : baezDuarteGramEntry 15 28 = vasyuninBEntry 15 28 := vasyuninBEntry_correct_axiom 15 28

theorem vasyuninBEntry_15_28_eval :
    ((((32506923/630770000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 28) ∧
    (vasyuninBEntry 15 28 ≤ (((32633077/630770000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1528_formula_bound
  constructor <;> linarith

theorem G15_28_interval :
    ((((32506923/630770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 28) ∧
    (baezDuarteGramEntry 15 28 ≤ (((32633077/630770000) : ℚ) : ℝ)) := by
  rw [G15_28_formula]
  exact vasyuninBEntry_15_28_eval

def interval_15_28 : NamedVasyuninInterval :=
{
  h := 15
  k := 28
  lower := (32506923/630770000)
  upper := (32633077/630770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_28_interval
}

theorem G15_29_formula : baezDuarteGramEntry 15 29 = vasyuninBEntry 15 29 := vasyuninBEntry_correct_axiom 15 29

theorem vasyuninBEntry_15_29_eval :
    ((((14501609/283910000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 29) ∧
    (vasyuninBEntry 15 29 ≤ (((14558391/283910000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1529_formula_bound
  constructor <;> linarith

theorem G15_29_interval :
    ((((14501609/283910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 29) ∧
    (baezDuarteGramEntry 15 29 ≤ (((14558391/283910000) : ℚ) : ℝ)) := by
  rw [G15_29_formula]
  exact vasyuninBEntry_15_29_eval

def interval_15_29 : NamedVasyuninInterval :=
{
  h := 15
  k := 29
  lower := (14501609/283910000)
  upper := (14558391/283910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_29_interval
}

theorem G15_30_formula : baezDuarteGramEntry 15 30 = vasyuninBEntry 15 30 := vasyuninBEntry_correct_axiom 15 30

theorem vasyuninBEntry_15_30_eval :
    ((((16952007/329930000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 30) ∧
    (vasyuninBEntry 15 30 ≤ (((17017993/329930000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 15 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 15)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 15)
  constructor <;> linarith

theorem G15_30_interval :
    ((((16952007/329930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 30) ∧
    (baezDuarteGramEntry 15 30 ≤ (((17017993/329930000) : ℚ) : ℝ)) := by
  rw [G15_30_formula]
  exact vasyuninBEntry_15_30_eval

def interval_15_30 : NamedVasyuninInterval :=
{
  h := 15
  k := 30
  lower := (16952007/329930000)
  upper := (17017993/329930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_30_interval
}

theorem G15_31_formula : baezDuarteGramEntry 15 31 = vasyuninBEntry 15 31 := vasyuninBEntry_correct_axiom 15 31

theorem vasyuninBEntry_15_31_eval :
    ((((8036093/164070000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 31) ∧
    (vasyuninBEntry 15 31 ≤ (((8068907/164070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1531_formula_bound
  constructor <;> linarith

theorem G15_31_interval :
    ((((8036093/164070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 31) ∧
    (baezDuarteGramEntry 15 31 ≤ (((8068907/164070000) : ℚ) : ℝ)) := by
  rw [G15_31_formula]
  exact vasyuninBEntry_15_31_eval

def interval_15_31 : NamedVasyuninInterval :=
{
  h := 15
  k := 31
  lower := (8036093/164070000)
  upper := (8068907/164070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_31_interval
}

theorem G15_32_formula : baezDuarteGramEntry 15 32 = vasyuninBEntry 15 32 := vasyuninBEntry_correct_axiom 15 32

theorem vasyuninBEntry_15_32_eval :
    ((((9438081/199190000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 32) ∧
    (vasyuninBEntry 15 32 ≤ (((9477919/199190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1532_formula_bound
  constructor <;> linarith

theorem G15_32_interval :
    ((((9438081/199190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 32) ∧
    (baezDuarteGramEntry 15 32 ≤ (((9477919/199190000) : ℚ) : ℝ)) := by
  rw [G15_32_formula]
  exact vasyuninBEntry_15_32_eval

def interval_15_32 : NamedVasyuninInterval :=
{
  h := 15
  k := 32
  lower := (9438081/199190000)
  upper := (9477919/199190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_32_interval
}

theorem G15_33_formula : baezDuarteGramEntry 15 33 = vasyuninBEntry 15 33 := vasyuninBEntry_correct_axiom 15 33

theorem vasyuninBEntry_15_33_eval :
    ((((40362447/875530000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 33) ∧
    (vasyuninBEntry 15 33 ≤ (((40537553/875530000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 11 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G15_33_interval :
    ((((40362447/875530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 33) ∧
    (baezDuarteGramEntry 15 33 ≤ (((40537553/875530000) : ℚ) : ℝ)) := by
  rw [G15_33_formula]
  exact vasyuninBEntry_15_33_eval

def interval_15_33 : NamedVasyuninInterval :=
{
  h := 15
  k := 33
  lower := (40362447/875530000)
  upper := (40537553/875530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_33_interval
}

theorem G15_34_formula : baezDuarteGramEntry 15 34 = vasyuninBEntry 15 34 := vasyuninBEntry_correct_axiom 15 34

theorem vasyuninBEntry_15_34_eval :
    ((((67001/1490000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 34) ∧
    (vasyuninBEntry 15 34 ≤ (((67299/1490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1534_formula_bound
  constructor <;> linarith

theorem G15_34_interval :
    ((((67001/1490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 34) ∧
    (baezDuarteGramEntry 15 34 ≤ (((67299/1490000) : ℚ) : ℝ)) := by
  rw [G15_34_formula]
  exact vasyuninBEntry_15_34_eval

def interval_15_34 : NamedVasyuninInterval :=
{
  h := 15
  k := 34
  lower := (67001/1490000)
  upper := (67299/1490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_34_interval
}

theorem G15_35_formula : baezDuarteGramEntry 15 35 = vasyuninBEntry 15 35 := vasyuninBEntry_correct_axiom 15 35

theorem vasyuninBEntry_15_35_eval :
    ((((1159867/26330000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 35) ∧
    (vasyuninBEntry 15 35 ≤ (((1165133/26330000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 7 5 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G15_35_interval :
    ((((1159867/26330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 35) ∧
    (baezDuarteGramEntry 15 35 ≤ (((1165133/26330000) : ℚ) : ℝ)) := by
  rw [G15_35_formula]
  exact vasyuninBEntry_15_35_eval

def interval_15_35 : NamedVasyuninInterval :=
{
  h := 15
  k := 35
  lower := (1159867/26330000)
  upper := (1165133/26330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_35_interval
}

theorem G15_36_formula : baezDuarteGramEntry 15 36 = vasyuninBEntry 15 36 := vasyuninBEntry_correct_axiom 15 36

theorem vasyuninBEntry_15_36_eval :
    ((((12481037/289630000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 36) ∧
    (vasyuninBEntry 15 36 ≤ (((12538963/289630000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_12_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 12 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G15_36_interval :
    ((((12481037/289630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 36) ∧
    (baezDuarteGramEntry 15 36 ≤ (((12538963/289630000) : ℚ) : ℝ)) := by
  rw [G15_36_formula]
  exact vasyuninBEntry_15_36_eval

def interval_15_36 : NamedVasyuninInterval :=
{
  h := 15
  k := 36
  lower := (12481037/289630000)
  upper := (12538963/289630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_36_interval
}

theorem G15_37_formula : baezDuarteGramEntry 15 37 = vasyuninBEntry 15 37 := vasyuninBEntry_correct_axiom 15 37

theorem vasyuninBEntry_15_37_eval :
    ((((26716867/631330000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 37) ∧
    (vasyuninBEntry 15 37 ≤ (((26843133/631330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1537_formula_bound
  constructor <;> linarith

theorem G15_37_interval :
    ((((26716867/631330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 37) ∧
    (baezDuarteGramEntry 15 37 ≤ (((26843133/631330000) : ℚ) : ℝ)) := by
  rw [G15_37_formula]
  exact vasyuninBEntry_15_37_eval

def interval_15_37 : NamedVasyuninInterval :=
{
  h := 15
  k := 37
  lower := (26716867/631330000)
  upper := (26843133/631330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_37_interval
}

theorem G15_38_formula : baezDuarteGramEntry 15 38 = vasyuninBEntry 15 38 := vasyuninBEntry_correct_axiom 15 38

theorem vasyuninBEntry_15_38_eval :
    ((((31334581/754190000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 38) ∧
    (vasyuninBEntry 15 38 ≤ (((31485419/754190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1538_formula_bound
  constructor <;> linarith

theorem G15_38_interval :
    ((((31334581/754190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 38) ∧
    (baezDuarteGramEntry 15 38 ≤ (((31485419/754190000) : ℚ) : ℝ)) := by
  rw [G15_38_formula]
  exact vasyuninBEntry_15_38_eval

def interval_15_38 : NamedVasyuninInterval :=
{
  h := 15
  k := 38
  lower := (31334581/754190000)
  upper := (31485419/754190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_38_interval
}

theorem G15_39_formula : baezDuarteGramEntry 15 39 = vasyuninBEntry 15 39 := vasyuninBEntry_correct_axiom 15 39

theorem vasyuninBEntry_15_39_eval :
    ((((38595341/946590000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 39) ∧
    (vasyuninBEntry 15 39 ≤ (((38784659/946590000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 13 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G15_39_interval :
    ((((38595341/946590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 39) ∧
    (baezDuarteGramEntry 15 39 ≤ (((38784659/946590000) : ℚ) : ℝ)) := by
  rw [G15_39_formula]
  exact vasyuninBEntry_15_39_eval

def interval_15_39 : NamedVasyuninInterval :=
{
  h := 15
  k := 39
  lower := (38595341/946590000)
  upper := (38784659/946590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_39_interval
}

theorem G15_40_formula : baezDuarteGramEntry 15 40 = vasyuninBEntry 15 40 := vasyuninBEntry_correct_axiom 15 40

theorem vasyuninBEntry_15_40_eval :
    ((((30863129/768710000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 40) ∧
    (vasyuninBEntry 15 40 ≤ (((31016871/768710000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 8 5 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G15_40_interval :
    ((((30863129/768710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 40) ∧
    (baezDuarteGramEntry 15 40 ≤ (((31016871/768710000) : ℚ) : ℝ)) := by
  rw [G15_40_formula]
  exact vasyuninBEntry_15_40_eval

def interval_15_40 : NamedVasyuninInterval :=
{
  h := 15
  k := 40
  lower := (30863129/768710000)
  upper := (31016871/768710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_40_interval
}

theorem G15_41_formula : baezDuarteGramEntry 15 41 = vasyuninBEntry 15 41 := vasyuninBEntry_correct_axiom 15 41

theorem vasyuninBEntry_15_41_eval :
    ((((34372949/870510000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 41) ∧
    (vasyuninBEntry 15 41 ≤ (((34547051/870510000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1541_formula_bound
  constructor <;> linarith

theorem G15_41_interval :
    ((((34372949/870510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 41) ∧
    (baezDuarteGramEntry 15 41 ≤ (((34547051/870510000) : ℚ) : ℝ)) := by
  rw [G15_41_formula]
  exact vasyuninBEntry_15_41_eval

def interval_15_41 : NamedVasyuninInterval :=
{
  h := 15
  k := 41
  lower := (34372949/870510000)
  upper := (34547051/870510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_41_interval
}

theorem G15_42_formula : baezDuarteGramEntry 15 42 = vasyuninBEntry 15 42 := vasyuninBEntry_correct_axiom 15 42

theorem vasyuninBEntry_15_42_eval :
    ((((1280713/32870000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 42) ∧
    (vasyuninBEntry 15 42 ≤ (((1287287/32870000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_14_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 14 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G15_42_interval :
    ((((1280713/32870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 42) ∧
    (baezDuarteGramEntry 15 42 ≤ (((1287287/32870000) : ℚ) : ℝ)) := by
  rw [G15_42_formula]
  exact vasyuninBEntry_15_42_eval

def interval_15_42 : NamedVasyuninInterval :=
{
  h := 15
  k := 42
  lower := (1280713/32870000)
  upper := (1287287/32870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_42_interval
}

theorem G15_43_formula : baezDuarteGramEntry 15 43 = vasyuninBEntry 15 43 := vasyuninBEntry_correct_axiom 15 43

theorem vasyuninBEntry_15_43_eval :
    ((((18362319/476810000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 43) ∧
    (vasyuninBEntry 15 43 ≤ (((18457681/476810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1543_formula_bound
  constructor <;> linarith

theorem G15_43_interval :
    ((((18362319/476810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 43) ∧
    (baezDuarteGramEntry 15 43 ≤ (((18457681/476810000) : ℚ) : ℝ)) := by
  rw [G15_43_formula]
  exact vasyuninBEntry_15_43_eval

def interval_15_43 : NamedVasyuninInterval :=
{
  h := 15
  k := 43
  lower := (18362319/476810000)
  upper := (18457681/476810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_43_interval
}

theorem G15_44_formula : baezDuarteGramEntry 15 44 = vasyuninBEntry 15 44 := vasyuninBEntry_correct_axiom 15 44

theorem vasyuninBEntry_15_44_eval :
    ((((37751183/988170000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 44) ∧
    (vasyuninBEntry 15 44 ≤ (((37948817/988170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1544_formula_bound
  constructor <;> linarith

theorem G15_44_interval :
    ((((37751183/988170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 44) ∧
    (baezDuarteGramEntry 15 44 ≤ (((37948817/988170000) : ℚ) : ℝ)) := by
  rw [G15_44_formula]
  exact vasyuninBEntry_15_44_eval

def interval_15_44 : NamedVasyuninInterval :=
{
  h := 15
  k := 44
  lower := (37751183/988170000)
  upper := (37948817/988170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_44_interval
}

theorem G15_45_formula : baezDuarteGramEntry 15 45 = vasyuninBEntry 15 45 := vasyuninBEntry_correct_axiom 15 45

theorem vasyuninBEntry_15_45_eval :
    ((((2757787/72130000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 45) ∧
    (vasyuninBEntry 15 45 ≤ (((2772213/72130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 3 15 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 15)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 15)
  constructor <;> linarith

theorem G15_45_interval :
    ((((2757787/72130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 45) ∧
    (baezDuarteGramEntry 15 45 ≤ (((2772213/72130000) : ℚ) : ℝ)) := by
  rw [G15_45_formula]
  exact vasyuninBEntry_15_45_eval

def interval_15_45 : NamedVasyuninInterval :=
{
  h := 15
  k := 45
  lower := (2757787/72130000)
  upper := (2772213/72130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_45_interval
}

theorem G15_46_formula : baezDuarteGramEntry 15 46 = vasyuninBEntry 15 46 := vasyuninBEntry_correct_axiom 15 46

theorem vasyuninBEntry_15_46_eval :
    ((((6163369/166310000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 46) ∧
    (vasyuninBEntry 15 46 ≤ (((6196631/166310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1546_formula_bound
  constructor <;> linarith

theorem G15_46_interval :
    ((((6163369/166310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 46) ∧
    (baezDuarteGramEntry 15 46 ≤ (((6196631/166310000) : ℚ) : ℝ)) := by
  rw [G15_46_formula]
  exact vasyuninBEntry_15_46_eval

def interval_15_46 : NamedVasyuninInterval :=
{
  h := 15
  k := 46
  lower := (6163369/166310000)
  upper := (6196631/166310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_46_interval
}

theorem G15_47_formula : baezDuarteGramEntry 15 47 = vasyuninBEntry 15 47 := vasyuninBEntry_correct_axiom 15 47

theorem vasyuninBEntry_15_47_eval :
    ((((12495517/344830000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 47) ∧
    (vasyuninBEntry 15 47 ≤ (((12564483/344830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1547_formula_bound
  constructor <;> linarith

theorem G15_47_interval :
    ((((12495517/344830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 47) ∧
    (baezDuarteGramEntry 15 47 ≤ (((12564483/344830000) : ℚ) : ℝ)) := by
  rw [G15_47_formula]
  exact vasyuninBEntry_15_47_eval

def interval_15_47 : NamedVasyuninInterval :=
{
  h := 15
  k := 47
  lower := (12495517/344830000)
  upper := (12564483/344830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_47_interval
}

theorem G15_48_formula : baezDuarteGramEntry 15 48 = vasyuninBEntry 15 48 := vasyuninBEntry_correct_axiom 15 48

theorem vasyuninBEntry_15_48_eval :
    ((((10540353/296470000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 48) ∧
    (vasyuninBEntry 15 48 ≤ (((10599647/296470000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_16_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 16 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G15_48_interval :
    ((((10540353/296470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 48) ∧
    (baezDuarteGramEntry 15 48 ≤ (((10599647/296470000) : ℚ) : ℝ)) := by
  rw [G15_48_formula]
  exact vasyuninBEntry_15_48_eval

def interval_15_48 : NamedVasyuninInterval :=
{
  h := 15
  k := 48
  lower := (10540353/296470000)
  upper := (10599647/296470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_48_interval
}

theorem G15_49_formula : baezDuarteGramEntry 15 49 = vasyuninBEntry 15 49 := vasyuninBEntry_correct_axiom 15 49

theorem vasyuninBEntry_15_49_eval :
    ((((6194767/177330000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 49) ∧
    (vasyuninBEntry 15 49 ≤ (((6230233/177330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1549_formula_bound
  constructor <;> linarith

theorem G15_49_interval :
    ((((6194767/177330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 49) ∧
    (baezDuarteGramEntry 15 49 ≤ (((6230233/177330000) : ℚ) : ℝ)) := by
  rw [G15_49_formula]
  exact vasyuninBEntry_15_49_eval

def interval_15_49 : NamedVasyuninInterval :=
{
  h := 15
  k := 49
  lower := (6194767/177330000)
  upper := (6230233/177330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_49_interval
}

theorem G15_50_formula : baezDuarteGramEntry 15 50 = vasyuninBEntry 15 50 := vasyuninBEntry_correct_axiom 15 50

theorem vasyuninBEntry_15_50_eval :
    ((((29594009/859910000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 50) ∧
    (vasyuninBEntry 15 50 ≤ (((29765991/859910000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 10 5 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G15_50_interval :
    ((((29594009/859910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 50) ∧
    (baezDuarteGramEntry 15 50 ≤ (((29765991/859910000) : ℚ) : ℝ)) := by
  rw [G15_50_formula]
  exact vasyuninBEntry_15_50_eval

def interval_15_50 : NamedVasyuninInterval :=
{
  h := 15
  k := 50
  lower := (29594009/859910000)
  upper := (29765991/859910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_50_interval
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

theorem G16_17_formula : baezDuarteGramEntry 16 17 = vasyuninBEntry 16 17 := vasyuninBEntry_correct_axiom 16 17

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

theorem G16_18_formula : baezDuarteGramEntry 16 18 = vasyuninBEntry 16 18 := vasyuninBEntry_correct_axiom 16 18

theorem vasyuninBEntry_16_18_eval :
    ((((36795403/545970000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 18) ∧
    (vasyuninBEntry 16 18 ≤ (((36904597/545970000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_8_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 8 9 2 (by norm_num)
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

theorem G16_19_formula : baezDuarteGramEntry 16 19 = vasyuninBEntry 16 19 := vasyuninBEntry_correct_axiom 16 19

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

theorem G16_20_formula : baezDuarteGramEntry 16 20 = vasyuninBEntry 16 20 := vasyuninBEntry_correct_axiom 16 20

theorem vasyuninBEntry_16_20_eval :
    ((((21470227/347730000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 20) ∧
    (vasyuninBEntry 16 20 ≤ (((21539773/347730000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 5 4 (by norm_num)
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

theorem G16_21_formula : baezDuarteGramEntry 16 21 = vasyuninBEntry 16 21 := vasyuninBEntry_correct_axiom 16 21

theorem vasyuninBEntry_16_21_eval :
    ((((3135981/52690000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 21) ∧
    (vasyuninBEntry 16 21 ≤ (((3146519/52690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1621_formula_bound
  constructor <;> linarith

theorem G16_21_interval :
    ((((3135981/52690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 21) ∧
    (baezDuarteGramEntry 16 21 ≤ (((3146519/52690000) : ℚ) : ℝ)) := by
  rw [G16_21_formula]
  exact vasyuninBEntry_16_21_eval

def interval_16_21 : NamedVasyuninInterval :=
{
  h := 16
  k := 21
  lower := (3135981/52690000)
  upper := (3146519/52690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_21_interval
}

theorem G16_22_formula : baezDuarteGramEntry 16 22 = vasyuninBEntry 16 22 := vasyuninBEntry_correct_axiom 16 22

theorem vasyuninBEntry_16_22_eval :
    ((((3813381/66190000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 22) ∧
    (vasyuninBEntry 16 22 ≤ (((3826619/66190000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_8_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 8 11 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G16_22_interval :
    ((((3813381/66190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 22) ∧
    (baezDuarteGramEntry 16 22 ≤ (((3826619/66190000) : ℚ) : ℝ)) := by
  rw [G16_22_formula]
  exact vasyuninBEntry_16_22_eval

def interval_16_22 : NamedVasyuninInterval :=
{
  h := 16
  k := 22
  lower := (3813381/66190000)
  upper := (3826619/66190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_22_interval
}

theorem G16_23_formula : baezDuarteGramEntry 16 23 = vasyuninBEntry 16 23 := vasyuninBEntry_correct_axiom 16 23

theorem vasyuninBEntry_16_23_eval :
    ((((36085559/644410000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 23) ∧
    (vasyuninBEntry 16 23 ≤ (((36214441/644410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1623_formula_bound
  constructor <;> linarith

theorem G16_23_interval :
    ((((36085559/644410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 23) ∧
    (baezDuarteGramEntry 16 23 ≤ (((36214441/644410000) : ℚ) : ℝ)) := by
  rw [G16_23_formula]
  exact vasyuninBEntry_16_23_eval

def interval_16_23 : NamedVasyuninInterval :=
{
  h := 16
  k := 23
  lower := (36085559/644410000)
  upper := (36214441/644410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_23_interval
}

theorem G16_24_formula : baezDuarteGramEntry 16 24 = vasyuninBEntry 16 24 := vasyuninBEntry_correct_axiom 16 24

theorem vasyuninBEntry_16_24_eval :
    ((((7321697/133030000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 24) ∧
    (vasyuninBEntry 16 24 ≤ (((7348303/133030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 8 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 8)
  constructor <;> linarith

theorem G16_24_interval :
    ((((7321697/133030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 24) ∧
    (baezDuarteGramEntry 16 24 ≤ (((7348303/133030000) : ℚ) : ℝ)) := by
  rw [G16_24_formula]
  exact vasyuninBEntry_16_24_eval

def interval_16_24 : NamedVasyuninInterval :=
{
  h := 16
  k := 24
  lower := (7321697/133030000)
  upper := (7348303/133030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_24_interval
}

theorem G16_25_formula : baezDuarteGramEntry 16 25 = vasyuninBEntry 16 25 := vasyuninBEntry_correct_axiom 16 25

theorem vasyuninBEntry_16_25_eval :
    ((((4537709/85410000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 25) ∧
    (vasyuninBEntry 16 25 ≤ (((4554791/85410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1625_formula_bound
  constructor <;> linarith

theorem G16_25_interval :
    ((((4537709/85410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 25) ∧
    (baezDuarteGramEntry 16 25 ≤ (((4554791/85410000) : ℚ) : ℝ)) := by
  rw [G16_25_formula]
  exact vasyuninBEntry_16_25_eval

def interval_16_25 : NamedVasyuninInterval :=
{
  h := 16
  k := 25
  lower := (4537709/85410000)
  upper := (4554791/85410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_25_interval
}

theorem G16_26_formula : baezDuarteGramEntry 16 26 = vasyuninBEntry 16 26 := vasyuninBEntry_correct_axiom 16 26

theorem vasyuninBEntry_16_26_eval :
    ((((9094451/175490000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 26) ∧
    (vasyuninBEntry 16 26 ≤ (((9129549/175490000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_8_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 8 13 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G16_26_interval :
    ((((9094451/175490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 26) ∧
    (baezDuarteGramEntry 16 26 ≤ (((9129549/175490000) : ℚ) : ℝ)) := by
  rw [G16_26_formula]
  exact vasyuninBEntry_16_26_eval

def interval_16_26 : NamedVasyuninInterval :=
{
  h := 16
  k := 26
  lower := (9094451/175490000)
  upper := (9129549/175490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_26_interval
}

theorem G16_27_formula : baezDuarteGramEntry 16 27 = vasyuninBEntry 16 27 := vasyuninBEntry_correct_axiom 16 27

theorem vasyuninBEntry_16_27_eval :
    ((((42057073/829270000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 27) ∧
    (vasyuninBEntry 16 27 ≤ (((42222927/829270000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1627_formula_bound
  constructor <;> linarith

theorem G16_27_interval :
    ((((42057073/829270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 27) ∧
    (baezDuarteGramEntry 16 27 ≤ (((42222927/829270000) : ℚ) : ℝ)) := by
  rw [G16_27_formula]
  exact vasyuninBEntry_16_27_eval

def interval_16_27 : NamedVasyuninInterval :=
{
  h := 16
  k := 27
  lower := (42057073/829270000)
  upper := (42222927/829270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_27_interval
}

theorem G16_28_formula : baezDuarteGramEntry 16 28 = vasyuninBEntry 16 28 := vasyuninBEntry_correct_axiom 16 28

theorem vasyuninBEntry_16_28_eval :
    ((((12330219/247810000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 28) ∧
    (vasyuninBEntry 16 28 ≤ (((12379781/247810000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 7 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G16_28_interval :
    ((((12330219/247810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 28) ∧
    (baezDuarteGramEntry 16 28 ≤ (((12379781/247810000) : ℚ) : ℝ)) := by
  rw [G16_28_formula]
  exact vasyuninBEntry_16_28_eval

def interval_16_28 : NamedVasyuninInterval :=
{
  h := 16
  k := 28
  lower := (12330219/247810000)
  upper := (12379781/247810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_28_interval
}

theorem G16_29_formula : baezDuarteGramEntry 16 29 = vasyuninBEntry 16 29 := vasyuninBEntry_correct_axiom 16 29

theorem vasyuninBEntry_16_29_eval :
    ((((2229189/45610000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 29) ∧
    (vasyuninBEntry 16 29 ≤ (((2238311/45610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1629_formula_bound
  constructor <;> linarith

theorem G16_29_interval :
    ((((2229189/45610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 29) ∧
    (baezDuarteGramEntry 16 29 ≤ (((2238311/45610000) : ℚ) : ℝ)) := by
  rw [G16_29_formula]
  exact vasyuninBEntry_16_29_eval

def interval_16_29 : NamedVasyuninInterval :=
{
  h := 16
  k := 29
  lower := (2229189/45610000)
  upper := (2238311/45610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_29_interval
}

theorem G16_30_formula : baezDuarteGramEntry 16 30 = vasyuninBEntry 16 30 := vasyuninBEntry_correct_axiom 16 30

theorem vasyuninBEntry_16_30_eval :
    ((((26305471/545290000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 30) ∧
    (vasyuninBEntry 16 30 ≤ (((26414529/545290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_8_15_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 8 15 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G16_30_interval :
    ((((26305471/545290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 30) ∧
    (baezDuarteGramEntry 16 30 ≤ (((26414529/545290000) : ℚ) : ℝ)) := by
  rw [G16_30_formula]
  exact vasyuninBEntry_16_30_eval

def interval_16_30 : NamedVasyuninInterval :=
{
  h := 16
  k := 30
  lower := (26305471/545290000)
  upper := (26414529/545290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_30_interval
}

theorem G16_31_formula : baezDuarteGramEntry 16 31 = vasyuninBEntry 16 31 := vasyuninBEntry_correct_axiom 16 31

theorem vasyuninBEntry_16_31_eval :
    ((((4036567/84330000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 31) ∧
    (vasyuninBEntry 16 31 ≤ (((4053433/84330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1631_formula_bound
  constructor <;> linarith

theorem G16_31_interval :
    ((((4036567/84330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 31) ∧
    (baezDuarteGramEntry 16 31 ≤ (((4053433/84330000) : ℚ) : ℝ)) := by
  rw [G16_31_formula]
  exact vasyuninBEntry_16_31_eval

def interval_16_31 : NamedVasyuninInterval :=
{
  h := 16
  k := 31
  lower := (4036567/84330000)
  upper := (4053433/84330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_31_interval
}

theorem G16_32_formula : baezDuarteGramEntry 16 32 = vasyuninBEntry 16 32 := vasyuninBEntry_correct_axiom 16 32

theorem vasyuninBEntry_16_32_eval :
    ((((3507717/72830000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 32) ∧
    (vasyuninBEntry 16 32 ≤ (((3522283/72830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 16 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 16)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 16)
  constructor <;> linarith

theorem G16_32_interval :
    ((((3507717/72830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 32) ∧
    (baezDuarteGramEntry 16 32 ≤ (((3522283/72830000) : ℚ) : ℝ)) := by
  rw [G16_32_formula]
  exact vasyuninBEntry_16_32_eval

def interval_16_32 : NamedVasyuninInterval :=
{
  h := 16
  k := 32
  lower := (3507717/72830000)
  upper := (3522283/72830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_32_interval
}

theorem G16_33_formula : baezDuarteGramEntry 16 33 = vasyuninBEntry 16 33 := vasyuninBEntry_correct_axiom 16 33

theorem vasyuninBEntry_16_33_eval :
    ((((1251281/27190000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 33) ∧
    (vasyuninBEntry 16 33 ≤ (((1256719/27190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1633_formula_bound
  constructor <;> linarith

theorem G16_33_interval :
    ((((1251281/27190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 33) ∧
    (baezDuarteGramEntry 16 33 ≤ (((1256719/27190000) : ℚ) : ℝ)) := by
  rw [G16_33_formula]
  exact vasyuninBEntry_16_33_eval

def interval_16_33 : NamedVasyuninInterval :=
{
  h := 16
  k := 33
  lower := (1251281/27190000)
  upper := (1256719/27190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_33_interval
}

theorem G16_34_formula : baezDuarteGramEntry 16 34 = vasyuninBEntry 16 34 := vasyuninBEntry_correct_axiom 16 34

theorem vasyuninBEntry_16_34_eval :
    ((((5283151/118490000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 34) ∧
    (vasyuninBEntry 16 34 ≤ (((5306849/118490000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_8_17_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 8 17 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G16_34_interval :
    ((((5283151/118490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 34) ∧
    (baezDuarteGramEntry 16 34 ≤ (((5306849/118490000) : ℚ) : ℝ)) := by
  rw [G16_34_formula]
  exact vasyuninBEntry_16_34_eval

def interval_16_34 : NamedVasyuninInterval :=
{
  h := 16
  k := 34
  lower := (5283151/118490000)
  upper := (5306849/118490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_34_interval
}

theorem G16_35_formula : baezDuarteGramEntry 16 35 = vasyuninBEntry 16 35 := vasyuninBEntry_correct_axiom 16 35

theorem vasyuninBEntry_16_35_eval :
    ((((15514261/357390000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 35) ∧
    (vasyuninBEntry 16 35 ≤ (((15585739/357390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1635_formula_bound
  constructor <;> linarith

theorem G16_35_interval :
    ((((15514261/357390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 35) ∧
    (baezDuarteGramEntry 16 35 ≤ (((15585739/357390000) : ℚ) : ℝ)) := by
  rw [G16_35_formula]
  exact vasyuninBEntry_16_35_eval

def interval_16_35 : NamedVasyuninInterval :=
{
  h := 16
  k := 35
  lower := (15514261/357390000)
  upper := (15585739/357390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_35_interval
}

theorem G16_36_formula : baezDuarteGramEntry 16 36 = vasyuninBEntry 16 36 := vasyuninBEntry_correct_axiom 16 36

theorem vasyuninBEntry_16_36_eval :
    ((((671667/15830000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 36) ∧
    (vasyuninBEntry 16 36 ≤ (((674833/15830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 9 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G16_36_interval :
    ((((671667/15830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 36) ∧
    (baezDuarteGramEntry 16 36 ≤ (((674833/15830000) : ℚ) : ℝ)) := by
  rw [G16_36_formula]
  exact vasyuninBEntry_16_36_eval

def interval_16_36 : NamedVasyuninInterval :=
{
  h := 16
  k := 36
  lower := (671667/15830000)
  upper := (674833/15830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_36_interval
}

theorem G16_37_formula : baezDuarteGramEntry 16 37 = vasyuninBEntry 16 37 := vasyuninBEntry_correct_axiom 16 37

theorem vasyuninBEntry_16_37_eval :
    ((((11133181/268190000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 37) ∧
    (vasyuninBEntry 16 37 ≤ (((11186819/268190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1637_formula_bound
  constructor <;> linarith

theorem G16_37_interval :
    ((((11133181/268190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 37) ∧
    (baezDuarteGramEntry 16 37 ≤ (((11186819/268190000) : ℚ) : ℝ)) := by
  rw [G16_37_formula]
  exact vasyuninBEntry_16_37_eval

def interval_16_37 : NamedVasyuninInterval :=
{
  h := 16
  k := 37
  lower := (11133181/268190000)
  upper := (11186819/268190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_37_interval
}

theorem G16_38_formula : baezDuarteGramEntry 16 38 = vasyuninBEntry 16 38 := vasyuninBEntry_correct_axiom 16 38

theorem vasyuninBEntry_16_38_eval :
    ((((18270097/449030000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 38) ∧
    (vasyuninBEntry 16 38 ≤ (((18359903/449030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_8_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 8 19 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G16_38_interval :
    ((((18270097/449030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 38) ∧
    (baezDuarteGramEntry 16 38 ≤ (((18359903/449030000) : ℚ) : ℝ)) := by
  rw [G16_38_formula]
  exact vasyuninBEntry_16_38_eval

def interval_16_38 : NamedVasyuninInterval :=
{
  h := 16
  k := 38
  lower := (18270097/449030000)
  upper := (18359903/449030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_38_interval
}

theorem G16_39_formula : baezDuarteGramEntry 16 39 = vasyuninBEntry 16 39 := vasyuninBEntry_correct_axiom 16 39

theorem vasyuninBEntry_16_39_eval :
    ((((37994907/950930000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 39) ∧
    (vasyuninBEntry 16 39 ≤ (((38185093/950930000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1639_formula_bound
  constructor <;> linarith

theorem G16_39_interval :
    ((((37994907/950930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 39) ∧
    (baezDuarteGramEntry 16 39 ≤ (((38185093/950930000) : ℚ) : ℝ)) := by
  rw [G16_39_formula]
  exact vasyuninBEntry_16_39_eval

def interval_16_39 : NamedVasyuninInterval :=
{
  h := 16
  k := 39
  lower := (37994907/950930000)
  upper := (38185093/950930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_39_interval
}

theorem G16_40_formula : baezDuarteGramEntry 16 40 = vasyuninBEntry 16 40 := vasyuninBEntry_correct_axiom 16 40

theorem vasyuninBEntry_16_40_eval :
    ((((4552211/115390000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 40) ∧
    (vasyuninBEntry 16 40 ≤ (((4575289/115390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 5 8 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 8)
  constructor <;> linarith

theorem G16_40_interval :
    ((((4552211/115390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 40) ∧
    (baezDuarteGramEntry 16 40 ≤ (((4575289/115390000) : ℚ) : ℝ)) := by
  rw [G16_40_formula]
  exact vasyuninBEntry_16_40_eval

def interval_16_40 : NamedVasyuninInterval :=
{
  h := 16
  k := 40
  lower := (4552211/115390000)
  upper := (4575289/115390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_40_interval
}

theorem G16_41_formula : baezDuarteGramEntry 16 41 = vasyuninBEntry 16 41 := vasyuninBEntry_correct_axiom 16 41

theorem vasyuninBEntry_16_41_eval :
    ((((4620031/119690000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 41) ∧
    (vasyuninBEntry 16 41 ≤ (((4643969/119690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1641_formula_bound
  constructor <;> linarith

theorem G16_41_interval :
    ((((4620031/119690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 41) ∧
    (baezDuarteGramEntry 16 41 ≤ (((4643969/119690000) : ℚ) : ℝ)) := by
  rw [G16_41_formula]
  exact vasyuninBEntry_16_41_eval

def interval_16_41 : NamedVasyuninInterval :=
{
  h := 16
  k := 41
  lower := (4620031/119690000)
  upper := (4643969/119690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_41_interval
}

theorem G16_42_formula : baezDuarteGramEntry 16 42 = vasyuninBEntry 16 42 := vasyuninBEntry_correct_axiom 16 42

theorem vasyuninBEntry_16_42_eval :
    ((((16426733/432670000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 42) ∧
    (vasyuninBEntry 16 42 ≤ (((16513267/432670000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_8_21_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 8 21 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G16_42_interval :
    ((((16426733/432670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 42) ∧
    (baezDuarteGramEntry 16 42 ≤ (((16513267/432670000) : ℚ) : ℝ)) := by
  rw [G16_42_formula]
  exact vasyuninBEntry_16_42_eval

def interval_16_42 : NamedVasyuninInterval :=
{
  h := 16
  k := 42
  lower := (16426733/432670000)
  upper := (16513267/432670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_42_interval
}

theorem G16_43_formula : baezDuarteGramEntry 16 43 = vasyuninBEntry 16 43 := vasyuninBEntry_correct_axiom 16 43

theorem vasyuninBEntry_16_43_eval :
    ((((1055179/28210000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 43) ∧
    (vasyuninBEntry 16 43 ≤ (((1060821/28210000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1643_formula_bound
  constructor <;> linarith

theorem G16_43_interval :
    ((((1055179/28210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 43) ∧
    (baezDuarteGramEntry 16 43 ≤ (((1060821/28210000) : ℚ) : ℝ)) := by
  rw [G16_43_formula]
  exact vasyuninBEntry_16_43_eval

def interval_16_43 : NamedVasyuninInterval :=
{
  h := 16
  k := 43
  lower := (1055179/28210000)
  upper := (1060821/28210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_43_interval
}

theorem G16_44_formula : baezDuarteGramEntry 16 44 = vasyuninBEntry 16 44 := vasyuninBEntry_correct_axiom 16 44

theorem vasyuninBEntry_16_44_eval :
    ((((895573/24270000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 44) ∧
    (vasyuninBEntry 16 44 ≤ (((900427/24270000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 11 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G16_44_interval :
    ((((895573/24270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 44) ∧
    (baezDuarteGramEntry 16 44 ≤ (((900427/24270000) : ℚ) : ℝ)) := by
  rw [G16_44_formula]
  exact vasyuninBEntry_16_44_eval

def interval_16_44 : NamedVasyuninInterval :=
{
  h := 16
  k := 44
  lower := (895573/24270000)
  upper := (900427/24270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_44_interval
}

theorem G16_45_formula : baezDuarteGramEntry 16 45 = vasyuninBEntry 16 45 := vasyuninBEntry_correct_axiom 16 45

theorem vasyuninBEntry_16_45_eval :
    ((((6534561/179390000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 45) ∧
    (vasyuninBEntry 16 45 ≤ (((6570439/179390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1645_formula_bound
  constructor <;> linarith

theorem G16_45_interval :
    ((((6534561/179390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 45) ∧
    (baezDuarteGramEntry 16 45 ≤ (((6570439/179390000) : ℚ) : ℝ)) := by
  rw [G16_45_formula]
  exact vasyuninBEntry_16_45_eval

def interval_16_45 : NamedVasyuninInterval :=
{
  h := 16
  k := 45
  lower := (6534561/179390000)
  upper := (6570439/179390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_45_interval
}

theorem G16_46_formula : baezDuarteGramEntry 16 46 = vasyuninBEntry 16 46 := vasyuninBEntry_correct_axiom 16 46

theorem vasyuninBEntry_16_46_eval :
    ((((453941/12590000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 46) ∧
    (vasyuninBEntry 16 46 ≤ (((456459/12590000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_8_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 8 23 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G16_46_interval :
    ((((453941/12590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 46) ∧
    (baezDuarteGramEntry 16 46 ≤ (((456459/12590000) : ℚ) : ℝ)) := by
  rw [G16_46_formula]
  exact vasyuninBEntry_16_46_eval

def interval_16_46 : NamedVasyuninInterval :=
{
  h := 16
  k := 46
  lower := (453941/12590000)
  upper := (456459/12590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_46_interval
}

theorem G16_47_formula : baezDuarteGramEntry 16 47 = vasyuninBEntry 16 47 := vasyuninBEntry_correct_axiom 16 47

theorem vasyuninBEntry_16_47_eval :
    ((((9159413/255870000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 47) ∧
    (vasyuninBEntry 16 47 ≤ (((9210587/255870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1647_formula_bound
  constructor <;> linarith

theorem G16_47_interval :
    ((((9159413/255870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 47) ∧
    (baezDuarteGramEntry 16 47 ≤ (((9210587/255870000) : ℚ) : ℝ)) := by
  rw [G16_47_formula]
  exact vasyuninBEntry_16_47_eval

def interval_16_47 : NamedVasyuninInterval :=
{
  h := 16
  k := 47
  lower := (9159413/255870000)
  upper := (9210587/255870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_47_interval
}

theorem G16_48_formula : baezDuarteGramEntry 16 48 = vasyuninBEntry 16 48 := vasyuninBEntry_correct_axiom 16 48

theorem vasyuninBEntry_16_48_eval :
    ((((33626171/938290000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 48) ∧
    (vasyuninBEntry 16 48 ≤ (((33813829/938290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 3 16 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 16)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 16)
  constructor <;> linarith

theorem G16_48_interval :
    ((((33626171/938290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 48) ∧
    (baezDuarteGramEntry 16 48 ≤ (((33813829/938290000) : ℚ) : ℝ)) := by
  rw [G16_48_formula]
  exact vasyuninBEntry_16_48_eval

def interval_16_48 : NamedVasyuninInterval :=
{
  h := 16
  k := 48
  lower := (33626171/938290000)
  upper := (33813829/938290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_48_interval
}

theorem G16_49_formula : baezDuarteGramEntry 16 49 = vasyuninBEntry 16 49 := vasyuninBEntry_correct_axiom 16 49

theorem vasyuninBEntry_16_49_eval :
    ((((4469653/128470000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 49) ∧
    (vasyuninBEntry 16 49 ≤ (((4495347/128470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1649_formula_bound
  constructor <;> linarith

theorem G16_49_interval :
    ((((4469653/128470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 49) ∧
    (baezDuarteGramEntry 16 49 ≤ (((4495347/128470000) : ℚ) : ℝ)) := by
  rw [G16_49_formula]
  exact vasyuninBEntry_16_49_eval

def interval_16_49 : NamedVasyuninInterval :=
{
  h := 16
  k := 49
  lower := (4469653/128470000)
  upper := (4495347/128470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_49_interval
}

theorem G16_50_formula : baezDuarteGramEntry 16 50 = vasyuninBEntry 16 50 := vasyuninBEntry_correct_axiom 16 50

theorem vasyuninBEntry_16_50_eval :
    ((((762511/22390000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 50) ∧
    (vasyuninBEntry 16 50 ≤ (((766989/22390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_8_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 8 25 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G16_50_interval :
    ((((762511/22390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 50) ∧
    (baezDuarteGramEntry 16 50 ≤ (((766989/22390000) : ℚ) : ℝ)) := by
  rw [G16_50_formula]
  exact vasyuninBEntry_16_50_eval

def interval_16_50 : NamedVasyuninInterval :=
{
  h := 16
  k := 50
  lower := (762511/22390000)
  upper := (766989/22390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_50_interval
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

theorem G17_18_formula : baezDuarteGramEntry 17 18 = vasyuninBEntry 17 18 := vasyuninBEntry_correct_axiom 17 18

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

theorem G17_19_formula : baezDuarteGramEntry 17 19 = vasyuninBEntry 17 19 := vasyuninBEntry_correct_axiom 17 19

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

theorem G17_20_formula : baezDuarteGramEntry 17 20 = vasyuninBEntry 17 20 := vasyuninBEntry_correct_axiom 17 20

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

theorem G17_21_formula : baezDuarteGramEntry 17 21 = vasyuninBEntry 17 21 := vasyuninBEntry_correct_axiom 17 21

theorem vasyuninBEntry_17_21_eval :
    ((((34800559/594410000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 21) ∧
    (vasyuninBEntry 17 21 ≤ (((34919441/594410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1721_formula_bound
  constructor <;> linarith

theorem G17_21_interval :
    ((((34800559/594410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 21) ∧
    (baezDuarteGramEntry 17 21 ≤ (((34919441/594410000) : ℚ) : ℝ)) := by
  rw [G17_21_formula]
  exact vasyuninBEntry_17_21_eval

def interval_17_21 : NamedVasyuninInterval :=
{
  h := 17
  k := 21
  lower := (34800559/594410000)
  upper := (34919441/594410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_21_interval
}

theorem G17_22_formula : baezDuarteGramEntry 17 22 = vasyuninBEntry 17 22 := vasyuninBEntry_correct_axiom 17 22

theorem vasyuninBEntry_17_22_eval :
    ((((693773/12270000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 22) ∧
    (vasyuninBEntry 17 22 ≤ (((696227/12270000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1722_formula_bound
  constructor <;> linarith

theorem G17_22_interval :
    ((((693773/12270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 22) ∧
    (baezDuarteGramEntry 17 22 ≤ (((696227/12270000) : ℚ) : ℝ)) := by
  rw [G17_22_formula]
  exact vasyuninBEntry_17_22_eval

def interval_17_22 : NamedVasyuninInterval :=
{
  h := 17
  k := 22
  lower := (693773/12270000)
  upper := (696227/12270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_22_interval
}

theorem G17_23_formula : baezDuarteGramEntry 17 23 = vasyuninBEntry 17 23 := vasyuninBEntry_correct_axiom 17 23

theorem vasyuninBEntry_17_23_eval :
    ((((930179/16960000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 23) ∧
    (vasyuninBEntry 17 23 ≤ (((933571/16960000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1723_formula_bound
  constructor <;> linarith

theorem G17_23_interval :
    ((((930179/16960000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 23) ∧
    (baezDuarteGramEntry 17 23 ≤ (((933571/16960000) : ℚ) : ℝ)) := by
  rw [G17_23_formula]
  exact vasyuninBEntry_17_23_eval

def interval_17_23 : NamedVasyuninInterval :=
{
  h := 17
  k := 23
  lower := (930179/16960000)
  upper := (933571/16960000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_23_interval
}

theorem G17_24_formula : baezDuarteGramEntry 17 24 = vasyuninBEntry 17 24 := vasyuninBEntry_correct_axiom 17 24

theorem vasyuninBEntry_17_24_eval :
    ((((48798413/915870000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 24) ∧
    (vasyuninBEntry 17 24 ≤ (((48981587/915870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1724_formula_bound
  constructor <;> linarith

theorem G17_24_interval :
    ((((48798413/915870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 24) ∧
    (baezDuarteGramEntry 17 24 ≤ (((48981587/915870000) : ℚ) : ℝ)) := by
  rw [G17_24_formula]
  exact vasyuninBEntry_17_24_eval

def interval_17_24 : NamedVasyuninInterval :=
{
  h := 17
  k := 24
  lower := (48798413/915870000)
  upper := (48981587/915870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_24_interval
}

theorem G17_25_formula : baezDuarteGramEntry 17 25 = vasyuninBEntry 17 25 := vasyuninBEntry_correct_axiom 17 25

theorem vasyuninBEntry_17_25_eval :
    ((((47688419/915810000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 25) ∧
    (vasyuninBEntry 17 25 ≤ (((47871581/915810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1725_formula_bound
  constructor <;> linarith

theorem G17_25_interval :
    ((((47688419/915810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 25) ∧
    (baezDuarteGramEntry 17 25 ≤ (((47871581/915810000) : ℚ) : ℝ)) := by
  rw [G17_25_formula]
  exact vasyuninBEntry_17_25_eval

def interval_17_25 : NamedVasyuninInterval :=
{
  h := 17
  k := 25
  lower := (47688419/915810000)
  upper := (47871581/915810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_25_interval
}

theorem G17_26_formula : baezDuarteGramEntry 17 26 = vasyuninBEntry 17 26 := vasyuninBEntry_correct_axiom 17 26

theorem vasyuninBEntry_17_26_eval :
    ((((7071081/139190000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 26) ∧
    (vasyuninBEntry 17 26 ≤ (((7098919/139190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1726_formula_bound
  constructor <;> linarith

theorem G17_26_interval :
    ((((7071081/139190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 26) ∧
    (baezDuarteGramEntry 17 26 ≤ (((7098919/139190000) : ℚ) : ℝ)) := by
  rw [G17_26_formula]
  exact vasyuninBEntry_17_26_eval

def interval_17_26 : NamedVasyuninInterval :=
{
  h := 17
  k := 26
  lower := (7071081/139190000)
  upper := (7098919/139190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_26_interval
}

theorem G17_27_formula : baezDuarteGramEntry 17 27 = vasyuninBEntry 17 27 := vasyuninBEntry_correct_axiom 17 27

theorem vasyuninBEntry_17_27_eval :
    ((((35897419/725810000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 27) ∧
    (vasyuninBEntry 17 27 ≤ (((36042581/725810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1727_formula_bound
  constructor <;> linarith

theorem G17_27_interval :
    ((((35897419/725810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 27) ∧
    (baezDuarteGramEntry 17 27 ≤ (((36042581/725810000) : ℚ) : ℝ)) := by
  rw [G17_27_formula]
  exact vasyuninBEntry_17_27_eval

def interval_17_27 : NamedVasyuninInterval :=
{
  h := 17
  k := 27
  lower := (35897419/725810000)
  upper := (36042581/725810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_27_interval
}

theorem G17_28_formula : baezDuarteGramEntry 17 28 = vasyuninBEntry 17 28 := vasyuninBEntry_correct_axiom 17 28

theorem vasyuninBEntry_17_28_eval :
    ((((706141/14590000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 28) ∧
    (vasyuninBEntry 17 28 ≤ (((709059/14590000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1728_formula_bound
  constructor <;> linarith

theorem G17_28_interval :
    ((((706141/14590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 28) ∧
    (baezDuarteGramEntry 17 28 ≤ (((709059/14590000) : ℚ) : ℝ)) := by
  rw [G17_28_formula]
  exact vasyuninBEntry_17_28_eval

def interval_17_28 : NamedVasyuninInterval :=
{
  h := 17
  k := 28
  lower := (706141/14590000)
  upper := (709059/14590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_28_interval
}

theorem G17_29_formula : baezDuarteGramEntry 17 29 = vasyuninBEntry 17 29 := vasyuninBEntry_correct_axiom 17 29

theorem vasyuninBEntry_17_29_eval :
    ((((202947/4280000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 29) ∧
    (vasyuninBEntry 17 29 ≤ (((203803/4280000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1729_formula_bound
  constructor <;> linarith

theorem G17_29_interval :
    ((((202947/4280000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 29) ∧
    (baezDuarteGramEntry 17 29 ≤ (((203803/4280000) : ℚ) : ℝ)) := by
  rw [G17_29_formula]
  exact vasyuninBEntry_17_29_eval

def interval_17_29 : NamedVasyuninInterval :=
{
  h := 17
  k := 29
  lower := (202947/4280000)
  upper := (203803/4280000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_29_interval
}

theorem G17_30_formula : baezDuarteGramEntry 17 30 = vasyuninBEntry 17 30 := vasyuninBEntry_correct_axiom 17 30

theorem vasyuninBEntry_17_30_eval :
    ((((25285717/542830000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 30) ∧
    (vasyuninBEntry 17 30 ≤ (((25394283/542830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1730_formula_bound
  constructor <;> linarith

theorem G17_30_interval :
    ((((25285717/542830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 30) ∧
    (baezDuarteGramEntry 17 30 ≤ (((25394283/542830000) : ℚ) : ℝ)) := by
  rw [G17_30_formula]
  exact vasyuninBEntry_17_30_eval

def interval_17_30 : NamedVasyuninInterval :=
{
  h := 17
  k := 30
  lower := (25285717/542830000)
  upper := (25394283/542830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_30_interval
}

theorem G17_31_formula : baezDuarteGramEntry 17 31 = vasyuninBEntry 17 31 := vasyuninBEntry_correct_axiom 17 31

theorem vasyuninBEntry_17_31_eval :
    ((((5416193/118070000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 31) ∧
    (vasyuninBEntry 17 31 ≤ (((5439807/118070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1731_formula_bound
  constructor <;> linarith

theorem G17_31_interval :
    ((((5416193/118070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 31) ∧
    (baezDuarteGramEntry 17 31 ≤ (((5439807/118070000) : ℚ) : ℝ)) := by
  rw [G17_31_formula]
  exact vasyuninBEntry_17_31_eval

def interval_17_31 : NamedVasyuninInterval :=
{
  h := 17
  k := 31
  lower := (5416193/118070000)
  upper := (5439807/118070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_31_interval
}

theorem G17_32_formula : baezDuarteGramEntry 17 32 = vasyuninBEntry 17 32 := vasyuninBEntry_correct_axiom 17 32

theorem vasyuninBEntry_17_32_eval :
    ((((12412621/273790000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 32) ∧
    (vasyuninBEntry 17 32 ≤ (((12467379/273790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1732_formula_bound
  constructor <;> linarith

theorem G17_32_interval :
    ((((12412621/273790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 32) ∧
    (baezDuarteGramEntry 17 32 ≤ (((12467379/273790000) : ℚ) : ℝ)) := by
  rw [G17_32_formula]
  exact vasyuninBEntry_17_32_eval

def interval_17_32 : NamedVasyuninInterval :=
{
  h := 17
  k := 32
  lower := (12412621/273790000)
  upper := (12467379/273790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_32_interval
}

theorem G17_33_formula : baezDuarteGramEntry 17 33 = vasyuninBEntry 17 33 := vasyuninBEntry_correct_axiom 17 33

theorem vasyuninBEntry_17_33_eval :
    ((((5036317/111830000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 33) ∧
    (vasyuninBEntry 17 33 ≤ (((5058683/111830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1733_formula_bound
  constructor <;> linarith

theorem G17_33_interval :
    ((((5036317/111830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 33) ∧
    (baezDuarteGramEntry 17 33 ≤ (((5058683/111830000) : ℚ) : ℝ)) := by
  rw [G17_33_formula]
  exact vasyuninBEntry_17_33_eval

def interval_17_33 : NamedVasyuninInterval :=
{
  h := 17
  k := 33
  lower := (5036317/111830000)
  upper := (5058683/111830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_33_interval
}

theorem G17_34_formula : baezDuarteGramEntry 17 34 = vasyuninBEntry 17 34 := vasyuninBEntry_correct_axiom 17 34

theorem vasyuninBEntry_17_34_eval :
    ((((4563681/100690000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 34) ∧
    (vasyuninBEntry 17 34 ≤ (((4583819/100690000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 17 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 17)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 17)
  constructor <;> linarith

theorem G17_34_interval :
    ((((4563681/100690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 34) ∧
    (baezDuarteGramEntry 17 34 ≤ (((4583819/100690000) : ℚ) : ℝ)) := by
  rw [G17_34_formula]
  exact vasyuninBEntry_17_34_eval

def interval_17_34 : NamedVasyuninInterval :=
{
  h := 17
  k := 34
  lower := (4563681/100690000)
  upper := (4583819/100690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_34_interval
}

theorem G17_35_formula : baezDuarteGramEntry 17 35 = vasyuninBEntry 17 35 := vasyuninBEntry_correct_axiom 17 35

theorem vasyuninBEntry_17_35_eval :
    ((((4729103/108970000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 35) ∧
    (vasyuninBEntry 17 35 ≤ (((4750897/108970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1735_formula_bound
  constructor <;> linarith

theorem G17_35_interval :
    ((((4729103/108970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 35) ∧
    (baezDuarteGramEntry 17 35 ≤ (((4750897/108970000) : ℚ) : ℝ)) := by
  rw [G17_35_formula]
  exact vasyuninBEntry_17_35_eval

def interval_17_35 : NamedVasyuninInterval :=
{
  h := 17
  k := 35
  lower := (4729103/108970000)
  upper := (4750897/108970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_35_interval
}

theorem G17_36_formula : baezDuarteGramEntry 17 36 = vasyuninBEntry 17 36 := vasyuninBEntry_correct_axiom 17 36

theorem vasyuninBEntry_17_36_eval :
    ((((20296787/482130000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 36) ∧
    (vasyuninBEntry 17 36 ≤ (((20393213/482130000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1736_formula_bound
  constructor <;> linarith

theorem G17_36_interval :
    ((((20296787/482130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 36) ∧
    (baezDuarteGramEntry 17 36 ≤ (((20393213/482130000) : ℚ) : ℝ)) := by
  rw [G17_36_formula]
  exact vasyuninBEntry_17_36_eval

def interval_17_36 : NamedVasyuninInterval :=
{
  h := 17
  k := 36
  lower := (20296787/482130000)
  upper := (20393213/482130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_36_interval
}

theorem G17_37_formula : baezDuarteGramEntry 17 37 = vasyuninBEntry 17 37 := vasyuninBEntry_correct_axiom 17 37

theorem vasyuninBEntry_17_37_eval :
    ((((6554027/159730000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 37) ∧
    (vasyuninBEntry 17 37 ≤ (((6585973/159730000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1737_formula_bound
  constructor <;> linarith

theorem G17_37_interval :
    ((((6554027/159730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 37) ∧
    (baezDuarteGramEntry 17 37 ≤ (((6585973/159730000) : ℚ) : ℝ)) := by
  rw [G17_37_formula]
  exact vasyuninBEntry_17_37_eval

def interval_17_37 : NamedVasyuninInterval :=
{
  h := 17
  k := 37
  lower := (6554027/159730000)
  upper := (6585973/159730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_37_interval
}

theorem G17_38_formula : baezDuarteGramEntry 17 38 = vasyuninBEntry 17 38 := vasyuninBEntry_correct_axiom 17 38

theorem vasyuninBEntry_17_38_eval :
    ((((201373/5020000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 38) ∧
    (vasyuninBEntry 17 38 ≤ (((202377/5020000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1738_formula_bound
  constructor <;> linarith

theorem G17_38_interval :
    ((((201373/5020000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 38) ∧
    (baezDuarteGramEntry 17 38 ≤ (((202377/5020000) : ℚ) : ℝ)) := by
  rw [G17_38_formula]
  exact vasyuninBEntry_17_38_eval

def interval_17_38 : NamedVasyuninInterval :=
{
  h := 17
  k := 38
  lower := (201373/5020000)
  upper := (202377/5020000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_38_interval
}

theorem G17_39_formula : baezDuarteGramEntry 17 39 = vasyuninBEntry 17 39 := vasyuninBEntry_correct_axiom 17 39

theorem vasyuninBEntry_17_39_eval :
    ((((4118269/104810000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 39) ∧
    (vasyuninBEntry 17 39 ≤ (((4139231/104810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1739_formula_bound
  constructor <;> linarith

theorem G17_39_interval :
    ((((4118269/104810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 39) ∧
    (baezDuarteGramEntry 17 39 ≤ (((4139231/104810000) : ℚ) : ℝ)) := by
  rw [G17_39_formula]
  exact vasyuninBEntry_17_39_eval

def interval_17_39 : NamedVasyuninInterval :=
{
  h := 17
  k := 39
  lower := (4118269/104810000)
  upper := (4139231/104810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_39_interval
}

theorem G17_40_formula : baezDuarteGramEntry 17 40 = vasyuninBEntry 17 40 := vasyuninBEntry_correct_axiom 17 40

theorem vasyuninBEntry_17_40_eval :
    ((((28127059/729410000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 40) ∧
    (vasyuninBEntry 17 40 ≤ (((28272941/729410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1740_formula_bound
  constructor <;> linarith

theorem G17_40_interval :
    ((((28127059/729410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 40) ∧
    (baezDuarteGramEntry 17 40 ≤ (((28272941/729410000) : ℚ) : ℝ)) := by
  rw [G17_40_formula]
  exact vasyuninBEntry_17_40_eval

def interval_17_40 : NamedVasyuninInterval :=
{
  h := 17
  k := 40
  lower := (28127059/729410000)
  upper := (28272941/729410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_40_interval
}

theorem G17_41_formula : baezDuarteGramEntry 17 41 = vasyuninBEntry 17 41 := vasyuninBEntry_correct_axiom 17 41

theorem vasyuninBEntry_17_41_eval :
    ((((22031821/581790000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 41) ∧
    (vasyuninBEntry 17 41 ≤ (((22148179/581790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1741_formula_bound
  constructor <;> linarith

theorem G17_41_interval :
    ((((22031821/581790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 41) ∧
    (baezDuarteGramEntry 17 41 ≤ (((22148179/581790000) : ℚ) : ℝ)) := by
  rw [G17_41_formula]
  exact vasyuninBEntry_17_41_eval

def interval_17_41 : NamedVasyuninInterval :=
{
  h := 17
  k := 41
  lower := (22031821/581790000)
  upper := (22148179/581790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_41_interval
}

theorem G17_42_formula : baezDuarteGramEntry 17 42 = vasyuninBEntry 17 42 := vasyuninBEntry_correct_axiom 17 42

theorem vasyuninBEntry_17_42_eval :
    ((((30119241/807590000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 42) ∧
    (vasyuninBEntry 17 42 ≤ (((30280759/807590000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1742_formula_bound
  constructor <;> linarith

theorem G17_42_interval :
    ((((30119241/807590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 42) ∧
    (baezDuarteGramEntry 17 42 ≤ (((30280759/807590000) : ℚ) : ℝ)) := by
  rw [G17_42_formula]
  exact vasyuninBEntry_17_42_eval

def interval_17_42 : NamedVasyuninInterval :=
{
  h := 17
  k := 42
  lower := (30119241/807590000)
  upper := (30280759/807590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_42_interval
}

theorem G17_43_formula : baezDuarteGramEntry 17 43 = vasyuninBEntry 17 43 := vasyuninBEntry_correct_axiom 17 43

theorem vasyuninBEntry_17_43_eval :
    ((((27664609/753910000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 43) ∧
    (vasyuninBEntry 17 43 ≤ (((27815391/753910000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1743_formula_bound
  constructor <;> linarith

theorem G17_43_interval :
    ((((27664609/753910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 43) ∧
    (baezDuarteGramEntry 17 43 ≤ (((27815391/753910000) : ℚ) : ℝ)) := by
  rw [G17_43_formula]
  exact vasyuninBEntry_17_43_eval

def interval_17_43 : NamedVasyuninInterval :=
{
  h := 17
  k := 43
  lower := (27664609/753910000)
  upper := (27815391/753910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_43_interval
}

theorem G17_44_formula : baezDuarteGramEntry 17 44 = vasyuninBEntry 17 44 := vasyuninBEntry_correct_axiom 17 44

theorem vasyuninBEntry_17_44_eval :
    ((((22796791/632090000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 44) ∧
    (vasyuninBEntry 17 44 ≤ (((22923209/632090000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1744_formula_bound
  constructor <;> linarith

theorem G17_44_interval :
    ((((22796791/632090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 44) ∧
    (baezDuarteGramEntry 17 44 ≤ (((22923209/632090000) : ℚ) : ℝ)) := by
  rw [G17_44_formula]
  exact vasyuninBEntry_17_44_eval

def interval_17_44 : NamedVasyuninInterval :=
{
  h := 17
  k := 44
  lower := (22796791/632090000)
  upper := (22923209/632090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_44_interval
}

theorem G17_45_formula : baezDuarteGramEntry 17 45 = vasyuninBEntry 17 45 := vasyuninBEntry_correct_axiom 17 45

theorem vasyuninBEntry_17_45_eval :
    ((((25388563/714370000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 45) ∧
    (vasyuninBEntry 17 45 ≤ (((25531437/714370000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1745_formula_bound
  constructor <;> linarith

theorem G17_45_interval :
    ((((25388563/714370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 45) ∧
    (baezDuarteGramEntry 17 45 ≤ (((25531437/714370000) : ℚ) : ℝ)) := by
  rw [G17_45_formula]
  exact vasyuninBEntry_17_45_eval

def interval_17_45 : NamedVasyuninInterval :=
{
  h := 17
  k := 45
  lower := (25388563/714370000)
  upper := (25531437/714370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_45_interval
}

theorem G17_46_formula : baezDuarteGramEntry 17 46 = vasyuninBEntry 17 46 := vasyuninBEntry_correct_axiom 17 46

theorem vasyuninBEntry_17_46_eval :
    ((((15490793/442070000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 46) ∧
    (vasyuninBEntry 17 46 ≤ (((15579207/442070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1746_formula_bound
  constructor <;> linarith

theorem G17_46_interval :
    ((((15490793/442070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 46) ∧
    (baezDuarteGramEntry 17 46 ≤ (((15579207/442070000) : ℚ) : ℝ)) := by
  rw [G17_46_formula]
  exact vasyuninBEntry_17_46_eval

def interval_17_46 : NamedVasyuninInterval :=
{
  h := 17
  k := 46
  lower := (15490793/442070000)
  upper := (15579207/442070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_46_interval
}

theorem G17_47_formula : baezDuarteGramEntry 17 47 = vasyuninBEntry 17 47 := vasyuninBEntry_correct_axiom 17 47

theorem vasyuninBEntry_17_47_eval :
    ((((125597/3630000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 47) ∧
    (vasyuninBEntry 17 47 ≤ (((126323/3630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1747_formula_bound
  constructor <;> linarith

theorem G17_47_interval :
    ((((125597/3630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 47) ∧
    (baezDuarteGramEntry 17 47 ≤ (((126323/3630000) : ℚ) : ℝ)) := by
  rw [G17_47_formula]
  exact vasyuninBEntry_17_47_eval

def interval_17_47 : NamedVasyuninInterval :=
{
  h := 17
  k := 47
  lower := (125597/3630000)
  upper := (126323/3630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_47_interval
}

theorem G17_48_formula : baezDuarteGramEntry 17 48 = vasyuninBEntry 17 48 := vasyuninBEntry_correct_axiom 17 48

theorem vasyuninBEntry_17_48_eval :
    ((((23491331/686690000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 48) ∧
    (vasyuninBEntry 17 48 ≤ (((23628669/686690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1748_formula_bound
  constructor <;> linarith

theorem G17_48_interval :
    ((((23491331/686690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 48) ∧
    (baezDuarteGramEntry 17 48 ≤ (((23628669/686690000) : ℚ) : ℝ)) := by
  rw [G17_48_formula]
  exact vasyuninBEntry_17_48_eval

def interval_17_48 : NamedVasyuninInterval :=
{
  h := 17
  k := 48
  lower := (23491331/686690000)
  upper := (23628669/686690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_48_interval
}

theorem G17_49_formula : baezDuarteGramEntry 17 49 = vasyuninBEntry 17 49 := vasyuninBEntry_correct_axiom 17 49

theorem vasyuninBEntry_17_49_eval :
    ((((20748779/612210000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 49) ∧
    (vasyuninBEntry 17 49 ≤ (((20871221/612210000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1749_formula_bound
  constructor <;> linarith

theorem G17_49_interval :
    ((((20748779/612210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 49) ∧
    (baezDuarteGramEntry 17 49 ≤ (((20871221/612210000) : ℚ) : ℝ)) := by
  rw [G17_49_formula]
  exact vasyuninBEntry_17_49_eval

def interval_17_49 : NamedVasyuninInterval :=
{
  h := 17
  k := 49
  lower := (20748779/612210000)
  upper := (20871221/612210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_49_interval
}

theorem G17_50_formula : baezDuarteGramEntry 17 50 = vasyuninBEntry 17 50 := vasyuninBEntry_correct_axiom 17 50

theorem vasyuninBEntry_17_50_eval :
    ((((6069477/180230000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 50) ∧
    (vasyuninBEntry 17 50 ≤ (((6105523/180230000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1750_formula_bound
  constructor <;> linarith

theorem G17_50_interval :
    ((((6069477/180230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 50) ∧
    (baezDuarteGramEntry 17 50 ≤ (((6105523/180230000) : ℚ) : ℝ)) := by
  rw [G17_50_formula]
  exact vasyuninBEntry_17_50_eval

def interval_17_50 : NamedVasyuninInterval :=
{
  h := 17
  k := 50
  lower := (6069477/180230000)
  upper := (6105523/180230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_50_interval
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

theorem G18_19_formula : baezDuarteGramEntry 18 19 = vasyuninBEntry 18 19 := vasyuninBEntry_correct_axiom 18 19

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

theorem G18_20_formula : baezDuarteGramEntry 18 20 = vasyuninBEntry 18 20 := vasyuninBEntry_correct_axiom 18 20

theorem vasyuninBEntry_18_20_eval :
    ((((44356831/731690000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 20) ∧
    (vasyuninBEntry 18 20 ≤ (((44503169/731690000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 10 2 (by norm_num)
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

theorem G18_21_formula : baezDuarteGramEntry 18 21 = vasyuninBEntry 18 21 := vasyuninBEntry_correct_axiom 18 21

theorem vasyuninBEntry_18_21_eval :
    ((((50772399/876010000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 21) ∧
    (vasyuninBEntry 18 21 ≤ (((50947601/876010000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_6_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 6 7 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G18_21_interval :
    ((((50772399/876010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 21) ∧
    (baezDuarteGramEntry 18 21 ≤ (((50947601/876010000) : ℚ) : ℝ)) := by
  rw [G18_21_formula]
  exact vasyuninBEntry_18_21_eval

def interval_18_21 : NamedVasyuninInterval :=
{
  h := 18
  k := 21
  lower := (50772399/876010000)
  upper := (50947601/876010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_21_interval
}

theorem G18_22_formula : baezDuarteGramEntry 18 22 = vasyuninBEntry 18 22 := vasyuninBEntry_correct_axiom 18 22

theorem vasyuninBEntry_18_22_eval :
    ((((2665219/47810000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 22) ∧
    (vasyuninBEntry 18 22 ≤ (((2674781/47810000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 11 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G18_22_interval :
    ((((2665219/47810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 22) ∧
    (baezDuarteGramEntry 18 22 ≤ (((2674781/47810000) : ℚ) : ℝ)) := by
  rw [G18_22_formula]
  exact vasyuninBEntry_18_22_eval

def interval_18_22 : NamedVasyuninInterval :=
{
  h := 18
  k := 22
  lower := (2665219/47810000)
  upper := (2674781/47810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_22_interval
}

theorem G18_23_formula : baezDuarteGramEntry 18 23 = vasyuninBEntry 18 23 := vasyuninBEntry_correct_axiom 18 23

theorem vasyuninBEntry_18_23_eval :
    ((((53750251/997490000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 23) ∧
    (vasyuninBEntry 18 23 ≤ (((53949749/997490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1823_formula_bound
  constructor <;> linarith

theorem G18_23_interval :
    ((((53750251/997490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 23) ∧
    (baezDuarteGramEntry 18 23 ≤ (((53949749/997490000) : ℚ) : ℝ)) := by
  rw [G18_23_formula]
  exact vasyuninBEntry_18_23_eval

def interval_18_23 : NamedVasyuninInterval :=
{
  h := 18
  k := 23
  lower := (53750251/997490000)
  upper := (53949749/997490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_23_interval
}

theorem G18_24_formula : baezDuarteGramEntry 18 24 = vasyuninBEntry 18 24 := vasyuninBEntry_correct_axiom 18 24

theorem vasyuninBEntry_18_24_eval :
    ((((6307979/120210000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 24) ∧
    (vasyuninBEntry 18 24 ≤ (((6332021/120210000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 4 6 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G18_24_interval :
    ((((6307979/120210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 24) ∧
    (baezDuarteGramEntry 18 24 ≤ (((6332021/120210000) : ℚ) : ℝ)) := by
  rw [G18_24_formula]
  exact vasyuninBEntry_18_24_eval

def interval_18_24 : NamedVasyuninInterval :=
{
  h := 18
  k := 24
  lower := (6307979/120210000)
  upper := (6332021/120210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_24_interval
}

theorem G18_25_formula : baezDuarteGramEntry 18 25 = vasyuninBEntry 18 25 := vasyuninBEntry_correct_axiom 18 25

theorem vasyuninBEntry_18_25_eval :
    ((((50820057/999430000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 25) ∧
    (vasyuninBEntry 18 25 ≤ (((51019943/999430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1825_formula_bound
  constructor <;> linarith

theorem G18_25_interval :
    ((((50820057/999430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 25) ∧
    (baezDuarteGramEntry 18 25 ≤ (((51019943/999430000) : ℚ) : ℝ)) := by
  rw [G18_25_formula]
  exact vasyuninBEntry_18_25_eval

def interval_18_25 : NamedVasyuninInterval :=
{
  h := 18
  k := 25
  lower := (50820057/999430000)
  upper := (51019943/999430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_25_interval
}

theorem G18_26_formula : baezDuarteGramEntry 18 26 = vasyuninBEntry 18 26 := vasyuninBEntry_correct_axiom 18 26

theorem vasyuninBEntry_18_26_eval :
    ((((8472929/170710000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 26) ∧
    (vasyuninBEntry 18 26 ≤ (((8507071/170710000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 13 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G18_26_interval :
    ((((8472929/170710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 26) ∧
    (baezDuarteGramEntry 18 26 ≤ (((8507071/170710000) : ℚ) : ℝ)) := by
  rw [G18_26_formula]
  exact vasyuninBEntry_18_26_eval

def interval_18_26 : NamedVasyuninInterval :=
{
  h := 18
  k := 26
  lower := (8472929/170710000)
  upper := (8507071/170710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_26_interval
}

theorem G18_27_formula : baezDuarteGramEntry 18 27 = vasyuninBEntry 18 27 := vasyuninBEntry_correct_axiom 18 27

theorem vasyuninBEntry_18_27_eval :
    ((((6506697/133030000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 27) ∧
    (vasyuninBEntry 18 27 ≤ (((6533303/133030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 9 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 9)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 9)
  constructor <;> linarith

theorem G18_27_interval :
    ((((6506697/133030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 27) ∧
    (baezDuarteGramEntry 18 27 ≤ (((6533303/133030000) : ℚ) : ℝ)) := by
  rw [G18_27_formula]
  exact vasyuninBEntry_18_27_eval

def interval_18_27 : NamedVasyuninInterval :=
{
  h := 18
  k := 27
  lower := (6506697/133030000)
  upper := (6533303/133030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_27_interval
}

theorem G18_28_formula : baezDuarteGramEntry 18 28 = vasyuninBEntry 18 28 := vasyuninBEntry_correct_axiom 18 28

theorem vasyuninBEntry_18_28_eval :
    ((((46282289/977110000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 28) ∧
    (vasyuninBEntry 18 28 ≤ (((46477711/977110000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_14_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 14 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G18_28_interval :
    ((((46282289/977110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 28) ∧
    (baezDuarteGramEntry 18 28 ≤ (((46477711/977110000) : ℚ) : ℝ)) := by
  rw [G18_28_formula]
  exact vasyuninBEntry_18_28_eval

def interval_18_28 : NamedVasyuninInterval :=
{
  h := 18
  k := 28
  lower := (46282289/977110000)
  upper := (46477711/977110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_28_interval
}

theorem G18_29_formula : baezDuarteGramEntry 18 29 = vasyuninBEntry 18 29 := vasyuninBEntry_correct_axiom 18 29

theorem vasyuninBEntry_18_29_eval :
    ((((29725781/642190000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 29) ∧
    (vasyuninBEntry 18 29 ≤ (((29854219/642190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1829_formula_bound
  constructor <;> linarith

theorem G18_29_interval :
    ((((29725781/642190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 29) ∧
    (baezDuarteGramEntry 18 29 ≤ (((29854219/642190000) : ℚ) : ℝ)) := by
  rw [G18_29_formula]
  exact vasyuninBEntry_18_29_eval

def interval_18_29 : NamedVasyuninInterval :=
{
  h := 18
  k := 29
  lower := (29725781/642190000)
  upper := (29854219/642190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_29_interval
}

theorem G18_30_formula : baezDuarteGramEntry 18 30 = vasyuninBEntry 18 30 := vasyuninBEntry_correct_axiom 18 30

theorem vasyuninBEntry_18_30_eval :
    ((((40251521/884790000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 30) ∧
    (vasyuninBEntry 18 30 ≤ (((40428479/884790000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 5 6 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G18_30_interval :
    ((((40251521/884790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 30) ∧
    (baezDuarteGramEntry 18 30 ≤ (((40428479/884790000) : ℚ) : ℝ)) := by
  rw [G18_30_formula]
  exact vasyuninBEntry_18_30_eval

def interval_18_30 : NamedVasyuninInterval :=
{
  h := 18
  k := 30
  lower := (40251521/884790000)
  upper := (40428479/884790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_30_interval
}

theorem G18_31_formula : baezDuarteGramEntry 18 31 = vasyuninBEntry 18 31 := vasyuninBEntry_correct_axiom 18 31

theorem vasyuninBEntry_18_31_eval :
    ((((12506921/280790000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 31) ∧
    (vasyuninBEntry 18 31 ≤ (((12563079/280790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1831_formula_bound
  constructor <;> linarith

theorem G18_31_interval :
    ((((12506921/280790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 31) ∧
    (baezDuarteGramEntry 18 31 ≤ (((12563079/280790000) : ℚ) : ℝ)) := by
  rw [G18_31_formula]
  exact vasyuninBEntry_18_31_eval

def interval_18_31 : NamedVasyuninInterval :=
{
  h := 18
  k := 31
  lower := (12506921/280790000)
  upper := (12563079/280790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_31_interval
}

theorem G18_32_formula : baezDuarteGramEntry 18 32 = vasyuninBEntry 18 32 := vasyuninBEntry_correct_axiom 18 32

theorem vasyuninBEntry_18_32_eval :
    ((((6014277/137230000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 32) ∧
    (vasyuninBEntry 18 32 ≤ (((6041723/137230000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_16_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 16 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G18_32_interval :
    ((((6014277/137230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 32) ∧
    (baezDuarteGramEntry 18 32 ≤ (((6041723/137230000) : ℚ) : ℝ)) := by
  rw [G18_32_formula]
  exact vasyuninBEntry_18_32_eval

def interval_18_32 : NamedVasyuninInterval :=
{
  h := 18
  k := 32
  lower := (6014277/137230000)
  upper := (6041723/137230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_32_interval
}

theorem G18_33_formula : baezDuarteGramEntry 18 33 = vasyuninBEntry 18 33 := vasyuninBEntry_correct_axiom 18 33

theorem vasyuninBEntry_18_33_eval :
    ((((18606963/430370000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 33) ∧
    (vasyuninBEntry 18 33 ≤ (((18693037/430370000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_6_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 6 11 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G18_33_interval :
    ((((18606963/430370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 33) ∧
    (baezDuarteGramEntry 18 33 ≤ (((18693037/430370000) : ℚ) : ℝ)) := by
  rw [G18_33_formula]
  exact vasyuninBEntry_18_33_eval

def interval_18_33 : NamedVasyuninInterval :=
{
  h := 18
  k := 33
  lower := (18606963/430370000)
  upper := (18693037/430370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_33_interval
}

theorem G18_34_formula : baezDuarteGramEntry 18 34 = vasyuninBEntry 18 34 := vasyuninBEntry_correct_axiom 18 34

theorem vasyuninBEntry_18_34_eval :
    ((((12949723/302770000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 34) ∧
    (vasyuninBEntry 18 34 ≤ (((13010277/302770000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_17_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 17 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G18_34_interval :
    ((((12949723/302770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 34) ∧
    (baezDuarteGramEntry 18 34 ≤ (((13010277/302770000) : ℚ) : ℝ)) := by
  rw [G18_34_formula]
  exact vasyuninBEntry_18_34_eval

def interval_18_34 : NamedVasyuninInterval :=
{
  h := 18
  k := 34
  lower := (12949723/302770000)
  upper := (13010277/302770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_34_interval
}

theorem G18_35_formula : baezDuarteGramEntry 18 35 = vasyuninBEntry 18 35 := vasyuninBEntry_correct_axiom 18 35

theorem vasyuninBEntry_18_35_eval :
    ((((11263511/264890000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 35) ∧
    (vasyuninBEntry 18 35 ≤ (((11316489/264890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1835_formula_bound
  constructor <;> linarith

theorem G18_35_interval :
    ((((11263511/264890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 35) ∧
    (baezDuarteGramEntry 18 35 ≤ (((11316489/264890000) : ℚ) : ℝ)) := by
  rw [G18_35_formula]
  exact vasyuninBEntry_18_35_eval

def interval_18_35 : NamedVasyuninInterval :=
{
  h := 18
  k := 35
  lower := (11263511/264890000)
  upper := (11316489/264890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_35_interval
}

theorem G18_36_formula : baezDuarteGramEntry 18 36 = vasyuninBEntry 18 36 := vasyuninBEntry_correct_axiom 18 36

theorem vasyuninBEntry_18_36_eval :
    ((((18890863/441370000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 36) ∧
    (vasyuninBEntry 18 36 ≤ (((18979137/441370000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 18 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 18)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 18)
  constructor <;> linarith

theorem G18_36_interval :
    ((((18890863/441370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 36) ∧
    (baezDuarteGramEntry 18 36 ≤ (((18979137/441370000) : ℚ) : ℝ)) := by
  rw [G18_36_formula]
  exact vasyuninBEntry_18_36_eval

def interval_18_36 : NamedVasyuninInterval :=
{
  h := 18
  k := 36
  lower := (18890863/441370000)
  upper := (18979137/441370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_36_interval
}

theorem G18_37_formula : baezDuarteGramEntry 18 37 = vasyuninBEntry 18 37 := vasyuninBEntry_correct_axiom 18 37

theorem vasyuninBEntry_18_37_eval :
    ((((3880549/94510000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 37) ∧
    (vasyuninBEntry 18 37 ≤ (((3899451/94510000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1837_formula_bound
  constructor <;> linarith

theorem G18_37_interval :
    ((((3880549/94510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 37) ∧
    (baezDuarteGramEntry 18 37 ≤ (((3899451/94510000) : ℚ) : ℝ)) := by
  rw [G18_37_formula]
  exact vasyuninBEntry_18_37_eval

def interval_18_37 : NamedVasyuninInterval :=
{
  h := 18
  k := 37
  lower := (3880549/94510000)
  upper := (3899451/94510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_37_interval
}

theorem G18_38_formula : baezDuarteGramEntry 18 38 = vasyuninBEntry 18 38 := vasyuninBEntry_correct_axiom 18 38

theorem vasyuninBEntry_18_38_eval :
    ((((12518609/313910000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 38) ∧
    (vasyuninBEntry 18 38 ≤ (((12581391/313910000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 19 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G18_38_interval :
    ((((12518609/313910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 38) ∧
    (baezDuarteGramEntry 18 38 ≤ (((12581391/313910000) : ℚ) : ℝ)) := by
  rw [G18_38_formula]
  exact vasyuninBEntry_18_38_eval

def interval_18_38 : NamedVasyuninInterval :=
{
  h := 18
  k := 38
  lower := (12518609/313910000)
  upper := (12581391/313910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_38_interval
}

theorem G18_39_formula : baezDuarteGramEntry 18 39 = vasyuninBEntry 18 39 := vasyuninBEntry_correct_axiom 18 39

theorem vasyuninBEntry_18_39_eval :
    ((((8106667/208330000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 39) ∧
    (vasyuninBEntry 18 39 ≤ (((8148333/208330000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_6_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 6 13 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G18_39_interval :
    ((((8106667/208330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 39) ∧
    (baezDuarteGramEntry 18 39 ≤ (((8148333/208330000) : ℚ) : ℝ)) := by
  rw [G18_39_formula]
  exact vasyuninBEntry_18_39_eval

def interval_18_39 : NamedVasyuninInterval :=
{
  h := 18
  k := 39
  lower := (8106667/208330000)
  upper := (8148333/208330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_39_interval
}

theorem G18_40_formula : baezDuarteGramEntry 18 40 = vasyuninBEntry 18 40 := vasyuninBEntry_correct_axiom 18 40

theorem vasyuninBEntry_18_40_eval :
    ((((3453427/90730000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 40) ∧
    (vasyuninBEntry 18 40 ≤ (((3471573/90730000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_20_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 20 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G18_40_interval :
    ((((3453427/90730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 40) ∧
    (baezDuarteGramEntry 18 40 ≤ (((3471573/90730000) : ℚ) : ℝ)) := by
  rw [G18_40_formula]
  exact vasyuninBEntry_18_40_eval

def interval_18_40 : NamedVasyuninInterval :=
{
  h := 18
  k := 40
  lower := (3453427/90730000)
  upper := (3471573/90730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_40_interval
}

theorem G18_41_formula : baezDuarteGramEntry 18 41 = vasyuninBEntry 18 41 := vasyuninBEntry_correct_axiom 18 41

theorem vasyuninBEntry_18_41_eval :
    ((((25242343/676570000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 41) ∧
    (vasyuninBEntry 18 41 ≤ (((25377657/676570000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1841_formula_bound
  constructor <;> linarith

theorem G18_41_interval :
    ((((25242343/676570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 41) ∧
    (baezDuarteGramEntry 18 41 ≤ (((25377657/676570000) : ℚ) : ℝ)) := by
  rw [G18_41_formula]
  exact vasyuninBEntry_18_41_eval

def interval_18_41 : NamedVasyuninInterval :=
{
  h := 18
  k := 41
  lower := (25242343/676570000)
  upper := (25377657/676570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_41_interval
}

theorem G18_42_formula : baezDuarteGramEntry 18 42 = vasyuninBEntry 18 42 := vasyuninBEntry_correct_axiom 18 42

theorem vasyuninBEntry_18_42_eval :
    ((((5816149/158510000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 42) ∧
    (vasyuninBEntry 18 42 ≤ (((5847851/158510000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 7 6 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G18_42_interval :
    ((((5816149/158510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 42) ∧
    (baezDuarteGramEntry 18 42 ≤ (((5847851/158510000) : ℚ) : ℝ)) := by
  rw [G18_42_formula]
  exact vasyuninBEntry_18_42_eval

def interval_18_42 : NamedVasyuninInterval :=
{
  h := 18
  k := 42
  lower := (5816149/158510000)
  upper := (5847851/158510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_42_interval
}

theorem G18_43_formula : baezDuarteGramEntry 18 43 = vasyuninBEntry 18 43 := vasyuninBEntry_correct_axiom 18 43

theorem vasyuninBEntry_18_43_eval :
    ((((19595569/544310000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 43) ∧
    (vasyuninBEntry 18 43 ≤ (((19704431/544310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1843_formula_bound
  constructor <;> linarith

theorem G18_43_interval :
    ((((19595569/544310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 43) ∧
    (baezDuarteGramEntry 18 43 ≤ (((19704431/544310000) : ℚ) : ℝ)) := by
  rw [G18_43_formula]
  exact vasyuninBEntry_18_43_eval

def interval_18_43 : NamedVasyuninInterval :=
{
  h := 18
  k := 43
  lower := (19595569/544310000)
  upper := (19704431/544310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_43_interval
}

theorem G18_44_formula : baezDuarteGramEntry 18 44 = vasyuninBEntry 18 44 := vasyuninBEntry_correct_axiom 18 44

theorem vasyuninBEntry_18_44_eval :
    ((((10071583/284170000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 44) ∧
    (vasyuninBEntry 18 44 ≤ (((10128417/284170000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_22_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 22 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G18_44_interval :
    ((((10071583/284170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 44) ∧
    (baezDuarteGramEntry 18 44 ≤ (((10128417/284170000) : ℚ) : ℝ)) := by
  rw [G18_44_formula]
  exact vasyuninBEntry_18_44_eval

def interval_18_44 : NamedVasyuninInterval :=
{
  h := 18
  k := 44
  lower := (10071583/284170000)
  upper := (10128417/284170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_44_interval
}

theorem G18_45_formula : baezDuarteGramEntry 18 45 = vasyuninBEntry 18 45 := vasyuninBEntry_correct_axiom 18 45

theorem vasyuninBEntry_18_45_eval :
    ((((12135383/346170000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 45) ∧
    (vasyuninBEntry 18 45 ≤ (((12204617/346170000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 5 9 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 9)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 9)
  constructor <;> linarith

theorem G18_45_interval :
    ((((12135383/346170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 45) ∧
    (baezDuarteGramEntry 18 45 ≤ (((12204617/346170000) : ℚ) : ℝ)) := by
  rw [G18_45_formula]
  exact vasyuninBEntry_18_45_eval

def interval_18_45 : NamedVasyuninInterval :=
{
  h := 18
  k := 45
  lower := (12135383/346170000)
  upper := (12204617/346170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_45_interval
}

theorem G18_46_formula : baezDuarteGramEntry 18 46 = vasyuninBEntry 18 46 := vasyuninBEntry_correct_axiom 18 46

theorem vasyuninBEntry_18_46_eval :
    ((((9133427/265730000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 46) ∧
    (vasyuninBEntry 18 46 ≤ (((9186573/265730000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 23 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G18_46_interval :
    ((((9133427/265730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 46) ∧
    (baezDuarteGramEntry 18 46 ≤ (((9186573/265730000) : ℚ) : ℝ)) := by
  rw [G18_46_formula]
  exact vasyuninBEntry_18_46_eval

def interval_18_46 : NamedVasyuninInterval :=
{
  h := 18
  k := 46
  lower := (9133427/265730000)
  upper := (9186573/265730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_46_interval
}

theorem G18_47_formula : baezDuarteGramEntry 18 47 = vasyuninBEntry 18 47 := vasyuninBEntry_correct_axiom 18 47

theorem vasyuninBEntry_18_47_eval :
    ((((25624307/756930000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 47) ∧
    (vasyuninBEntry 18 47 ≤ (((25775693/756930000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1847_formula_bound
  constructor <;> linarith

theorem G18_47_interval :
    ((((25624307/756930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 47) ∧
    (baezDuarteGramEntry 18 47 ≤ (((25775693/756930000) : ℚ) : ℝ)) := by
  rw [G18_47_formula]
  exact vasyuninBEntry_18_47_eval

def interval_18_47 : NamedVasyuninInterval :=
{
  h := 18
  k := 47
  lower := (25624307/756930000)
  upper := (25775693/756930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_47_interval
}

theorem G18_48_formula : baezDuarteGramEntry 18 48 = vasyuninBEntry 18 48 := vasyuninBEntry_correct_axiom 18 48

theorem vasyuninBEntry_18_48_eval :
    ((((12128731/362690000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 48) ∧
    (vasyuninBEntry 18 48 ≤ (((12201269/362690000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 8 6 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G18_48_interval :
    ((((12128731/362690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 48) ∧
    (baezDuarteGramEntry 18 48 ≤ (((12201269/362690000) : ℚ) : ℝ)) := by
  rw [G18_48_formula]
  exact vasyuninBEntry_18_48_eval

def interval_18_48 : NamedVasyuninInterval :=
{
  h := 18
  k := 48
  lower := (12128731/362690000)
  upper := (12201269/362690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_48_interval
}

theorem G18_49_formula : baezDuarteGramEntry 18 49 = vasyuninBEntry 18 49 := vasyuninBEntry_correct_axiom 18 49

theorem vasyuninBEntry_18_49_eval :
    ((((23957329/726710000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 49) ∧
    (vasyuninBEntry 18 49 ≤ (((24102671/726710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1849_formula_bound
  constructor <;> linarith

theorem G18_49_interval :
    ((((23957329/726710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 49) ∧
    (baezDuarteGramEntry 18 49 ≤ (((24102671/726710000) : ℚ) : ℝ)) := by
  rw [G18_49_formula]
  exact vasyuninBEntry_18_49_eval

def interval_18_49 : NamedVasyuninInterval :=
{
  h := 18
  k := 49
  lower := (23957329/726710000)
  upper := (24102671/726710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_49_interval
}

theorem G18_50_formula : baezDuarteGramEntry 18 50 = vasyuninBEntry 18 50 := vasyuninBEntry_correct_axiom 18 50

theorem vasyuninBEntry_18_50_eval :
    ((((11404999/350010000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 50) ∧
    (vasyuninBEntry 18 50 ≤ (((11475001/350010000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 25 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G18_50_interval :
    ((((11404999/350010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 50) ∧
    (baezDuarteGramEntry 18 50 ≤ (((11475001/350010000) : ℚ) : ℝ)) := by
  rw [G18_50_formula]
  exact vasyuninBEntry_18_50_eval

def interval_18_50 : NamedVasyuninInterval :=
{
  h := 18
  k := 50
  lower := (11404999/350010000)
  upper := (11475001/350010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_50_interval
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

end RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
