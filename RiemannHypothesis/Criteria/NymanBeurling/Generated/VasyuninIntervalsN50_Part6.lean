import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBoundsGenerated
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPrimitiveBounds
import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part1
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part2
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part3
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part4
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part5

namespace RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Certificates.Generated

theorem G23_41_formula : baezDuarteGramEntry 23 41 = vasyuninBEntry 23 41 := vasyuninBEntry_correct_axiom 23 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_23_41_eval :
    ((((31268649/913510000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 41) ∧
    (vasyuninBEntry 23 41 ≤ (((31451351/913510000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2341_formula_bound
  constructor <;> linarith

theorem G23_41_interval :
    ((((31268649/913510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 41) ∧
    (baezDuarteGramEntry 23 41 ≤ (((31451351/913510000) : ℚ) : ℝ)) := by
  rw [G23_41_formula]
  exact vasyuninBEntry_23_41_eval

def interval_23_41 : NamedVasyuninInterval :=
{
  h := 23
  k := 41
  lower := (31268649/913510000)
  upper := (31451351/913510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_41_interval
}

theorem G23_42_formula : baezDuarteGramEntry 23 42 = vasyuninBEntry 23 42 := vasyuninBEntry_correct_axiom 23 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_23_42_eval :
    ((((27887639/823610000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 42) ∧
    (vasyuninBEntry 23 42 ≤ (((28052361/823610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2342_formula_bound
  constructor <;> linarith

theorem G23_42_interval :
    ((((27887639/823610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 42) ∧
    (baezDuarteGramEntry 23 42 ≤ (((28052361/823610000) : ℚ) : ℝ)) := by
  rw [G23_42_formula]
  exact vasyuninBEntry_23_42_eval

def interval_23_42 : NamedVasyuninInterval :=
{
  h := 23
  k := 42
  lower := (27887639/823610000)
  upper := (28052361/823610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_42_interval
}

theorem G23_43_formula : baezDuarteGramEntry 23 43 = vasyuninBEntry 23 43 := vasyuninBEntry_correct_axiom 23 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_23_43_eval :
    ((((17517797/522030000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 43) ∧
    (vasyuninBEntry 23 43 ≤ (((17622203/522030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2343_formula_bound
  constructor <;> linarith

theorem G23_43_interval :
    ((((17517797/522030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 43) ∧
    (baezDuarteGramEntry 23 43 ≤ (((17622203/522030000) : ℚ) : ℝ)) := by
  rw [G23_43_formula]
  exact vasyuninBEntry_23_43_eval

def interval_23_43 : NamedVasyuninInterval :=
{
  h := 23
  k := 43
  lower := (17517797/522030000)
  upper := (17622203/522030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_43_interval
}

theorem G23_44_formula : baezDuarteGramEntry 23 44 = vasyuninBEntry 23 44 := vasyuninBEntry_correct_axiom 23 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_23_44_eval :
    ((((26031919/780810000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 44) ∧
    (vasyuninBEntry 23 44 ≤ (((26188081/780810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2344_formula_bound
  constructor <;> linarith

theorem G23_44_interval :
    ((((26031919/780810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 44) ∧
    (baezDuarteGramEntry 23 44 ≤ (((26188081/780810000) : ℚ) : ℝ)) := by
  rw [G23_44_formula]
  exact vasyuninBEntry_23_44_eval

def interval_23_44 : NamedVasyuninInterval :=
{
  h := 23
  k := 44
  lower := (26031919/780810000)
  upper := (26188081/780810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_44_interval
}

theorem G23_45_formula : baezDuarteGramEntry 23 45 = vasyuninBEntry 23 45 := vasyuninBEntry_correct_axiom 23 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_23_45_eval :
    ((((30757487/925130000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 45) ∧
    (vasyuninBEntry 23 45 ≤ (((30942513/925130000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2345_formula_bound
  constructor <;> linarith

theorem G23_45_interval :
    ((((30757487/925130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 45) ∧
    (baezDuarteGramEntry 23 45 ≤ (((30942513/925130000) : ℚ) : ℝ)) := by
  rw [G23_45_formula]
  exact vasyuninBEntry_23_45_eval

def interval_23_45 : NamedVasyuninInterval :=
{
  h := 23
  k := 45
  lower := (30757487/925130000)
  upper := (30942513/925130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_45_interval
}

theorem G23_46_formula : baezDuarteGramEntry 23 46 = vasyuninBEntry 23 46 := vasyuninBEntry_correct_axiom 23 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_23_46_eval :
    ((((5880433/175670000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 46) ∧
    (vasyuninBEntry 23 46 ≤ (((5915567/175670000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 23 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 23)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 23)
  constructor <;> linarith

theorem G23_46_interval :
    ((((5880433/175670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 46) ∧
    (baezDuarteGramEntry 23 46 ≤ (((5915567/175670000) : ℚ) : ℝ)) := by
  rw [G23_46_formula]
  exact vasyuninBEntry_23_46_eval

def interval_23_46 : NamedVasyuninInterval :=
{
  h := 23
  k := 46
  lower := (5880433/175670000)
  upper := (5915567/175670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_46_interval
}

theorem G23_47_formula : baezDuarteGramEntry 23 47 = vasyuninBEntry 23 47 := vasyuninBEntry_correct_axiom 23 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_23_47_eval :
    ((((13916977/430230000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 47) ∧
    (vasyuninBEntry 23 47 ≤ (((14003023/430230000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2347_formula_bound
  constructor <;> linarith

theorem G23_47_interval :
    ((((13916977/430230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 47) ∧
    (baezDuarteGramEntry 23 47 ≤ (((14003023/430230000) : ℚ) : ℝ)) := by
  rw [G23_47_formula]
  exact vasyuninBEntry_23_47_eval

def interval_23_47 : NamedVasyuninInterval :=
{
  h := 23
  k := 47
  lower := (13916977/430230000)
  upper := (14003023/430230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_47_interval
}

theorem G23_48_formula : baezDuarteGramEntry 23 48 = vasyuninBEntry 23 48 := vasyuninBEntry_correct_axiom 23 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_23_48_eval :
    ((((25987663/823370000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 48) ∧
    (vasyuninBEntry 23 48 ≤ (((26152337/823370000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2348_formula_bound
  constructor <;> linarith

theorem G23_48_interval :
    ((((25987663/823370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 48) ∧
    (baezDuarteGramEntry 23 48 ≤ (((26152337/823370000) : ℚ) : ℝ)) := by
  rw [G23_48_formula]
  exact vasyuninBEntry_23_48_eval

def interval_23_48 : NamedVasyuninInterval :=
{
  h := 23
  k := 48
  lower := (25987663/823370000)
  upper := (26152337/823370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_48_interval
}

theorem G23_49_formula : baezDuarteGramEntry 23 49 = vasyuninBEntry 23 49 := vasyuninBEntry_correct_axiom 23 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_23_49_eval :
    ((((11482847/371530000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 49) ∧
    (vasyuninBEntry 23 49 ≤ (((11557153/371530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2349_formula_bound
  constructor <;> linarith

theorem G23_49_interval :
    ((((11482847/371530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 49) ∧
    (baezDuarteGramEntry 23 49 ≤ (((11557153/371530000) : ℚ) : ℝ)) := by
  rw [G23_49_formula]
  exact vasyuninBEntry_23_49_eval

def interval_23_49 : NamedVasyuninInterval :=
{
  h := 23
  k := 49
  lower := (11482847/371530000)
  upper := (11557153/371530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_49_interval
}

theorem G23_50_formula : baezDuarteGramEntry 23 50 = vasyuninBEntry 23 50 := vasyuninBEntry_correct_axiom 23 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_23_50_eval :
    ((((19107011/629890000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 50) ∧
    (vasyuninBEntry 23 50 ≤ (((19232989/629890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2350_formula_bound
  constructor <;> linarith

theorem G23_50_interval :
    ((((19107011/629890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 50) ∧
    (baezDuarteGramEntry 23 50 ≤ (((19232989/629890000) : ℚ) : ℝ)) := by
  rw [G23_50_formula]
  exact vasyuninBEntry_23_50_eval

def interval_23_50 : NamedVasyuninInterval :=
{
  h := 23
  k := 50
  lower := (19107011/629890000)
  upper := (19232989/629890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_50_interval
}

theorem G24_1_formula : baezDuarteGramEntry 24 1 = vasyuninBEntry 1 24 := by
  rw [baezDuarteGramEntry_symm 24 1]
  exact G1_24_formula

theorem G24_1_interval :
    ((((71586897/631030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 1) ∧
    (baezDuarteGramEntry 24 1 ≤ (((71713103/631030000) : ℚ) : ℝ)) := by
  rw [G24_1_formula]
  exact vasyuninBEntry_1_24_eval

def interval_24_1 : NamedVasyuninInterval :=
{
  h := 24
  k := 1
  lower := (71586897/631030000)
  upper := (71713103/631030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_1_interval
}

theorem G24_2_formula : baezDuarteGramEntry 24 2 = vasyuninBEntry 2 24 := by
  rw [baezDuarteGramEntry_symm 24 2]
  exact G2_24_formula

theorem G24_2_interval :
    ((((23820997/240030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 2) ∧
    (baezDuarteGramEntry 24 2 ≤ (((23869003/240030000) : ℚ) : ℝ)) := by
  rw [G24_2_formula]
  exact vasyuninBEntry_2_24_eval

def interval_24_2 : NamedVasyuninInterval :=
{
  h := 24
  k := 2
  lower := (23820997/240030000)
  upper := (23869003/240030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_2_interval
}

theorem G24_3_formula : baezDuarteGramEntry 24 3 = vasyuninBEntry 3 24 := by
  rw [baezDuarteGramEntry_symm 24 3]
  exact G3_24_formula

theorem G24_3_interval :
    ((((14941087/164130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 3) ∧
    (baezDuarteGramEntry 24 3 ≤ (((14973913/164130000) : ℚ) : ℝ)) := by
  rw [G24_3_formula]
  exact vasyuninBEntry_3_24_eval

def interval_24_3 : NamedVasyuninInterval :=
{
  h := 24
  k := 3
  lower := (14941087/164130000)
  upper := (14973913/164130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_3_interval
}

theorem G24_4_formula : baezDuarteGramEntry 24 4 = vasyuninBEntry 4 24 := by
  rw [baezDuarteGramEntry_symm 24 4]
  exact G4_24_formula

theorem G24_4_interval :
    ((((71156557/834430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 4) ∧
    (baezDuarteGramEntry 24 4 ≤ (((71323443/834430000) : ℚ) : ℝ)) := by
  rw [G24_4_formula]
  exact vasyuninBEntry_4_24_eval

def interval_24_4 : NamedVasyuninInterval :=
{
  h := 24
  k := 4
  lower := (71156557/834430000)
  upper := (71323443/834430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_4_interval
}

theorem G24_5_formula : baezDuarteGramEntry 24 5 = vasyuninBEntry 5 24 := by
  rw [baezDuarteGramEntry_symm 24 5]
  exact G5_24_formula

theorem G24_5_interval :
    ((((1583011/19890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 5) ∧
    (baezDuarteGramEntry 24 5 ≤ (((1586989/19890000) : ℚ) : ℝ)) := by
  rw [G24_5_formula]
  exact vasyuninBEntry_5_24_eval

def interval_24_5 : NamedVasyuninInterval :=
{
  h := 24
  k := 5
  lower := (1583011/19890000)
  upper := (1586989/19890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_5_interval
}

theorem G24_6_formula : baezDuarteGramEntry 24 6 = vasyuninBEntry 6 24 := by
  rw [baezDuarteGramEntry_symm 24 6]
  exact G6_24_formula

theorem G24_6_interval :
    ((((25287287/327130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 6) ∧
    (baezDuarteGramEntry 24 6 ≤ (((25352713/327130000) : ℚ) : ℝ)) := by
  rw [G24_6_formula]
  exact vasyuninBEntry_6_24_eval

def interval_24_6 : NamedVasyuninInterval :=
{
  h := 24
  k := 6
  lower := (25287287/327130000)
  upper := (25352713/327130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_6_interval
}

theorem G24_7_formula : baezDuarteGramEntry 24 7 = vasyuninBEntry 7 24 := by
  rw [baezDuarteGramEntry_symm 24 7]
  exact G7_24_formula

theorem G24_7_interval :
    ((((7952993/110070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 7) ∧
    (baezDuarteGramEntry 24 7 ≤ (((7975007/110070000) : ℚ) : ℝ)) := by
  rw [G24_7_formula]
  exact vasyuninBEntry_7_24_eval

def interval_24_7 : NamedVasyuninInterval :=
{
  h := 24
  k := 7
  lower := (7952993/110070000)
  upper := (7975007/110070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_7_interval
}

theorem G24_8_formula : baezDuarteGramEntry 24 8 = vasyuninBEntry 8 24 := by
  rw [baezDuarteGramEntry_symm 24 8]
  exact G8_24_formula

theorem G24_8_interval :
    ((((67346171/938290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 8) ∧
    (baezDuarteGramEntry 24 8 ≤ (((67533829/938290000) : ℚ) : ℝ)) := by
  rw [G24_8_formula]
  exact vasyuninBEntry_8_24_eval

def interval_24_8 : NamedVasyuninInterval :=
{
  h := 24
  k := 8
  lower := (67346171/938290000)
  upper := (67533829/938290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_8_interval
}

theorem G24_9_formula : baezDuarteGramEntry 24 9 = vasyuninBEntry 9 24 := by
  rw [baezDuarteGramEntry_symm 24 9]
  exact G9_24_formula

theorem G24_9_interval :
    ((((4010887/59880000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 9) ∧
    (baezDuarteGramEntry 24 9 ≤ (((4022863/59880000) : ℚ) : ℝ)) := by
  rw [G24_9_formula]
  exact vasyuninBEntry_9_24_eval

def interval_24_9 : NamedVasyuninInterval :=
{
  h := 24
  k := 9
  lower := (4010887/59880000)
  upper := (4022863/59880000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_9_interval
}

theorem G24_10_formula : baezDuarteGramEntry 24 10 = vasyuninBEntry 10 24 := by
  rw [baezDuarteGramEntry_symm 24 10]
  exact G10_24_formula

theorem G24_10_interval :
    ((((59527979/920210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 10) ∧
    (baezDuarteGramEntry 24 10 ≤ (((59712021/920210000) : ℚ) : ℝ)) := by
  rw [G24_10_formula]
  exact vasyuninBEntry_10_24_eval

def interval_24_10 : NamedVasyuninInterval :=
{
  h := 24
  k := 10
  lower := (59527979/920210000)
  upper := (59712021/920210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_10_interval
}

theorem G24_11_formula : baezDuarteGramEntry 24 11 = vasyuninBEntry 11 24 := by
  rw [baezDuarteGramEntry_symm 24 11]
  exact G11_24_formula

theorem G24_11_interval :
    ((((27746189/438110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 11) ∧
    (baezDuarteGramEntry 24 11 ≤ (((27833811/438110000) : ℚ) : ℝ)) := by
  rw [G24_11_formula]
  exact vasyuninBEntry_11_24_eval

def interval_24_11 : NamedVasyuninInterval :=
{
  h := 24
  k := 11
  lower := (27746189/438110000)
  upper := (27833811/438110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_11_interval
}

theorem G24_12_formula : baezDuarteGramEntry 24 12 = vasyuninBEntry 12 24 := by
  rw [baezDuarteGramEntry_symm 24 12]
  exact G12_24_formula

theorem G24_12_interval :
    ((((14038151/218490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 12) ∧
    (baezDuarteGramEntry 24 12 ≤ (((14081849/218490000) : ℚ) : ℝ)) := by
  rw [G24_12_formula]
  exact vasyuninBEntry_12_24_eval

def interval_24_12 : NamedVasyuninInterval :=
{
  h := 24
  k := 12
  lower := (14038151/218490000)
  upper := (14081849/218490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_12_interval
}

theorem G24_13_formula : baezDuarteGramEntry 24 13 = vasyuninBEntry 13 24 := by
  rw [baezDuarteGramEntry_symm 24 13]
  exact G13_24_formula

theorem G24_13_interval :
    ((((3969603/66470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 13) ∧
    (baezDuarteGramEntry 24 13 ≤ (((3982897/66470000) : ℚ) : ℝ)) := by
  rw [G24_13_formula]
  exact vasyuninBEntry_13_24_eval

def interval_24_13 : NamedVasyuninInterval :=
{
  h := 24
  k := 13
  lower := (3969603/66470000)
  upper := (3982897/66470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_13_interval
}

theorem G24_14_formula : baezDuarteGramEntry 24 14 = vasyuninBEntry 14 24 := by
  rw [baezDuarteGramEntry_symm 24 14]
  exact G14_24_formula

theorem G24_14_interval :
    ((((47357571/824290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 14) ∧
    (baezDuarteGramEntry 24 14 ≤ (((47522429/824290000) : ℚ) : ℝ)) := by
  rw [G24_14_formula]
  exact vasyuninBEntry_14_24_eval

def interval_24_14 : NamedVasyuninInterval :=
{
  h := 24
  k := 14
  lower := (47357571/824290000)
  upper := (47522429/824290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_14_interval
}

theorem G24_15_formula : baezDuarteGramEntry 24 15 = vasyuninBEntry 15 24 := by
  rw [baezDuarteGramEntry_symm 24 15]
  exact G15_24_formula

theorem G24_15_interval :
    ((((837001/14990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 15) ∧
    (baezDuarteGramEntry 24 15 ≤ (((839999/14990000) : ℚ) : ℝ)) := by
  rw [G24_15_formula]
  exact vasyuninBEntry_15_24_eval

def interval_24_15 : NamedVasyuninInterval :=
{
  h := 24
  k := 15
  lower := (837001/14990000)
  upper := (839999/14990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_15_interval
}

theorem G24_16_formula : baezDuarteGramEntry 24 16 = vasyuninBEntry 16 24 := by
  rw [baezDuarteGramEntry_symm 24 16]
  exact G16_24_formula

theorem G24_16_interval :
    ((((7321697/133030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 16) ∧
    (baezDuarteGramEntry 24 16 ≤ (((7348303/133030000) : ℚ) : ℝ)) := by
  rw [G24_16_formula]
  exact vasyuninBEntry_16_24_eval

def interval_24_16 : NamedVasyuninInterval :=
{
  h := 24
  k := 16
  lower := (7321697/133030000)
  upper := (7348303/133030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_16_interval
}

theorem G24_17_formula : baezDuarteGramEntry 24 17 = vasyuninBEntry 17 24 := by
  rw [baezDuarteGramEntry_symm 24 17]
  exact G17_24_formula

theorem G24_17_interval :
    ((((48798413/915870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 17) ∧
    (baezDuarteGramEntry 24 17 ≤ (((48981587/915870000) : ℚ) : ℝ)) := by
  rw [G24_17_formula]
  exact vasyuninBEntry_17_24_eval

def interval_24_17 : NamedVasyuninInterval :=
{
  h := 24
  k := 17
  lower := (48798413/915870000)
  upper := (48981587/915870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_17_interval
}

theorem G24_18_formula : baezDuarteGramEntry 24 18 = vasyuninBEntry 18 24 := by
  rw [baezDuarteGramEntry_symm 24 18]
  exact G18_24_formula

theorem G24_18_interval :
    ((((6307979/120210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 18) ∧
    (baezDuarteGramEntry 24 18 ≤ (((6332021/120210000) : ℚ) : ℝ)) := by
  rw [G24_18_formula]
  exact vasyuninBEntry_18_24_eval

def interval_24_18 : NamedVasyuninInterval :=
{
  h := 24
  k := 18
  lower := (6307979/120210000)
  upper := (6332021/120210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_18_interval
}

theorem G24_19_formula : baezDuarteGramEntry 24 19 = vasyuninBEntry 19 24 := by
  rw [baezDuarteGramEntry_symm 24 19]
  exact G19_24_formula

theorem G24_19_interval :
    ((((48465881/941190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 19) ∧
    (baezDuarteGramEntry 24 19 ≤ (((48654119/941190000) : ℚ) : ℝ)) := by
  rw [G24_19_formula]
  exact vasyuninBEntry_19_24_eval

def interval_24_19 : NamedVasyuninInterval :=
{
  h := 24
  k := 19
  lower := (48465881/941190000)
  upper := (48654119/941190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_19_interval
}

theorem G24_20_formula : baezDuarteGramEntry 24 20 = vasyuninBEntry 20 24 := by
  rw [baezDuarteGramEntry_symm 24 20]
  exact G20_24_formula

theorem G24_20_interval :
    ((((8732859/171410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 20) ∧
    (baezDuarteGramEntry 24 20 ≤ (((8767141/171410000) : ℚ) : ℝ)) := by
  rw [G24_20_formula]
  exact vasyuninBEntry_20_24_eval

def interval_24_20 : NamedVasyuninInterval :=
{
  h := 24
  k := 20
  lower := (8732859/171410000)
  upper := (8767141/171410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_20_interval
}

theorem G24_21_formula : baezDuarteGramEntry 24 21 = vasyuninBEntry 21 24 := by
  rw [baezDuarteGramEntry_symm 24 21]
  exact G21_24_formula

theorem G24_21_interval :
    ((((9139929/180710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 21) ∧
    (baezDuarteGramEntry 24 21 ≤ (((9176071/180710000) : ℚ) : ℝ)) := by
  rw [G24_21_formula]
  exact vasyuninBEntry_21_24_eval

def interval_24_21 : NamedVasyuninInterval :=
{
  h := 24
  k := 21
  lower := (9139929/180710000)
  upper := (9176071/180710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_21_interval
}

theorem G24_22_formula : baezDuarteGramEntry 24 22 = vasyuninBEntry 22 24 := by
  rw [baezDuarteGramEntry_symm 24 22]
  exact G22_24_formula

theorem G24_22_interval :
    ((((15369579/304210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 22) ∧
    (baezDuarteGramEntry 24 22 ≤ (((15430421/304210000) : ℚ) : ℝ)) := by
  rw [G24_22_formula]
  exact vasyuninBEntry_22_24_eval

def interval_24_22 : NamedVasyuninInterval :=
{
  h := 24
  k := 22
  lower := (15369579/304210000)
  upper := (15430421/304210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_22_interval
}

theorem G24_23_formula : baezDuarteGramEntry 24 23 = vasyuninBEntry 23 24 := by
  rw [baezDuarteGramEntry_symm 24 23]
  exact G23_24_formula

theorem G24_23_interval :
    ((((21238281/417190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 23) ∧
    (baezDuarteGramEntry 24 23 ≤ (((21321719/417190000) : ℚ) : ℝ)) := by
  rw [G24_23_formula]
  exact vasyuninBEntry_23_24_eval

def interval_24_23 : NamedVasyuninInterval :=
{
  h := 24
  k := 23
  lower := (21238281/417190000)
  upper := (21321719/417190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_23_interval
}

theorem G24_24_formula_eq : baezDuarteGramEntry 24 24 = (1 / (24 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 24 := by norm_num
  rw [baez_duarte_diagonal_scaling 24 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G24_24_log_gamma_interval :
  ((((49605383/946170000) : ℚ) : ℝ) ≤ (1 / (24 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (24 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((49794617/946170000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 24 (by norm_num)
  constructor
  · have : ((((49605383/946170000) : ℚ) : ℝ) ≤ (1 / (24 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (24 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((49794617/946170000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G24_24_interval : ((((49605383/946170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 24) ∧ (baezDuarteGramEntry 24 24 ≤ (((49794617/946170000) : ℚ) : ℝ)) := by
  rw [G24_24_formula_eq]
  exact G24_24_log_gamma_interval

def interval_24_24 : NamedVasyuninInterval :=
{
  h := 24
  k := 24
  lower := (49605383/946170000)
  upper := (49794617/946170000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G24_24_interval
}

theorem G24_25_formula : baezDuarteGramEntry 24 25 = vasyuninBEntry 24 25 := vasyuninBEntry_correct_axiom 24 25 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_25_eval :
    ((((7857929/160710000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 25) ∧
    (vasyuninBEntry 24 25 ≤ (((7890071/160710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2425_formula_bound
  constructor <;> linarith

theorem G24_25_interval :
    ((((7857929/160710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 25) ∧
    (baezDuarteGramEntry 24 25 ≤ (((7890071/160710000) : ℚ) : ℝ)) := by
  rw [G24_25_formula]
  exact vasyuninBEntry_24_25_eval

def interval_24_25 : NamedVasyuninInterval :=
{
  h := 24
  k := 25
  lower := (7857929/160710000)
  upper := (7890071/160710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_25_interval
}

theorem G24_26_formula : baezDuarteGramEntry 24 26 = vasyuninBEntry 24 26 := vasyuninBEntry_correct_axiom 24 26 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_26_eval :
    ((((653599/14010000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 26) ∧
    (vasyuninBEntry 24 26 ≤ (((656401/14010000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_12_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 12 13 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G24_26_interval :
    ((((653599/14010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 26) ∧
    (baezDuarteGramEntry 24 26 ≤ (((656401/14010000) : ℚ) : ℝ)) := by
  rw [G24_26_formula]
  exact vasyuninBEntry_24_26_eval

def interval_24_26 : NamedVasyuninInterval :=
{
  h := 24
  k := 26
  lower := (653599/14010000)
  upper := (656401/14010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_26_interval
}

theorem G24_27_formula : baezDuarteGramEntry 24 27 = vasyuninBEntry 24 27 := vasyuninBEntry_correct_axiom 24 27 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_27_eval :
    ((((43872281/977190000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 27) ∧
    (vasyuninBEntry 24 27 ≤ (((44067719/977190000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_8_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 8 9 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G24_27_interval :
    ((((43872281/977190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 27) ∧
    (baezDuarteGramEntry 24 27 ≤ (((44067719/977190000) : ℚ) : ℝ)) := by
  rw [G24_27_formula]
  exact vasyuninBEntry_24_27_eval

def interval_24_27 : NamedVasyuninInterval :=
{
  h := 24
  k := 27
  lower := (43872281/977190000)
  upper := (44067719/977190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_27_interval
}

theorem G24_28_formula : baezDuarteGramEntry 24 28 = vasyuninBEntry 24 28 := vasyuninBEntry_correct_axiom 24 28 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_28_eval :
    ((((20393059/469410000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 28) ∧
    (vasyuninBEntry 24 28 ≤ (((20486941/469410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_6_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 6 7 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G24_28_interval :
    ((((20393059/469410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 28) ∧
    (baezDuarteGramEntry 24 28 ≤ (((20486941/469410000) : ℚ) : ℝ)) := by
  rw [G24_28_formula]
  exact vasyuninBEntry_24_28_eval

def interval_24_28 : NamedVasyuninInterval :=
{
  h := 24
  k := 28
  lower := (20393059/469410000)
  upper := (20486941/469410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_28_interval
}

theorem G24_29_formula : baezDuarteGramEntry 24 29 = vasyuninBEntry 24 29 := vasyuninBEntry_correct_axiom 24 29 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_29_eval :
    ((((3269247/77530000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 29) ∧
    (vasyuninBEntry 24 29 ≤ (((3284753/77530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2429_formula_bound
  constructor <;> linarith

theorem G24_29_interval :
    ((((3269247/77530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 29) ∧
    (baezDuarteGramEntry 24 29 ≤ (((3284753/77530000) : ℚ) : ℝ)) := by
  rw [G24_29_formula]
  exact vasyuninBEntry_24_29_eval

def interval_24_29 : NamedVasyuninInterval :=
{
  h := 24
  k := 29
  lower := (3269247/77530000)
  upper := (3284753/77530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_29_interval
}

theorem G24_30_formula : baezDuarteGramEntry 24 30 = vasyuninBEntry 24 30 := vasyuninBEntry_correct_axiom 24 30 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_30_eval :
    ((((19552461/475390000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 30) ∧
    (vasyuninBEntry 24 30 ≤ (((19647539/475390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 5 6 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G24_30_interval :
    ((((19552461/475390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 30) ∧
    (baezDuarteGramEntry 24 30 ≤ (((19647539/475390000) : ℚ) : ℝ)) := by
  rw [G24_30_formula]
  exact vasyuninBEntry_24_30_eval

def interval_24_30 : NamedVasyuninInterval :=
{
  h := 24
  k := 30
  lower := (19552461/475390000)
  upper := (19647539/475390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_30_interval
}

theorem G24_31_formula : baezDuarteGramEntry 24 31 = vasyuninBEntry 24 31 := vasyuninBEntry_correct_axiom 24 31 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_31_eval :
    ((((27082421/675790000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 31) ∧
    (vasyuninBEntry 24 31 ≤ (((27217579/675790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2431_formula_bound
  constructor <;> linarith

theorem G24_31_interval :
    ((((27082421/675790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 31) ∧
    (baezDuarteGramEntry 24 31 ≤ (((27217579/675790000) : ℚ) : ℝ)) := by
  rw [G24_31_formula]
  exact vasyuninBEntry_24_31_eval

def interval_24_31 : NamedVasyuninInterval :=
{
  h := 24
  k := 31
  lower := (27082421/675790000)
  upper := (27217579/675790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_31_interval
}

theorem G24_32_formula : baezDuarteGramEntry 24 32 = vasyuninBEntry 24 32 := vasyuninBEntry_correct_axiom 24 32 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_32_eval :
    ((((1575993/40070000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 32) ∧
    (vasyuninBEntry 24 32 ≤ (((1584007/40070000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 4 8 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 8)
  constructor <;> linarith

theorem G24_32_interval :
    ((((1575993/40070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 32) ∧
    (baezDuarteGramEntry 24 32 ≤ (((1584007/40070000) : ℚ) : ℝ)) := by
  rw [G24_32_formula]
  exact vasyuninBEntry_24_32_eval

def interval_24_32 : NamedVasyuninInterval :=
{
  h := 24
  k := 32
  lower := (1575993/40070000)
  upper := (1584007/40070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_32_interval
}

theorem G24_33_formula : baezDuarteGramEntry 24 33 = vasyuninBEntry 24 33 := vasyuninBEntry_correct_axiom 24 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_33_eval :
    ((((9253387/241130000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 33) ∧
    (vasyuninBEntry 24 33 ≤ (((9301613/241130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_8_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 8 11 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G24_33_interval :
    ((((9253387/241130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 33) ∧
    (baezDuarteGramEntry 24 33 ≤ (((9301613/241130000) : ℚ) : ℝ)) := by
  rw [G24_33_formula]
  exact vasyuninBEntry_24_33_eval

def interval_24_33 : NamedVasyuninInterval :=
{
  h := 24
  k := 33
  lower := (9253387/241130000)
  upper := (9301613/241130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_33_interval
}

theorem G24_34_formula : baezDuarteGramEntry 24 34 = vasyuninBEntry 24 34 := vasyuninBEntry_correct_axiom 24 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_34_eval :
    ((((6335663/168370000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 34) ∧
    (vasyuninBEntry 24 34 ≤ (((6369337/168370000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_12_17_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 12 17 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G24_34_interval :
    ((((6335663/168370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 34) ∧
    (baezDuarteGramEntry 24 34 ≤ (((6369337/168370000) : ℚ) : ℝ)) := by
  rw [G24_34_formula]
  exact vasyuninBEntry_24_34_eval

def interval_24_34 : NamedVasyuninInterval :=
{
  h := 24
  k := 34
  lower := (6335663/168370000)
  upper := (6369337/168370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_34_interval
}

theorem G24_35_formula : baezDuarteGramEntry 24 35 = vasyuninBEntry 24 35 := vasyuninBEntry_correct_axiom 24 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_35_eval :
    ((((27575481/745190000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 35) ∧
    (vasyuninBEntry 24 35 ≤ (((27724519/745190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2435_formula_bound
  constructor <;> linarith

theorem G24_35_interval :
    ((((27575481/745190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 35) ∧
    (baezDuarteGramEntry 24 35 ≤ (((27724519/745190000) : ℚ) : ℝ)) := by
  rw [G24_35_formula]
  exact vasyuninBEntry_24_35_eval

def interval_24_35 : NamedVasyuninInterval :=
{
  h := 24
  k := 35
  lower := (27575481/745190000)
  upper := (27724519/745190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_35_interval
}

theorem G24_36_formula : baezDuarteGramEntry 24 36 = vasyuninBEntry 24 36 := vasyuninBEntry_correct_axiom 24 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_36_eval :
    ((((4876697/133030000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 36) ∧
    (vasyuninBEntry 24 36 ≤ (((4903303/133030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 12 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 12)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 12)
  constructor <;> linarith

theorem G24_36_interval :
    ((((4876697/133030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 36) ∧
    (baezDuarteGramEntry 24 36 ≤ (((4903303/133030000) : ℚ) : ℝ)) := by
  rw [G24_36_formula]
  exact vasyuninBEntry_24_36_eval

def interval_24_36 : NamedVasyuninInterval :=
{
  h := 24
  k := 36
  lower := (4876697/133030000)
  upper := (4903303/133030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_36_interval
}

theorem G24_37_formula : baezDuarteGramEntry 24 37 = vasyuninBEntry 24 37 := vasyuninBEntry_correct_axiom 24 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_37_eval :
    ((((14419643/403570000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 37) ∧
    (vasyuninBEntry 24 37 ≤ (((14500357/403570000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2437_formula_bound
  constructor <;> linarith

theorem G24_37_interval :
    ((((14419643/403570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 37) ∧
    (baezDuarteGramEntry 24 37 ≤ (((14500357/403570000) : ℚ) : ℝ)) := by
  rw [G24_37_formula]
  exact vasyuninBEntry_24_37_eval

def interval_24_37 : NamedVasyuninInterval :=
{
  h := 24
  k := 37
  lower := (14419643/403570000)
  upper := (14500357/403570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_37_interval
}

theorem G24_38_formula : baezDuarteGramEntry 24 38 = vasyuninBEntry 24 38 := vasyuninBEntry_correct_axiom 24 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_38_eval :
    ((((1483271/42290000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 38) ∧
    (vasyuninBEntry 24 38 ≤ (((1491729/42290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_12_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 12 19 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G24_38_interval :
    ((((1483271/42290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 38) ∧
    (baezDuarteGramEntry 24 38 ≤ (((1491729/42290000) : ℚ) : ℝ)) := by
  rw [G24_38_formula]
  exact vasyuninBEntry_24_38_eval

def interval_24_38 : NamedVasyuninInterval :=
{
  h := 24
  k := 38
  lower := (1483271/42290000)
  upper := (1491729/42290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_38_interval
}

theorem G24_39_formula : baezDuarteGramEntry 24 39 = vasyuninBEntry 24 39 := vasyuninBEntry_correct_axiom 24 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_39_eval :
    ((((18207249/527510000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 39) ∧
    (vasyuninBEntry 24 39 ≤ (((18312751/527510000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_8_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 8 13 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G24_39_interval :
    ((((18207249/527510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 39) ∧
    (baezDuarteGramEntry 24 39 ≤ (((18312751/527510000) : ℚ) : ℝ)) := by
  rw [G24_39_formula]
  exact vasyuninBEntry_24_39_eval

def interval_24_39 : NamedVasyuninInterval :=
{
  h := 24
  k := 39
  lower := (18207249/527510000)
  upper := (18312751/527510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_39_interval
}

theorem G24_40_formula : baezDuarteGramEntry 24 40 = vasyuninBEntry 24 40 := vasyuninBEntry_correct_axiom 24 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_40_eval :
    ((((10055507/294930000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 40) ∧
    (vasyuninBEntry 24 40 ≤ (((10114493/294930000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 5 8 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 8)
  constructor <;> linarith

theorem G24_40_interval :
    ((((10055507/294930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 40) ∧
    (baezDuarteGramEntry 24 40 ≤ (((10114493/294930000) : ℚ) : ℝ)) := by
  rw [G24_40_formula]
  exact vasyuninBEntry_24_40_eval

def interval_24_40 : NamedVasyuninInterval :=
{
  h := 24
  k := 40
  lower := (10055507/294930000)
  upper := (10114493/294930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_40_interval
}

theorem G24_41_formula : baezDuarteGramEntry 24 41 = vasyuninBEntry 24 41 := vasyuninBEntry_correct_axiom 24 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_41_eval :
    ((((27677457/825430000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 41) ∧
    (vasyuninBEntry 24 41 ≤ (((27842543/825430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2441_formula_bound
  constructor <;> linarith

theorem G24_41_interval :
    ((((27677457/825430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 41) ∧
    (baezDuarteGramEntry 24 41 ≤ (((27842543/825430000) : ℚ) : ℝ)) := by
  rw [G24_41_formula]
  exact vasyuninBEntry_24_41_eval

def interval_24_41 : NamedVasyuninInterval :=
{
  h := 24
  k := 41
  lower := (27677457/825430000)
  upper := (27842543/825430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_41_interval
}

theorem G24_42_formula : baezDuarteGramEntry 24 42 = vasyuninBEntry 24 42 := vasyuninBEntry_correct_axiom 24 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_42_eval :
    ((((24635657/743430000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 42) ∧
    (vasyuninBEntry 24 42 ≤ (((24784343/743430000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 7 6 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G24_42_interval :
    ((((24635657/743430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 42) ∧
    (baezDuarteGramEntry 24 42 ≤ (((24784343/743430000) : ℚ) : ℝ)) := by
  rw [G24_42_formula]
  exact vasyuninBEntry_24_42_eval

def interval_24_42 : NamedVasyuninInterval :=
{
  h := 24
  k := 42
  lower := (24635657/743430000)
  upper := (24784343/743430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_42_interval
}

theorem G24_43_formula : baezDuarteGramEntry 24 43 = vasyuninBEntry 24 43 := vasyuninBEntry_correct_axiom 24 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_43_eval :
    ((((22710597/694030000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 43) ∧
    (vasyuninBEntry 24 43 ≤ (((22849403/694030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2443_formula_bound
  constructor <;> linarith

theorem G24_43_interval :
    ((((22710597/694030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 43) ∧
    (baezDuarteGramEntry 24 43 ≤ (((22849403/694030000) : ℚ) : ℝ)) := by
  rw [G24_43_formula]
  exact vasyuninBEntry_24_43_eval

def interval_24_43 : NamedVasyuninInterval :=
{
  h := 24
  k := 43
  lower := (22710597/694030000)
  upper := (22849403/694030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_43_interval
}

theorem G24_44_formula : baezDuarteGramEntry 24 44 = vasyuninBEntry 24 44 := vasyuninBEntry_correct_axiom 24 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_44_eval :
    ((((22749787/702130000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 44) ∧
    (vasyuninBEntry 24 44 ≤ (((22890213/702130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_6_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 6 11 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G24_44_interval :
    ((((22749787/702130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 44) ∧
    (baezDuarteGramEntry 24 44 ≤ (((22890213/702130000) : ℚ) : ℝ)) := by
  rw [G24_44_formula]
  exact vasyuninBEntry_24_44_eval

def interval_24_44 : NamedVasyuninInterval :=
{
  h := 24
  k := 44
  lower := (22749787/702130000)
  upper := (22890213/702130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_44_interval
}

theorem G24_45_formula : baezDuarteGramEntry 24 45 = vasyuninBEntry 24 45 := vasyuninBEntry_correct_axiom 24 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_45_eval :
    ((((13054367/406330000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 45) ∧
    (vasyuninBEntry 24 45 ≤ (((13135633/406330000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_8_15_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 8 15 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G24_45_interval :
    ((((13054367/406330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 45) ∧
    (baezDuarteGramEntry 24 45 ≤ (((13135633/406330000) : ℚ) : ℝ)) := by
  rw [G24_45_formula]
  exact vasyuninBEntry_24_45_eval

def interval_24_45 : NamedVasyuninInterval :=
{
  h := 24
  k := 45
  lower := (13054367/406330000)
  upper := (13135633/406330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_45_interval
}

theorem G24_46_formula : baezDuarteGramEntry 24 46 = vasyuninBEntry 24 46 := vasyuninBEntry_correct_axiom 24 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_46_eval :
    ((((21383041/669590000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 46) ∧
    (vasyuninBEntry 24 46 ≤ (((21516959/669590000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_12_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 12 23 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G24_46_interval :
    ((((21383041/669590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 46) ∧
    (baezDuarteGramEntry 24 46 ≤ (((21516959/669590000) : ℚ) : ℝ)) := by
  rw [G24_46_formula]
  exact vasyuninBEntry_24_46_eval

def interval_24_46 : NamedVasyuninInterval :=
{
  h := 24
  k := 46
  lower := (21383041/669590000)
  upper := (21516959/669590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_46_interval
}

theorem G24_47_formula : baezDuarteGramEntry 24 47 = vasyuninBEntry 24 47 := vasyuninBEntry_correct_axiom 24 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_47_eval :
    ((((1207709/37910000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 47) ∧
    (vasyuninBEntry 24 47 ≤ (((1215291/37910000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2447_formula_bound
  constructor <;> linarith

theorem G24_47_interval :
    ((((1207709/37910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 47) ∧
    (baezDuarteGramEntry 24 47 ≤ (((1215291/37910000) : ℚ) : ℝ)) := by
  rw [G24_47_formula]
  exact vasyuninBEntry_24_47_eval

def interval_24_47 : NamedVasyuninInterval :=
{
  h := 24
  k := 47
  lower := (1207709/37910000)
  upper := (1215291/37910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_47_interval
}

theorem G24_48_formula : baezDuarteGramEntry 24 48 = vasyuninBEntry 24 48 := vasyuninBEntry_correct_axiom 24 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_48_eval :
    ((((7008151/218490000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 48) ∧
    (vasyuninBEntry 24 48 ≤ (((7051849/218490000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 24 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 24)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 24)
  constructor <;> linarith

theorem G24_48_interval :
    ((((7008151/218490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 48) ∧
    (baezDuarteGramEntry 24 48 ≤ (((7051849/218490000) : ℚ) : ℝ)) := by
  rw [G24_48_formula]
  exact vasyuninBEntry_24_48_eval

def interval_24_48 : NamedVasyuninInterval :=
{
  h := 24
  k := 48
  lower := (7008151/218490000)
  upper := (7051849/218490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_48_interval
}

theorem G24_49_formula : baezDuarteGramEntry 24 49 = vasyuninBEntry 24 49 := vasyuninBEntry_correct_axiom 24 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_49_eval :
    ((((3671917/118330000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 49) ∧
    (vasyuninBEntry 24 49 ≤ (((3695583/118330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2449_formula_bound
  constructor <;> linarith

theorem G24_49_interval :
    ((((3671917/118330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 49) ∧
    (baezDuarteGramEntry 24 49 ≤ (((3695583/118330000) : ℚ) : ℝ)) := by
  rw [G24_49_formula]
  exact vasyuninBEntry_24_49_eval

def interval_24_49 : NamedVasyuninInterval :=
{
  h := 24
  k := 49
  lower := (3671917/118330000)
  upper := (3695583/118330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_49_interval
}

theorem G24_50_formula : baezDuarteGramEntry 24 50 = vasyuninBEntry 24 50 := vasyuninBEntry_correct_axiom 24 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_24_50_eval :
    ((((838433/27670000) : ℚ) : ℝ) ≤ vasyuninBEntry 24 50) ∧
    (vasyuninBEntry 24 50 ≤ (((843967/27670000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_12_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 12 25 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G24_50_interval :
    ((((838433/27670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 24 50) ∧
    (baezDuarteGramEntry 24 50 ≤ (((843967/27670000) : ℚ) : ℝ)) := by
  rw [G24_50_formula]
  exact vasyuninBEntry_24_50_eval

def interval_24_50 : NamedVasyuninInterval :=
{
  h := 24
  k := 50
  lower := (838433/27670000)
  upper := (843967/27670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G24_50_interval
}

theorem G25_1_formula : baezDuarteGramEntry 25 1 = vasyuninBEntry 1 25 := by
  rw [baezDuarteGramEntry_symm 25 1]
  exact G1_25_formula

theorem G25_1_interval :
    ((((21774153/198470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 1) ∧
    (baezDuarteGramEntry 25 1 ≤ (((21813847/198470000) : ℚ) : ℝ)) := by
  rw [G25_1_formula]
  exact vasyuninBEntry_1_25_eval

def interval_25_1 : NamedVasyuninInterval :=
{
  h := 25
  k := 1
  lower := (21774153/198470000)
  upper := (21813847/198470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_1_interval
}

theorem G25_2_formula : baezDuarteGramEntry 25 2 = vasyuninBEntry 2 25 := by
  rw [baezDuarteGramEntry_symm 25 2]
  exact G2_25_formula

theorem G25_2_interval :
    ((((42475557/444430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 2) ∧
    (baezDuarteGramEntry 25 2 ≤ (((42564443/444430000) : ℚ) : ℝ)) := by
  rw [G25_2_formula]
  exact vasyuninBEntry_2_25_eval

def interval_25_2 : NamedVasyuninInterval :=
{
  h := 25
  k := 2
  lower := (42475557/444430000)
  upper := (42564443/444430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_2_interval
}

theorem G25_3_formula : baezDuarteGramEntry 25 3 = vasyuninBEntry 3 25 := by
  rw [baezDuarteGramEntry_symm 25 3]
  exact G3_25_formula

theorem G25_3_interval :
    ((((58183431/665690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 3) ∧
    (baezDuarteGramEntry 25 3 ≤ (((58316569/665690000) : ℚ) : ℝ)) := by
  rw [G25_3_formula]
  exact vasyuninBEntry_3_25_eval

def interval_25_3 : NamedVasyuninInterval :=
{
  h := 25
  k := 3
  lower := (58183431/665690000)
  upper := (58316569/665690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_3_interval
}

theorem G25_4_formula : baezDuarteGramEntry 25 4 = vasyuninBEntry 4 25 := by
  rw [baezDuarteGramEntry_symm 25 4]
  exact G4_25_formula

theorem G25_4_interval :
    ((((11106401/135990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 4) ∧
    (baezDuarteGramEntry 25 4 ≤ (((11133599/135990000) : ℚ) : ℝ)) := by
  rw [G25_4_formula]
  exact vasyuninBEntry_4_25_eval

def interval_25_4 : NamedVasyuninInterval :=
{
  h := 25
  k := 4
  lower := (11106401/135990000)
  upper := (11133599/135990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_4_interval
}

theorem G25_5_formula : baezDuarteGramEntry 25 5 = vasyuninBEntry 5 25 := by
  rw [baezDuarteGramEntry_symm 25 5]
  exact G5_25_formula

theorem G25_5_interval :
    ((((59434187/758130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 5) ∧
    (baezDuarteGramEntry 25 5 ≤ (((59585813/758130000) : ℚ) : ℝ)) := by
  rw [G25_5_formula]
  exact vasyuninBEntry_5_25_eval

def interval_25_5 : NamedVasyuninInterval :=
{
  h := 25
  k := 5
  lower := (59434187/758130000)
  upper := (59585813/758130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_5_interval
}

theorem G25_6_formula : baezDuarteGramEntry 25 6 = vasyuninBEntry 6 25 := by
  rw [baezDuarteGramEntry_symm 25 6]
  exact G6_25_formula

theorem G25_6_interval :
    ((((4757297/64530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 6) ∧
    (baezDuarteGramEntry 25 6 ≤ (((4770203/64530000) : ℚ) : ℝ)) := by
  rw [G25_6_formula]
  exact vasyuninBEntry_6_25_eval

def interval_25_6 : NamedVasyuninInterval :=
{
  h := 25
  k := 6
  lower := (4757297/64530000)
  upper := (4770203/64530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_6_interval
}

theorem G25_7_formula : baezDuarteGramEntry 25 7 = vasyuninBEntry 7 25 := by
  rw [baezDuarteGramEntry_symm 25 7]
  exact G7_25_formula

theorem G25_7_interval :
    ((((5122699/73010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 7) ∧
    (baezDuarteGramEntry 25 7 ≤ (((5137301/73010000) : ℚ) : ℝ)) := by
  rw [G25_7_formula]
  exact vasyuninBEntry_7_25_eval

def interval_25_7 : NamedVasyuninInterval :=
{
  h := 25
  k := 7
  lower := (5122699/73010000)
  upper := (5137301/73010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_7_interval
}

theorem G25_8_formula : baezDuarteGramEntry 25 8 = vasyuninBEntry 8 25 := by
  rw [baezDuarteGramEntry_symm 25 8]
  exact G8_25_formula

theorem G25_8_interval :
    ((((39971401/585990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 8) ∧
    (baezDuarteGramEntry 25 8 ≤ (((40088599/585990000) : ℚ) : ℝ)) := by
  rw [G25_8_formula]
  exact vasyuninBEntry_8_25_eval

def interval_25_8 : NamedVasyuninInterval :=
{
  h := 25
  k := 8
  lower := (39971401/585990000)
  upper := (40088599/585990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_8_interval
}

theorem G25_9_formula : baezDuarteGramEntry 25 9 = vasyuninBEntry 9 25 := by
  rw [baezDuarteGramEntry_symm 25 9]
  exact G9_25_formula

theorem G25_9_interval :
    ((((31516713/482870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 9) ∧
    (baezDuarteGramEntry 25 9 ≤ (((31613287/482870000) : ℚ) : ℝ)) := by
  rw [G25_9_formula]
  exact vasyuninBEntry_9_25_eval

def interval_25_9 : NamedVasyuninInterval :=
{
  h := 25
  k := 9
  lower := (31516713/482870000)
  upper := (31613287/482870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_9_interval
}

theorem G25_10_formula : baezDuarteGramEntry 25 10 = vasyuninBEntry 10 25 := by
  rw [baezDuarteGramEntry_symm 25 10]
  exact G10_25_formula

theorem G25_10_interval :
    ((((7290461/115390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 10) ∧
    (baezDuarteGramEntry 25 10 ≤ (((7313539/115390000) : ℚ) : ℝ)) := by
  rw [G25_10_formula]
  exact vasyuninBEntry_10_25_eval

def interval_25_10 : NamedVasyuninInterval :=
{
  h := 25
  k := 10
  lower := (7290461/115390000)
  upper := (7313539/115390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_10_interval
}

theorem G25_11_formula : baezDuarteGramEntry 25 11 = vasyuninBEntry 11 25 := by
  rw [baezDuarteGramEntry_symm 25 11]
  exact G11_25_formula

theorem G25_11_interval :
    ((((360611/5890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 11) ∧
    (baezDuarteGramEntry 25 11 ≤ (((361789/5890000) : ℚ) : ℝ)) := by
  rw [G25_11_formula]
  exact vasyuninBEntry_11_25_eval

def interval_25_11 : NamedVasyuninInterval :=
{
  h := 25
  k := 11
  lower := (360611/5890000)
  upper := (361789/5890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_11_interval
}

theorem G25_12_formula : baezDuarteGramEntry 25 12 = vasyuninBEntry 12 25 := by
  rw [baezDuarteGramEntry_symm 25 12]
  exact G12_25_formula

theorem G25_12_interval :
    ((((32336729/532710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 12) ∧
    (baezDuarteGramEntry 25 12 ≤ (((32443271/532710000) : ℚ) : ℝ)) := by
  rw [G25_12_formula]
  exact vasyuninBEntry_12_25_eval

def interval_25_12 : NamedVasyuninInterval :=
{
  h := 25
  k := 12
  lower := (32336729/532710000)
  upper := (32443271/532710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_12_interval
}

theorem G25_13_formula : baezDuarteGramEntry 25 13 = vasyuninBEntry 13 25 := by
  rw [baezDuarteGramEntry_symm 25 13]
  exact G13_25_formula

theorem G25_13_interval :
    ((((13729231/232690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 13) ∧
    (baezDuarteGramEntry 25 13 ≤ (((13775769/232690000) : ℚ) : ℝ)) := by
  rw [G25_13_formula]
  exact vasyuninBEntry_13_25_eval

def interval_25_13 : NamedVasyuninInterval :=
{
  h := 25
  k := 13
  lower := (13729231/232690000)
  upper := (13775769/232690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_13_interval
}

theorem G25_14_formula : baezDuarteGramEntry 25 14 = vasyuninBEntry 14 25 := by
  rw [baezDuarteGramEntry_symm 25 14]
  exact G14_25_formula

theorem G25_14_interval :
    ((((8859251/157490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 14) ∧
    (baezDuarteGramEntry 25 14 ≤ (((8890749/157490000) : ℚ) : ℝ)) := by
  rw [G25_14_formula]
  exact vasyuninBEntry_14_25_eval

def interval_25_14 : NamedVasyuninInterval :=
{
  h := 25
  k := 14
  lower := (8859251/157490000)
  upper := (8890749/157490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_14_interval
}

theorem G25_15_formula : baezDuarteGramEntry 25 15 = vasyuninBEntry 15 25 := by
  rw [baezDuarteGramEntry_symm 25 15]
  exact G15_25_formula

theorem G25_15_interval :
    ((((40356103/738970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 15) ∧
    (baezDuarteGramEntry 25 15 ≤ (((40503897/738970000) : ℚ) : ℝ)) := by
  rw [G25_15_formula]
  exact vasyuninBEntry_15_25_eval

def interval_25_15 : NamedVasyuninInterval :=
{
  h := 25
  k := 15
  lower := (40356103/738970000)
  upper := (40503897/738970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_15_interval
}

theorem G25_16_formula : baezDuarteGramEntry 25 16 = vasyuninBEntry 16 25 := by
  rw [baezDuarteGramEntry_symm 25 16]
  exact G16_25_formula

theorem G25_16_interval :
    ((((4537709/85410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 16) ∧
    (baezDuarteGramEntry 25 16 ≤ (((4554791/85410000) : ℚ) : ℝ)) := by
  rw [G25_16_formula]
  exact vasyuninBEntry_16_25_eval

def interval_25_16 : NamedVasyuninInterval :=
{
  h := 25
  k := 16
  lower := (4537709/85410000)
  upper := (4554791/85410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_16_interval
}

theorem G25_17_formula : baezDuarteGramEntry 25 17 = vasyuninBEntry 17 25 := by
  rw [baezDuarteGramEntry_symm 25 17]
  exact G17_25_formula

theorem G25_17_interval :
    ((((47688419/915810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 17) ∧
    (baezDuarteGramEntry 25 17 ≤ (((47871581/915810000) : ℚ) : ℝ)) := by
  rw [G25_17_formula]
  exact vasyuninBEntry_17_25_eval

def interval_25_17 : NamedVasyuninInterval :=
{
  h := 25
  k := 17
  lower := (47688419/915810000)
  upper := (47871581/915810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_17_interval
}

theorem G25_18_formula : baezDuarteGramEntry 25 18 = vasyuninBEntry 18 25 := by
  rw [baezDuarteGramEntry_symm 25 18]
  exact G18_25_formula

theorem G25_18_interval :
    ((((50820057/999430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 18) ∧
    (baezDuarteGramEntry 25 18 ≤ (((51019943/999430000) : ℚ) : ℝ)) := by
  rw [G25_18_formula]
  exact vasyuninBEntry_18_25_eval

def interval_25_18 : NamedVasyuninInterval :=
{
  h := 25
  k := 18
  lower := (50820057/999430000)
  upper := (51019943/999430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_18_interval
}

theorem G25_19_formula : baezDuarteGramEntry 25 19 = vasyuninBEntry 19 25 := by
  rw [baezDuarteGramEntry_symm 25 19]
  exact G19_25_formula

theorem G25_19_interval :
    ((((23597829/471710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 19) ∧
    (baezDuarteGramEntry 25 19 ≤ (((23692171/471710000) : ℚ) : ℝ)) := by
  rw [G25_19_formula]
  exact vasyuninBEntry_19_25_eval

def interval_25_19 : NamedVasyuninInterval :=
{
  h := 25
  k := 19
  lower := (23597829/471710000)
  upper := (23692171/471710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_19_interval
}

theorem G25_20_formula : baezDuarteGramEntry 25 20 = vasyuninBEntry 20 25 := by
  rw [baezDuarteGramEntry_symm 25 20]
  exact G20_25_formula

theorem G25_20_interval :
    ((((23472461/475390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 20) ∧
    (baezDuarteGramEntry 25 20 ≤ (((23567539/475390000) : ℚ) : ℝ)) := by
  rw [G25_20_formula]
  exact vasyuninBEntry_20_25_eval

def interval_25_20 : NamedVasyuninInterval :=
{
  h := 25
  k := 20
  lower := (23472461/475390000)
  upper := (23567539/475390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_20_interval
}

theorem G25_21_formula : baezDuarteGramEntry 25 21 = vasyuninBEntry 21 25 := by
  rw [baezDuarteGramEntry_symm 25 21]
  exact G21_25_formula

theorem G25_21_interval :
    ((((42063797/862030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 21) ∧
    (baezDuarteGramEntry 25 21 ≤ (((42236203/862030000) : ℚ) : ℝ)) := by
  rw [G25_21_formula]
  exact vasyuninBEntry_21_25_eval

def interval_25_21 : NamedVasyuninInterval :=
{
  h := 25
  k := 21
  lower := (42063797/862030000)
  upper := (42236203/862030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_21_interval
}

theorem G25_22_formula : baezDuarteGramEntry 25 22 = vasyuninBEntry 22 25 := by
  rw [baezDuarteGramEntry_symm 25 22]
  exact G22_25_formula

theorem G25_22_interval :
    ((((9163611/188890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 22) ∧
    (baezDuarteGramEntry 25 22 ≤ (((9201389/188890000) : ℚ) : ℝ)) := by
  rw [G25_22_formula]
  exact vasyuninBEntry_22_25_eval

def interval_25_22 : NamedVasyuninInterval :=
{
  h := 25
  k := 22
  lower := (9163611/188890000)
  upper := (9201389/188890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_22_interval
}

theorem G25_23_formula : baezDuarteGramEntry 25 23 = vasyuninBEntry 23 25 := by
  rw [baezDuarteGramEntry_symm 25 23]
  exact G23_25_formula

theorem G25_23_interval :
    ((((40755977/840230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 23) ∧
    (baezDuarteGramEntry 25 23 ≤ (((40924023/840230000) : ℚ) : ℝ)) := by
  rw [G25_23_formula]
  exact vasyuninBEntry_23_25_eval

def interval_25_23 : NamedVasyuninInterval :=
{
  h := 25
  k := 23
  lower := (40755977/840230000)
  upper := (40924023/840230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_23_interval
}

theorem G25_24_formula : baezDuarteGramEntry 25 24 = vasyuninBEntry 24 25 := by
  rw [baezDuarteGramEntry_symm 25 24]
  exact G24_25_formula

theorem G25_24_interval :
    ((((7857929/160710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 24) ∧
    (baezDuarteGramEntry 25 24 ≤ (((7890071/160710000) : ℚ) : ℝ)) := by
  rw [G25_24_formula]
  exact vasyuninBEntry_24_25_eval

def interval_25_24 : NamedVasyuninInterval :=
{
  h := 25
  k := 24
  lower := (7857929/160710000)
  upper := (7890071/160710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_24_interval
}

theorem G25_25_formula_eq : baezDuarteGramEntry 25 25 = (1 / (25 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 25 := by norm_num
  rw [baez_duarte_diagonal_scaling 25 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G25_25_log_gamma_interval :
  ((((12273113/243870000) : ℚ) : ℝ) ≤ (1 / (25 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (25 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((12321887/243870000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 25 (by norm_num)
  constructor
  · have : ((((12273113/243870000) : ℚ) : ℝ) ≤ (1 / (25 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (25 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((12321887/243870000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G25_25_interval : ((((12273113/243870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 25) ∧ (baezDuarteGramEntry 25 25 ≤ (((12321887/243870000) : ℚ) : ℝ)) := by
  rw [G25_25_formula_eq]
  exact G25_25_log_gamma_interval

def interval_25_25 : NamedVasyuninInterval :=
{
  h := 25
  k := 25
  lower := (12273113/243870000)
  upper := (12321887/243870000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G25_25_interval
}

theorem G25_26_formula : baezDuarteGramEntry 25 26 = vasyuninBEntry 25 26 := vasyuninBEntry_correct_axiom 25 26 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_26_eval :
    ((((7300479/155210000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 26) ∧
    (vasyuninBEntry 25 26 ≤ (((7331521/155210000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2526_formula_bound
  constructor <;> linarith

theorem G25_26_interval :
    ((((7300479/155210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 26) ∧
    (baezDuarteGramEntry 25 26 ≤ (((7331521/155210000) : ℚ) : ℝ)) := by
  rw [G25_26_formula]
  exact vasyuninBEntry_25_26_eval

def interval_25_26 : NamedVasyuninInterval :=
{
  h := 25
  k := 26
  lower := (7300479/155210000)
  upper := (7331521/155210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_26_interval
}

theorem G25_27_formula : baezDuarteGramEntry 25 27 = vasyuninBEntry 25 27 := vasyuninBEntry_correct_axiom 25 27 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_27_eval :
    ((((15819791/352090000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 27) ∧
    (vasyuninBEntry 25 27 ≤ (((15890209/352090000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2527_formula_bound
  constructor <;> linarith

theorem G25_27_interval :
    ((((15819791/352090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 27) ∧
    (baezDuarteGramEntry 25 27 ≤ (((15890209/352090000) : ℚ) : ℝ)) := by
  rw [G25_27_formula]
  exact vasyuninBEntry_25_27_eval

def interval_25_27 : NamedVasyuninInterval :=
{
  h := 25
  k := 27
  lower := (15819791/352090000)
  upper := (15890209/352090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_27_interval
}

theorem G25_28_formula : baezDuarteGramEntry 25 28 = vasyuninBEntry 25 28 := vasyuninBEntry_correct_axiom 25 28 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_28_eval :
    ((((10792559/249410000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 28) ∧
    (vasyuninBEntry 25 28 ≤ (((10842441/249410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2528_formula_bound
  constructor <;> linarith

theorem G25_28_interval :
    ((((10792559/249410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 28) ∧
    (baezDuarteGramEntry 25 28 ≤ (((10842441/249410000) : ℚ) : ℝ)) := by
  rw [G25_28_formula]
  exact vasyuninBEntry_25_28_eval

def interval_25_28 : NamedVasyuninInterval :=
{
  h := 25
  k := 28
  lower := (10792559/249410000)
  upper := (10842441/249410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_28_interval
}

theorem G25_29_formula : baezDuarteGramEntry 25 29 = vasyuninBEntry 25 29 := vasyuninBEntry_correct_axiom 25 29 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_29_eval :
    ((((38398339/916610000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 29) ∧
    (vasyuninBEntry 25 29 ≤ (((38581661/916610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2529_formula_bound
  constructor <;> linarith

theorem G25_29_interval :
    ((((38398339/916610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 29) ∧
    (baezDuarteGramEntry 25 29 ≤ (((38581661/916610000) : ℚ) : ℝ)) := by
  rw [G25_29_formula]
  exact vasyuninBEntry_25_29_eval

def interval_25_29 : NamedVasyuninInterval :=
{
  h := 25
  k := 29
  lower := (38398339/916610000)
  upper := (38581661/916610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_29_interval
}

theorem G25_30_formula : baezDuarteGramEntry 25 30 = vasyuninBEntry 25 30 := vasyuninBEntry_correct_axiom 25 30 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_30_eval :
    ((((6982859/171410000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 30) ∧
    (vasyuninBEntry 25 30 ≤ (((7017141/171410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_6_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 6 5 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G25_30_interval :
    ((((6982859/171410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 30) ∧
    (baezDuarteGramEntry 25 30 ≤ (((7017141/171410000) : ℚ) : ℝ)) := by
  rw [G25_30_formula]
  exact vasyuninBEntry_25_30_eval

def interval_25_30 : NamedVasyuninInterval :=
{
  h := 25
  k := 30
  lower := (6982859/171410000)
  upper := (7017141/171410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_30_interval
}

theorem G25_31_formula : baezDuarteGramEntry 25 31 = vasyuninBEntry 25 31 := vasyuninBEntry_correct_axiom 25 31 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_31_eval :
    ((((10244177/258230000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 31) ∧
    (vasyuninBEntry 25 31 ≤ (((10295823/258230000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2531_formula_bound
  constructor <;> linarith

theorem G25_31_interval :
    ((((10244177/258230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 31) ∧
    (baezDuarteGramEntry 25 31 ≤ (((10295823/258230000) : ℚ) : ℝ)) := by
  rw [G25_31_formula]
  exact vasyuninBEntry_25_31_eval

def interval_25_31 : NamedVasyuninInterval :=
{
  h := 25
  k := 31
  lower := (10244177/258230000)
  upper := (10295823/258230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_31_interval
}

theorem G25_32_formula : baezDuarteGramEntry 25 32 = vasyuninBEntry 25 32 := vasyuninBEntry_correct_axiom 25 32 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_32_eval :
    ((((195199/5041250) : ℚ) : ℝ) ≤ vasyuninBEntry 25 32) ∧
    (vasyuninBEntry 25 32 ≤ (((784829/20165000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2532_formula_bound
  constructor <;> linarith

theorem G25_32_interval :
    ((((195199/5041250) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 32) ∧
    (baezDuarteGramEntry 25 32 ≤ (((784829/20165000) : ℚ) : ℝ)) := by
  rw [G25_32_formula]
  exact vasyuninBEntry_25_32_eval

def interval_25_32 : NamedVasyuninInterval :=
{
  h := 25
  k := 32
  lower := (195199/5041250)
  upper := (784829/20165000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_32_interval
}

theorem G25_33_formula : baezDuarteGramEntry 25 33 = vasyuninBEntry 25 33 := vasyuninBEntry_correct_axiom 25 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_33_eval :
    ((((19019847/501530000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 33) ∧
    (vasyuninBEntry 25 33 ≤ (((19120153/501530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2533_formula_bound
  constructor <;> linarith

theorem G25_33_interval :
    ((((19019847/501530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 33) ∧
    (baezDuarteGramEntry 25 33 ≤ (((19120153/501530000) : ℚ) : ℝ)) := by
  rw [G25_33_formula]
  exact vasyuninBEntry_25_33_eval

def interval_25_33 : NamedVasyuninInterval :=
{
  h := 25
  k := 33
  lower := (19019847/501530000)
  upper := (19120153/501530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_33_interval
}

theorem G25_34_formula : baezDuarteGramEntry 25 34 = vasyuninBEntry 25 34 := vasyuninBEntry_correct_axiom 25 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_34_eval :
    ((((12007649/323510000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 34) ∧
    (vasyuninBEntry 25 34 ≤ (((12072351/323510000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2534_formula_bound
  constructor <;> linarith

theorem G25_34_interval :
    ((((12007649/323510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 34) ∧
    (baezDuarteGramEntry 25 34 ≤ (((12072351/323510000) : ℚ) : ℝ)) := by
  rw [G25_34_formula]
  exact vasyuninBEntry_25_34_eval

def interval_25_34 : NamedVasyuninInterval :=
{
  h := 25
  k := 34
  lower := (12007649/323510000)
  upper := (12072351/323510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_34_interval
}

theorem G25_35_formula : baezDuarteGramEntry 25 35 = vasyuninBEntry 25 35 := vasyuninBEntry_correct_axiom 25 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_35_eval :
    ((((18898109/518910000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 35) ∧
    (vasyuninBEntry 25 35 ≤ (((19001891/518910000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 7 5 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G25_35_interval :
    ((((18898109/518910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 35) ∧
    (baezDuarteGramEntry 25 35 ≤ (((19001891/518910000) : ℚ) : ℝ)) := by
  rw [G25_35_formula]
  exact vasyuninBEntry_25_35_eval

def interval_25_35 : NamedVasyuninInterval :=
{
  h := 25
  k := 35
  lower := (18898109/518910000)
  upper := (19001891/518910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_35_interval
}

theorem G25_36_formula : baezDuarteGramEntry 25 36 = vasyuninBEntry 25 36 := vasyuninBEntry_correct_axiom 25 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_36_eval :
    ((((10341087/289130000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 36) ∧
    (vasyuninBEntry 25 36 ≤ (((10398913/289130000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2536_formula_bound
  constructor <;> linarith

theorem G25_36_interval :
    ((((10341087/289130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 36) ∧
    (baezDuarteGramEntry 25 36 ≤ (((10398913/289130000) : ℚ) : ℝ)) := by
  rw [G25_36_formula]
  exact vasyuninBEntry_25_36_eval

def interval_25_36 : NamedVasyuninInterval :=
{
  h := 25
  k := 36
  lower := (10341087/289130000)
  upper := (10398913/289130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_36_interval
}

theorem G25_37_formula : baezDuarteGramEntry 25 37 = vasyuninBEntry 25 37 := vasyuninBEntry_correct_axiom 25 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_37_eval :
    ((((20601609/583910000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 37) ∧
    (vasyuninBEntry 25 37 ≤ (((20718391/583910000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2537_formula_bound
  constructor <;> linarith

theorem G25_37_interval :
    ((((20601609/583910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 37) ∧
    (baezDuarteGramEntry 25 37 ≤ (((20718391/583910000) : ℚ) : ℝ)) := by
  rw [G25_37_formula]
  exact vasyuninBEntry_25_37_eval

def interval_25_37 : NamedVasyuninInterval :=
{
  h := 25
  k := 37
  lower := (20601609/583910000)
  upper := (20718391/583910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_37_interval
}

theorem G25_38_formula : baezDuarteGramEntry 25 38 = vasyuninBEntry 25 38 := vasyuninBEntry_correct_axiom 25 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_38_eval :
    ((((22874069/659310000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 38) ∧
    (vasyuninBEntry 25 38 ≤ (((23005931/659310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2538_formula_bound
  constructor <;> linarith

theorem G25_38_interval :
    ((((22874069/659310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 38) ∧
    (baezDuarteGramEntry 25 38 ≤ (((23005931/659310000) : ℚ) : ℝ)) := by
  rw [G25_38_formula]
  exact vasyuninBEntry_25_38_eval

def interval_25_38 : NamedVasyuninInterval :=
{
  h := 25
  k := 38
  lower := (22874069/659310000)
  upper := (23005931/659310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_38_interval
}

theorem G25_39_formula : baezDuarteGramEntry 25 39 = vasyuninBEntry 25 39 := vasyuninBEntry_correct_axiom 25 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_39_eval :
    ((((32354849/951510000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 39) ∧
    (vasyuninBEntry 25 39 ≤ (((32545151/951510000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2539_formula_bound
  constructor <;> linarith

theorem G25_39_interval :
    ((((32354849/951510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 39) ∧
    (baezDuarteGramEntry 25 39 ≤ (((32545151/951510000) : ℚ) : ℝ)) := by
  rw [G25_39_formula]
  exact vasyuninBEntry_25_39_eval

def interval_25_39 : NamedVasyuninInterval :=
{
  h := 25
  k := 39
  lower := (32354849/951510000)
  upper := (32545151/951510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_39_interval
}

theorem G25_40_formula : baezDuarteGramEntry 25 40 = vasyuninBEntry 25 40 := vasyuninBEntry_correct_axiom 25 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_40_eval :
    ((((12223471/365290000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 40) ∧
    (vasyuninBEntry 25 40 ≤ (((12296529/365290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 8 5 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G25_40_interval :
    ((((12223471/365290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 40) ∧
    (baezDuarteGramEntry 25 40 ≤ (((12296529/365290000) : ℚ) : ℝ)) := by
  rw [G25_40_formula]
  exact vasyuninBEntry_25_40_eval

def interval_25_40 : NamedVasyuninInterval :=
{
  h := 25
  k := 40
  lower := (12223471/365290000)
  upper := (12296529/365290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_40_interval
}

theorem G25_41_formula : baezDuarteGramEntry 25 41 = vasyuninBEntry 25 41 := vasyuninBEntry_correct_axiom 25 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_41_eval :
    ((((2472497/75030000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 41) ∧
    (vasyuninBEntry 25 41 ≤ (((2487503/75030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2541_formula_bound
  constructor <;> linarith

theorem G25_41_interval :
    ((((2472497/75030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 41) ∧
    (baezDuarteGramEntry 25 41 ≤ (((2487503/75030000) : ℚ) : ℝ)) := by
  rw [G25_41_formula]
  exact vasyuninBEntry_25_41_eval

def interval_25_41 : NamedVasyuninInterval :=
{
  h := 25
  k := 41
  lower := (2472497/75030000)
  upper := (2487503/75030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_41_interval
}

theorem G25_42_formula : baezDuarteGramEntry 25 42 = vasyuninBEntry 25 42 := vasyuninBEntry_correct_axiom 25 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_42_eval :
    ((((12047949/370510000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 42) ∧
    (vasyuninBEntry 25 42 ≤ (((12122051/370510000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2542_formula_bound
  constructor <;> linarith

theorem G25_42_interval :
    ((((12047949/370510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 42) ∧
    (baezDuarteGramEntry 25 42 ≤ (((12122051/370510000) : ℚ) : ℝ)) := by
  rw [G25_42_formula]
  exact vasyuninBEntry_25_42_eval

def interval_25_42 : NamedVasyuninInterval :=
{
  h := 25
  k := 42
  lower := (12047949/370510000)
  upper := (12122051/370510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_42_interval
}

theorem G25_43_formula : baezDuarteGramEntry 25 43 = vasyuninBEntry 25 43 := vasyuninBEntry_correct_axiom 25 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_43_eval :
    ((((23257467/725330000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 43) ∧
    (vasyuninBEntry 25 43 ≤ (((23402533/725330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2543_formula_bound
  constructor <;> linarith

theorem G25_43_interval :
    ((((23257467/725330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 43) ∧
    (baezDuarteGramEntry 25 43 ≤ (((23402533/725330000) : ℚ) : ℝ)) := by
  rw [G25_43_formula]
  exact vasyuninBEntry_25_43_eval

def interval_25_43 : NamedVasyuninInterval :=
{
  h := 25
  k := 43
  lower := (23257467/725330000)
  upper := (23402533/725330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_43_interval
}

theorem G25_44_formula : baezDuarteGramEntry 25 44 = vasyuninBEntry 25 44 := vasyuninBEntry_correct_axiom 25 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_44_eval :
    ((((222501/7021250) : ℚ) : ℝ) ≤ vasyuninBEntry 25 44) ∧
    (vasyuninBEntry 25 44 ≤ (((895621/28085000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2544_formula_bound
  constructor <;> linarith

theorem G25_44_interval :
    ((((222501/7021250) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 44) ∧
    (baezDuarteGramEntry 25 44 ≤ (((895621/28085000) : ℚ) : ℝ)) := by
  rw [G25_44_formula]
  exact vasyuninBEntry_25_44_eval

def interval_25_44 : NamedVasyuninInterval :=
{
  h := 25
  k := 44
  lower := (222501/7021250)
  upper := (895621/28085000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_44_interval
}

theorem G25_45_formula : baezDuarteGramEntry 25 45 = vasyuninBEntry 25 45 := vasyuninBEntry_correct_axiom 25 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_45_eval :
    ((((3437039/109610000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 45) ∧
    (vasyuninBEntry 25 45 ≤ (((3458961/109610000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 9 5 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G25_45_interval :
    ((((3437039/109610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 45) ∧
    (baezDuarteGramEntry 25 45 ≤ (((3458961/109610000) : ℚ) : ℝ)) := by
  rw [G25_45_formula]
  exact vasyuninBEntry_25_45_eval

def interval_25_45 : NamedVasyuninInterval :=
{
  h := 25
  k := 45
  lower := (3437039/109610000)
  upper := (3458961/109610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_45_interval
}

theorem G25_46_formula : baezDuarteGramEntry 25 46 = vasyuninBEntry 25 46 := vasyuninBEntry_correct_axiom 25 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_46_eval :
    ((((30342271/977290000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 46) ∧
    (vasyuninBEntry 25 46 ≤ (((30537729/977290000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2546_formula_bound
  constructor <;> linarith

theorem G25_46_interval :
    ((((30342271/977290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 46) ∧
    (baezDuarteGramEntry 25 46 ≤ (((30537729/977290000) : ℚ) : ℝ)) := by
  rw [G25_46_formula]
  exact vasyuninBEntry_25_46_eval

def interval_25_46 : NamedVasyuninInterval :=
{
  h := 25
  k := 46
  lower := (30342271/977290000)
  upper := (30537729/977290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_46_interval
}

theorem G25_47_formula : baezDuarteGramEntry 25 47 = vasyuninBEntry 25 47 := vasyuninBEntry_correct_axiom 25 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_47_eval :
    ((((28846369/936310000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 47) ∧
    (vasyuninBEntry 25 47 ≤ (((29033631/936310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2547_formula_bound
  constructor <;> linarith

theorem G25_47_interval :
    ((((28846369/936310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 47) ∧
    (baezDuarteGramEntry 25 47 ≤ (((29033631/936310000) : ℚ) : ℝ)) := by
  rw [G25_47_formula]
  exact vasyuninBEntry_25_47_eval

def interval_25_47 : NamedVasyuninInterval :=
{
  h := 25
  k := 47
  lower := (28846369/936310000)
  upper := (29033631/936310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_47_interval
}

theorem G25_48_formula : baezDuarteGramEntry 25 48 = vasyuninBEntry 25 48 := vasyuninBEntry_correct_axiom 25 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_48_eval :
    ((((23523231/767690000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 48) ∧
    (vasyuninBEntry 25 48 ≤ (((23676769/767690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2548_formula_bound
  constructor <;> linarith

theorem G25_48_interval :
    ((((23523231/767690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 48) ∧
    (baezDuarteGramEntry 25 48 ≤ (((23676769/767690000) : ℚ) : ℝ)) := by
  rw [G25_48_formula]
  exact vasyuninBEntry_25_48_eval

def interval_25_48 : NamedVasyuninInterval :=
{
  h := 25
  k := 48
  lower := (23523231/767690000)
  upper := (23676769/767690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_48_interval
}

theorem G25_49_formula : baezDuarteGramEntry 25 49 = vasyuninBEntry 25 49 := vasyuninBEntry_correct_axiom 25 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_49_eval :
    ((((7485521/244790000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 49) ∧
    (vasyuninBEntry 25 49 ≤ (((7534479/244790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2549_formula_bound
  constructor <;> linarith

theorem G25_49_interval :
    ((((7485521/244790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 49) ∧
    (baezDuarteGramEntry 25 49 ≤ (((7534479/244790000) : ℚ) : ℝ)) := by
  rw [G25_49_formula]
  exact vasyuninBEntry_25_49_eval

def interval_25_49 : NamedVasyuninInterval :=
{
  h := 25
  k := 49
  lower := (7485521/244790000)
  upper := (7534479/244790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_49_interval
}

theorem G25_50_formula : baezDuarteGramEntry 25 50 = vasyuninBEntry 25 50 := vasyuninBEntry_correct_axiom 25 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_25_50_eval :
    ((((12265163/398370000) : ℚ) : ℝ) ≤ vasyuninBEntry 25 50) ∧
    (vasyuninBEntry 25 50 ≤ (((12344837/398370000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 25 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 25)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 25)
  constructor <;> linarith

theorem G25_50_interval :
    ((((12265163/398370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 25 50) ∧
    (baezDuarteGramEntry 25 50 ≤ (((12344837/398370000) : ℚ) : ℝ)) := by
  rw [G25_50_formula]
  exact vasyuninBEntry_25_50_eval

def interval_25_50 : NamedVasyuninInterval :=
{
  h := 25
  k := 50
  lower := (12265163/398370000)
  upper := (12344837/398370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G25_50_interval
}

theorem G26_1_formula : baezDuarteGramEntry 26 1 = vasyuninBEntry 1 26 := by
  rw [baezDuarteGramEntry_symm 26 1]
  exact G1_26_formula

theorem G26_1_interval :
    ((((32829097/309030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 1) ∧
    (baezDuarteGramEntry 26 1 ≤ (((32890903/309030000) : ℚ) : ℝ)) := by
  rw [G26_1_formula]
  exact vasyuninBEntry_1_26_eval

def interval_26_1 : NamedVasyuninInterval :=
{
  h := 26
  k := 1
  lower := (32829097/309030000)
  upper := (32890903/309030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_1_interval
}

theorem G26_2_formula : baezDuarteGramEntry 26 2 = vasyuninBEntry 2 26 := by
  rw [baezDuarteGramEntry_symm 26 2]
  exact G2_26_formula

theorem G26_2_interval :
    ((((26776241/287590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 2) ∧
    (baezDuarteGramEntry 26 2 ≤ (((26833759/287590000) : ℚ) : ℝ)) := by
  rw [G26_2_formula]
  exact vasyuninBEntry_2_26_eval

def interval_26_2 : NamedVasyuninInterval :=
{
  h := 26
  k := 2
  lower := (26776241/287590000)
  upper := (26833759/287590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_2_interval
}

theorem G26_3_formula : baezDuarteGramEntry 26 3 = vasyuninBEntry 3 26 := by
  rw [baezDuarteGramEntry_symm 26 3]
  exact G3_26_formula

theorem G26_3_interval :
    ((((6220663/73370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 3) ∧
    (baezDuarteGramEntry 26 3 ≤ (((6235337/73370000) : ℚ) : ℝ)) := by
  rw [G26_3_formula]
  exact vasyuninBEntry_3_26_eval

def interval_26_3 : NamedVasyuninInterval :=
{
  h := 26
  k := 3
  lower := (6220663/73370000)
  upper := (6235337/73370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_3_interval
}

theorem G26_4_formula : baezDuarteGramEntry 26 4 = vasyuninBEntry 4 26 := by
  rw [baezDuarteGramEntry_symm 26 4]
  exact G4_26_formula

theorem G26_4_interval :
    ((((61252729/772710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 4) ∧
    (baezDuarteGramEntry 26 4 ≤ (((61407271/772710000) : ℚ) : ℝ)) := by
  rw [G26_4_formula]
  exact vasyuninBEntry_4_26_eval

def interval_26_4 : NamedVasyuninInterval :=
{
  h := 26
  k := 4
  lower := (61252729/772710000)
  upper := (61407271/772710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_4_interval
}

theorem G26_5_formula : baezDuarteGramEntry 26 5 = vasyuninBEntry 5 26 := by
  rw [baezDuarteGramEntry_symm 26 5]
  exact G5_26_formula

theorem G26_5_interval :
    ((((13661797/182030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 5) ∧
    (baezDuarteGramEntry 26 5 ≤ (((13698203/182030000) : ℚ) : ℝ)) := by
  rw [G26_5_formula]
  exact vasyuninBEntry_5_26_eval

def interval_26_5 : NamedVasyuninInterval :=
{
  h := 26
  k := 5
  lower := (13661797/182030000)
  upper := (13698203/182030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_5_interval
}

theorem G26_6_formula : baezDuarteGramEntry 26 6 = vasyuninBEntry 6 26 := by
  rw [baezDuarteGramEntry_symm 26 6]
  exact G6_26_formula

theorem G26_6_interval :
    ((((21325121/298790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 6) ∧
    (baezDuarteGramEntry 26 6 ≤ (((21384879/298790000) : ℚ) : ℝ)) := by
  rw [G26_6_formula]
  exact vasyuninBEntry_6_26_eval

def interval_26_6 : NamedVasyuninInterval :=
{
  h := 26
  k := 6
  lower := (21325121/298790000)
  upper := (21384879/298790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_6_interval
}

theorem G26_7_formula : baezDuarteGramEntry 26 7 = vasyuninBEntry 7 26 := by
  rw [baezDuarteGramEntry_symm 26 7]
  exact G7_26_formula

theorem G26_7_interval :
    ((((59183361/866390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 7) ∧
    (baezDuarteGramEntry 26 7 ≤ (((59356639/866390000) : ℚ) : ℝ)) := by
  rw [G26_7_formula]
  exact vasyuninBEntry_7_26_eval

def interval_26_7 : NamedVasyuninInterval :=
{
  h := 26
  k := 7
  lower := (59183361/866390000)
  upper := (59356639/866390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_7_interval
}

theorem G26_8_formula : baezDuarteGramEntry 26 8 = vasyuninBEntry 8 26 := by
  rw [baezDuarteGramEntry_symm 26 8]
  exact G8_26_formula

theorem G26_8_interval :
    ((((27463321/416790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 8) ∧
    (baezDuarteGramEntry 26 8 ≤ (((27546679/416790000) : ℚ) : ℝ)) := by
  rw [G26_8_formula]
  exact vasyuninBEntry_8_26_eval

def interval_26_8 : NamedVasyuninInterval :=
{
  h := 26
  k := 8
  lower := (27463321/416790000)
  upper := (27546679/416790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_8_interval
}

theorem G26_9_formula : baezDuarteGramEntry 26 9 = vasyuninBEntry 9 26 := by
  rw [baezDuarteGramEntry_symm 26 9]
  exact G9_26_formula

theorem G26_9_interval :
    ((((8696423/135770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 9) ∧
    (baezDuarteGramEntry 26 9 ≤ (((8723577/135770000) : ℚ) : ℝ)) := by
  rw [G26_9_formula]
  exact vasyuninBEntry_9_26_eval

def interval_26_9 : NamedVasyuninInterval :=
{
  h := 26
  k := 9
  lower := (8696423/135770000)
  upper := (8723577/135770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_9_interval
}

theorem G26_10_formula : baezDuarteGramEntry 26 10 = vasyuninBEntry 10 26 := by
  rw [baezDuarteGramEntry_symm 26 10]
  exact G10_26_formula

theorem G26_10_interval :
    ((((57426181/938190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 10) ∧
    (baezDuarteGramEntry 26 10 ≤ (((57613819/938190000) : ℚ) : ℝ)) := by
  rw [G26_10_formula]
  exact vasyuninBEntry_10_26_eval

def interval_26_10 : NamedVasyuninInterval :=
{
  h := 26
  k := 10
  lower := (57426181/938190000)
  upper := (57613819/938190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_10_interval
}

theorem G26_11_formula : baezDuarteGramEntry 26 11 = vasyuninBEntry 11 26 := by
  rw [baezDuarteGramEntry_symm 26 11]
  exact G11_26_formula

theorem G26_11_interval :
    ((((1793857/30180000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 11) ∧
    (baezDuarteGramEntry 26 11 ≤ (((1799893/30180000) : ℚ) : ℝ)) := by
  rw [G26_11_formula]
  exact vasyuninBEntry_11_26_eval

def interval_26_11 : NamedVasyuninInterval :=
{
  h := 26
  k := 11
  lower := (1793857/30180000)
  upper := (1799893/30180000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_11_interval
}

theorem G26_12_formula : baezDuarteGramEntry 26 12 = vasyuninBEntry 12 26 := by
  rw [baezDuarteGramEntry_symm 26 12]
  exact G12_26_formula

theorem G26_12_interval :
    ((((44563717/762830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 12) ∧
    (baezDuarteGramEntry 26 12 ≤ (((44716283/762830000) : ℚ) : ℝ)) := by
  rw [G26_12_formula]
  exact vasyuninBEntry_12_26_eval

def interval_26_12 : NamedVasyuninInterval :=
{
  h := 26
  k := 12
  lower := (44563717/762830000)
  upper := (44716283/762830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_12_interval
}

theorem G26_13_formula : baezDuarteGramEntry 26 13 = vasyuninBEntry 13 26 := by
  rw [baezDuarteGramEntry_symm 26 13]
  exact G13_26_formula

theorem G26_13_interval :
    ((((34811297/587030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 13) ∧
    (baezDuarteGramEntry 26 13 ≤ (((34928703/587030000) : ℚ) : ℝ)) := by
  rw [G26_13_formula]
  exact vasyuninBEntry_13_26_eval

def interval_26_13 : NamedVasyuninInterval :=
{
  h := 26
  k := 13
  lower := (34811297/587030000)
  upper := (34928703/587030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_13_interval
}

theorem G26_14_formula : baezDuarteGramEntry 26 14 = vasyuninBEntry 14 26 := by
  rw [baezDuarteGramEntry_symm 26 14]
  exact G14_26_formula

theorem G26_14_interval :
    ((((1105003/19970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 14) ∧
    (baezDuarteGramEntry 26 14 ≤ (((1108997/19970000) : ℚ) : ℝ)) := by
  rw [G26_14_formula]
  exact vasyuninBEntry_14_26_eval

def interval_26_14 : NamedVasyuninInterval :=
{
  h := 26
  k := 14
  lower := (1105003/19970000)
  upper := (1108997/19970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_14_interval
}

theorem G26_15_formula : baezDuarteGramEntry 26 15 = vasyuninBEntry 15 26 := by
  rw [baezDuarteGramEntry_symm 26 15]
  exact G15_26_formula

theorem G26_15_interval :
    ((((25631903/480970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 15) ∧
    (baezDuarteGramEntry 26 15 ≤ (((25728097/480970000) : ℚ) : ℝ)) := by
  rw [G26_15_formula]
  exact vasyuninBEntry_15_26_eval

def interval_26_15 : NamedVasyuninInterval :=
{
  h := 26
  k := 15
  lower := (25631903/480970000)
  upper := (25728097/480970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_15_interval
}

theorem G26_16_formula : baezDuarteGramEntry 26 16 = vasyuninBEntry 16 26 := by
  rw [baezDuarteGramEntry_symm 26 16]
  exact G16_26_formula

theorem G26_16_interval :
    ((((9094451/175490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 16) ∧
    (baezDuarteGramEntry 26 16 ≤ (((9129549/175490000) : ℚ) : ℝ)) := by
  rw [G26_16_formula]
  exact vasyuninBEntry_16_26_eval

def interval_26_16 : NamedVasyuninInterval :=
{
  h := 26
  k := 16
  lower := (9094451/175490000)
  upper := (9129549/175490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_16_interval
}

theorem G26_17_formula : baezDuarteGramEntry 26 17 = vasyuninBEntry 17 26 := by
  rw [baezDuarteGramEntry_symm 26 17]
  exact G17_26_formula

theorem G26_17_interval :
    ((((7071081/139190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 17) ∧
    (baezDuarteGramEntry 26 17 ≤ (((7098919/139190000) : ℚ) : ℝ)) := by
  rw [G26_17_formula]
  exact vasyuninBEntry_17_26_eval

def interval_26_17 : NamedVasyuninInterval :=
{
  h := 26
  k := 17
  lower := (7071081/139190000)
  upper := (7098919/139190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_17_interval
}

theorem G26_18_formula : baezDuarteGramEntry 26 18 = vasyuninBEntry 18 26 := by
  rw [baezDuarteGramEntry_symm 26 18]
  exact G18_26_formula

theorem G26_18_interval :
    ((((8472929/170710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 18) ∧
    (baezDuarteGramEntry 26 18 ≤ (((8507071/170710000) : ℚ) : ℝ)) := by
  rw [G26_18_formula]
  exact vasyuninBEntry_18_26_eval

def interval_26_18 : NamedVasyuninInterval :=
{
  h := 26
  k := 18
  lower := (8472929/170710000)
  upper := (8507071/170710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_18_interval
}

theorem G26_19_formula : baezDuarteGramEntry 26 19 = vasyuninBEntry 19 26 := by
  rw [baezDuarteGramEntry_symm 26 19]
  exact G19_26_formula

theorem G26_19_interval :
    ((((2966403/60970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 19) ∧
    (baezDuarteGramEntry 26 19 ≤ (((2978597/60970000) : ℚ) : ℝ)) := by
  rw [G26_19_formula]
  exact vasyuninBEntry_19_26_eval

def interval_26_19 : NamedVasyuninInterval :=
{
  h := 26
  k := 19
  lower := (2966403/60970000)
  upper := (2978597/60970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_19_interval
}

theorem G26_20_formula : baezDuarteGramEntry 26 20 = vasyuninBEntry 20 26 := by
  rw [baezDuarteGramEntry_symm 26 20]
  exact G20_26_formula

theorem G26_20_interval :
    ((((8749733/182670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 20) ∧
    (baezDuarteGramEntry 26 20 ≤ (((8786267/182670000) : ℚ) : ℝ)) := by
  rw [G26_20_formula]
  exact vasyuninBEntry_20_26_eval

def interval_26_20 : NamedVasyuninInterval :=
{
  h := 26
  k := 20
  lower := (8749733/182670000)
  upper := (8786267/182670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_20_interval
}

theorem G26_21_formula : baezDuarteGramEntry 26 21 = vasyuninBEntry 21 26 := by
  rw [baezDuarteGramEntry_symm 26 21]
  exact G21_26_formula

theorem G26_21_interval :
    ((((23545219/497810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 21) ∧
    (baezDuarteGramEntry 26 21 ≤ (((23644781/497810000) : ℚ) : ℝ)) := by
  rw [G26_21_formula]
  exact vasyuninBEntry_21_26_eval

def interval_26_21 : NamedVasyuninInterval :=
{
  h := 26
  k := 21
  lower := (23545219/497810000)
  upper := (23644781/497810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_21_interval
}

theorem G26_22_formula : baezDuarteGramEntry 26 22 = vasyuninBEntry 22 26 := by
  rw [baezDuarteGramEntry_symm 26 22]
  exact G22_26_formula

theorem G26_22_interval :
    ((((13655857/291430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 22) ∧
    (baezDuarteGramEntry 26 22 ≤ (((13714143/291430000) : ℚ) : ℝ)) := by
  rw [G26_22_formula]
  exact vasyuninBEntry_22_26_eval

def interval_26_22 : NamedVasyuninInterval :=
{
  h := 26
  k := 22
  lower := (13655857/291430000)
  upper := (13714143/291430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_22_interval
}

theorem G26_23_formula : baezDuarteGramEntry 26 23 = vasyuninBEntry 23 26 := by
  rw [baezDuarteGramEntry_symm 26 23]
  exact G23_26_formula

theorem G26_23_interval :
    ((((39984247/857530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 23) ∧
    (baezDuarteGramEntry 26 23 ≤ (((40155753/857530000) : ℚ) : ℝ)) := by
  rw [G26_23_formula]
  exact vasyuninBEntry_23_26_eval

def interval_26_23 : NamedVasyuninInterval :=
{
  h := 26
  k := 23
  lower := (39984247/857530000)
  upper := (40155753/857530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_23_interval
}

theorem G26_24_formula : baezDuarteGramEntry 26 24 = vasyuninBEntry 24 26 := by
  rw [baezDuarteGramEntry_symm 26 24]
  exact G24_26_formula

theorem G26_24_interval :
    ((((653599/14010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 24) ∧
    (baezDuarteGramEntry 26 24 ≤ (((656401/14010000) : ℚ) : ℝ)) := by
  rw [G26_24_formula]
  exact vasyuninBEntry_24_26_eval

def interval_26_24 : NamedVasyuninInterval :=
{
  h := 26
  k := 24
  lower := (653599/14010000)
  upper := (656401/14010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_24_interval
}

theorem G26_25_formula : baezDuarteGramEntry 26 25 = vasyuninBEntry 25 26 := by
  rw [baezDuarteGramEntry_symm 26 25]
  exact G25_26_formula

theorem G26_25_interval :
    ((((7300479/155210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 25) ∧
    (baezDuarteGramEntry 26 25 ≤ (((7331521/155210000) : ℚ) : ℝ)) := by
  rw [G26_25_formula]
  exact vasyuninBEntry_25_26_eval

def interval_26_25 : NamedVasyuninInterval :=
{
  h := 26
  k := 25
  lower := (7300479/155210000)
  upper := (7331521/155210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_25_interval
}

theorem G26_26_formula_eq : baezDuarteGramEntry 26 26 = (1 / (26 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 26 := by norm_num
  rw [baez_duarte_diagonal_scaling 26 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G26_26_log_gamma_interval :
  ((((1653383/34170000) : ℚ) : ℝ) ≤ (1 / (26 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (26 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((1660217/34170000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 26 (by norm_num)
  constructor
  · have : ((((1653383/34170000) : ℚ) : ℝ) ≤ (1 / (26 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (26 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((1660217/34170000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G26_26_interval : ((((1653383/34170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 26) ∧ (baezDuarteGramEntry 26 26 ≤ (((1660217/34170000) : ℚ) : ℝ)) := by
  rw [G26_26_formula_eq]
  exact G26_26_log_gamma_interval

def interval_26_26 : NamedVasyuninInterval :=
{
  h := 26
  k := 26
  lower := (1653383/34170000)
  upper := (1660217/34170000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G26_26_interval
}

theorem G26_27_formula : baezDuarteGramEntry 26 27 = vasyuninBEntry 26 27 := vasyuninBEntry_correct_axiom 26 27 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_27_eval :
    ((((6200317/136830000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 27) ∧
    (vasyuninBEntry 26 27 ≤ (((6227683/136830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2627_formula_bound
  constructor <;> linarith

theorem G26_27_interval :
    ((((6200317/136830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 27) ∧
    (baezDuarteGramEntry 26 27 ≤ (((6227683/136830000) : ℚ) : ℝ)) := by
  rw [G26_27_formula]
  exact vasyuninBEntry_26_27_eval

def interval_26_27 : NamedVasyuninInterval :=
{
  h := 26
  k := 27
  lower := (6200317/136830000)
  upper := (6227683/136830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_27_interval
}

theorem G26_28_formula : baezDuarteGramEntry 26 28 = vasyuninBEntry 26 28 := vasyuninBEntry_correct_axiom 26 28 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_28_eval :
    ((((3821183/88170000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 28) ∧
    (vasyuninBEntry 26 28 ≤ (((3838817/88170000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_13_14_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 13 14 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G26_28_interval :
    ((((3821183/88170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 28) ∧
    (baezDuarteGramEntry 26 28 ≤ (((3838817/88170000) : ℚ) : ℝ)) := by
  rw [G26_28_formula]
  exact vasyuninBEntry_26_28_eval

def interval_26_28 : NamedVasyuninInterval :=
{
  h := 26
  k := 28
  lower := (3821183/88170000)
  upper := (3838817/88170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_28_interval
}

theorem G26_29_formula : baezDuarteGramEntry 26 29 = vasyuninBEntry 26 29 := vasyuninBEntry_correct_axiom 26 29 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_29_eval :
    ((((37819463/905370000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 29) ∧
    (vasyuninBEntry 26 29 ≤ (((38000537/905370000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2629_formula_bound
  constructor <;> linarith

theorem G26_29_interval :
    ((((37819463/905370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 29) ∧
    (baezDuarteGramEntry 26 29 ≤ (((38000537/905370000) : ℚ) : ℝ)) := by
  rw [G26_29_formula]
  exact vasyuninBEntry_26_29_eval

def interval_26_29 : NamedVasyuninInterval :=
{
  h := 26
  k := 29
  lower := (37819463/905370000)
  upper := (38000537/905370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_29_interval
}

theorem G26_30_formula : baezDuarteGramEntry 26 30 = vasyuninBEntry 26 30 := vasyuninBEntry_correct_axiom 26 30 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_30_eval :
    ((((19945711/492890000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 30) ∧
    (vasyuninBEntry 26 30 ≤ (((20044289/492890000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_13_15_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 13 15 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G26_30_interval :
    ((((19945711/492890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 30) ∧
    (baezDuarteGramEntry 26 30 ≤ (((20044289/492890000) : ℚ) : ℝ)) := by
  rw [G26_30_formula]
  exact vasyuninBEntry_26_30_eval

def interval_26_30 : NamedVasyuninInterval :=
{
  h := 26
  k := 30
  lower := (19945711/492890000)
  upper := (20044289/492890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_30_interval
}

theorem G26_31_formula : baezDuarteGramEntry 26 31 = vasyuninBEntry 26 31 := vasyuninBEntry_correct_axiom 26 31 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_31_eval :
    ((((29036201/737990000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 31) ∧
    (vasyuninBEntry 26 31 ≤ (((29183799/737990000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2631_formula_bound
  constructor <;> linarith

theorem G26_31_interval :
    ((((29036201/737990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 31) ∧
    (baezDuarteGramEntry 26 31 ≤ (((29183799/737990000) : ℚ) : ℝ)) := by
  rw [G26_31_formula]
  exact vasyuninBEntry_26_31_eval

def interval_26_31 : NamedVasyuninInterval :=
{
  h := 26
  k := 31
  lower := (29036201/737990000)
  upper := (29183799/737990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_31_interval
}

theorem G26_32_formula : baezDuarteGramEntry 26 32 = vasyuninBEntry 26 32 := vasyuninBEntry_correct_axiom 26 32 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_32_eval :
    ((((2070601/53990000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 32) ∧
    (vasyuninBEntry 26 32 ≤ (((2081399/53990000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_13_16_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 13 16 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G26_32_interval :
    ((((2070601/53990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 32) ∧
    (baezDuarteGramEntry 26 32 ≤ (((2081399/53990000) : ℚ) : ℝ)) := by
  rw [G26_32_formula]
  exact vasyuninBEntry_26_32_eval

def interval_26_32 : NamedVasyuninInterval :=
{
  h := 26
  k := 32
  lower := (2070601/53990000)
  upper := (2081399/53990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_32_interval
}

theorem G26_33_formula : baezDuarteGramEntry 26 33 = vasyuninBEntry 26 33 := vasyuninBEntry_correct_axiom 26 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_33_eval :
    ((((15109667/403330000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 33) ∧
    (vasyuninBEntry 26 33 ≤ (((15190333/403330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2633_formula_bound
  constructor <;> linarith

theorem G26_33_interval :
    ((((15109667/403330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 33) ∧
    (baezDuarteGramEntry 26 33 ≤ (((15190333/403330000) : ℚ) : ℝ)) := by
  rw [G26_33_formula]
  exact vasyuninBEntry_26_33_eval

def interval_26_33 : NamedVasyuninInterval :=
{
  h := 26
  k := 33
  lower := (15109667/403330000)
  upper := (15190333/403330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_33_interval
}

theorem G26_34_formula : baezDuarteGramEntry 26 34 = vasyuninBEntry 26 34 := vasyuninBEntry_correct_axiom 26 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_34_eval :
    ((((31304643/853570000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 34) ∧
    (vasyuninBEntry 26 34 ≤ (((31475357/853570000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_13_17_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 13 17 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G26_34_interval :
    ((((31304643/853570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 34) ∧
    (baezDuarteGramEntry 26 34 ≤ (((31475357/853570000) : ℚ) : ℝ)) := by
  rw [G26_34_formula]
  exact vasyuninBEntry_26_34_eval

def interval_26_34 : NamedVasyuninInterval :=
{
  h := 26
  k := 34
  lower := (31304643/853570000)
  upper := (31475357/853570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_34_interval
}

theorem G26_35_formula : baezDuarteGramEntry 26 35 = vasyuninBEntry 26 35 := vasyuninBEntry_correct_axiom 26 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_35_eval :
    ((((19595521/544790000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 35) ∧
    (vasyuninBEntry 26 35 ≤ (((19704479/544790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2635_formula_bound
  constructor <;> linarith

theorem G26_35_interval :
    ((((19595521/544790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 35) ∧
    (baezDuarteGramEntry 26 35 ≤ (((19704479/544790000) : ℚ) : ℝ)) := by
  rw [G26_35_formula]
  exact vasyuninBEntry_26_35_eval

def interval_26_35 : NamedVasyuninInterval :=
{
  h := 26
  k := 35
  lower := (19595521/544790000)
  upper := (19704479/544790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_35_interval
}

theorem G26_36_formula : baezDuarteGramEntry 26 36 = vasyuninBEntry 26 36 := vasyuninBEntry_correct_axiom 26 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_36_eval :
    ((((13491719/382810000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 36) ∧
    (vasyuninBEntry 26 36 ≤ (((13568281/382810000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_13_18_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 13 18 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G26_36_interval :
    ((((13491719/382810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 36) ∧
    (baezDuarteGramEntry 26 36 ≤ (((13568281/382810000) : ℚ) : ℝ)) := by
  rw [G26_36_formula]
  exact vasyuninBEntry_26_36_eval

def interval_26_36 : NamedVasyuninInterval :=
{
  h := 26
  k := 36
  lower := (13491719/382810000)
  upper := (13568281/382810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_36_interval
}

theorem G26_37_formula : baezDuarteGramEntry 26 37 = vasyuninBEntry 26 37 := vasyuninBEntry_correct_axiom 26 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_37_eval :
    ((((34290977/990230000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 37) ∧
    (vasyuninBEntry 26 37 ≤ (((34489023/990230000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2637_formula_bound
  constructor <;> linarith

theorem G26_37_interval :
    ((((34290977/990230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 37) ∧
    (baezDuarteGramEntry 26 37 ≤ (((34489023/990230000) : ℚ) : ℝ)) := by
  rw [G26_37_formula]
  exact vasyuninBEntry_26_37_eval

def interval_26_37 : NamedVasyuninInterval :=
{
  h := 26
  k := 37
  lower := (34290977/990230000)
  upper := (34489023/990230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_37_interval
}

theorem G26_38_formula : baezDuarteGramEntry 26 38 = vasyuninBEntry 26 38 := vasyuninBEntry_correct_axiom 26 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_38_eval :
    ((((9247891/271090000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 38) ∧
    (vasyuninBEntry 26 38 ≤ (((9302109/271090000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_13_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 13 19 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G26_38_interval :
    ((((9247891/271090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 38) ∧
    (baezDuarteGramEntry 26 38 ≤ (((9302109/271090000) : ℚ) : ℝ)) := by
  rw [G26_38_formula]
  exact vasyuninBEntry_26_38_eval

def interval_26_38 : NamedVasyuninInterval :=
{
  h := 26
  k := 38
  lower := (9247891/271090000)
  upper := (9302109/271090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_38_interval
}

theorem G26_39_formula : baezDuarteGramEntry 26 39 = vasyuninBEntry 26 39 := vasyuninBEntry_correct_axiom 26 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_39_eval :
    ((((20319937/600630000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 39) ∧
    (vasyuninBEntry 26 39 ≤ (((20440063/600630000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 13 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 13)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 13)
  constructor <;> linarith

theorem G26_39_interval :
    ((((20319937/600630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 39) ∧
    (baezDuarteGramEntry 26 39 ≤ (((20440063/600630000) : ℚ) : ℝ)) := by
  rw [G26_39_formula]
  exact vasyuninBEntry_26_39_eval

def interval_26_39 : NamedVasyuninInterval :=
{
  h := 26
  k := 39
  lower := (20319937/600630000)
  upper := (20440063/600630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_39_interval
}

theorem G26_40_formula : baezDuarteGramEntry 26 40 = vasyuninBEntry 26 40 := vasyuninBEntry_correct_axiom 26 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_40_eval :
    ((((1324739/40110000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 40) ∧
    (vasyuninBEntry 26 40 ≤ (((1332761/40110000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_13_20_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 13 20 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G26_40_interval :
    ((((1324739/40110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 40) ∧
    (baezDuarteGramEntry 26 40 ≤ (((1332761/40110000) : ℚ) : ℝ)) := by
  rw [G26_40_formula]
  exact vasyuninBEntry_26_40_eval

def interval_26_40 : NamedVasyuninInterval :=
{
  h := 26
  k := 40
  lower := (1324739/40110000)
  upper := (1332761/40110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_40_interval
}

theorem G26_41_formula : baezDuarteGramEntry 26 41 = vasyuninBEntry 26 41 := vasyuninBEntry_correct_axiom 26 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_41_eval :
    ((((439583/13545000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 41) ∧
    (vasyuninBEntry 26 41 ≤ (((110573/3386250) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2641_formula_bound
  constructor <;> linarith

theorem G26_41_interval :
    ((((439583/13545000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 41) ∧
    (baezDuarteGramEntry 26 41 ≤ (((110573/3386250) : ℚ) : ℝ)) := by
  rw [G26_41_formula]
  exact vasyuninBEntry_26_41_eval

def interval_26_41 : NamedVasyuninInterval :=
{
  h := 26
  k := 41
  lower := (439583/13545000)
  upper := (110573/3386250)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_41_interval
}

theorem G26_42_formula : baezDuarteGramEntry 26 42 = vasyuninBEntry 26 42 := vasyuninBEntry_correct_axiom 26 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_42_eval :
    ((((23636051/739490000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 42) ∧
    (vasyuninBEntry 26 42 ≤ (((23783949/739490000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_13_21_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 13 21 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G26_42_interval :
    ((((23636051/739490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 42) ∧
    (baezDuarteGramEntry 26 42 ≤ (((23783949/739490000) : ℚ) : ℝ)) := by
  rw [G26_42_formula]
  exact vasyuninBEntry_26_42_eval

def interval_26_42 : NamedVasyuninInterval :=
{
  h := 26
  k := 42
  lower := (23636051/739490000)
  upper := (23783949/739490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_42_interval
}

theorem G26_43_formula : baezDuarteGramEntry 26 43 = vasyuninBEntry 26 43 := vasyuninBEntry_correct_axiom 26 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_43_eval :
    ((((570691/18090000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 43) ∧
    (vasyuninBEntry 26 43 ≤ (((574309/18090000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2643_formula_bound
  constructor <;> linarith

theorem G26_43_interval :
    ((((570691/18090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 43) ∧
    (baezDuarteGramEntry 26 43 ≤ (((574309/18090000) : ℚ) : ℝ)) := by
  rw [G26_43_formula]
  exact vasyuninBEntry_26_43_eval

def interval_26_43 : NamedVasyuninInterval :=
{
  h := 26
  k := 43
  lower := (570691/18090000)
  upper := (574309/18090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_43_interval
}

theorem G26_44_formula : baezDuarteGramEntry 26 44 = vasyuninBEntry 26 44 := vasyuninBEntry_correct_axiom 26 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_44_eval :
    ((((15869001/509990000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 44) ∧
    (vasyuninBEntry 26 44 ≤ (((15970999/509990000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_13_22_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 13 22 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G26_44_interval :
    ((((15869001/509990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 44) ∧
    (baezDuarteGramEntry 26 44 ≤ (((15970999/509990000) : ℚ) : ℝ)) := by
  rw [G26_44_formula]
  exact vasyuninBEntry_26_44_eval

def interval_26_44 : NamedVasyuninInterval :=
{
  h := 26
  k := 44
  lower := (15869001/509990000)
  upper := (15970999/509990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_44_interval
}

theorem G26_45_formula : baezDuarteGramEntry 26 45 = vasyuninBEntry 26 45 := vasyuninBEntry_correct_axiom 26 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_45_eval :
    ((((14637361/476390000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 45) ∧
    (vasyuninBEntry 26 45 ≤ (((14732639/476390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2645_formula_bound
  constructor <;> linarith

theorem G26_45_interval :
    ((((14637361/476390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 45) ∧
    (baezDuarteGramEntry 26 45 ≤ (((14732639/476390000) : ℚ) : ℝ)) := by
  rw [G26_45_formula]
  exact vasyuninBEntry_26_45_eval

def interval_26_45 : NamedVasyuninInterval :=
{
  h := 26
  k := 45
  lower := (14637361/476390000)
  upper := (14732639/476390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_45_interval
}

theorem G26_46_formula : baezDuarteGramEntry 26 46 = vasyuninBEntry 26 46 := vasyuninBEntry_correct_axiom 26 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_46_eval :
    ((((11681551/384490000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 46) ∧
    (vasyuninBEntry 26 46 ≤ (((11758449/384490000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_13_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 13 23 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G26_46_interval :
    ((((11681551/384490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 46) ∧
    (baezDuarteGramEntry 26 46 ≤ (((11758449/384490000) : ℚ) : ℝ)) := by
  rw [G26_46_formula]
  exact vasyuninBEntry_26_46_eval

def interval_26_46 : NamedVasyuninInterval :=
{
  h := 26
  k := 46
  lower := (11681551/384490000)
  upper := (11758449/384490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_46_interval
}

theorem G26_47_formula : baezDuarteGramEntry 26 47 = vasyuninBEntry 26 47 := vasyuninBEntry_correct_axiom 26 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_47_eval :
    ((((838811/27890000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 47) ∧
    (vasyuninBEntry 26 47 ≤ (((844389/27890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2647_formula_bound
  constructor <;> linarith

theorem G26_47_interval :
    ((((838811/27890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 47) ∧
    (baezDuarteGramEntry 26 47 ≤ (((844389/27890000) : ℚ) : ℝ)) := by
  rw [G26_47_formula]
  exact vasyuninBEntry_26_47_eval

def interval_26_47 : NamedVasyuninInterval :=
{
  h := 26
  k := 47
  lower := (838811/27890000)
  upper := (844389/27890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_47_interval
}

theorem G26_48_formula : baezDuarteGramEntry 26 48 = vasyuninBEntry 26 48 := vasyuninBEntry_correct_axiom 26 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_48_eval :
    ((((27956219/937810000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 48) ∧
    (vasyuninBEntry 26 48 ≤ (((28143781/937810000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_13_24_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 13 24 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G26_48_interval :
    ((((27956219/937810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 48) ∧
    (baezDuarteGramEntry 26 48 ≤ (((28143781/937810000) : ℚ) : ℝ)) := by
  rw [G26_48_formula]
  exact vasyuninBEntry_26_48_eval

def interval_26_48 : NamedVasyuninInterval :=
{
  h := 26
  k := 48
  lower := (27956219/937810000)
  upper := (28143781/937810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_48_interval
}

theorem G26_49_formula : baezDuarteGramEntry 26 49 = vasyuninBEntry 26 49 := vasyuninBEntry_correct_axiom 26 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_49_eval :
    ((((9786933/330670000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 49) ∧
    (vasyuninBEntry 26 49 ≤ (((9853067/330670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2649_formula_bound
  constructor <;> linarith

theorem G26_49_interval :
    ((((9786933/330670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 49) ∧
    (baezDuarteGramEntry 26 49 ≤ (((9853067/330670000) : ℚ) : ℝ)) := by
  rw [G26_49_formula]
  exact vasyuninBEntry_26_49_eval

def interval_26_49 : NamedVasyuninInterval :=
{
  h := 26
  k := 49
  lower := (9786933/330670000)
  upper := (9853067/330670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_49_interval
}

theorem G26_50_formula : baezDuarteGramEntry 26 50 = vasyuninBEntry 26 50 := vasyuninBEntry_correct_axiom 26 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_26_50_eval :
    ((((13115467/445330000) : ℚ) : ℝ) ≤ vasyuninBEntry 26 50) ∧
    (vasyuninBEntry 26 50 ≤ (((13204533/445330000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_13_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 13 25 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G26_50_interval :
    ((((13115467/445330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 26 50) ∧
    (baezDuarteGramEntry 26 50 ≤ (((13204533/445330000) : ℚ) : ℝ)) := by
  rw [G26_50_formula]
  exact vasyuninBEntry_26_50_eval

def interval_26_50 : NamedVasyuninInterval :=
{
  h := 26
  k := 50
  lower := (13115467/445330000)
  upper := (13204533/445330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G26_50_interval
}

theorem G27_1_formula : baezDuarteGramEntry 27 1 = vasyuninBEntry 1 27 := by
  rw [baezDuarteGramEntry_symm 27 1]
  exact G1_27_formula

theorem G27_1_interval :
    ((((95806971/930290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 1) ∧
    (baezDuarteGramEntry 27 1 ≤ (((95993029/930290000) : ℚ) : ℝ)) := by
  rw [G27_1_formula]
  exact vasyuninBEntry_1_27_eval

def interval_27_1 : NamedVasyuninInterval :=
{
  h := 27
  k := 1
  lower := (95806971/930290000)
  upper := (95993029/930290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_1_interval
}

theorem G27_2_formula : baezDuarteGramEntry 27 2 = vasyuninBEntry 2 27 := by
  rw [baezDuarteGramEntry_symm 27 2]
  exact G2_27_formula

theorem G27_2_interval :
    ((((30266339/336610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 2) ∧
    (baezDuarteGramEntry 27 2 ≤ (((30333661/336610000) : ℚ) : ℝ)) := by
  rw [G27_2_formula]
  exact vasyuninBEntry_2_27_eval

def interval_27_2 : NamedVasyuninInterval :=
{
  h := 27
  k := 2
  lower := (30266339/336610000)
  upper := (30333661/336610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_2_interval
}

theorem G27_3_formula : baezDuarteGramEntry 27 3 = vasyuninBEntry 3 27 := by
  rw [baezDuarteGramEntry_symm 27 3]
  exact G3_27_formula

theorem G27_3_interval :
    ((((71344061/859390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 3) ∧
    (baezDuarteGramEntry 27 3 ≤ (((71515939/859390000) : ℚ) : ℝ)) := by
  rw [G27_3_formula]
  exact vasyuninBEntry_3_27_eval

def interval_27_3 : NamedVasyuninInterval :=
{
  h := 27
  k := 3
  lower := (71344061/859390000)
  upper := (71515939/859390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_3_interval
}

theorem G27_4_formula : baezDuarteGramEntry 27 4 = vasyuninBEntry 4 27 := by
  rw [baezDuarteGramEntry_symm 27 4]
  exact G4_27_formula

theorem G27_4_interval :
    ((((16558501/214990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 4) ∧
    (baezDuarteGramEntry 27 4 ≤ (((16601499/214990000) : ℚ) : ℝ)) := by
  rw [G27_4_formula]
  exact vasyuninBEntry_4_27_eval

def interval_27_4 : NamedVasyuninInterval :=
{
  h := 27
  k := 4
  lower := (16558501/214990000)
  upper := (16601499/214990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_4_interval
}

theorem G27_5_formula : baezDuarteGramEntry 27 5 = vasyuninBEntry 5 27 := by
  rw [baezDuarteGramEntry_symm 27 5]
  exact G5_27_formula

theorem G27_5_interval :
    ((((8113849/111510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 5) ∧
    (baezDuarteGramEntry 27 5 ≤ (((8136151/111510000) : ℚ) : ℝ)) := by
  rw [G27_5_formula]
  exact vasyuninBEntry_5_27_eval

def interval_27_5 : NamedVasyuninInterval :=
{
  h := 27
  k := 5
  lower := (8113849/111510000)
  upper := (8136151/111510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_5_interval
}

theorem G27_6_formula : baezDuarteGramEntry 27 6 = vasyuninBEntry 6 27 := by
  rw [baezDuarteGramEntry_symm 27 6]
  exact G6_27_formula

theorem G27_6_interval :
    ((((13089161/188390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 6) ∧
    (baezDuarteGramEntry 27 6 ≤ (((13126839/188390000) : ℚ) : ℝ)) := by
  rw [G27_6_formula]
  exact vasyuninBEntry_6_27_eval

def interval_27_6 : NamedVasyuninInterval :=
{
  h := 27
  k := 6
  lower := (13089161/188390000)
  upper := (13126839/188390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_6_interval
}

theorem G27_7_formula : baezDuarteGramEntry 27 7 = vasyuninBEntry 7 27 := by
  rw [baezDuarteGramEntry_symm 27 7]
  exact G7_27_formula

theorem G27_7_interval :
    ((((32032073/479270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 7) ∧
    (baezDuarteGramEntry 27 7 ≤ (((32127927/479270000) : ℚ) : ℝ)) := by
  rw [G27_7_formula]
  exact vasyuninBEntry_7_27_eval

def interval_27_7 : NamedVasyuninInterval :=
{
  h := 27
  k := 7
  lower := (32032073/479270000)
  upper := (32127927/479270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_7_interval
}

theorem G27_8_formula : baezDuarteGramEntry 27 8 = vasyuninBEntry 8 27 := by
  rw [baezDuarteGramEntry_symm 27 8]
  exact G8_27_formula

theorem G27_8_interval :
    ((((8291033/129670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 8) ∧
    (baezDuarteGramEntry 27 8 ≤ (((8316967/129670000) : ℚ) : ℝ)) := by
  rw [G27_8_formula]
  exact vasyuninBEntry_8_27_eval

def interval_27_8 : NamedVasyuninInterval :=
{
  h := 27
  k := 8
  lower := (8291033/129670000)
  upper := (8316967/129670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_8_interval
}

theorem G27_9_formula : baezDuarteGramEntry 27 9 = vasyuninBEntry 9 27 := by
  rw [baezDuarteGramEntry_symm 27 9]
  exact G9_27_formula

theorem G27_9_interval :
    ((((32169569/504310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 9) ∧
    (baezDuarteGramEntry 27 9 ≤ (((32270431/504310000) : ℚ) : ℝ)) := by
  rw [G27_9_formula]
  exact vasyuninBEntry_9_27_eval

def interval_27_9 : NamedVasyuninInterval :=
{
  h := 27
  k := 9
  lower := (32169569/504310000)
  upper := (32270431/504310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_9_interval
}

theorem G27_10_formula : baezDuarteGramEntry 27 10 = vasyuninBEntry 10 27 := by
  rw [baezDuarteGramEntry_symm 27 10]
  exact G10_27_formula

theorem G27_10_interval :
    ((((13717033/229670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 10) ∧
    (baezDuarteGramEntry 27 10 ≤ (((13762967/229670000) : ℚ) : ℝ)) := by
  rw [G27_10_formula]
  exact vasyuninBEntry_10_27_eval

def interval_27_10 : NamedVasyuninInterval :=
{
  h := 27
  k := 10
  lower := (13717033/229670000)
  upper := (13762967/229670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_10_interval
}

theorem G27_11_formula : baezDuarteGramEntry 27 11 = vasyuninBEntry 11 27 := by
  rw [baezDuarteGramEntry_symm 27 11]
  exact G11_27_formula

theorem G27_11_interval :
    ((((5244943/90570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 11) ∧
    (baezDuarteGramEntry 27 11 ≤ (((5263057/90570000) : ℚ) : ℝ)) := by
  rw [G27_11_formula]
  exact vasyuninBEntry_11_27_eval

def interval_27_11 : NamedVasyuninInterval :=
{
  h := 27
  k := 11
  lower := (5244943/90570000)
  upper := (5263057/90570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_11_interval
}

theorem G27_12_formula : baezDuarteGramEntry 27 12 = vasyuninBEntry 12 27 := by
  rw [baezDuarteGramEntry_symm 27 12]
  exact G12_27_formula

theorem G27_12_interval :
    ((((54284103/958970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 12) ∧
    (baezDuarteGramEntry 27 12 ≤ (((54475897/958970000) : ℚ) : ℝ)) := by
  rw [G27_12_formula]
  exact vasyuninBEntry_12_27_eval

def interval_27_12 : NamedVasyuninInterval :=
{
  h := 27
  k := 12
  lower := (54284103/958970000)
  upper := (54475897/958970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_12_interval
}

theorem G27_13_formula : baezDuarteGramEntry 27 13 = vasyuninBEntry 13 27 := by
  rw [baezDuarteGramEntry_symm 27 13]
  exact G13_27_formula

theorem G27_13_interval :
    ((((29647261/527390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 13) ∧
    (baezDuarteGramEntry 27 13 ≤ (((29752739/527390000) : ℚ) : ℝ)) := by
  rw [G27_13_formula]
  exact vasyuninBEntry_13_27_eval

def interval_27_13 : NamedVasyuninInterval :=
{
  h := 27
  k := 13
  lower := (29647261/527390000)
  upper := (29752739/527390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_13_interval
}

theorem G27_14_formula : baezDuarteGramEntry 27 14 = vasyuninBEntry 14 27 := by
  rw [baezDuarteGramEntry_symm 27 14]
  exact G14_27_formula

theorem G27_14_interval :
    ((((13547757/247430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 14) ∧
    (baezDuarteGramEntry 27 14 ≤ (((13597243/247430000) : ℚ) : ℝ)) := by
  rw [G27_14_formula]
  exact vasyuninBEntry_14_27_eval

def interval_27_14 : NamedVasyuninInterval :=
{
  h := 27
  k := 14
  lower := (13547757/247430000)
  upper := (13597243/247430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_14_interval
}

theorem G27_15_formula : baezDuarteGramEntry 27 15 = vasyuninBEntry 15 27 := by
  rw [baezDuarteGramEntry_symm 27 15]
  exact G15_27_formula

theorem G27_15_interval :
    ((((17207117/328830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 15) ∧
    (baezDuarteGramEntry 27 15 ≤ (((17272883/328830000) : ℚ) : ℝ)) := by
  rw [G27_15_formula]
  exact vasyuninBEntry_15_27_eval

def interval_27_15 : NamedVasyuninInterval :=
{
  h := 27
  k := 15
  lower := (17207117/328830000)
  upper := (17272883/328830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_15_interval
}

theorem G27_16_formula : baezDuarteGramEntry 27 16 = vasyuninBEntry 16 27 := by
  rw [baezDuarteGramEntry_symm 27 16]
  exact G16_27_formula

theorem G27_16_interval :
    ((((42057073/829270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 16) ∧
    (baezDuarteGramEntry 27 16 ≤ (((42222927/829270000) : ℚ) : ℝ)) := by
  rw [G27_16_formula]
  exact vasyuninBEntry_16_27_eval

def interval_27_16 : NamedVasyuninInterval :=
{
  h := 27
  k := 16
  lower := (42057073/829270000)
  upper := (42222927/829270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_16_interval
}

theorem G27_17_formula : baezDuarteGramEntry 27 17 = vasyuninBEntry 17 27 := by
  rw [baezDuarteGramEntry_symm 27 17]
  exact G17_27_formula

theorem G27_17_interval :
    ((((35897419/725810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 17) ∧
    (baezDuarteGramEntry 27 17 ≤ (((36042581/725810000) : ℚ) : ℝ)) := by
  rw [G27_17_formula]
  exact vasyuninBEntry_17_27_eval

def interval_27_17 : NamedVasyuninInterval :=
{
  h := 27
  k := 17
  lower := (35897419/725810000)
  upper := (36042581/725810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_17_interval
}

theorem G27_18_formula : baezDuarteGramEntry 27 18 = vasyuninBEntry 18 27 := by
  rw [baezDuarteGramEntry_symm 27 18]
  exact G18_27_formula

theorem G27_18_interval :
    ((((6506697/133030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 18) ∧
    (baezDuarteGramEntry 27 18 ≤ (((6533303/133030000) : ℚ) : ℝ)) := by
  rw [G27_18_formula]
  exact vasyuninBEntry_18_27_eval

def interval_27_18 : NamedVasyuninInterval :=
{
  h := 27
  k := 18
  lower := (6506697/133030000)
  upper := (6533303/133030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_18_interval
}

theorem G27_19_formula : baezDuarteGramEntry 27 19 = vasyuninBEntry 19 27 := by
  rw [baezDuarteGramEntry_symm 27 19]
  exact G19_27_formula

theorem G27_19_interval :
    ((((19972921/420790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 19) ∧
    (baezDuarteGramEntry 27 19 ≤ (((20057079/420790000) : ℚ) : ℝ)) := by
  rw [G27_19_formula]
  exact vasyuninBEntry_19_27_eval

def interval_27_19 : NamedVasyuninInterval :=
{
  h := 27
  k := 19
  lower := (19972921/420790000)
  upper := (20057079/420790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_19_interval
}

theorem G27_20_formula : baezDuarteGramEntry 27 20 = vasyuninBEntry 20 27 := by
  rw [baezDuarteGramEntry_symm 27 20]
  exact G20_27_formula

theorem G27_20_interval :
    ((((7711481/165190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 20) ∧
    (baezDuarteGramEntry 27 20 ≤ (((7744519/165190000) : ℚ) : ℝ)) := by
  rw [G27_20_formula]
  exact vasyuninBEntry_20_27_eval

def interval_27_20 : NamedVasyuninInterval :=
{
  h := 27
  k := 20
  lower := (7711481/165190000)
  upper := (7744519/165190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_20_interval
}

theorem G27_21_formula : baezDuarteGramEntry 27 21 = vasyuninBEntry 21 27 := by
  rw [baezDuarteGramEntry_symm 27 21]
  exact G21_27_formula

theorem G27_21_interval :
    ((((11327863/246370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 21) ∧
    (baezDuarteGramEntry 27 21 ≤ (((11377137/246370000) : ℚ) : ℝ)) := by
  rw [G27_21_formula]
  exact vasyuninBEntry_21_27_eval

def interval_27_21 : NamedVasyuninInterval :=
{
  h := 27
  k := 21
  lower := (11327863/246370000)
  upper := (11377137/246370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_21_interval
}

theorem G27_22_formula : baezDuarteGramEntry 27 22 = vasyuninBEntry 22 27 := by
  rw [baezDuarteGramEntry_symm 27 22]
  exact G22_27_formula

theorem G27_22_interval :
    ((((9479139/208610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 22) ∧
    (baezDuarteGramEntry 27 22 ≤ (((9520861/208610000) : ℚ) : ℝ)) := by
  rw [G27_22_formula]
  exact vasyuninBEntry_22_27_eval

def interval_27_22 : NamedVasyuninInterval :=
{
  h := 27
  k := 22
  lower := (9479139/208610000)
  upper := (9520861/208610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_22_interval
}

theorem G27_23_formula : baezDuarteGramEntry 27 23 = vasyuninBEntry 23 27 := by
  rw [baezDuarteGramEntry_symm 27 23]
  exact G23_27_formula

theorem G27_23_interval :
    ((((29235137/648630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 23) ∧
    (baezDuarteGramEntry 27 23 ≤ (((29364863/648630000) : ℚ) : ℝ)) := by
  rw [G27_23_formula]
  exact vasyuninBEntry_23_27_eval

def interval_27_23 : NamedVasyuninInterval :=
{
  h := 27
  k := 23
  lower := (29235137/648630000)
  upper := (29364863/648630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_23_interval
}

theorem G27_24_formula : baezDuarteGramEntry 27 24 = vasyuninBEntry 24 27 := by
  rw [baezDuarteGramEntry_symm 27 24]
  exact G24_27_formula

theorem G27_24_interval :
    ((((43872281/977190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 24) ∧
    (baezDuarteGramEntry 27 24 ≤ (((44067719/977190000) : ℚ) : ℝ)) := by
  rw [G27_24_formula]
  exact vasyuninBEntry_24_27_eval

def interval_27_24 : NamedVasyuninInterval :=
{
  h := 27
  k := 24
  lower := (43872281/977190000)
  upper := (44067719/977190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_24_interval
}

theorem G27_25_formula : baezDuarteGramEntry 27 25 = vasyuninBEntry 25 27 := by
  rw [baezDuarteGramEntry_symm 27 25]
  exact G25_27_formula

theorem G27_25_interval :
    ((((15819791/352090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 25) ∧
    (baezDuarteGramEntry 27 25 ≤ (((15890209/352090000) : ℚ) : ℝ)) := by
  rw [G27_25_formula]
  exact vasyuninBEntry_25_27_eval

def interval_27_25 : NamedVasyuninInterval :=
{
  h := 27
  k := 25
  lower := (15819791/352090000)
  upper := (15890209/352090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_25_interval
}

theorem G27_26_formula : baezDuarteGramEntry 27 26 = vasyuninBEntry 26 27 := by
  rw [baezDuarteGramEntry_symm 27 26]
  exact G26_27_formula

theorem G27_26_interval :
    ((((6200317/136830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 26) ∧
    (baezDuarteGramEntry 27 26 ≤ (((6227683/136830000) : ℚ) : ℝ)) := by
  rw [G27_26_formula]
  exact vasyuninBEntry_26_27_eval

def interval_27_26 : NamedVasyuninInterval :=
{
  h := 27
  k := 26
  lower := (6200317/136830000)
  upper := (6227683/136830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_26_interval
}

theorem G27_27_formula_eq : baezDuarteGramEntry 27 27 = (1 / (27 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 27 := by norm_num
  rw [baez_duarte_diagonal_scaling 27 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G27_27_log_gamma_interval :
  ((((12553057/269430000) : ℚ) : ℝ) ≤ (1 / (27 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (27 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((12606943/269430000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 27 (by norm_num)
  constructor
  · have : ((((12553057/269430000) : ℚ) : ℝ) ≤ (1 / (27 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (27 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((12606943/269430000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G27_27_interval : ((((12553057/269430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 27) ∧ (baezDuarteGramEntry 27 27 ≤ (((12606943/269430000) : ℚ) : ℝ)) := by
  rw [G27_27_formula_eq]
  exact G27_27_log_gamma_interval

def interval_27_27 : NamedVasyuninInterval :=
{
  h := 27
  k := 27
  lower := (12553057/269430000)
  upper := (12606943/269430000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G27_27_interval
}

theorem G27_28_formula : baezDuarteGramEntry 27 28 = vasyuninBEntry 27 28 := vasyuninBEntry_correct_axiom 27 28 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_28_eval :
    ((((42502771/972290000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 28) ∧
    (vasyuninBEntry 27 28 ≤ (((42697229/972290000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2728_formula_bound
  constructor <;> linarith

theorem G27_28_interval :
    ((((42502771/972290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 28) ∧
    (baezDuarteGramEntry 27 28 ≤ (((42697229/972290000) : ℚ) : ℝ)) := by
  rw [G27_28_formula]
  exact vasyuninBEntry_27_28_eval

def interval_27_28 : NamedVasyuninInterval :=
{
  h := 27
  k := 28
  lower := (42502771/972290000)
  upper := (42697229/972290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_28_interval
}

theorem G27_29_formula : baezDuarteGramEntry 27 29 = vasyuninBEntry 27 29 := vasyuninBEntry_correct_axiom 27 29 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_29_eval :
    ((((40223891/961090000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 29) ∧
    (vasyuninBEntry 27 29 ≤ (((40416109/961090000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2729_formula_bound
  constructor <;> linarith

theorem G27_29_interval :
    ((((40223891/961090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 29) ∧
    (baezDuarteGramEntry 27 29 ≤ (((40416109/961090000) : ℚ) : ℝ)) := by
  rw [G27_29_formula]
  exact vasyuninBEntry_27_29_eval

def interval_27_29 : NamedVasyuninInterval :=
{
  h := 27
  k := 29
  lower := (40223891/961090000)
  upper := (40416109/961090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_29_interval
}

theorem G27_30_formula : baezDuarteGramEntry 27 30 = vasyuninBEntry 27 30 := vasyuninBEntry_correct_axiom 27 30 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_30_eval :
    ((((29546831/731690000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 30) ∧
    (vasyuninBEntry 27 30 ≤ (((29693169/731690000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 10 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G27_30_interval :
    ((((29546831/731690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 30) ∧
    (baezDuarteGramEntry 27 30 ≤ (((29693169/731690000) : ℚ) : ℝ)) := by
  rw [G27_30_formula]
  exact vasyuninBEntry_27_30_eval

def interval_27_30 : NamedVasyuninInterval :=
{
  h := 27
  k := 30
  lower := (29546831/731690000)
  upper := (29693169/731690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_30_interval
}

theorem G27_31_formula : baezDuarteGramEntry 27 31 = vasyuninBEntry 27 31 := vasyuninBEntry_correct_axiom 27 31 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_31_eval :
    ((((38950479/995210000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 31) ∧
    (vasyuninBEntry 27 31 ≤ (((39149521/995210000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2731_formula_bound
  constructor <;> linarith

theorem G27_31_interval :
    ((((38950479/995210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 31) ∧
    (baezDuarteGramEntry 27 31 ≤ (((39149521/995210000) : ℚ) : ℝ)) := by
  rw [G27_31_formula]
  exact vasyuninBEntry_27_31_eval

def interval_27_31 : NamedVasyuninInterval :=
{
  h := 27
  k := 31
  lower := (38950479/995210000)
  upper := (39149521/995210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_31_interval
}

theorem G27_32_formula : baezDuarteGramEntry 27 32 = vasyuninBEntry 27 32 := vasyuninBEntry_correct_axiom 27 32 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_32_eval :
    ((((7598041/199590000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 32) ∧
    (vasyuninBEntry 27 32 ≤ (((7637959/199590000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2732_formula_bound
  constructor <;> linarith

theorem G27_32_interval :
    ((((7598041/199590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 32) ∧
    (baezDuarteGramEntry 27 32 ≤ (((7637959/199590000) : ℚ) : ℝ)) := by
  rw [G27_32_formula]
  exact vasyuninBEntry_27_32_eval

def interval_27_32 : NamedVasyuninInterval :=
{
  h := 27
  k := 32
  lower := (7598041/199590000)
  upper := (7637959/199590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_32_interval
}

theorem G27_33_formula : baezDuarteGramEntry 27 33 = vasyuninBEntry 27 33 := vasyuninBEntry_correct_axiom 27 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_33_eval :
    ((((1775219/47810000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 33) ∧
    (vasyuninBEntry 27 33 ≤ (((1784781/47810000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 11 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G27_33_interval :
    ((((1775219/47810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 33) ∧
    (baezDuarteGramEntry 27 33 ≤ (((1784781/47810000) : ℚ) : ℝ)) := by
  rw [G27_33_formula]
  exact vasyuninBEntry_27_33_eval

def interval_27_33 : NamedVasyuninInterval :=
{
  h := 27
  k := 33
  lower := (1775219/47810000)
  upper := (1784781/47810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_33_interval
}

theorem G27_34_formula : baezDuarteGramEntry 27 34 = vasyuninBEntry 27 34 := vasyuninBEntry_correct_axiom 27 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_34_eval :
    ((((33308237/917630000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 34) ∧
    (vasyuninBEntry 27 34 ≤ (((33491763/917630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2734_formula_bound
  constructor <;> linarith

theorem G27_34_interval :
    ((((33308237/917630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 34) ∧
    (baezDuarteGramEntry 27 34 ≤ (((33491763/917630000) : ℚ) : ℝ)) := by
  rw [G27_34_formula]
  exact vasyuninBEntry_27_34_eval

def interval_27_34 : NamedVasyuninInterval :=
{
  h := 27
  k := 34
  lower := (33308237/917630000)
  upper := (33491763/917630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_34_interval
}

theorem G27_35_formula : baezDuarteGramEntry 27 35 = vasyuninBEntry 27 35 := vasyuninBEntry_correct_axiom 27 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_35_eval :
    ((((8860057/249430000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 35) ∧
    (vasyuninBEntry 27 35 ≤ (((8909943/249430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2735_formula_bound
  constructor <;> linarith

theorem G27_35_interval :
    ((((8860057/249430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 35) ∧
    (baezDuarteGramEntry 27 35 ≤ (((8909943/249430000) : ℚ) : ℝ)) := by
  rw [G27_35_formula]
  exact vasyuninBEntry_27_35_eval

def interval_27_35 : NamedVasyuninInterval :=
{
  h := 27
  k := 35
  lower := (8860057/249430000)
  upper := (8909943/249430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_35_interval
}

theorem G27_36_formula : baezDuarteGramEntry 27 36 = vasyuninBEntry 27 36 := vasyuninBEntry_correct_axiom 27 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_36_eval :
    ((((12603937/360630000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 36) ∧
    (vasyuninBEntry 27 36 ≤ (((12676063/360630000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 4 9 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 9)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 9)
  constructor <;> linarith

theorem G27_36_interval :
    ((((12603937/360630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 36) ∧
    (baezDuarteGramEntry 27 36 ≤ (((12676063/360630000) : ℚ) : ℝ)) := by
  rw [G27_36_formula]
  exact vasyuninBEntry_27_36_eval

def interval_27_36 : NamedVasyuninInterval :=
{
  h := 27
  k := 36
  lower := (12603937/360630000)
  upper := (12676063/360630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_36_interval
}

theorem G27_37_formula : baezDuarteGramEntry 27 37 = vasyuninBEntry 27 37 := vasyuninBEntry_correct_axiom 27 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_37_eval :
    ((((6261677/183230000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 37) ∧
    (vasyuninBEntry 27 37 ≤ (((6298323/183230000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2737_formula_bound
  constructor <;> linarith

theorem G27_37_interval :
    ((((6261677/183230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 37) ∧
    (baezDuarteGramEntry 27 37 ≤ (((6298323/183230000) : ℚ) : ℝ)) := by
  rw [G27_37_formula]
  exact vasyuninBEntry_27_37_eval

def interval_27_37 : NamedVasyuninInterval :=
{
  h := 27
  k := 37
  lower := (6261677/183230000)
  upper := (6298323/183230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_37_interval
}

theorem G27_38_formula : baezDuarteGramEntry 27 38 = vasyuninBEntry 27 38 := vasyuninBEntry_correct_axiom 27 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_38_eval :
    ((((5409889/161110000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 38) ∧
    (vasyuninBEntry 27 38 ≤ (((5442111/161110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2738_formula_bound
  constructor <;> linarith

theorem G27_38_interval :
    ((((5409889/161110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 38) ∧
    (baezDuarteGramEntry 27 38 ≤ (((5442111/161110000) : ℚ) : ℝ)) := by
  rw [G27_38_formula]
  exact vasyuninBEntry_27_38_eval

def interval_27_38 : NamedVasyuninInterval :=
{
  h := 27
  k := 38
  lower := (5409889/161110000)
  upper := (5442111/161110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_38_interval
}

theorem G27_39_formula : baezDuarteGramEntry 27 39 = vasyuninBEntry 27 39 := vasyuninBEntry_correct_axiom 27 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_39_eval :
    ((((5642929/170710000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 39) ∧
    (vasyuninBEntry 27 39 ≤ (((5677071/170710000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 13 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G27_39_interval :
    ((((5642929/170710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 39) ∧
    (baezDuarteGramEntry 27 39 ≤ (((5677071/170710000) : ℚ) : ℝ)) := by
  rw [G27_39_formula]
  exact vasyuninBEntry_27_39_eval

def interval_27_39 : NamedVasyuninInterval :=
{
  h := 27
  k := 39
  lower := (5642929/170710000)
  upper := (5677071/170710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_39_interval
}

theorem G27_40_formula : baezDuarteGramEntry 27 40 = vasyuninBEntry 27 40 := vasyuninBEntry_correct_axiom 27 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_40_eval :
    ((((27505753/842470000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 40) ∧
    (vasyuninBEntry 27 40 ≤ (((27674247/842470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2740_formula_bound
  constructor <;> linarith

theorem G27_40_interval :
    ((((27505753/842470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 40) ∧
    (baezDuarteGramEntry 27 40 ≤ (((27674247/842470000) : ℚ) : ℝ)) := by
  rw [G27_40_formula]
  exact vasyuninBEntry_27_40_eval

def interval_27_40 : NamedVasyuninInterval :=
{
  h := 27
  k := 40
  lower := (27505753/842470000)
  upper := (27674247/842470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_40_interval
}

theorem G27_41_formula : baezDuarteGramEntry 27 41 = vasyuninBEntry 27 41 := vasyuninBEntry_correct_axiom 27 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_41_eval :
    ((((3828091/119090000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 41) ∧
    (vasyuninBEntry 27 41 ≤ (((3851909/119090000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2741_formula_bound
  constructor <;> linarith

theorem G27_41_interval :
    ((((3828091/119090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 41) ∧
    (baezDuarteGramEntry 27 41 ≤ (((3851909/119090000) : ℚ) : ℝ)) := by
  rw [G27_41_formula]
  exact vasyuninBEntry_27_41_eval

def interval_27_41 : NamedVasyuninInterval :=
{
  h := 27
  k := 41
  lower := (3828091/119090000)
  upper := (3851909/119090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_41_interval
}

theorem G27_42_formula : baezDuarteGramEntry 27 42 = vasyuninBEntry 27 42 := vasyuninBEntry_correct_axiom 27 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_42_eval :
    ((((30822289/977110000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 42) ∧
    (vasyuninBEntry 27 42 ≤ (((31017711/977110000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_14_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 14 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G27_42_interval :
    ((((30822289/977110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 42) ∧
    (baezDuarteGramEntry 27 42 ≤ (((31017711/977110000) : ℚ) : ℝ)) := by
  rw [G27_42_formula]
  exact vasyuninBEntry_27_42_eval

def interval_27_42 : NamedVasyuninInterval :=
{
  h := 27
  k := 42
  lower := (30822289/977110000)
  upper := (31017711/977110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_42_interval
}

theorem G27_43_formula : baezDuarteGramEntry 27 43 = vasyuninBEntry 27 43 := vasyuninBEntry_correct_axiom 27 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_43_eval :
    ((((13451679/433210000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 43) ∧
    (vasyuninBEntry 27 43 ≤ (((13538321/433210000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2743_formula_bound
  constructor <;> linarith

theorem G27_43_interval :
    ((((13451679/433210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 43) ∧
    (baezDuarteGramEntry 27 43 ≤ (((13538321/433210000) : ℚ) : ℝ)) := by
  rw [G27_43_formula]
  exact vasyuninBEntry_27_43_eval

def interval_27_43 : NamedVasyuninInterval :=
{
  h := 27
  k := 43
  lower := (13451679/433210000)
  upper := (13538321/433210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_43_interval
}

theorem G27_44_formula : baezDuarteGramEntry 27 44 = vasyuninBEntry 27 44 := vasyuninBEntry_correct_axiom 27 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_44_eval :
    ((((1410393/46070000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 44) ∧
    (vasyuninBEntry 27 44 ≤ (((1419607/46070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2744_formula_bound
  constructor <;> linarith

theorem G27_44_interval :
    ((((1410393/46070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 44) ∧
    (baezDuarteGramEntry 27 44 ≤ (((1419607/46070000) : ℚ) : ℝ)) := by
  rw [G27_44_formula]
  exact vasyuninBEntry_27_44_eval

def interval_27_44 : NamedVasyuninInterval :=
{
  h := 27
  k := 44
  lower := (1410393/46070000)
  upper := (1419607/46070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_44_interval
}

theorem G27_45_formula : baezDuarteGramEntry 27 45 = vasyuninBEntry 27 45 := vasyuninBEntry_correct_axiom 27 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_45_eval :
    ((((30290017/999830000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 45) ∧
    (vasyuninBEntry 27 45 ≤ (((30489983/999830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 5 9 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 9)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 9)
  constructor <;> linarith

theorem G27_45_interval :
    ((((30290017/999830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 45) ∧
    (baezDuarteGramEntry 27 45 ≤ (((30489983/999830000) : ℚ) : ℝ)) := by
  rw [G27_45_formula]
  exact vasyuninBEntry_27_45_eval

def interval_27_45 : NamedVasyuninInterval :=
{
  h := 27
  k := 45
  lower := (30290017/999830000)
  upper := (30489983/999830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_45_interval
}

theorem G27_46_formula : baezDuarteGramEntry 27 46 = vasyuninBEntry 27 46 := vasyuninBEntry_correct_axiom 27 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_46_eval :
    ((((1143169/38310000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 46) ∧
    (vasyuninBEntry 27 46 ≤ (((1150831/38310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2746_formula_bound
  constructor <;> linarith

theorem G27_46_interval :
    ((((1143169/38310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 46) ∧
    (baezDuarteGramEntry 27 46 ≤ (((1150831/38310000) : ℚ) : ℝ)) := by
  rw [G27_46_formula]
  exact vasyuninBEntry_27_46_eval

def interval_27_46 : NamedVasyuninInterval :=
{
  h := 27
  k := 46
  lower := (1143169/38310000)
  upper := (1150831/38310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_46_interval
}

theorem G27_47_formula : baezDuarteGramEntry 27 47 = vasyuninBEntry 27 47 := vasyuninBEntry_correct_axiom 27 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_47_eval :
    ((((7153253/242470000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 47) ∧
    (vasyuninBEntry 27 47 ≤ (((7201747/242470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2747_formula_bound
  constructor <;> linarith

theorem G27_47_interval :
    ((((7153253/242470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 47) ∧
    (baezDuarteGramEntry 27 47 ≤ (((7201747/242470000) : ℚ) : ℝ)) := by
  rw [G27_47_formula]
  exact vasyuninBEntry_27_47_eval

def interval_27_47 : NamedVasyuninInterval :=
{
  h := 27
  k := 47
  lower := (7153253/242470000)
  upper := (7201747/242470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_47_interval
}

theorem G27_48_formula : baezDuarteGramEntry 27 48 = vasyuninBEntry 27 48 := vasyuninBEntry_correct_axiom 27 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_48_eval :
    ((((134539/4610000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 48) ∧
    (vasyuninBEntry 27 48 ≤ (((135461/4610000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_16_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 16 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G27_48_interval :
    ((((134539/4610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 48) ∧
    (baezDuarteGramEntry 27 48 ≤ (((135461/4610000) : ℚ) : ℝ)) := by
  rw [G27_48_formula]
  exact vasyuninBEntry_27_48_eval

def interval_27_48 : NamedVasyuninInterval :=
{
  h := 27
  k := 48
  lower := (134539/4610000)
  upper := (135461/4610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_48_interval
}

theorem G27_49_formula : baezDuarteGramEntry 27 49 = vasyuninBEntry 27 49 := vasyuninBEntry_correct_axiom 27 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_49_eval :
    ((((305817/10580000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 49) ∧
    (vasyuninBEntry 27 49 ≤ (((307933/10580000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2749_formula_bound
  constructor <;> linarith

theorem G27_49_interval :
    ((((305817/10580000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 49) ∧
    (baezDuarteGramEntry 27 49 ≤ (((307933/10580000) : ℚ) : ℝ)) := by
  rw [G27_49_formula]
  exact vasyuninBEntry_27_49_eval

def interval_27_49 : NamedVasyuninInterval :=
{
  h := 27
  k := 49
  lower := (305817/10580000)
  upper := (307933/10580000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_49_interval
}

theorem G27_50_formula : baezDuarteGramEntry 27 50 = vasyuninBEntry 27 50 := vasyuninBEntry_correct_axiom 27 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_27_50_eval :
    ((((13657361/476390000) : ℚ) : ℝ) ≤ vasyuninBEntry 27 50) ∧
    (vasyuninBEntry 27 50 ≤ (((13752639/476390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2750_formula_bound
  constructor <;> linarith

theorem G27_50_interval :
    ((((13657361/476390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 27 50) ∧
    (baezDuarteGramEntry 27 50 ≤ (((13752639/476390000) : ℚ) : ℝ)) := by
  rw [G27_50_formula]
  exact vasyuninBEntry_27_50_eval

def interval_27_50 : NamedVasyuninInterval :=
{
  h := 27
  k := 50
  lower := (13657361/476390000)
  upper := (13752639/476390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G27_50_interval
}

theorem G28_1_formula : baezDuarteGramEntry 28 1 = vasyuninBEntry 1 28 := by
  rw [baezDuarteGramEntry_symm 28 1]
  exact G1_28_formula

theorem G28_1_interval :
    ((((14749243/147570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 1) ∧
    (baezDuarteGramEntry 28 1 ≤ (((14778757/147570000) : ℚ) : ℝ)) := by
  rw [G28_1_formula]
  exact vasyuninBEntry_1_28_eval

def interval_28_1 : NamedVasyuninInterval :=
{
  h := 28
  k := 1
  lower := (14749243/147570000)
  upper := (14778757/147570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_1_interval
}

theorem G28_2_formula : baezDuarteGramEntry 28 2 = vasyuninBEntry 2 28 := by
  rw [baezDuarteGramEntry_symm 28 2]
  exact G2_28_formula

theorem G28_2_interval :
    ((((75094417/855830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 2) ∧
    (baezDuarteGramEntry 28 2 ≤ (((75265583/855830000) : ℚ) : ℝ)) := by
  rw [G28_2_formula]
  exact vasyuninBEntry_2_28_eval

def interval_28_2 : NamedVasyuninInterval :=
{
  h := 28
  k := 2
  lower := (75094417/855830000)
  upper := (75265583/855830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_2_interval
}

theorem G28_3_formula : baezDuarteGramEntry 28 3 = vasyuninBEntry 3 28 := by
  rw [baezDuarteGramEntry_symm 28 3]
  exact G3_28_formula

theorem G28_3_interval :
    ((((44074949/550510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 3) ∧
    (baezDuarteGramEntry 28 3 ≤ (((44185051/550510000) : ℚ) : ℝ)) := by
  rw [G28_3_formula]
  exact vasyuninBEntry_3_28_eval

def interval_28_3 : NamedVasyuninInterval :=
{
  h := 28
  k := 3
  lower := (44074949/550510000)
  upper := (44185051/550510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_3_interval
}

theorem G28_4_formula : baezDuarteGramEntry 28 4 = vasyuninBEntry 4 28 := by
  rw [baezDuarteGramEntry_symm 28 4]
  exact G4_28_formula

theorem G28_4_interval :
    ((((38818731/512690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 4) ∧
    (baezDuarteGramEntry 28 4 ≤ (((38921269/512690000) : ℚ) : ℝ)) := by
  rw [G28_4_formula]
  exact vasyuninBEntry_4_28_eval

def interval_28_4 : NamedVasyuninInterval :=
{
  h := 28
  k := 4
  lower := (38818731/512690000)
  upper := (38921269/512690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_4_interval
}

theorem G28_5_formula : baezDuarteGramEntry 28 5 = vasyuninBEntry 5 28 := by
  rw [baezDuarteGramEntry_symm 28 5]
  exact G5_28_formula

theorem G28_5_interval :
    ((((1402619/19810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 5) ∧
    (baezDuarteGramEntry 28 5 ≤ (((1406581/19810000) : ℚ) : ℝ)) := by
  rw [G28_5_formula]
  exact vasyuninBEntry_5_28_eval

def interval_28_5 : NamedVasyuninInterval :=
{
  h := 28
  k := 5
  lower := (1402619/19810000)
  upper := (1406581/19810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_5_interval
}

theorem G28_6_formula : baezDuarteGramEntry 28 6 = vasyuninBEntry 6 28 := by
  rw [baezDuarteGramEntry_symm 28 6]
  exact G6_28_formula

theorem G28_6_interval :
    ((((20589527/304730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 6) ∧
    (baezDuarteGramEntry 28 6 ≤ (((20650473/304730000) : ℚ) : ℝ)) := by
  rw [G28_6_formula]
  exact vasyuninBEntry_6_28_eval

def interval_28_6 : NamedVasyuninInterval :=
{
  h := 28
  k := 6
  lower := (20589527/304730000)
  upper := (20650473/304730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_6_interval
}

theorem G28_7_formula : baezDuarteGramEntry 28 7 = vasyuninBEntry 7 28 := by
  rw [baezDuarteGramEntry_symm 28 7]
  exact G7_28_formula

theorem G28_7_interval :
    ((((1518957/22930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 7) ∧
    (baezDuarteGramEntry 28 7 ≤ (((1523543/22930000) : ℚ) : ℝ)) := by
  rw [G28_7_formula]
  exact vasyuninBEntry_7_28_eval

def interval_28_7 : NamedVasyuninInterval :=
{
  h := 28
  k := 7
  lower := (1518957/22930000)
  upper := (1523543/22930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_7_interval
}

theorem G28_8_formula : baezDuarteGramEntry 28 8 = vasyuninBEntry 8 28 := by
  rw [baezDuarteGramEntry_symm 28 8]
  exact G8_28_formula

theorem G28_8_interval :
    ((((51627357/826430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 8) ∧
    (baezDuarteGramEntry 28 8 ≤ (((51792643/826430000) : ℚ) : ℝ)) := by
  rw [G28_8_formula]
  exact vasyuninBEntry_8_28_eval

def interval_28_8 : NamedVasyuninInterval :=
{
  h := 28
  k := 8
  lower := (51627357/826430000)
  upper := (51792643/826430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_8_interval
}

theorem G28_9_formula : baezDuarteGramEntry 28 9 = vasyuninBEntry 9 28 := by
  rw [baezDuarteGramEntry_symm 28 9]
  exact G9_28_formula

theorem G28_9_interval :
    ((((2958641/48590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 9) ∧
    (baezDuarteGramEntry 28 9 ≤ (((2968359/48590000) : ℚ) : ℝ)) := by
  rw [G28_9_formula]
  exact vasyuninBEntry_9_28_eval

def interval_28_9 : NamedVasyuninInterval :=
{
  h := 28
  k := 9
  lower := (2958641/48590000)
  upper := (2968359/48590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_9_interval
}

theorem G28_10_formula : baezDuarteGramEntry 28 10 = vasyuninBEntry 10 28 := by
  rw [baezDuarteGramEntry_symm 28 10]
  exact G10_28_formula

theorem G28_10_interval :
    ((((1922713/32870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 10) ∧
    (baezDuarteGramEntry 28 10 ≤ (((1929287/32870000) : ℚ) : ℝ)) := by
  rw [G28_10_formula]
  exact vasyuninBEntry_10_28_eval

def interval_28_10 : NamedVasyuninInterval :=
{
  h := 28
  k := 10
  lower := (1922713/32870000)
  upper := (1929287/32870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_10_interval
}

theorem G28_11_formula : baezDuarteGramEntry 28 11 = vasyuninBEntry 11 28 := by
  rw [baezDuarteGramEntry_symm 28 11]
  exact G11_28_formula

theorem G28_11_interval :
    ((((48823551/864490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 11) ∧
    (baezDuarteGramEntry 28 11 ≤ (((48996449/864490000) : ℚ) : ℝ)) := by
  rw [G28_11_formula]
  exact vasyuninBEntry_11_28_eval

def interval_28_11 : NamedVasyuninInterval :=
{
  h := 28
  k := 11
  lower := (48823551/864490000)
  upper := (48996449/864490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_11_interval
}

theorem G28_12_formula : baezDuarteGramEntry 28 12 = vasyuninBEntry 12 28 := by
  rw [baezDuarteGramEntry_symm 28 12]
  exact G12_28_formula

theorem G28_12_interval :
    ((((22289539/404610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 12) ∧
    (baezDuarteGramEntry 28 12 ≤ (((22370461/404610000) : ℚ) : ℝ)) := by
  rw [G28_12_formula]
  exact vasyuninBEntry_12_28_eval

def interval_28_12 : NamedVasyuninInterval :=
{
  h := 28
  k := 12
  lower := (22289539/404610000)
  upper := (22370461/404610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_12_interval
}

theorem G28_13_formula : baezDuarteGramEntry 28 13 = vasyuninBEntry 13 28 := by
  rw [baezDuarteGramEntry_symm 28 13]
  exact G13_28_formula

theorem G28_13_interval :
    ((((79129/1460000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 13) ∧
    (baezDuarteGramEntry 28 13 ≤ (((79421/1460000) : ℚ) : ℝ)) := by
  rw [G28_13_formula]
  exact vasyuninBEntry_13_28_eval

def interval_28_13 : NamedVasyuninInterval :=
{
  h := 28
  k := 13
  lower := (79129/1460000)
  upper := (79421/1460000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_13_interval
}

theorem G28_14_formula : baezDuarteGramEntry 28 14 = vasyuninBEntry 14 28 := by
  rw [baezDuarteGramEntry_symm 28 14]
  exact G14_28_formula

theorem G28_14_interval :
    ((((24300863/441370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 14) ∧
    (baezDuarteGramEntry 28 14 ≤ (((24389137/441370000) : ℚ) : ℝ)) := by
  rw [G28_14_formula]
  exact vasyuninBEntry_14_28_eval

def interval_28_14 : NamedVasyuninInterval :=
{
  h := 28
  k := 14
  lower := (24300863/441370000)
  upper := (24389137/441370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_14_interval
}

theorem G28_15_formula : baezDuarteGramEntry 28 15 = vasyuninBEntry 15 28 := by
  rw [baezDuarteGramEntry_symm 28 15]
  exact G15_28_formula

theorem G28_15_interval :
    ((((32506923/630770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 15) ∧
    (baezDuarteGramEntry 28 15 ≤ (((32633077/630770000) : ℚ) : ℝ)) := by
  rw [G28_15_formula]
  exact vasyuninBEntry_15_28_eval

def interval_28_15 : NamedVasyuninInterval :=
{
  h := 28
  k := 15
  lower := (32506923/630770000)
  upper := (32633077/630770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_15_interval
}

theorem G28_16_formula : baezDuarteGramEntry 28 16 = vasyuninBEntry 16 28 := by
  rw [baezDuarteGramEntry_symm 28 16]
  exact G16_28_formula

theorem G28_16_interval :
    ((((12330219/247810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 16) ∧
    (baezDuarteGramEntry 28 16 ≤ (((12379781/247810000) : ℚ) : ℝ)) := by
  rw [G28_16_formula]
  exact vasyuninBEntry_16_28_eval

def interval_28_16 : NamedVasyuninInterval :=
{
  h := 28
  k := 16
  lower := (12330219/247810000)
  upper := (12379781/247810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_16_interval
}

theorem G28_17_formula : baezDuarteGramEntry 28 17 = vasyuninBEntry 17 28 := by
  rw [baezDuarteGramEntry_symm 28 17]
  exact G17_28_formula

theorem G28_17_interval :
    ((((706141/14590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 17) ∧
    (baezDuarteGramEntry 28 17 ≤ (((709059/14590000) : ℚ) : ℝ)) := by
  rw [G28_17_formula]
  exact vasyuninBEntry_17_28_eval

def interval_28_17 : NamedVasyuninInterval :=
{
  h := 28
  k := 17
  lower := (706141/14590000)
  upper := (709059/14590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_17_interval
}

theorem G28_18_formula : baezDuarteGramEntry 28 18 = vasyuninBEntry 18 28 := by
  rw [baezDuarteGramEntry_symm 28 18]
  exact G18_28_formula

theorem G28_18_interval :
    ((((46282289/977110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 18) ∧
    (baezDuarteGramEntry 28 18 ≤ (((46477711/977110000) : ℚ) : ℝ)) := by
  rw [G28_18_formula]
  exact vasyuninBEntry_18_28_eval

def interval_28_18 : NamedVasyuninInterval :=
{
  h := 28
  k := 18
  lower := (46282289/977110000)
  upper := (46477711/977110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_18_interval
}

end RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
