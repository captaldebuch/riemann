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

namespace RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Certificates.Generated

theorem G32_47_formula : baezDuarteGramEntry 32 47 = vasyuninBEntry 32 47 := vasyuninBEntry_correct_axiom 32 47

theorem vasyuninBEntry_32_47_eval :
    ((((20605429/745710000) : ℚ) : ℝ) ≤ vasyuninBEntry 32 47) ∧
    (vasyuninBEntry 32 47 ≤ (((20754571/745710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3247_formula_bound
  constructor <;> linarith

theorem G32_47_interval :
    ((((20605429/745710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 47) ∧
    (baezDuarteGramEntry 32 47 ≤ (((20754571/745710000) : ℚ) : ℝ)) := by
  rw [G32_47_formula]
  exact vasyuninBEntry_32_47_eval

def interval_32_47 : NamedVasyuninInterval :=
{
  h := 32
  k := 47
  lower := (20605429/745710000)
  upper := (20754571/745710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_47_interval
}

theorem G32_48_formula : baezDuarteGramEntry 32 48 = vasyuninBEntry 32 48 := vasyuninBEntry_correct_axiom 32 48

theorem vasyuninBEntry_32_48_eval :
    ((((3654197/133030000) : ℚ) : ℝ) ≤ vasyuninBEntry 32 48) ∧
    (vasyuninBEntry 32 48 ≤ (((3680803/133030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 16 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 16)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 16)
  constructor <;> linarith

theorem G32_48_interval :
    ((((3654197/133030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 48) ∧
    (baezDuarteGramEntry 32 48 ≤ (((3680803/133030000) : ℚ) : ℝ)) := by
  rw [G32_48_formula]
  exact vasyuninBEntry_32_48_eval

def interval_32_48 : NamedVasyuninInterval :=
{
  h := 32
  k := 48
  lower := (3654197/133030000)
  upper := (3680803/133030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_48_interval
}

theorem G32_49_formula : baezDuarteGramEntry 32 49 = vasyuninBEntry 32 49 := vasyuninBEntry_correct_axiom 32 49

theorem vasyuninBEntry_32_49_eval :
    ((((14296881/531190000) : ℚ) : ℝ) ≤ vasyuninBEntry 32 49) ∧
    (vasyuninBEntry 32 49 ≤ (((14403119/531190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3249_formula_bound
  constructor <;> linarith

theorem G32_49_interval :
    ((((14296881/531190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 49) ∧
    (baezDuarteGramEntry 32 49 ≤ (((14403119/531190000) : ℚ) : ℝ)) := by
  rw [G32_49_formula]
  exact vasyuninBEntry_32_49_eval

def interval_32_49 : NamedVasyuninInterval :=
{
  h := 32
  k := 49
  lower := (14296881/531190000)
  upper := (14403119/531190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_49_interval
}

theorem G32_50_formula : baezDuarteGramEntry 32 50 = vasyuninBEntry 32 50 := vasyuninBEntry_correct_axiom 32 50

theorem vasyuninBEntry_32_50_eval :
    ((((6089533/229670000) : ℚ) : ℝ) ≤ vasyuninBEntry 32 50) ∧
    (vasyuninBEntry 32 50 ≤ (((6135467/229670000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_16_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 16 25 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G32_50_interval :
    ((((6089533/229670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 50) ∧
    (baezDuarteGramEntry 32 50 ≤ (((6135467/229670000) : ℚ) : ℝ)) := by
  rw [G32_50_formula]
  exact vasyuninBEntry_32_50_eval

def interval_32_50 : NamedVasyuninInterval :=
{
  h := 32
  k := 50
  lower := (6089533/229670000)
  upper := (6135467/229670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_50_interval
}

theorem G33_1_formula : baezDuarteGramEntry 33 1 = vasyuninBEntry 1 33 := by
  rw [baezDuarteGramEntry_symm 33 1]
  exact G1_33_formula

theorem G33_1_interval :
    ((((61299747/702530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 1) ∧
    (baezDuarteGramEntry 33 1 ≤ (((61440253/702530000) : ℚ) : ℝ)) := by
  rw [G33_1_formula]
  exact vasyuninBEntry_1_33_eval

def interval_33_1 : NamedVasyuninInterval :=
{
  h := 33
  k := 1
  lower := (61299747/702530000)
  upper := (61440253/702530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_1_interval
}

theorem G33_2_formula : baezDuarteGramEntry 33 2 = vasyuninBEntry 2 33 := by
  rw [baezDuarteGramEntry_symm 33 2]
  exact G2_33_formula

theorem G33_2_interval :
    ((((76350321/996790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 2) ∧
    (baezDuarteGramEntry 33 2 ≤ (((76549679/996790000) : ℚ) : ℝ)) := by
  rw [G33_2_formula]
  exact vasyuninBEntry_2_33_eval

def interval_33_2 : NamedVasyuninInterval :=
{
  h := 33
  k := 2
  lower := (76350321/996790000)
  upper := (76549679/996790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_2_interval
}

theorem G33_3_formula : baezDuarteGramEntry 33 3 = vasyuninBEntry 3 33 := by
  rw [baezDuarteGramEntry_symm 33 3]
  exact G3_33_formula

theorem G33_3_interval :
    ((((31325793/442070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 3) ∧
    (baezDuarteGramEntry 33 3 ≤ (((31414207/442070000) : ℚ) : ℝ)) := by
  rw [G33_3_formula]
  exact vasyuninBEntry_3_33_eval

def interval_33_3 : NamedVasyuninInterval :=
{
  h := 33
  k := 3
  lower := (31325793/442070000)
  upper := (31414207/442070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_3_interval
}

theorem G33_4_formula : baezDuarteGramEntry 33 4 = vasyuninBEntry 4 33 := by
  rw [baezDuarteGramEntry_symm 33 4]
  exact G4_33_formula

theorem G33_4_interval :
    ((((8676867/131330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 4) ∧
    (baezDuarteGramEntry 33 4 ≤ (((8703133/131330000) : ℚ) : ℝ)) := by
  rw [G33_4_formula]
  exact vasyuninBEntry_4_33_eval

def interval_33_4 : NamedVasyuninInterval :=
{
  h := 33
  k := 4
  lower := (8676867/131330000)
  upper := (8703133/131330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_4_interval
}

theorem G33_5_formula : baezDuarteGramEntry 33 5 = vasyuninBEntry 5 33 := by
  rw [baezDuarteGramEntry_symm 33 5]
  exact G5_33_formula

theorem G33_5_interval :
    ((((19768411/315890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 5) ∧
    (baezDuarteGramEntry 33 5 ≤ (((19831589/315890000) : ℚ) : ℝ)) := by
  rw [G33_5_formula]
  exact vasyuninBEntry_5_33_eval

def interval_33_5 : NamedVasyuninInterval :=
{
  h := 33
  k := 5
  lower := (19768411/315890000)
  upper := (19831589/315890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_5_interval
}

theorem G33_6_formula : baezDuarteGramEntry 33 6 = vasyuninBEntry 6 33 := by
  rw [baezDuarteGramEntry_symm 33 6]
  exact G6_33_formula

theorem G33_6_interval :
    ((((52302667/873330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 6) ∧
    (baezDuarteGramEntry 33 6 ≤ (((52477333/873330000) : ℚ) : ℝ)) := by
  rw [G33_6_formula]
  exact vasyuninBEntry_6_33_eval

def interval_33_6 : NamedVasyuninInterval :=
{
  h := 33
  k := 6
  lower := (52302667/873330000)
  upper := (52477333/873330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_6_interval
}

theorem G33_7_formula : baezDuarteGramEntry 33 7 = vasyuninBEntry 7 33 := by
  rw [baezDuarteGramEntry_symm 33 7]
  exact G7_33_formula

theorem G33_7_interval :
    ((((47127989/820110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 7) ∧
    (baezDuarteGramEntry 33 7 ≤ (((47292011/820110000) : ℚ) : ℝ)) := by
  rw [G33_7_formula]
  exact vasyuninBEntry_7_33_eval

def interval_33_7 : NamedVasyuninInterval :=
{
  h := 33
  k := 7
  lower := (47127989/820110000)
  upper := (47292011/820110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_7_interval
}

theorem G33_8_formula : baezDuarteGramEntry 33 8 = vasyuninBEntry 8 33 := by
  rw [baezDuarteGramEntry_symm 33 8]
  exact G8_33_formula

theorem G33_8_interval :
    ((((53583961/960390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 8) ∧
    (baezDuarteGramEntry 33 8 ≤ (((53776039/960390000) : ℚ) : ℝ)) := by
  rw [G33_8_formula]
  exact vasyuninBEntry_8_33_eval

def interval_33_8 : NamedVasyuninInterval :=
{
  h := 33
  k := 8
  lower := (53583961/960390000)
  upper := (53776039/960390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_8_interval
}

theorem G33_9_formula : baezDuarteGramEntry 33 9 = vasyuninBEntry 9 33 := by
  rw [baezDuarteGramEntry_symm 33 9]
  exact G9_33_formula

theorem G33_9_interval :
    ((((14727527/274730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 9) ∧
    (baezDuarteGramEntry 33 9 ≤ (((14782473/274730000) : ℚ) : ℝ)) := by
  rw [G33_9_formula]
  exact vasyuninBEntry_9_33_eval

def interval_33_9 : NamedVasyuninInterval :=
{
  h := 33
  k := 9
  lower := (14727527/274730000)
  upper := (14782473/274730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_9_interval
}

theorem G33_10_formula : baezDuarteGramEntry 33 10 = vasyuninBEntry 10 33 := by
  rw [baezDuarteGramEntry_symm 33 10]
  exact G10_33_formula

theorem G33_10_interval :
    ((((25471043/489570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 10) ∧
    (baezDuarteGramEntry 33 10 ≤ (((25568957/489570000) : ℚ) : ℝ)) := by
  rw [G33_10_formula]
  exact vasyuninBEntry_10_33_eval

def interval_33_10 : NamedVasyuninInterval :=
{
  h := 33
  k := 10
  lower := (25471043/489570000)
  upper := (25568957/489570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_10_interval
}

theorem G33_11_formula : baezDuarteGramEntry 33 11 = vasyuninBEntry 11 33 := by
  rw [baezDuarteGramEntry_symm 33 11]
  exact G11_33_formula

theorem G33_11_interval :
    ((((3752807/71930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 11) ∧
    (baezDuarteGramEntry 33 11 ≤ (((3767193/71930000) : ℚ) : ℝ)) := by
  rw [G33_11_formula]
  exact vasyuninBEntry_11_33_eval

def interval_33_11 : NamedVasyuninInterval :=
{
  h := 33
  k := 11
  lower := (3752807/71930000)
  upper := (3767193/71930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_11_interval
}

theorem G33_12_formula : baezDuarteGramEntry 33 12 = vasyuninBEntry 12 33 := by
  rw [baezDuarteGramEntry_symm 33 12]
  exact G12_33_formula

theorem G33_12_interval :
    ((((19106193/388070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 12) ∧
    (baezDuarteGramEntry 33 12 ≤ (((19183807/388070000) : ℚ) : ℝ)) := by
  rw [G33_12_formula]
  exact vasyuninBEntry_12_33_eval

def interval_33_12 : NamedVasyuninInterval :=
{
  h := 33
  k := 12
  lower := (19106193/388070000)
  upper := (19183807/388070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_12_interval
}

theorem G33_13_formula : baezDuarteGramEntry 33 13 = vasyuninBEntry 13 33 := by
  rw [baezDuarteGramEntry_symm 33 13]
  exact G13_33_formula

theorem G33_13_interval :
    ((((6895597/144030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 13) ∧
    (baezDuarteGramEntry 33 13 ≤ (((6924403/144030000) : ℚ) : ℝ)) := by
  rw [G33_13_formula]
  exact vasyuninBEntry_13_33_eval

def interval_33_13 : NamedVasyuninInterval :=
{
  h := 33
  k := 13
  lower := (6895597/144030000)
  upper := (6924403/144030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_13_interval
}

theorem G33_14_formula : baezDuarteGramEntry 33 14 = vasyuninBEntry 14 33 := by
  rw [baezDuarteGramEntry_symm 33 14]
  exact G14_33_formula

theorem G33_14_interval :
    ((((4819697/103030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 14) ∧
    (baezDuarteGramEntry 33 14 ≤ (((4840303/103030000) : ℚ) : ℝ)) := by
  rw [G33_14_formula]
  exact vasyuninBEntry_14_33_eval

def interval_33_14 : NamedVasyuninInterval :=
{
  h := 33
  k := 14
  lower := (4819697/103030000)
  upper := (4840303/103030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_14_interval
}

theorem G33_15_formula : baezDuarteGramEntry 33 15 = vasyuninBEntry 15 33 := by
  rw [baezDuarteGramEntry_symm 33 15]
  exact G15_33_formula

theorem G33_15_interval :
    ((((40362447/875530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 15) ∧
    (baezDuarteGramEntry 33 15 ≤ (((40537553/875530000) : ℚ) : ℝ)) := by
  rw [G33_15_formula]
  exact vasyuninBEntry_15_33_eval

def interval_33_15 : NamedVasyuninInterval :=
{
  h := 33
  k := 15
  lower := (40362447/875530000)
  upper := (40537553/875530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_15_interval
}

theorem G33_16_formula : baezDuarteGramEntry 33 16 = vasyuninBEntry 16 33 := by
  rw [baezDuarteGramEntry_symm 33 16]
  exact G16_33_formula

theorem G33_16_interval :
    ((((1251281/27190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 16) ∧
    (baezDuarteGramEntry 33 16 ≤ (((1256719/27190000) : ℚ) : ℝ)) := by
  rw [G33_16_formula]
  exact vasyuninBEntry_16_33_eval

def interval_33_16 : NamedVasyuninInterval :=
{
  h := 33
  k := 16
  lower := (1251281/27190000)
  upper := (1256719/27190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_16_interval
}

theorem G33_17_formula : baezDuarteGramEntry 33 17 = vasyuninBEntry 17 33 := by
  rw [baezDuarteGramEntry_symm 33 17]
  exact G17_33_formula

theorem G33_17_interval :
    ((((5036317/111830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 17) ∧
    (baezDuarteGramEntry 33 17 ≤ (((5058683/111830000) : ℚ) : ℝ)) := by
  rw [G33_17_formula]
  exact vasyuninBEntry_17_33_eval

def interval_33_17 : NamedVasyuninInterval :=
{
  h := 33
  k := 17
  lower := (5036317/111830000)
  upper := (5058683/111830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_17_interval
}

theorem G33_18_formula : baezDuarteGramEntry 33 18 = vasyuninBEntry 18 33 := by
  rw [baezDuarteGramEntry_symm 33 18]
  exact G18_33_formula

theorem G33_18_interval :
    ((((18606963/430370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 18) ∧
    (baezDuarteGramEntry 33 18 ≤ (((18693037/430370000) : ℚ) : ℝ)) := by
  rw [G33_18_formula]
  exact vasyuninBEntry_18_33_eval

def interval_33_18 : NamedVasyuninInterval :=
{
  h := 33
  k := 18
  lower := (18606963/430370000)
  upper := (18693037/430370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_18_interval
}

theorem G33_19_formula : baezDuarteGramEntry 33 19 = vasyuninBEntry 19 33 := by
  rw [baezDuarteGramEntry_symm 33 19]
  exact G19_33_formula

theorem G33_19_interval :
    ((((7943591/189090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 19) ∧
    (baezDuarteGramEntry 33 19 ≤ (((7981409/189090000) : ℚ) : ℝ)) := by
  rw [G33_19_formula]
  exact vasyuninBEntry_19_33_eval

def interval_33_19 : NamedVasyuninInterval :=
{
  h := 33
  k := 19
  lower := (7943591/189090000)
  upper := (7981409/189090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_19_interval
}

theorem G33_20_formula : baezDuarteGramEntry 33 20 = vasyuninBEntry 20 33 := by
  rw [baezDuarteGramEntry_symm 33 20]
  exact G20_33_formula

theorem G33_20_interval :
    ((((37528661/913390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 20) ∧
    (baezDuarteGramEntry 33 20 ≤ (((37711339/913390000) : ℚ) : ℝ)) := by
  rw [G33_20_formula]
  exact vasyuninBEntry_20_33_eval

def interval_33_20 : NamedVasyuninInterval :=
{
  h := 33
  k := 20
  lower := (37528661/913390000)
  upper := (37711339/913390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_20_interval
}

theorem G33_21_formula : baezDuarteGramEntry 33 21 = vasyuninBEntry 21 33 := by
  rw [baezDuarteGramEntry_symm 33 21]
  exact G21_33_formula

theorem G33_21_interval :
    ((((8705901/215990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 21) ∧
    (baezDuarteGramEntry 33 21 ≤ (((8749099/215990000) : ℚ) : ℝ)) := by
  rw [G33_21_formula]
  exact vasyuninBEntry_21_33_eval

def interval_33_21 : NamedVasyuninInterval :=
{
  h := 33
  k := 21
  lower := (8705901/215990000)
  upper := (8749099/215990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_21_interval
}

theorem G33_22_formula : baezDuarteGramEntry 33 22 = vasyuninBEntry 22 33 := by
  rw [baezDuarteGramEntry_symm 33 22]
  exact G22_33_formula

theorem G33_22_interval :
    ((((14673317/366830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 22) ∧
    (baezDuarteGramEntry 33 22 ≤ (((14746683/366830000) : ℚ) : ℝ)) := by
  rw [G33_22_formula]
  exact vasyuninBEntry_22_33_eval

def interval_33_22 : NamedVasyuninInterval :=
{
  h := 33
  k := 22
  lower := (14673317/366830000)
  upper := (14746683/366830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_22_interval
}

theorem G33_23_formula : baezDuarteGramEntry 33 23 = vasyuninBEntry 23 33 := by
  rw [baezDuarteGramEntry_symm 33 23]
  exact G23_33_formula

theorem G33_23_interval :
    ((((1830303/46970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 23) ∧
    (baezDuarteGramEntry 33 23 ≤ (((1839697/46970000) : ℚ) : ℝ)) := by
  rw [G33_23_formula]
  exact vasyuninBEntry_23_33_eval

def interval_33_23 : NamedVasyuninInterval :=
{
  h := 33
  k := 23
  lower := (1830303/46970000)
  upper := (1839697/46970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_23_interval
}

theorem G33_24_formula : baezDuarteGramEntry 33 24 = vasyuninBEntry 24 33 := by
  rw [baezDuarteGramEntry_symm 33 24]
  exact G24_33_formula

theorem G33_24_interval :
    ((((9253387/241130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 24) ∧
    (baezDuarteGramEntry 33 24 ≤ (((9301613/241130000) : ℚ) : ℝ)) := by
  rw [G33_24_formula]
  exact vasyuninBEntry_24_33_eval

def interval_33_24 : NamedVasyuninInterval :=
{
  h := 33
  k := 24
  lower := (9253387/241130000)
  upper := (9301613/241130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_24_interval
}

theorem G33_25_formula : baezDuarteGramEntry 33 25 = vasyuninBEntry 25 33 := by
  rw [baezDuarteGramEntry_symm 33 25]
  exact G25_33_formula

theorem G33_25_interval :
    ((((19019847/501530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 25) ∧
    (baezDuarteGramEntry 33 25 ≤ (((19120153/501530000) : ℚ) : ℝ)) := by
  rw [G33_25_formula]
  exact vasyuninBEntry_25_33_eval

def interval_33_25 : NamedVasyuninInterval :=
{
  h := 33
  k := 25
  lower := (19019847/501530000)
  upper := (19120153/501530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_25_interval
}

theorem G33_26_formula : baezDuarteGramEntry 33 26 = vasyuninBEntry 26 33 := by
  rw [baezDuarteGramEntry_symm 33 26]
  exact G26_33_formula

theorem G33_26_interval :
    ((((15109667/403330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 26) ∧
    (baezDuarteGramEntry 33 26 ≤ (((15190333/403330000) : ℚ) : ℝ)) := by
  rw [G33_26_formula]
  exact vasyuninBEntry_26_33_eval

def interval_33_26 : NamedVasyuninInterval :=
{
  h := 33
  k := 26
  lower := (15109667/403330000)
  upper := (15190333/403330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_26_interval
}

theorem G33_27_formula : baezDuarteGramEntry 33 27 = vasyuninBEntry 27 33 := by
  rw [baezDuarteGramEntry_symm 33 27]
  exact G27_33_formula

theorem G33_27_interval :
    ((((1775219/47810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 27) ∧
    (baezDuarteGramEntry 33 27 ≤ (((1784781/47810000) : ℚ) : ℝ)) := by
  rw [G33_27_formula]
  exact vasyuninBEntry_27_33_eval

def interval_33_27 : NamedVasyuninInterval :=
{
  h := 33
  k := 27
  lower := (1775219/47810000)
  upper := (1784781/47810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_27_interval
}

theorem G33_28_formula : baezDuarteGramEntry 33 28 = vasyuninBEntry 28 33 := by
  rw [baezDuarteGramEntry_symm 33 28]
  exact G28_33_formula

theorem G33_28_interval :
    ((((19158051/519490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 28) ∧
    (baezDuarteGramEntry 33 28 ≤ (((19261949/519490000) : ℚ) : ℝ)) := by
  rw [G33_28_formula]
  exact vasyuninBEntry_28_33_eval

def interval_33_28 : NamedVasyuninInterval :=
{
  h := 33
  k := 28
  lower := (19158051/519490000)
  upper := (19261949/519490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_28_interval
}

theorem G33_29_formula : baezDuarteGramEntry 33 29 = vasyuninBEntry 29 33 := by
  rw [baezDuarteGramEntry_symm 33 29]
  exact G29_33_formula

theorem G33_29_interval :
    ((((33758097/919030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 29) ∧
    (baezDuarteGramEntry 33 29 ≤ (((33941903/919030000) : ℚ) : ℝ)) := by
  rw [G33_29_formula]
  exact vasyuninBEntry_29_33_eval

def interval_33_29 : NamedVasyuninInterval :=
{
  h := 33
  k := 29
  lower := (33758097/919030000)
  upper := (33941903/919030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_29_interval
}

theorem G33_30_formula : baezDuarteGramEntry 33 30 = vasyuninBEntry 30 33 := by
  rw [baezDuarteGramEntry_symm 33 30]
  exact G30_33_formula

theorem G33_30_interval :
    ((((32920309/896910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 30) ∧
    (baezDuarteGramEntry 33 30 ≤ (((33099691/896910000) : ℚ) : ℝ)) := by
  rw [G33_30_formula]
  exact vasyuninBEntry_30_33_eval

def interval_33_30 : NamedVasyuninInterval :=
{
  h := 33
  k := 30
  lower := (32920309/896910000)
  upper := (33099691/896910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_30_interval
}

theorem G33_31_formula : baezDuarteGramEntry 33 31 = vasyuninBEntry 31 33 := by
  rw [baezDuarteGramEntry_symm 33 31]
  exact G31_33_formula

theorem G33_31_interval :
    ((((32092833/871670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 31) ∧
    (baezDuarteGramEntry 33 31 ≤ (((32267167/871670000) : ℚ) : ℝ)) := by
  rw [G33_31_formula]
  exact vasyuninBEntry_31_33_eval

def interval_33_31 : NamedVasyuninInterval :=
{
  h := 33
  k := 31
  lower := (32092833/871670000)
  upper := (32267167/871670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_31_interval
}

theorem G33_32_formula : baezDuarteGramEntry 33 32 = vasyuninBEntry 32 33 := by
  rw [baezDuarteGramEntry_symm 33 32]
  exact G32_33_formula

theorem G33_32_interval :
    ((((2568089/69110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 32) ∧
    (baezDuarteGramEntry 33 32 ≤ (((2581911/69110000) : ℚ) : ℝ)) := by
  rw [G33_32_formula]
  exact vasyuninBEntry_32_33_eval

def interval_33_32 : NamedVasyuninInterval :=
{
  h := 33
  k := 32
  lower := (2568089/69110000)
  upper := (2581911/69110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_32_interval
}

theorem G33_33_formula_eq : baezDuarteGramEntry 33 33 = (1 / (33 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 33 := by norm_num
  rw [baez_duarte_diagonal_scaling 33 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G33_33_log_gamma_interval :
  ((((26580239/697610000) : ℚ) : ℝ) ≤ (1 / (33 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (33 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((26719761/697610000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 33 (by norm_num)
  constructor
  · have : ((((26580239/697610000) : ℚ) : ℝ) ≤ (1 / (33 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (33 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((26719761/697610000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G33_33_interval : ((((26580239/697610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 33) ∧ (baezDuarteGramEntry 33 33 ≤ (((26719761/697610000) : ℚ) : ℝ)) := by
  rw [G33_33_formula_eq]
  exact G33_33_log_gamma_interval

def interval_33_33 : NamedVasyuninInterval :=
{
  h := 33
  k := 33
  lower := (26580239/697610000)
  upper := (26719761/697610000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G33_33_interval
}

theorem G33_34_formula : baezDuarteGramEntry 33 34 = vasyuninBEntry 33 34 := vasyuninBEntry_correct_axiom 33 34

theorem vasyuninBEntry_33_34_eval :
    ((((20303723/562770000) : ℚ) : ℝ) ≤ vasyuninBEntry 33 34) ∧
    (vasyuninBEntry 33 34 ≤ (((20416277/562770000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3334_formula_bound
  constructor <;> linarith

theorem G33_34_interval :
    ((((20303723/562770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 34) ∧
    (baezDuarteGramEntry 33 34 ≤ (((20416277/562770000) : ℚ) : ℝ)) := by
  rw [G33_34_formula]
  exact vasyuninBEntry_33_34_eval

def interval_33_34 : NamedVasyuninInterval :=
{
  h := 33
  k := 34
  lower := (20303723/562770000)
  upper := (20416277/562770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_34_interval
}

theorem G33_35_formula : baezDuarteGramEntry 33 35 = vasyuninBEntry 33 35 := vasyuninBEntry_correct_axiom 33 35

theorem vasyuninBEntry_33_35_eval :
    ((((27012227/777730000) : ℚ) : ℝ) ≤ vasyuninBEntry 33 35) ∧
    (vasyuninBEntry 33 35 ≤ (((27167773/777730000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3335_formula_bound
  constructor <;> linarith

theorem G33_35_interval :
    ((((27012227/777730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 35) ∧
    (baezDuarteGramEntry 33 35 ≤ (((27167773/777730000) : ℚ) : ℝ)) := by
  rw [G33_35_formula]
  exact vasyuninBEntry_33_35_eval

def interval_33_35 : NamedVasyuninInterval :=
{
  h := 33
  k := 35
  lower := (27012227/777730000)
  upper := (27167773/777730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_35_interval
}

theorem G33_36_formula : baezDuarteGramEntry 33 36 = vasyuninBEntry 33 36 := vasyuninBEntry_correct_axiom 33 36

theorem vasyuninBEntry_33_36_eval :
    ((((30708737/912630000) : ℚ) : ℝ) ≤ vasyuninBEntry 33 36) ∧
    (vasyuninBEntry 33 36 ≤ (((30891263/912630000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_12_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 12 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G33_36_interval :
    ((((30708737/912630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 36) ∧
    (baezDuarteGramEntry 33 36 ≤ (((30891263/912630000) : ℚ) : ℝ)) := by
  rw [G33_36_formula]
  exact vasyuninBEntry_33_36_eval

def interval_33_36 : NamedVasyuninInterval :=
{
  h := 33
  k := 36
  lower := (30708737/912630000)
  upper := (30891263/912630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_36_interval
}

theorem G33_37_formula : baezDuarteGramEntry 33 37 = vasyuninBEntry 33 37 := vasyuninBEntry_correct_axiom 33 37

theorem vasyuninBEntry_33_37_eval :
    ((((12481857/381430000) : ℚ) : ℝ) ≤ vasyuninBEntry 33 37) ∧
    (vasyuninBEntry 33 37 ≤ (((12558143/381430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3337_formula_bound
  constructor <;> linarith

theorem G33_37_interval :
    ((((12481857/381430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 37) ∧
    (baezDuarteGramEntry 33 37 ≤ (((12558143/381430000) : ℚ) : ℝ)) := by
  rw [G33_37_formula]
  exact vasyuninBEntry_33_37_eval

def interval_33_37 : NamedVasyuninInterval :=
{
  h := 33
  k := 37
  lower := (12481857/381430000)
  upper := (12558143/381430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_37_interval
}

theorem G33_38_formula : baezDuarteGramEntry 33 38 = vasyuninBEntry 33 38 := vasyuninBEntry_correct_axiom 33 38

theorem vasyuninBEntry_33_38_eval :
    ((((4667377/146230000) : ℚ) : ℝ) ≤ vasyuninBEntry 33 38) ∧
    (vasyuninBEntry 33 38 ≤ (((4696623/146230000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3338_formula_bound
  constructor <;> linarith

theorem G33_38_interval :
    ((((4667377/146230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 38) ∧
    (baezDuarteGramEntry 33 38 ≤ (((4696623/146230000) : ℚ) : ℝ)) := by
  rw [G33_38_formula]
  exact vasyuninBEntry_33_38_eval

def interval_33_38 : NamedVasyuninInterval :=
{
  h := 33
  k := 38
  lower := (4667377/146230000)
  upper := (4696623/146230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_38_interval
}

theorem G33_39_formula : baezDuarteGramEntry 33 39 = vasyuninBEntry 33 39 := vasyuninBEntry_correct_axiom 33 39

theorem vasyuninBEntry_33_39_eval :
    ((((27282571/874290000) : ℚ) : ℝ) ≤ vasyuninBEntry 33 39) ∧
    (vasyuninBEntry 33 39 ≤ (((27457429/874290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 13 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G33_39_interval :
    ((((27282571/874290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 39) ∧
    (baezDuarteGramEntry 33 39 ≤ (((27457429/874290000) : ℚ) : ℝ)) := by
  rw [G33_39_formula]
  exact vasyuninBEntry_33_39_eval

def interval_33_39 : NamedVasyuninInterval :=
{
  h := 33
  k := 39
  lower := (27282571/874290000)
  upper := (27457429/874290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_39_interval
}

theorem G33_40_formula : baezDuarteGramEntry 33 40 = vasyuninBEntry 33 40 := vasyuninBEntry_correct_axiom 33 40

theorem vasyuninBEntry_33_40_eval :
    ((((11178421/365790000) : ℚ) : ℝ) ≤ vasyuninBEntry 33 40) ∧
    (vasyuninBEntry 33 40 ≤ (((11251579/365790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3340_formula_bound
  constructor <;> linarith

theorem G33_40_interval :
    ((((11178421/365790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 40) ∧
    (baezDuarteGramEntry 33 40 ≤ (((11251579/365790000) : ℚ) : ℝ)) := by
  rw [G33_40_formula]
  exact vasyuninBEntry_33_40_eval

def interval_33_40 : NamedVasyuninInterval :=
{
  h := 33
  k := 40
  lower := (11178421/365790000)
  upper := (11251579/365790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_40_interval
}

theorem G33_41_formula : baezDuarteGramEntry 33 41 = vasyuninBEntry 33 41 := vasyuninBEntry_correct_axiom 33 41

theorem vasyuninBEntry_33_41_eval :
    ((((12892011/429890000) : ℚ) : ℝ) ≤ vasyuninBEntry 33 41) ∧
    (vasyuninBEntry 33 41 ≤ (((12977989/429890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3341_formula_bound
  constructor <;> linarith

theorem G33_41_interval :
    ((((12892011/429890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 41) ∧
    (baezDuarteGramEntry 33 41 ≤ (((12977989/429890000) : ℚ) : ℝ)) := by
  rw [G33_41_formula]
  exact vasyuninBEntry_33_41_eval

def interval_33_41 : NamedVasyuninInterval :=
{
  h := 33
  k := 41
  lower := (12892011/429890000)
  upper := (12977989/429890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_41_interval
}

theorem G33_42_formula : baezDuarteGramEntry 33 42 = vasyuninBEntry 33 42 := vasyuninBEntry_correct_axiom 33 42

theorem vasyuninBEntry_33_42_eval :
    ((((17331121/588790000) : ℚ) : ℝ) ≤ vasyuninBEntry 33 42) ∧
    (vasyuninBEntry 33 42 ≤ (((17448879/588790000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_14_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 14 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G33_42_interval :
    ((((17331121/588790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 42) ∧
    (baezDuarteGramEntry 33 42 ≤ (((17448879/588790000) : ℚ) : ℝ)) := by
  rw [G33_42_formula]
  exact vasyuninBEntry_33_42_eval

def interval_33_42 : NamedVasyuninInterval :=
{
  h := 33
  k := 42
  lower := (17331121/588790000)
  upper := (17448879/588790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_42_interval
}

theorem G33_43_formula : baezDuarteGramEntry 33 43 = vasyuninBEntry 33 43 := vasyuninBEntry_correct_axiom 33 43

theorem vasyuninBEntry_33_43_eval :
    ((((839599/29010000) : ℚ) : ℝ) ≤ vasyuninBEntry 33 43) ∧
    (vasyuninBEntry 33 43 ≤ (((845401/29010000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3343_formula_bound
  constructor <;> linarith

theorem G33_43_interval :
    ((((839599/29010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 43) ∧
    (baezDuarteGramEntry 33 43 ≤ (((845401/29010000) : ℚ) : ℝ)) := by
  rw [G33_43_formula]
  exact vasyuninBEntry_33_43_eval

def interval_33_43 : NamedVasyuninInterval :=
{
  h := 33
  k := 43
  lower := (839599/29010000)
  upper := (845401/29010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_43_interval
}

theorem G33_44_formula : baezDuarteGramEntry 33 44 = vasyuninBEntry 33 44 := vasyuninBEntry_correct_axiom 33 44

theorem vasyuninBEntry_33_44_eval :
    ((((12595923/440770000) : ℚ) : ℝ) ≤ vasyuninBEntry 33 44) ∧
    (vasyuninBEntry 33 44 ≤ (((12684077/440770000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 4 11 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 11)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 11)
  constructor <;> linarith

theorem G33_44_interval :
    ((((12595923/440770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 44) ∧
    (baezDuarteGramEntry 33 44 ≤ (((12684077/440770000) : ℚ) : ℝ)) := by
  rw [G33_44_formula]
  exact vasyuninBEntry_33_44_eval

def interval_33_44 : NamedVasyuninInterval :=
{
  h := 33
  k := 44
  lower := (12595923/440770000)
  upper := (12684077/440770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_44_interval
}

theorem G33_45_formula : baezDuarteGramEntry 33 45 = vasyuninBEntry 33 45 := vasyuninBEntry_correct_axiom 33 45

theorem vasyuninBEntry_33_45_eval :
    ((((64987/2317500) : ℚ) : ℝ) ≤ vasyuninBEntry 33 45) ∧
    (vasyuninBEntry 33 45 ≤ (((130901/4635000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_15_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 15 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G33_45_interval :
    ((((64987/2317500) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 45) ∧
    (baezDuarteGramEntry 33 45 ≤ (((130901/4635000) : ℚ) : ℝ)) := by
  rw [G33_45_formula]
  exact vasyuninBEntry_33_45_eval

def interval_33_45 : NamedVasyuninInterval :=
{
  h := 33
  k := 45
  lower := (64987/2317500)
  upper := (130901/4635000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_45_interval
}

theorem G33_46_formula : baezDuarteGramEntry 33 46 = vasyuninBEntry 33 46 := vasyuninBEntry_correct_axiom 33 46

theorem vasyuninBEntry_33_46_eval :
    ((((215221/7790000) : ℚ) : ℝ) ≤ vasyuninBEntry 33 46) ∧
    (vasyuninBEntry 33 46 ≤ (((216779/7790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3346_formula_bound
  constructor <;> linarith

theorem G33_46_interval :
    ((((215221/7790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 46) ∧
    (baezDuarteGramEntry 33 46 ≤ (((216779/7790000) : ℚ) : ℝ)) := by
  rw [G33_46_formula]
  exact vasyuninBEntry_33_46_eval

def interval_33_46 : NamedVasyuninInterval :=
{
  h := 33
  k := 46
  lower := (215221/7790000)
  upper := (216779/7790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_46_interval
}

theorem G33_47_formula : baezDuarteGramEntry 33 47 = vasyuninBEntry 33 47 := vasyuninBEntry_correct_axiom 33 47

theorem vasyuninBEntry_33_47_eval :
    ((((1342573/49270000) : ℚ) : ℝ) ≤ vasyuninBEntry 33 47) ∧
    (vasyuninBEntry 33 47 ≤ (((1352427/49270000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3347_formula_bound
  constructor <;> linarith

theorem G33_47_interval :
    ((((1342573/49270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 47) ∧
    (baezDuarteGramEntry 33 47 ≤ (((1352427/49270000) : ℚ) : ℝ)) := by
  rw [G33_47_formula]
  exact vasyuninBEntry_33_47_eval

def interval_33_47 : NamedVasyuninInterval :=
{
  h := 33
  k := 47
  lower := (1342573/49270000)
  upper := (1352427/49270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_47_interval
}

theorem G33_48_formula : baezDuarteGramEntry 33 48 = vasyuninBEntry 33 48 := vasyuninBEntry_correct_axiom 33 48

theorem vasyuninBEntry_33_48_eval :
    ((((21500143/798570000) : ℚ) : ℝ) ≤ vasyuninBEntry 33 48) ∧
    (vasyuninBEntry 33 48 ≤ (((21659857/798570000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_16_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 16 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G33_48_interval :
    ((((21500143/798570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 48) ∧
    (baezDuarteGramEntry 33 48 ≤ (((21659857/798570000) : ℚ) : ℝ)) := by
  rw [G33_48_formula]
  exact vasyuninBEntry_33_48_eval

def interval_33_48 : NamedVasyuninInterval :=
{
  h := 33
  k := 48
  lower := (21500143/798570000)
  upper := (21659857/798570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_48_interval
}

theorem G33_49_formula : baezDuarteGramEntry 33 49 = vasyuninBEntry 33 49 := vasyuninBEntry_correct_axiom 33 49

theorem vasyuninBEntry_33_49_eval :
    ((((1718557/64430000) : ℚ) : ℝ) ≤ vasyuninBEntry 33 49) ∧
    (vasyuninBEntry 33 49 ≤ (((1731443/64430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3349_formula_bound
  constructor <;> linarith

theorem G33_49_interval :
    ((((1718557/64430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 49) ∧
    (baezDuarteGramEntry 33 49 ≤ (((1731443/64430000) : ℚ) : ℝ)) := by
  rw [G33_49_formula]
  exact vasyuninBEntry_33_49_eval

def interval_33_49 : NamedVasyuninInterval :=
{
  h := 33
  k := 49
  lower := (1718557/64430000)
  upper := (1731443/64430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_49_interval
}

theorem G33_50_formula : baezDuarteGramEntry 33 50 = vasyuninBEntry 33 50 := vasyuninBEntry_correct_axiom 33 50

theorem vasyuninBEntry_33_50_eval :
    ((((637579/24210000) : ℚ) : ℝ) ≤ vasyuninBEntry 33 50) ∧
    (vasyuninBEntry 33 50 ≤ (((642421/24210000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3350_formula_bound
  constructor <;> linarith

theorem G33_50_interval :
    ((((637579/24210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 33 50) ∧
    (baezDuarteGramEntry 33 50 ≤ (((642421/24210000) : ℚ) : ℝ)) := by
  rw [G33_50_formula]
  exact vasyuninBEntry_33_50_eval

def interval_33_50 : NamedVasyuninInterval :=
{
  h := 33
  k := 50
  lower := (637579/24210000)
  upper := (642421/24210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G33_50_interval
}

theorem G34_1_formula : baezDuarteGramEntry 34 1 = vasyuninBEntry 1 34 := by
  rw [baezDuarteGramEntry_symm 34 1]
  exact G1_34_formula

theorem G34_1_interval :
    ((((12988741/152590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 1) ∧
    (baezDuarteGramEntry 34 1 ≤ (((13019259/152590000) : ℚ) : ℝ)) := by
  rw [G34_1_formula]
  exact vasyuninBEntry_1_34_eval

def interval_34_1 : NamedVasyuninInterval :=
{
  h := 34
  k := 1
  lower := (12988741/152590000)
  upper := (13019259/152590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_1_interval
}

theorem G34_2_formula : baezDuarteGramEntry 34 2 = vasyuninBEntry 2 34 := by
  rw [baezDuarteGramEntry_symm 34 2]
  exact G2_34_formula

theorem G34_2_interval :
    ((((3445409/45910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 2) ∧
    (baezDuarteGramEntry 34 2 ≤ (((3454591/45910000) : ℚ) : ℝ)) := by
  rw [G34_2_formula]
  exact vasyuninBEntry_2_34_eval

def interval_34_2 : NamedVasyuninInterval :=
{
  h := 34
  k := 2
  lower := (3445409/45910000)
  upper := (3454591/45910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_2_interval
}

theorem G34_3_formula : baezDuarteGramEntry 34 3 = vasyuninBEntry 3 34 := by
  rw [baezDuarteGramEntry_symm 34 3]
  exact G3_34_formula

theorem G34_3_interval :
    ((((62189587/904130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 3) ∧
    (baezDuarteGramEntry 34 3 ≤ (((62370413/904130000) : ℚ) : ℝ)) := by
  rw [G34_3_formula]
  exact vasyuninBEntry_3_34_eval

def interval_34_3 : NamedVasyuninInterval :=
{
  h := 34
  k := 3
  lower := (62189587/904130000)
  upper := (62370413/904130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_3_interval
}

theorem G34_4_formula : baezDuarteGramEntry 34 4 = vasyuninBEntry 4 34 := by
  rw [baezDuarteGramEntry_symm 34 4]
  exact G4_34_formula

theorem G34_4_interval :
    ((((17073553/264470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 4) ∧
    (baezDuarteGramEntry 34 4 ≤ (((17126447/264470000) : ℚ) : ℝ)) := by
  rw [G34_4_formula]
  exact vasyuninBEntry_4_34_eval

def interval_34_4 : NamedVasyuninInterval :=
{
  h := 34
  k := 4
  lower := (17073553/264470000)
  upper := (17126447/264470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_4_interval
}

theorem G34_5_formula : baezDuarteGramEntry 34 5 = vasyuninBEntry 5 34 := by
  rw [baezDuarteGramEntry_symm 34 5]
  exact G5_34_formula

theorem G34_5_interval :
    ((((52684049/859510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 5) ∧
    (baezDuarteGramEntry 34 5 ≤ (((52855951/859510000) : ℚ) : ℝ)) := by
  rw [G34_5_formula]
  exact vasyuninBEntry_5_34_eval

def interval_34_5 : NamedVasyuninInterval :=
{
  h := 34
  k := 5
  lower := (52684049/859510000)
  upper := (52855951/859510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_5_interval
}

theorem G34_6_formula : baezDuarteGramEntry 34 6 = vasyuninBEntry 6 34 := by
  rw [baezDuarteGramEntry_symm 34 6]
  exact G6_34_formula

theorem G34_6_interval :
    ((((55065891/941090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 6) ∧
    (baezDuarteGramEntry 34 6 ≤ (((55254109/941090000) : ℚ) : ℝ)) := by
  rw [G34_6_formula]
  exact vasyuninBEntry_6_34_eval

def interval_34_6 : NamedVasyuninInterval :=
{
  h := 34
  k := 6
  lower := (55065891/941090000)
  upper := (55254109/941090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_6_interval
}

theorem G34_7_formula : baezDuarteGramEntry 34 7 = vasyuninBEntry 7 34 := by
  rw [baezDuarteGramEntry_symm 34 7]
  exact G7_34_formula

theorem G34_7_interval :
    ((((11709253/207470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 7) ∧
    (baezDuarteGramEntry 34 7 ≤ (((11750747/207470000) : ℚ) : ℝ)) := by
  rw [G34_7_formula]
  exact vasyuninBEntry_7_34_eval

def interval_34_7 : NamedVasyuninInterval :=
{
  h := 34
  k := 7
  lower := (11709253/207470000)
  upper := (11750747/207470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_7_interval
}

theorem G34_8_formula : baezDuarteGramEntry 34 8 = vasyuninBEntry 8 34 := by
  rw [baezDuarteGramEntry_symm 34 8]
  exact G8_34_formula

theorem G34_8_interval :
    ((((40116161/738390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 8) ∧
    (baezDuarteGramEntry 34 8 ≤ (((40263839/738390000) : ℚ) : ℝ)) := by
  rw [G34_8_formula]
  exact vasyuninBEntry_8_34_eval

def interval_34_8 : NamedVasyuninInterval :=
{
  h := 34
  k := 8
  lower := (40116161/738390000)
  upper := (40263839/738390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_8_interval
}

theorem G34_9_formula : baezDuarteGramEntry 34 9 = vasyuninBEntry 9 34 := by
  rw [baezDuarteGramEntry_symm 34 9]
  exact G9_34_formula

theorem G34_9_interval :
    ((((6567503/124970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 9) ∧
    (baezDuarteGramEntry 34 9 ≤ (((6592497/124970000) : ℚ) : ℝ)) := by
  rw [G34_9_formula]
  exact vasyuninBEntry_9_34_eval

def interval_34_9 : NamedVasyuninInterval :=
{
  h := 34
  k := 9
  lower := (6567503/124970000)
  upper := (6592497/124970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_9_interval
}

theorem G34_10_formula : baezDuarteGramEntry 34 10 = vasyuninBEntry 10 34 := by
  rw [baezDuarteGramEntry_symm 34 10]
  exact G10_34_formula

theorem G34_10_interval :
    ((((21812113/428870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 10) ∧
    (baezDuarteGramEntry 34 10 ≤ (((21897887/428870000) : ℚ) : ℝ)) := by
  rw [G34_10_formula]
  exact vasyuninBEntry_10_34_eval

def interval_34_10 : NamedVasyuninInterval :=
{
  h := 34
  k := 10
  lower := (21812113/428870000)
  upper := (21897887/428870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_10_interval
}

theorem G34_11_formula : baezDuarteGramEntry 34 11 = vasyuninBEntry 11 34 := by
  rw [baezDuarteGramEntry_symm 34 11]
  exact G11_34_formula

theorem G34_11_interval :
    ((((35030131/698690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 11) ∧
    (baezDuarteGramEntry 34 11 ≤ (((35169869/698690000) : ℚ) : ℝ)) := by
  rw [G34_11_formula]
  exact vasyuninBEntry_11_34_eval

def interval_34_11 : NamedVasyuninInterval :=
{
  h := 34
  k := 11
  lower := (35030131/698690000)
  upper := (35169869/698690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_11_interval
}

theorem G34_12_formula : baezDuarteGramEntry 34 12 = vasyuninBEntry 12 34 := by
  rw [baezDuarteGramEntry_symm 34 12]
  exact G12_34_formula

theorem G34_12_interval :
    ((((8864197/183030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 12) ∧
    (baezDuarteGramEntry 34 12 ≤ (((8900803/183030000) : ℚ) : ℝ)) := by
  rw [G34_12_formula]
  exact vasyuninBEntry_12_34_eval

def interval_34_12 : NamedVasyuninInterval :=
{
  h := 34
  k := 12
  lower := (8864197/183030000)
  upper := (8900803/183030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_12_interval
}

theorem G34_13_formula : baezDuarteGramEntry 34 13 = vasyuninBEntry 13 34 := by
  rw [baezDuarteGramEntry_symm 34 13]
  exact G13_34_formula

theorem G34_13_interval :
    ((((2316307/49430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 13) ∧
    (baezDuarteGramEntry 34 13 ≤ (((2326193/49430000) : ℚ) : ℝ)) := by
  rw [G34_13_formula]
  exact vasyuninBEntry_13_34_eval

def interval_34_13 : NamedVasyuninInterval :=
{
  h := 34
  k := 13
  lower := (2316307/49430000)
  upper := (2326193/49430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_13_interval
}

theorem G34_14_formula : baezDuarteGramEntry 34 14 = vasyuninBEntry 14 34 := by
  rw [baezDuarteGramEntry_symm 34 14]
  exact G14_34_formula

theorem G34_14_interval :
    ((((5927057/129430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 14) ∧
    (baezDuarteGramEntry 34 14 ≤ (((5952943/129430000) : ℚ) : ℝ)) := by
  rw [G34_14_formula]
  exact vasyuninBEntry_14_34_eval

def interval_34_14 : NamedVasyuninInterval :=
{
  h := 34
  k := 14
  lower := (5927057/129430000)
  upper := (5952943/129430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_14_interval
}

theorem G34_15_formula : baezDuarteGramEntry 34 15 = vasyuninBEntry 15 34 := by
  rw [baezDuarteGramEntry_symm 34 15]
  exact G15_34_formula

theorem G34_15_interval :
    ((((67001/1490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 15) ∧
    (baezDuarteGramEntry 34 15 ≤ (((67299/1490000) : ℚ) : ℝ)) := by
  rw [G34_15_formula]
  exact vasyuninBEntry_15_34_eval

def interval_34_15 : NamedVasyuninInterval :=
{
  h := 34
  k := 15
  lower := (67001/1490000)
  upper := (67299/1490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_15_interval
}

theorem G34_16_formula : baezDuarteGramEntry 34 16 = vasyuninBEntry 16 34 := by
  rw [baezDuarteGramEntry_symm 34 16]
  exact G16_34_formula

theorem G34_16_interval :
    ((((5283151/118490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 16) ∧
    (baezDuarteGramEntry 34 16 ≤ (((5306849/118490000) : ℚ) : ℝ)) := by
  rw [G34_16_formula]
  exact vasyuninBEntry_16_34_eval

def interval_34_16 : NamedVasyuninInterval :=
{
  h := 34
  k := 16
  lower := (5283151/118490000)
  upper := (5306849/118490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_16_interval
}

theorem G34_17_formula : baezDuarteGramEntry 34 17 = vasyuninBEntry 17 34 := by
  rw [baezDuarteGramEntry_symm 34 17]
  exact G17_34_formula

theorem G34_17_interval :
    ((((4563681/100690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 17) ∧
    (baezDuarteGramEntry 34 17 ≤ (((4583819/100690000) : ℚ) : ℝ)) := by
  rw [G34_17_formula]
  exact vasyuninBEntry_17_34_eval

def interval_34_17 : NamedVasyuninInterval :=
{
  h := 34
  k := 17
  lower := (4563681/100690000)
  upper := (4583819/100690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_17_interval
}

theorem G34_18_formula : baezDuarteGramEntry 34 18 = vasyuninBEntry 18 34 := by
  rw [baezDuarteGramEntry_symm 34 18]
  exact G18_34_formula

theorem G34_18_interval :
    ((((12949723/302770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 18) ∧
    (baezDuarteGramEntry 34 18 ≤ (((13010277/302770000) : ℚ) : ℝ)) := by
  rw [G34_18_formula]
  exact vasyuninBEntry_18_34_eval

def interval_34_18 : NamedVasyuninInterval :=
{
  h := 34
  k := 18
  lower := (12949723/302770000)
  upper := (13010277/302770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_18_interval
}

theorem G34_19_formula : baezDuarteGramEntry 34 19 = vasyuninBEntry 19 34 := by
  rw [baezDuarteGramEntry_symm 34 19]
  exact G19_34_formula

theorem G34_19_interval :
    ((((468867/11330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 19) ∧
    (baezDuarteGramEntry 34 19 ≤ (((471133/11330000) : ℚ) : ℝ)) := by
  rw [G34_19_formula]
  exact vasyuninBEntry_19_34_eval

def interval_34_19 : NamedVasyuninInterval :=
{
  h := 34
  k := 19
  lower := (468867/11330000)
  upper := (471133/11330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_19_interval
}

theorem G34_20_formula : baezDuarteGramEntry 34 20 = vasyuninBEntry 20 34 := by
  rw [baezDuarteGramEntry_symm 34 20]
  exact G20_34_formula

theorem G34_20_interval :
    ((((17965501/444990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 20) ∧
    (baezDuarteGramEntry 34 20 ≤ (((18054499/444990000) : ℚ) : ℝ)) := by
  rw [G34_20_formula]
  exact vasyuninBEntry_20_34_eval

def interval_34_20 : NamedVasyuninInterval :=
{
  h := 34
  k := 20
  lower := (17965501/444990000)
  upper := (18054499/444990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_20_interval
}

theorem G34_21_formula : baezDuarteGramEntry 34 21 = vasyuninBEntry 21 34 := by
  rw [baezDuarteGramEntry_symm 34 21]
  exact G21_34_formula

theorem G34_21_interval :
    ((((30363211/767890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 21) ∧
    (baezDuarteGramEntry 34 21 ≤ (((30516789/767890000) : ℚ) : ℝ)) := by
  rw [G34_21_formula]
  exact vasyuninBEntry_21_34_eval

def interval_34_21 : NamedVasyuninInterval :=
{
  h := 34
  k := 21
  lower := (30363211/767890000)
  upper := (30516789/767890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_21_interval
}

theorem G34_22_formula : baezDuarteGramEntry 34 22 = vasyuninBEntry 22 34 := by
  rw [baezDuarteGramEntry_symm 34 22]
  exact G22_34_formula

theorem G34_22_interval :
    ((((1791397/46030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 22) ∧
    (baezDuarteGramEntry 34 22 ≤ (((1800603/46030000) : ℚ) : ℝ)) := by
  rw [G34_22_formula]
  exact vasyuninBEntry_22_34_eval

def interval_34_22 : NamedVasyuninInterval :=
{
  h := 34
  k := 22
  lower := (1791397/46030000)
  upper := (1800603/46030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_22_interval
}

theorem G34_23_formula : baezDuarteGramEntry 34 23 = vasyuninBEntry 23 34 := by
  rw [baezDuarteGramEntry_symm 34 23]
  exact G23_34_formula

theorem G34_23_interval :
    ((((38350069/999310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 23) ∧
    (baezDuarteGramEntry 34 23 ≤ (((38549931/999310000) : ℚ) : ℝ)) := by
  rw [G34_23_formula]
  exact vasyuninBEntry_23_34_eval

def interval_34_23 : NamedVasyuninInterval :=
{
  h := 34
  k := 23
  lower := (38350069/999310000)
  upper := (38549931/999310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_23_interval
}

theorem G34_24_formula : baezDuarteGramEntry 34 24 = vasyuninBEntry 24 34 := by
  rw [baezDuarteGramEntry_symm 34 24]
  exact G24_34_formula

theorem G34_24_interval :
    ((((6335663/168370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 24) ∧
    (baezDuarteGramEntry 34 24 ≤ (((6369337/168370000) : ℚ) : ℝ)) := by
  rw [G34_24_formula]
  exact vasyuninBEntry_24_34_eval

def interval_34_24 : NamedVasyuninInterval :=
{
  h := 34
  k := 24
  lower := (6335663/168370000)
  upper := (6369337/168370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_24_interval
}

theorem G34_25_formula : baezDuarteGramEntry 34 25 = vasyuninBEntry 25 34 := by
  rw [baezDuarteGramEntry_symm 34 25]
  exact G25_34_formula

theorem G34_25_interval :
    ((((12007649/323510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 25) ∧
    (baezDuarteGramEntry 34 25 ≤ (((12072351/323510000) : ℚ) : ℝ)) := by
  rw [G34_25_formula]
  exact vasyuninBEntry_25_34_eval

def interval_34_25 : NamedVasyuninInterval :=
{
  h := 34
  k := 25
  lower := (12007649/323510000)
  upper := (12072351/323510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_25_interval
}

theorem G34_26_formula : baezDuarteGramEntry 34 26 = vasyuninBEntry 26 34 := by
  rw [baezDuarteGramEntry_symm 34 26]
  exact G26_34_formula

theorem G34_26_interval :
    ((((31304643/853570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 26) ∧
    (baezDuarteGramEntry 34 26 ≤ (((31475357/853570000) : ℚ) : ℝ)) := by
  rw [G34_26_formula]
  exact vasyuninBEntry_26_34_eval

def interval_34_26 : NamedVasyuninInterval :=
{
  h := 34
  k := 26
  lower := (31304643/853570000)
  upper := (31475357/853570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_26_interval
}

theorem G34_27_formula : baezDuarteGramEntry 34 27 = vasyuninBEntry 27 34 := by
  rw [baezDuarteGramEntry_symm 34 27]
  exact G27_34_formula

theorem G34_27_interval :
    ((((33308237/917630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 27) ∧
    (baezDuarteGramEntry 34 27 ≤ (((33491763/917630000) : ℚ) : ℝ)) := by
  rw [G34_27_formula]
  exact vasyuninBEntry_27_34_eval

def interval_34_27 : NamedVasyuninInterval :=
{
  h := 34
  k := 27
  lower := (33308237/917630000)
  upper := (33491763/917630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_27_interval
}

theorem G34_28_formula : baezDuarteGramEntry 34 28 = vasyuninBEntry 28 34 := by
  rw [baezDuarteGramEntry_symm 34 28]
  exact G28_34_formula

theorem G34_28_interval :
    ((((1914679/53210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 28) ∧
    (baezDuarteGramEntry 34 28 ≤ (((1925321/53210000) : ℚ) : ℝ)) := by
  rw [G34_28_formula]
  exact vasyuninBEntry_28_34_eval

def interval_34_28 : NamedVasyuninInterval :=
{
  h := 34
  k := 28
  lower := (1914679/53210000)
  upper := (1925321/53210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_28_interval
}

theorem G34_29_formula : baezDuarteGramEntry 34 29 = vasyuninBEntry 29 34 := by
  rw [baezDuarteGramEntry_symm 34 29]
  exact G29_34_formula

theorem G34_29_interval :
    ((((33945093/949070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 29) ∧
    (baezDuarteGramEntry 34 29 ≤ (((34134907/949070000) : ℚ) : ℝ)) := by
  rw [G34_29_formula]
  exact vasyuninBEntry_29_34_eval

def interval_34_29 : NamedVasyuninInterval :=
{
  h := 34
  k := 29
  lower := (33945093/949070000)
  upper := (34134907/949070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_29_interval
}

theorem G34_30_formula : baezDuarteGramEntry 34 30 = vasyuninBEntry 30 34 := by
  rw [baezDuarteGramEntry_symm 34 30]
  exact G30_34_formula

theorem G34_30_interval :
    ((((27572633/773670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 30) ∧
    (baezDuarteGramEntry 34 30 ≤ (((27727367/773670000) : ℚ) : ℝ)) := by
  rw [G34_30_formula]
  exact vasyuninBEntry_30_34_eval

def interval_34_30 : NamedVasyuninInterval :=
{
  h := 34
  k := 30
  lower := (27572633/773670000)
  upper := (27727367/773670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_30_interval
}

theorem G34_31_formula : baezDuarteGramEntry 34 31 = vasyuninBEntry 31 34 := by
  rw [baezDuarteGramEntry_symm 34 31]
  exact G31_34_formula

theorem G34_31_interval :
    ((((24670741/692590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 31) ∧
    (baezDuarteGramEntry 34 31 ≤ (((24809259/692590000) : ℚ) : ℝ)) := by
  rw [G34_31_formula]
  exact vasyuninBEntry_31_34_eval

def interval_34_31 : NamedVasyuninInterval :=
{
  h := 34
  k := 31
  lower := (24670741/692590000)
  upper := (24809259/692590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_31_interval
}

theorem G34_32_formula : baezDuarteGramEntry 34 32 = vasyuninBEntry 32 34 := by
  rw [baezDuarteGramEntry_symm 34 32]
  exact G32_34_formula

theorem G34_32_interval :
    ((((18029561/504390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 32) ∧
    (baezDuarteGramEntry 34 32 ≤ (((18130439/504390000) : ℚ) : ℝ)) := by
  rw [G34_32_formula]
  exact vasyuninBEntry_32_34_eval

def interval_34_32 : NamedVasyuninInterval :=
{
  h := 34
  k := 32
  lower := (18029561/504390000)
  upper := (18130439/504390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_32_interval
}

theorem G34_33_formula : baezDuarteGramEntry 34 33 = vasyuninBEntry 33 34 := by
  rw [baezDuarteGramEntry_symm 34 33]
  exact G33_34_formula

theorem G34_33_interval :
    ((((20303723/562770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 33) ∧
    (baezDuarteGramEntry 34 33 ≤ (((20416277/562770000) : ℚ) : ℝ)) := by
  rw [G34_33_formula]
  exact vasyuninBEntry_33_34_eval

def interval_34_33 : NamedVasyuninInterval :=
{
  h := 34
  k := 33
  lower := (20303723/562770000)
  upper := (20416277/562770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_33_interval
}

theorem G34_34_formula_eq : baezDuarteGramEntry 34 34 = (1 / (34 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 34 := by norm_num
  rw [baez_duarte_diagonal_scaling 34 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G34_34_log_gamma_interval :
  ((((3321019/89810000) : ℚ) : ℝ) ≤ (1 / (34 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (34 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((3338981/89810000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 34 (by norm_num)
  constructor
  · have : ((((3321019/89810000) : ℚ) : ℝ) ≤ (1 / (34 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (34 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((3338981/89810000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G34_34_interval : ((((3321019/89810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 34) ∧ (baezDuarteGramEntry 34 34 ≤ (((3338981/89810000) : ℚ) : ℝ)) := by
  rw [G34_34_formula_eq]
  exact G34_34_log_gamma_interval

def interval_34_34 : NamedVasyuninInterval :=
{
  h := 34
  k := 34
  lower := (3321019/89810000)
  upper := (3338981/89810000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G34_34_interval
}

theorem G34_35_formula : baezDuarteGramEntry 34 35 = vasyuninBEntry 34 35 := vasyuninBEntry_correct_axiom 34 35

theorem vasyuninBEntry_34_35_eval :
    ((((2337333/66670000) : ℚ) : ℝ) ≤ vasyuninBEntry 34 35) ∧
    (vasyuninBEntry 34 35 ≤ (((2350667/66670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3435_formula_bound
  constructor <;> linarith

theorem G34_35_interval :
    ((((2337333/66670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 35) ∧
    (baezDuarteGramEntry 34 35 ≤ (((2350667/66670000) : ℚ) : ℝ)) := by
  rw [G34_35_formula]
  exact vasyuninBEntry_34_35_eval

def interval_34_35 : NamedVasyuninInterval :=
{
  h := 34
  k := 35
  lower := (2337333/66670000)
  upper := (2350667/66670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_35_interval
}

theorem G34_36_formula : baezDuarteGramEntry 34 36 = vasyuninBEntry 34 36 := vasyuninBEntry_correct_axiom 34 36

theorem vasyuninBEntry_34_36_eval :
    ((((16815217/497830000) : ℚ) : ℝ) ≤ vasyuninBEntry 34 36) ∧
    (vasyuninBEntry 34 36 ≤ (((16914783/497830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_17_18_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 17 18 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G34_36_interval :
    ((((16815217/497830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 36) ∧
    (baezDuarteGramEntry 34 36 ≤ (((16914783/497830000) : ℚ) : ℝ)) := by
  rw [G34_36_formula]
  exact vasyuninBEntry_34_36_eval

def interval_34_36 : NamedVasyuninInterval :=
{
  h := 34
  k := 36
  lower := (16815217/497830000)
  upper := (16914783/497830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_36_interval
}

theorem G34_37_formula : baezDuarteGramEntry 34 37 = vasyuninBEntry 34 37 := vasyuninBEntry_correct_axiom 34 37

theorem vasyuninBEntry_34_37_eval :
    ((((30606513/934870000) : ℚ) : ℝ) ≤ vasyuninBEntry 34 37) ∧
    (vasyuninBEntry 34 37 ≤ (((30793487/934870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3437_formula_bound
  constructor <;> linarith

theorem G34_37_interval :
    ((((30606513/934870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 37) ∧
    (baezDuarteGramEntry 34 37 ≤ (((30793487/934870000) : ℚ) : ℝ)) := by
  rw [G34_37_formula]
  exact vasyuninBEntry_34_37_eval

def interval_34_37 : NamedVasyuninInterval :=
{
  h := 34
  k := 37
  lower := (30606513/934870000)
  upper := (30793487/934870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_37_interval
}

theorem G34_38_formula : baezDuarteGramEntry 34 38 = vasyuninBEntry 34 38 := vasyuninBEntry_correct_axiom 34 38

theorem vasyuninBEntry_34_38_eval :
    ((((4621493/145070000) : ℚ) : ℝ) ≤ vasyuninBEntry 34 38) ∧
    (vasyuninBEntry 34 38 ≤ (((4650507/145070000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_17_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 17 19 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G34_38_interval :
    ((((4621493/145070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 38) ∧
    (baezDuarteGramEntry 34 38 ≤ (((4650507/145070000) : ℚ) : ℝ)) := by
  rw [G34_38_formula]
  exact vasyuninBEntry_34_38_eval

def interval_34_38 : NamedVasyuninInterval :=
{
  h := 34
  k := 38
  lower := (4621493/145070000)
  upper := (4650507/145070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_38_interval
}

theorem G34_39_formula : baezDuarteGramEntry 34 39 = vasyuninBEntry 34 39 := vasyuninBEntry_correct_axiom 34 39

theorem vasyuninBEntry_34_39_eval :
    ((((246831/7940000) : ℚ) : ℝ) ≤ vasyuninBEntry 34 39) ∧
    (vasyuninBEntry 34 39 ≤ (((248419/7940000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3439_formula_bound
  constructor <;> linarith

theorem G34_39_interval :
    ((((246831/7940000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 39) ∧
    (baezDuarteGramEntry 34 39 ≤ (((248419/7940000) : ℚ) : ℝ)) := by
  rw [G34_39_formula]
  exact vasyuninBEntry_34_39_eval

def interval_34_39 : NamedVasyuninInterval :=
{
  h := 34
  k := 39
  lower := (246831/7940000)
  upper := (248419/7940000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_39_interval
}

theorem G34_40_formula : baezDuarteGramEntry 34 40 = vasyuninBEntry 34 40 := vasyuninBEntry_correct_axiom 34 40

theorem vasyuninBEntry_34_40_eval :
    ((((21499279/707210000) : ℚ) : ℝ) ≤ vasyuninBEntry 34 40) ∧
    (vasyuninBEntry 34 40 ≤ (((21640721/707210000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_17_20_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 17 20 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G34_40_interval :
    ((((21499279/707210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 40) ∧
    (baezDuarteGramEntry 34 40 ≤ (((21640721/707210000) : ℚ) : ℝ)) := by
  rw [G34_40_formula]
  exact vasyuninBEntry_34_40_eval

def interval_34_40 : NamedVasyuninInterval :=
{
  h := 34
  k := 40
  lower := (21499279/707210000)
  upper := (21640721/707210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_40_interval
}

theorem G34_41_formula : baezDuarteGramEntry 34 41 = vasyuninBEntry 34 41 := vasyuninBEntry_correct_axiom 34 41

theorem vasyuninBEntry_34_41_eval :
    ((((1209689/40610000) : ℚ) : ℝ) ≤ vasyuninBEntry 34 41) ∧
    (vasyuninBEntry 34 41 ≤ (((1217811/40610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3441_formula_bound
  constructor <;> linarith

theorem G34_41_interval :
    ((((1209689/40610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 41) ∧
    (baezDuarteGramEntry 34 41 ≤ (((1217811/40610000) : ℚ) : ℝ)) := by
  rw [G34_41_formula]
  exact vasyuninBEntry_34_41_eval

def interval_34_41 : NamedVasyuninInterval :=
{
  h := 34
  k := 41
  lower := (1209689/40610000)
  upper := (1217811/40610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_41_interval
}

theorem G34_42_formula : baezDuarteGramEntry 34 42 = vasyuninBEntry 34 42 := vasyuninBEntry_correct_axiom 34 42

theorem vasyuninBEntry_34_42_eval :
    ((((17370559/594410000) : ℚ) : ℝ) ≤ vasyuninBEntry 34 42) ∧
    (vasyuninBEntry 34 42 ≤ (((17489441/594410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_17_21_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 17 21 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G34_42_interval :
    ((((17370559/594410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 42) ∧
    (baezDuarteGramEntry 34 42 ≤ (((17489441/594410000) : ℚ) : ℝ)) := by
  rw [G34_42_formula]
  exact vasyuninBEntry_34_42_eval

def interval_34_42 : NamedVasyuninInterval :=
{
  h := 34
  k := 42
  lower := (17370559/594410000)
  upper := (17489441/594410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_42_interval
}

theorem G34_43_formula : baezDuarteGramEntry 34 43 = vasyuninBEntry 34 43 := vasyuninBEntry_correct_axiom 34 43

theorem vasyuninBEntry_34_43_eval :
    ((((11898547/414530000) : ℚ) : ℝ) ≤ vasyuninBEntry 34 43) ∧
    (vasyuninBEntry 34 43 ≤ (((11981453/414530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3443_formula_bound
  constructor <;> linarith

theorem G34_43_interval :
    ((((11898547/414530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 43) ∧
    (baezDuarteGramEntry 34 43 ≤ (((11981453/414530000) : ℚ) : ℝ)) := by
  rw [G34_43_formula]
  exact vasyuninBEntry_34_43_eval

def interval_34_43 : NamedVasyuninInterval :=
{
  h := 34
  k := 43
  lower := (11898547/414530000)
  upper := (11981453/414530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_43_interval
}

theorem G34_44_formula : baezDuarteGramEntry 34 44 = vasyuninBEntry 34 44 := vasyuninBEntry_correct_axiom 34 44

theorem vasyuninBEntry_34_44_eval :
    ((((346273/12270000) : ℚ) : ℝ) ≤ vasyuninBEntry 34 44) ∧
    (vasyuninBEntry 34 44 ≤ (((348727/12270000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_17_22_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 17 22 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G34_44_interval :
    ((((346273/12270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 44) ∧
    (baezDuarteGramEntry 34 44 ≤ (((348727/12270000) : ℚ) : ℝ)) := by
  rw [G34_44_formula]
  exact vasyuninBEntry_34_44_eval

def interval_34_44 : NamedVasyuninInterval :=
{
  h := 34
  k := 44
  lower := (346273/12270000)
  upper := (348727/12270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_44_interval
}

theorem G34_45_formula : baezDuarteGramEntry 34 45 = vasyuninBEntry 34 45 := vasyuninBEntry_correct_axiom 34 45

theorem vasyuninBEntry_34_45_eval :
    ((((305153/10970000) : ℚ) : ℝ) ≤ vasyuninBEntry 34 45) ∧
    (vasyuninBEntry 34 45 ≤ (((307347/10970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3445_formula_bound
  constructor <;> linarith

theorem G34_45_interval :
    ((((305153/10970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 45) ∧
    (baezDuarteGramEntry 34 45 ≤ (((307347/10970000) : ℚ) : ℝ)) := by
  rw [G34_45_formula]
  exact vasyuninBEntry_34_45_eval

def interval_34_45 : NamedVasyuninInterval :=
{
  h := 34
  k := 45
  lower := (305153/10970000)
  upper := (307347/10970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_45_interval
}

theorem G34_46_formula : baezDuarteGramEntry 34 46 = vasyuninBEntry 34 46 := vasyuninBEntry_correct_axiom 34 46

theorem vasyuninBEntry_34_46_eval :
    ((((928483/33920000) : ℚ) : ℝ) ≤ vasyuninBEntry 34 46) ∧
    (vasyuninBEntry 34 46 ≤ (((935267/33920000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_17_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 17 23 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G34_46_interval :
    ((((928483/33920000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 46) ∧
    (baezDuarteGramEntry 34 46 ≤ (((935267/33920000) : ℚ) : ℝ)) := by
  rw [G34_46_formula]
  exact vasyuninBEntry_34_46_eval

def interval_34_46 : NamedVasyuninInterval :=
{
  h := 34
  k := 46
  lower := (928483/33920000)
  upper := (935267/33920000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_46_interval
}

theorem G34_47_formula : baezDuarteGramEntry 34 47 = vasyuninBEntry 34 47 := vasyuninBEntry_correct_axiom 34 47

theorem vasyuninBEntry_34_47_eval :
    ((((23990999/890010000) : ℚ) : ℝ) ≤ vasyuninBEntry 34 47) ∧
    (vasyuninBEntry 34 47 ≤ (((24169001/890010000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3447_formula_bound
  constructor <;> linarith

theorem G34_47_interval :
    ((((23990999/890010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 47) ∧
    (baezDuarteGramEntry 34 47 ≤ (((24169001/890010000) : ℚ) : ℝ)) := by
  rw [G34_47_formula]
  exact vasyuninBEntry_34_47_eval

def interval_34_47 : NamedVasyuninInterval :=
{
  h := 34
  k := 47
  lower := (23990999/890010000)
  upper := (24169001/890010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_47_interval
}

theorem G34_48_formula : baezDuarteGramEntry 34 48 = vasyuninBEntry 34 48 := vasyuninBEntry_correct_axiom 34 48

theorem vasyuninBEntry_34_48_eval :
    ((((6107033/229670000) : ℚ) : ℝ) ≤ vasyuninBEntry 34 48) ∧
    (vasyuninBEntry 34 48 ≤ (((6152967/229670000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_17_24_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 17 24 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G34_48_interval :
    ((((6107033/229670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 48) ∧
    (baezDuarteGramEntry 34 48 ≤ (((6152967/229670000) : ℚ) : ℝ)) := by
  rw [G34_48_formula]
  exact vasyuninBEntry_34_48_eval

def interval_34_48 : NamedVasyuninInterval :=
{
  h := 34
  k := 48
  lower := (6107033/229670000)
  upper := (6152967/229670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_48_interval
}

theorem G34_49_formula : baezDuarteGramEntry 34 49 = vasyuninBEntry 34 49 := vasyuninBEntry_correct_axiom 34 49

theorem vasyuninBEntry_34_49_eval :
    ((((21378589/814110000) : ℚ) : ℝ) ≤ vasyuninBEntry 34 49) ∧
    (vasyuninBEntry 34 49 ≤ (((21541411/814110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3449_formula_bound
  constructor <;> linarith

theorem G34_49_interval :
    ((((21378589/814110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 49) ∧
    (baezDuarteGramEntry 34 49 ≤ (((21541411/814110000) : ℚ) : ℝ)) := by
  rw [G34_49_formula]
  exact vasyuninBEntry_34_49_eval

def interval_34_49 : NamedVasyuninInterval :=
{
  h := 34
  k := 49
  lower := (21378589/814110000)
  upper := (21541411/814110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_49_interval
}

theorem G34_50_formula : baezDuarteGramEntry 34 50 = vasyuninBEntry 34 50 := vasyuninBEntry_correct_axiom 34 50

theorem vasyuninBEntry_34_50_eval :
    ((((23798419/915810000) : ℚ) : ℝ) ≤ vasyuninBEntry 34 50) ∧
    (vasyuninBEntry 34 50 ≤ (((23981581/915810000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_17_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 17 25 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G34_50_interval :
    ((((23798419/915810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 34 50) ∧
    (baezDuarteGramEntry 34 50 ≤ (((23981581/915810000) : ℚ) : ℝ)) := by
  rw [G34_50_formula]
  exact vasyuninBEntry_34_50_eval

def interval_34_50 : NamedVasyuninInterval :=
{
  h := 34
  k := 50
  lower := (23798419/915810000)
  upper := (23981581/915810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G34_50_interval
}

theorem G35_1_formula : baezDuarteGramEntry 35 1 = vasyuninBEntry 1 35 := by
  rw [baezDuarteGramEntry_symm 35 1]
  exact G1_35_formula

theorem G35_1_interval :
    ((((7660781/92190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 1) ∧
    (baezDuarteGramEntry 35 1 ≤ (((7679219/92190000) : ℚ) : ℝ)) := by
  rw [G35_1_formula]
  exact vasyuninBEntry_1_35_eval

def interval_35_1 : NamedVasyuninInterval :=
{
  h := 35
  k := 1
  lower := (7660781/92190000)
  upper := (7679219/92190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_1_interval
}

theorem G35_2_formula : baezDuarteGramEntry 35 2 = vasyuninBEntry 2 35 := by
  rw [baezDuarteGramEntry_symm 35 2]
  exact G2_35_formula

theorem G35_2_interval :
    ((((57311551/784490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 2) ∧
    (baezDuarteGramEntry 35 2 ≤ (((57468449/784490000) : ℚ) : ℝ)) := by
  rw [G35_2_formula]
  exact vasyuninBEntry_2_35_eval

def interval_35_2 : NamedVasyuninInterval :=
{
  h := 35
  k := 2
  lower := (57311551/784490000)
  upper := (57468449/784490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_2_interval
}

theorem G35_3_formula : baezDuarteGramEntry 35 3 = vasyuninBEntry 3 35 := by
  rw [baezDuarteGramEntry_symm 35 3]
  exact G3_35_formula

theorem G35_3_interval :
    ((((52531859/781410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 3) ∧
    (baezDuarteGramEntry 35 3 ≤ (((52688141/781410000) : ℚ) : ℝ)) := by
  rw [G35_3_formula]
  exact vasyuninBEntry_3_35_eval

def interval_35_3 : NamedVasyuninInterval :=
{
  h := 35
  k := 3
  lower := (52531859/781410000)
  upper := (52688141/781410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_3_interval
}

theorem G35_4_formula : baezDuarteGramEntry 35 4 = vasyuninBEntry 4 35 := by
  rw [baezDuarteGramEntry_symm 35 4]
  exact G4_35_formula

theorem G35_4_interval :
    ((((2750143/43570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 4) ∧
    (baezDuarteGramEntry 35 4 ≤ (((2758857/43570000) : ℚ) : ℝ)) := by
  rw [G35_4_formula]
  exact vasyuninBEntry_4_35_eval

def interval_35_4 : NamedVasyuninInterval :=
{
  h := 35
  k := 4
  lower := (2750143/43570000)
  upper := (2758857/43570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_4_interval
}

theorem G35_5_formula : baezDuarteGramEntry 35 5 = vasyuninBEntry 5 35 := by
  rw [baezDuarteGramEntry_symm 35 5]
  exact G5_35_formula

theorem G35_5_interval :
    ((((2560771/42290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 5) ∧
    (baezDuarteGramEntry 35 5 ≤ (((2569229/42290000) : ℚ) : ℝ)) := by
  rw [G35_5_formula]
  exact vasyuninBEntry_5_35_eval

def interval_35_5 : NamedVasyuninInterval :=
{
  h := 35
  k := 5
  lower := (2560771/42290000)
  upper := (2569229/42290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_5_interval
}

theorem G35_6_formula : baezDuarteGramEntry 35 6 = vasyuninBEntry 6 35 := by
  rw [baezDuarteGramEntry_symm 35 6]
  exact G6_35_formula

theorem G35_6_interval :
    ((((2254871/39290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 6) ∧
    (baezDuarteGramEntry 35 6 ≤ (((2262729/39290000) : ℚ) : ℝ)) := by
  rw [G35_6_formula]
  exact vasyuninBEntry_6_35_eval

def interval_35_6 : NamedVasyuninInterval :=
{
  h := 35
  k := 6
  lower := (2254871/39290000)
  upper := (2262729/39290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_6_interval
}

theorem G35_7_formula : baezDuarteGramEntry 35 7 = vasyuninBEntry 7 35 := by
  rw [baezDuarteGramEntry_symm 35 7]
  exact G7_35_formula

theorem G35_7_interval :
    ((((5759709/102910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 7) ∧
    (baezDuarteGramEntry 35 7 ≤ (((5780291/102910000) : ℚ) : ℝ)) := by
  rw [G35_7_formula]
  exact vasyuninBEntry_7_35_eval

def interval_35_7 : NamedVasyuninInterval :=
{
  h := 35
  k := 7
  lower := (5759709/102910000)
  upper := (5780291/102910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_7_interval
}

theorem G35_8_formula : baezDuarteGramEntry 35 8 = vasyuninBEntry 8 35 := by
  rw [baezDuarteGramEntry_symm 35 8]
  exact G8_35_formula

theorem G35_8_interval :
    ((((13968677/263230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 8) ∧
    (baezDuarteGramEntry 35 8 ≤ (((14021323/263230000) : ℚ) : ℝ)) := by
  rw [G35_8_formula]
  exact vasyuninBEntry_8_35_eval

def interval_35_8 : NamedVasyuninInterval :=
{
  h := 35
  k := 8
  lower := (13968677/263230000)
  upper := (14021323/263230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_8_interval
}

theorem G35_9_formula : baezDuarteGramEntry 35 9 = vasyuninBEntry 9 35 := by
  rw [baezDuarteGramEntry_symm 35 9]
  exact G9_35_formula

theorem G35_9_interval :
    ((((35471471/685290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 9) ∧
    (baezDuarteGramEntry 35 9 ≤ (((35608529/685290000) : ℚ) : ℝ)) := by
  rw [G35_9_formula]
  exact vasyuninBEntry_9_35_eval

def interval_35_9 : NamedVasyuninInterval :=
{
  h := 35
  k := 9
  lower := (35471471/685290000)
  upper := (35608529/685290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_9_interval
}

theorem G35_10_formula : baezDuarteGramEntry 35 10 = vasyuninBEntry 10 35 := by
  rw [baezDuarteGramEntry_symm 35 10]
  exact G10_35_formula

theorem G35_10_interval :
    ((((195329/3910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 10) ∧
    (baezDuarteGramEntry 35 10 ≤ (((196111/3910000) : ℚ) : ℝ)) := by
  rw [G35_10_formula]
  exact vasyuninBEntry_10_35_eval

def interval_35_10 : NamedVasyuninInterval :=
{
  h := 35
  k := 10
  lower := (195329/3910000)
  upper := (196111/3910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_10_interval
}

theorem G35_11_formula : baezDuarteGramEntry 35 11 = vasyuninBEntry 11 35 := by
  rw [baezDuarteGramEntry_symm 35 11]
  exact G11_35_formula

theorem G35_11_interval :
    ((((46314997/950030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 11) ∧
    (baezDuarteGramEntry 35 11 ≤ (((46505003/950030000) : ℚ) : ℝ)) := by
  rw [G35_11_formula]
  exact vasyuninBEntry_11_35_eval

def interval_35_11 : NamedVasyuninInterval :=
{
  h := 35
  k := 11
  lower := (46314997/950030000)
  upper := (46505003/950030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_11_interval
}

theorem G35_12_formula : baezDuarteGramEntry 35 12 = vasyuninBEntry 12 35 := by
  rw [baezDuarteGramEntry_symm 35 12]
  exact G12_35_formula

theorem G35_12_interval :
    ((((4024091/84090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 12) ∧
    (baezDuarteGramEntry 35 12 ≤ (((4040909/84090000) : ℚ) : ℝ)) := by
  rw [G35_12_formula]
  exact vasyuninBEntry_12_35_eval

def interval_35_12 : NamedVasyuninInterval :=
{
  h := 35
  k := 12
  lower := (4024091/84090000)
  upper := (4040909/84090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_12_interval
}

theorem G35_13_formula : baezDuarteGramEntry 35 13 = vasyuninBEntry 13 35 := by
  rw [baezDuarteGramEntry_symm 35 13]
  exact G13_35_formula

theorem G35_13_interval :
    ((((79587/1730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 13) ∧
    (baezDuarteGramEntry 35 13 ≤ (((79933/1730000) : ℚ) : ℝ)) := by
  rw [G35_13_formula]
  exact vasyuninBEntry_13_35_eval

def interval_35_13 : NamedVasyuninInterval :=
{
  h := 35
  k := 13
  lower := (79587/1730000)
  upper := (79933/1730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_13_interval
}

theorem G35_14_formula : baezDuarteGramEntry 35 14 = vasyuninBEntry 14 35 := by
  rw [baezDuarteGramEntry_symm 35 14]
  exact G14_35_formula

theorem G35_14_interval :
    ((((36429227/807730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 14) ∧
    (baezDuarteGramEntry 35 14 ≤ (((36590773/807730000) : ℚ) : ℝ)) := by
  rw [G35_14_formula]
  exact vasyuninBEntry_14_35_eval

def interval_35_14 : NamedVasyuninInterval :=
{
  h := 35
  k := 14
  lower := (36429227/807730000)
  upper := (36590773/807730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_14_interval
}

theorem G35_15_formula : baezDuarteGramEntry 35 15 = vasyuninBEntry 15 35 := by
  rw [baezDuarteGramEntry_symm 35 15]
  exact G15_35_formula

theorem G35_15_interval :
    ((((1159867/26330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 15) ∧
    (baezDuarteGramEntry 35 15 ≤ (((1165133/26330000) : ℚ) : ℝ)) := by
  rw [G35_15_formula]
  exact vasyuninBEntry_15_35_eval

def interval_35_15 : NamedVasyuninInterval :=
{
  h := 35
  k := 15
  lower := (1159867/26330000)
  upper := (1165133/26330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_15_interval
}

theorem G35_16_formula : baezDuarteGramEntry 35 16 = vasyuninBEntry 16 35 := by
  rw [baezDuarteGramEntry_symm 35 16]
  exact G16_35_formula

theorem G35_16_interval :
    ((((15514261/357390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 16) ∧
    (baezDuarteGramEntry 35 16 ≤ (((15585739/357390000) : ℚ) : ℝ)) := by
  rw [G35_16_formula]
  exact vasyuninBEntry_16_35_eval

def interval_35_16 : NamedVasyuninInterval :=
{
  h := 35
  k := 16
  lower := (15514261/357390000)
  upper := (15585739/357390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_16_interval
}

theorem G35_17_formula : baezDuarteGramEntry 35 17 = vasyuninBEntry 17 35 := by
  rw [baezDuarteGramEntry_symm 35 17]
  exact G17_35_formula

theorem G35_17_interval :
    ((((4729103/108970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 17) ∧
    (baezDuarteGramEntry 35 17 ≤ (((4750897/108970000) : ℚ) : ℝ)) := by
  rw [G35_17_formula]
  exact vasyuninBEntry_17_35_eval

def interval_35_17 : NamedVasyuninInterval :=
{
  h := 35
  k := 17
  lower := (4729103/108970000)
  upper := (4750897/108970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_17_interval
}

theorem G35_18_formula : baezDuarteGramEntry 35 18 = vasyuninBEntry 18 35 := by
  rw [baezDuarteGramEntry_symm 35 18]
  exact G18_35_formula

theorem G35_18_interval :
    ((((11263511/264890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 18) ∧
    (baezDuarteGramEntry 35 18 ≤ (((11316489/264890000) : ℚ) : ℝ)) := by
  rw [G35_18_formula]
  exact vasyuninBEntry_18_35_eval

def interval_35_18 : NamedVasyuninInterval :=
{
  h := 35
  k := 18
  lower := (11263511/264890000)
  upper := (11316489/264890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_18_interval
}

theorem G35_19_formula : baezDuarteGramEntry 35 19 = vasyuninBEntry 19 35 := by
  rw [baezDuarteGramEntry_symm 35 19]
  exact G19_35_formula

theorem G35_19_interval :
    ((((2254483/55170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 19) ∧
    (baezDuarteGramEntry 35 19 ≤ (((2265517/55170000) : ℚ) : ℝ)) := by
  rw [G35_19_formula]
  exact vasyuninBEntry_19_35_eval

def interval_35_19 : NamedVasyuninInterval :=
{
  h := 35
  k := 19
  lower := (2254483/55170000)
  upper := (2265517/55170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_19_interval
}

theorem G35_20_formula : baezDuarteGramEntry 35 20 = vasyuninBEntry 20 35 := by
  rw [baezDuarteGramEntry_symm 35 20]
  exact G20_35_formula

theorem G35_20_interval :
    ((((38742621/973790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 20) ∧
    (baezDuarteGramEntry 35 20 ≤ (((38937379/973790000) : ℚ) : ℝ)) := by
  rw [G35_20_formula]
  exact vasyuninBEntry_20_35_eval

def interval_35_20 : NamedVasyuninInterval :=
{
  h := 35
  k := 20
  lower := (38742621/973790000)
  upper := (38937379/973790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_20_interval
}

theorem G35_21_formula : baezDuarteGramEntry 35 21 = vasyuninBEntry 21 35 := by
  rw [baezDuarteGramEntry_symm 35 21]
  exact G21_35_formula

theorem G35_21_interval :
    ((((1792277/45980000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 21) ∧
    (baezDuarteGramEntry 35 21 ≤ (((1801473/45980000) : ℚ) : ℝ)) := by
  rw [G35_21_formula]
  exact vasyuninBEntry_21_35_eval

def interval_35_21 : NamedVasyuninInterval :=
{
  h := 35
  k := 21
  lower := (1792277/45980000)
  upper := (1801473/45980000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_21_interval
}

theorem G35_22_formula : baezDuarteGramEntry 35 22 = vasyuninBEntry 22 35 := by
  rw [baezDuarteGramEntry_symm 35 22]
  exact G22_35_formula

theorem G35_22_interval :
    ((((18571327/486730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 22) ∧
    (baezDuarteGramEntry 35 22 ≤ (((18668673/486730000) : ℚ) : ℝ)) := by
  rw [G35_22_formula]
  exact vasyuninBEntry_22_35_eval

def interval_35_22 : NamedVasyuninInterval :=
{
  h := 35
  k := 22
  lower := (18571327/486730000)
  upper := (18668673/486730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_22_interval
}

theorem G35_23_formula : baezDuarteGramEntry 35 23 = vasyuninBEntry 23 35 := by
  rw [baezDuarteGramEntry_symm 35 23]
  exact G23_35_formula

theorem G35_23_interval :
    ((((18271511/484890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 23) ∧
    (baezDuarteGramEntry 35 23 ≤ (((18368489/484890000) : ℚ) : ℝ)) := by
  rw [G35_23_formula]
  exact vasyuninBEntry_23_35_eval

def interval_35_23 : NamedVasyuninInterval :=
{
  h := 35
  k := 23
  lower := (18271511/484890000)
  upper := (18368489/484890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_23_interval
}

theorem G35_24_formula : baezDuarteGramEntry 35 24 = vasyuninBEntry 24 35 := by
  rw [baezDuarteGramEntry_symm 35 24]
  exact G24_35_formula

theorem G35_24_interval :
    ((((27575481/745190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 24) ∧
    (baezDuarteGramEntry 35 24 ≤ (((27724519/745190000) : ℚ) : ℝ)) := by
  rw [G35_24_formula]
  exact vasyuninBEntry_24_35_eval

def interval_35_24 : NamedVasyuninInterval :=
{
  h := 35
  k := 24
  lower := (27575481/745190000)
  upper := (27724519/745190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_24_interval
}

theorem G35_25_formula : baezDuarteGramEntry 35 25 = vasyuninBEntry 25 35 := by
  rw [baezDuarteGramEntry_symm 35 25]
  exact G25_35_formula

theorem G35_25_interval :
    ((((18898109/518910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 25) ∧
    (baezDuarteGramEntry 35 25 ≤ (((19001891/518910000) : ℚ) : ℝ)) := by
  rw [G35_25_formula]
  exact vasyuninBEntry_25_35_eval

def interval_35_25 : NamedVasyuninInterval :=
{
  h := 35
  k := 25
  lower := (18898109/518910000)
  upper := (19001891/518910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_25_interval
}

theorem G35_26_formula : baezDuarteGramEntry 35 26 = vasyuninBEntry 26 35 := by
  rw [baezDuarteGramEntry_symm 35 26]
  exact G26_35_formula

theorem G35_26_interval :
    ((((19595521/544790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 26) ∧
    (baezDuarteGramEntry 35 26 ≤ (((19704479/544790000) : ℚ) : ℝ)) := by
  rw [G35_26_formula]
  exact vasyuninBEntry_26_35_eval

def interval_35_26 : NamedVasyuninInterval :=
{
  h := 35
  k := 26
  lower := (19595521/544790000)
  upper := (19704479/544790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_26_interval
}

theorem G35_27_formula : baezDuarteGramEntry 35 27 = vasyuninBEntry 27 35 := by
  rw [baezDuarteGramEntry_symm 35 27]
  exact G27_35_formula

theorem G35_27_interval :
    ((((8860057/249430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 27) ∧
    (baezDuarteGramEntry 35 27 ≤ (((8909943/249430000) : ℚ) : ℝ)) := by
  rw [G35_27_formula]
  exact vasyuninBEntry_27_35_eval

def interval_35_27 : NamedVasyuninInterval :=
{
  h := 35
  k := 27
  lower := (8860057/249430000)
  upper := (8909943/249430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_27_interval
}

theorem G35_28_formula : baezDuarteGramEntry 35 28 = vasyuninBEntry 28 35 := by
  rw [baezDuarteGramEntry_symm 35 28]
  exact G28_35_formula

theorem G35_28_interval :
    ((((16752461/475390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 28) ∧
    (baezDuarteGramEntry 35 28 ≤ (((16847539/475390000) : ℚ) : ℝ)) := by
  rw [G35_28_formula]
  exact vasyuninBEntry_28_35_eval

def interval_35_28 : NamedVasyuninInterval :=
{
  h := 35
  k := 28
  lower := (16752461/475390000)
  upper := (16847539/475390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_28_interval
}

theorem G35_29_formula : baezDuarteGramEntry 35 29 = vasyuninBEntry 29 35 := by
  rw [baezDuarteGramEntry_symm 35 29]
  exact G29_35_formula

theorem G35_29_interval :
    ((((12259887/351130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 29) ∧
    (baezDuarteGramEntry 35 29 ≤ (((12330113/351130000) : ℚ) : ℝ)) := by
  rw [G35_29_formula]
  exact vasyuninBEntry_29_35_eval

def interval_35_29 : NamedVasyuninInterval :=
{
  h := 35
  k := 29
  lower := (12259887/351130000)
  upper := (12330113/351130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_29_interval
}

theorem G35_30_formula : baezDuarteGramEntry 35 30 = vasyuninBEntry 30 35 := by
  rw [baezDuarteGramEntry_symm 35 30]
  exact G30_35_formula

theorem G35_30_interval :
    ((((9243389/266110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 30) ∧
    (baezDuarteGramEntry 35 30 ≤ (((9296611/266110000) : ℚ) : ℝ)) := by
  rw [G35_30_formula]
  exact vasyuninBEntry_30_35_eval

def interval_35_30 : NamedVasyuninInterval :=
{
  h := 35
  k := 30
  lower := (9243389/266110000)
  upper := (9296611/266110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_30_interval
}

theorem G35_31_formula : baezDuarteGramEntry 35 31 = vasyuninBEntry 31 35 := by
  rw [baezDuarteGramEntry_symm 35 31]
  exact G31_35_formula

theorem G35_31_interval :
    ((((16671829/481710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 31) ∧
    (baezDuarteGramEntry 35 31 ≤ (((16768171/481710000) : ℚ) : ℝ)) := by
  rw [G35_31_formula]
  exact vasyuninBEntry_31_35_eval

def interval_35_31 : NamedVasyuninInterval :=
{
  h := 35
  k := 31
  lower := (16671829/481710000)
  upper := (16768171/481710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_31_interval
}

theorem G35_32_formula : baezDuarteGramEntry 35 32 = vasyuninBEntry 32 35 := by
  rw [baezDuarteGramEntry_symm 35 32]
  exact G32_35_formula

theorem G35_32_interval :
    ((((1774871/51290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 32) ∧
    (baezDuarteGramEntry 35 32 ≤ (((1785129/51290000) : ℚ) : ℝ)) := by
  rw [G35_32_formula]
  exact vasyuninBEntry_32_35_eval

def interval_35_32 : NamedVasyuninInterval :=
{
  h := 35
  k := 32
  lower := (1774871/51290000)
  upper := (1785129/51290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_32_interval
}

theorem G35_33_formula : baezDuarteGramEntry 35 33 = vasyuninBEntry 33 35 := by
  rw [baezDuarteGramEntry_symm 35 33]
  exact G33_35_formula

theorem G35_33_interval :
    ((((27012227/777730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 33) ∧
    (baezDuarteGramEntry 35 33 ≤ (((27167773/777730000) : ℚ) : ℝ)) := by
  rw [G35_33_formula]
  exact vasyuninBEntry_33_35_eval

def interval_35_33 : NamedVasyuninInterval :=
{
  h := 35
  k := 33
  lower := (27012227/777730000)
  upper := (27167773/777730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_33_interval
}

theorem G35_34_formula : baezDuarteGramEntry 35 34 = vasyuninBEntry 34 35 := by
  rw [baezDuarteGramEntry_symm 35 34]
  exact G34_35_formula

theorem G35_34_interval :
    ((((2337333/66670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 34) ∧
    (baezDuarteGramEntry 35 34 ≤ (((2350667/66670000) : ℚ) : ℝ)) := by
  rw [G35_34_formula]
  exact vasyuninBEntry_34_35_eval

def interval_35_34 : NamedVasyuninInterval :=
{
  h := 35
  k := 34
  lower := (2337333/66670000)
  upper := (2350667/66670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_34_interval
}

theorem G35_35_formula_eq : baezDuarteGramEntry 35 35 = (1 / (35 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 35 := by norm_num
  rw [baez_duarte_diagonal_scaling 35 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G35_35_log_gamma_interval :
  ((((11328461/315390000) : ℚ) : ℝ) ≤ (1 / (35 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (35 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((11391539/315390000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 35 (by norm_num)
  constructor
  · have : ((((11328461/315390000) : ℚ) : ℝ) ≤ (1 / (35 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (35 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((11391539/315390000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G35_35_interval : ((((11328461/315390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 35) ∧ (baezDuarteGramEntry 35 35 ≤ (((11391539/315390000) : ℚ) : ℝ)) := by
  rw [G35_35_formula_eq]
  exact G35_35_log_gamma_interval

def interval_35_35 : NamedVasyuninInterval :=
{
  h := 35
  k := 35
  lower := (11328461/315390000)
  upper := (11391539/315390000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G35_35_interval
}

theorem G35_36_formula : baezDuarteGramEntry 35 36 = vasyuninBEntry 35 36 := vasyuninBEntry_correct_axiom 35 36

theorem vasyuninBEntry_35_36_eval :
    ((((14622113/428870000) : ℚ) : ℝ) ≤ vasyuninBEntry 35 36) ∧
    (vasyuninBEntry 35 36 ≤ (((14707887/428870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3536_formula_bound
  constructor <;> linarith

theorem G35_36_interval :
    ((((14622113/428870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 36) ∧
    (baezDuarteGramEntry 35 36 ≤ (((14707887/428870000) : ℚ) : ℝ)) := by
  rw [G35_36_formula]
  exact vasyuninBEntry_35_36_eval

def interval_35_36 : NamedVasyuninInterval :=
{
  h := 35
  k := 36
  lower := (14622113/428870000)
  upper := (14707887/428870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_36_interval
}

theorem G35_37_formula : baezDuarteGramEntry 35 37 = vasyuninBEntry 35 37 := vasyuninBEntry_correct_axiom 35 37

theorem vasyuninBEntry_35_37_eval :
    ((((17975317/546830000) : ℚ) : ℝ) ≤ vasyuninBEntry 35 37) ∧
    (vasyuninBEntry 35 37 ≤ (((18084683/546830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3537_formula_bound
  constructor <;> linarith

theorem G35_37_interval :
    ((((17975317/546830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 37) ∧
    (baezDuarteGramEntry 35 37 ≤ (((18084683/546830000) : ℚ) : ℝ)) := by
  rw [G35_37_formula]
  exact vasyuninBEntry_35_37_eval

def interval_35_37 : NamedVasyuninInterval :=
{
  h := 35
  k := 37
  lower := (17975317/546830000)
  upper := (18084683/546830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_37_interval
}

theorem G35_38_formula : baezDuarteGramEntry 35 38 = vasyuninBEntry 35 38 := vasyuninBEntry_correct_axiom 35 38

theorem vasyuninBEntry_35_38_eval :
    ((((25310607/793930000) : ℚ) : ℝ) ≤ vasyuninBEntry 35 38) ∧
    (vasyuninBEntry 35 38 ≤ (((25469393/793930000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3538_formula_bound
  constructor <;> linarith

theorem G35_38_interval :
    ((((25310607/793930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 38) ∧
    (baezDuarteGramEntry 35 38 ≤ (((25469393/793930000) : ℚ) : ℝ)) := by
  rw [G35_38_formula]
  exact vasyuninBEntry_35_38_eval

def interval_35_38 : NamedVasyuninInterval :=
{
  h := 35
  k := 38
  lower := (25310607/793930000)
  upper := (25469393/793930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_38_interval
}

theorem G35_39_formula : baezDuarteGramEntry 35 39 = vasyuninBEntry 35 39 := vasyuninBEntry_correct_axiom 35 39

theorem vasyuninBEntry_35_39_eval :
    ((((5512239/177610000) : ℚ) : ℝ) ≤ vasyuninBEntry 35 39) ∧
    (vasyuninBEntry 35 39 ≤ (((5547761/177610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3539_formula_bound
  constructor <;> linarith

theorem G35_39_interval :
    ((((5512239/177610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 39) ∧
    (baezDuarteGramEntry 35 39 ≤ (((5547761/177610000) : ℚ) : ℝ)) := by
  rw [G35_39_formula]
  exact vasyuninBEntry_35_39_eval

def interval_35_39 : NamedVasyuninInterval :=
{
  h := 35
  k := 39
  lower := (5512239/177610000)
  upper := (5547761/177610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_39_interval
}

theorem G35_40_formula : baezDuarteGramEntry 35 40 = vasyuninBEntry 35 40 := vasyuninBEntry_correct_axiom 35 40

theorem vasyuninBEntry_35_40_eval :
    ((((2630321/86790000) : ℚ) : ℝ) ≤ vasyuninBEntry 35 40) ∧
    (vasyuninBEntry 35 40 ≤ (((2647679/86790000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 8 5 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G35_40_interval :
    ((((2630321/86790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 40) ∧
    (baezDuarteGramEntry 35 40 ≤ (((2647679/86790000) : ℚ) : ℝ)) := by
  rw [G35_40_formula]
  exact vasyuninBEntry_35_40_eval

def interval_35_40 : NamedVasyuninInterval :=
{
  h := 35
  k := 40
  lower := (2630321/86790000)
  upper := (2647679/86790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_40_interval
}

theorem G35_41_formula : baezDuarteGramEntry 35 41 = vasyuninBEntry 35 41 := vasyuninBEntry_correct_axiom 35 41

theorem vasyuninBEntry_35_41_eval :
    ((((14979463/505370000) : ℚ) : ℝ) ≤ vasyuninBEntry 35 41) ∧
    (vasyuninBEntry 35 41 ≤ (((15080537/505370000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3541_formula_bound
  constructor <;> linarith

theorem G35_41_interval :
    ((((14979463/505370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 41) ∧
    (baezDuarteGramEntry 35 41 ≤ (((15080537/505370000) : ℚ) : ℝ)) := by
  rw [G35_41_formula]
  exact vasyuninBEntry_35_41_eval

def interval_35_41 : NamedVasyuninInterval :=
{
  h := 35
  k := 41
  lower := (14979463/505370000)
  upper := (15080537/505370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_41_interval
}

theorem G35_42_formula : baezDuarteGramEntry 35 42 = vasyuninBEntry 35 42 := vasyuninBEntry_correct_axiom 35 42

theorem vasyuninBEntry_35_42_eval :
    ((((4982859/171410000) : ℚ) : ℝ) ≤ vasyuninBEntry 35 42) ∧
    (vasyuninBEntry 35 42 ≤ (((5017141/171410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_6_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 6 7 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 7)
  constructor <;> linarith

theorem G35_42_interval :
    ((((4982859/171410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 42) ∧
    (baezDuarteGramEntry 35 42 ≤ (((5017141/171410000) : ℚ) : ℝ)) := by
  rw [G35_42_formula]
  exact vasyuninBEntry_35_42_eval

def interval_35_42 : NamedVasyuninInterval :=
{
  h := 35
  k := 42
  lower := (4982859/171410000)
  upper := (5017141/171410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_42_interval
}

theorem G35_43_formula : baezDuarteGramEntry 35 43 = vasyuninBEntry 35 43 := vasyuninBEntry_correct_axiom 35 43

theorem vasyuninBEntry_35_43_eval :
    ((((24175179/848210000) : ℚ) : ℝ) ≤ vasyuninBEntry 35 43) ∧
    (vasyuninBEntry 35 43 ≤ (((24344821/848210000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3543_formula_bound
  constructor <;> linarith

theorem G35_43_interval :
    ((((24175179/848210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 43) ∧
    (baezDuarteGramEntry 35 43 ≤ (((24344821/848210000) : ℚ) : ℝ)) := by
  rw [G35_43_formula]
  exact vasyuninBEntry_35_43_eval

def interval_35_43 : NamedVasyuninInterval :=
{
  h := 35
  k := 43
  lower := (24175179/848210000)
  upper := (24344821/848210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_43_interval
}

theorem G35_44_formula : baezDuarteGramEntry 35 44 = vasyuninBEntry 35 44 := vasyuninBEntry_correct_axiom 35 44

theorem vasyuninBEntry_35_44_eval :
    ((((5348411/190890000) : ℚ) : ℝ) ≤ vasyuninBEntry 35 44) ∧
    (vasyuninBEntry 35 44 ≤ (((5386589/190890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3544_formula_bound
  constructor <;> linarith

theorem G35_44_interval :
    ((((5348411/190890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 44) ∧
    (baezDuarteGramEntry 35 44 ≤ (((5386589/190890000) : ℚ) : ℝ)) := by
  rw [G35_44_formula]
  exact vasyuninBEntry_35_44_eval

def interval_35_44 : NamedVasyuninInterval :=
{
  h := 35
  k := 44
  lower := (5348411/190890000)
  upper := (5386589/190890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_44_interval
}

theorem G35_45_formula : baezDuarteGramEntry 35 45 = vasyuninBEntry 35 45 := vasyuninBEntry_correct_axiom 35 45

theorem vasyuninBEntry_35_45_eval :
    ((((3816147/138530000) : ℚ) : ℝ) ≤ vasyuninBEntry 35 45) ∧
    (vasyuninBEntry 35 45 ≤ (((3843853/138530000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 9 5 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G35_45_interval :
    ((((3816147/138530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 45) ∧
    (baezDuarteGramEntry 35 45 ≤ (((3843853/138530000) : ℚ) : ℝ)) := by
  rw [G35_45_formula]
  exact vasyuninBEntry_35_45_eval

def interval_35_45 : NamedVasyuninInterval :=
{
  h := 35
  k := 45
  lower := (3816147/138530000)
  upper := (3843853/138530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_45_interval
}

theorem G35_46_formula : baezDuarteGramEntry 35 46 = vasyuninBEntry 35 46 := vasyuninBEntry_correct_axiom 35 46

theorem vasyuninBEntry_35_46_eval :
    ((((26980551/994490000) : ℚ) : ℝ) ≤ vasyuninBEntry 35 46) ∧
    (vasyuninBEntry 35 46 ≤ (((27179449/994490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3546_formula_bound
  constructor <;> linarith

theorem G35_46_interval :
    ((((26980551/994490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 46) ∧
    (baezDuarteGramEntry 35 46 ≤ (((27179449/994490000) : ℚ) : ℝ)) := by
  rw [G35_46_formula]
  exact vasyuninBEntry_35_46_eval

def interval_35_46 : NamedVasyuninInterval :=
{
  h := 35
  k := 46
  lower := (26980551/994490000)
  upper := (27179449/994490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_46_interval
}

theorem G35_47_formula : baezDuarteGramEntry 35 47 = vasyuninBEntry 35 47 := vasyuninBEntry_correct_axiom 35 47

theorem vasyuninBEntry_35_47_eval :
    ((((200351/7490000) : ℚ) : ℝ) ≤ vasyuninBEntry 35 47) ∧
    (vasyuninBEntry 35 47 ≤ (((201849/7490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3547_formula_bound
  constructor <;> linarith

theorem G35_47_interval :
    ((((200351/7490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 47) ∧
    (baezDuarteGramEntry 35 47 ≤ (((201849/7490000) : ℚ) : ℝ)) := by
  rw [G35_47_formula]
  exact vasyuninBEntry_35_47_eval

def interval_35_47 : NamedVasyuninInterval :=
{
  h := 35
  k := 47
  lower := (200351/7490000)
  upper := (201849/7490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_47_interval
}

theorem G35_48_formula : baezDuarteGramEntry 35 48 = vasyuninBEntry 35 48 := vasyuninBEntry_correct_axiom 35 48

theorem vasyuninBEntry_35_48_eval :
    ((((16168583/614170000) : ℚ) : ℝ) ≤ vasyuninBEntry 35 48) ∧
    (vasyuninBEntry 35 48 ≤ (((16291417/614170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3548_formula_bound
  constructor <;> linarith

theorem G35_48_interval :
    ((((16168583/614170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 48) ∧
    (baezDuarteGramEntry 35 48 ≤ (((16291417/614170000) : ℚ) : ℝ)) := by
  rw [G35_48_formula]
  exact vasyuninBEntry_35_48_eval

def interval_35_48 : NamedVasyuninInterval :=
{
  h := 35
  k := 48
  lower := (16168583/614170000)
  upper := (16291417/614170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_48_interval
}

theorem G35_49_formula : baezDuarteGramEntry 35 49 = vasyuninBEntry 35 49 := vasyuninBEntry_correct_axiom 35 49

theorem vasyuninBEntry_35_49_eval :
    ((((4664549/179510000) : ℚ) : ℝ) ≤ vasyuninBEntry 35 49) ∧
    (vasyuninBEntry 35 49 ≤ (((4700451/179510000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 7 7 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 7)
  constructor <;> linarith

theorem G35_49_interval :
    ((((4664549/179510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 49) ∧
    (baezDuarteGramEntry 35 49 ≤ (((4700451/179510000) : ℚ) : ℝ)) := by
  rw [G35_49_formula]
  exact vasyuninBEntry_35_49_eval

def interval_35_49 : NamedVasyuninInterval :=
{
  h := 35
  k := 49
  lower := (4664549/179510000)
  upper := (4700451/179510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_49_interval
}

theorem G35_50_formula : baezDuarteGramEntry 35 50 = vasyuninBEntry 35 50 := vasyuninBEntry_correct_axiom 35 50

theorem vasyuninBEntry_35_50_eval :
    ((((16007581/624190000) : ℚ) : ℝ) ≤ vasyuninBEntry 35 50) ∧
    (vasyuninBEntry 35 50 ≤ (((16132419/624190000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 10 5 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G35_50_interval :
    ((((16007581/624190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 35 50) ∧
    (baezDuarteGramEntry 35 50 ≤ (((16132419/624190000) : ℚ) : ℝ)) := by
  rw [G35_50_formula]
  exact vasyuninBEntry_35_50_eval

def interval_35_50 : NamedVasyuninInterval :=
{
  h := 35
  k := 50
  lower := (16007581/624190000)
  upper := (16132419/624190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G35_50_interval
}

theorem G36_1_formula : baezDuarteGramEntry 36 1 = vasyuninBEntry 1 36 := by
  rw [baezDuarteGramEntry_symm 36 1]
  exact G1_36_formula

theorem G36_1_interval :
    ((((18107693/223070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 1) ∧
    (baezDuarteGramEntry 36 1 ≤ (((18152307/223070000) : ℚ) : ℝ)) := by
  rw [G36_1_formula]
  exact vasyuninBEntry_1_36_eval

def interval_36_1 : NamedVasyuninInterval :=
{
  h := 36
  k := 1
  lower := (18107693/223070000)
  upper := (18152307/223070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_1_interval
}

theorem G36_2_formula : baezDuarteGramEntry 36 2 = vasyuninBEntry 2 36 := by
  rw [baezDuarteGramEntry_symm 36 2]
  exact G2_36_formula

theorem G36_2_interval :
    ((((6770551/94490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 2) ∧
    (baezDuarteGramEntry 36 2 ≤ (((6789449/94490000) : ℚ) : ℝ)) := by
  rw [G36_2_formula]
  exact vasyuninBEntry_2_36_eval

def interval_36_2 : NamedVasyuninInterval :=
{
  h := 36
  k := 2
  lower := (6770551/94490000)
  upper := (6789449/94490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_2_interval
}

theorem G36_3_formula : baezDuarteGramEntry 36 3 = vasyuninBEntry 3 36 := by
  rw [baezDuarteGramEntry_symm 36 3]
  exact G3_36_formula

theorem G36_3_interval :
    ((((47617991/720090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 3) ∧
    (baezDuarteGramEntry 36 3 ≤ (((47762009/720090000) : ℚ) : ℝ)) := by
  rw [G36_3_formula]
  exact vasyuninBEntry_3_36_eval

def interval_36_3 : NamedVasyuninInterval :=
{
  h := 36
  k := 3
  lower := (47617991/720090000)
  upper := (47762009/720090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_3_interval
}

theorem G36_4_formula : baezDuarteGramEntry 36 4 = vasyuninBEntry 4 36 := by
  rw [baezDuarteGramEntry_symm 36 4]
  exact G4_36_formula

theorem G36_4_interval :
    ((((20387243/327570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 4) ∧
    (baezDuarteGramEntry 36 4 ≤ (((20452757/327570000) : ℚ) : ℝ)) := by
  rw [G36_4_formula]
  exact vasyuninBEntry_4_36_eval

def interval_36_4 : NamedVasyuninInterval :=
{
  h := 36
  k := 4
  lower := (20387243/327570000)
  upper := (20452757/327570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_4_interval
}

theorem G36_5_formula : baezDuarteGramEntry 36 5 = vasyuninBEntry 5 36 := by
  rw [baezDuarteGramEntry_symm 36 5]
  exact G5_36_formula

theorem G36_5_interval :
    ((((11111071/189290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 5) ∧
    (baezDuarteGramEntry 36 5 ≤ (((11148929/189290000) : ℚ) : ℝ)) := by
  rw [G36_5_formula]
  exact vasyuninBEntry_5_36_eval

def interval_36_5 : NamedVasyuninInterval :=
{
  h := 36
  k := 5
  lower := (11111071/189290000)
  upper := (11148929/189290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_5_interval
}

theorem G36_6_formula : baezDuarteGramEntry 36 6 = vasyuninBEntry 6 36 := by
  rw [baezDuarteGramEntry_symm 36 6]
  exact G6_36_formula

theorem G36_6_interval :
    ((((31135201/547990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 6) ∧
    (baezDuarteGramEntry 36 6 ≤ (((31244799/547990000) : ℚ) : ℝ)) := by
  rw [G36_6_formula]
  exact vasyuninBEntry_6_36_eval

def interval_36_6 : NamedVasyuninInterval :=
{
  h := 36
  k := 6
  lower := (31135201/547990000)
  upper := (31244799/547990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_6_interval
}

theorem G36_7_formula : baezDuarteGramEntry 36 7 = vasyuninBEntry 7 36 := by
  rw [baezDuarteGramEntry_symm 36 7]
  exact G7_36_formula

theorem G36_7_interval :
    ((((48739947/900530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 7) ∧
    (baezDuarteGramEntry 36 7 ≤ (((48920053/900530000) : ℚ) : ℝ)) := by
  rw [G36_7_formula]
  exact vasyuninBEntry_7_36_eval

def interval_36_7 : NamedVasyuninInterval :=
{
  h := 36
  k := 7
  lower := (48739947/900530000)
  upper := (48920053/900530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_7_interval
}

theorem G36_8_formula : baezDuarteGramEntry 36 8 = vasyuninBEntry 8 36 := by
  rw [baezDuarteGramEntry_symm 36 8]
  exact G8_36_formula

theorem G36_8_interval :
    ((((8286091/159090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 8) ∧
    (baezDuarteGramEntry 36 8 ≤ (((8317909/159090000) : ℚ) : ℝ)) := by
  rw [G36_8_formula]
  exact vasyuninBEntry_8_36_eval

def interval_36_8 : NamedVasyuninInterval :=
{
  h := 36
  k := 8
  lower := (8286091/159090000)
  upper := (8317909/159090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_8_interval
}

theorem G36_9_formula : baezDuarteGramEntry 36 9 = vasyuninBEntry 9 36 := by
  rw [baezDuarteGramEntry_symm 36 9]
  exact G9_36_formula

theorem G36_9_interval :
    ((((16847287/327130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 9) ∧
    (baezDuarteGramEntry 36 9 ≤ (((16912713/327130000) : ℚ) : ℝ)) := by
  rw [G36_9_formula]
  exact vasyuninBEntry_9_36_eval

def interval_36_9 : NamedVasyuninInterval :=
{
  h := 36
  k := 9
  lower := (16847287/327130000)
  upper := (16912713/327130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_9_interval
}

theorem G36_10_formula : baezDuarteGramEntry 36 10 = vasyuninBEntry 10 36 := by
  rw [baezDuarteGramEntry_symm 36 10]
  exact G10_36_formula

theorem G36_10_interval :
    ((((7985639/163610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 10) ∧
    (baezDuarteGramEntry 36 10 ≤ (((8018361/163610000) : ℚ) : ℝ)) := by
  rw [G36_10_formula]
  exact vasyuninBEntry_10_36_eval

def interval_36_10 : NamedVasyuninInterval :=
{
  h := 36
  k := 10
  lower := (7985639/163610000)
  upper := (8018361/163610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_10_interval
}

theorem G36_11_formula : baezDuarteGramEntry 36 11 = vasyuninBEntry 11 36 := by
  rw [baezDuarteGramEntry_symm 36 11]
  exact G11_36_formula

theorem G36_11_interval :
    ((((27252747/572530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 11) ∧
    (baezDuarteGramEntry 36 11 ≤ (((27367253/572530000) : ℚ) : ℝ)) := by
  rw [G36_11_formula]
  exact vasyuninBEntry_11_36_eval

def interval_36_11 : NamedVasyuninInterval :=
{
  h := 36
  k := 11
  lower := (27252747/572530000)
  upper := (27367253/572530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_11_interval
}

theorem G36_12_formula : baezDuarteGramEntry 36 12 = vasyuninBEntry 12 36 := by
  rw [baezDuarteGramEntry_symm 36 12]
  exact G12_36_formula

theorem G36_12_interval :
    ((((37910717/792830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 12) ∧
    (baezDuarteGramEntry 36 12 ≤ (((38069283/792830000) : ℚ) : ℝ)) := by
  rw [G36_12_formula]
  exact vasyuninBEntry_12_36_eval

def interval_36_12 : NamedVasyuninInterval :=
{
  h := 36
  k := 12
  lower := (37910717/792830000)
  upper := (38069283/792830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_12_interval
}

theorem G36_13_formula : baezDuarteGramEntry 36 13 = vasyuninBEntry 13 36 := by
  rw [baezDuarteGramEntry_symm 36 13]
  exact G13_36_formula

theorem G36_13_interval :
    ((((22570103/498970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 13) ∧
    (baezDuarteGramEntry 36 13 ≤ (((22669897/498970000) : ℚ) : ℝ)) := by
  rw [G36_13_formula]
  exact vasyuninBEntry_13_36_eval

def interval_36_13 : NamedVasyuninInterval :=
{
  h := 36
  k := 13
  lower := (22570103/498970000)
  upper := (22669897/498970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_13_interval
}

theorem G36_14_formula : baezDuarteGramEntry 36 14 = vasyuninBEntry 14 36 := by
  rw [baezDuarteGramEntry_symm 36 14]
  exact G14_36_formula

theorem G36_14_interval :
    ((((41336101/938990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 14) ∧
    (baezDuarteGramEntry 36 14 ≤ (((41523899/938990000) : ℚ) : ℝ)) := by
  rw [G36_14_formula]
  exact vasyuninBEntry_14_36_eval

def interval_36_14 : NamedVasyuninInterval :=
{
  h := 36
  k := 14
  lower := (41336101/938990000)
  upper := (41523899/938990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_14_interval
}

theorem G36_15_formula : baezDuarteGramEntry 36 15 = vasyuninBEntry 15 36 := by
  rw [baezDuarteGramEntry_symm 36 15]
  exact G15_36_formula

theorem G36_15_interval :
    ((((12481037/289630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 15) ∧
    (baezDuarteGramEntry 36 15 ≤ (((12538963/289630000) : ℚ) : ℝ)) := by
  rw [G36_15_formula]
  exact vasyuninBEntry_15_36_eval

def interval_36_15 : NamedVasyuninInterval :=
{
  h := 36
  k := 15
  lower := (12481037/289630000)
  upper := (12538963/289630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_15_interval
}

theorem G36_16_formula : baezDuarteGramEntry 36 16 = vasyuninBEntry 16 36 := by
  rw [baezDuarteGramEntry_symm 36 16]
  exact G16_36_formula

theorem G36_16_interval :
    ((((671667/15830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 16) ∧
    (baezDuarteGramEntry 36 16 ≤ (((674833/15830000) : ℚ) : ℝ)) := by
  rw [G36_16_formula]
  exact vasyuninBEntry_16_36_eval

def interval_36_16 : NamedVasyuninInterval :=
{
  h := 36
  k := 16
  lower := (671667/15830000)
  upper := (674833/15830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_16_interval
}

theorem G36_17_formula : baezDuarteGramEntry 36 17 = vasyuninBEntry 17 36 := by
  rw [baezDuarteGramEntry_symm 36 17]
  exact G17_36_formula

theorem G36_17_interval :
    ((((20296787/482130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 17) ∧
    (baezDuarteGramEntry 36 17 ≤ (((20393213/482130000) : ℚ) : ℝ)) := by
  rw [G36_17_formula]
  exact vasyuninBEntry_17_36_eval

def interval_36_17 : NamedVasyuninInterval :=
{
  h := 36
  k := 17
  lower := (20296787/482130000)
  upper := (20393213/482130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_17_interval
}

theorem G36_18_formula : baezDuarteGramEntry 36 18 = vasyuninBEntry 18 36 := by
  rw [baezDuarteGramEntry_symm 36 18]
  exact G18_36_formula

theorem G36_18_interval :
    ((((18890863/441370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 18) ∧
    (baezDuarteGramEntry 36 18 ≤ (((18979137/441370000) : ℚ) : ℝ)) := by
  rw [G36_18_formula]
  exact vasyuninBEntry_18_36_eval

def interval_36_18 : NamedVasyuninInterval :=
{
  h := 36
  k := 18
  lower := (18890863/441370000)
  upper := (18979137/441370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_18_interval
}

theorem G36_19_formula : baezDuarteGramEntry 36 19 = vasyuninBEntry 19 36 := by
  rw [baezDuarteGramEntry_symm 36 19]
  exact G19_36_formula

theorem G36_19_interval :
    ((((6100927/150730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 19) ∧
    (baezDuarteGramEntry 36 19 ≤ (((6131073/150730000) : ℚ) : ℝ)) := by
  rw [G36_19_formula]
  exact vasyuninBEntry_19_36_eval

def interval_36_19 : NamedVasyuninInterval :=
{
  h := 36
  k := 19
  lower := (6100927/150730000)
  upper := (6131073/150730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_19_interval
}

theorem G36_20_formula : baezDuarteGramEntry 36 20 = vasyuninBEntry 20 36 := by
  rw [baezDuarteGramEntry_symm 36 20]
  exact G20_36_formula

theorem G36_20_interval :
    ((((4299039/109610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 20) ∧
    (baezDuarteGramEntry 36 20 ≤ (((4320961/109610000) : ℚ) : ℝ)) := by
  rw [G36_20_formula]
  exact vasyuninBEntry_20_36_eval

def interval_36_20 : NamedVasyuninInterval :=
{
  h := 36
  k := 20
  lower := (4299039/109610000)
  upper := (4320961/109610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_20_interval
}

theorem G36_21_formula : baezDuarteGramEntry 36 21 = vasyuninBEntry 21 36 := by
  rw [baezDuarteGramEntry_symm 36 21]
  exact G21_36_formula

theorem G36_21_interval :
    ((((20695919/540810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 21) ∧
    (baezDuarteGramEntry 36 21 ≤ (((20804081/540810000) : ℚ) : ℝ)) := by
  rw [G36_21_formula]
  exact vasyuninBEntry_21_36_eval

def interval_36_21 : NamedVasyuninInterval :=
{
  h := 36
  k := 21
  lower := (20695919/540810000)
  upper := (20804081/540810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_21_interval
}

theorem G36_22_formula : baezDuarteGramEntry 36 22 = vasyuninBEntry 22 36 := by
  rw [baezDuarteGramEntry_symm 36 22]
  exact G22_36_formula

theorem G36_22_interval :
    ((((16032257/427430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 22) ∧
    (baezDuarteGramEntry 36 22 ≤ (((16117743/427430000) : ℚ) : ℝ)) := by
  rw [G36_22_formula]
  exact vasyuninBEntry_22_36_eval

def interval_36_22 : NamedVasyuninInterval :=
{
  h := 36
  k := 22
  lower := (16032257/427430000)
  upper := (16117743/427430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_22_interval
}

theorem G36_23_formula : baezDuarteGramEntry 36 23 = vasyuninBEntry 23 36 := by
  rw [baezDuarteGramEntry_symm 36 23]
  exact G23_36_formula

theorem G36_23_interval :
    ((((1385743/37570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 23) ∧
    (baezDuarteGramEntry 36 23 ≤ (((1393257/37570000) : ℚ) : ℝ)) := by
  rw [G36_23_formula]
  exact vasyuninBEntry_23_36_eval

def interval_36_23 : NamedVasyuninInterval :=
{
  h := 36
  k := 23
  lower := (1385743/37570000)
  upper := (1393257/37570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_23_interval
}

theorem G36_24_formula : baezDuarteGramEntry 36 24 = vasyuninBEntry 24 36 := by
  rw [baezDuarteGramEntry_symm 36 24]
  exact G24_36_formula

theorem G36_24_interval :
    ((((4876697/133030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 24) ∧
    (baezDuarteGramEntry 36 24 ≤ (((4903303/133030000) : ℚ) : ℝ)) := by
  rw [G36_24_formula]
  exact vasyuninBEntry_24_36_eval

def interval_36_24 : NamedVasyuninInterval :=
{
  h := 36
  k := 24
  lower := (4876697/133030000)
  upper := (4903303/133030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_24_interval
}

theorem G36_25_formula : baezDuarteGramEntry 36 25 = vasyuninBEntry 25 36 := by
  rw [baezDuarteGramEntry_symm 36 25]
  exact G25_36_formula

theorem G36_25_interval :
    ((((10341087/289130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 25) ∧
    (baezDuarteGramEntry 36 25 ≤ (((10398913/289130000) : ℚ) : ℝ)) := by
  rw [G36_25_formula]
  exact vasyuninBEntry_25_36_eval

def interval_36_25 : NamedVasyuninInterval :=
{
  h := 36
  k := 25
  lower := (10341087/289130000)
  upper := (10398913/289130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_25_interval
}

theorem G36_26_formula : baezDuarteGramEntry 36 26 = vasyuninBEntry 26 36 := by
  rw [baezDuarteGramEntry_symm 36 26]
  exact G26_36_formula

theorem G36_26_interval :
    ((((13491719/382810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 26) ∧
    (baezDuarteGramEntry 36 26 ≤ (((13568281/382810000) : ℚ) : ℝ)) := by
  rw [G36_26_formula]
  exact vasyuninBEntry_26_36_eval

def interval_36_26 : NamedVasyuninInterval :=
{
  h := 36
  k := 26
  lower := (13491719/382810000)
  upper := (13568281/382810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_26_interval
}

theorem G36_27_formula : baezDuarteGramEntry 36 27 = vasyuninBEntry 27 36 := by
  rw [baezDuarteGramEntry_symm 36 27]
  exact G27_36_formula

theorem G36_27_interval :
    ((((12603937/360630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 27) ∧
    (baezDuarteGramEntry 36 27 ≤ (((12676063/360630000) : ℚ) : ℝ)) := by
  rw [G36_27_formula]
  exact vasyuninBEntry_27_36_eval

def interval_36_27 : NamedVasyuninInterval :=
{
  h := 36
  k := 27
  lower := (12603937/360630000)
  upper := (12676063/360630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_27_interval
}

theorem G36_28_formula : baezDuarteGramEntry 36 28 = vasyuninBEntry 28 36 := by
  rw [baezDuarteGramEntry_symm 36 28]
  exact G28_36_formula

theorem G36_28_interval :
    ((((5837061/169390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 28) ∧
    (baezDuarteGramEntry 36 28 ≤ (((5870939/169390000) : ℚ) : ℝ)) := by
  rw [G36_28_formula]
  exact vasyuninBEntry_28_36_eval

def interval_36_28 : NamedVasyuninInterval :=
{
  h := 36
  k := 28
  lower := (5837061/169390000)
  upper := (5870939/169390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_28_interval
}

theorem G36_29_formula : baezDuarteGramEntry 36 29 = vasyuninBEntry 29 36 := by
  rw [baezDuarteGramEntry_symm 36 29]
  exact G29_36_formula

theorem G36_29_interval :
    ((((6385307/186930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 29) ∧
    (baezDuarteGramEntry 36 29 ≤ (((6422693/186930000) : ℚ) : ℝ)) := by
  rw [G36_29_formula]
  exact vasyuninBEntry_29_36_eval

def interval_36_29 : NamedVasyuninInterval :=
{
  h := 36
  k := 29
  lower := (6385307/186930000)
  upper := (6422693/186930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_29_interval
}

theorem G36_30_formula : baezDuarteGramEntry 36 30 = vasyuninBEntry 30 36 := by
  rw [baezDuarteGramEntry_symm 36 30]
  exact G30_36_formula

theorem G36_30_interval :
    ((((17448577/514230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 30) ∧
    (baezDuarteGramEntry 36 30 ≤ (((17551423/514230000) : ℚ) : ℝ)) := by
  rw [G36_30_formula]
  exact vasyuninBEntry_30_36_eval

def interval_36_30 : NamedVasyuninInterval :=
{
  h := 36
  k := 30
  lower := (17448577/514230000)
  upper := (17551423/514230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_30_interval
}

theorem G36_31_formula : baezDuarteGramEntry 36 31 = vasyuninBEntry 31 36 := by
  rw [baezDuarteGramEntry_symm 36 31]
  exact G31_36_formula

theorem G36_31_interval :
    ((((33510657/993430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 31) ∧
    (baezDuarteGramEntry 36 31 ≤ (((33709343/993430000) : ℚ) : ℝ)) := by
  rw [G36_31_formula]
  exact vasyuninBEntry_31_36_eval

def interval_36_31 : NamedVasyuninInterval :=
{
  h := 36
  k := 31
  lower := (33510657/993430000)
  upper := (33709343/993430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_31_interval
}

theorem G36_32_formula : baezDuarteGramEntry 36 32 = vasyuninBEntry 32 36 := by
  rw [baezDuarteGramEntry_symm 36 32]
  exact G32_36_formula

theorem G36_32_interval :
    ((((6638271/197290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 32) ∧
    (baezDuarteGramEntry 36 32 ≤ (((6677729/197290000) : ℚ) : ℝ)) := by
  rw [G36_32_formula]
  exact vasyuninBEntry_32_36_eval

def interval_36_32 : NamedVasyuninInterval :=
{
  h := 36
  k := 32
  lower := (6638271/197290000)
  upper := (6677729/197290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_32_interval
}

theorem G36_33_formula : baezDuarteGramEntry 36 33 = vasyuninBEntry 33 36 := by
  rw [baezDuarteGramEntry_symm 36 33]
  exact G33_36_formula

theorem G36_33_interval :
    ((((30708737/912630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 33) ∧
    (baezDuarteGramEntry 36 33 ≤ (((30891263/912630000) : ℚ) : ℝ)) := by
  rw [G36_33_formula]
  exact vasyuninBEntry_33_36_eval

def interval_36_33 : NamedVasyuninInterval :=
{
  h := 36
  k := 33
  lower := (30708737/912630000)
  upper := (30891263/912630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_33_interval
}

theorem G36_34_formula : baezDuarteGramEntry 36 34 = vasyuninBEntry 34 36 := by
  rw [baezDuarteGramEntry_symm 36 34]
  exact G34_36_formula

theorem G36_34_interval :
    ((((16815217/497830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 34) ∧
    (baezDuarteGramEntry 36 34 ≤ (((16914783/497830000) : ℚ) : ℝ)) := by
  rw [G36_34_formula]
  exact vasyuninBEntry_34_36_eval

def interval_36_34 : NamedVasyuninInterval :=
{
  h := 36
  k := 34
  lower := (16815217/497830000)
  upper := (16914783/497830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_34_interval
}

theorem G36_35_formula : baezDuarteGramEntry 36 35 = vasyuninBEntry 35 36 := by
  rw [baezDuarteGramEntry_symm 36 35]
  exact G35_36_formula

theorem G36_35_interval :
    ((((14622113/428870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 35) ∧
    (baezDuarteGramEntry 36 35 ≤ (((14707887/428870000) : ℚ) : ℝ)) := by
  rw [G36_35_formula]
  exact vasyuninBEntry_35_36_eval

def interval_36_35 : NamedVasyuninInterval :=
{
  h := 36
  k := 35
  lower := (14622113/428870000)
  upper := (14707887/428870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_35_interval
}

theorem G36_36_formula_eq : baezDuarteGramEntry 36 36 = (1 / (36 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 36 := by norm_num
  rw [baez_duarte_diagonal_scaling 36 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G36_36_log_gamma_interval :
  ((((3136019/89810000) : ℚ) : ℝ) ≤ (1 / (36 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (36 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((3153981/89810000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 36 (by norm_num)
  constructor
  · have : ((((3136019/89810000) : ℚ) : ℝ) ≤ (1 / (36 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (36 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((3153981/89810000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G36_36_interval : ((((3136019/89810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 36) ∧ (baezDuarteGramEntry 36 36 ≤ (((3153981/89810000) : ℚ) : ℝ)) := by
  rw [G36_36_formula_eq]
  exact G36_36_log_gamma_interval

def interval_36_36 : NamedVasyuninInterval :=
{
  h := 36
  k := 36
  lower := (3136019/89810000)
  upper := (3153981/89810000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G36_36_interval
}

theorem G36_37_formula : baezDuarteGramEntry 36 37 = vasyuninBEntry 36 37 := vasyuninBEntry_correct_axiom 36 37

theorem vasyuninBEntry_36_37_eval :
    ((((9566171/288290000) : ℚ) : ℝ) ≤ vasyuninBEntry 36 37) ∧
    (vasyuninBEntry 36 37 ≤ (((9623829/288290000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3637_formula_bound
  constructor <;> linarith

theorem G36_37_interval :
    ((((9566171/288290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 37) ∧
    (baezDuarteGramEntry 36 37 ≤ (((9623829/288290000) : ℚ) : ℝ)) := by
  rw [G36_37_formula]
  exact vasyuninBEntry_36_37_eval

def interval_36_37 : NamedVasyuninInterval :=
{
  h := 36
  k := 37
  lower := (9566171/288290000)
  upper := (9623829/288290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_37_interval
}

theorem G36_38_formula : baezDuarteGramEntry 36 38 = vasyuninBEntry 36 38 := vasyuninBEntry_correct_axiom 36 38

theorem vasyuninBEntry_36_38_eval :
    ((((4750163/148370000) : ℚ) : ℝ) ≤ vasyuninBEntry 36 38) ∧
    (vasyuninBEntry 36 38 ≤ (((4779837/148370000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_18_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 18 19 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G36_38_interval :
    ((((4750163/148370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 38) ∧
    (baezDuarteGramEntry 36 38 ≤ (((4779837/148370000) : ℚ) : ℝ)) := by
  rw [G36_38_formula]
  exact vasyuninBEntry_36_38_eval

def interval_36_38 : NamedVasyuninInterval :=
{
  h := 36
  k := 38
  lower := (4750163/148370000)
  upper := (4779837/148370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_38_interval
}

theorem G36_39_formula : baezDuarteGramEntry 36 39 = vasyuninBEntry 36 39 := vasyuninBEntry_correct_axiom 36 39

theorem vasyuninBEntry_36_39_eval :
    ((((1305797/42030000) : ℚ) : ℝ) ≤ vasyuninBEntry 36 39) ∧
    (vasyuninBEntry 36 39 ≤ (((1314203/42030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_12_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 12 13 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G36_39_interval :
    ((((1305797/42030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 39) ∧
    (baezDuarteGramEntry 36 39 ≤ (((1314203/42030000) : ℚ) : ℝ)) := by
  rw [G36_39_formula]
  exact vasyuninBEntry_36_39_eval

def interval_36_39 : NamedVasyuninInterval :=
{
  h := 36
  k := 39
  lower := (1305797/42030000)
  upper := (1314203/42030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_39_interval
}

theorem G36_40_formula : baezDuarteGramEntry 36 40 = vasyuninBEntry 36 40 := vasyuninBEntry_correct_axiom 36 40

theorem vasyuninBEntry_36_40_eval :
    ((((1723679/56960000) : ℚ) : ℝ) ≤ vasyuninBEntry 36 40) ∧
    (vasyuninBEntry 36 40 ≤ (((1735071/56960000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 10 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G36_40_interval :
    ((((1723679/56960000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 40) ∧
    (baezDuarteGramEntry 36 40 ≤ (((1735071/56960000) : ℚ) : ℝ)) := by
  rw [G36_40_formula]
  exact vasyuninBEntry_36_40_eval

def interval_36_40 : NamedVasyuninInterval :=
{
  h := 36
  k := 40
  lower := (1723679/56960000)
  upper := (1735071/56960000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_40_interval
}

theorem G36_41_formula : baezDuarteGramEntry 36 41 = vasyuninBEntry 36 41 := vasyuninBEntry_correct_axiom 36 41

theorem vasyuninBEntry_36_41_eval :
    ((((2023153/68470000) : ℚ) : ℝ) ≤ vasyuninBEntry 36 41) ∧
    (vasyuninBEntry 36 41 ≤ (((2036847/68470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3641_formula_bound
  constructor <;> linarith

theorem G36_41_interval :
    ((((2023153/68470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 41) ∧
    (baezDuarteGramEntry 36 41 ≤ (((2036847/68470000) : ℚ) : ℝ)) := by
  rw [G36_41_formula]
  exact vasyuninBEntry_36_41_eval

def interval_36_41 : NamedVasyuninInterval :=
{
  h := 36
  k := 41
  lower := (2023153/68470000)
  upper := (2036847/68470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_41_interval
}

theorem G36_42_formula : baezDuarteGramEntry 36 42 = vasyuninBEntry 36 42 := vasyuninBEntry_correct_axiom 36 42

theorem vasyuninBEntry_36_42_eval :
    ((((25342399/876010000) : ℚ) : ℝ) ≤ vasyuninBEntry 36 42) ∧
    (vasyuninBEntry 36 42 ≤ (((25517601/876010000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_6_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 6 7 6 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G36_42_interval :
    ((((25342399/876010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 42) ∧
    (baezDuarteGramEntry 36 42 ≤ (((25517601/876010000) : ℚ) : ℝ)) := by
  rw [G36_42_formula]
  exact vasyuninBEntry_36_42_eval

def interval_36_42 : NamedVasyuninInterval :=
{
  h := 36
  k := 42
  lower := (25342399/876010000)
  upper := (25517601/876010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_42_interval
}

theorem G36_43_formula : baezDuarteGramEntry 36 43 = vasyuninBEntry 36 43 := vasyuninBEntry_correct_axiom 36 43

theorem vasyuninBEntry_36_43_eval :
    ((((21255023/749770000) : ℚ) : ℝ) ≤ vasyuninBEntry 36 43) ∧
    (vasyuninBEntry 36 43 ≤ (((21404977/749770000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3643_formula_bound
  constructor <;> linarith

theorem G36_43_interval :
    ((((21255023/749770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 43) ∧
    (baezDuarteGramEntry 36 43 ≤ (((21404977/749770000) : ℚ) : ℝ)) := by
  rw [G36_43_formula]
  exact vasyuninBEntry_36_43_eval

def interval_36_43 : NamedVasyuninInterval :=
{
  h := 36
  k := 43
  lower := (21255023/749770000)
  upper := (21404977/749770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_43_interval
}

theorem G36_44_formula : baezDuarteGramEntry 36 44 = vasyuninBEntry 36 44 := vasyuninBEntry_correct_axiom 36 44

theorem vasyuninBEntry_36_44_eval :
    ((((1330219/47810000) : ℚ) : ℝ) ≤ vasyuninBEntry 36 44) ∧
    (vasyuninBEntry 36 44 ≤ (((1339781/47810000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 11 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G36_44_interval :
    ((((1330219/47810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 44) ∧
    (baezDuarteGramEntry 36 44 ≤ (((1339781/47810000) : ℚ) : ℝ)) := by
  rw [G36_44_formula]
  exact vasyuninBEntry_36_44_eval

def interval_36_44 : NamedVasyuninInterval :=
{
  h := 36
  k := 44
  lower := (1330219/47810000)
  upper := (1339781/47810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_44_interval
}

theorem G36_45_formula : baezDuarteGramEntry 36 45 = vasyuninBEntry 36 45 := vasyuninBEntry_correct_axiom 36 45

theorem vasyuninBEntry_36_45_eval :
    ((((20794071/759290000) : ℚ) : ℝ) ≤ vasyuninBEntry 36 45) ∧
    (vasyuninBEntry 36 45 ≤ (((20945929/759290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 5 9 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 9)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 9)
  constructor <;> linarith

theorem G36_45_interval :
    ((((20794071/759290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 45) ∧
    (baezDuarteGramEntry 36 45 ≤ (((20945929/759290000) : ℚ) : ℝ)) := by
  rw [G36_45_formula]
  exact vasyuninBEntry_36_45_eval

def interval_36_45 : NamedVasyuninInterval :=
{
  h := 36
  k := 45
  lower := (20794071/759290000)
  upper := (20945929/759290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_45_interval
}

theorem G36_46_formula : baezDuarteGramEntry 36 46 = vasyuninBEntry 36 46 := vasyuninBEntry_correct_axiom 36 46

theorem vasyuninBEntry_36_46_eval :
    ((((26083011/969890000) : ℚ) : ℝ) ≤ vasyuninBEntry 36 46) ∧
    (vasyuninBEntry 36 46 ≤ (((26276989/969890000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_18_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 18 23 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G36_46_interval :
    ((((26083011/969890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 46) ∧
    (baezDuarteGramEntry 36 46 ≤ (((26276989/969890000) : ℚ) : ℝ)) := by
  rw [G36_46_formula]
  exact vasyuninBEntry_36_46_eval

def interval_36_46 : NamedVasyuninInterval :=
{
  h := 36
  k := 46
  lower := (26083011/969890000)
  upper := (26276989/969890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_46_interval
}

theorem G36_47_formula : baezDuarteGramEntry 36 47 = vasyuninBEntry 36 47 := vasyuninBEntry_correct_axiom 36 47

theorem vasyuninBEntry_36_47_eval :
    ((((20582293/777070000) : ℚ) : ℝ) ≤ vasyuninBEntry 36 47) ∧
    (vasyuninBEntry 36 47 ≤ (((20737707/777070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3647_formula_bound
  constructor <;> linarith

theorem G36_47_interval :
    ((((20582293/777070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 47) ∧
    (baezDuarteGramEntry 36 47 ≤ (((20737707/777070000) : ℚ) : ℝ)) := by
  rw [G36_47_formula]
  exact vasyuninBEntry_36_47_eval

def interval_36_47 : NamedVasyuninInterval :=
{
  h := 36
  k := 47
  lower := (20582293/777070000)
  upper := (20737707/777070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_47_interval
}

theorem G36_48_formula : baezDuarteGramEntry 36 48 = vasyuninBEntry 36 48 := vasyuninBEntry_correct_axiom 36 48

theorem vasyuninBEntry_36_48_eval :
    ((((3147979/120210000) : ℚ) : ℝ) ≤ vasyuninBEntry 36 48) ∧
    (vasyuninBEntry 36 48 ≤ (((3172021/120210000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 4 12 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 12)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 12)
  constructor <;> linarith

theorem G36_48_interval :
    ((((3147979/120210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 48) ∧
    (baezDuarteGramEntry 36 48 ≤ (((3172021/120210000) : ℚ) : ℝ)) := by
  rw [G36_48_formula]
  exact vasyuninBEntry_36_48_eval

def interval_36_48 : NamedVasyuninInterval :=
{
  h := 36
  k := 48
  lower := (3147979/120210000)
  upper := (3172021/120210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_48_interval
}

theorem G36_49_formula : baezDuarteGramEntry 36 49 = vasyuninBEntry 36 49 := vasyuninBEntry_correct_axiom 36 49

theorem vasyuninBEntry_36_49_eval :
    ((((4024359/156410000) : ℚ) : ℝ) ≤ vasyuninBEntry 36 49) ∧
    (vasyuninBEntry 36 49 ≤ (((4055641/156410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3649_formula_bound
  constructor <;> linarith

theorem G36_49_interval :
    ((((4024359/156410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 49) ∧
    (baezDuarteGramEntry 36 49 ≤ (((4055641/156410000) : ℚ) : ℝ)) := by
  rw [G36_49_formula]
  exact vasyuninBEntry_36_49_eval

def interval_36_49 : NamedVasyuninInterval :=
{
  h := 36
  k := 49
  lower := (4024359/156410000)
  upper := (4055641/156410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_49_interval
}

theorem G36_50_formula : baezDuarteGramEntry 36 50 = vasyuninBEntry 36 50 := vasyuninBEntry_correct_axiom 36 50

theorem vasyuninBEntry_36_50_eval :
    ((((25360057/999430000) : ℚ) : ℝ) ≤ vasyuninBEntry 36 50) ∧
    (vasyuninBEntry 36 50 ≤ (((25559943/999430000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_18_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 18 25 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G36_50_interval :
    ((((25360057/999430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 36 50) ∧
    (baezDuarteGramEntry 36 50 ≤ (((25559943/999430000) : ℚ) : ℝ)) := by
  rw [G36_50_formula]
  exact vasyuninBEntry_36_50_eval

def interval_36_50 : NamedVasyuninInterval :=
{
  h := 36
  k := 50
  lower := (25360057/999430000)
  upper := (25559943/999430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G36_50_interval
}

theorem G37_1_formula : baezDuarteGramEntry 37 1 = vasyuninBEntry 1 37 := by
  rw [baezDuarteGramEntry_symm 37 1]
  exact G1_37_formula

theorem G37_1_interval :
    ((((2290713/28870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 1) ∧
    (baezDuarteGramEntry 37 1 ≤ (((2296487/28870000) : ℚ) : ℝ)) := by
  rw [G37_1_formula]
  exact vasyuninBEntry_1_37_eval

def interval_37_1 : NamedVasyuninInterval :=
{
  h := 37
  k := 1
  lower := (2290713/28870000)
  upper := (2296487/28870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_1_interval
}

theorem G37_2_formula : baezDuarteGramEntry 37 2 = vasyuninBEntry 2 37 := by
  rw [baezDuarteGramEntry_symm 37 2]
  exact G2_37_formula

theorem G37_2_interval :
    ((((12552031/179690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 2) ∧
    (baezDuarteGramEntry 37 2 ≤ (((12587969/179690000) : ℚ) : ℝ)) := by
  rw [G37_2_formula]
  exact vasyuninBEntry_2_37_eval

def interval_37_2 : NamedVasyuninInterval :=
{
  h := 37
  k := 2
  lower := (12552031/179690000)
  upper := (12587969/179690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_2_interval
}

theorem G37_3_formula : baezDuarteGramEntry 37 3 = vasyuninBEntry 3 37 := by
  rw [baezDuarteGramEntry_symm 37 3]
  exact G3_37_formula

theorem G37_3_interval :
    ((((3872981/60190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 3) ∧
    (baezDuarteGramEntry 37 3 ≤ (((3885019/60190000) : ℚ) : ℝ)) := by
  rw [G37_3_formula]
  exact vasyuninBEntry_3_37_eval

def interval_37_3 : NamedVasyuninInterval :=
{
  h := 37
  k := 3
  lower := (3872981/60190000)
  upper := (3885019/60190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_3_interval
}

theorem G37_4_formula : baezDuarteGramEntry 37 4 = vasyuninBEntry 4 37 := by
  rw [baezDuarteGramEntry_symm 37 4]
  exact G4_37_formula

theorem G37_4_interval :
    ((((1817931/30065000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 4) ∧
    (baezDuarteGramEntry 37 4 ≤ (((227993/3758125) : ℚ) : ℝ)) := by
  rw [G37_4_formula]
  exact vasyuninBEntry_4_37_eval

def interval_37_4 : NamedVasyuninInterval :=
{
  h := 37
  k := 4
  lower := (1817931/30065000)
  upper := (227993/3758125)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_4_interval
}

theorem G37_5_formula : baezDuarteGramEntry 37 5 = vasyuninBEntry 5 37 := by
  rw [baezDuarteGramEntry_symm 37 5]
  exact G5_37_formula

theorem G37_5_interval :
    ((((5869769/102310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 5) ∧
    (baezDuarteGramEntry 37 5 ≤ (((5890231/102310000) : ℚ) : ℝ)) := by
  rw [G37_5_formula]
  exact vasyuninBEntry_5_37_eval

def interval_37_5 : NamedVasyuninInterval :=
{
  h := 37
  k := 5
  lower := (5869769/102310000)
  upper := (5890231/102310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_5_interval
}

theorem G37_6_formula : baezDuarteGramEntry 37 6 = vasyuninBEntry 6 37 := by
  rw [baezDuarteGramEntry_symm 37 6]
  exact G6_37_formula

theorem G37_6_interval :
    ((((35934733/652670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 6) ∧
    (baezDuarteGramEntry 37 6 ≤ (((36065267/652670000) : ℚ) : ℝ)) := by
  rw [G37_6_formula]
  exact vasyuninBEntry_6_37_eval

def interval_37_6 : NamedVasyuninInterval :=
{
  h := 37
  k := 6
  lower := (35934733/652670000)
  upper := (36065267/652670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_6_interval
}

theorem G37_7_formula : baezDuarteGramEntry 37 7 = vasyuninBEntry 7 37 := by
  rw [baezDuarteGramEntry_symm 37 7]
  exact G7_37_formula

theorem G37_7_interval :
    ((((48069017/909830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 7) ∧
    (baezDuarteGramEntry 37 7 ≤ (((48250983/909830000) : ℚ) : ℝ)) := by
  rw [G37_7_formula]
  exact vasyuninBEntry_7_37_eval

def interval_37_7 : NamedVasyuninInterval :=
{
  h := 37
  k := 7
  lower := (48069017/909830000)
  upper := (48250983/909830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_7_interval
}

theorem G37_8_formula : baezDuarteGramEntry 37 8 = vasyuninBEntry 8 37 := by
  rw [baezDuarteGramEntry_symm 37 8]
  exact G8_37_formula

theorem G37_8_interval :
    ((((43554487/855130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 8) ∧
    (baezDuarteGramEntry 37 8 ≤ (((43725513/855130000) : ℚ) : ℝ)) := by
  rw [G37_8_formula]
  exact vasyuninBEntry_8_37_eval

def interval_37_8 : NamedVasyuninInterval :=
{
  h := 37
  k := 8
  lower := (43554487/855130000)
  upper := (43725513/855130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_8_interval
}

theorem G37_9_formula : baezDuarteGramEntry 37 9 = vasyuninBEntry 9 37 := by
  rw [baezDuarteGramEntry_symm 37 9]
  exact G9_37_formula

theorem G37_9_interval :
    ((((49260983/990170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 9) ∧
    (baezDuarteGramEntry 37 9 ≤ (((49459017/990170000) : ℚ) : ℝ)) := by
  rw [G37_9_formula]
  exact vasyuninBEntry_9_37_eval

def interval_37_9 : NamedVasyuninInterval :=
{
  h := 37
  k := 9
  lower := (49260983/990170000)
  upper := (49459017/990170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_9_interval
}

theorem G37_10_formula : baezDuarteGramEntry 37 10 = vasyuninBEntry 10 37 := by
  rw [baezDuarteGramEntry_symm 37 10]
  exact G10_37_formula

theorem G37_10_interval :
    ((((6596231/137690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 10) ∧
    (baezDuarteGramEntry 37 10 ≤ (((6623769/137690000) : ℚ) : ℝ)) := by
  rw [G37_10_formula]
  exact vasyuninBEntry_10_37_eval

def interval_37_10 : NamedVasyuninInterval :=
{
  h := 37
  k := 10
  lower := (6596231/137690000)
  upper := (6623769/137690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_10_interval
}

theorem G37_11_formula : baezDuarteGramEntry 37 11 = vasyuninBEntry 11 37 := by
  rw [baezDuarteGramEntry_symm 37 11]
  exact G11_37_formula

theorem G37_11_interval :
    ((((41800289/897110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 11) ∧
    (baezDuarteGramEntry 37 11 ≤ (((41979711/897110000) : ℚ) : ℝ)) := by
  rw [G37_11_formula]
  exact vasyuninBEntry_11_37_eval

def interval_37_11 : NamedVasyuninInterval :=
{
  h := 37
  k := 11
  lower := (41800289/897110000)
  upper := (41979711/897110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_11_interval
}

theorem G37_12_formula : baezDuarteGramEntry 37 12 = vasyuninBEntry 12 37 := by
  rw [baezDuarteGramEntry_symm 37 12]
  exact G12_37_formula

theorem G37_12_interval :
    ((((16623917/360830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 12) ∧
    (baezDuarteGramEntry 37 12 ≤ (((16696083/360830000) : ℚ) : ℝ)) := by
  rw [G37_12_formula]
  exact vasyuninBEntry_12_37_eval

def interval_37_12 : NamedVasyuninInterval :=
{
  h := 37
  k := 12
  lower := (16623917/360830000)
  upper := (16696083/360830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_12_interval
}

theorem G37_13_formula : baezDuarteGramEntry 37 13 = vasyuninBEntry 13 37 := by
  rw [baezDuarteGramEntry_symm 37 13]
  exact G13_37_formula

theorem G37_13_interval :
    ((((21571627/483730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 13) ∧
    (baezDuarteGramEntry 37 13 ≤ (((21668373/483730000) : ℚ) : ℝ)) := by
  rw [G37_13_formula]
  exact vasyuninBEntry_13_37_eval

def interval_37_13 : NamedVasyuninInterval :=
{
  h := 37
  k := 13
  lower := (21571627/483730000)
  upper := (21668373/483730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_13_interval
}

theorem G37_14_formula : baezDuarteGramEntry 37 14 = vasyuninBEntry 14 37 := by
  rw [baezDuarteGramEntry_symm 37 14]
  exact G14_37_formula

theorem G37_14_interval :
    ((((27127231/627690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 14) ∧
    (baezDuarteGramEntry 37 14 ≤ (((27252769/627690000) : ℚ) : ℝ)) := by
  rw [G37_14_formula]
  exact vasyuninBEntry_14_37_eval

def interval_37_14 : NamedVasyuninInterval :=
{
  h := 37
  k := 14
  lower := (27127231/627690000)
  upper := (27252769/627690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_14_interval
}

theorem G37_15_formula : baezDuarteGramEntry 37 15 = vasyuninBEntry 15 37 := by
  rw [baezDuarteGramEntry_symm 37 15]
  exact G15_37_formula

theorem G37_15_interval :
    ((((26716867/631330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 15) ∧
    (baezDuarteGramEntry 37 15 ≤ (((26843133/631330000) : ℚ) : ℝ)) := by
  rw [G37_15_formula]
  exact vasyuninBEntry_15_37_eval

def interval_37_15 : NamedVasyuninInterval :=
{
  h := 37
  k := 15
  lower := (26716867/631330000)
  upper := (26843133/631330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_15_interval
}

theorem G37_16_formula : baezDuarteGramEntry 37 16 = vasyuninBEntry 16 37 := by
  rw [baezDuarteGramEntry_symm 37 16]
  exact G16_37_formula

theorem G37_16_interval :
    ((((11133181/268190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 16) ∧
    (baezDuarteGramEntry 37 16 ≤ (((11186819/268190000) : ℚ) : ℝ)) := by
  rw [G37_16_formula]
  exact vasyuninBEntry_16_37_eval

def interval_37_16 : NamedVasyuninInterval :=
{
  h := 37
  k := 16
  lower := (11133181/268190000)
  upper := (11186819/268190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_16_interval
}

theorem G37_17_formula : baezDuarteGramEntry 37 17 = vasyuninBEntry 17 37 := by
  rw [baezDuarteGramEntry_symm 37 17]
  exact G17_37_formula

theorem G37_17_interval :
    ((((6554027/159730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 17) ∧
    (baezDuarteGramEntry 37 17 ≤ (((6585973/159730000) : ℚ) : ℝ)) := by
  rw [G37_17_formula]
  exact vasyuninBEntry_17_37_eval

def interval_37_17 : NamedVasyuninInterval :=
{
  h := 37
  k := 17
  lower := (6554027/159730000)
  upper := (6585973/159730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_17_interval
}

theorem G37_18_formula : baezDuarteGramEntry 37 18 = vasyuninBEntry 18 37 := by
  rw [baezDuarteGramEntry_symm 37 18]
  exact G18_37_formula

theorem G37_18_interval :
    ((((3880549/94510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 18) ∧
    (baezDuarteGramEntry 37 18 ≤ (((3899451/94510000) : ℚ) : ℝ)) := by
  rw [G37_18_formula]
  exact vasyuninBEntry_18_37_eval

def interval_37_18 : NamedVasyuninInterval :=
{
  h := 37
  k := 18
  lower := (3880549/94510000)
  upper := (3899451/94510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_18_interval
}

theorem G37_19_formula : baezDuarteGramEntry 37 19 = vasyuninBEntry 19 37 := by
  rw [baezDuarteGramEntry_symm 37 19]
  exact G19_37_formula

theorem G37_19_interval :
    ((((7229549/179510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 19) ∧
    (baezDuarteGramEntry 37 19 ≤ (((7265451/179510000) : ℚ) : ℝ)) := by
  rw [G37_19_formula]
  exact vasyuninBEntry_19_37_eval

def interval_37_19 : NamedVasyuninInterval :=
{
  h := 37
  k := 19
  lower := (7229549/179510000)
  upper := (7265451/179510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_19_interval
}

theorem G37_20_formula : baezDuarteGramEntry 37 20 = vasyuninBEntry 20 37 := by
  rw [baezDuarteGramEntry_symm 37 20]
  exact G20_37_formula

theorem G37_20_interval :
    ((((7464737/192630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 20) ∧
    (baezDuarteGramEntry 37 20 ≤ (((7503263/192630000) : ℚ) : ℝ)) := by
  rw [G37_20_formula]
  exact vasyuninBEntry_20_37_eval

def interval_37_20 : NamedVasyuninInterval :=
{
  h := 37
  k := 20
  lower := (7464737/192630000)
  upper := (7503263/192630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_20_interval
}

theorem G37_21_formula : baezDuarteGramEntry 37 21 = vasyuninBEntry 21 37 := by
  rw [baezDuarteGramEntry_symm 37 21]
  exact G21_37_formula

theorem G37_21_interval :
    ((((3353111/88890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 21) ∧
    (baezDuarteGramEntry 37 21 ≤ (((3370889/88890000) : ℚ) : ℝ)) := by
  rw [G37_21_formula]
  exact vasyuninBEntry_21_37_eval

def interval_37_21 : NamedVasyuninInterval :=
{
  h := 37
  k := 21
  lower := (3353111/88890000)
  upper := (3370889/88890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_21_interval
}

theorem G37_22_formula : baezDuarteGramEntry 37 22 = vasyuninBEntry 22 37 := by
  rw [baezDuarteGramEntry_symm 37 22]
  exact G22_37_formula

theorem G37_22_interval :
    ((((15797233/427670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 22) ∧
    (baezDuarteGramEntry 37 22 ≤ (((15882767/427670000) : ℚ) : ℝ)) := by
  rw [G37_22_formula]
  exact vasyuninBEntry_22_37_eval

def interval_37_22 : NamedVasyuninInterval :=
{
  h := 37
  k := 22
  lower := (15797233/427670000)
  upper := (15882767/427670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_22_interval
}

theorem G37_23_formula : baezDuarteGramEntry 37 23 = vasyuninBEntry 23 37 := by
  rw [baezDuarteGramEntry_symm 37 23]
  exact G23_37_formula

theorem G37_23_interval :
    ((((7008161/193390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 23) ∧
    (baezDuarteGramEntry 37 23 ≤ (((7046839/193390000) : ℚ) : ℝ)) := by
  rw [G37_23_formula]
  exact vasyuninBEntry_23_37_eval

def interval_37_23 : NamedVasyuninInterval :=
{
  h := 37
  k := 23
  lower := (7008161/193390000)
  upper := (7046839/193390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_23_interval
}

theorem G37_24_formula : baezDuarteGramEntry 37 24 = vasyuninBEntry 24 37 := by
  rw [baezDuarteGramEntry_symm 37 24]
  exact G24_37_formula

theorem G37_24_interval :
    ((((14419643/403570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 24) ∧
    (baezDuarteGramEntry 37 24 ≤ (((14500357/403570000) : ℚ) : ℝ)) := by
  rw [G37_24_formula]
  exact vasyuninBEntry_24_37_eval

def interval_37_24 : NamedVasyuninInterval :=
{
  h := 37
  k := 24
  lower := (14419643/403570000)
  upper := (14500357/403570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_24_interval
}

end RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
