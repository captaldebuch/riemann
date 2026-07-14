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

namespace RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Certificates.Generated

theorem G42_3_formula : baezDuarteGramEntry 42 3 = vasyuninBEntry 3 42 := by
  rw [baezDuarteGramEntry_symm 42 3]
  exact G3_42_formula

theorem G42_3_interval :
    ((((50034417/855830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 3) ∧
    (baezDuarteGramEntry 42 3 ≤ (((50205583/855830000) : ℚ) : ℝ)) := by
  rw [G42_3_formula]
  exact vasyuninBEntry_3_42_eval

def interval_42_3 : NamedVasyuninInterval :=
{
  h := 42
  k := 3
  lower := (50034417/855830000)
  upper := (50205583/855830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_3_interval
}

theorem G42_4_formula : baezDuarteGramEntry 42 4 = vasyuninBEntry 4 42 := by
  rw [baezDuarteGramEntry_symm 42 4]
  exact G4_42_formula

theorem G42_4_interval :
    ((((18191783/332170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 4) ∧
    (baezDuarteGramEntry 42 4 ≤ (((18258217/332170000) : ℚ) : ℝ)) := by
  rw [G42_4_formula]
  exact vasyuninBEntry_4_42_eval

def interval_42_4 : NamedVasyuninInterval :=
{
  h := 42
  k := 4
  lower := (18191783/332170000)
  upper := (18258217/332170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_4_interval
}

theorem G42_5_formula : baezDuarteGramEntry 42 5 = vasyuninBEntry 5 42 := by
  rw [baezDuarteGramEntry_symm 42 5]
  exact G5_42_formula

theorem G42_5_interval :
    ((((39534049/759510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 5) ∧
    (baezDuarteGramEntry 42 5 ≤ (((39685951/759510000) : ℚ) : ℝ)) := by
  rw [G42_5_formula]
  exact vasyuninBEntry_5_42_eval

def interval_42_5 : NamedVasyuninInterval :=
{
  h := 42
  k := 5
  lower := (39534049/759510000)
  upper := (39685951/759510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_5_interval
}

theorem G42_6_formula : baezDuarteGramEntry 42 6 = vasyuninBEntry 6 42 := by
  rw [baezDuarteGramEntry_symm 42 6]
  exact G6_42_formula

theorem G42_6_interval :
    ((((43453857/861430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 6) ∧
    (baezDuarteGramEntry 42 6 ≤ (((43626143/861430000) : ℚ) : ℝ)) := by
  rw [G42_6_formula]
  exact vasyuninBEntry_6_42_eval

def interval_42_6 : NamedVasyuninInterval :=
{
  h := 42
  k := 6
  lower := (43453857/861430000)
  upper := (43626143/861430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_6_interval
}

theorem G42_7_formula : baezDuarteGramEntry 42 7 = vasyuninBEntry 7 42 := by
  rw [baezDuarteGramEntry_symm 42 7]
  exact G7_42_formula

theorem G42_7_interval :
    ((((2546769/52310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 7) ∧
    (baezDuarteGramEntry 42 7 ≤ (((2557231/52310000) : ℚ) : ℝ)) := by
  rw [G42_7_formula]
  exact vasyuninBEntry_7_42_eval

def interval_42_7 : NamedVasyuninInterval :=
{
  h := 42
  k := 7
  lower := (2546769/52310000)
  upper := (2557231/52310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_7_interval
}

theorem G42_8_formula : baezDuarteGramEntry 42 8 = vasyuninBEntry 8 42 := by
  rw [baezDuarteGramEntry_symm 42 8]
  exact G8_42_formula

theorem G42_8_interval :
    ((((756373/16270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 8) ∧
    (baezDuarteGramEntry 42 8 ≤ (((759627/16270000) : ℚ) : ℝ)) := by
  rw [G42_8_formula]
  exact vasyuninBEntry_8_42_eval

def interval_42_8 : NamedVasyuninInterval :=
{
  h := 42
  k := 8
  lower := (756373/16270000)
  upper := (759627/16270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_8_interval
}

theorem G42_9_formula : baezDuarteGramEntry 42 9 = vasyuninBEntry 9 42 := by
  rw [baezDuarteGramEntry_symm 42 9]
  exact G9_42_formula

theorem G42_9_interval :
    ((((41148581/914190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 9) ∧
    (baezDuarteGramEntry 42 9 ≤ (((41331419/914190000) : ℚ) : ℝ)) := by
  rw [G42_9_formula]
  exact vasyuninBEntry_9_42_eval

def interval_42_9 : NamedVasyuninInterval :=
{
  h := 42
  k := 9
  lower := (41148581/914190000)
  upper := (41331419/914190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_9_interval
}

theorem G42_10_formula : baezDuarteGramEntry 42 10 = vasyuninBEntry 10 42 := by
  rw [baezDuarteGramEntry_symm 42 10]
  exact G10_42_formula

theorem G42_10_interval :
    ((((190441/4340000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 10) ∧
    (baezDuarteGramEntry 42 10 ≤ (((191309/4340000) : ℚ) : ℝ)) := by
  rw [G42_10_formula]
  exact vasyuninBEntry_10_42_eval

def interval_42_10 : NamedVasyuninInterval :=
{
  h := 42
  k := 10
  lower := (190441/4340000)
  upper := (191309/4340000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_10_interval
}

theorem G42_11_formula : baezDuarteGramEntry 42 11 = vasyuninBEntry 11 42 := by
  rw [baezDuarteGramEntry_symm 42 11]
  exact G11_42_formula

theorem G42_11_interval :
    ((((7747863/181370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 11) ∧
    (baezDuarteGramEntry 42 11 ≤ (((7784137/181370000) : ℚ) : ℝ)) := by
  rw [G42_11_formula]
  exact vasyuninBEntry_11_42_eval

def interval_42_11 : NamedVasyuninInterval :=
{
  h := 42
  k := 11
  lower := (7747863/181370000)
  upper := (7784137/181370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_11_interval
}

theorem G42_12_formula : baezDuarteGramEntry 42 12 = vasyuninBEntry 12 42 := by
  rw [baezDuarteGramEntry_symm 42 12]
  exact G12_42_formula

theorem G42_12_interval :
    ((((38088471/915290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 12) ∧
    (baezDuarteGramEntry 42 12 ≤ (((38271529/915290000) : ℚ) : ℝ)) := by
  rw [G42_12_formula]
  exact vasyuninBEntry_12_42_eval

def interval_42_12 : NamedVasyuninInterval :=
{
  h := 42
  k := 12
  lower := (38088471/915290000)
  upper := (38271529/915290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_12_interval
}

theorem G42_13_formula : baezDuarteGramEntry 42 13 = vasyuninBEntry 13 42 := by
  rw [baezDuarteGramEntry_symm 42 13]
  exact G13_42_formula

theorem G42_13_interval :
    ((((4696459/115410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 13) ∧
    (baezDuarteGramEntry 42 13 ≤ (((4719541/115410000) : ℚ) : ℝ)) := by
  rw [G42_13_formula]
  exact vasyuninBEntry_13_42_eval

def interval_42_13 : NamedVasyuninInterval :=
{
  h := 42
  k := 13
  lower := (4696459/115410000)
  upper := (4719541/115410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_13_interval
}

theorem G42_14_formula : baezDuarteGramEntry 42 14 = vasyuninBEntry 14 42 := by
  rw [baezDuarteGramEntry_symm 42 14]
  exact G14_42_formula

theorem G42_14_interval :
    ((((32450797/792030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 14) ∧
    (baezDuarteGramEntry 42 14 ≤ (((32609203/792030000) : ℚ) : ℝ)) := by
  rw [G42_14_formula]
  exact vasyuninBEntry_14_42_eval

def interval_42_14 : NamedVasyuninInterval :=
{
  h := 42
  k := 14
  lower := (32450797/792030000)
  upper := (32609203/792030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_14_interval
}

theorem G42_15_formula : baezDuarteGramEntry 42 15 = vasyuninBEntry 15 42 := by
  rw [baezDuarteGramEntry_symm 42 15]
  exact G15_42_formula

theorem G42_15_interval :
    ((((1280713/32870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 15) ∧
    (baezDuarteGramEntry 42 15 ≤ (((1287287/32870000) : ℚ) : ℝ)) := by
  rw [G42_15_formula]
  exact vasyuninBEntry_15_42_eval

def interval_42_15 : NamedVasyuninInterval :=
{
  h := 42
  k := 15
  lower := (1280713/32870000)
  upper := (1287287/32870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_15_interval
}

theorem G42_16_formula : baezDuarteGramEntry 42 16 = vasyuninBEntry 16 42 := by
  rw [baezDuarteGramEntry_symm 42 16]
  exact G16_42_formula

theorem G42_16_interval :
    ((((16426733/432670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 16) ∧
    (baezDuarteGramEntry 42 16 ≤ (((16513267/432670000) : ℚ) : ℝ)) := by
  rw [G42_16_formula]
  exact vasyuninBEntry_16_42_eval

def interval_42_16 : NamedVasyuninInterval :=
{
  h := 42
  k := 16
  lower := (16426733/432670000)
  upper := (16513267/432670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_16_interval
}

theorem G42_17_formula : baezDuarteGramEntry 42 17 = vasyuninBEntry 17 42 := by
  rw [baezDuarteGramEntry_symm 42 17]
  exact G17_42_formula

theorem G42_17_interval :
    ((((30119241/807590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 17) ∧
    (baezDuarteGramEntry 42 17 ≤ (((30280759/807590000) : ℚ) : ℝ)) := by
  rw [G42_17_formula]
  exact vasyuninBEntry_17_42_eval

def interval_42_17 : NamedVasyuninInterval :=
{
  h := 42
  k := 17
  lower := (30119241/807590000)
  upper := (30280759/807590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_17_interval
}

theorem G42_18_formula : baezDuarteGramEntry 42 18 = vasyuninBEntry 18 42 := by
  rw [baezDuarteGramEntry_symm 42 18]
  exact G18_42_formula

theorem G42_18_interval :
    ((((5816149/158510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 18) ∧
    (baezDuarteGramEntry 42 18 ≤ (((5847851/158510000) : ℚ) : ℝ)) := by
  rw [G42_18_formula]
  exact vasyuninBEntry_18_42_eval

def interval_42_18 : NamedVasyuninInterval :=
{
  h := 42
  k := 18
  lower := (5816149/158510000)
  upper := (5847851/158510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_18_interval
}

theorem G42_19_formula : baezDuarteGramEntry 42 19 = vasyuninBEntry 19 42 := by
  rw [baezDuarteGramEntry_symm 42 19]
  exact G19_42_formula

theorem G42_19_interval :
    ((((24213137/668630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 19) ∧
    (baezDuarteGramEntry 42 19 ≤ (((24346863/668630000) : ℚ) : ℝ)) := by
  rw [G42_19_formula]
  exact vasyuninBEntry_19_42_eval

def interval_42_19 : NamedVasyuninInterval :=
{
  h := 42
  k := 19
  lower := (24213137/668630000)
  upper := (24346863/668630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_19_interval
}

theorem G42_20_formula : baezDuarteGramEntry 42 20 = vasyuninBEntry 20 42 := by
  rw [baezDuarteGramEntry_symm 42 20]
  exact G20_42_formula

theorem G42_20_interval :
    ((((3482347/96530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 20) ∧
    (baezDuarteGramEntry 42 20 ≤ (((3501653/96530000) : ℚ) : ℝ)) := by
  rw [G42_20_formula]
  exact vasyuninBEntry_20_42_eval

def interval_42_20 : NamedVasyuninInterval :=
{
  h := 42
  k := 20
  lower := (3482347/96530000)
  upper := (3501653/96530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_20_interval
}

theorem G42_21_formula : baezDuarteGramEntry 42 21 = vasyuninBEntry 21 42 := by
  rw [baezDuarteGramEntry_symm 42 21]
  exact G21_42_formula

theorem G42_21_interval :
    ((((16185863/441370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 21) ∧
    (baezDuarteGramEntry 42 21 ≤ (((16274137/441370000) : ℚ) : ℝ)) := by
  rw [G42_21_formula]
  exact vasyuninBEntry_21_42_eval

def interval_42_21 : NamedVasyuninInterval :=
{
  h := 42
  k := 21
  lower := (16185863/441370000)
  upper := (16274137/441370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_21_interval
}

theorem G42_22_formula : baezDuarteGramEntry 42 22 = vasyuninBEntry 22 42 := by
  rw [baezDuarteGramEntry_symm 42 22]
  exact G22_42_formula

theorem G42_22_interval :
    ((((27700577/794230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 22) ∧
    (baezDuarteGramEntry 42 22 ≤ (((27859423/794230000) : ℚ) : ℝ)) := by
  rw [G42_22_formula]
  exact vasyuninBEntry_22_42_eval

def interval_42_22 : NamedVasyuninInterval :=
{
  h := 42
  k := 22
  lower := (27700577/794230000)
  upper := (27859423/794230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_22_interval
}

theorem G42_23_formula : baezDuarteGramEntry 42 23 = vasyuninBEntry 23 42 := by
  rw [baezDuarteGramEntry_symm 42 23]
  exact G23_42_formula

theorem G42_23_interval :
    ((((27887639/823610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 23) ∧
    (baezDuarteGramEntry 42 23 ≤ (((28052361/823610000) : ℚ) : ℝ)) := by
  rw [G42_23_formula]
  exact vasyuninBEntry_23_42_eval

def interval_42_23 : NamedVasyuninInterval :=
{
  h := 42
  k := 23
  lower := (27887639/823610000)
  upper := (28052361/823610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_23_interval
}

theorem G42_24_formula : baezDuarteGramEntry 42 24 = vasyuninBEntry 24 42 := by
  rw [baezDuarteGramEntry_symm 42 24]
  exact G24_42_formula

theorem G42_24_interval :
    ((((24635657/743430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 24) ∧
    (baezDuarteGramEntry 42 24 ≤ (((24784343/743430000) : ℚ) : ℝ)) := by
  rw [G42_24_formula]
  exact vasyuninBEntry_24_42_eval

def interval_42_24 : NamedVasyuninInterval :=
{
  h := 42
  k := 24
  lower := (24635657/743430000)
  upper := (24784343/743430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_24_interval
}

theorem G42_25_formula : baezDuarteGramEntry 42 25 = vasyuninBEntry 25 42 := by
  rw [baezDuarteGramEntry_symm 42 25]
  exact G25_42_formula

theorem G42_25_interval :
    ((((12047949/370510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 25) ∧
    (baezDuarteGramEntry 42 25 ≤ (((12122051/370510000) : ℚ) : ℝ)) := by
  rw [G42_25_formula]
  exact vasyuninBEntry_25_42_eval

def interval_42_25 : NamedVasyuninInterval :=
{
  h := 42
  k := 25
  lower := (12047949/370510000)
  upper := (12122051/370510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_25_interval
}

theorem G42_26_formula : baezDuarteGramEntry 42 26 = vasyuninBEntry 26 42 := by
  rw [baezDuarteGramEntry_symm 42 26]
  exact G26_42_formula

theorem G42_26_interval :
    ((((23636051/739490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 26) ∧
    (baezDuarteGramEntry 42 26 ≤ (((23783949/739490000) : ℚ) : ℝ)) := by
  rw [G42_26_formula]
  exact vasyuninBEntry_26_42_eval

def interval_42_26 : NamedVasyuninInterval :=
{
  h := 42
  k := 26
  lower := (23636051/739490000)
  upper := (23783949/739490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_26_interval
}

theorem G42_27_formula : baezDuarteGramEntry 42 27 = vasyuninBEntry 27 42 := by
  rw [baezDuarteGramEntry_symm 42 27]
  exact G27_42_formula

theorem G42_27_interval :
    ((((30822289/977110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 27) ∧
    (baezDuarteGramEntry 42 27 ≤ (((31017711/977110000) : ℚ) : ℝ)) := by
  rw [G42_27_formula]
  exact vasyuninBEntry_27_42_eval

def interval_42_27 : NamedVasyuninInterval :=
{
  h := 42
  k := 27
  lower := (30822289/977110000)
  upper := (31017711/977110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_27_interval
}

theorem G42_28_formula : baezDuarteGramEntry 42 28 = vasyuninBEntry 28 42 := by
  rw [baezDuarteGramEntry_symm 42 28]
  exact G28_42_formula

theorem G42_28_interval :
    ((((29246879/931210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 28) ∧
    (baezDuarteGramEntry 42 28 ≤ (((29433121/931210000) : ℚ) : ℝ)) := by
  rw [G42_28_formula]
  exact vasyuninBEntry_28_42_eval

def interval_42_28 : NamedVasyuninInterval :=
{
  h := 42
  k := 28
  lower := (29246879/931210000)
  upper := (29433121/931210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_28_interval
}

theorem G42_29_formula : baezDuarteGramEntry 42 29 = vasyuninBEntry 29 42 := by
  rw [baezDuarteGramEntry_symm 42 29]
  exact G29_42_formula

theorem G42_29_interval :
    ((((1621721/52790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 29) ∧
    (baezDuarteGramEntry 42 29 ≤ (((1632279/52790000) : ℚ) : ℝ)) := by
  rw [G42_29_formula]
  exact vasyuninBEntry_29_42_eval

def interval_42_29 : NamedVasyuninInterval :=
{
  h := 42
  k := 29
  lower := (1621721/52790000)
  upper := (1632279/52790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_29_interval
}

theorem G42_30_formula : baezDuarteGramEntry 42 30 = vasyuninBEntry 30 42 := by
  rw [baezDuarteGramEntry_symm 42 30]
  exact G30_42_formula

theorem G42_30_interval :
    ((((6040087/199130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 30) ∧
    (baezDuarteGramEntry 42 30 ≤ (((6079913/199130000) : ℚ) : ℝ)) := by
  rw [G42_30_formula]
  exact vasyuninBEntry_30_42_eval

def interval_42_30 : NamedVasyuninInterval :=
{
  h := 42
  k := 30
  lower := (6040087/199130000)
  upper := (6079913/199130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_30_interval
}

theorem G42_31_formula : baezDuarteGramEntry 42 31 = vasyuninBEntry 31 42 := by
  rw [baezDuarteGramEntry_symm 42 31]
  exact G31_42_formula

theorem G42_31_interval :
    ((((3984717/132830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 31) ∧
    (baezDuarteGramEntry 42 31 ≤ (((4011283/132830000) : ℚ) : ℝ)) := by
  rw [G42_31_formula]
  exact vasyuninBEntry_31_42_eval

def interval_42_31 : NamedVasyuninInterval :=
{
  h := 42
  k := 31
  lower := (3984717/132830000)
  upper := (4011283/132830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_31_interval
}

theorem G42_32_formula : baezDuarteGramEntry 42 32 = vasyuninBEntry 32 42 := by
  rw [baezDuarteGramEntry_symm 42 32]
  exact G32_42_formula

theorem G42_32_interval :
    ((((391339/13172500) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 32) ∧
    (baezDuarteGramEntry 42 32 ≤ (((787947/26345000) : ℚ) : ℝ)) := by
  rw [G42_32_formula]
  exact vasyuninBEntry_32_42_eval

def interval_42_32 : NamedVasyuninInterval :=
{
  h := 42
  k := 32
  lower := (391339/13172500)
  upper := (787947/26345000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_32_interval
}

theorem G42_33_formula : baezDuarteGramEntry 42 33 = vasyuninBEntry 33 42 := by
  rw [baezDuarteGramEntry_symm 42 33]
  exact G33_42_formula

theorem G42_33_interval :
    ((((17331121/588790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 33) ∧
    (baezDuarteGramEntry 42 33 ≤ (((17448879/588790000) : ℚ) : ℝ)) := by
  rw [G42_33_formula]
  exact vasyuninBEntry_33_42_eval

def interval_42_33 : NamedVasyuninInterval :=
{
  h := 42
  k := 33
  lower := (17331121/588790000)
  upper := (17448879/588790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_33_interval
}

theorem G42_34_formula : baezDuarteGramEntry 42 34 = vasyuninBEntry 34 42 := by
  rw [baezDuarteGramEntry_symm 42 34]
  exact G34_42_formula

theorem G42_34_interval :
    ((((17370559/594410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 34) ∧
    (baezDuarteGramEntry 42 34 ≤ (((17489441/594410000) : ℚ) : ℝ)) := by
  rw [G42_34_formula]
  exact vasyuninBEntry_34_42_eval

def interval_42_34 : NamedVasyuninInterval :=
{
  h := 42
  k := 34
  lower := (17370559/594410000)
  upper := (17489441/594410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_34_interval
}

theorem G42_35_formula : baezDuarteGramEntry 42 35 = vasyuninBEntry 35 42 := by
  rw [baezDuarteGramEntry_symm 42 35]
  exact G35_42_formula

theorem G42_35_interval :
    ((((4982859/171410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 35) ∧
    (baezDuarteGramEntry 42 35 ≤ (((5017141/171410000) : ℚ) : ℝ)) := by
  rw [G42_35_formula]
  exact vasyuninBEntry_35_42_eval

def interval_42_35 : NamedVasyuninInterval :=
{
  h := 42
  k := 35
  lower := (4982859/171410000)
  upper := (5017141/171410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_35_interval
}

theorem G42_36_formula : baezDuarteGramEntry 42 36 = vasyuninBEntry 36 42 := by
  rw [baezDuarteGramEntry_symm 42 36]
  exact G36_42_formula

theorem G42_36_interval :
    ((((25342399/876010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 36) ∧
    (baezDuarteGramEntry 42 36 ≤ (((25517601/876010000) : ℚ) : ℝ)) := by
  rw [G42_36_formula]
  exact vasyuninBEntry_36_42_eval

def interval_42_36 : NamedVasyuninInterval :=
{
  h := 42
  k := 36
  lower := (25342399/876010000)
  upper := (25517601/876010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_36_interval
}

theorem G42_37_formula : baezDuarteGramEntry 42 37 = vasyuninBEntry 37 42 := by
  rw [baezDuarteGramEntry_symm 42 37]
  exact G37_42_formula

theorem G42_37_interval :
    ((((5550749/192510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 37) ∧
    (baezDuarteGramEntry 42 37 ≤ (((5589251/192510000) : ℚ) : ℝ)) := by
  rw [G42_37_formula]
  exact vasyuninBEntry_37_42_eval

def interval_42_37 : NamedVasyuninInterval :=
{
  h := 42
  k := 37
  lower := (5550749/192510000)
  upper := (5589251/192510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_37_interval
}

theorem G42_38_formula : baezDuarteGramEntry 42 38 = vasyuninBEntry 38 42 := by
  rw [baezDuarteGramEntry_symm 42 38]
  exact G38_42_formula

theorem G42_38_interval :
    ((((27046127/938730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 38) ∧
    (baezDuarteGramEntry 42 38 ≤ (((27233873/938730000) : ℚ) : ℝ)) := by
  rw [G42_38_formula]
  exact vasyuninBEntry_38_42_eval

def interval_42_38 : NamedVasyuninInterval :=
{
  h := 42
  k := 38
  lower := (27046127/938730000)
  upper := (27233873/938730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_38_interval
}

theorem G42_39_formula : baezDuarteGramEntry 42 39 = vasyuninBEntry 39 42 := by
  rw [baezDuarteGramEntry_symm 42 39]
  exact G39_42_formula

theorem G42_39_interval :
    ((((26876869/931310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 39) ∧
    (baezDuarteGramEntry 42 39 ≤ (((27063131/931310000) : ℚ) : ℝ)) := by
  rw [G42_39_formula]
  exact vasyuninBEntry_39_42_eval

def interval_42_39 : NamedVasyuninInterval :=
{
  h := 42
  k := 39
  lower := (26876869/931310000)
  upper := (27063131/931310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_39_interval
}

theorem G42_40_formula : baezDuarteGramEntry 42 40 = vasyuninBEntry 40 42 := by
  rw [baezDuarteGramEntry_symm 42 40]
  exact G40_42_formula

theorem G42_40_interval :
    ((((16817/580000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 40) ∧
    (baezDuarteGramEntry 42 40 ≤ (((16933/580000) : ℚ) : ℝ)) := by
  rw [G42_40_formula]
  exact vasyuninBEntry_40_42_eval

def interval_42_40 : NamedVasyuninInterval :=
{
  h := 42
  k := 40
  lower := (16817/580000)
  upper := (16933/580000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_40_interval
}

theorem G42_41_formula : baezDuarteGramEntry 42 41 = vasyuninBEntry 41 42 := by
  rw [baezDuarteGramEntry_symm 42 41]
  exact G41_42_formula

theorem G42_41_interval :
    ((((2251059/76910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 41) ∧
    (baezDuarteGramEntry 42 41 ≤ (((2266441/76910000) : ℚ) : ℝ)) := by
  rw [G42_41_formula]
  exact vasyuninBEntry_41_42_eval

def interval_42_41 : NamedVasyuninInterval :=
{
  h := 42
  k := 41
  lower := (2251059/76910000)
  upper := (2266441/76910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_41_interval
}

theorem G42_42_formula_eq : baezDuarteGramEntry 42 42 = (1 / (42 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 42 := by norm_num
  rw [baez_duarte_diagonal_scaling 42 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G42_42_log_gamma_interval :
  ((((28305383/946170000) : ℚ) : ℝ) ≤ (1 / (42 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (42 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((28494617/946170000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 42 (by norm_num)
  constructor
  · have : ((((28305383/946170000) : ℚ) : ℝ) ≤ (1 / (42 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (42 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((28494617/946170000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G42_42_interval : ((((28305383/946170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 42) ∧ (baezDuarteGramEntry 42 42 ≤ (((28494617/946170000) : ℚ) : ℝ)) := by
  rw [G42_42_formula_eq]
  exact G42_42_log_gamma_interval

def interval_42_42 : NamedVasyuninInterval :=
{
  h := 42
  k := 42
  lower := (28305383/946170000)
  upper := (28494617/946170000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G42_42_interval
}

theorem G42_43_formula : baezDuarteGramEntry 42 43 = vasyuninBEntry 42 43 := vasyuninBEntry_correct_axiom 42 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_42_43_eval :
    ((((26317961/920390000) : ℚ) : ℝ) ≤ vasyuninBEntry 42 43) ∧
    (vasyuninBEntry 42 43 ≤ (((26502039/920390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4243_formula_bound
  constructor <;> linarith

theorem G42_43_interval :
    ((((26317961/920390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 43) ∧
    (baezDuarteGramEntry 42 43 ≤ (((26502039/920390000) : ℚ) : ℝ)) := by
  rw [G42_43_formula]
  exact vasyuninBEntry_42_43_eval

def interval_42_43 : NamedVasyuninInterval :=
{
  h := 42
  k := 43
  lower := (26317961/920390000)
  upper := (26502039/920390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_43_interval
}

theorem G42_44_formula : baezDuarteGramEntry 42 44 = vasyuninBEntry 42 44 := vasyuninBEntry_correct_axiom 42 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_42_44_eval :
    ((((3248269/117310000) : ℚ) : ℝ) ≤ vasyuninBEntry 42 44) ∧
    (vasyuninBEntry 42 44 ≤ (((3271731/117310000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_21_22_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 21 22 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G42_44_interval :
    ((((3248269/117310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 44) ∧
    (baezDuarteGramEntry 42 44 ≤ (((3271731/117310000) : ℚ) : ℝ)) := by
  rw [G42_44_formula]
  exact vasyuninBEntry_42_44_eval

def interval_42_44 : NamedVasyuninInterval :=
{
  h := 42
  k := 44
  lower := (3248269/117310000)
  upper := (3271731/117310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_44_interval
}

theorem G42_45_formula : baezDuarteGramEntry 42 45 = vasyuninBEntry 42 45 := vasyuninBEntry_correct_axiom 42 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_42_45_eval :
    ((((16339363/606370000) : ℚ) : ℝ) ≤ vasyuninBEntry 42 45) ∧
    (vasyuninBEntry 42 45 ≤ (((16460637/606370000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_14_15_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 14 15 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G42_45_interval :
    ((((16339363/606370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 45) ∧
    (baezDuarteGramEntry 42 45 ≤ (((16460637/606370000) : ℚ) : ℝ)) := by
  rw [G42_45_formula]
  exact vasyuninBEntry_42_45_eval

def interval_42_45 : NamedVasyuninInterval :=
{
  h := 42
  k := 45
  lower := (16339363/606370000)
  upper := (16460637/606370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_45_interval
}

theorem G42_46_formula : baezDuarteGramEntry 42 46 = vasyuninBEntry 42 46 := vasyuninBEntry_correct_axiom 42 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_42_46_eval :
    ((((25303803/961970000) : ℚ) : ℝ) ≤ vasyuninBEntry 42 46) ∧
    (vasyuninBEntry 42 46 ≤ (((25496197/961970000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_21_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 21 23 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G42_46_interval :
    ((((25303803/961970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 46) ∧
    (baezDuarteGramEntry 42 46 ≤ (((25496197/961970000) : ℚ) : ℝ)) := by
  rw [G42_46_formula]
  exact vasyuninBEntry_42_46_eval

def interval_42_46 : NamedVasyuninInterval :=
{
  h := 42
  k := 46
  lower := (25303803/961970000)
  upper := (25496197/961970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_46_interval
}

theorem G42_47_formula : baezDuarteGramEntry 42 47 = vasyuninBEntry 42 47 := vasyuninBEntry_correct_axiom 42 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_42_47_eval :
    ((((4861113/188870000) : ℚ) : ℝ) ≤ vasyuninBEntry 42 47) ∧
    (vasyuninBEntry 42 47 ≤ (((4898887/188870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4247_formula_bound
  constructor <;> linarith

theorem G42_47_interval :
    ((((4861113/188870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 47) ∧
    (baezDuarteGramEntry 42 47 ≤ (((4898887/188870000) : ℚ) : ℝ)) := by
  rw [G42_47_formula]
  exact vasyuninBEntry_42_47_eval

def interval_42_47 : NamedVasyuninInterval :=
{
  h := 42
  k := 47
  lower := (4861113/188870000)
  upper := (4898887/188870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_47_interval
}

theorem G42_48_formula : baezDuarteGramEntry 42 48 = vasyuninBEntry 42 48 := vasyuninBEntry_correct_axiom 42 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_42_48_eval :
    ((((9661719/382810000) : ℚ) : ℝ) ≤ vasyuninBEntry 42 48) ∧
    (vasyuninBEntry 42 48 ≤ (((9738281/382810000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 8 6 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G42_48_interval :
    ((((9661719/382810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 48) ∧
    (baezDuarteGramEntry 42 48 ≤ (((9738281/382810000) : ℚ) : ℝ)) := by
  rw [G42_48_formula]
  exact vasyuninBEntry_42_48_eval

def interval_42_48 : NamedVasyuninInterval :=
{
  h := 42
  k := 48
  lower := (9661719/382810000)
  upper := (9738281/382810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_48_interval
}

theorem G42_49_formula : baezDuarteGramEntry 42 49 = vasyuninBEntry 42 49 := vasyuninBEntry_correct_axiom 42 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_42_49_eval :
    ((((11633059/469410000) : ℚ) : ℝ) ≤ vasyuninBEntry 42 49) ∧
    (vasyuninBEntry 42 49 ≤ (((11726941/469410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_6_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 6 7 7 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 7)
  constructor <;> linarith

theorem G42_49_interval :
    ((((11633059/469410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 49) ∧
    (baezDuarteGramEntry 42 49 ≤ (((11726941/469410000) : ℚ) : ℝ)) := by
  rw [G42_49_formula]
  exact vasyuninBEntry_42_49_eval

def interval_42_49 : NamedVasyuninInterval :=
{
  h := 42
  k := 49
  lower := (11633059/469410000)
  upper := (11726941/469410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_49_interval
}

theorem G42_50_formula : baezDuarteGramEntry 42 50 = vasyuninBEntry 42 50 := vasyuninBEntry_correct_axiom 42 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_42_50_eval :
    ((((23503469/965310000) : ℚ) : ℝ) ≤ vasyuninBEntry 42 50) ∧
    (vasyuninBEntry 42 50 ≤ (((23696531/965310000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_21_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 21 25 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G42_50_interval :
    ((((23503469/965310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 50) ∧
    (baezDuarteGramEntry 42 50 ≤ (((23696531/965310000) : ℚ) : ℝ)) := by
  rw [G42_50_formula]
  exact vasyuninBEntry_42_50_eval

def interval_42_50 : NamedVasyuninInterval :=
{
  h := 42
  k := 50
  lower := (23503469/965310000)
  upper := (23696531/965310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_50_interval
}

theorem G43_1_formula : baezDuarteGramEntry 43 1 = vasyuninBEntry 1 43 := by
  rw [baezDuarteGramEntry_symm 43 1]
  exact G1_43_formula

theorem G43_1_interval :
    ((((60583447/865530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 1) ∧
    (baezDuarteGramEntry 43 1 ≤ (((60756553/865530000) : ℚ) : ℝ)) := by
  rw [G43_1_formula]
  exact vasyuninBEntry_1_43_eval

def interval_43_1 : NamedVasyuninInterval :=
{
  h := 43
  k := 1
  lower := (60583447/865530000)
  upper := (60756553/865530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_1_interval
}

theorem G43_2_formula : baezDuarteGramEntry 43 2 = vasyuninBEntry 2 43 := by
  rw [baezDuarteGramEntry_symm 43 2]
  exact G2_43_formula

theorem G43_2_interval :
    ((((8678467/140330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 2) ∧
    (baezDuarteGramEntry 43 2 ≤ (((8706533/140330000) : ℚ) : ℝ)) := by
  rw [G43_2_formula]
  exact vasyuninBEntry_2_43_eval

def interval_43_2 : NamedVasyuninInterval :=
{
  h := 43
  k := 2
  lower := (8678467/140330000)
  upper := (8706533/140330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_2_interval
}

theorem G43_3_formula : baezDuarteGramEntry 43 3 = vasyuninBEntry 3 43 := by
  rw [baezDuarteGramEntry_symm 43 3]
  exact G3_43_formula

theorem G43_3_interval :
    ((((17634121/308790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 3) ∧
    (baezDuarteGramEntry 43 3 ≤ (((17695879/308790000) : ℚ) : ℝ)) := by
  rw [G43_3_formula]
  exact vasyuninBEntry_3_43_eval

def interval_43_3 : NamedVasyuninInterval :=
{
  h := 43
  k := 3
  lower := (17634121/308790000)
  upper := (17695879/308790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_3_interval
}

theorem G43_4_formula : baezDuarteGramEntry 43 4 = vasyuninBEntry 4 43 := by
  rw [baezDuarteGramEntry_symm 43 4]
  exact G4_43_formula

theorem G43_4_interval :
    ((((41882097/779030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 4) ∧
    (baezDuarteGramEntry 43 4 ≤ (((42037903/779030000) : ℚ) : ℝ)) := by
  rw [G43_4_formula]
  exact vasyuninBEntry_4_43_eval

def interval_43_4 : NamedVasyuninInterval :=
{
  h := 43
  k := 4
  lower := (41882097/779030000)
  upper := (42037903/779030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_4_interval
}

theorem G43_5_formula : baezDuarteGramEntry 43 5 = vasyuninBEntry 5 43 := by
  rw [baezDuarteGramEntry_symm 43 5]
  exact G5_43_formula

theorem G43_5_interval :
    ((((29103059/569410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 5) ∧
    (baezDuarteGramEntry 43 5 ≤ (((29216941/569410000) : ℚ) : ℝ)) := by
  rw [G43_5_formula]
  exact vasyuninBEntry_5_43_eval

def interval_43_5 : NamedVasyuninInterval :=
{
  h := 43
  k := 5
  lower := (29103059/569410000)
  upper := (29216941/569410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_5_interval
}

theorem G43_6_formula : baezDuarteGramEntry 43 6 = vasyuninBEntry 6 43 := by
  rw [baezDuarteGramEntry_symm 43 6]
  exact G6_43_formula

theorem G43_6_interval :
    ((((41345801/841990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 6) ∧
    (baezDuarteGramEntry 43 6 ≤ (((41514199/841990000) : ℚ) : ℝ)) := by
  rw [G43_6_formula]
  exact vasyuninBEntry_6_43_eval

def interval_43_6 : NamedVasyuninInterval :=
{
  h := 43
  k := 6
  lower := (41345801/841990000)
  upper := (41514199/841990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_6_interval
}

theorem G43_7_formula : baezDuarteGramEntry 43 7 = vasyuninBEntry 7 43 := by
  rw [baezDuarteGramEntry_symm 43 7]
  exact G7_43_formula

theorem G43_7_interval :
    ((((20117513/424870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 7) ∧
    (baezDuarteGramEntry 43 7 ≤ (((20202487/424870000) : ℚ) : ℝ)) := by
  rw [G43_7_formula]
  exact vasyuninBEntry_7_43_eval

def interval_43_7 : NamedVasyuninInterval :=
{
  h := 43
  k := 7
  lower := (20117513/424870000)
  upper := (20202487/424870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_7_interval
}

theorem G43_8_formula : baezDuarteGramEntry 43 8 = vasyuninBEntry 8 43 := by
  rw [baezDuarteGramEntry_symm 43 8]
  exact G8_43_formula

theorem G43_8_interval :
    ((((44672033/979670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 8) ∧
    (baezDuarteGramEntry 43 8 ≤ (((44867967/979670000) : ℚ) : ℝ)) := by
  rw [G43_8_formula]
  exact vasyuninBEntry_8_43_eval

def interval_43_8 : NamedVasyuninInterval :=
{
  h := 43
  k := 8
  lower := (44672033/979670000)
  upper := (44867967/979670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_8_interval
}

theorem G43_9_formula : baezDuarteGramEntry 43 9 = vasyuninBEntry 9 43 := by
  rw [baezDuarteGramEntry_symm 43 9]
  exact G9_43_formula

theorem G43_9_interval :
    ((((1448729/32710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 9) ∧
    (baezDuarteGramEntry 43 9 ≤ (((1455271/32710000) : ℚ) : ℝ)) := by
  rw [G43_9_formula]
  exact vasyuninBEntry_9_43_eval

def interval_43_9 : NamedVasyuninInterval :=
{
  h := 43
  k := 9
  lower := (1448729/32710000)
  upper := (1455271/32710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_9_interval
}

theorem G43_10_formula : baezDuarteGramEntry 43 10 = vasyuninBEntry 10 43 := by
  rw [baezDuarteGramEntry_symm 43 10]
  exact G10_43_formula

theorem G43_10_interval :
    ((((36375437/845630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 10) ∧
    (baezDuarteGramEntry 43 10 ≤ (((36544563/845630000) : ℚ) : ℝ)) := by
  rw [G43_10_formula]
  exact vasyuninBEntry_10_43_eval

def interval_43_10 : NamedVasyuninInterval :=
{
  h := 43
  k := 10
  lower := (36375437/845630000)
  upper := (36544563/845630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_10_interval
}

theorem G43_11_formula : baezDuarteGramEntry 43 11 = vasyuninBEntry 11 43 := by
  rw [baezDuarteGramEntry_symm 43 11]
  exact G11_43_formula

theorem G43_11_interval :
    ((((13847219/327810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 11) ∧
    (baezDuarteGramEntry 43 11 ≤ (((13912781/327810000) : ℚ) : ℝ)) := by
  rw [G43_11_formula]
  exact vasyuninBEntry_11_43_eval

def interval_43_11 : NamedVasyuninInterval :=
{
  h := 43
  k := 11
  lower := (13847219/327810000)
  upper := (13912781/327810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_11_interval
}

theorem G43_12_formula : baezDuarteGramEntry 43 12 = vasyuninBEntry 12 43 := by
  rw [baezDuarteGramEntry_symm 43 12]
  exact G12_43_formula

theorem G43_12_interval :
    ((((7595377/186230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 12) ∧
    (baezDuarteGramEntry 43 12 ≤ (((7632623/186230000) : ℚ) : ℝ)) := by
  rw [G43_12_formula]
  exact vasyuninBEntry_12_43_eval

def interval_43_12 : NamedVasyuninInterval :=
{
  h := 43
  k := 12
  lower := (7595377/186230000)
  upper := (7632623/186230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_12_interval
}

theorem G43_13_formula : baezDuarteGramEntry 43 13 = vasyuninBEntry 13 43 := by
  rw [baezDuarteGramEntry_symm 43 13]
  exact G13_43_formula

theorem G43_13_interval :
    ((((3418937/85630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 13) ∧
    (baezDuarteGramEntry 43 13 ≤ (((3436063/85630000) : ℚ) : ℝ)) := by
  rw [G43_13_formula]
  exact vasyuninBEntry_13_43_eval

def interval_43_13 : NamedVasyuninInterval :=
{
  h := 43
  k := 13
  lower := (3418937/85630000)
  upper := (3436063/85630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_13_interval
}

theorem G43_14_formula : baezDuarteGramEntry 43 14 = vasyuninBEntry 14 43 := by
  rw [baezDuarteGramEntry_symm 43 14]
  exact G14_43_formula

theorem G43_14_interval :
    ((((17535767/442330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 14) ∧
    (baezDuarteGramEntry 43 14 ≤ (((17624233/442330000) : ℚ) : ℝ)) := by
  rw [G43_14_formula]
  exact vasyuninBEntry_14_43_eval

def interval_43_14 : NamedVasyuninInterval :=
{
  h := 43
  k := 14
  lower := (17535767/442330000)
  upper := (17624233/442330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_14_interval
}

theorem G43_15_formula : baezDuarteGramEntry 43 15 = vasyuninBEntry 15 43 := by
  rw [baezDuarteGramEntry_symm 43 15]
  exact G15_43_formula

theorem G43_15_interval :
    ((((18362319/476810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 15) ∧
    (baezDuarteGramEntry 43 15 ≤ (((18457681/476810000) : ℚ) : ℝ)) := by
  rw [G43_15_formula]
  exact vasyuninBEntry_15_43_eval

def interval_43_15 : NamedVasyuninInterval :=
{
  h := 43
  k := 15
  lower := (18362319/476810000)
  upper := (18457681/476810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_15_interval
}

theorem G43_16_formula : baezDuarteGramEntry 43 16 = vasyuninBEntry 16 43 := by
  rw [baezDuarteGramEntry_symm 43 16]
  exact G16_43_formula

theorem G43_16_interval :
    ((((1055179/28210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 16) ∧
    (baezDuarteGramEntry 43 16 ≤ (((1060821/28210000) : ℚ) : ℝ)) := by
  rw [G43_16_formula]
  exact vasyuninBEntry_16_43_eval

def interval_43_16 : NamedVasyuninInterval :=
{
  h := 43
  k := 16
  lower := (1055179/28210000)
  upper := (1060821/28210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_16_interval
}

theorem G43_17_formula : baezDuarteGramEntry 43 17 = vasyuninBEntry 17 43 := by
  rw [baezDuarteGramEntry_symm 43 17]
  exact G17_43_formula

theorem G43_17_interval :
    ((((27664609/753910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 17) ∧
    (baezDuarteGramEntry 43 17 ≤ (((27815391/753910000) : ℚ) : ℝ)) := by
  rw [G43_17_formula]
  exact vasyuninBEntry_17_43_eval

def interval_43_17 : NamedVasyuninInterval :=
{
  h := 43
  k := 17
  lower := (27664609/753910000)
  upper := (27815391/753910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_17_interval
}

theorem G43_18_formula : baezDuarteGramEntry 43 18 = vasyuninBEntry 18 43 := by
  rw [baezDuarteGramEntry_symm 43 18]
  exact G18_43_formula

theorem G43_18_interval :
    ((((19595569/544310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 18) ∧
    (baezDuarteGramEntry 43 18 ≤ (((19704431/544310000) : ℚ) : ℝ)) := by
  rw [G43_18_formula]
  exact vasyuninBEntry_18_43_eval

def interval_43_18 : NamedVasyuninInterval :=
{
  h := 43
  k := 18
  lower := (19595569/544310000)
  upper := (19704431/544310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_18_interval
}

theorem G43_19_formula : baezDuarteGramEntry 43 19 = vasyuninBEntry 19 43 := by
  rw [baezDuarteGramEntry_symm 43 19]
  exact G19_43_formula

theorem G43_19_interval :
    ((((17121803/481970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 19) ∧
    (baezDuarteGramEntry 43 19 ≤ (((17218197/481970000) : ℚ) : ℝ)) := by
  rw [G43_19_formula]
  exact vasyuninBEntry_19_43_eval

def interval_43_19 : NamedVasyuninInterval :=
{
  h := 43
  k := 19
  lower := (17121803/481970000)
  upper := (17218197/481970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_19_interval
}

theorem G43_20_formula : baezDuarteGramEntry 43 20 = vasyuninBEntry 20 43 := by
  rw [baezDuarteGramEntry_symm 43 20]
  exact G20_43_formula

theorem G43_20_interval :
    ((((867539/24610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 20) ∧
    (baezDuarteGramEntry 43 20 ≤ (((872461/24610000) : ℚ) : ℝ)) := by
  rw [G43_20_formula]
  exact vasyuninBEntry_20_43_eval

def interval_43_20 : NamedVasyuninInterval :=
{
  h := 43
  k := 20
  lower := (867539/24610000)
  upper := (872461/24610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_20_interval
}

theorem G43_21_formula : baezDuarteGramEntry 43 21 = vasyuninBEntry 21 43 := by
  rw [baezDuarteGramEntry_symm 43 21]
  exact G21_43_formula

theorem G43_21_interval :
    ((((13950533/394670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 21) ∧
    (baezDuarteGramEntry 43 21 ≤ (((14029467/394670000) : ℚ) : ℝ)) := by
  rw [G43_21_formula]
  exact vasyuninBEntry_21_43_eval

def interval_43_21 : NamedVasyuninInterval :=
{
  h := 43
  k := 21
  lower := (13950533/394670000)
  upper := (14029467/394670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_21_interval
}

theorem G43_22_formula : baezDuarteGramEntry 43 22 = vasyuninBEntry 22 43 := by
  rw [baezDuarteGramEntry_symm 43 22]
  exact G22_43_formula

theorem G43_22_interval :
    ((((5538069/159310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 22) ∧
    (baezDuarteGramEntry 43 22 ≤ (((5569931/159310000) : ℚ) : ℝ)) := by
  rw [G43_22_formula]
  exact vasyuninBEntry_22_43_eval

def interval_43_22 : NamedVasyuninInterval :=
{
  h := 43
  k := 22
  lower := (5538069/159310000)
  upper := (5569931/159310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_22_interval
}

theorem G43_23_formula : baezDuarteGramEntry 43 23 = vasyuninBEntry 23 43 := by
  rw [baezDuarteGramEntry_symm 43 23]
  exact G23_43_formula

theorem G43_23_interval :
    ((((17517797/522030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 23) ∧
    (baezDuarteGramEntry 43 23 ≤ (((17622203/522030000) : ℚ) : ℝ)) := by
  rw [G43_23_formula]
  exact vasyuninBEntry_23_43_eval

def interval_43_23 : NamedVasyuninInterval :=
{
  h := 43
  k := 23
  lower := (17517797/522030000)
  upper := (17622203/522030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_23_interval
}

theorem G43_24_formula : baezDuarteGramEntry 43 24 = vasyuninBEntry 24 43 := by
  rw [baezDuarteGramEntry_symm 43 24]
  exact G24_43_formula

theorem G43_24_interval :
    ((((22710597/694030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 24) ∧
    (baezDuarteGramEntry 43 24 ≤ (((22849403/694030000) : ℚ) : ℝ)) := by
  rw [G43_24_formula]
  exact vasyuninBEntry_24_43_eval

def interval_43_24 : NamedVasyuninInterval :=
{
  h := 43
  k := 24
  lower := (22710597/694030000)
  upper := (22849403/694030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_24_interval
}

theorem G43_25_formula : baezDuarteGramEntry 43 25 = vasyuninBEntry 25 43 := by
  rw [baezDuarteGramEntry_symm 43 25]
  exact G25_43_formula

theorem G43_25_interval :
    ((((23257467/725330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 25) ∧
    (baezDuarteGramEntry 43 25 ≤ (((23402533/725330000) : ℚ) : ℝ)) := by
  rw [G43_25_formula]
  exact vasyuninBEntry_25_43_eval

def interval_43_25 : NamedVasyuninInterval :=
{
  h := 43
  k := 25
  lower := (23257467/725330000)
  upper := (23402533/725330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_25_interval
}

theorem G43_26_formula : baezDuarteGramEntry 43 26 = vasyuninBEntry 26 43 := by
  rw [baezDuarteGramEntry_symm 43 26]
  exact G26_43_formula

theorem G43_26_interval :
    ((((570691/18090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 26) ∧
    (baezDuarteGramEntry 43 26 ≤ (((574309/18090000) : ℚ) : ℝ)) := by
  rw [G43_26_formula]
  exact vasyuninBEntry_26_43_eval

def interval_43_26 : NamedVasyuninInterval :=
{
  h := 43
  k := 26
  lower := (570691/18090000)
  upper := (574309/18090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_26_interval
}

theorem G43_27_formula : baezDuarteGramEntry 43 27 = vasyuninBEntry 27 43 := by
  rw [baezDuarteGramEntry_symm 43 27]
  exact G27_43_formula

theorem G43_27_interval :
    ((((13451679/433210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 27) ∧
    (baezDuarteGramEntry 43 27 ≤ (((13538321/433210000) : ℚ) : ℝ)) := by
  rw [G43_27_formula]
  exact vasyuninBEntry_27_43_eval

def interval_43_27 : NamedVasyuninInterval :=
{
  h := 43
  k := 27
  lower := (13451679/433210000)
  upper := (13538321/433210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_27_interval
}

theorem G43_28_formula : baezDuarteGramEntry 43 28 = vasyuninBEntry 28 43 := by
  rw [baezDuarteGramEntry_symm 43 28]
  exact G28_43_formula

theorem G43_28_interval :
    ((((10924419/355810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 28) ∧
    (baezDuarteGramEntry 43 28 ≤ (((10995581/355810000) : ℚ) : ℝ)) := by
  rw [G43_28_formula]
  exact vasyuninBEntry_28_43_eval

def interval_43_28 : NamedVasyuninInterval :=
{
  h := 43
  k := 28
  lower := (10924419/355810000)
  upper := (10995581/355810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_28_interval
}

theorem G43_29_formula : baezDuarteGramEntry 43 29 = vasyuninBEntry 29 43 := by
  rw [baezDuarteGramEntry_symm 43 29]
  exact G29_43_formula

theorem G43_29_interval :
    ((((5344907/175930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 29) ∧
    (baezDuarteGramEntry 43 29 ≤ (((5380093/175930000) : ℚ) : ℝ)) := by
  rw [G43_29_formula]
  exact vasyuninBEntry_29_43_eval

def interval_43_29 : NamedVasyuninInterval :=
{
  h := 43
  k := 29
  lower := (5344907/175930000)
  upper := (5380093/175930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_29_interval
}

theorem G43_30_formula : baezDuarteGramEntry 43 30 = vasyuninBEntry 30 43 := by
  rw [baezDuarteGramEntry_symm 43 30]
  exact G30_43_formula

theorem G43_30_interval :
    ((((1092343/36570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 30) ∧
    (baezDuarteGramEntry 43 30 ≤ (((1099657/36570000) : ℚ) : ℝ)) := by
  rw [G43_30_formula]
  exact vasyuninBEntry_30_43_eval

def interval_43_30 : NamedVasyuninInterval :=
{
  h := 43
  k := 30
  lower := (1092343/36570000)
  upper := (1099657/36570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_30_interval
}

theorem G43_31_formula : baezDuarteGramEntry 43 31 = vasyuninBEntry 31 43 := by
  rw [baezDuarteGramEntry_symm 43 31]
  exact G31_43_formula

theorem G43_31_interval :
    ((((27187861/921390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 31) ∧
    (baezDuarteGramEntry 43 31 ≤ (((27372139/921390000) : ℚ) : ℝ)) := by
  rw [G43_31_formula]
  exact vasyuninBEntry_31_43_eval

def interval_43_31 : NamedVasyuninInterval :=
{
  h := 43
  k := 31
  lower := (27187861/921390000)
  upper := (27372139/921390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_31_interval
}

theorem G43_32_formula : baezDuarteGramEntry 43 32 = vasyuninBEntry 32 43 := by
  rw [baezDuarteGramEntry_symm 43 32]
  exact G32_43_formula

theorem G43_32_interval :
    ((((12183347/416530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 32) ∧
    (baezDuarteGramEntry 43 32 ≤ (((12266653/416530000) : ℚ) : ℝ)) := by
  rw [G43_32_formula]
  exact vasyuninBEntry_32_43_eval

def interval_43_32 : NamedVasyuninInterval :=
{
  h := 43
  k := 32
  lower := (12183347/416530000)
  upper := (12266653/416530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_32_interval
}

theorem G43_33_formula : baezDuarteGramEntry 43 33 = vasyuninBEntry 33 43 := by
  rw [baezDuarteGramEntry_symm 43 33]
  exact G33_43_formula

theorem G43_33_interval :
    ((((839599/29010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 33) ∧
    (baezDuarteGramEntry 43 33 ≤ (((845401/29010000) : ℚ) : ℝ)) := by
  rw [G43_33_formula]
  exact vasyuninBEntry_33_43_eval

def interval_43_33 : NamedVasyuninInterval :=
{
  h := 43
  k := 33
  lower := (839599/29010000)
  upper := (845401/29010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_33_interval
}

theorem G43_34_formula : baezDuarteGramEntry 43 34 = vasyuninBEntry 34 43 := by
  rw [baezDuarteGramEntry_symm 43 34]
  exact G34_43_formula

theorem G43_34_interval :
    ((((11898547/414530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 34) ∧
    (baezDuarteGramEntry 43 34 ≤ (((11981453/414530000) : ℚ) : ℝ)) := by
  rw [G43_34_formula]
  exact vasyuninBEntry_34_43_eval

def interval_43_34 : NamedVasyuninInterval :=
{
  h := 43
  k := 34
  lower := (11898547/414530000)
  upper := (11981453/414530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_34_interval
}

theorem G43_35_formula : baezDuarteGramEntry 43 35 = vasyuninBEntry 35 43 := by
  rw [baezDuarteGramEntry_symm 43 35]
  exact G35_43_formula

theorem G43_35_interval :
    ((((24175179/848210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 35) ∧
    (baezDuarteGramEntry 43 35 ≤ (((24344821/848210000) : ℚ) : ℝ)) := by
  rw [G43_35_formula]
  exact vasyuninBEntry_35_43_eval

def interval_43_35 : NamedVasyuninInterval :=
{
  h := 43
  k := 35
  lower := (24175179/848210000)
  upper := (24344821/848210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_35_interval
}

theorem G43_36_formula : baezDuarteGramEntry 43 36 = vasyuninBEntry 36 43 := by
  rw [baezDuarteGramEntry_symm 43 36]
  exact G36_43_formula

theorem G43_36_interval :
    ((((21255023/749770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 36) ∧
    (baezDuarteGramEntry 43 36 ≤ (((21404977/749770000) : ℚ) : ℝ)) := by
  rw [G43_36_formula]
  exact vasyuninBEntry_36_43_eval

def interval_43_36 : NamedVasyuninInterval :=
{
  h := 43
  k := 36
  lower := (21255023/749770000)
  upper := (21404977/749770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_36_interval
}

theorem G43_37_formula : baezDuarteGramEntry 43 37 = vasyuninBEntry 37 43 := by
  rw [baezDuarteGramEntry_symm 43 37]
  exact G37_43_formula

theorem G43_37_interval :
    ((((12864427/455730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 37) ∧
    (baezDuarteGramEntry 43 37 ≤ (((12955573/455730000) : ℚ) : ℝ)) := by
  rw [G43_37_formula]
  exact vasyuninBEntry_37_43_eval

def interval_43_37 : NamedVasyuninInterval :=
{
  h := 43
  k := 37
  lower := (12864427/455730000)
  upper := (12955573/455730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_37_interval
}

theorem G43_38_formula : baezDuarteGramEntry 43 38 = vasyuninBEntry 38 43 := by
  rw [baezDuarteGramEntry_symm 43 38]
  exact G38_43_formula

theorem G43_38_interval :
    ((((11030821/391790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 38) ∧
    (baezDuarteGramEntry 43 38 ≤ (((11109179/391790000) : ℚ) : ℝ)) := by
  rw [G43_38_formula]
  exact vasyuninBEntry_38_43_eval

def interval_43_38 : NamedVasyuninInterval :=
{
  h := 43
  k := 38
  lower := (11030821/391790000)
  upper := (11109179/391790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_38_interval
}

theorem G43_39_formula : baezDuarteGramEntry 43 39 = vasyuninBEntry 39 43 := by
  rw [baezDuarteGramEntry_symm 43 39]
  exact G39_43_formula

theorem G43_39_interval :
    ((((120721/4290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 39) ∧
    (baezDuarteGramEntry 43 39 ≤ (((121579/4290000) : ℚ) : ℝ)) := by
  rw [G43_39_formula]
  exact vasyuninBEntry_39_43_eval

def interval_43_39 : NamedVasyuninInterval :=
{
  h := 43
  k := 39
  lower := (120721/4290000)
  upper := (121579/4290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_39_interval
}

theorem G43_40_formula : baezDuarteGramEntry 43 40 = vasyuninBEntry 40 43 := by
  rw [baezDuarteGramEntry_symm 43 40]
  exact G40_43_formula

theorem G43_40_interval :
    ((((229187/8130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 40) ∧
    (baezDuarteGramEntry 43 40 ≤ (((230813/8130000) : ℚ) : ℝ)) := by
  rw [G43_40_formula]
  exact vasyuninBEntry_40_43_eval

def interval_43_40 : NamedVasyuninInterval :=
{
  h := 43
  k := 40
  lower := (229187/8130000)
  upper := (230813/8130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_40_interval
}

theorem G43_41_formula : baezDuarteGramEntry 43 41 = vasyuninBEntry 41 43 := by
  rw [baezDuarteGramEntry_symm 43 41]
  exact G41_43_formula

theorem G43_41_interval :
    ((((23098457/815430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 41) ∧
    (baezDuarteGramEntry 43 41 ≤ (((23261543/815430000) : ℚ) : ℝ)) := by
  rw [G43_41_formula]
  exact vasyuninBEntry_41_43_eval

def interval_43_41 : NamedVasyuninInterval :=
{
  h := 43
  k := 41
  lower := (23098457/815430000)
  upper := (23261543/815430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_41_interval
}

theorem G43_42_formula : baezDuarteGramEntry 43 42 = vasyuninBEntry 42 43 := by
  rw [baezDuarteGramEntry_symm 43 42]
  exact G42_43_formula

theorem G43_42_interval :
    ((((26317961/920390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 42) ∧
    (baezDuarteGramEntry 43 42 ≤ (((26502039/920390000) : ℚ) : ℝ)) := by
  rw [G43_42_formula]
  exact vasyuninBEntry_42_43_eval

def interval_43_42 : NamedVasyuninInterval :=
{
  h := 43
  k := 42
  lower := (26317961/920390000)
  upper := (26502039/920390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_42_interval
}

theorem G43_43_formula_eq : baezDuarteGramEntry 43 43 = (1 / (43 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 43 := by norm_num
  rw [baez_duarte_diagonal_scaling 43 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G43_43_log_gamma_interval :
  ((((15805903/540970000) : ℚ) : ℝ) ≤ (1 / (43 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (43 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((15914097/540970000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 43 (by norm_num)
  constructor
  · have : ((((15805903/540970000) : ℚ) : ℝ) ≤ (1 / (43 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (43 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((15914097/540970000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G43_43_interval : ((((15805903/540970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 43) ∧ (baezDuarteGramEntry 43 43 ≤ (((15914097/540970000) : ℚ) : ℝ)) := by
  rw [G43_43_formula_eq]
  exact G43_43_log_gamma_interval

def interval_43_43 : NamedVasyuninInterval :=
{
  h := 43
  k := 43
  lower := (15805903/540970000)
  upper := (15914097/540970000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G43_43_interval
}

theorem G43_44_formula : baezDuarteGramEntry 43 44 = vasyuninBEntry 43 44 := vasyuninBEntry_correct_axiom 43 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_43_44_eval :
    ((((23725117/848830000) : ℚ) : ℝ) ≤ vasyuninBEntry 43 44) ∧
    (vasyuninBEntry 43 44 ≤ (((23894883/848830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4344_formula_bound
  constructor <;> linarith

theorem G43_44_interval :
    ((((23725117/848830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 44) ∧
    (baezDuarteGramEntry 43 44 ≤ (((23894883/848830000) : ℚ) : ℝ)) := by
  rw [G43_44_formula]
  exact vasyuninBEntry_43_44_eval

def interval_43_44 : NamedVasyuninInterval :=
{
  h := 43
  k := 44
  lower := (23725117/848830000)
  upper := (23894883/848830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_44_interval
}

theorem G43_45_formula : baezDuarteGramEntry 43 45 = vasyuninBEntry 43 45 := vasyuninBEntry_correct_axiom 43 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_43_45_eval :
    ((((7512259/277410000) : ℚ) : ℝ) ≤ vasyuninBEntry 43 45) ∧
    (vasyuninBEntry 43 45 ≤ (((7567741/277410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4345_formula_bound
  constructor <;> linarith

theorem G43_45_interval :
    ((((7512259/277410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 45) ∧
    (baezDuarteGramEntry 43 45 ≤ (((7567741/277410000) : ℚ) : ℝ)) := by
  rw [G43_45_formula]
  exact vasyuninBEntry_43_45_eval

def interval_43_45 : NamedVasyuninInterval :=
{
  h := 43
  k := 45
  lower := (7512259/277410000)
  upper := (7567741/277410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_45_interval
}

theorem G43_46_formula : baezDuarteGramEntry 43 46 = vasyuninBEntry 43 46 := vasyuninBEntry_correct_axiom 43 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_43_46_eval :
    ((((4626451/175490000) : ℚ) : ℝ) ≤ vasyuninBEntry 43 46) ∧
    (vasyuninBEntry 43 46 ≤ (((4661549/175490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4346_formula_bound
  constructor <;> linarith

theorem G43_46_interval :
    ((((4626451/175490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 46) ∧
    (baezDuarteGramEntry 43 46 ≤ (((4661549/175490000) : ℚ) : ℝ)) := by
  rw [G43_46_formula]
  exact vasyuninBEntry_43_46_eval

def interval_43_46 : NamedVasyuninInterval :=
{
  h := 43
  k := 46
  lower := (4626451/175490000)
  upper := (4661549/175490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_46_interval
}

theorem G43_47_formula : baezDuarteGramEntry 43 47 = vasyuninBEntry 43 47 := vasyuninBEntry_correct_axiom 43 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_43_47_eval :
    ((((1096989/42610000) : ℚ) : ℝ) ≤ vasyuninBEntry 43 47) ∧
    (vasyuninBEntry 43 47 ≤ (((1105511/42610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4347_formula_bound
  constructor <;> linarith

theorem G43_47_interval :
    ((((1096989/42610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 47) ∧
    (baezDuarteGramEntry 43 47 ≤ (((1105511/42610000) : ℚ) : ℝ)) := by
  rw [G43_47_formula]
  exact vasyuninBEntry_43_47_eval

def interval_43_47 : NamedVasyuninInterval :=
{
  h := 43
  k := 47
  lower := (1096989/42610000)
  upper := (1105511/42610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_47_interval
}

theorem G43_48_formula : baezDuarteGramEntry 43 48 = vasyuninBEntry 43 48 := vasyuninBEntry_correct_axiom 43 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_43_48_eval :
    ((((2388521/94790000) : ℚ) : ℝ) ≤ vasyuninBEntry 43 48) ∧
    (vasyuninBEntry 43 48 ≤ (((2407479/94790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4348_formula_bound
  constructor <;> linarith

theorem G43_48_interval :
    ((((2388521/94790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 48) ∧
    (baezDuarteGramEntry 43 48 ≤ (((2407479/94790000) : ℚ) : ℝ)) := by
  rw [G43_48_formula]
  exact vasyuninBEntry_43_48_eval

def interval_43_48 : NamedVasyuninInterval :=
{
  h := 43
  k := 48
  lower := (2388521/94790000)
  upper := (2407479/94790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_48_interval
}

theorem G43_49_formula : baezDuarteGramEntry 43 49 = vasyuninBEntry 43 49 := vasyuninBEntry_correct_axiom 43 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_43_49_eval :
    ((((1715059/69410000) : ℚ) : ℝ) ≤ vasyuninBEntry 43 49) ∧
    (vasyuninBEntry 43 49 ≤ (((1728941/69410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4349_formula_bound
  constructor <;> linarith

theorem G43_49_interval :
    ((((1715059/69410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 49) ∧
    (baezDuarteGramEntry 43 49 ≤ (((1728941/69410000) : ℚ) : ℝ)) := by
  rw [G43_49_formula]
  exact vasyuninBEntry_43_49_eval

def interval_43_49 : NamedVasyuninInterval :=
{
  h := 43
  k := 49
  lower := (1715059/69410000)
  upper := (1728941/69410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_49_interval
}

theorem G43_50_formula : baezDuarteGramEntry 43 50 = vasyuninBEntry 43 50 := vasyuninBEntry_correct_axiom 43 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_43_50_eval :
    ((((21869869/901310000) : ℚ) : ℝ) ≤ vasyuninBEntry 43 50) ∧
    (vasyuninBEntry 43 50 ≤ (((22050131/901310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4350_formula_bound
  constructor <;> linarith

theorem G43_50_interval :
    ((((21869869/901310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 43 50) ∧
    (baezDuarteGramEntry 43 50 ≤ (((22050131/901310000) : ℚ) : ℝ)) := by
  rw [G43_50_formula]
  exact vasyuninBEntry_43_50_eval

def interval_43_50 : NamedVasyuninInterval :=
{
  h := 43
  k := 50
  lower := (21869869/901310000)
  upper := (22050131/901310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G43_50_interval
}

theorem G44_1_formula : baezDuarteGramEntry 44 1 = vasyuninBEntry 1 44 := by
  rw [baezDuarteGramEntry_symm 44 1]
  exact G1_44_formula

theorem G44_1_interval :
    ((((17097599/249010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 1) ∧
    (baezDuarteGramEntry 44 1 ≤ (((17147401/249010000) : ℚ) : ℝ)) := by
  rw [G44_1_formula]
  exact vasyuninBEntry_1_44_eval

def interval_44_1 : NamedVasyuninInterval :=
{
  h := 44
  k := 1
  lower := (17097599/249010000)
  upper := (17147401/249010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_1_interval
}

theorem G44_2_formula : baezDuarteGramEntry 44 2 = vasyuninBEntry 2 44 := by
  rw [baezDuarteGramEntry_symm 44 2]
  exact G2_44_formula

theorem G44_2_interval :
    ((((3671467/60330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 2) ∧
    (baezDuarteGramEntry 44 2 ≤ (((3683533/60330000) : ℚ) : ℝ)) := by
  rw [G44_2_formula]
  exact vasyuninBEntry_2_44_eval

def interval_44_2 : NamedVasyuninInterval :=
{
  h := 44
  k := 2
  lower := (3671467/60330000)
  upper := (3683533/60330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_2_interval
}

theorem G44_3_formula : baezDuarteGramEntry 44 3 = vasyuninBEntry 3 44 := by
  rw [baezDuarteGramEntry_symm 44 3]
  exact G3_44_formula

theorem G44_3_interval :
    ((((33989377/606230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 3) ∧
    (baezDuarteGramEntry 44 3 ≤ (((34110623/606230000) : ℚ) : ℝ)) := by
  rw [G44_3_formula]
  exact vasyuninBEntry_3_44_eval

def interval_44_3 : NamedVasyuninInterval :=
{
  h := 44
  k := 3
  lower := (33989377/606230000)
  upper := (34110623/606230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_3_interval
}

theorem G44_4_formula : baezDuarteGramEntry 44 4 = vasyuninBEntry 4 44 := by
  rw [baezDuarteGramEntry_symm 44 4]
  exact G4_44_formula

theorem G44_4_interval :
    ((((37459483/705170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 4) ∧
    (baezDuarteGramEntry 44 4 ≤ (((37600517/705170000) : ℚ) : ℝ)) := by
  rw [G44_4_formula]
  exact vasyuninBEntry_4_44_eval

def interval_44_4 : NamedVasyuninInterval :=
{
  h := 44
  k := 4
  lower := (37459483/705170000)
  upper := (37600517/705170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_4_interval
}

theorem G44_5_formula : baezDuarteGramEntry 44 5 = vasyuninBEntry 5 44 := by
  rw [baezDuarteGramEntry_symm 44 5]
  exact G5_44_formula

theorem G44_5_interval :
    ((((22944367/456330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 5) ∧
    (baezDuarteGramEntry 44 5 ≤ (((23035633/456330000) : ℚ) : ℝ)) := by
  rw [G44_5_formula]
  exact vasyuninBEntry_5_44_eval

def interval_44_5 : NamedVasyuninInterval :=
{
  h := 44
  k := 5
  lower := (22944367/456330000)
  upper := (23035633/456330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_5_interval
}

theorem G44_6_formula : baezDuarteGramEntry 44 6 = vasyuninBEntry 6 44 := by
  rw [baezDuarteGramEntry_symm 44 6]
  exact G6_44_formula

theorem G44_6_interval :
    ((((34378611/713890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 6) ∧
    (baezDuarteGramEntry 44 6 ≤ (((34521389/713890000) : ℚ) : ℝ)) := by
  rw [G44_6_formula]
  exact vasyuninBEntry_6_44_eval

def interval_44_6 : NamedVasyuninInterval :=
{
  h := 44
  k := 6
  lower := (34378611/713890000)
  upper := (34521389/713890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_6_interval
}

theorem G44_7_formula : baezDuarteGramEntry 44 7 = vasyuninBEntry 7 44 := by
  rw [baezDuarteGramEntry_symm 44 7]
  exact G7_44_formula

theorem G44_7_interval :
    ((((19662619/423810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 7) ∧
    (baezDuarteGramEntry 44 7 ≤ (((19747381/423810000) : ℚ) : ℝ)) := by
  rw [G44_7_formula]
  exact vasyuninBEntry_7_44_eval

def interval_44_7 : NamedVasyuninInterval :=
{
  h := 44
  k := 7
  lower := (19662619/423810000)
  upper := (19747381/423810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_7_interval
}

theorem G44_8_formula : baezDuarteGramEntry 44 8 = vasyuninBEntry 8 44 := by
  rw [baezDuarteGramEntry_symm 44 8]
  exact G8_44_formula

theorem G44_8_interval :
    ((((36538607/813930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 8) ∧
    (baezDuarteGramEntry 44 8 ≤ (((36701393/813930000) : ℚ) : ℝ)) := by
  rw [G44_8_formula]
  exact vasyuninBEntry_8_44_eval

def interval_44_8 : NamedVasyuninInterval :=
{
  h := 44
  k := 8
  lower := (36538607/813930000)
  upper := (36701393/813930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_8_interval
}

theorem G44_9_formula : baezDuarteGramEntry 44 9 = vasyuninBEntry 9 44 := by
  rw [baezDuarteGramEntry_symm 44 9]
  exact G9_44_formula

theorem G44_9_interval :
    ((((13763527/314730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 9) ∧
    (baezDuarteGramEntry 44 9 ≤ (((13826473/314730000) : ℚ) : ℝ)) := by
  rw [G44_9_formula]
  exact vasyuninBEntry_9_44_eval

def interval_44_9 : NamedVasyuninInterval :=
{
  h := 44
  k := 9
  lower := (13763527/314730000)
  upper := (13826473/314730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_9_interval
}

theorem G44_10_formula : baezDuarteGramEntry 44 10 = vasyuninBEntry 10 44 := by
  rw [baezDuarteGramEntry_symm 44 10]
  exact G10_44_formula

theorem G44_10_interval :
    ((((6888697/163030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 10) ∧
    (baezDuarteGramEntry 44 10 ≤ (((6921303/163030000) : ℚ) : ℝ)) := by
  rw [G44_10_formula]
  exact vasyuninBEntry_10_44_eval

def interval_44_10 : NamedVasyuninInterval :=
{
  h := 44
  k := 10
  lower := (6888697/163030000)
  upper := (6921303/163030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_10_interval
}

theorem G44_11_formula : baezDuarteGramEntry 44 11 = vasyuninBEntry 11 44 := by
  rw [baezDuarteGramEntry_symm 44 11]
  exact G11_44_formula

theorem G44_11_interval :
    ((((1596709/37910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 11) ∧
    (baezDuarteGramEntry 44 11 ≤ (((1604291/37910000) : ℚ) : ℝ)) := by
  rw [G44_11_formula]
  exact vasyuninBEntry_11_44_eval

def interval_44_11 : NamedVasyuninInterval :=
{
  h := 44
  k := 11
  lower := (1596709/37910000)
  upper := (1604291/37910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_11_interval
}

theorem G44_12_formula : baezDuarteGramEntry 44 12 = vasyuninBEntry 12 44 := by
  rw [baezDuarteGramEntry_symm 44 12]
  exact G12_44_formula

theorem G44_12_interval :
    ((((18538861/461390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 12) ∧
    (baezDuarteGramEntry 44 12 ≤ (((18631139/461390000) : ℚ) : ℝ)) := by
  rw [G44_12_formula]
  exact vasyuninBEntry_12_44_eval

def interval_44_12 : NamedVasyuninInterval :=
{
  h := 44
  k := 12
  lower := (18538861/461390000)
  upper := (18631139/461390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_12_interval
}

theorem G44_13_formula : baezDuarteGramEntry 44 13 = vasyuninBEntry 13 44 := by
  rw [baezDuarteGramEntry_symm 44 13]
  exact G13_44_formula

theorem G44_13_interval :
    ((((33265189/848110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 13) ∧
    (baezDuarteGramEntry 44 13 ≤ (((33434811/848110000) : ℚ) : ℝ)) := by
  rw [G44_13_formula]
  exact vasyuninBEntry_13_44_eval

def interval_44_13 : NamedVasyuninInterval :=
{
  h := 44
  k := 13
  lower := (33265189/848110000)
  upper := (33434811/848110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_13_interval
}

theorem G44_14_formula : baezDuarteGramEntry 44 14 = vasyuninBEntry 14 44 := by
  rw [baezDuarteGramEntry_symm 44 14]
  exact G14_44_formula

theorem G44_14_interval :
    ((((33852577/874230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 14) ∧
    (baezDuarteGramEntry 44 14 ≤ (((34027423/874230000) : ℚ) : ℝ)) := by
  rw [G44_14_formula]
  exact vasyuninBEntry_14_44_eval

def interval_44_14 : NamedVasyuninInterval :=
{
  h := 44
  k := 14
  lower := (33852577/874230000)
  upper := (34027423/874230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_14_interval
}

theorem G44_15_formula : baezDuarteGramEntry 44 15 = vasyuninBEntry 15 44 := by
  rw [baezDuarteGramEntry_symm 44 15]
  exact G15_44_formula

theorem G44_15_interval :
    ((((37751183/988170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 15) ∧
    (baezDuarteGramEntry 44 15 ≤ (((37948817/988170000) : ℚ) : ℝ)) := by
  rw [G44_15_formula]
  exact vasyuninBEntry_15_44_eval

def interval_44_15 : NamedVasyuninInterval :=
{
  h := 44
  k := 15
  lower := (37751183/988170000)
  upper := (37948817/988170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_15_interval
}

theorem G44_16_formula : baezDuarteGramEntry 44 16 = vasyuninBEntry 16 44 := by
  rw [baezDuarteGramEntry_symm 44 16]
  exact G16_44_formula

theorem G44_16_interval :
    ((((895573/24270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 16) ∧
    (baezDuarteGramEntry 44 16 ≤ (((900427/24270000) : ℚ) : ℝ)) := by
  rw [G44_16_formula]
  exact vasyuninBEntry_16_44_eval

def interval_44_16 : NamedVasyuninInterval :=
{
  h := 44
  k := 16
  lower := (895573/24270000)
  upper := (900427/24270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_16_interval
}

theorem G44_17_formula : baezDuarteGramEntry 44 17 = vasyuninBEntry 17 44 := by
  rw [baezDuarteGramEntry_symm 44 17]
  exact G17_44_formula

theorem G44_17_interval :
    ((((22796791/632090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 17) ∧
    (baezDuarteGramEntry 44 17 ≤ (((22923209/632090000) : ℚ) : ℝ)) := by
  rw [G44_17_formula]
  exact vasyuninBEntry_17_44_eval

def interval_44_17 : NamedVasyuninInterval :=
{
  h := 44
  k := 17
  lower := (22796791/632090000)
  upper := (22923209/632090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_17_interval
}

theorem G44_18_formula : baezDuarteGramEntry 44 18 = vasyuninBEntry 18 44 := by
  rw [baezDuarteGramEntry_symm 44 18]
  exact G18_44_formula

theorem G44_18_interval :
    ((((10071583/284170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 18) ∧
    (baezDuarteGramEntry 44 18 ≤ (((10128417/284170000) : ℚ) : ℝ)) := by
  rw [G44_18_formula]
  exact vasyuninBEntry_18_44_eval

def interval_44_18 : NamedVasyuninInterval :=
{
  h := 44
  k := 18
  lower := (10071583/284170000)
  upper := (10128417/284170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_18_interval
}

theorem G44_19_formula : baezDuarteGramEntry 44 19 = vasyuninBEntry 19 44 := by
  rw [baezDuarteGramEntry_symm 44 19]
  exact G19_44_formula

theorem G44_19_interval :
    ((((2071067/59330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 19) ∧
    (baezDuarteGramEntry 44 19 ≤ (((2082933/59330000) : ℚ) : ℝ)) := by
  rw [G44_19_formula]
  exact vasyuninBEntry_19_44_eval

def interval_44_19 : NamedVasyuninInterval :=
{
  h := 44
  k := 19
  lower := (2071067/59330000)
  upper := (2082933/59330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_19_interval
}

theorem G44_20_formula : baezDuarteGramEntry 44 20 = vasyuninBEntry 20 44 := by
  rw [baezDuarteGramEntry_symm 44 20]
  exact G20_44_formula

theorem G44_20_interval :
    ((((26573089/769110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 20) ∧
    (baezDuarteGramEntry 44 20 ≤ (((26726911/769110000) : ℚ) : ℝ)) := by
  rw [G44_20_formula]
  exact vasyuninBEntry_20_44_eval

def interval_44_20 : NamedVasyuninInterval :=
{
  h := 44
  k := 20
  lower := (26573089/769110000)
  upper := (26726911/769110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_20_interval
}

theorem G44_21_formula : baezDuarteGramEntry 44 21 = vasyuninBEntry 21 44 := by
  rw [baezDuarteGramEntry_symm 44 21]
  exact G21_44_formula

theorem G44_21_interval :
    ((((19782547/574530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 21) ∧
    (baezDuarteGramEntry 44 21 ≤ (((19897453/574530000) : ℚ) : ℝ)) := by
  rw [G44_21_formula]
  exact vasyuninBEntry_21_44_eval

def interval_44_21 : NamedVasyuninInterval :=
{
  h := 44
  k := 21
  lower := (19782547/574530000)
  upper := (19897453/574530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_21_interval
}

theorem G44_22_formula : baezDuarteGramEntry 44 22 = vasyuninBEntry 22 44 := by
  rw [baezDuarteGramEntry_symm 44 22]
  exact G22_44_formula

theorem G44_22_interval :
    ((((28039887/801130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 22) ∧
    (baezDuarteGramEntry 44 22 ≤ (((28200113/801130000) : ℚ) : ℝ)) := by
  rw [G44_22_formula]
  exact vasyuninBEntry_22_44_eval

def interval_44_22 : NamedVasyuninInterval :=
{
  h := 44
  k := 22
  lower := (28039887/801130000)
  upper := (28200113/801130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_22_interval
}

theorem G44_23_formula : baezDuarteGramEntry 44 23 = vasyuninBEntry 23 44 := by
  rw [baezDuarteGramEntry_symm 44 23]
  exact G23_44_formula

theorem G44_23_interval :
    ((((26031919/780810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 23) ∧
    (baezDuarteGramEntry 44 23 ≤ (((26188081/780810000) : ℚ) : ℝ)) := by
  rw [G44_23_formula]
  exact vasyuninBEntry_23_44_eval

def interval_44_23 : NamedVasyuninInterval :=
{
  h := 44
  k := 23
  lower := (26031919/780810000)
  upper := (26188081/780810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_23_interval
}

theorem G44_24_formula : baezDuarteGramEntry 44 24 = vasyuninBEntry 24 44 := by
  rw [baezDuarteGramEntry_symm 44 24]
  exact G24_44_formula

theorem G44_24_interval :
    ((((22749787/702130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 24) ∧
    (baezDuarteGramEntry 44 24 ≤ (((22890213/702130000) : ℚ) : ℝ)) := by
  rw [G44_24_formula]
  exact vasyuninBEntry_24_44_eval

def interval_44_24 : NamedVasyuninInterval :=
{
  h := 44
  k := 24
  lower := (22749787/702130000)
  upper := (22890213/702130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_24_interval
}

theorem G44_25_formula : baezDuarteGramEntry 44 25 = vasyuninBEntry 25 44 := by
  rw [baezDuarteGramEntry_symm 44 25]
  exact G25_44_formula

theorem G44_25_interval :
    ((((222501/7021250) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 25) ∧
    (baezDuarteGramEntry 44 25 ≤ (((895621/28085000) : ℚ) : ℝ)) := by
  rw [G44_25_formula]
  exact vasyuninBEntry_25_44_eval

def interval_44_25 : NamedVasyuninInterval :=
{
  h := 44
  k := 25
  lower := (222501/7021250)
  upper := (895621/28085000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_25_interval
}

theorem G44_26_formula : baezDuarteGramEntry 44 26 = vasyuninBEntry 26 44 := by
  rw [baezDuarteGramEntry_symm 44 26]
  exact G26_44_formula

theorem G44_26_interval :
    ((((15869001/509990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 26) ∧
    (baezDuarteGramEntry 44 26 ≤ (((15970999/509990000) : ℚ) : ℝ)) := by
  rw [G44_26_formula]
  exact vasyuninBEntry_26_44_eval

def interval_44_26 : NamedVasyuninInterval :=
{
  h := 44
  k := 26
  lower := (15869001/509990000)
  upper := (15970999/509990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_26_interval
}

theorem G44_27_formula : baezDuarteGramEntry 44 27 = vasyuninBEntry 27 44 := by
  rw [baezDuarteGramEntry_symm 44 27]
  exact G27_44_formula

theorem G44_27_interval :
    ((((1410393/46070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 27) ∧
    (baezDuarteGramEntry 44 27 ≤ (((1419607/46070000) : ℚ) : ℝ)) := by
  rw [G44_27_formula]
  exact vasyuninBEntry_27_44_eval

def interval_44_27 : NamedVasyuninInterval :=
{
  h := 44
  k := 27
  lower := (1410393/46070000)
  upper := (1419607/46070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_27_interval
}

theorem G44_28_formula : baezDuarteGramEntry 44 28 = vasyuninBEntry 28 44 := by
  rw [baezDuarteGramEntry_symm 44 28]
  exact G28_44_formula

theorem G44_28_interval :
    ((((29223251/967490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 28) ∧
    (baezDuarteGramEntry 44 28 ≤ (((29416749/967490000) : ℚ) : ℝ)) := by
  rw [G44_28_formula]
  exact vasyuninBEntry_28_44_eval

def interval_44_28 : NamedVasyuninInterval :=
{
  h := 44
  k := 28
  lower := (29223251/967490000)
  upper := (29416749/967490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_28_interval
}

theorem G44_29_formula : baezDuarteGramEntry 44 29 = vasyuninBEntry 29 44 := by
  rw [baezDuarteGramEntry_symm 44 29]
  exact G29_44_formula

theorem G44_29_interval :
    ((((4195987/140130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 29) ∧
    (baezDuarteGramEntry 44 29 ≤ (((4224013/140130000) : ℚ) : ℝ)) := by
  rw [G44_29_formula]
  exact vasyuninBEntry_29_44_eval

def interval_44_29 : NamedVasyuninInterval :=
{
  h := 44
  k := 29
  lower := (4195987/140130000)
  upper := (4224013/140130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_29_interval
}

theorem G44_30_formula : baezDuarteGramEntry 44 30 = vasyuninBEntry 30 44 := by
  rw [baezDuarteGramEntry_symm 44 30]
  exact G30_44_formula

theorem G44_30_interval :
    ((((17002367/576330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 30) ∧
    (baezDuarteGramEntry 44 30 ≤ (((17117633/576330000) : ℚ) : ℝ)) := by
  rw [G44_30_formula]
  exact vasyuninBEntry_30_44_eval

def interval_44_30 : NamedVasyuninInterval :=
{
  h := 44
  k := 30
  lower := (17002367/576330000)
  upper := (17117633/576330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_30_interval
}

theorem G44_31_formula : baezDuarteGramEntry 44 31 = vasyuninBEntry 31 44 := by
  rw [baezDuarteGramEntry_symm 44 31]
  exact G31_44_formula

theorem G44_31_interval :
    ((((2822791/97090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 31) ∧
    (baezDuarteGramEntry 44 31 ≤ (((2842209/97090000) : ℚ) : ℝ)) := by
  rw [G44_31_formula]
  exact vasyuninBEntry_31_44_eval

def interval_44_31 : NamedVasyuninInterval :=
{
  h := 44
  k := 31
  lower := (2822791/97090000)
  upper := (2842209/97090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_31_interval
}

theorem G44_32_formula : baezDuarteGramEntry 44 32 = vasyuninBEntry 32 44 := by
  rw [baezDuarteGramEntry_symm 44 32]
  exact G32_44_formula

theorem G44_32_interval :
    ((((1903381/66190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 32) ∧
    (baezDuarteGramEntry 44 32 ≤ (((1916619/66190000) : ℚ) : ℝ)) := by
  rw [G44_32_formula]
  exact vasyuninBEntry_32_44_eval

def interval_44_32 : NamedVasyuninInterval :=
{
  h := 44
  k := 32
  lower := (1903381/66190000)
  upper := (1916619/66190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_32_interval
}

theorem G44_33_formula : baezDuarteGramEntry 44 33 = vasyuninBEntry 33 44 := by
  rw [baezDuarteGramEntry_symm 44 33]
  exact G33_44_formula

theorem G44_33_interval :
    ((((12595923/440770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 33) ∧
    (baezDuarteGramEntry 44 33 ≤ (((12684077/440770000) : ℚ) : ℝ)) := by
  rw [G44_33_formula]
  exact vasyuninBEntry_33_44_eval

def interval_44_33 : NamedVasyuninInterval :=
{
  h := 44
  k := 33
  lower := (12595923/440770000)
  upper := (12684077/440770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_33_interval
}

theorem G44_34_formula : baezDuarteGramEntry 44 34 = vasyuninBEntry 34 44 := by
  rw [baezDuarteGramEntry_symm 44 34]
  exact G34_44_formula

theorem G44_34_interval :
    ((((346273/12270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 34) ∧
    (baezDuarteGramEntry 44 34 ≤ (((348727/12270000) : ℚ) : ℝ)) := by
  rw [G44_34_formula]
  exact vasyuninBEntry_34_44_eval

def interval_44_34 : NamedVasyuninInterval :=
{
  h := 44
  k := 34
  lower := (346273/12270000)
  upper := (348727/12270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_34_interval
}

theorem G44_35_formula : baezDuarteGramEntry 44 35 = vasyuninBEntry 35 44 := by
  rw [baezDuarteGramEntry_symm 44 35]
  exact G35_44_formula

theorem G44_35_interval :
    ((((5348411/190890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 35) ∧
    (baezDuarteGramEntry 44 35 ≤ (((5386589/190890000) : ℚ) : ℝ)) := by
  rw [G44_35_formula]
  exact vasyuninBEntry_35_44_eval

def interval_44_35 : NamedVasyuninInterval :=
{
  h := 44
  k := 35
  lower := (5348411/190890000)
  upper := (5386589/190890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_35_interval
}

theorem G44_36_formula : baezDuarteGramEntry 44 36 = vasyuninBEntry 36 44 := by
  rw [baezDuarteGramEntry_symm 44 36]
  exact G36_44_formula

theorem G44_36_interval :
    ((((1330219/47810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 36) ∧
    (baezDuarteGramEntry 44 36 ≤ (((1339781/47810000) : ℚ) : ℝ)) := by
  rw [G44_36_formula]
  exact vasyuninBEntry_36_44_eval

def interval_44_36 : NamedVasyuninInterval :=
{
  h := 44
  k := 36
  lower := (1330219/47810000)
  upper := (1339781/47810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_36_interval
}

theorem G44_37_formula : baezDuarteGramEntry 44 37 = vasyuninBEntry 37 44 := by
  rw [baezDuarteGramEntry_symm 44 37]
  exact G37_44_formula

theorem G44_37_interval :
    ((((25657293/927070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 37) ∧
    (baezDuarteGramEntry 44 37 ≤ (((25842707/927070000) : ℚ) : ℝ)) := by
  rw [G44_37_formula]
  exact vasyuninBEntry_37_44_eval

def interval_44_37 : NamedVasyuninInterval :=
{
  h := 44
  k := 37
  lower := (25657293/927070000)
  upper := (25842707/927070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_37_interval
}

theorem G44_38_formula : baezDuarteGramEntry 44 38 = vasyuninBEntry 38 44 := by
  rw [baezDuarteGramEntry_symm 44 38]
  exact G38_44_formula

theorem G44_38_interval :
    ((((442769/16060000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 38) ∧
    (baezDuarteGramEntry 44 38 ≤ (((445981/16060000) : ℚ) : ℝ)) := by
  rw [G44_38_formula]
  exact vasyuninBEntry_38_44_eval

def interval_44_38 : NamedVasyuninInterval :=
{
  h := 44
  k := 38
  lower := (442769/16060000)
  upper := (445981/16060000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_38_interval
}

theorem G44_39_formula : baezDuarteGramEntry 44 39 = vasyuninBEntry 39 44 := by
  rw [baezDuarteGramEntry_symm 44 39]
  exact G39_44_formula

theorem G44_39_interval :
    ((((3629307/131930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 39) ∧
    (baezDuarteGramEntry 44 39 ≤ (((3655693/131930000) : ℚ) : ℝ)) := by
  rw [G44_39_formula]
  exact vasyuninBEntry_39_44_eval

def interval_44_39 : NamedVasyuninInterval :=
{
  h := 44
  k := 39
  lower := (3629307/131930000)
  upper := (3655693/131930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_39_interval
}

theorem G44_40_formula : baezDuarteGramEntry 44 40 = vasyuninBEntry 40 44 := by
  rw [baezDuarteGramEntry_symm 44 40]
  exact G40_44_formula

theorem G44_40_interval :
    ((((13077451/475490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 40) ∧
    (baezDuarteGramEntry 44 40 ≤ (((13172549/475490000) : ℚ) : ℝ)) := by
  rw [G44_40_formula]
  exact vasyuninBEntry_40_44_eval

def interval_44_40 : NamedVasyuninInterval :=
{
  h := 44
  k := 40
  lower := (13077451/475490000)
  upper := (13172549/475490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_40_interval
}

theorem G44_41_formula : baezDuarteGramEntry 44 41 = vasyuninBEntry 41 44 := by
  rw [baezDuarteGramEntry_symm 44 41]
  exact G41_44_formula

theorem G44_41_interval :
    ((((2923141/106090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 41) ∧
    (baezDuarteGramEntry 44 41 ≤ (((2944359/106090000) : ℚ) : ℝ)) := by
  rw [G44_41_formula]
  exact vasyuninBEntry_41_44_eval

def interval_44_41 : NamedVasyuninInterval :=
{
  h := 44
  k := 41
  lower := (2923141/106090000)
  upper := (2944359/106090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_41_interval
}

theorem G44_42_formula : baezDuarteGramEntry 44 42 = vasyuninBEntry 42 44 := by
  rw [baezDuarteGramEntry_symm 44 42]
  exact G42_44_formula

theorem G44_42_interval :
    ((((3248269/117310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 42) ∧
    (baezDuarteGramEntry 44 42 ≤ (((3271731/117310000) : ℚ) : ℝ)) := by
  rw [G44_42_formula]
  exact vasyuninBEntry_42_44_eval

def interval_44_42 : NamedVasyuninInterval :=
{
  h := 44
  k := 42
  lower := (3248269/117310000)
  upper := (3271731/117310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_42_interval
}

theorem G44_43_formula : baezDuarteGramEntry 44 43 = vasyuninBEntry 43 44 := by
  rw [baezDuarteGramEntry_symm 44 43]
  exact G43_44_formula

theorem G44_43_interval :
    ((((23725117/848830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 43) ∧
    (baezDuarteGramEntry 44 43 ≤ (((23894883/848830000) : ℚ) : ℝ)) := by
  rw [G44_43_formula]
  exact vasyuninBEntry_43_44_eval

def interval_44_43 : NamedVasyuninInterval :=
{
  h := 44
  k := 43
  lower := (23725117/848830000)
  upper := (23894883/848830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_43_interval
}

theorem G44_44_formula_eq : baezDuarteGramEntry 44 44 = (1 / (44 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 44 := by norm_num
  rw [baez_duarte_diagonal_scaling 44 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G44_44_log_gamma_interval :
  ((((3876423/135770000) : ℚ) : ℝ) ≤ (1 / (44 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (44 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((3903577/135770000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 44 (by norm_num)
  constructor
  · have : ((((3876423/135770000) : ℚ) : ℝ) ≤ (1 / (44 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (44 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((3903577/135770000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G44_44_interval : ((((3876423/135770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 44) ∧ (baezDuarteGramEntry 44 44 ≤ (((3903577/135770000) : ℚ) : ℝ)) := by
  rw [G44_44_formula_eq]
  exact G44_44_log_gamma_interval

def interval_44_44 : NamedVasyuninInterval :=
{
  h := 44
  k := 44
  lower := (3876423/135770000)
  upper := (3903577/135770000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G44_44_interval
}

theorem G44_45_formula : baezDuarteGramEntry 44 45 = vasyuninBEntry 44 45 := vasyuninBEntry_correct_axiom 44 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_44_45_eval :
    ((((2944229/107710000) : ℚ) : ℝ) ≤ vasyuninBEntry 44 45) ∧
    (vasyuninBEntry 44 45 ≤ (((2965771/107710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4445_formula_bound
  constructor <;> linarith

theorem G44_45_interval :
    ((((2944229/107710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 45) ∧
    (baezDuarteGramEntry 44 45 ≤ (((2965771/107710000) : ℚ) : ℝ)) := by
  rw [G44_45_formula]
  exact vasyuninBEntry_44_45_eval

def interval_44_45 : NamedVasyuninInterval :=
{
  h := 44
  k := 45
  lower := (2944229/107710000)
  upper := (2965771/107710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_45_interval
}

theorem G44_46_formula : baezDuarteGramEntry 44 46 = vasyuninBEntry 44 46 := vasyuninBEntry_correct_axiom 44 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_44_46_eval :
    ((((866729/32710000) : ℚ) : ℝ) ≤ vasyuninBEntry 44 46) ∧
    (vasyuninBEntry 44 46 ≤ (((873271/32710000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_22_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 22 23 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G44_46_interval :
    ((((866729/32710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 46) ∧
    (baezDuarteGramEntry 44 46 ≤ (((873271/32710000) : ℚ) : ℝ)) := by
  rw [G44_46_formula]
  exact vasyuninBEntry_44_46_eval

def interval_44_46 : NamedVasyuninInterval :=
{
  h := 44
  k := 46
  lower := (866729/32710000)
  upper := (873271/32710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_46_interval
}

theorem G44_47_formula : baezDuarteGramEntry 44 47 = vasyuninBEntry 44 47 := vasyuninBEntry_correct_axiom 44 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_44_47_eval :
    ((((16187273/627270000) : ℚ) : ℝ) ≤ vasyuninBEntry 44 47) ∧
    (vasyuninBEntry 44 47 ≤ (((16312727/627270000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4447_formula_bound
  constructor <;> linarith

theorem G44_47_interval :
    ((((16187273/627270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 47) ∧
    (baezDuarteGramEntry 44 47 ≤ (((16312727/627270000) : ℚ) : ℝ)) := by
  rw [G44_47_formula]
  exact vasyuninBEntry_44_47_eval

def interval_44_47 : NamedVasyuninInterval :=
{
  h := 44
  k := 47
  lower := (16187273/627270000)
  upper := (16312727/627270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_47_interval
}

theorem G44_48_formula : baezDuarteGramEntry 44 48 = vasyuninBEntry 44 48 := vasyuninBEntry_correct_axiom 44 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_44_48_eval :
    ((((7669579/304210000) : ℚ) : ℝ) ≤ vasyuninBEntry 44 48) ∧
    (vasyuninBEntry 44 48 ≤ (((7730421/304210000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_12_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 12 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G44_48_interval :
    ((((7669579/304210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 48) ∧
    (baezDuarteGramEntry 44 48 ≤ (((7730421/304210000) : ℚ) : ℝ)) := by
  rw [G44_48_formula]
  exact vasyuninBEntry_44_48_eval

def interval_44_48 : NamedVasyuninInterval :=
{
  h := 44
  k := 48
  lower := (7669579/304210000)
  upper := (7730421/304210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_48_interval
}

theorem G44_49_formula : baezDuarteGramEntry 44 49 = vasyuninBEntry 44 49 := vasyuninBEntry_correct_axiom 44 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_44_49_eval :
    ((((11662747/472530000) : ℚ) : ℝ) ≤ vasyuninBEntry 44 49) ∧
    (vasyuninBEntry 44 49 ≤ (((11757253/472530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4449_formula_bound
  constructor <;> linarith

theorem G44_49_interval :
    ((((11662747/472530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 49) ∧
    (baezDuarteGramEntry 44 49 ≤ (((11757253/472530000) : ℚ) : ℝ)) := by
  rw [G44_49_formula]
  exact vasyuninBEntry_44_49_eval

def interval_44_49 : NamedVasyuninInterval :=
{
  h := 44
  k := 49
  lower := (11662747/472530000)
  upper := (11757253/472530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_49_interval
}

theorem G44_50_formula : baezDuarteGramEntry 44 50 = vasyuninBEntry 44 50 := vasyuninBEntry_correct_axiom 44 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_44_50_eval :
    ((((11875939/490610000) : ℚ) : ℝ) ≤ vasyuninBEntry 44 50) ∧
    (vasyuninBEntry 44 50 ≤ (((11974061/490610000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_22_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 22 25 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G44_50_interval :
    ((((11875939/490610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 44 50) ∧
    (baezDuarteGramEntry 44 50 ≤ (((11974061/490610000) : ℚ) : ℝ)) := by
  rw [G44_50_formula]
  exact vasyuninBEntry_44_50_eval

def interval_44_50 : NamedVasyuninInterval :=
{
  h := 44
  k := 50
  lower := (11875939/490610000)
  upper := (11974061/490610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G44_50_interval
}

theorem G45_1_formula : baezDuarteGramEntry 45 1 = vasyuninBEntry 1 45 := by
  rw [baezDuarteGramEntry_symm 45 1]
  exact G1_45_formula

theorem G45_1_interval :
    ((((58483207/867930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 1) ∧
    (baezDuarteGramEntry 45 1 ≤ (((58656793/867930000) : ℚ) : ℝ)) := by
  rw [G45_1_formula]
  exact vasyuninBEntry_1_45_eval

def interval_45_1 : NamedVasyuninInterval :=
{
  h := 45
  k := 1
  lower := (58483207/867930000)
  upper := (58656793/867930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_1_interval
}

theorem G45_2_formula : baezDuarteGramEntry 45 2 = vasyuninBEntry 2 45 := by
  rw [baezDuarteGramEntry_symm 45 2]
  exact G2_45_formula

theorem G45_2_interval :
    ((((56764751/952490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 2) ∧
    (baezDuarteGramEntry 45 2 ≤ (((56955249/952490000) : ℚ) : ℝ)) := by
  rw [G45_2_formula]
  exact vasyuninBEntry_2_45_eval

def interval_45_2 : NamedVasyuninInterval :=
{
  h := 45
  k := 2
  lower := (56764751/952490000)
  upper := (56955249/952490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_2_interval
}

theorem G45_3_formula : baezDuarteGramEntry 45 3 = vasyuninBEntry 3 45 := by
  rw [baezDuarteGramEntry_symm 45 3]
  exact G3_45_formula

theorem G45_3_interval :
    ((((53752817/971830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 3) ∧
    (baezDuarteGramEntry 45 3 ≤ (((53947183/971830000) : ℚ) : ℝ)) := by
  rw [G45_3_formula]
  exact vasyuninBEntry_3_45_eval

def interval_45_3 : NamedVasyuninInterval :=
{
  h := 45
  k := 3
  lower := (53752817/971830000)
  upper := (53947183/971830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_3_interval
}

theorem G45_4_formula : baezDuarteGramEntry 45 4 = vasyuninBEntry 4 45 := by
  rw [baezDuarteGramEntry_symm 45 4]
  exact G4_45_formula

theorem G45_4_interval :
    ((((21338869/411310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 4) ∧
    (baezDuarteGramEntry 45 4 ≤ (((21421131/411310000) : ℚ) : ℝ)) := by
  rw [G45_4_formula]
  exact vasyuninBEntry_4_45_eval

def interval_45_4 : NamedVasyuninInterval :=
{
  h := 45
  k := 4
  lower := (21338869/411310000)
  upper := (21421131/411310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_4_interval
}

theorem G45_5_formula : baezDuarteGramEntry 45 5 = vasyuninBEntry 5 45 := by
  rw [baezDuarteGramEntry_symm 45 5]
  exact G5_45_formula

theorem G45_5_interval :
    ((((44690207/897930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 5) ∧
    (baezDuarteGramEntry 45 5 ≤ (((44869793/897930000) : ℚ) : ℝ)) := by
  rw [G45_5_formula]
  exact vasyuninBEntry_5_45_eval

def interval_45_5 : NamedVasyuninInterval :=
{
  h := 45
  k := 5
  lower := (44690207/897930000)
  upper := (44869793/897930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_5_interval
}

theorem G45_6_formula : baezDuarteGramEntry 45 6 = vasyuninBEntry 6 45 := by
  rw [baezDuarteGramEntry_symm 45 6]
  exact G6_45_formula

theorem G45_6_interval :
    ((((8394773/177270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 6) ∧
    (baezDuarteGramEntry 45 6 ≤ (((8430227/177270000) : ℚ) : ℝ)) := by
  rw [G45_6_formula]
  exact vasyuninBEntry_6_45_eval

def interval_45_6 : NamedVasyuninInterval :=
{
  h := 45
  k := 6
  lower := (8394773/177270000)
  upper := (8430227/177270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_6_interval
}

theorem G45_7_formula : baezDuarteGramEntry 45 7 = vasyuninBEntry 7 45 := by
  rw [baezDuarteGramEntry_symm 45 7]
  exact G7_45_formula

theorem G45_7_interval :
    ((((4649797/102030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 7) ∧
    (baezDuarteGramEntry 45 7 ≤ (((4670203/102030000) : ℚ) : ℝ)) := by
  rw [G45_7_formula]
  exact vasyuninBEntry_7_45_eval

def interval_45_7 : NamedVasyuninInterval :=
{
  h := 45
  k := 7
  lower := (4649797/102030000)
  upper := (4670203/102030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_7_interval
}

theorem G45_8_formula : baezDuarteGramEntry 45 8 = vasyuninBEntry 8 45 := by
  rw [baezDuarteGramEntry_symm 45 8]
  exact G8_45_formula

theorem G45_8_interval :
    ((((3411259/77410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 8) ∧
    (baezDuarteGramEntry 45 8 ≤ (((3426741/77410000) : ℚ) : ℝ)) := by
  rw [G45_8_formula]
  exact vasyuninBEntry_8_45_eval

def interval_45_8 : NamedVasyuninInterval :=
{
  h := 45
  k := 8
  lower := (3411259/77410000)
  upper := (3426741/77410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_8_interval
}

theorem G45_9_formula : baezDuarteGramEntry 45 9 = vasyuninBEntry 9 45 := by
  rw [baezDuarteGramEntry_symm 45 9]
  exact G9_45_formula

theorem G45_9_interval :
    ((((42761717/982830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 9) ∧
    (baezDuarteGramEntry 45 9 ≤ (((42958283/982830000) : ℚ) : ℝ)) := by
  rw [G45_9_formula]
  exact vasyuninBEntry_9_45_eval

def interval_45_9 : NamedVasyuninInterval :=
{
  h := 45
  k := 9
  lower := (42761717/982830000)
  upper := (42958283/982830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_9_interval
}

theorem G45_10_formula : baezDuarteGramEntry 45 10 = vasyuninBEntry 10 45 := by
  rw [baezDuarteGramEntry_symm 45 10]
  exact G10_45_formula

theorem G45_10_interval :
    ((((1503889/36110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 10) ∧
    (baezDuarteGramEntry 45 10 ≤ (((1511111/36110000) : ℚ) : ℝ)) := by
  rw [G45_10_formula]
  exact vasyuninBEntry_10_45_eval

def interval_45_10 : NamedVasyuninInterval :=
{
  h := 45
  k := 10
  lower := (1503889/36110000)
  upper := (1511111/36110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_10_interval
}

theorem G45_11_formula : baezDuarteGramEntry 45 11 = vasyuninBEntry 11 45 := by
  rw [baezDuarteGramEntry_symm 45 11]
  exact G11_45_formula

theorem G45_11_interval :
    ((((35273743/862570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 11) ∧
    (baezDuarteGramEntry 45 11 ≤ (((35446257/862570000) : ℚ) : ℝ)) := by
  rw [G45_11_formula]
  exact vasyuninBEntry_11_45_eval

def interval_45_11 : NamedVasyuninInterval :=
{
  h := 45
  k := 11
  lower := (35273743/862570000)
  upper := (35446257/862570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_11_interval
}

theorem G45_12_formula : baezDuarteGramEntry 45 12 = vasyuninBEntry 12 45 := by
  rw [baezDuarteGramEntry_symm 45 12]
  exact G12_45_formula

theorem G45_12_interval :
    ((((24099113/608870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 12) ∧
    (baezDuarteGramEntry 45 12 ≤ (((24220887/608870000) : ℚ) : ℝ)) := by
  rw [G45_12_formula]
  exact vasyuninBEntry_12_45_eval

def interval_45_12 : NamedVasyuninInterval :=
{
  h := 45
  k := 12
  lower := (24099113/608870000)
  upper := (24220887/608870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_12_interval
}

theorem G45_13_formula : baezDuarteGramEntry 45 13 = vasyuninBEntry 13 45 := by
  rw [baezDuarteGramEntry_symm 45 13]
  exact G13_45_formula

theorem G45_13_interval :
    ((((4076941/105590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 13) ∧
    (baezDuarteGramEntry 45 13 ≤ (((4098059/105590000) : ℚ) : ℝ)) := by
  rw [G45_13_formula]
  exact vasyuninBEntry_13_45_eval

def interval_45_13 : NamedVasyuninInterval :=
{
  h := 45
  k := 13
  lower := (4076941/105590000)
  upper := (4098059/105590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_13_interval
}

theorem G45_14_formula : baezDuarteGramEntry 45 14 = vasyuninBEntry 14 45 := by
  rw [baezDuarteGramEntry_symm 45 14]
  exact G14_45_formula

theorem G45_14_interval :
    ((((8871619/233810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 14) ∧
    (baezDuarteGramEntry 45 14 ≤ (((8918381/233810000) : ℚ) : ℝ)) := by
  rw [G45_14_formula]
  exact vasyuninBEntry_14_45_eval

def interval_45_14 : NamedVasyuninInterval :=
{
  h := 45
  k := 14
  lower := (8871619/233810000)
  upper := (8918381/233810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_14_interval
}

theorem G45_15_formula : baezDuarteGramEntry 45 15 = vasyuninBEntry 15 45 := by
  rw [baezDuarteGramEntry_symm 45 15]
  exact G15_45_formula

theorem G45_15_interval :
    ((((2757787/72130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 15) ∧
    (baezDuarteGramEntry 45 15 ≤ (((2772213/72130000) : ℚ) : ℝ)) := by
  rw [G45_15_formula]
  exact vasyuninBEntry_15_45_eval

def interval_45_15 : NamedVasyuninInterval :=
{
  h := 45
  k := 15
  lower := (2757787/72130000)
  upper := (2772213/72130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_15_interval
}

theorem G45_16_formula : baezDuarteGramEntry 45 16 = vasyuninBEntry 16 45 := by
  rw [baezDuarteGramEntry_symm 45 16]
  exact G16_45_formula

theorem G45_16_interval :
    ((((6534561/179390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 16) ∧
    (baezDuarteGramEntry 45 16 ≤ (((6570439/179390000) : ℚ) : ℝ)) := by
  rw [G45_16_formula]
  exact vasyuninBEntry_16_45_eval

def interval_45_16 : NamedVasyuninInterval :=
{
  h := 45
  k := 16
  lower := (6534561/179390000)
  upper := (6570439/179390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_16_interval
}

theorem G45_17_formula : baezDuarteGramEntry 45 17 = vasyuninBEntry 17 45 := by
  rw [baezDuarteGramEntry_symm 45 17]
  exact G17_45_formula

theorem G45_17_interval :
    ((((25388563/714370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 17) ∧
    (baezDuarteGramEntry 45 17 ≤ (((25531437/714370000) : ℚ) : ℝ)) := by
  rw [G45_17_formula]
  exact vasyuninBEntry_17_45_eval

def interval_45_17 : NamedVasyuninInterval :=
{
  h := 45
  k := 17
  lower := (25388563/714370000)
  upper := (25531437/714370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_17_interval
}

theorem G45_18_formula : baezDuarteGramEntry 45 18 = vasyuninBEntry 18 45 := by
  rw [baezDuarteGramEntry_symm 45 18]
  exact G18_45_formula

theorem G45_18_interval :
    ((((12135383/346170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 18) ∧
    (baezDuarteGramEntry 45 18 ≤ (((12204617/346170000) : ℚ) : ℝ)) := by
  rw [G45_18_formula]
  exact vasyuninBEntry_18_45_eval

def interval_45_18 : NamedVasyuninInterval :=
{
  h := 45
  k := 18
  lower := (12135383/346170000)
  upper := (12204617/346170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_18_interval
}

theorem G45_19_formula : baezDuarteGramEntry 45 19 = vasyuninBEntry 19 45 := by
  rw [baezDuarteGramEntry_symm 45 19]
  exact G19_45_formula

theorem G45_19_interval :
    ((((1547989/45110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 19) ∧
    (baezDuarteGramEntry 45 19 ≤ (((1557011/45110000) : ℚ) : ℝ)) := by
  rw [G45_19_formula]
  exact vasyuninBEntry_19_45_eval

def interval_45_19 : NamedVasyuninInterval :=
{
  h := 45
  k := 19
  lower := (1547989/45110000)
  upper := (1557011/45110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_19_interval
}

theorem G45_20_formula : baezDuarteGramEntry 45 20 = vasyuninBEntry 20 45 := by
  rw [baezDuarteGramEntry_symm 45 20]
  exact G20_45_formula

theorem G45_20_interval :
    ((((537017/15830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 20) ∧
    (baezDuarteGramEntry 45 20 ≤ (((540183/15830000) : ℚ) : ℝ)) := by
  rw [G45_20_formula]
  exact vasyuninBEntry_20_45_eval

def interval_45_20 : NamedVasyuninInterval :=
{
  h := 45
  k := 20
  lower := (537017/15830000)
  upper := (540183/15830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_20_interval
}

theorem G45_21_formula : baezDuarteGramEntry 45 21 = vasyuninBEntry 21 45 := by
  rw [baezDuarteGramEntry_symm 45 21]
  exact G21_45_formula

theorem G45_21_interval :
    ((((28874263/857370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 21) ∧
    (baezDuarteGramEntry 45 21 ≤ (((29045737/857370000) : ℚ) : ℝ)) := by
  rw [G45_21_formula]
  exact vasyuninBEntry_21_45_eval

def interval_45_21 : NamedVasyuninInterval :=
{
  h := 45
  k := 21
  lower := (28874263/857370000)
  upper := (29045737/857370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_21_interval
}

theorem G45_22_formula : baezDuarteGramEntry 45 22 = vasyuninBEntry 22 45 := by
  rw [baezDuarteGramEntry_symm 45 22]
  exact G22_45_formula

theorem G45_22_interval :
    ((((241239/7141250) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 22) ∧
    (baezDuarteGramEntry 45 22 ≤ (((970669/28565000) : ℚ) : ℝ)) := by
  rw [G45_22_formula]
  exact vasyuninBEntry_22_45_eval

def interval_45_22 : NamedVasyuninInterval :=
{
  h := 45
  k := 22
  lower := (241239/7141250)
  upper := (970669/28565000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_22_interval
}

theorem G45_23_formula : baezDuarteGramEntry 45 23 = vasyuninBEntry 23 45 := by
  rw [baezDuarteGramEntry_symm 45 23]
  exact G23_45_formula

theorem G45_23_interval :
    ((((30757487/925130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 23) ∧
    (baezDuarteGramEntry 45 23 ≤ (((30942513/925130000) : ℚ) : ℝ)) := by
  rw [G45_23_formula]
  exact vasyuninBEntry_23_45_eval

def interval_45_23 : NamedVasyuninInterval :=
{
  h := 45
  k := 23
  lower := (30757487/925130000)
  upper := (30942513/925130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_23_interval
}

theorem G45_24_formula : baezDuarteGramEntry 45 24 = vasyuninBEntry 24 45 := by
  rw [baezDuarteGramEntry_symm 45 24]
  exact G24_45_formula

theorem G45_24_interval :
    ((((13054367/406330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 24) ∧
    (baezDuarteGramEntry 45 24 ≤ (((13135633/406330000) : ℚ) : ℝ)) := by
  rw [G45_24_formula]
  exact vasyuninBEntry_24_45_eval

def interval_45_24 : NamedVasyuninInterval :=
{
  h := 45
  k := 24
  lower := (13054367/406330000)
  upper := (13135633/406330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_24_interval
}

theorem G45_25_formula : baezDuarteGramEntry 45 25 = vasyuninBEntry 25 45 := by
  rw [baezDuarteGramEntry_symm 45 25]
  exact G25_45_formula

theorem G45_25_interval :
    ((((3437039/109610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 25) ∧
    (baezDuarteGramEntry 45 25 ≤ (((3458961/109610000) : ℚ) : ℝ)) := by
  rw [G45_25_formula]
  exact vasyuninBEntry_25_45_eval

def interval_45_25 : NamedVasyuninInterval :=
{
  h := 45
  k := 25
  lower := (3437039/109610000)
  upper := (3458961/109610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_25_interval
}

theorem G45_26_formula : baezDuarteGramEntry 45 26 = vasyuninBEntry 26 45 := by
  rw [baezDuarteGramEntry_symm 45 26]
  exact G26_45_formula

theorem G45_26_interval :
    ((((14637361/476390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 26) ∧
    (baezDuarteGramEntry 45 26 ≤ (((14732639/476390000) : ℚ) : ℝ)) := by
  rw [G45_26_formula]
  exact vasyuninBEntry_26_45_eval

def interval_45_26 : NamedVasyuninInterval :=
{
  h := 45
  k := 26
  lower := (14637361/476390000)
  upper := (14732639/476390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_26_interval
}

theorem G45_27_formula : baezDuarteGramEntry 45 27 = vasyuninBEntry 27 45 := by
  rw [baezDuarteGramEntry_symm 45 27]
  exact G27_45_formula

theorem G45_27_interval :
    ((((30290017/999830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 27) ∧
    (baezDuarteGramEntry 45 27 ≤ (((30489983/999830000) : ℚ) : ℝ)) := by
  rw [G45_27_formula]
  exact vasyuninBEntry_27_45_eval

def interval_45_27 : NamedVasyuninInterval :=
{
  h := 45
  k := 27
  lower := (30290017/999830000)
  upper := (30489983/999830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_27_interval
}

theorem G45_28_formula : baezDuarteGramEntry 45 28 = vasyuninBEntry 28 45 := by
  rw [baezDuarteGramEntry_symm 45 28]
  exact G28_45_formula

theorem G45_28_interval :
    ((((13135873/441270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 28) ∧
    (baezDuarteGramEntry 45 28 ≤ (((13224127/441270000) : ℚ) : ℝ)) := by
  rw [G45_28_formula]
  exact vasyuninBEntry_28_45_eval

def interval_45_28 : NamedVasyuninInterval :=
{
  h := 45
  k := 28
  lower := (13135873/441270000)
  upper := (13224127/441270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_28_interval
}

theorem G45_29_formula : baezDuarteGramEntry 45 29 = vasyuninBEntry 29 45 := by
  rw [baezDuarteGramEntry_symm 45 29]
  exact G29_45_formula

theorem G45_29_interval :
    ((((9517639/323610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 29) ∧
    (baezDuarteGramEntry 45 29 ≤ (((9582361/323610000) : ℚ) : ℝ)) := by
  rw [G45_29_formula]
  exact vasyuninBEntry_29_45_eval

def interval_45_29 : NamedVasyuninInterval :=
{
  h := 45
  k := 29
  lower := (9517639/323610000)
  upper := (9582361/323610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_29_interval
}

theorem G45_30_formula : baezDuarteGramEntry 45 30 = vasyuninBEntry 30 45 := by
  rw [baezDuarteGramEntry_symm 45 30]
  exact G30_45_formula

theorem G45_30_interval :
    ((((14176627/483730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 30) ∧
    (baezDuarteGramEntry 45 30 ≤ (((14273373/483730000) : ℚ) : ℝ)) := by
  rw [G45_30_formula]
  exact vasyuninBEntry_30_45_eval

def interval_45_30 : NamedVasyuninInterval :=
{
  h := 45
  k := 30
  lower := (14176627/483730000)
  upper := (14273373/483730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_30_interval
}

theorem G45_31_formula : baezDuarteGramEntry 45 31 = vasyuninBEntry 31 45 := by
  rw [baezDuarteGramEntry_symm 45 31]
  exact G31_45_formula

theorem G45_31_interval :
    ((((4934803/171970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 31) ∧
    (baezDuarteGramEntry 45 31 ≤ (((4969197/171970000) : ℚ) : ℝ)) := by
  rw [G45_31_formula]
  exact vasyuninBEntry_31_45_eval

def interval_45_31 : NamedVasyuninInterval :=
{
  h := 45
  k := 31
  lower := (4934803/171970000)
  upper := (4969197/171970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_31_interval
}

theorem G45_32_formula : baezDuarteGramEntry 45 32 = vasyuninBEntry 32 45 := by
  rw [baezDuarteGramEntry_symm 45 32]
  exact G32_45_formula

theorem G45_32_interval :
    ((((4372567/154330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 32) ∧
    (baezDuarteGramEntry 45 32 ≤ (((4403433/154330000) : ℚ) : ℝ)) := by
  rw [G45_32_formula]
  exact vasyuninBEntry_32_45_eval

def interval_45_32 : NamedVasyuninInterval :=
{
  h := 45
  k := 32
  lower := (4372567/154330000)
  upper := (4403433/154330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_32_interval
}

theorem G45_33_formula : baezDuarteGramEntry 45 33 = vasyuninBEntry 33 45 := by
  rw [baezDuarteGramEntry_symm 45 33]
  exact G33_45_formula

theorem G45_33_interval :
    ((((64987/2317500) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 33) ∧
    (baezDuarteGramEntry 45 33 ≤ (((130901/4635000) : ℚ) : ℝ)) := by
  rw [G45_33_formula]
  exact vasyuninBEntry_33_45_eval

def interval_45_33 : NamedVasyuninInterval :=
{
  h := 45
  k := 33
  lower := (64987/2317500)
  upper := (130901/4635000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_33_interval
}

theorem G45_34_formula : baezDuarteGramEntry 45 34 = vasyuninBEntry 34 45 := by
  rw [baezDuarteGramEntry_symm 45 34]
  exact G34_45_formula

theorem G45_34_interval :
    ((((305153/10970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 34) ∧
    (baezDuarteGramEntry 45 34 ≤ (((307347/10970000) : ℚ) : ℝ)) := by
  rw [G45_34_formula]
  exact vasyuninBEntry_34_45_eval

def interval_45_34 : NamedVasyuninInterval :=
{
  h := 45
  k := 34
  lower := (305153/10970000)
  upper := (307347/10970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_34_interval
}

theorem G45_35_formula : baezDuarteGramEntry 45 35 = vasyuninBEntry 35 45 := by
  rw [baezDuarteGramEntry_symm 45 35]
  exact G35_45_formula

theorem G45_35_interval :
    ((((3816147/138530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 35) ∧
    (baezDuarteGramEntry 45 35 ≤ (((3843853/138530000) : ℚ) : ℝ)) := by
  rw [G45_35_formula]
  exact vasyuninBEntry_35_45_eval

def interval_45_35 : NamedVasyuninInterval :=
{
  h := 45
  k := 35
  lower := (3816147/138530000)
  upper := (3843853/138530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_35_interval
}

theorem G45_36_formula : baezDuarteGramEntry 45 36 = vasyuninBEntry 36 45 := by
  rw [baezDuarteGramEntry_symm 45 36]
  exact G36_45_formula

theorem G45_36_interval :
    ((((20794071/759290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 36) ∧
    (baezDuarteGramEntry 45 36 ≤ (((20945929/759290000) : ℚ) : ℝ)) := by
  rw [G45_36_formula]
  exact vasyuninBEntry_36_45_eval

def interval_45_36 : NamedVasyuninInterval :=
{
  h := 45
  k := 36
  lower := (20794071/759290000)
  upper := (20945929/759290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_36_interval
}

theorem G45_37_formula : baezDuarteGramEntry 45 37 = vasyuninBEntry 37 45 := by
  rw [baezDuarteGramEntry_symm 45 37]
  exact G37_45_formula

theorem G45_37_interval :
    ((((4700201/172990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 37) ∧
    (baezDuarteGramEntry 45 37 ≤ (((4734799/172990000) : ℚ) : ℝ)) := by
  rw [G45_37_formula]
  exact vasyuninBEntry_37_45_eval

def interval_45_37 : NamedVasyuninInterval :=
{
  h := 45
  k := 37
  lower := (4700201/172990000)
  upper := (4734799/172990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_37_interval
}

theorem G45_38_formula : baezDuarteGramEntry 45 38 = vasyuninBEntry 38 45 := by
  rw [baezDuarteGramEntry_symm 45 38]
  exact G38_45_formula

theorem G45_38_interval :
    ((((18421867/681330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 38) ∧
    (baezDuarteGramEntry 45 38 ≤ (((18558133/681330000) : ℚ) : ℝ)) := by
  rw [G45_38_formula]
  exact vasyuninBEntry_38_45_eval

def interval_45_38 : NamedVasyuninInterval :=
{
  h := 45
  k := 38
  lower := (18421867/681330000)
  upper := (18558133/681330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_38_interval
}

theorem G45_39_formula : baezDuarteGramEntry 45 39 = vasyuninBEntry 39 45 := by
  rw [baezDuarteGramEntry_symm 45 39]
  exact G39_45_formula

theorem G45_39_interval :
    ((((6329011/234890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 39) ∧
    (baezDuarteGramEntry 45 39 ≤ (((6375989/234890000) : ℚ) : ℝ)) := by
  rw [G45_39_formula]
  exact vasyuninBEntry_39_45_eval

def interval_45_39 : NamedVasyuninInterval :=
{
  h := 45
  k := 39
  lower := (6329011/234890000)
  upper := (6375989/234890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_39_interval
}

theorem G45_40_formula : baezDuarteGramEntry 45 40 = vasyuninBEntry 40 45 := by
  rw [baezDuarteGramEntry_symm 45 40]
  exact G40_45_formula

theorem G45_40_interval :
    ((((14685403/545970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 40) ∧
    (baezDuarteGramEntry 45 40 ≤ (((14794597/545970000) : ℚ) : ℝ)) := by
  rw [G45_40_formula]
  exact vasyuninBEntry_40_45_eval

def interval_45_40 : NamedVasyuninInterval :=
{
  h := 45
  k := 40
  lower := (14685403/545970000)
  upper := (14794597/545970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_40_interval
}

theorem G45_41_formula : baezDuarteGramEntry 45 41 = vasyuninBEntry 41 45 := by
  rw [baezDuarteGramEntry_symm 45 41]
  exact G41_45_formula

theorem G45_41_interval :
    ((((3708209/137910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 41) ∧
    (baezDuarteGramEntry 45 41 ≤ (((3735791/137910000) : ℚ) : ℝ)) := by
  rw [G45_41_formula]
  exact vasyuninBEntry_41_45_eval

def interval_45_41 : NamedVasyuninInterval :=
{
  h := 45
  k := 41
  lower := (3708209/137910000)
  upper := (3735791/137910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_41_interval
}

theorem G45_42_formula : baezDuarteGramEntry 45 42 = vasyuninBEntry 42 45 := by
  rw [baezDuarteGramEntry_symm 45 42]
  exact G42_45_formula

theorem G45_42_interval :
    ((((16339363/606370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 42) ∧
    (baezDuarteGramEntry 45 42 ≤ (((16460637/606370000) : ℚ) : ℝ)) := by
  rw [G45_42_formula]
  exact vasyuninBEntry_42_45_eval

def interval_45_42 : NamedVasyuninInterval :=
{
  h := 45
  k := 42
  lower := (16339363/606370000)
  upper := (16460637/606370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_42_interval
}

theorem G45_43_formula : baezDuarteGramEntry 45 43 = vasyuninBEntry 43 45 := by
  rw [baezDuarteGramEntry_symm 45 43]
  exact G43_45_formula

theorem G45_43_interval :
    ((((7512259/277410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 43) ∧
    (baezDuarteGramEntry 45 43 ≤ (((7567741/277410000) : ℚ) : ℝ)) := by
  rw [G45_43_formula]
  exact vasyuninBEntry_43_45_eval

def interval_45_43 : NamedVasyuninInterval :=
{
  h := 45
  k := 43
  lower := (7512259/277410000)
  upper := (7567741/277410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_43_interval
}

theorem G45_44_formula : baezDuarteGramEntry 45 44 = vasyuninBEntry 44 45 := by
  rw [baezDuarteGramEntry_symm 45 44]
  exact G44_45_formula

theorem G45_44_interval :
    ((((2944229/107710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 44) ∧
    (baezDuarteGramEntry 45 44 ≤ (((2965771/107710000) : ℚ) : ℝ)) := by
  rw [G45_44_formula]
  exact vasyuninBEntry_44_45_eval

def interval_45_44 : NamedVasyuninInterval :=
{
  h := 45
  k := 44
  lower := (2944229/107710000)
  upper := (2965771/107710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_44_interval
}

theorem G45_45_formula_eq : baezDuarteGramEntry 45 45 = (1 / (45 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 45 := by norm_num
  rw [baez_duarte_diagonal_scaling 45 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G45_45_log_gamma_interval :
  ((((2507019/89810000) : ℚ) : ℝ) ≤ (1 / (45 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (45 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((2524981/89810000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 45 (by norm_num)
  constructor
  · have : ((((2507019/89810000) : ℚ) : ℝ) ≤ (1 / (45 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (45 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((2524981/89810000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G45_45_interval : ((((2507019/89810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 45) ∧ (baezDuarteGramEntry 45 45 ≤ (((2524981/89810000) : ℚ) : ℝ)) := by
  rw [G45_45_formula_eq]
  exact G45_45_log_gamma_interval

def interval_45_45 : NamedVasyuninInterval :=
{
  h := 45
  k := 45
  lower := (2507019/89810000)
  upper := (2524981/89810000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G45_45_interval
}

theorem G45_46_formula : baezDuarteGramEntry 45 46 = vasyuninBEntry 45 46 := vasyuninBEntry_correct_axiom 45 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_45_46_eval :
    ((((2506877/93730000) : ℚ) : ℝ) ≤ vasyuninBEntry 45 46) ∧
    (vasyuninBEntry 45 46 ≤ (((2525623/93730000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4546_formula_bound
  constructor <;> linarith

theorem G45_46_interval :
    ((((2506877/93730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 46) ∧
    (baezDuarteGramEntry 45 46 ≤ (((2525623/93730000) : ℚ) : ℝ)) := by
  rw [G45_46_formula]
  exact vasyuninBEntry_45_46_eval

def interval_45_46 : NamedVasyuninInterval :=
{
  h := 45
  k := 46
  lower := (2506877/93730000)
  upper := (2525623/93730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_46_interval
}

theorem G45_47_formula : baezDuarteGramEntry 45 47 = vasyuninBEntry 45 47 := vasyuninBEntry_correct_axiom 45 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_45_47_eval :
    ((((6186151/238490000) : ℚ) : ℝ) ≤ vasyuninBEntry 45 47) ∧
    (vasyuninBEntry 45 47 ≤ (((6233849/238490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4547_formula_bound
  constructor <;> linarith

theorem G45_47_interval :
    ((((6186151/238490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 47) ∧
    (baezDuarteGramEntry 45 47 ≤ (((6233849/238490000) : ℚ) : ℝ)) := by
  rw [G45_47_formula]
  exact vasyuninBEntry_45_47_eval

def interval_45_47 : NamedVasyuninInterval :=
{
  h := 45
  k := 47
  lower := (6186151/238490000)
  upper := (6233849/238490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_47_interval
}

theorem G45_48_formula : baezDuarteGramEntry 45 48 = vasyuninBEntry 45 48 := vasyuninBEntry_correct_axiom 45 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_45_48_eval :
    ((((2557879/101210000) : ℚ) : ℝ) ≤ vasyuninBEntry 45 48) ∧
    (vasyuninBEntry 45 48 ≤ (((2578121/101210000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_15_16_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 15 16 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G45_48_interval :
    ((((2557879/101210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 48) ∧
    (baezDuarteGramEntry 45 48 ≤ (((2578121/101210000) : ℚ) : ℝ)) := by
  rw [G45_48_formula]
  exact vasyuninBEntry_45_48_eval

def interval_45_48 : NamedVasyuninInterval :=
{
  h := 45
  k := 48
  lower := (2557879/101210000)
  upper := (2578121/101210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_48_interval
}

theorem G45_49_formula : baezDuarteGramEntry 45 49 = vasyuninBEntry 45 49 := vasyuninBEntry_correct_axiom 45 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_45_49_eval :
    ((((6558443/265570000) : ℚ) : ℝ) ≤ vasyuninBEntry 45 49) ∧
    (vasyuninBEntry 45 49 ≤ (((6611557/265570000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4549_formula_bound
  constructor <;> linarith

theorem G45_49_interval :
    ((((6558443/265570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 49) ∧
    (baezDuarteGramEntry 45 49 ≤ (((6611557/265570000) : ℚ) : ℝ)) := by
  rw [G45_49_formula]
  exact vasyuninBEntry_45_49_eval

def interval_45_49 : NamedVasyuninInterval :=
{
  h := 45
  k := 49
  lower := (6558443/265570000)
  upper := (6611557/265570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_49_interval
}

theorem G45_50_formula : baezDuarteGramEntry 45 50 = vasyuninBEntry 45 50 := vasyuninBEntry_correct_axiom 45 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_45_50_eval :
    ((((24060531/994690000) : ℚ) : ℝ) ≤ vasyuninBEntry 45 50) ∧
    (vasyuninBEntry 45 50 ≤ (((24259469/994690000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 10 5 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G45_50_interval :
    ((((24060531/994690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 45 50) ∧
    (baezDuarteGramEntry 45 50 ≤ (((24259469/994690000) : ℚ) : ℝ)) := by
  rw [G45_50_formula]
  exact vasyuninBEntry_45_50_eval

def interval_45_50 : NamedVasyuninInterval :=
{
  h := 45
  k := 50
  lower := (24060531/994690000)
  upper := (24259469/994690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G45_50_interval
}

theorem G46_1_formula : baezDuarteGramEntry 46 1 = vasyuninBEntry 1 46 := by
  rw [baezDuarteGramEntry_symm 46 1]
  exact G1_46_formula

theorem G46_1_interval :
    ((((25791013/389870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 1) ∧
    (baezDuarteGramEntry 46 1 ≤ (((25868987/389870000) : ℚ) : ℝ)) := by
  rw [G46_1_formula]
  exact vasyuninBEntry_1_46_eval

def interval_46_1 : NamedVasyuninInterval :=
{
  h := 46
  k := 1
  lower := (25791013/389870000)
  upper := (25868987/389870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_1_interval
}

theorem G46_2_formula : baezDuarteGramEntry 46 2 = vasyuninBEntry 2 46 := by
  rw [baezDuarteGramEntry_symm 46 2]
  exact G2_46_formula

theorem G46_2_interval :
    ((((28825879/491210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 2) ∧
    (baezDuarteGramEntry 46 2 ≤ (((28924121/491210000) : ℚ) : ℝ)) := by
  rw [G46_2_formula]
  exact vasyuninBEntry_2_46_eval

def interval_46_2 : NamedVasyuninInterval :=
{
  h := 46
  k := 2
  lower := (28825879/491210000)
  upper := (28924121/491210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_2_interval
}

theorem G46_3_formula : baezDuarteGramEntry 46 3 = vasyuninBEntry 3 46 := by
  rw [baezDuarteGramEntry_symm 46 3]
  exact G3_46_formula

theorem G46_3_interval :
    ((((21989363/406370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 3) ∧
    (baezDuarteGramEntry 46 3 ≤ (((22070637/406370000) : ℚ) : ℝ)) := by
  rw [G46_3_formula]
  exact vasyuninBEntry_3_46_eval

def interval_46_3 : NamedVasyuninInterval :=
{
  h := 46
  k := 3
  lower := (21989363/406370000)
  upper := (22070637/406370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_3_interval
}

theorem G46_4_formula : baezDuarteGramEntry 46 4 = vasyuninBEntry 4 46 := by
  rw [baezDuarteGramEntry_symm 46 4]
  exact G4_46_formula

theorem G46_4_interval :
    ((((50431091/989090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 4) ∧
    (baezDuarteGramEntry 46 4 ≤ (((50628909/989090000) : ℚ) : ℝ)) := by
  rw [G46_4_formula]
  exact vasyuninBEntry_4_46_eval

def interval_46_4 : NamedVasyuninInterval :=
{
  h := 46
  k := 4
  lower := (50431091/989090000)
  upper := (50628909/989090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_4_interval
}

theorem G46_5_formula : baezDuarteGramEntry 46 5 = vasyuninBEntry 5 46 := by
  rw [baezDuarteGramEntry_symm 46 5]
  exact G5_46_formula

theorem G46_5_interval :
    ((((11670977/240230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 5) ∧
    (baezDuarteGramEntry 46 5 ≤ (((11719023/240230000) : ℚ) : ℝ)) := by
  rw [G46_5_formula]
  exact vasyuninBEntry_5_46_eval

def interval_46_5 : NamedVasyuninInterval :=
{
  h := 46
  k := 5
  lower := (11670977/240230000)
  upper := (11719023/240230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_5_interval
}

theorem G46_6_formula : baezDuarteGramEntry 46 6 = vasyuninBEntry 6 46 := by
  rw [baezDuarteGramEntry_symm 46 6]
  exact G6_46_formula

theorem G46_6_interval :
    ((((27790283/597170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 6) ∧
    (baezDuarteGramEntry 46 6 ≤ (((27909717/597170000) : ℚ) : ℝ)) := by
  rw [G46_6_formula]
  exact vasyuninBEntry_6_46_eval

def interval_46_6 : NamedVasyuninInterval :=
{
  h := 46
  k := 6
  lower := (27790283/597170000)
  upper := (27909717/597170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_6_interval
}

theorem G46_7_formula : baezDuarteGramEntry 46 7 = vasyuninBEntry 7 46 := by
  rw [baezDuarteGramEntry_symm 46 7]
  exact G7_46_formula

theorem G46_7_interval :
    ((((8715553/194470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 7) ∧
    (baezDuarteGramEntry 46 7 ≤ (((8754447/194470000) : ℚ) : ℝ)) := by
  rw [G46_7_formula]
  exact vasyuninBEntry_7_46_eval

def interval_46_7 : NamedVasyuninInterval :=
{
  h := 46
  k := 7
  lower := (8715553/194470000)
  upper := (8754447/194470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_7_interval
}

theorem G46_8_formula : baezDuarteGramEntry 46 8 = vasyuninBEntry 8 46 := by
  rw [baezDuarteGramEntry_symm 46 8]
  exact G8_46_formula

theorem G46_8_interval :
    ((((855629/19710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 8) ∧
    (baezDuarteGramEntry 46 8 ≤ (((859571/19710000) : ℚ) : ℝ)) := by
  rw [G46_8_formula]
  exact vasyuninBEntry_8_46_eval

def interval_46_8 : NamedVasyuninInterval :=
{
  h := 46
  k := 8
  lower := (855629/19710000)
  upper := (859571/19710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_8_interval
}

theorem G46_9_formula : baezDuarteGramEntry 46 9 = vasyuninBEntry 9 46 := by
  rw [baezDuarteGramEntry_symm 46 9]
  exact G9_46_formula

theorem G46_9_interval :
    ((((7140631/168690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 9) ∧
    (baezDuarteGramEntry 46 9 ≤ (((7174369/168690000) : ℚ) : ℝ)) := by
  rw [G46_9_formula]
  exact vasyuninBEntry_9_46_eval

def interval_46_9 : NamedVasyuninInterval :=
{
  h := 46
  k := 9
  lower := (7140631/168690000)
  upper := (7174369/168690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_9_interval
}

theorem G46_10_formula : baezDuarteGramEntry 46 10 = vasyuninBEntry 10 46 := by
  rw [baezDuarteGramEntry_symm 46 10]
  exact G10_46_formula

theorem G46_10_interval :
    ((((39124317/956830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 10) ∧
    (baezDuarteGramEntry 46 10 ≤ (((39315683/956830000) : ℚ) : ℝ)) := by
  rw [G46_10_formula]
  exact vasyuninBEntry_10_46_eval

def interval_46_10 : NamedVasyuninInterval :=
{
  h := 46
  k := 10
  lower := (39124317/956830000)
  upper := (39315683/956830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_10_interval
}

theorem G46_11_formula : baezDuarteGramEntry 46 11 = vasyuninBEntry 11 46 := by
  rw [baezDuarteGramEntry_symm 46 11]
  exact G11_46_formula

theorem G46_11_interval :
    ((((2041151/50990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 11) ∧
    (baezDuarteGramEntry 46 11 ≤ (((2051349/50990000) : ℚ) : ℝ)) := by
  rw [G46_11_formula]
  exact vasyuninBEntry_11_46_eval

def interval_46_11 : NamedVasyuninInterval :=
{
  h := 46
  k := 11
  lower := (2041151/50990000)
  upper := (2051349/50990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_11_interval
}

theorem G46_12_formula : baezDuarteGramEntry 46 12 = vasyuninBEntry 12 46 := by
  rw [baezDuarteGramEntry_symm 46 12]
  exact G12_46_formula

theorem G46_12_interval :
    ((((3750401/95990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 12) ∧
    (baezDuarteGramEntry 46 12 ≤ (((3769599/95990000) : ℚ) : ℝ)) := by
  rw [G46_12_formula]
  exact vasyuninBEntry_12_46_eval

def interval_46_12 : NamedVasyuninInterval :=
{
  h := 46
  k := 12
  lower := (3750401/95990000)
  upper := (3769599/95990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_12_interval
}

theorem G46_13_formula : baezDuarteGramEntry 46 13 = vasyuninBEntry 13 46 := by
  rw [baezDuarteGramEntry_symm 46 13]
  exact G13_46_formula

theorem G46_13_interval :
    ((((8293179/218210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 13) ∧
    (baezDuarteGramEntry 46 13 ≤ (((8336821/218210000) : ℚ) : ℝ)) := by
  rw [G46_13_formula]
  exact vasyuninBEntry_13_46_eval

def interval_46_13 : NamedVasyuninInterval :=
{
  h := 46
  k := 13
  lower := (8293179/218210000)
  upper := (8336821/218210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_13_interval
}

theorem G46_14_formula : baezDuarteGramEntry 46 14 = vasyuninBEntry 14 46 := by
  rw [baezDuarteGramEntry_symm 46 14]
  exact G14_46_formula

theorem G46_14_interval :
    ((((2808463/75370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 14) ∧
    (baezDuarteGramEntry 46 14 ≤ (((2823537/75370000) : ℚ) : ℝ)) := by
  rw [G46_14_formula]
  exact vasyuninBEntry_14_46_eval

def interval_46_14 : NamedVasyuninInterval :=
{
  h := 46
  k := 14
  lower := (2808463/75370000)
  upper := (2823537/75370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_14_interval
}

theorem G46_15_formula : baezDuarteGramEntry 46 15 = vasyuninBEntry 15 46 := by
  rw [baezDuarteGramEntry_symm 46 15]
  exact G15_46_formula

theorem G46_15_interval :
    ((((6163369/166310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 15) ∧
    (baezDuarteGramEntry 46 15 ≤ (((6196631/166310000) : ℚ) : ℝ)) := by
  rw [G46_15_formula]
  exact vasyuninBEntry_15_46_eval

def interval_46_15 : NamedVasyuninInterval :=
{
  h := 46
  k := 15
  lower := (6163369/166310000)
  upper := (6196631/166310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_15_interval
}

theorem G46_16_formula : baezDuarteGramEntry 46 16 = vasyuninBEntry 16 46 := by
  rw [baezDuarteGramEntry_symm 46 16]
  exact G16_46_formula

theorem G46_16_interval :
    ((((453941/12590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 16) ∧
    (baezDuarteGramEntry 46 16 ≤ (((456459/12590000) : ℚ) : ℝ)) := by
  rw [G46_16_formula]
  exact vasyuninBEntry_16_46_eval

def interval_46_16 : NamedVasyuninInterval :=
{
  h := 46
  k := 16
  lower := (453941/12590000)
  upper := (456459/12590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_16_interval
}

theorem G46_17_formula : baezDuarteGramEntry 46 17 = vasyuninBEntry 17 46 := by
  rw [baezDuarteGramEntry_symm 46 17]
  exact G17_46_formula

theorem G46_17_interval :
    ((((15490793/442070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 17) ∧
    (baezDuarteGramEntry 46 17 ≤ (((15579207/442070000) : ℚ) : ℝ)) := by
  rw [G46_17_formula]
  exact vasyuninBEntry_17_46_eval

def interval_46_17 : NamedVasyuninInterval :=
{
  h := 46
  k := 17
  lower := (15490793/442070000)
  upper := (15579207/442070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_17_interval
}

theorem G46_18_formula : baezDuarteGramEntry 46 18 = vasyuninBEntry 18 46 := by
  rw [baezDuarteGramEntry_symm 46 18]
  exact G18_46_formula

theorem G46_18_interval :
    ((((9133427/265730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 18) ∧
    (baezDuarteGramEntry 46 18 ≤ (((9186573/265730000) : ℚ) : ℝ)) := by
  rw [G46_18_formula]
  exact vasyuninBEntry_18_46_eval

def interval_46_18 : NamedVasyuninInterval :=
{
  h := 46
  k := 18
  lower := (9133427/265730000)
  upper := (9186573/265730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_18_interval
}

theorem G46_19_formula : baezDuarteGramEntry 46 19 = vasyuninBEntry 19 46 := by
  rw [baezDuarteGramEntry_symm 46 19]
  exact G19_46_formula

theorem G46_19_interval :
    ((((22294007/659930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 19) ∧
    (baezDuarteGramEntry 46 19 ≤ (((22425993/659930000) : ℚ) : ℝ)) := by
  rw [G46_19_formula]
  exact vasyuninBEntry_19_46_eval

def interval_46_19 : NamedVasyuninInterval :=
{
  h := 46
  k := 19
  lower := (22294007/659930000)
  upper := (22425993/659930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_19_interval
}

theorem G46_20_formula : baezDuarteGramEntry 46 20 = vasyuninBEntry 20 46 := by
  rw [baezDuarteGramEntry_symm 46 20]
  exact G20_46_formula

theorem G46_20_interval :
    ((((19112641/573590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 20) ∧
    (baezDuarteGramEntry 46 20 ≤ (((19227359/573590000) : ℚ) : ℝ)) := by
  rw [G46_20_formula]
  exact vasyuninBEntry_20_46_eval

def interval_46_20 : NamedVasyuninInterval :=
{
  h := 46
  k := 20
  lower := (19112641/573590000)
  upper := (19227359/573590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_20_interval
}

theorem G46_21_formula : baezDuarteGramEntry 46 21 = vasyuninBEntry 21 46 := by
  rw [baezDuarteGramEntry_symm 46 21]
  exact G21_46_formula

theorem G46_21_interval :
    ((((3529309/106910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 21) ∧
    (baezDuarteGramEntry 46 21 ≤ (((3550691/106910000) : ℚ) : ℝ)) := by
  rw [G46_21_formula]
  exact vasyuninBEntry_21_46_eval

def interval_46_21 : NamedVasyuninInterval :=
{
  h := 46
  k := 21
  lower := (3529309/106910000)
  upper := (3550691/106910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_21_interval
}

theorem G46_22_formula : baezDuarteGramEntry 46 22 = vasyuninBEntry 22 46 := by
  rw [baezDuarteGramEntry_symm 46 22]
  exact G22_46_formula

theorem G46_22_interval :
    ((((29959039/909610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 22) ∧
    (baezDuarteGramEntry 46 22 ≤ (((30140961/909610000) : ℚ) : ℝ)) := by
  rw [G46_22_formula]
  exact vasyuninBEntry_22_46_eval

def interval_46_22 : NamedVasyuninInterval :=
{
  h := 46
  k := 22
  lower := (29959039/909610000)
  upper := (30140961/909610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_22_interval
}

theorem G46_23_formula : baezDuarteGramEntry 46 23 = vasyuninBEntry 23 46 := by
  rw [baezDuarteGramEntry_symm 46 23]
  exact G23_46_formula

theorem G46_23_interval :
    ((((5880433/175670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 23) ∧
    (baezDuarteGramEntry 46 23 ≤ (((5915567/175670000) : ℚ) : ℝ)) := by
  rw [G46_23_formula]
  exact vasyuninBEntry_23_46_eval

def interval_46_23 : NamedVasyuninInterval :=
{
  h := 46
  k := 23
  lower := (5880433/175670000)
  upper := (5915567/175670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_23_interval
}

theorem G46_24_formula : baezDuarteGramEntry 46 24 = vasyuninBEntry 24 46 := by
  rw [baezDuarteGramEntry_symm 46 24]
  exact G24_46_formula

theorem G46_24_interval :
    ((((21383041/669590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 24) ∧
    (baezDuarteGramEntry 46 24 ≤ (((21516959/669590000) : ℚ) : ℝ)) := by
  rw [G46_24_formula]
  exact vasyuninBEntry_24_46_eval

def interval_46_24 : NamedVasyuninInterval :=
{
  h := 46
  k := 24
  lower := (21383041/669590000)
  upper := (21516959/669590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_24_interval
}

theorem G46_25_formula : baezDuarteGramEntry 46 25 = vasyuninBEntry 25 46 := by
  rw [baezDuarteGramEntry_symm 46 25]
  exact G25_46_formula

theorem G46_25_interval :
    ((((30342271/977290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 25) ∧
    (baezDuarteGramEntry 46 25 ≤ (((30537729/977290000) : ℚ) : ℝ)) := by
  rw [G46_25_formula]
  exact vasyuninBEntry_25_46_eval

def interval_46_25 : NamedVasyuninInterval :=
{
  h := 46
  k := 25
  lower := (30342271/977290000)
  upper := (30537729/977290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_25_interval
}

theorem G46_26_formula : baezDuarteGramEntry 46 26 = vasyuninBEntry 26 46 := by
  rw [baezDuarteGramEntry_symm 46 26]
  exact G26_46_formula

theorem G46_26_interval :
    ((((11681551/384490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 26) ∧
    (baezDuarteGramEntry 46 26 ≤ (((11758449/384490000) : ℚ) : ℝ)) := by
  rw [G46_26_formula]
  exact vasyuninBEntry_26_46_eval

def interval_46_26 : NamedVasyuninInterval :=
{
  h := 46
  k := 26
  lower := (11681551/384490000)
  upper := (11758449/384490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_26_interval
}

theorem G46_27_formula : baezDuarteGramEntry 46 27 = vasyuninBEntry 27 46 := by
  rw [baezDuarteGramEntry_symm 46 27]
  exact G27_46_formula

theorem G46_27_interval :
    ((((1143169/38310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 27) ∧
    (baezDuarteGramEntry 46 27 ≤ (((1150831/38310000) : ℚ) : ℝ)) := by
  rw [G46_27_formula]
  exact vasyuninBEntry_27_46_eval

def interval_46_27 : NamedVasyuninInterval :=
{
  h := 46
  k := 27
  lower := (1143169/38310000)
  upper := (1150831/38310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_27_interval
}

theorem G46_28_formula : baezDuarteGramEntry 46 28 = vasyuninBEntry 28 46 := by
  rw [baezDuarteGramEntry_symm 46 28]
  exact G28_46_formula

theorem G46_28_interval :
    ((((17769529/604710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 28) ∧
    (baezDuarteGramEntry 46 28 ≤ (((17890471/604710000) : ℚ) : ℝ)) := by
  rw [G46_28_formula]
  exact vasyuninBEntry_28_46_eval

def interval_46_28 : NamedVasyuninInterval :=
{
  h := 46
  k := 28
  lower := (17769529/604710000)
  upper := (17890471/604710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_28_interval
}

theorem G46_29_formula : baezDuarteGramEntry 46 29 = vasyuninBEntry 29 46 := by
  rw [baezDuarteGramEntry_symm 46 29]
  exact G29_46_formula

theorem G46_29_interval :
    ((((4279231/147690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 29) ∧
    (baezDuarteGramEntry 46 29 ≤ (((4308769/147690000) : ℚ) : ℝ)) := by
  rw [G46_29_formula]
  exact vasyuninBEntry_29_46_eval

def interval_46_29 : NamedVasyuninInterval :=
{
  h := 46
  k := 29
  lower := (4279231/147690000)
  upper := (4308769/147690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_29_interval
}

theorem G46_30_formula : baezDuarteGramEntry 46 30 = vasyuninBEntry 30 46 := by
  rw [baezDuarteGramEntry_symm 46 30]
  exact G30_46_formula

theorem G46_30_interval :
    ((((23119403/805970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 30) ∧
    (baezDuarteGramEntry 46 30 ≤ (((23280597/805970000) : ℚ) : ℝ)) := by
  rw [G46_30_formula]
  exact vasyuninBEntry_30_46_eval

def interval_46_30 : NamedVasyuninInterval :=
{
  h := 46
  k := 30
  lower := (23119403/805970000)
  upper := (23280597/805970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_30_interval
}

end RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
