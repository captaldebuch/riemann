import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBoundsGenerated
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPrimitiveBounds
import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part1

namespace RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Certificates.Generated

theorem G5_29_formula : baezDuarteGramEntry 5 29 = vasyuninBEntry 5 29 := vasyuninBEntry_correct_axiom 5 29 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_29_eval :
    ((((12793493/185070000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 29) ∧
    (vasyuninBEntry 5 29 ≤ (((12830507/185070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_529_formula_bound
  constructor <;> linarith

theorem G5_29_interval :
    ((((12793493/185070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 29) ∧
    (baezDuarteGramEntry 5 29 ≤ (((12830507/185070000) : ℚ) : ℝ)) := by
  rw [G5_29_formula]
  exact vasyuninBEntry_5_29_eval

def interval_5_29 : NamedVasyuninInterval :=
{
  h := 5
  k := 29
  lower := (12793493/185070000)
  upper := (12830507/185070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_29_interval
}

theorem G5_30_formula : baezDuarteGramEntry 5 30 = vasyuninBEntry 5 30 := vasyuninBEntry_correct_axiom 5 30 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_30_eval :
    ((((5680421/83290000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 30) ∧
    (vasyuninBEntry 5 30 ≤ (((5697079/83290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_6_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 6 5 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G5_30_interval :
    ((((5680421/83290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 30) ∧
    (baezDuarteGramEntry 5 30 ≤ (((5697079/83290000) : ℚ) : ℝ)) := by
  rw [G5_30_formula]
  exact vasyuninBEntry_5_30_eval

def interval_5_30 : NamedVasyuninInterval :=
{
  h := 5
  k := 30
  lower := (5680421/83290000)
  upper := (5697079/83290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_30_interval
}

theorem G5_31_formula : baezDuarteGramEntry 5 31 = vasyuninBEntry 5 31 := vasyuninBEntry_correct_axiom 5 31 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_31_eval :
    ((((35955331/546690000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 31) ∧
    (vasyuninBEntry 5 31 ≤ (((36064669/546690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_531_formula_bound
  constructor <;> linarith

theorem G5_31_interval :
    ((((35955331/546690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 31) ∧
    (baezDuarteGramEntry 5 31 ≤ (((36064669/546690000) : ℚ) : ℝ)) := by
  rw [G5_31_formula]
  exact vasyuninBEntry_5_31_eval

def interval_5_31 : NamedVasyuninInterval :=
{
  h := 5
  k := 31
  lower := (35955331/546690000)
  upper := (36064669/546690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_31_interval
}

theorem G5_32_formula : baezDuarteGramEntry 5 32 = vasyuninBEntry 5 32 := vasyuninBEntry_correct_axiom 5 32 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_32_eval :
    ((((10091747/157530000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 32) ∧
    (vasyuninBEntry 5 32 ≤ (((10123253/157530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_532_formula_bound
  constructor <;> linarith

theorem G5_32_interval :
    ((((10091747/157530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 32) ∧
    (baezDuarteGramEntry 5 32 ≤ (((10123253/157530000) : ℚ) : ℝ)) := by
  rw [G5_32_formula]
  exact vasyuninBEntry_5_32_eval

def interval_5_32 : NamedVasyuninInterval :=
{
  h := 5
  k := 32
  lower := (10091747/157530000)
  upper := (10123253/157530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_32_interval
}

theorem G5_33_formula : baezDuarteGramEntry 5 33 = vasyuninBEntry 5 33 := vasyuninBEntry_correct_axiom 5 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_33_eval :
    ((((19768411/315890000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 33) ∧
    (vasyuninBEntry 5 33 ≤ (((19831589/315890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_533_formula_bound
  constructor <;> linarith

theorem G5_33_interval :
    ((((19768411/315890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 33) ∧
    (baezDuarteGramEntry 5 33 ≤ (((19831589/315890000) : ℚ) : ℝ)) := by
  rw [G5_33_formula]
  exact vasyuninBEntry_5_33_eval

def interval_5_33 : NamedVasyuninInterval :=
{
  h := 5
  k := 33
  lower := (19768411/315890000)
  upper := (19831589/315890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_33_interval
}

theorem G5_34_formula : baezDuarteGramEntry 5 34 = vasyuninBEntry 5 34 := vasyuninBEntry_correct_axiom 5 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_34_eval :
    ((((52684049/859510000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 34) ∧
    (vasyuninBEntry 5 34 ≤ (((52855951/859510000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_534_formula_bound
  constructor <;> linarith

theorem G5_34_interval :
    ((((52684049/859510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 34) ∧
    (baezDuarteGramEntry 5 34 ≤ (((52855951/859510000) : ℚ) : ℝ)) := by
  rw [G5_34_formula]
  exact vasyuninBEntry_5_34_eval

def interval_5_34 : NamedVasyuninInterval :=
{
  h := 5
  k := 34
  lower := (52684049/859510000)
  upper := (52855951/859510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_34_interval
}

theorem G5_35_formula : baezDuarteGramEntry 5 35 = vasyuninBEntry 5 35 := vasyuninBEntry_correct_axiom 5 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_35_eval :
    ((((2560771/42290000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 35) ∧
    (vasyuninBEntry 5 35 ≤ (((2569229/42290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 7 5 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G5_35_interval :
    ((((2560771/42290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 35) ∧
    (baezDuarteGramEntry 5 35 ≤ (((2569229/42290000) : ℚ) : ℝ)) := by
  rw [G5_35_formula]
  exact vasyuninBEntry_5_35_eval

def interval_5_35 : NamedVasyuninInterval :=
{
  h := 5
  k := 35
  lower := (2560771/42290000)
  upper := (2569229/42290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_35_interval
}

theorem G5_36_formula : baezDuarteGramEntry 5 36 = vasyuninBEntry 5 36 := vasyuninBEntry_correct_axiom 5 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_36_eval :
    ((((11111071/189290000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 36) ∧
    (vasyuninBEntry 5 36 ≤ (((11148929/189290000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_536_formula_bound
  constructor <;> linarith

theorem G5_36_interval :
    ((((11111071/189290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 36) ∧
    (baezDuarteGramEntry 5 36 ≤ (((11148929/189290000) : ℚ) : ℝ)) := by
  rw [G5_36_formula]
  exact vasyuninBEntry_5_36_eval

def interval_5_36 : NamedVasyuninInterval :=
{
  h := 5
  k := 36
  lower := (11111071/189290000)
  upper := (11148929/189290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_36_interval
}

theorem G5_37_formula : baezDuarteGramEntry 5 37 = vasyuninBEntry 5 37 := vasyuninBEntry_correct_axiom 5 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_37_eval :
    ((((5869769/102310000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 37) ∧
    (vasyuninBEntry 5 37 ≤ (((5890231/102310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_537_formula_bound
  constructor <;> linarith

theorem G5_37_interval :
    ((((5869769/102310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 37) ∧
    (baezDuarteGramEntry 5 37 ≤ (((5890231/102310000) : ℚ) : ℝ)) := by
  rw [G5_37_formula]
  exact vasyuninBEntry_5_37_eval

def interval_5_37 : NamedVasyuninInterval :=
{
  h := 5
  k := 37
  lower := (5869769/102310000)
  upper := (5890231/102310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_37_interval
}

theorem G5_38_formula : baezDuarteGramEntry 5 38 = vasyuninBEntry 5 38 := vasyuninBEntry_correct_axiom 5 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_38_eval :
    ((((49422073/879270000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 38) ∧
    (vasyuninBEntry 5 38 ≤ (((49597927/879270000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_538_formula_bound
  constructor <;> linarith

theorem G5_38_interval :
    ((((49422073/879270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 38) ∧
    (baezDuarteGramEntry 5 38 ≤ (((49597927/879270000) : ℚ) : ℝ)) := by
  rw [G5_38_formula]
  exact vasyuninBEntry_5_38_eval

def interval_5_38 : NamedVasyuninInterval :=
{
  h := 5
  k := 38
  lower := (49422073/879270000)
  upper := (49597927/879270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_38_interval
}

theorem G5_39_formula : baezDuarteGramEntry 5 39 = vasyuninBEntry 5 39 := vasyuninBEntry_correct_axiom 5 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_39_eval :
    ((((53652783/972170000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 39) ∧
    (vasyuninBEntry 5 39 ≤ (((53847217/972170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_539_formula_bound
  constructor <;> linarith

theorem G5_39_interval :
    ((((53652783/972170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 39) ∧
    (baezDuarteGramEntry 5 39 ≤ (((53847217/972170000) : ℚ) : ℝ)) := by
  rw [G5_39_formula]
  exact vasyuninBEntry_5_39_eval

def interval_5_39 : NamedVasyuninInterval :=
{
  h := 5
  k := 39
  lower := (53652783/972170000)
  upper := (53847217/972170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_39_interval
}

theorem G5_40_formula : baezDuarteGramEntry 5 40 = vasyuninBEntry 5 40 := vasyuninBEntry_correct_axiom 5 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_40_eval :
    ((((42731707/782930000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 40) ∧
    (vasyuninBEntry 5 40 ≤ (((42888293/782930000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 8 5 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G5_40_interval :
    ((((42731707/782930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 40) ∧
    (baezDuarteGramEntry 5 40 ≤ (((42888293/782930000) : ℚ) : ℝ)) := by
  rw [G5_40_formula]
  exact vasyuninBEntry_5_40_eval

def interval_5_40 : NamedVasyuninInterval :=
{
  h := 5
  k := 40
  lower := (42731707/782930000)
  upper := (42888293/782930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_40_interval
}

theorem G5_41_formula : baezDuarteGramEntry 5 41 = vasyuninBEntry 5 41 := vasyuninBEntry_correct_axiom 5 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_41_eval :
    ((((15520779/292210000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 41) ∧
    (vasyuninBEntry 5 41 ≤ (((15579221/292210000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_541_formula_bound
  constructor <;> linarith

theorem G5_41_interval :
    ((((15520779/292210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 41) ∧
    (baezDuarteGramEntry 5 41 ≤ (((15579221/292210000) : ℚ) : ℝ)) := by
  rw [G5_41_formula]
  exact vasyuninBEntry_5_41_eval

def interval_5_41 : NamedVasyuninInterval :=
{
  h := 5
  k := 41
  lower := (15520779/292210000)
  upper := (15579221/292210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_41_interval
}

theorem G5_42_formula : baezDuarteGramEntry 5 42 = vasyuninBEntry 5 42 := vasyuninBEntry_correct_axiom 5 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_42_eval :
    ((((39534049/759510000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 42) ∧
    (vasyuninBEntry 5 42 ≤ (((39685951/759510000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_542_formula_bound
  constructor <;> linarith

theorem G5_42_interval :
    ((((39534049/759510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 42) ∧
    (baezDuarteGramEntry 5 42 ≤ (((39685951/759510000) : ℚ) : ℝ)) := by
  rw [G5_42_formula]
  exact vasyuninBEntry_5_42_eval

def interval_5_42 : NamedVasyuninInterval :=
{
  h := 5
  k := 42
  lower := (39534049/759510000)
  upper := (39685951/759510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_42_interval
}

theorem G5_43_formula : baezDuarteGramEntry 5 43 = vasyuninBEntry 5 43 := vasyuninBEntry_correct_axiom 5 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_43_eval :
    ((((29103059/569410000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 43) ∧
    (vasyuninBEntry 5 43 ≤ (((29216941/569410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_543_formula_bound
  constructor <;> linarith

theorem G5_43_interval :
    ((((29103059/569410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 43) ∧
    (baezDuarteGramEntry 5 43 ≤ (((29216941/569410000) : ℚ) : ℝ)) := by
  rw [G5_43_formula]
  exact vasyuninBEntry_5_43_eval

def interval_5_43 : NamedVasyuninInterval :=
{
  h := 5
  k := 43
  lower := (29103059/569410000)
  upper := (29216941/569410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_43_interval
}

theorem G5_44_formula : baezDuarteGramEntry 5 44 = vasyuninBEntry 5 44 := vasyuninBEntry_correct_axiom 5 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_44_eval :
    ((((22944367/456330000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 44) ∧
    (vasyuninBEntry 5 44 ≤ (((23035633/456330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_544_formula_bound
  constructor <;> linarith

theorem G5_44_interval :
    ((((22944367/456330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 44) ∧
    (baezDuarteGramEntry 5 44 ≤ (((23035633/456330000) : ℚ) : ℝ)) := by
  rw [G5_44_formula]
  exact vasyuninBEntry_5_44_eval

def interval_5_44 : NamedVasyuninInterval :=
{
  h := 5
  k := 44
  lower := (22944367/456330000)
  upper := (23035633/456330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_44_interval
}

theorem G5_45_formula : baezDuarteGramEntry 5 45 = vasyuninBEntry 5 45 := vasyuninBEntry_correct_axiom 5 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_45_eval :
    ((((44690207/897930000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 45) ∧
    (vasyuninBEntry 5 45 ≤ (((44869793/897930000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 9 5 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G5_45_interval :
    ((((44690207/897930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 45) ∧
    (baezDuarteGramEntry 5 45 ≤ (((44869793/897930000) : ℚ) : ℝ)) := by
  rw [G5_45_formula]
  exact vasyuninBEntry_5_45_eval

def interval_5_45 : NamedVasyuninInterval :=
{
  h := 5
  k := 45
  lower := (44690207/897930000)
  upper := (44869793/897930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_45_interval
}

theorem G5_46_formula : baezDuarteGramEntry 5 46 = vasyuninBEntry 5 46 := vasyuninBEntry_correct_axiom 5 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_46_eval :
    ((((11670977/240230000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 46) ∧
    (vasyuninBEntry 5 46 ≤ (((11719023/240230000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_546_formula_bound
  constructor <;> linarith

theorem G5_46_interval :
    ((((11670977/240230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 46) ∧
    (baezDuarteGramEntry 5 46 ≤ (((11719023/240230000) : ℚ) : ℝ)) := by
  rw [G5_46_formula]
  exact vasyuninBEntry_5_46_eval

def interval_5_46 : NamedVasyuninInterval :=
{
  h := 5
  k := 46
  lower := (11670977/240230000)
  upper := (11719023/240230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_46_interval
}

theorem G5_47_formula : baezDuarteGramEntry 5 47 = vasyuninBEntry 5 47 := vasyuninBEntry_correct_axiom 5 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_47_eval :
    ((((41393239/867610000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 47) ∧
    (vasyuninBEntry 5 47 ≤ (((41566761/867610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_547_formula_bound
  constructor <;> linarith

theorem G5_47_interval :
    ((((41393239/867610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 47) ∧
    (baezDuarteGramEntry 5 47 ≤ (((41566761/867610000) : ℚ) : ℝ)) := by
  rw [G5_47_formula]
  exact vasyuninBEntry_5_47_eval

def interval_5_47 : NamedVasyuninInterval :=
{
  h := 5
  k := 47
  lower := (41393239/867610000)
  upper := (41566761/867610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_47_interval
}

theorem G5_48_formula : baezDuarteGramEntry 5 48 = vasyuninBEntry 5 48 := vasyuninBEntry_correct_axiom 5 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_48_eval :
    ((((2906931/61940000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 48) ∧
    (vasyuninBEntry 5 48 ≤ (((2919319/61940000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_548_formula_bound
  constructor <;> linarith

theorem G5_48_interval :
    ((((2906931/61940000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 48) ∧
    (baezDuarteGramEntry 5 48 ≤ (((2919319/61940000) : ℚ) : ℝ)) := by
  rw [G5_48_formula]
  exact vasyuninBEntry_5_48_eval

def interval_5_48 : NamedVasyuninInterval :=
{
  h := 5
  k := 48
  lower := (2906931/61940000)
  upper := (2919319/61940000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_48_interval
}

theorem G5_49_formula : baezDuarteGramEntry 5 49 = vasyuninBEntry 5 49 := vasyuninBEntry_correct_axiom 5 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_49_eval :
    ((((2444713/52870000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 49) ∧
    (vasyuninBEntry 5 49 ≤ (((2455287/52870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_549_formula_bound
  constructor <;> linarith

theorem G5_49_interval :
    ((((2444713/52870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 49) ∧
    (baezDuarteGramEntry 5 49 ≤ (((2455287/52870000) : ℚ) : ℝ)) := by
  rw [G5_49_formula]
  exact vasyuninBEntry_5_49_eval

def interval_5_49 : NamedVasyuninInterval :=
{
  h := 5
  k := 49
  lower := (2444713/52870000)
  upper := (2455287/52870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_49_interval
}

theorem G5_50_formula : baezDuarteGramEntry 5 50 = vasyuninBEntry 5 50 := vasyuninBEntry_correct_axiom 5 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_50_eval :
    ((((16264493/355070000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 50) ∧
    (vasyuninBEntry 5 50 ≤ (((16335507/355070000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 10 5 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G5_50_interval :
    ((((16264493/355070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 50) ∧
    (baezDuarteGramEntry 5 50 ≤ (((16335507/355070000) : ℚ) : ℝ)) := by
  rw [G5_50_formula]
  exact vasyuninBEntry_5_50_eval

def interval_5_50 : NamedVasyuninInterval :=
{
  h := 5
  k := 50
  lower := (16264493/355070000)
  upper := (16335507/355070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_50_interval
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

theorem G6_21_formula : baezDuarteGramEntry 6 21 = vasyuninBEntry 6 21 := vasyuninBEntry_correct_axiom 6 21 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_21_eval :
    ((((76268471/915290000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 21) ∧
    (vasyuninBEntry 6 21 ≤ (((76451529/915290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 7 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G6_21_interval :
    ((((76268471/915290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 21) ∧
    (baezDuarteGramEntry 6 21 ≤ (((76451529/915290000) : ℚ) : ℝ)) := by
  rw [G6_21_formula]
  exact vasyuninBEntry_6_21_eval

def interval_6_21 : NamedVasyuninInterval :=
{
  h := 6
  k := 21
  lower := (76268471/915290000)
  upper := (76451529/915290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_21_interval
}

theorem G6_22_formula : baezDuarteGramEntry 6 22 = vasyuninBEntry 6 22 := vasyuninBEntry_correct_axiom 6 22 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_22_eval :
    ((((71321359/886410000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 22) ∧
    (vasyuninBEntry 6 22 ≤ (((71498641/886410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 11 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G6_22_interval :
    ((((71321359/886410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 22) ∧
    (baezDuarteGramEntry 6 22 ≤ (((71498641/886410000) : ℚ) : ℝ)) := by
  rw [G6_22_formula]
  exact vasyuninBEntry_6_22_eval

def interval_6_22 : NamedVasyuninInterval :=
{
  h := 6
  k := 22
  lower := (71321359/886410000)
  upper := (71498641/886410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_22_interval
}

theorem G6_23_formula : baezDuarteGramEntry 6 23 = vasyuninBEntry 6 23 := vasyuninBEntry_correct_axiom 6 23 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_23_eval :
    ((((75273793/962070000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 23) ∧
    (vasyuninBEntry 6 23 ≤ (((75466207/962070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_623_formula_bound
  constructor <;> linarith

theorem G6_23_interval :
    ((((75273793/962070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 23) ∧
    (baezDuarteGramEntry 6 23 ≤ (((75466207/962070000) : ℚ) : ℝ)) := by
  rw [G6_23_formula]
  exact vasyuninBEntry_6_23_eval

def interval_6_23 : NamedVasyuninInterval :=
{
  h := 6
  k := 23
  lower := (75273793/962070000)
  upper := (75466207/962070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_23_interval
}

theorem G6_24_formula : baezDuarteGramEntry 6 24 = vasyuninBEntry 6 24 := vasyuninBEntry_correct_axiom 6 24 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_24_eval :
    ((((25287287/327130000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 24) ∧
    (vasyuninBEntry 6 24 ≤ (((25352713/327130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 4 6 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G6_24_interval :
    ((((25287287/327130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 24) ∧
    (baezDuarteGramEntry 6 24 ≤ (((25352713/327130000) : ℚ) : ℝ)) := by
  rw [G6_24_formula]
  exact vasyuninBEntry_6_24_eval

def interval_6_24 : NamedVasyuninInterval :=
{
  h := 6
  k := 24
  lower := (25287287/327130000)
  upper := (25352713/327130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_24_interval
}

theorem G6_25_formula : baezDuarteGramEntry 6 25 = vasyuninBEntry 6 25 := vasyuninBEntry_correct_axiom 6 25 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_25_eval :
    ((((4757297/64530000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 25) ∧
    (vasyuninBEntry 6 25 ≤ (((4770203/64530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_625_formula_bound
  constructor <;> linarith

theorem G6_25_interval :
    ((((4757297/64530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 25) ∧
    (baezDuarteGramEntry 6 25 ≤ (((4770203/64530000) : ℚ) : ℝ)) := by
  rw [G6_25_formula]
  exact vasyuninBEntry_6_25_eval

def interval_6_25 : NamedVasyuninInterval :=
{
  h := 6
  k := 25
  lower := (4757297/64530000)
  upper := (4770203/64530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_25_interval
}

theorem G6_26_formula : baezDuarteGramEntry 6 26 = vasyuninBEntry 6 26 := vasyuninBEntry_correct_axiom 6 26 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_26_eval :
    ((((21325121/298790000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 26) ∧
    (vasyuninBEntry 6 26 ≤ (((21384879/298790000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 13 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G6_26_interval :
    ((((21325121/298790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 26) ∧
    (baezDuarteGramEntry 6 26 ≤ (((21384879/298790000) : ℚ) : ℝ)) := by
  rw [G6_26_formula]
  exact vasyuninBEntry_6_26_eval

def interval_6_26 : NamedVasyuninInterval :=
{
  h := 6
  k := 26
  lower := (21325121/298790000)
  upper := (21384879/298790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_26_interval
}

theorem G6_27_formula : baezDuarteGramEntry 6 27 = vasyuninBEntry 6 27 := vasyuninBEntry_correct_axiom 6 27 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_27_eval :
    ((((13089161/188390000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 27) ∧
    (vasyuninBEntry 6 27 ≤ (((13126839/188390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 9 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G6_27_interval :
    ((((13089161/188390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 27) ∧
    (baezDuarteGramEntry 6 27 ≤ (((13126839/188390000) : ℚ) : ℝ)) := by
  rw [G6_27_formula]
  exact vasyuninBEntry_6_27_eval

def interval_6_27 : NamedVasyuninInterval :=
{
  h := 6
  k := 27
  lower := (13089161/188390000)
  upper := (13126839/188390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_27_interval
}

theorem G6_28_formula : baezDuarteGramEntry 6 28 = vasyuninBEntry 6 28 := vasyuninBEntry_correct_axiom 6 28 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_28_eval :
    ((((20589527/304730000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 28) ∧
    (vasyuninBEntry 6 28 ≤ (((20650473/304730000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_14_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 14 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G6_28_interval :
    ((((20589527/304730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 28) ∧
    (baezDuarteGramEntry 6 28 ≤ (((20650473/304730000) : ℚ) : ℝ)) := by
  rw [G6_28_formula]
  exact vasyuninBEntry_6_28_eval

def interval_6_28 : NamedVasyuninInterval :=
{
  h := 6
  k := 28
  lower := (20589527/304730000)
  upper := (20650473/304730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_28_interval
}

theorem G6_29_formula : baezDuarteGramEntry 6 29 = vasyuninBEntry 6 29 := vasyuninBEntry_correct_axiom 6 29 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_29_eval :
    ((((17842981/270190000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 29) ∧
    (vasyuninBEntry 6 29 ≤ (((17897019/270190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_629_formula_bound
  constructor <;> linarith

theorem G6_29_interval :
    ((((17842981/270190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 29) ∧
    (baezDuarteGramEntry 6 29 ≤ (((17897019/270190000) : ℚ) : ℝ)) := by
  rw [G6_29_formula]
  exact vasyuninBEntry_6_29_eval

def interval_6_29 : NamedVasyuninInterval :=
{
  h := 6
  k := 29
  lower := (17842981/270190000)
  upper := (17897019/270190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_29_interval
}

theorem G6_30_formula : baezDuarteGramEntry 6 30 = vasyuninBEntry 6 30 := vasyuninBEntry_correct_axiom 6 30 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_30_eval :
    ((((21397239/327610000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 30) ∧
    (vasyuninBEntry 6 30 ≤ (((21462761/327610000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 5 6 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G6_30_interval :
    ((((21397239/327610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 30) ∧
    (baezDuarteGramEntry 6 30 ≤ (((21462761/327610000) : ℚ) : ℝ)) := by
  rw [G6_30_formula]
  exact vasyuninBEntry_6_30_eval

def interval_6_30 : NamedVasyuninInterval :=
{
  h := 6
  k := 30
  lower := (21397239/327610000)
  upper := (21462761/327610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_30_interval
}

theorem G6_31_formula : baezDuarteGramEntry 6 31 = vasyuninBEntry 6 31 := vasyuninBEntry_correct_axiom 6 31 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_31_eval :
    ((((1077287/17130000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 31) ∧
    (vasyuninBEntry 6 31 ≤ (((1080713/17130000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_631_formula_bound
  constructor <;> linarith

theorem G6_31_interval :
    ((((1077287/17130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 31) ∧
    (baezDuarteGramEntry 6 31 ≤ (((1080713/17130000) : ℚ) : ℝ)) := by
  rw [G6_31_formula]
  exact vasyuninBEntry_6_31_eval

def interval_6_31 : NamedVasyuninInterval :=
{
  h := 6
  k := 31
  lower := (1077287/17130000)
  upper := (1080713/17130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_31_interval
}

theorem G6_32_formula : baezDuarteGramEntry 6 32 = vasyuninBEntry 6 32 := vasyuninBEntry_correct_axiom 6 32 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_32_eval :
    ((((9888853/161470000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 32) ∧
    (vasyuninBEntry 6 32 ≤ (((9921147/161470000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_16_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 16 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G6_32_interval :
    ((((9888853/161470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 32) ∧
    (baezDuarteGramEntry 6 32 ≤ (((9921147/161470000) : ℚ) : ℝ)) := by
  rw [G6_32_formula]
  exact vasyuninBEntry_6_32_eval

def interval_6_32 : NamedVasyuninInterval :=
{
  h := 6
  k := 32
  lower := (9888853/161470000)
  upper := (9921147/161470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_32_interval
}

theorem G6_33_formula : baezDuarteGramEntry 6 33 = vasyuninBEntry 6 33 := vasyuninBEntry_correct_axiom 6 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_33_eval :
    ((((52302667/873330000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 33) ∧
    (vasyuninBEntry 6 33 ≤ (((52477333/873330000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 11 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G6_33_interval :
    ((((52302667/873330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 33) ∧
    (baezDuarteGramEntry 6 33 ≤ (((52477333/873330000) : ℚ) : ℝ)) := by
  rw [G6_33_formula]
  exact vasyuninBEntry_6_33_eval

def interval_6_33 : NamedVasyuninInterval :=
{
  h := 6
  k := 33
  lower := (52302667/873330000)
  upper := (52477333/873330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_33_interval
}

theorem G6_34_formula : baezDuarteGramEntry 6 34 = vasyuninBEntry 6 34 := vasyuninBEntry_correct_axiom 6 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_34_eval :
    ((((55065891/941090000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 34) ∧
    (vasyuninBEntry 6 34 ≤ (((55254109/941090000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_17_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 17 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G6_34_interval :
    ((((55065891/941090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 34) ∧
    (baezDuarteGramEntry 6 34 ≤ (((55254109/941090000) : ℚ) : ℝ)) := by
  rw [G6_34_formula]
  exact vasyuninBEntry_6_34_eval

def interval_6_34 : NamedVasyuninInterval :=
{
  h := 6
  k := 34
  lower := (55065891/941090000)
  upper := (55254109/941090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_34_interval
}

theorem G6_35_formula : baezDuarteGramEntry 6 35 = vasyuninBEntry 6 35 := vasyuninBEntry_correct_axiom 6 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_35_eval :
    ((((2254871/39290000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 35) ∧
    (vasyuninBEntry 6 35 ≤ (((2262729/39290000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_635_formula_bound
  constructor <;> linarith

theorem G6_35_interval :
    ((((2254871/39290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 35) ∧
    (baezDuarteGramEntry 6 35 ≤ (((2262729/39290000) : ℚ) : ℝ)) := by
  rw [G6_35_formula]
  exact vasyuninBEntry_6_35_eval

def interval_6_35 : NamedVasyuninInterval :=
{
  h := 6
  k := 35
  lower := (2254871/39290000)
  upper := (2262729/39290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_35_interval
}

theorem G6_36_formula : baezDuarteGramEntry 6 36 = vasyuninBEntry 6 36 := vasyuninBEntry_correct_axiom 6 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_36_eval :
    ((((31135201/547990000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 36) ∧
    (vasyuninBEntry 6 36 ≤ (((31244799/547990000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_6_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 6 6 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G6_36_interval :
    ((((31135201/547990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 36) ∧
    (baezDuarteGramEntry 6 36 ≤ (((31244799/547990000) : ℚ) : ℝ)) := by
  rw [G6_36_formula]
  exact vasyuninBEntry_6_36_eval

def interval_6_36 : NamedVasyuninInterval :=
{
  h := 6
  k := 36
  lower := (31135201/547990000)
  upper := (31244799/547990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_36_interval
}

theorem G6_37_formula : baezDuarteGramEntry 6 37 = vasyuninBEntry 6 37 := vasyuninBEntry_correct_axiom 6 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_37_eval :
    ((((35934733/652670000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 37) ∧
    (vasyuninBEntry 6 37 ≤ (((36065267/652670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_637_formula_bound
  constructor <;> linarith

theorem G6_37_interval :
    ((((35934733/652670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 37) ∧
    (baezDuarteGramEntry 6 37 ≤ (((36065267/652670000) : ℚ) : ℝ)) := by
  rw [G6_37_formula]
  exact vasyuninBEntry_6_37_eval

def interval_6_37 : NamedVasyuninInterval :=
{
  h := 6
  k := 37
  lower := (35934733/652670000)
  upper := (36065267/652670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_37_interval
}

theorem G6_38_formula : baezDuarteGramEntry 6 38 = vasyuninBEntry 6 38 := vasyuninBEntry_correct_axiom 6 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_38_eval :
    ((((4672321/86790000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 38) ∧
    (vasyuninBEntry 6 38 ≤ (((4689679/86790000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 19 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G6_38_interval :
    ((((4672321/86790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 38) ∧
    (baezDuarteGramEntry 6 38 ≤ (((4689679/86790000) : ℚ) : ℝ)) := by
  rw [G6_38_formula]
  exact vasyuninBEntry_6_38_eval

def interval_6_38 : NamedVasyuninInterval :=
{
  h := 6
  k := 38
  lower := (4672321/86790000)
  upper := (4689679/86790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_38_interval
}

theorem G6_39_formula : baezDuarteGramEntry 6 39 = vasyuninBEntry 6 39 := vasyuninBEntry_correct_axiom 6 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_39_eval :
    ((((46761459/885410000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 39) ∧
    (vasyuninBEntry 6 39 ≤ (((46938541/885410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 13 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G6_39_interval :
    ((((46761459/885410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 39) ∧
    (baezDuarteGramEntry 6 39 ≤ (((46938541/885410000) : ℚ) : ℝ)) := by
  rw [G6_39_formula]
  exact vasyuninBEntry_6_39_eval

def interval_6_39 : NamedVasyuninInterval :=
{
  h := 6
  k := 39
  lower := (46761459/885410000)
  upper := (46938541/885410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_39_interval
}

theorem G6_40_formula : baezDuarteGramEntry 6 40 = vasyuninBEntry 6 40 := vasyuninBEntry_correct_axiom 6 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_40_eval :
    ((((18798689/363110000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 40) ∧
    (vasyuninBEntry 6 40 ≤ (((18871311/363110000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_20_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 20 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G6_40_interval :
    ((((18798689/363110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 40) ∧
    (baezDuarteGramEntry 6 40 ≤ (((18871311/363110000) : ℚ) : ℝ)) := by
  rw [G6_40_formula]
  exact vasyuninBEntry_6_40_eval

def interval_6_40 : NamedVasyuninInterval :=
{
  h := 6
  k := 40
  lower := (18798689/363110000)
  upper := (18871311/363110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_40_interval
}

theorem G6_41_formula : baezDuarteGramEntry 6 41 = vasyuninBEntry 6 41 := vasyuninBEntry_correct_axiom 6 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_41_eval :
    ((((5844769/114810000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 41) ∧
    (vasyuninBEntry 6 41 ≤ (((5867731/114810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_641_formula_bound
  constructor <;> linarith

theorem G6_41_interval :
    ((((5844769/114810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 41) ∧
    (baezDuarteGramEntry 6 41 ≤ (((5867731/114810000) : ℚ) : ℝ)) := by
  rw [G6_41_formula]
  exact vasyuninBEntry_6_41_eval

def interval_6_41 : NamedVasyuninInterval :=
{
  h := 6
  k := 41
  lower := (5844769/114810000)
  upper := (5867731/114810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_41_interval
}

theorem G6_42_formula : baezDuarteGramEntry 6 42 = vasyuninBEntry 6 42 := vasyuninBEntry_correct_axiom 6 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_42_eval :
    ((((43453857/861430000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 42) ∧
    (vasyuninBEntry 6 42 ≤ (((43626143/861430000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 7 6 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G6_42_interval :
    ((((43453857/861430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 42) ∧
    (baezDuarteGramEntry 6 42 ≤ (((43626143/861430000) : ℚ) : ℝ)) := by
  rw [G6_42_formula]
  exact vasyuninBEntry_6_42_eval

def interval_6_42 : NamedVasyuninInterval :=
{
  h := 6
  k := 42
  lower := (43453857/861430000)
  upper := (43626143/861430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_42_interval
}

theorem G6_43_formula : baezDuarteGramEntry 6 43 = vasyuninBEntry 6 43 := vasyuninBEntry_correct_axiom 6 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_43_eval :
    ((((41345801/841990000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 43) ∧
    (vasyuninBEntry 6 43 ≤ (((41514199/841990000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_643_formula_bound
  constructor <;> linarith

theorem G6_43_interval :
    ((((41345801/841990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 43) ∧
    (baezDuarteGramEntry 6 43 ≤ (((41514199/841990000) : ℚ) : ℝ)) := by
  rw [G6_43_formula]
  exact vasyuninBEntry_6_43_eval

def interval_6_43 : NamedVasyuninInterval :=
{
  h := 6
  k := 43
  lower := (41345801/841990000)
  upper := (41514199/841990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_43_interval
}

theorem G6_44_formula : baezDuarteGramEntry 6 44 = vasyuninBEntry 6 44 := vasyuninBEntry_correct_axiom 6 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_44_eval :
    ((((34378611/713890000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 44) ∧
    (vasyuninBEntry 6 44 ≤ (((34521389/713890000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_22_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 22 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G6_44_interval :
    ((((34378611/713890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 44) ∧
    (baezDuarteGramEntry 6 44 ≤ (((34521389/713890000) : ℚ) : ℝ)) := by
  rw [G6_44_formula]
  exact vasyuninBEntry_6_44_eval

def interval_6_44 : NamedVasyuninInterval :=
{
  h := 6
  k := 44
  lower := (34378611/713890000)
  upper := (34521389/713890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_44_interval
}

theorem G6_45_formula : baezDuarteGramEntry 6 45 = vasyuninBEntry 6 45 := vasyuninBEntry_correct_axiom 6 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_45_eval :
    ((((8394773/177270000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 45) ∧
    (vasyuninBEntry 6 45 ≤ (((8430227/177270000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_15_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 15 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G6_45_interval :
    ((((8394773/177270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 45) ∧
    (baezDuarteGramEntry 6 45 ≤ (((8430227/177270000) : ℚ) : ℝ)) := by
  rw [G6_45_formula]
  exact vasyuninBEntry_6_45_eval

def interval_6_45 : NamedVasyuninInterval :=
{
  h := 6
  k := 45
  lower := (8394773/177270000)
  upper := (8430227/177270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_45_interval
}

theorem G6_46_formula : baezDuarteGramEntry 6 46 = vasyuninBEntry 6 46 := vasyuninBEntry_correct_axiom 6 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_46_eval :
    ((((27790283/597170000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 46) ∧
    (vasyuninBEntry 6 46 ≤ (((27909717/597170000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 23 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G6_46_interval :
    ((((27790283/597170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 46) ∧
    (baezDuarteGramEntry 6 46 ≤ (((27909717/597170000) : ℚ) : ℝ)) := by
  rw [G6_46_formula]
  exact vasyuninBEntry_6_46_eval

def interval_6_46 : NamedVasyuninInterval :=
{
  h := 6
  k := 46
  lower := (27790283/597170000)
  upper := (27909717/597170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_46_interval
}

theorem G6_47_formula : baezDuarteGramEntry 6 47 = vasyuninBEntry 6 47 := vasyuninBEntry_correct_axiom 6 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_47_eval :
    ((((4534111/98890000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 47) ∧
    (vasyuninBEntry 6 47 ≤ (((4553889/98890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_647_formula_bound
  constructor <;> linarith

theorem G6_47_interval :
    ((((4534111/98890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 47) ∧
    (baezDuarteGramEntry 6 47 ≤ (((4553889/98890000) : ℚ) : ℝ)) := by
  rw [G6_47_formula]
  exact vasyuninBEntry_6_47_eval

def interval_6_47 : NamedVasyuninInterval :=
{
  h := 6
  k := 47
  lower := (4534111/98890000)
  upper := (4553889/98890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_47_interval
}

theorem G6_48_formula : baezDuarteGramEntry 6 48 = vasyuninBEntry 6 48 := vasyuninBEntry_correct_axiom 6 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_48_eval :
    ((((42456619/933810000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 48) ∧
    (vasyuninBEntry 6 48 ≤ (((42643381/933810000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 8 6 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G6_48_interval :
    ((((42456619/933810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 48) ∧
    (baezDuarteGramEntry 6 48 ≤ (((42643381/933810000) : ℚ) : ℝ)) := by
  rw [G6_48_formula]
  exact vasyuninBEntry_6_48_eval

def interval_6_48 : NamedVasyuninInterval :=
{
  h := 6
  k := 48
  lower := (42456619/933810000)
  upper := (42643381/933810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_48_interval
}

theorem G6_49_formula : baezDuarteGramEntry 6 49 = vasyuninBEntry 6 49 := vasyuninBEntry_correct_axiom 6 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_49_eval :
    ((((25113451/565490000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 49) ∧
    (vasyuninBEntry 6 49 ≤ (((25226549/565490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_649_formula_bound
  constructor <;> linarith

theorem G6_49_interval :
    ((((25113451/565490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 49) ∧
    (baezDuarteGramEntry 6 49 ≤ (((25226549/565490000) : ℚ) : ℝ)) := by
  rw [G6_49_formula]
  exact vasyuninBEntry_6_49_eval

def interval_6_49 : NamedVasyuninInterval :=
{
  h := 6
  k := 49
  lower := (25113451/565490000)
  upper := (25226549/565490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_49_interval
}

theorem G6_50_formula : baezDuarteGramEntry 6 50 = vasyuninBEntry 6 50 := vasyuninBEntry_correct_axiom 6 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_50_eval :
    ((((22219099/509010000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 50) ∧
    (vasyuninBEntry 6 50 ≤ (((22320901/509010000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 25 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G6_50_interval :
    ((((22219099/509010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 50) ∧
    (baezDuarteGramEntry 6 50 ≤ (((22320901/509010000) : ℚ) : ℝ)) := by
  rw [G6_50_formula]
  exact vasyuninBEntry_6_50_eval

def interval_6_50 : NamedVasyuninInterval :=
{
  h := 6
  k := 50
  lower := (22219099/509010000)
  upper := (22320901/509010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_50_interval
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

theorem G7_21_formula : baezDuarteGramEntry 7 21 = vasyuninBEntry 7 21 := vasyuninBEntry_correct_axiom 7 21 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_21_eval :
    ((((76816371/936290000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 21) ∧
    (vasyuninBEntry 7 21 ≤ (((77003629/936290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 3 7 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 7)
  constructor <;> linarith

theorem G7_21_interval :
    ((((76816371/936290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 21) ∧
    (baezDuarteGramEntry 7 21 ≤ (((77003629/936290000) : ℚ) : ℝ)) := by
  rw [G7_21_formula]
  exact vasyuninBEntry_7_21_eval

def interval_7_21 : NamedVasyuninInterval :=
{
  h := 7
  k := 21
  lower := (76816371/936290000)
  upper := (77003629/936290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_21_interval
}

theorem G7_22_formula : baezDuarteGramEntry 7 22 = vasyuninBEntry 7 22 := vasyuninBEntry_correct_axiom 7 22 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_22_eval :
    ((((67792577/874230000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 22) ∧
    (vasyuninBEntry 7 22 ≤ (((67967423/874230000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_722_formula_bound
  constructor <;> linarith

theorem G7_22_interval :
    ((((67792577/874230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 22) ∧
    (baezDuarteGramEntry 7 22 ≤ (((67967423/874230000) : ℚ) : ℝ)) := by
  rw [G7_22_formula]
  exact vasyuninBEntry_7_22_eval

def interval_7_22 : NamedVasyuninInterval :=
{
  h := 7
  k := 22
  lower := (67792577/874230000)
  upper := (67967423/874230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_22_interval
}

theorem G7_23_formula : baezDuarteGramEntry 7 23 = vasyuninBEntry 7 23 := vasyuninBEntry_correct_axiom 7 23 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_23_eval :
    ((((5624463/75370000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 23) ∧
    (vasyuninBEntry 7 23 ≤ (((5639537/75370000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_723_formula_bound
  constructor <;> linarith

theorem G7_23_interval :
    ((((5624463/75370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 23) ∧
    (baezDuarteGramEntry 7 23 ≤ (((5639537/75370000) : ℚ) : ℝ)) := by
  rw [G7_23_formula]
  exact vasyuninBEntry_7_23_eval

def interval_7_23 : NamedVasyuninInterval :=
{
  h := 7
  k := 23
  lower := (5624463/75370000)
  upper := (5639537/75370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_23_interval
}

theorem G7_24_formula : baezDuarteGramEntry 7 24 = vasyuninBEntry 7 24 := vasyuninBEntry_correct_axiom 7 24 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_24_eval :
    ((((7952993/110070000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 24) ∧
    (vasyuninBEntry 7 24 ≤ (((7975007/110070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_724_formula_bound
  constructor <;> linarith

theorem G7_24_interval :
    ((((7952993/110070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 24) ∧
    (baezDuarteGramEntry 7 24 ≤ (((7975007/110070000) : ℚ) : ℝ)) := by
  rw [G7_24_formula]
  exact vasyuninBEntry_7_24_eval

def interval_7_24 : NamedVasyuninInterval :=
{
  h := 7
  k := 24
  lower := (7952993/110070000)
  upper := (7975007/110070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_24_interval
}

theorem G7_25_formula : baezDuarteGramEntry 7 25 = vasyuninBEntry 7 25 := vasyuninBEntry_correct_axiom 7 25 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_25_eval :
    ((((5122699/73010000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 25) ∧
    (vasyuninBEntry 7 25 ≤ (((5137301/73010000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_725_formula_bound
  constructor <;> linarith

theorem G7_25_interval :
    ((((5122699/73010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 25) ∧
    (baezDuarteGramEntry 7 25 ≤ (((5137301/73010000) : ℚ) : ℝ)) := by
  rw [G7_25_formula]
  exact vasyuninBEntry_7_25_eval

def interval_7_25 : NamedVasyuninInterval :=
{
  h := 7
  k := 25
  lower := (5122699/73010000)
  upper := (5137301/73010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_25_interval
}

theorem G7_26_formula : baezDuarteGramEntry 7 26 = vasyuninBEntry 7 26 := vasyuninBEntry_correct_axiom 7 26 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_26_eval :
    ((((59183361/866390000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 26) ∧
    (vasyuninBEntry 7 26 ≤ (((59356639/866390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_726_formula_bound
  constructor <;> linarith

theorem G7_26_interval :
    ((((59183361/866390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 26) ∧
    (baezDuarteGramEntry 7 26 ≤ (((59356639/866390000) : ℚ) : ℝ)) := by
  rw [G7_26_formula]
  exact vasyuninBEntry_7_26_eval

def interval_7_26 : NamedVasyuninInterval :=
{
  h := 7
  k := 26
  lower := (59183361/866390000)
  upper := (59356639/866390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_26_interval
}

theorem G7_27_formula : baezDuarteGramEntry 7 27 = vasyuninBEntry 7 27 := vasyuninBEntry_correct_axiom 7 27 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_27_eval :
    ((((32032073/479270000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 27) ∧
    (vasyuninBEntry 7 27 ≤ (((32127927/479270000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_727_formula_bound
  constructor <;> linarith

theorem G7_27_interval :
    ((((32032073/479270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 27) ∧
    (baezDuarteGramEntry 7 27 ≤ (((32127927/479270000) : ℚ) : ℝ)) := by
  rw [G7_27_formula]
  exact vasyuninBEntry_7_27_eval

def interval_7_27 : NamedVasyuninInterval :=
{
  h := 7
  k := 27
  lower := (32032073/479270000)
  upper := (32127927/479270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_27_interval
}

theorem G7_28_formula : baezDuarteGramEntry 7 28 = vasyuninBEntry 7 28 := vasyuninBEntry_correct_axiom 7 28 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_28_eval :
    ((((1518957/22930000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 28) ∧
    (vasyuninBEntry 7 28 ≤ (((1523543/22930000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 4 7 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 7)
  constructor <;> linarith

theorem G7_28_interval :
    ((((1518957/22930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 28) ∧
    (baezDuarteGramEntry 7 28 ≤ (((1523543/22930000) : ℚ) : ℝ)) := by
  rw [G7_28_formula]
  exact vasyuninBEntry_7_28_eval

def interval_7_28 : NamedVasyuninInterval :=
{
  h := 7
  k := 28
  lower := (1518957/22930000)
  upper := (1523543/22930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_28_interval
}

theorem G7_29_formula : baezDuarteGramEntry 7 29 = vasyuninBEntry 7 29 := vasyuninBEntry_correct_axiom 7 29 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_29_eval :
    ((((58198369/916310000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 29) ∧
    (vasyuninBEntry 7 29 ≤ (((58381631/916310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_729_formula_bound
  constructor <;> linarith

theorem G7_29_interval :
    ((((58198369/916310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 29) ∧
    (baezDuarteGramEntry 7 29 ≤ (((58381631/916310000) : ℚ) : ℝ)) := by
  rw [G7_29_formula]
  exact vasyuninBEntry_7_29_eval

def interval_7_29 : NamedVasyuninInterval :=
{
  h := 7
  k := 29
  lower := (58198369/916310000)
  upper := (58381631/916310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_29_interval
}

theorem G7_30_formula : baezDuarteGramEntry 7 30 = vasyuninBEntry 7 30 := vasyuninBEntry_correct_axiom 7 30 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_30_eval :
    ((((10882351/176490000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 30) ∧
    (vasyuninBEntry 7 30 ≤ (((10917649/176490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_730_formula_bound
  constructor <;> linarith

theorem G7_30_interval :
    ((((10882351/176490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 30) ∧
    (baezDuarteGramEntry 7 30 ≤ (((10917649/176490000) : ℚ) : ℝ)) := by
  rw [G7_30_formula]
  exact vasyuninBEntry_7_30_eval

def interval_7_30 : NamedVasyuninInterval :=
{
  h := 7
  k := 30
  lower := (10882351/176490000)
  upper := (10917649/176490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_30_interval
}

theorem G7_31_formula : baezDuarteGramEntry 7 31 = vasyuninBEntry 7 31 := vasyuninBEntry_correct_axiom 7 31 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_31_eval :
    ((((607739/10110000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 31) ∧
    (vasyuninBEntry 7 31 ≤ (((609761/10110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_731_formula_bound
  constructor <;> linarith

theorem G7_31_interval :
    ((((607739/10110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 31) ∧
    (baezDuarteGramEntry 7 31 ≤ (((609761/10110000) : ℚ) : ℝ)) := by
  rw [G7_31_formula]
  exact vasyuninBEntry_7_31_eval

def interval_7_31 : NamedVasyuninInterval :=
{
  h := 7
  k := 31
  lower := (607739/10110000)
  upper := (609761/10110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_31_interval
}

theorem G7_32_formula : baezDuarteGramEntry 7 32 = vasyuninBEntry 7 32 := vasyuninBEntry_correct_axiom 7 32 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_32_eval :
    ((((4100517/69830000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 32) ∧
    (vasyuninBEntry 7 32 ≤ (((4114483/69830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_732_formula_bound
  constructor <;> linarith

theorem G7_32_interval :
    ((((4100517/69830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 32) ∧
    (baezDuarteGramEntry 7 32 ≤ (((4114483/69830000) : ℚ) : ℝ)) := by
  rw [G7_32_formula]
  exact vasyuninBEntry_7_32_eval

def interval_7_32 : NamedVasyuninInterval :=
{
  h := 7
  k := 32
  lower := (4100517/69830000)
  upper := (4114483/69830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_32_interval
}

theorem G7_33_formula : baezDuarteGramEntry 7 33 = vasyuninBEntry 7 33 := vasyuninBEntry_correct_axiom 7 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_33_eval :
    ((((47127989/820110000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 33) ∧
    (vasyuninBEntry 7 33 ≤ (((47292011/820110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_733_formula_bound
  constructor <;> linarith

theorem G7_33_interval :
    ((((47127989/820110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 33) ∧
    (baezDuarteGramEntry 7 33 ≤ (((47292011/820110000) : ℚ) : ℝ)) := by
  rw [G7_33_formula]
  exact vasyuninBEntry_7_33_eval

def interval_7_33 : NamedVasyuninInterval :=
{
  h := 7
  k := 33
  lower := (47127989/820110000)
  upper := (47292011/820110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_33_interval
}

theorem G7_34_formula : baezDuarteGramEntry 7 34 = vasyuninBEntry 7 34 := vasyuninBEntry_correct_axiom 7 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_34_eval :
    ((((11709253/207470000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 34) ∧
    (vasyuninBEntry 7 34 ≤ (((11750747/207470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_734_formula_bound
  constructor <;> linarith

theorem G7_34_interval :
    ((((11709253/207470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 34) ∧
    (baezDuarteGramEntry 7 34 ≤ (((11750747/207470000) : ℚ) : ℝ)) := by
  rw [G7_34_formula]
  exact vasyuninBEntry_7_34_eval

def interval_7_34 : NamedVasyuninInterval :=
{
  h := 7
  k := 34
  lower := (11709253/207470000)
  upper := (11750747/207470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_34_interval
}

theorem G7_35_formula : baezDuarteGramEntry 7 35 = vasyuninBEntry 7 35 := vasyuninBEntry_correct_axiom 7 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_35_eval :
    ((((5759709/102910000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 35) ∧
    (vasyuninBEntry 7 35 ≤ (((5780291/102910000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 5 7 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 7)
  constructor <;> linarith

theorem G7_35_interval :
    ((((5759709/102910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 35) ∧
    (baezDuarteGramEntry 7 35 ≤ (((5780291/102910000) : ℚ) : ℝ)) := by
  rw [G7_35_formula]
  exact vasyuninBEntry_7_35_eval

def interval_7_35 : NamedVasyuninInterval :=
{
  h := 7
  k := 35
  lower := (5759709/102910000)
  upper := (5780291/102910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_35_interval
}

theorem G7_36_formula : baezDuarteGramEntry 7 36 = vasyuninBEntry 7 36 := vasyuninBEntry_correct_axiom 7 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_36_eval :
    ((((48739947/900530000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 36) ∧
    (vasyuninBEntry 7 36 ≤ (((48920053/900530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_736_formula_bound
  constructor <;> linarith

theorem G7_36_interval :
    ((((48739947/900530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 36) ∧
    (baezDuarteGramEntry 7 36 ≤ (((48920053/900530000) : ℚ) : ℝ)) := by
  rw [G7_36_formula]
  exact vasyuninBEntry_7_36_eval

def interval_7_36 : NamedVasyuninInterval :=
{
  h := 7
  k := 36
  lower := (48739947/900530000)
  upper := (48920053/900530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_36_interval
}

theorem G7_37_formula : baezDuarteGramEntry 7 37 = vasyuninBEntry 7 37 := vasyuninBEntry_correct_axiom 7 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_37_eval :
    ((((48069017/909830000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 37) ∧
    (vasyuninBEntry 7 37 ≤ (((48250983/909830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_737_formula_bound
  constructor <;> linarith

theorem G7_37_interval :
    ((((48069017/909830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 37) ∧
    (baezDuarteGramEntry 7 37 ≤ (((48250983/909830000) : ℚ) : ℝ)) := by
  rw [G7_37_formula]
  exact vasyuninBEntry_7_37_eval

def interval_7_37 : NamedVasyuninInterval :=
{
  h := 7
  k := 37
  lower := (48069017/909830000)
  upper := (48250983/909830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_37_interval
}

theorem G7_38_formula : baezDuarteGramEntry 7 38 = vasyuninBEntry 7 38 := vasyuninBEntry_correct_axiom 7 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_38_eval :
    ((((31459193/608070000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 38) ∧
    (vasyuninBEntry 7 38 ≤ (((31580807/608070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_738_formula_bound
  constructor <;> linarith

theorem G7_38_interval :
    ((((31459193/608070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 38) ∧
    (baezDuarteGramEntry 7 38 ≤ (((31580807/608070000) : ℚ) : ℝ)) := by
  rw [G7_38_formula]
  exact vasyuninBEntry_7_38_eval

def interval_7_38 : NamedVasyuninInterval :=
{
  h := 7
  k := 38
  lower := (31459193/608070000)
  upper := (31580807/608070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_38_interval
}

theorem G7_39_formula : baezDuarteGramEntry 7 39 = vasyuninBEntry 7 39 := vasyuninBEntry_correct_axiom 7 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_39_eval :
    ((((25250233/497670000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 39) ∧
    (vasyuninBEntry 7 39 ≤ (((25349767/497670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_739_formula_bound
  constructor <;> linarith

theorem G7_39_interval :
    ((((25250233/497670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 39) ∧
    (baezDuarteGramEntry 7 39 ≤ (((25349767/497670000) : ℚ) : ℝ)) := by
  rw [G7_39_formula]
  exact vasyuninBEntry_7_39_eval

def interval_7_39 : NamedVasyuninInterval :=
{
  h := 7
  k := 39
  lower := (25250233/497670000)
  upper := (25349767/497670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_39_interval
}

theorem G7_40_formula : baezDuarteGramEntry 7 40 = vasyuninBEntry 7 40 := vasyuninBEntry_correct_axiom 7 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_40_eval :
    ((((47015637/943630000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 40) ∧
    (vasyuninBEntry 7 40 ≤ (((47204363/943630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_740_formula_bound
  constructor <;> linarith

theorem G7_40_interval :
    ((((47015637/943630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 40) ∧
    (baezDuarteGramEntry 7 40 ≤ (((47204363/943630000) : ℚ) : ℝ)) := by
  rw [G7_40_formula]
  exact vasyuninBEntry_7_40_eval

def interval_7_40 : NamedVasyuninInterval :=
{
  h := 7
  k := 40
  lower := (47015637/943630000)
  upper := (47204363/943630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_40_interval
}

theorem G7_41_formula : baezDuarteGramEntry 7 41 = vasyuninBEntry 7 41 := vasyuninBEntry_correct_axiom 7 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_41_eval :
    ((((8067557/164430000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 41) ∧
    (vasyuninBEntry 7 41 ≤ (((8100443/164430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_741_formula_bound
  constructor <;> linarith

theorem G7_41_interval :
    ((((8067557/164430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 41) ∧
    (baezDuarteGramEntry 7 41 ≤ (((8100443/164430000) : ℚ) : ℝ)) := by
  rw [G7_41_formula]
  exact vasyuninBEntry_7_41_eval

def interval_7_41 : NamedVasyuninInterval :=
{
  h := 7
  k := 41
  lower := (8067557/164430000)
  upper := (8100443/164430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_41_interval
}

theorem G7_42_formula : baezDuarteGramEntry 7 42 = vasyuninBEntry 7 42 := vasyuninBEntry_correct_axiom 7 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_42_eval :
    ((((2546769/52310000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 42) ∧
    (vasyuninBEntry 7 42 ≤ (((2557231/52310000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_6_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 6 7 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 7)
  constructor <;> linarith

theorem G7_42_interval :
    ((((2546769/52310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 42) ∧
    (baezDuarteGramEntry 7 42 ≤ (((2557231/52310000) : ℚ) : ℝ)) := by
  rw [G7_42_formula]
  exact vasyuninBEntry_7_42_eval

def interval_7_42 : NamedVasyuninInterval :=
{
  h := 7
  k := 42
  lower := (2546769/52310000)
  upper := (2557231/52310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_42_interval
}

theorem G7_43_formula : baezDuarteGramEntry 7 43 = vasyuninBEntry 7 43 := vasyuninBEntry_correct_axiom 7 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_43_eval :
    ((((20117513/424870000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 43) ∧
    (vasyuninBEntry 7 43 ≤ (((20202487/424870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_743_formula_bound
  constructor <;> linarith

theorem G7_43_interval :
    ((((20117513/424870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 43) ∧
    (baezDuarteGramEntry 7 43 ≤ (((20202487/424870000) : ℚ) : ℝ)) := by
  rw [G7_43_formula]
  exact vasyuninBEntry_7_43_eval

def interval_7_43 : NamedVasyuninInterval :=
{
  h := 7
  k := 43
  lower := (20117513/424870000)
  upper := (20202487/424870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_43_interval
}

theorem G7_44_formula : baezDuarteGramEntry 7 44 = vasyuninBEntry 7 44 := vasyuninBEntry_correct_axiom 7 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_44_eval :
    ((((19662619/423810000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 44) ∧
    (vasyuninBEntry 7 44 ≤ (((19747381/423810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_744_formula_bound
  constructor <;> linarith

theorem G7_44_interval :
    ((((19662619/423810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 44) ∧
    (baezDuarteGramEntry 7 44 ≤ (((19747381/423810000) : ℚ) : ℝ)) := by
  rw [G7_44_formula]
  exact vasyuninBEntry_7_44_eval

def interval_7_44 : NamedVasyuninInterval :=
{
  h := 7
  k := 44
  lower := (19662619/423810000)
  upper := (19747381/423810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_44_interval
}

theorem G7_45_formula : baezDuarteGramEntry 7 45 = vasyuninBEntry 7 45 := vasyuninBEntry_correct_axiom 7 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_45_eval :
    ((((4649797/102030000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 45) ∧
    (vasyuninBEntry 7 45 ≤ (((4670203/102030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_745_formula_bound
  constructor <;> linarith

theorem G7_45_interval :
    ((((4649797/102030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 45) ∧
    (baezDuarteGramEntry 7 45 ≤ (((4670203/102030000) : ℚ) : ℝ)) := by
  rw [G7_45_formula]
  exact vasyuninBEntry_7_45_eval

def interval_7_45 : NamedVasyuninInterval :=
{
  h := 7
  k := 45
  lower := (4649797/102030000)
  upper := (4670203/102030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_45_interval
}

theorem G7_46_formula : baezDuarteGramEntry 7 46 = vasyuninBEntry 7 46 := vasyuninBEntry_correct_axiom 7 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_46_eval :
    ((((8715553/194470000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 46) ∧
    (vasyuninBEntry 7 46 ≤ (((8754447/194470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_746_formula_bound
  constructor <;> linarith

theorem G7_46_interval :
    ((((8715553/194470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 46) ∧
    (baezDuarteGramEntry 7 46 ≤ (((8754447/194470000) : ℚ) : ℝ)) := by
  rw [G7_46_formula]
  exact vasyuninBEntry_7_46_eval

def interval_7_46 : NamedVasyuninInterval :=
{
  h := 7
  k := 46
  lower := (8715553/194470000)
  upper := (8754447/194470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_46_interval
}

theorem G7_47_formula : baezDuarteGramEntry 7 47 = vasyuninBEntry 7 47 := vasyuninBEntry_correct_axiom 7 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_47_eval :
    ((((14417323/326770000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 47) ∧
    (vasyuninBEntry 7 47 ≤ (((14482677/326770000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_747_formula_bound
  constructor <;> linarith

theorem G7_47_interval :
    ((((14417323/326770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 47) ∧
    (baezDuarteGramEntry 7 47 ≤ (((14482677/326770000) : ℚ) : ℝ)) := by
  rw [G7_47_formula]
  exact vasyuninBEntry_7_47_eval

def interval_7_47 : NamedVasyuninInterval :=
{
  h := 7
  k := 47
  lower := (14417323/326770000)
  upper := (14482677/326770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_47_interval
}

theorem G7_48_formula : baezDuarteGramEntry 7 48 = vasyuninBEntry 7 48 := vasyuninBEntry_correct_axiom 7 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_48_eval :
    ((((21395851/491490000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 48) ∧
    (vasyuninBEntry 7 48 ≤ (((21494149/491490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_748_formula_bound
  constructor <;> linarith

theorem G7_48_interval :
    ((((21395851/491490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 48) ∧
    (baezDuarteGramEntry 7 48 ≤ (((21494149/491490000) : ℚ) : ℝ)) := by
  rw [G7_48_formula]
  exact vasyuninBEntry_7_48_eval

def interval_7_48 : NamedVasyuninInterval :=
{
  h := 7
  k := 48
  lower := (21395851/491490000)
  upper := (21494149/491490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_48_interval
}

theorem G7_49_formula : baezDuarteGramEntry 7 49 = vasyuninBEntry 7 49 := vasyuninBEntry_correct_axiom 7 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_49_eval :
    ((((5894363/136370000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 49) ∧
    (vasyuninBEntry 7 49 ≤ (((5921637/136370000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 7 7 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 7)
  constructor <;> linarith

theorem G7_49_interval :
    ((((5894363/136370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 49) ∧
    (baezDuarteGramEntry 7 49 ≤ (((5921637/136370000) : ℚ) : ℝ)) := by
  rw [G7_49_formula]
  exact vasyuninBEntry_7_49_eval

def interval_7_49 : NamedVasyuninInterval :=
{
  h := 7
  k := 49
  lower := (5894363/136370000)
  upper := (5921637/136370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_49_interval
}

theorem G7_50_formula : baezDuarteGramEntry 7 50 = vasyuninBEntry 7 50 := vasyuninBEntry_correct_axiom 7 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_50_eval :
    ((((8150689/193110000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 50) ∧
    (vasyuninBEntry 7 50 ≤ (((8189311/193110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_750_formula_bound
  constructor <;> linarith

theorem G7_50_interval :
    ((((8150689/193110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 50) ∧
    (baezDuarteGramEntry 7 50 ≤ (((8189311/193110000) : ℚ) : ℝ)) := by
  rw [G7_50_formula]
  exact vasyuninBEntry_7_50_eval

def interval_7_50 : NamedVasyuninInterval :=
{
  h := 7
  k := 50
  lower := (8150689/193110000)
  upper := (8189311/193110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_50_interval
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

theorem G8_21_formula : baezDuarteGramEntry 8 21 = vasyuninBEntry 8 21 := vasyuninBEntry_correct_axiom 8 21 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_21_eval :
    ((((32896733/432670000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 21) ∧
    (vasyuninBEntry 8 21 ≤ (((32983267/432670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_821_formula_bound
  constructor <;> linarith

theorem G8_21_interval :
    ((((32896733/432670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 21) ∧
    (baezDuarteGramEntry 8 21 ≤ (((32983267/432670000) : ℚ) : ℝ)) := by
  rw [G8_21_formula]
  exact vasyuninBEntry_8_21_eval

def interval_8_21 : NamedVasyuninInterval :=
{
  h := 8
  k := 21
  lower := (32896733/432670000)
  upper := (32983267/432670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_21_interval
}

theorem G8_22_formula : baezDuarteGramEntry 8 22 = vasyuninBEntry 8 22 := vasyuninBEntry_correct_axiom 8 22 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_22_eval :
    ((((69875447/945530000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 22) ∧
    (vasyuninBEntry 8 22 ≤ (((70064553/945530000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 11 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G8_22_interval :
    ((((69875447/945530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 22) ∧
    (baezDuarteGramEntry 8 22 ≤ (((70064553/945530000) : ℚ) : ℝ)) := by
  rw [G8_22_formula]
  exact vasyuninBEntry_8_22_eval

def interval_8_22 : NamedVasyuninInterval :=
{
  h := 8
  k := 22
  lower := (69875447/945530000)
  upper := (70064553/945530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_22_interval
}

theorem G8_23_formula : baezDuarteGramEntry 8 23 = vasyuninBEntry 8 23 := vasyuninBEntry_correct_axiom 8 23 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_23_eval :
    ((((909141/12590000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 23) ∧
    (vasyuninBEntry 8 23 ≤ (((911659/12590000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_823_formula_bound
  constructor <;> linarith

theorem G8_23_interval :
    ((((909141/12590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 23) ∧
    (baezDuarteGramEntry 8 23 ≤ (((911659/12590000) : ℚ) : ℝ)) := by
  rw [G8_23_formula]
  exact vasyuninBEntry_8_23_eval

def interval_8_23 : NamedVasyuninInterval :=
{
  h := 8
  k := 23
  lower := (909141/12590000)
  upper := (911659/12590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_23_interval
}

theorem G8_24_formula : baezDuarteGramEntry 8 24 = vasyuninBEntry 8 24 := vasyuninBEntry_correct_axiom 8 24 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_24_eval :
    ((((67346171/938290000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 24) ∧
    (vasyuninBEntry 8 24 ≤ (((67533829/938290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 3 8 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 8)
  constructor <;> linarith

theorem G8_24_interval :
    ((((67346171/938290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 24) ∧
    (baezDuarteGramEntry 8 24 ≤ (((67533829/938290000) : ℚ) : ℝ)) := by
  rw [G8_24_formula]
  exact vasyuninBEntry_8_24_eval

def interval_8_24 : NamedVasyuninInterval :=
{
  h := 8
  k := 24
  lower := (67346171/938290000)
  upper := (67533829/938290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_24_interval
}

theorem G8_25_formula : baezDuarteGramEntry 8 25 = vasyuninBEntry 8 25 := vasyuninBEntry_correct_axiom 8 25 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_25_eval :
    ((((39971401/585990000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 25) ∧
    (vasyuninBEntry 8 25 ≤ (((40088599/585990000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_825_formula_bound
  constructor <;> linarith

theorem G8_25_interval :
    ((((39971401/585990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 25) ∧
    (baezDuarteGramEntry 8 25 ≤ (((40088599/585990000) : ℚ) : ℝ)) := by
  rw [G8_25_formula]
  exact vasyuninBEntry_8_25_eval

def interval_8_25 : NamedVasyuninInterval :=
{
  h := 8
  k := 25
  lower := (39971401/585990000)
  upper := (40088599/585990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_25_interval
}

theorem G8_26_formula : baezDuarteGramEntry 8 26 = vasyuninBEntry 8 26 := vasyuninBEntry_correct_axiom 8 26 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_26_eval :
    ((((27463321/416790000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 26) ∧
    (vasyuninBEntry 8 26 ≤ (((27546679/416790000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 13 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G8_26_interval :
    ((((27463321/416790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 26) ∧
    (baezDuarteGramEntry 8 26 ≤ (((27546679/416790000) : ℚ) : ℝ)) := by
  rw [G8_26_formula]
  exact vasyuninBEntry_8_26_eval

def interval_8_26 : NamedVasyuninInterval :=
{
  h := 8
  k := 26
  lower := (27463321/416790000)
  upper := (27546679/416790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_26_interval
}

theorem G8_27_formula : baezDuarteGramEntry 8 27 = vasyuninBEntry 8 27 := vasyuninBEntry_correct_axiom 8 27 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_27_eval :
    ((((8291033/129670000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 27) ∧
    (vasyuninBEntry 8 27 ≤ (((8316967/129670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_827_formula_bound
  constructor <;> linarith

theorem G8_27_interval :
    ((((8291033/129670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 27) ∧
    (baezDuarteGramEntry 8 27 ≤ (((8316967/129670000) : ℚ) : ℝ)) := by
  rw [G8_27_formula]
  exact vasyuninBEntry_8_27_eval

def interval_8_27 : NamedVasyuninInterval :=
{
  h := 8
  k := 27
  lower := (8291033/129670000)
  upper := (8316967/129670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_27_interval
}

theorem G8_28_formula : baezDuarteGramEntry 8 28 = vasyuninBEntry 8 28 := vasyuninBEntry_correct_axiom 8 28 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_28_eval :
    ((((51627357/826430000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 28) ∧
    (vasyuninBEntry 8 28 ≤ (((51792643/826430000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 7 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G8_28_interval :
    ((((51627357/826430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 28) ∧
    (baezDuarteGramEntry 8 28 ≤ (((51792643/826430000) : ℚ) : ℝ)) := by
  rw [G8_28_formula]
  exact vasyuninBEntry_8_28_eval

def interval_8_28 : NamedVasyuninInterval :=
{
  h := 8
  k := 28
  lower := (51627357/826430000)
  upper := (51792643/826430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_28_interval
}

theorem G8_29_formula : baezDuarteGramEntry 8 29 = vasyuninBEntry 8 29 := vasyuninBEntry_correct_axiom 8 29 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_29_eval :
    ((((19837337/326630000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 29) ∧
    (vasyuninBEntry 8 29 ≤ (((19902663/326630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_829_formula_bound
  constructor <;> linarith

theorem G8_29_interval :
    ((((19837337/326630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 29) ∧
    (baezDuarteGramEntry 8 29 ≤ (((19902663/326630000) : ℚ) : ℝ)) := by
  rw [G8_29_formula]
  exact vasyuninBEntry_8_29_eval

def interval_8_29 : NamedVasyuninInterval :=
{
  h := 8
  k := 29
  lower := (19837337/326630000)
  upper := (19902663/326630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_29_interval
}

theorem G8_30_formula : baezDuarteGramEntry 8 30 = vasyuninBEntry 8 30 := vasyuninBEntry_correct_axiom 8 30 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_30_eval :
    ((((36179113/608870000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 30) ∧
    (vasyuninBEntry 8 30 ≤ (((36300887/608870000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_15_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 15 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G8_30_interval :
    ((((36179113/608870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 30) ∧
    (baezDuarteGramEntry 8 30 ≤ (((36300887/608870000) : ℚ) : ℝ)) := by
  rw [G8_30_formula]
  exact vasyuninBEntry_8_30_eval

def interval_8_30 : NamedVasyuninInterval :=
{
  h := 8
  k := 30
  lower := (36179113/608870000)
  upper := (36300887/608870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_30_interval
}

theorem G8_31_formula : baezDuarteGramEntry 8 31 = vasyuninBEntry 8 31 := vasyuninBEntry_correct_axiom 8 31 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_31_eval :
    ((((57152033/979670000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 31) ∧
    (vasyuninBEntry 8 31 ≤ (((57347967/979670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_831_formula_bound
  constructor <;> linarith

theorem G8_31_interval :
    ((((57152033/979670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 31) ∧
    (baezDuarteGramEntry 8 31 ≤ (((57347967/979670000) : ℚ) : ℝ)) := by
  rw [G8_31_formula]
  exact vasyuninBEntry_8_31_eval

def interval_8_31 : NamedVasyuninInterval :=
{
  h := 8
  k := 31
  lower := (57152033/979670000)
  upper := (57347967/979670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_31_interval
}

theorem G8_32_formula : baezDuarteGramEntry 8 32 = vasyuninBEntry 8 32 := vasyuninBEntry_correct_axiom 8 32 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_32_eval :
    ((((18957287/327130000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 32) ∧
    (vasyuninBEntry 8 32 ≤ (((19022713/327130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 4 8 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 8)
  constructor <;> linarith

theorem G8_32_interval :
    ((((18957287/327130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 32) ∧
    (baezDuarteGramEntry 8 32 ≤ (((19022713/327130000) : ℚ) : ℝ)) := by
  rw [G8_32_formula]
  exact vasyuninBEntry_8_32_eval

def interval_8_32 : NamedVasyuninInterval :=
{
  h := 8
  k := 32
  lower := (18957287/327130000)
  upper := (19022713/327130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_32_interval
}

theorem G8_33_formula : baezDuarteGramEntry 8 33 = vasyuninBEntry 8 33 := vasyuninBEntry_correct_axiom 8 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_33_eval :
    ((((53583961/960390000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 33) ∧
    (vasyuninBEntry 8 33 ≤ (((53776039/960390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_833_formula_bound
  constructor <;> linarith

theorem G8_33_interval :
    ((((53583961/960390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 33) ∧
    (baezDuarteGramEntry 8 33 ≤ (((53776039/960390000) : ℚ) : ℝ)) := by
  rw [G8_33_formula]
  exact vasyuninBEntry_8_33_eval

def interval_8_33 : NamedVasyuninInterval :=
{
  h := 8
  k := 33
  lower := (53583961/960390000)
  upper := (53776039/960390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_33_interval
}

theorem G8_34_formula : baezDuarteGramEntry 8 34 = vasyuninBEntry 8 34 := vasyuninBEntry_correct_axiom 8 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_34_eval :
    ((((40116161/738390000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 34) ∧
    (vasyuninBEntry 8 34 ≤ (((40263839/738390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_17_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 17 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G8_34_interval :
    ((((40116161/738390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 34) ∧
    (baezDuarteGramEntry 8 34 ≤ (((40263839/738390000) : ℚ) : ℝ)) := by
  rw [G8_34_formula]
  exact vasyuninBEntry_8_34_eval

def interval_8_34 : NamedVasyuninInterval :=
{
  h := 8
  k := 34
  lower := (40116161/738390000)
  upper := (40263839/738390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_34_interval
}

theorem G8_35_formula : baezDuarteGramEntry 8 35 = vasyuninBEntry 8 35 := vasyuninBEntry_correct_axiom 8 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_35_eval :
    ((((13968677/263230000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 35) ∧
    (vasyuninBEntry 8 35 ≤ (((14021323/263230000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_835_formula_bound
  constructor <;> linarith

theorem G8_35_interval :
    ((((13968677/263230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 35) ∧
    (baezDuarteGramEntry 8 35 ≤ (((14021323/263230000) : ℚ) : ℝ)) := by
  rw [G8_35_formula]
  exact vasyuninBEntry_8_35_eval

def interval_8_35 : NamedVasyuninInterval :=
{
  h := 8
  k := 35
  lower := (13968677/263230000)
  upper := (14021323/263230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_35_interval
}

theorem G8_36_formula : baezDuarteGramEntry 8 36 = vasyuninBEntry 8 36 := vasyuninBEntry_correct_axiom 8 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_36_eval :
    ((((8286091/159090000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 36) ∧
    (vasyuninBEntry 8 36 ≤ (((8317909/159090000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 9 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G8_36_interval :
    ((((8286091/159090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 36) ∧
    (baezDuarteGramEntry 8 36 ≤ (((8317909/159090000) : ℚ) : ℝ)) := by
  rw [G8_36_formula]
  exact vasyuninBEntry_8_36_eval

def interval_8_36 : NamedVasyuninInterval :=
{
  h := 8
  k := 36
  lower := (8286091/159090000)
  upper := (8317909/159090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_36_interval
}

theorem G8_37_formula : baezDuarteGramEntry 8 37 = vasyuninBEntry 8 37 := vasyuninBEntry_correct_axiom 8 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_37_eval :
    ((((43554487/855130000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 37) ∧
    (vasyuninBEntry 8 37 ≤ (((43725513/855130000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_837_formula_bound
  constructor <;> linarith

theorem G8_37_interval :
    ((((43554487/855130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 37) ∧
    (baezDuarteGramEntry 8 37 ≤ (((43725513/855130000) : ℚ) : ℝ)) := by
  rw [G8_37_formula]
  exact vasyuninBEntry_8_37_eval

def interval_8_37 : NamedVasyuninInterval :=
{
  h := 8
  k := 37
  lower := (43554487/855130000)
  upper := (43725513/855130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_37_interval
}

theorem G8_38_formula : baezDuarteGramEntry 8 38 = vasyuninBEntry 8 38 := vasyuninBEntry_correct_axiom 8 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_38_eval :
    ((((41227603/823970000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 38) ∧
    (vasyuninBEntry 8 38 ≤ (((41392397/823970000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 19 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G8_38_interval :
    ((((41227603/823970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 38) ∧
    (baezDuarteGramEntry 8 38 ≤ (((41392397/823970000) : ℚ) : ℝ)) := by
  rw [G8_38_formula]
  exact vasyuninBEntry_8_38_eval

def interval_8_38 : NamedVasyuninInterval :=
{
  h := 8
  k := 38
  lower := (41227603/823970000)
  upper := (41392397/823970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_38_interval
}

theorem G8_39_formula : baezDuarteGramEntry 8 39 = vasyuninBEntry 8 39 := vasyuninBEntry_correct_axiom 8 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_39_eval :
    ((((4020591/81590000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 39) ∧
    (vasyuninBEntry 8 39 ≤ (((4036909/81590000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_839_formula_bound
  constructor <;> linarith

theorem G8_39_interval :
    ((((4020591/81590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 39) ∧
    (baezDuarteGramEntry 8 39 ≤ (((4036909/81590000) : ℚ) : ℝ)) := by
  rw [G8_39_formula]
  exact vasyuninBEntry_8_39_eval

def interval_8_39 : NamedVasyuninInterval :=
{
  h := 8
  k := 39
  lower := (4020591/81590000)
  upper := (4036909/81590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_39_interval
}

theorem G8_40_formula : baezDuarteGramEntry 8 40 = vasyuninBEntry 8 40 := vasyuninBEntry_correct_axiom 8 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_40_eval :
    ((((26116657/533430000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 40) ∧
    (vasyuninBEntry 8 40 ≤ (((26223343/533430000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 5 8 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 8)
  constructor <;> linarith

theorem G8_40_interval :
    ((((26116657/533430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 40) ∧
    (baezDuarteGramEntry 8 40 ≤ (((26223343/533430000) : ℚ) : ℝ)) := by
  rw [G8_40_formula]
  exact vasyuninBEntry_8_40_eval

def interval_8_40 : NamedVasyuninInterval :=
{
  h := 8
  k := 40
  lower := (26116657/533430000)
  upper := (26223343/533430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_40_interval
}

theorem G8_41_formula : baezDuarteGramEntry 8 41 = vasyuninBEntry 8 41 := vasyuninBEntry_correct_axiom 8 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_41_eval :
    ((((5499673/115770000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 41) ∧
    (vasyuninBEntry 8 41 ≤ (((5522827/115770000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_841_formula_bound
  constructor <;> linarith

theorem G8_41_interval :
    ((((5499673/115770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 41) ∧
    (baezDuarteGramEntry 8 41 ≤ (((5522827/115770000) : ℚ) : ℝ)) := by
  rw [G8_41_formula]
  exact vasyuninBEntry_8_41_eval

def interval_8_41 : NamedVasyuninInterval :=
{
  h := 8
  k := 41
  lower := (5499673/115770000)
  upper := (5522827/115770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_41_interval
}

theorem G8_42_formula : baezDuarteGramEntry 8 42 = vasyuninBEntry 8 42 := vasyuninBEntry_correct_axiom 8 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_42_eval :
    ((((756373/16270000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 42) ∧
    (vasyuninBEntry 8 42 ≤ (((759627/16270000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_21_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 21 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G8_42_interval :
    ((((756373/16270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 42) ∧
    (baezDuarteGramEntry 8 42 ≤ (((759627/16270000) : ℚ) : ℝ)) := by
  rw [G8_42_formula]
  exact vasyuninBEntry_8_42_eval

def interval_8_42 : NamedVasyuninInterval :=
{
  h := 8
  k := 42
  lower := (756373/16270000)
  upper := (759627/16270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_42_interval
}

theorem G8_43_formula : baezDuarteGramEntry 8 43 = vasyuninBEntry 8 43 := vasyuninBEntry_correct_axiom 8 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_43_eval :
    ((((44672033/979670000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 43) ∧
    (vasyuninBEntry 8 43 ≤ (((44867967/979670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_843_formula_bound
  constructor <;> linarith

theorem G8_43_interval :
    ((((44672033/979670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 43) ∧
    (baezDuarteGramEntry 8 43 ≤ (((44867967/979670000) : ℚ) : ℝ)) := by
  rw [G8_43_formula]
  exact vasyuninBEntry_8_43_eval

def interval_8_43 : NamedVasyuninInterval :=
{
  h := 8
  k := 43
  lower := (44672033/979670000)
  upper := (44867967/979670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_43_interval
}

theorem G8_44_formula : baezDuarteGramEntry 8 44 = vasyuninBEntry 8 44 := vasyuninBEntry_correct_axiom 8 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_44_eval :
    ((((36538607/813930000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 44) ∧
    (vasyuninBEntry 8 44 ≤ (((36701393/813930000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 11 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G8_44_interval :
    ((((36538607/813930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 44) ∧
    (baezDuarteGramEntry 8 44 ≤ (((36701393/813930000) : ℚ) : ℝ)) := by
  rw [G8_44_formula]
  exact vasyuninBEntry_8_44_eval

def interval_8_44 : NamedVasyuninInterval :=
{
  h := 8
  k := 44
  lower := (36538607/813930000)
  upper := (36701393/813930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_44_interval
}

theorem G8_45_formula : baezDuarteGramEntry 8 45 = vasyuninBEntry 8 45 := vasyuninBEntry_correct_axiom 8 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_45_eval :
    ((((3411259/77410000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 45) ∧
    (vasyuninBEntry 8 45 ≤ (((3426741/77410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_845_formula_bound
  constructor <;> linarith

theorem G8_45_interval :
    ((((3411259/77410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 45) ∧
    (baezDuarteGramEntry 8 45 ≤ (((3426741/77410000) : ℚ) : ℝ)) := by
  rw [G8_45_formula]
  exact vasyuninBEntry_8_45_eval

def interval_8_45 : NamedVasyuninInterval :=
{
  h := 8
  k := 45
  lower := (3411259/77410000)
  upper := (3426741/77410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_45_interval
}

theorem G8_46_formula : baezDuarteGramEntry 8 46 = vasyuninBEntry 8 46 := vasyuninBEntry_correct_axiom 8 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_46_eval :
    ((((855629/19710000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 46) ∧
    (vasyuninBEntry 8 46 ≤ (((859571/19710000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 23 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G8_46_interval :
    ((((855629/19710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 46) ∧
    (baezDuarteGramEntry 8 46 ≤ (((859571/19710000) : ℚ) : ℝ)) := by
  rw [G8_46_formula]
  exact vasyuninBEntry_8_46_eval

def interval_8_46 : NamedVasyuninInterval :=
{
  h := 8
  k := 46
  lower := (855629/19710000)
  upper := (859571/19710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_46_interval
}

theorem G8_47_formula : baezDuarteGramEntry 8 47 = vasyuninBEntry 8 47 := vasyuninBEntry_correct_axiom 8 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_47_eval :
    ((((571167/13330000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 47) ∧
    (vasyuninBEntry 8 47 ≤ (((573833/13330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_847_formula_bound
  constructor <;> linarith

theorem G8_47_interval :
    ((((571167/13330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 47) ∧
    (baezDuarteGramEntry 8 47 ≤ (((573833/13330000) : ℚ) : ℝ)) := by
  rw [G8_47_formula]
  exact vasyuninBEntry_8_47_eval

def interval_8_47 : NamedVasyuninInterval :=
{
  h := 8
  k := 47
  lower := (571167/13330000)
  upper := (573833/13330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_47_interval
}

theorem G8_48_formula : baezDuarteGramEntry 8 48 = vasyuninBEntry 8 48 := vasyuninBEntry_correct_axiom 8 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_48_eval :
    ((((35536557/834430000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 48) ∧
    (vasyuninBEntry 8 48 ≤ (((35703443/834430000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_6_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 6 8 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 8)
  constructor <;> linarith

theorem G8_48_interval :
    ((((35536557/834430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 48) ∧
    (baezDuarteGramEntry 8 48 ≤ (((35703443/834430000) : ℚ) : ℝ)) := by
  rw [G8_48_formula]
  exact vasyuninBEntry_8_48_eval

def interval_8_48 : NamedVasyuninInterval :=
{
  h := 8
  k := 48
  lower := (35536557/834430000)
  upper := (35703443/834430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_48_interval
}

theorem G8_49_formula : baezDuarteGramEntry 8 49 = vasyuninBEntry 8 49 := vasyuninBEntry_correct_axiom 8 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_49_eval :
    ((((25059667/603330000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 49) ∧
    (vasyuninBEntry 8 49 ≤ (((25180333/603330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_849_formula_bound
  constructor <;> linarith

theorem G8_49_interval :
    ((((25059667/603330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 49) ∧
    (baezDuarteGramEntry 8 49 ≤ (((25180333/603330000) : ℚ) : ℝ)) := by
  rw [G8_49_formula]
  exact vasyuninBEntry_8_49_eval

def interval_8_49 : NamedVasyuninInterval :=
{
  h := 8
  k := 49
  lower := (25059667/603330000)
  upper := (25180333/603330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_49_interval
}

theorem G8_50_formula : baezDuarteGramEntry 8 50 = vasyuninBEntry 8 50 := vasyuninBEntry_correct_axiom 8 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_50_eval :
    ((((5546401/135990000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 50) ∧
    (vasyuninBEntry 8 50 ≤ (((5573599/135990000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 25 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G8_50_interval :
    ((((5546401/135990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 50) ∧
    (baezDuarteGramEntry 8 50 ≤ (((5573599/135990000) : ℚ) : ℝ)) := by
  rw [G8_50_formula]
  exact vasyuninBEntry_8_50_eval

def interval_8_50 : NamedVasyuninInterval :=
{
  h := 8
  k := 50
  lower := (5546401/135990000)
  upper := (5573599/135990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_50_interval
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

theorem G9_21_formula : baezDuarteGramEntry 9 21 = vasyuninBEntry 9 21 := vasyuninBEntry_correct_axiom 9 21 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_21_eval :
    ((((65980213/897870000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 21) ∧
    (vasyuninBEntry 9 21 ≤ (((66159787/897870000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 7 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G9_21_interval :
    ((((65980213/897870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 21) ∧
    (baezDuarteGramEntry 9 21 ≤ (((66159787/897870000) : ℚ) : ℝ)) := by
  rw [G9_21_formula]
  exact vasyuninBEntry_9_21_eval

def interval_9_21 : NamedVasyuninInterval :=
{
  h := 9
  k := 21
  lower := (65980213/897870000)
  upper := (66159787/897870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_21_interval
}

theorem G9_22_formula : baezDuarteGramEntry 9 22 = vasyuninBEntry 9 22 := vasyuninBEntry_correct_axiom 9 22 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_22_eval :
    ((((13487/190000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 22) ∧
    (vasyuninBEntry 9 22 ≤ (((541/7600) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_922_formula_bound
  constructor <;> linarith

theorem G9_22_interval :
    ((((13487/190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 22) ∧
    (baezDuarteGramEntry 9 22 ≤ (((541/7600) : ℚ) : ℝ)) := by
  rw [G9_22_formula]
  exact vasyuninBEntry_9_22_eval

def interval_9_22 : NamedVasyuninInterval :=
{
  h := 9
  k := 22
  lower := (13487/190000)
  upper := (541/7600)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_22_interval
}

theorem G9_23_formula : baezDuarteGramEntry 9 23 = vasyuninBEntry 9 23 := vasyuninBEntry_correct_axiom 9 23 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_23_eval :
    ((((29981449/435510000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 23) ∧
    (vasyuninBEntry 9 23 ≤ (((30068551/435510000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_923_formula_bound
  constructor <;> linarith

theorem G9_23_interval :
    ((((29981449/435510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 23) ∧
    (baezDuarteGramEntry 9 23 ≤ (((30068551/435510000) : ℚ) : ℝ)) := by
  rw [G9_23_formula]
  exact vasyuninBEntry_9_23_eval

def interval_9_23 : NamedVasyuninInterval :=
{
  h := 9
  k := 23
  lower := (29981449/435510000)
  upper := (30068551/435510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_23_interval
}

theorem G9_24_formula : baezDuarteGramEntry 9 24 = vasyuninBEntry 9 24 := vasyuninBEntry_correct_axiom 9 24 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_24_eval :
    ((((4010887/59880000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 24) ∧
    (vasyuninBEntry 9 24 ≤ (((4022863/59880000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 8 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G9_24_interval :
    ((((4010887/59880000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 24) ∧
    (baezDuarteGramEntry 9 24 ≤ (((4022863/59880000) : ℚ) : ℝ)) := by
  rw [G9_24_formula]
  exact vasyuninBEntry_9_24_eval

def interval_9_24 : NamedVasyuninInterval :=
{
  h := 9
  k := 24
  lower := (4010887/59880000)
  upper := (4022863/59880000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_24_interval
}

theorem G9_25_formula : baezDuarteGramEntry 9 25 = vasyuninBEntry 9 25 := vasyuninBEntry_correct_axiom 9 25 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_25_eval :
    ((((31516713/482870000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 25) ∧
    (vasyuninBEntry 9 25 ≤ (((31613287/482870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_925_formula_bound
  constructor <;> linarith

theorem G9_25_interval :
    ((((31516713/482870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 25) ∧
    (baezDuarteGramEntry 9 25 ≤ (((31613287/482870000) : ℚ) : ℝ)) := by
  rw [G9_25_formula]
  exact vasyuninBEntry_9_25_eval

def interval_9_25 : NamedVasyuninInterval :=
{
  h := 9
  k := 25
  lower := (31516713/482870000)
  upper := (31613287/482870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_25_interval
}

theorem G9_26_formula : baezDuarteGramEntry 9 26 = vasyuninBEntry 9 26 := vasyuninBEntry_correct_axiom 9 26 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_26_eval :
    ((((8696423/135770000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 26) ∧
    (vasyuninBEntry 9 26 ≤ (((8723577/135770000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_926_formula_bound
  constructor <;> linarith

theorem G9_26_interval :
    ((((8696423/135770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 26) ∧
    (baezDuarteGramEntry 9 26 ≤ (((8723577/135770000) : ℚ) : ℝ)) := by
  rw [G9_26_formula]
  exact vasyuninBEntry_9_26_eval

def interval_9_26 : NamedVasyuninInterval :=
{
  h := 9
  k := 26
  lower := (8696423/135770000)
  upper := (8723577/135770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_26_interval
}

theorem G9_27_formula : baezDuarteGramEntry 9 27 = vasyuninBEntry 9 27 := vasyuninBEntry_correct_axiom 9 27 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_27_eval :
    ((((32169569/504310000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 27) ∧
    (vasyuninBEntry 9 27 ≤ (((32270431/504310000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 3 9 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 9)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 9)
  constructor <;> linarith

theorem G9_27_interval :
    ((((32169569/504310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 27) ∧
    (baezDuarteGramEntry 9 27 ≤ (((32270431/504310000) : ℚ) : ℝ)) := by
  rw [G9_27_formula]
  exact vasyuninBEntry_9_27_eval

def interval_9_27 : NamedVasyuninInterval :=
{
  h := 9
  k := 27
  lower := (32169569/504310000)
  upper := (32270431/504310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_27_interval
}

theorem G9_28_formula : baezDuarteGramEntry 9 28 = vasyuninBEntry 9 28 := vasyuninBEntry_correct_axiom 9 28 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_28_eval :
    ((((2958641/48590000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 28) ∧
    (vasyuninBEntry 9 28 ≤ (((2968359/48590000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_928_formula_bound
  constructor <;> linarith

theorem G9_28_interval :
    ((((2958641/48590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 28) ∧
    (baezDuarteGramEntry 9 28 ≤ (((2968359/48590000) : ℚ) : ℝ)) := by
  rw [G9_28_formula]
  exact vasyuninBEntry_9_28_eval

def interval_9_28 : NamedVasyuninInterval :=
{
  h := 9
  k := 28
  lower := (2958641/48590000)
  upper := (2968359/48590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_28_interval
}

theorem G9_29_formula : baezDuarteGramEntry 9 29 = vasyuninBEntry 9 29 := vasyuninBEntry_correct_axiom 9 29 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_29_eval :
    ((((699813/11870000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 29) ∧
    (vasyuninBEntry 9 29 ≤ (((702187/11870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_929_formula_bound
  constructor <;> linarith

theorem G9_29_interval :
    ((((699813/11870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 29) ∧
    (baezDuarteGramEntry 9 29 ≤ (((702187/11870000) : ℚ) : ℝ)) := by
  rw [G9_29_formula]
  exact vasyuninBEntry_9_29_eval

def interval_9_29 : NamedVasyuninInterval :=
{
  h := 9
  k := 29
  lower := (699813/11870000)
  upper := (702187/11870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_29_interval
}

theorem G9_30_formula : baezDuarteGramEntry 9 30 = vasyuninBEntry 9 30 := vasyuninBEntry_correct_axiom 9 30 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_30_eval :
    ((((7291303/126970000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 30) ∧
    (vasyuninBEntry 9 30 ≤ (((7316697/126970000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 10 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G9_30_interval :
    ((((7291303/126970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 30) ∧
    (baezDuarteGramEntry 9 30 ≤ (((7316697/126970000) : ℚ) : ℝ)) := by
  rw [G9_30_formula]
  exact vasyuninBEntry_9_30_eval

def interval_9_30 : NamedVasyuninInterval :=
{
  h := 9
  k := 30
  lower := (7291303/126970000)
  upper := (7316697/126970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_30_interval
}

theorem G9_31_formula : baezDuarteGramEntry 9 31 = vasyuninBEntry 9 31 := vasyuninBEntry_correct_axiom 9 31 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_31_eval :
    ((((2748841/49090000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 31) ∧
    (vasyuninBEntry 9 31 ≤ (((2758659/49090000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_931_formula_bound
  constructor <;> linarith

theorem G9_31_interval :
    ((((2748841/49090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 31) ∧
    (baezDuarteGramEntry 9 31 ≤ (((2758659/49090000) : ℚ) : ℝ)) := by
  rw [G9_31_formula]
  exact vasyuninBEntry_9_31_eval

def interval_9_31 : NamedVasyuninInterval :=
{
  h := 9
  k := 31
  lower := (2748841/49090000)
  upper := (2758659/49090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_31_interval
}

theorem G9_32_formula : baezDuarteGramEntry 9 32 = vasyuninBEntry 9 32 := vasyuninBEntry_correct_axiom 9 32 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_32_eval :
    ((((10301179/188210000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 32) ∧
    (vasyuninBEntry 9 32 ≤ (((10338821/188210000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_932_formula_bound
  constructor <;> linarith

theorem G9_32_interval :
    ((((10301179/188210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 32) ∧
    (baezDuarteGramEntry 9 32 ≤ (((10338821/188210000) : ℚ) : ℝ)) := by
  rw [G9_32_formula]
  exact vasyuninBEntry_9_32_eval

def interval_9_32 : NamedVasyuninInterval :=
{
  h := 9
  k := 32
  lower := (10301179/188210000)
  upper := (10338821/188210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_32_interval
}

theorem G9_33_formula : baezDuarteGramEntry 9 33 = vasyuninBEntry 9 33 := vasyuninBEntry_correct_axiom 9 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_33_eval :
    ((((14727527/274730000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 33) ∧
    (vasyuninBEntry 9 33 ≤ (((14782473/274730000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 11 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G9_33_interval :
    ((((14727527/274730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 33) ∧
    (baezDuarteGramEntry 9 33 ≤ (((14782473/274730000) : ℚ) : ℝ)) := by
  rw [G9_33_formula]
  exact vasyuninBEntry_9_33_eval

def interval_9_33 : NamedVasyuninInterval :=
{
  h := 9
  k := 33
  lower := (14727527/274730000)
  upper := (14782473/274730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_33_interval
}

theorem G9_34_formula : baezDuarteGramEntry 9 34 = vasyuninBEntry 9 34 := vasyuninBEntry_correct_axiom 9 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_34_eval :
    ((((6567503/124970000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 34) ∧
    (vasyuninBEntry 9 34 ≤ (((6592497/124970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_934_formula_bound
  constructor <;> linarith

theorem G9_34_interval :
    ((((6567503/124970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 34) ∧
    (baezDuarteGramEntry 9 34 ≤ (((6592497/124970000) : ℚ) : ℝ)) := by
  rw [G9_34_formula]
  exact vasyuninBEntry_9_34_eval

def interval_9_34 : NamedVasyuninInterval :=
{
  h := 9
  k := 34
  lower := (6567503/124970000)
  upper := (6592497/124970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_34_interval
}

theorem G9_35_formula : baezDuarteGramEntry 9 35 = vasyuninBEntry 9 35 := vasyuninBEntry_correct_axiom 9 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_35_eval :
    ((((35471471/685290000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 35) ∧
    (vasyuninBEntry 9 35 ≤ (((35608529/685290000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_935_formula_bound
  constructor <;> linarith

theorem G9_35_interval :
    ((((35471471/685290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 35) ∧
    (baezDuarteGramEntry 9 35 ≤ (((35608529/685290000) : ℚ) : ℝ)) := by
  rw [G9_35_formula]
  exact vasyuninBEntry_9_35_eval

def interval_9_35 : NamedVasyuninInterval :=
{
  h := 9
  k := 35
  lower := (35471471/685290000)
  upper := (35608529/685290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_35_interval
}

theorem G9_36_formula : baezDuarteGramEntry 9 36 = vasyuninBEntry 9 36 := vasyuninBEntry_correct_axiom 9 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_36_eval :
    ((((16847287/327130000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 36) ∧
    (vasyuninBEntry 9 36 ≤ (((16912713/327130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 4 9 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 9)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 9)
  constructor <;> linarith

theorem G9_36_interval :
    ((((16847287/327130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 36) ∧
    (baezDuarteGramEntry 9 36 ≤ (((16912713/327130000) : ℚ) : ℝ)) := by
  rw [G9_36_formula]
  exact vasyuninBEntry_9_36_eval

def interval_9_36 : NamedVasyuninInterval :=
{
  h := 9
  k := 36
  lower := (16847287/327130000)
  upper := (16912713/327130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_36_interval
}

theorem G9_37_formula : baezDuarteGramEntry 9 37 = vasyuninBEntry 9 37 := vasyuninBEntry_correct_axiom 9 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_37_eval :
    ((((49260983/990170000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 37) ∧
    (vasyuninBEntry 9 37 ≤ (((49459017/990170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_937_formula_bound
  constructor <;> linarith

theorem G9_37_interval :
    ((((49260983/990170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 37) ∧
    (baezDuarteGramEntry 9 37 ≤ (((49459017/990170000) : ℚ) : ℝ)) := by
  rw [G9_37_formula]
  exact vasyuninBEntry_9_37_eval

def interval_9_37 : NamedVasyuninInterval :=
{
  h := 9
  k := 37
  lower := (49260983/990170000)
  upper := (49459017/990170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_37_interval
}

theorem G9_38_formula : baezDuarteGramEntry 9 38 = vasyuninBEntry 9 38 := vasyuninBEntry_correct_axiom 9 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_38_eval :
    ((((2837903/58470000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 38) ∧
    (vasyuninBEntry 9 38 ≤ (((2849597/58470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_938_formula_bound
  constructor <;> linarith

theorem G9_38_interval :
    ((((2837903/58470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 38) ∧
    (baezDuarteGramEntry 9 38 ≤ (((2849597/58470000) : ℚ) : ℝ)) := by
  rw [G9_38_formula]
  exact vasyuninBEntry_9_38_eval

def interval_9_38 : NamedVasyuninInterval :=
{
  h := 9
  k := 38
  lower := (2837903/58470000)
  upper := (2849597/58470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_38_interval
}

theorem G9_39_formula : baezDuarteGramEntry 9 39 = vasyuninBEntry 9 39 := vasyuninBEntry_correct_axiom 9 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_39_eval :
    ((((16969311/356890000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 39) ∧
    (vasyuninBEntry 9 39 ≤ (((17040689/356890000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 13 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G9_39_interval :
    ((((16969311/356890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 39) ∧
    (baezDuarteGramEntry 9 39 ≤ (((17040689/356890000) : ℚ) : ℝ)) := by
  rw [G9_39_formula]
  exact vasyuninBEntry_9_39_eval

def interval_9_39 : NamedVasyuninInterval :=
{
  h := 9
  k := 39
  lower := (16969311/356890000)
  upper := (17040689/356890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_39_interval
}

theorem G9_40_formula : baezDuarteGramEntry 9 40 = vasyuninBEntry 9 40 := vasyuninBEntry_correct_axiom 9 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_40_eval :
    ((((2338109/50160000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 40) ∧
    (vasyuninBEntry 9 40 ≤ (((2348141/50160000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_940_formula_bound
  constructor <;> linarith

theorem G9_40_interval :
    ((((2338109/50160000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 40) ∧
    (baezDuarteGramEntry 9 40 ≤ (((2348141/50160000) : ℚ) : ℝ)) := by
  rw [G9_40_formula]
  exact vasyuninBEntry_9_40_eval

def interval_9_40 : NamedVasyuninInterval :=
{
  h := 9
  k := 40
  lower := (2338109/50160000)
  upper := (2348141/50160000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_40_interval
}

theorem G9_41_formula : baezDuarteGramEntry 9 41 = vasyuninBEntry 9 41 := vasyuninBEntry_correct_axiom 9 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_41_eval :
    ((((45740069/999310000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 41) ∧
    (vasyuninBEntry 9 41 ≤ (((45939931/999310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_941_formula_bound
  constructor <;> linarith

theorem G9_41_interval :
    ((((45740069/999310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 41) ∧
    (baezDuarteGramEntry 9 41 ≤ (((45939931/999310000) : ℚ) : ℝ)) := by
  rw [G9_41_formula]
  exact vasyuninBEntry_9_41_eval

def interval_9_41 : NamedVasyuninInterval :=
{
  h := 9
  k := 41
  lower := (45740069/999310000)
  upper := (45939931/999310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_41_interval
}

theorem G9_42_formula : baezDuarteGramEntry 9 42 = vasyuninBEntry 9 42 := vasyuninBEntry_correct_axiom 9 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_42_eval :
    ((((41148581/914190000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 42) ∧
    (vasyuninBEntry 9 42 ≤ (((41331419/914190000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_14_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 14 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G9_42_interval :
    ((((41148581/914190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 42) ∧
    (baezDuarteGramEntry 9 42 ≤ (((41331419/914190000) : ℚ) : ℝ)) := by
  rw [G9_42_formula]
  exact vasyuninBEntry_9_42_eval

def interval_9_42 : NamedVasyuninInterval :=
{
  h := 9
  k := 42
  lower := (41148581/914190000)
  upper := (41331419/914190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_42_interval
}

theorem G9_43_formula : baezDuarteGramEntry 9 43 = vasyuninBEntry 9 43 := vasyuninBEntry_correct_axiom 9 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_43_eval :
    ((((1448729/32710000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 43) ∧
    (vasyuninBEntry 9 43 ≤ (((1455271/32710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_943_formula_bound
  constructor <;> linarith

theorem G9_43_interval :
    ((((1448729/32710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 43) ∧
    (baezDuarteGramEntry 9 43 ≤ (((1455271/32710000) : ℚ) : ℝ)) := by
  rw [G9_43_formula]
  exact vasyuninBEntry_9_43_eval

def interval_9_43 : NamedVasyuninInterval :=
{
  h := 9
  k := 43
  lower := (1448729/32710000)
  upper := (1455271/32710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_43_interval
}

theorem G9_44_formula : baezDuarteGramEntry 9 44 = vasyuninBEntry 9 44 := vasyuninBEntry_correct_axiom 9 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_44_eval :
    ((((13763527/314730000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 44) ∧
    (vasyuninBEntry 9 44 ≤ (((13826473/314730000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_944_formula_bound
  constructor <;> linarith

theorem G9_44_interval :
    ((((13763527/314730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 44) ∧
    (baezDuarteGramEntry 9 44 ≤ (((13826473/314730000) : ℚ) : ℝ)) := by
  rw [G9_44_formula]
  exact vasyuninBEntry_9_44_eval

def interval_9_44 : NamedVasyuninInterval :=
{
  h := 9
  k := 44
  lower := (13763527/314730000)
  upper := (13826473/314730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_44_interval
}

theorem G9_45_formula : baezDuarteGramEntry 9 45 = vasyuninBEntry 9 45 := vasyuninBEntry_correct_axiom 9 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_45_eval :
    ((((42761717/982830000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 45) ∧
    (vasyuninBEntry 9 45 ≤ (((42958283/982830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 5 9 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 9)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 9)
  constructor <;> linarith

theorem G9_45_interval :
    ((((42761717/982830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 45) ∧
    (baezDuarteGramEntry 9 45 ≤ (((42958283/982830000) : ℚ) : ℝ)) := by
  rw [G9_45_formula]
  exact vasyuninBEntry_9_45_eval

def interval_9_45 : NamedVasyuninInterval :=
{
  h := 9
  k := 45
  lower := (42761717/982830000)
  upper := (42958283/982830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_45_interval
}

theorem G9_46_formula : baezDuarteGramEntry 9 46 = vasyuninBEntry 9 46 := vasyuninBEntry_correct_axiom 9 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_46_eval :
    ((((7140631/168690000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 46) ∧
    (vasyuninBEntry 9 46 ≤ (((7174369/168690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_946_formula_bound
  constructor <;> linarith

theorem G9_46_interval :
    ((((7140631/168690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 46) ∧
    (baezDuarteGramEntry 9 46 ≤ (((7174369/168690000) : ℚ) : ℝ)) := by
  rw [G9_46_formula]
  exact vasyuninBEntry_9_46_eval

def interval_9_46 : NamedVasyuninInterval :=
{
  h := 9
  k := 46
  lower := (7140631/168690000)
  upper := (7174369/168690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_46_interval
}

theorem G9_47_formula : baezDuarteGramEntry 9 47 = vasyuninBEntry 9 47 := vasyuninBEntry_correct_axiom 9 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_47_eval :
    ((((728993/17570000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 47) ∧
    (vasyuninBEntry 9 47 ≤ (((732507/17570000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_947_formula_bound
  constructor <;> linarith

theorem G9_47_interval :
    ((((728993/17570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 47) ∧
    (baezDuarteGramEntry 9 47 ≤ (((732507/17570000) : ℚ) : ℝ)) := by
  rw [G9_47_formula]
  exact vasyuninBEntry_9_47_eval

def interval_9_47 : NamedVasyuninInterval :=
{
  h := 9
  k := 47
  lower := (728993/17570000)
  upper := (732507/17570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_47_interval
}

theorem G9_48_formula : baezDuarteGramEntry 9 48 = vasyuninBEntry 9 48 := vasyuninBEntry_correct_axiom 9 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_48_eval :
    ((((19761559/484410000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 48) ∧
    (vasyuninBEntry 9 48 ≤ (((19858441/484410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_16_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 16 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G9_48_interval :
    ((((19761559/484410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 48) ∧
    (baezDuarteGramEntry 9 48 ≤ (((19858441/484410000) : ℚ) : ℝ)) := by
  rw [G9_48_formula]
  exact vasyuninBEntry_9_48_eval

def interval_9_48 : NamedVasyuninInterval :=
{
  h := 9
  k := 48
  lower := (19761559/484410000)
  upper := (19858441/484410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_48_interval
}

theorem G9_49_formula : baezDuarteGramEntry 9 49 = vasyuninBEntry 9 49 := vasyuninBEntry_correct_axiom 9 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_49_eval :
    ((((35272109/878910000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 49) ∧
    (vasyuninBEntry 9 49 ≤ (((35447891/878910000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_949_formula_bound
  constructor <;> linarith

theorem G9_49_interval :
    ((((35272109/878910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 49) ∧
    (baezDuarteGramEntry 9 49 ≤ (((35447891/878910000) : ℚ) : ℝ)) := by
  rw [G9_49_formula]
  exact vasyuninBEntry_9_49_eval

def interval_9_49 : NamedVasyuninInterval :=
{
  h := 9
  k := 49
  lower := (35272109/878910000)
  upper := (35447891/878910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_49_interval
}

theorem G9_50_formula : baezDuarteGramEntry 9 50 = vasyuninBEntry 9 50 := vasyuninBEntry_correct_axiom 9 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_50_eval :
    ((((10732847/271530000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 50) ∧
    (vasyuninBEntry 9 50 ≤ (((10787153/271530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_950_formula_bound
  constructor <;> linarith

theorem G9_50_interval :
    ((((10732847/271530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 50) ∧
    (baezDuarteGramEntry 9 50 ≤ (((10787153/271530000) : ℚ) : ℝ)) := by
  rw [G9_50_formula]
  exact vasyuninBEntry_9_50_eval

def interval_9_50 : NamedVasyuninInterval :=
{
  h := 9
  k := 50
  lower := (10732847/271530000)
  upper := (10787153/271530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_50_interval
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

end RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
