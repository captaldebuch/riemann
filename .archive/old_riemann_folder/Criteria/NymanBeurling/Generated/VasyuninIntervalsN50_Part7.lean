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

namespace RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Certificates.Generated

theorem G28_19_formula : baezDuarteGramEntry 28 19 = vasyuninBEntry 19 28 := by
  rw [baezDuarteGramEntry_symm 28 19]
  exact G19_28_formula

theorem G28_19_interval :
    ((((1937337/41630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 19) ∧
    (baezDuarteGramEntry 28 19 ≤ (((1945663/41630000) : ℚ) : ℝ)) := by
  rw [G28_19_formula]
  exact vasyuninBEntry_19_28_eval

def interval_28_19 : NamedVasyuninInterval :=
{
  h := 28
  k := 19
  lower := (1937337/41630000)
  upper := (1945663/41630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_19_interval
}

theorem G28_20_formula : baezDuarteGramEntry 28 20 = vasyuninBEntry 20 28 := by
  rw [baezDuarteGramEntry_symm 28 20]
  exact G20_28_formula

theorem G28_20_interval :
    ((((9070087/199130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 20) ∧
    (baezDuarteGramEntry 28 20 ≤ (((9109913/199130000) : ℚ) : ℝ)) := by
  rw [G28_20_formula]
  exact vasyuninBEntry_20_28_eval

def interval_28_20 : NamedVasyuninInterval :=
{
  h := 28
  k := 20
  lower := (9070087/199130000)
  upper := (9109913/199130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_20_interval
}

theorem G28_21_formula : baezDuarteGramEntry 28 21 = vasyuninBEntry 21 28 := by
  rw [baezDuarteGramEntry_symm 28 21]
  exact G21_28_formula

theorem G28_21_interval :
    ((((12611951/280490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 21) ∧
    (baezDuarteGramEntry 28 21 ≤ (((12668049/280490000) : ℚ) : ℝ)) := by
  rw [G28_21_formula]
  exact vasyuninBEntry_21_28_eval

def interval_28_21 : NamedVasyuninInterval :=
{
  h := 28
  k := 21
  lower := (12611951/280490000)
  upper := (12668049/280490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_21_interval
}

theorem G28_22_formula : baezDuarteGramEntry 28 22 = vasyuninBEntry 22 28 := by
  rw [baezDuarteGramEntry_symm 28 22]
  exact G22_28_formula

theorem G28_22_interval :
    ((((23427001/529990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 22) ∧
    (baezDuarteGramEntry 28 22 ≤ (((23532999/529990000) : ℚ) : ℝ)) := by
  rw [G28_22_formula]
  exact vasyuninBEntry_22_28_eval

def interval_28_22 : NamedVasyuninInterval :=
{
  h := 28
  k := 22
  lower := (23427001/529990000)
  upper := (23532999/529990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_22_interval
}

theorem G28_23_formula : baezDuarteGramEntry 28 23 = vasyuninBEntry 23 28 := by
  rw [baezDuarteGramEntry_symm 28 23]
  exact G23_28_formula

theorem G28_23_interval :
    ((((38142789/872110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 23) ∧
    (baezDuarteGramEntry 28 23 ≤ (((38317211/872110000) : ℚ) : ℝ)) := by
  rw [G28_23_formula]
  exact vasyuninBEntry_23_28_eval

def interval_28_23 : NamedVasyuninInterval :=
{
  h := 28
  k := 23
  lower := (38142789/872110000)
  upper := (38317211/872110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_23_interval
}

theorem G28_24_formula : baezDuarteGramEntry 28 24 = vasyuninBEntry 24 28 := by
  rw [baezDuarteGramEntry_symm 28 24]
  exact G24_28_formula

theorem G28_24_interval :
    ((((20393059/469410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 24) ∧
    (baezDuarteGramEntry 28 24 ≤ (((20486941/469410000) : ℚ) : ℝ)) := by
  rw [G28_24_formula]
  exact vasyuninBEntry_24_28_eval

def interval_28_24 : NamedVasyuninInterval :=
{
  h := 28
  k := 24
  lower := (20393059/469410000)
  upper := (20486941/469410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_24_interval
}

theorem G28_25_formula : baezDuarteGramEntry 28 25 = vasyuninBEntry 25 28 := by
  rw [baezDuarteGramEntry_symm 28 25]
  exact G25_28_formula

theorem G28_25_interval :
    ((((10792559/249410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 25) ∧
    (baezDuarteGramEntry 28 25 ≤ (((10842441/249410000) : ℚ) : ℝ)) := by
  rw [G28_25_formula]
  exact vasyuninBEntry_25_28_eval

def interval_28_25 : NamedVasyuninInterval :=
{
  h := 28
  k := 25
  lower := (10792559/249410000)
  upper := (10842441/249410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_25_interval
}

theorem G28_26_formula : baezDuarteGramEntry 28 26 = vasyuninBEntry 26 28 := by
  rw [baezDuarteGramEntry_symm 28 26]
  exact G26_28_formula

theorem G28_26_interval :
    ((((3821183/88170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 26) ∧
    (baezDuarteGramEntry 28 26 ≤ (((3838817/88170000) : ℚ) : ℝ)) := by
  rw [G28_26_formula]
  exact vasyuninBEntry_26_28_eval

def interval_28_26 : NamedVasyuninInterval :=
{
  h := 28
  k := 26
  lower := (3821183/88170000)
  upper := (3838817/88170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_26_interval
}

theorem G28_27_formula : baezDuarteGramEntry 28 27 = vasyuninBEntry 27 28 := by
  rw [baezDuarteGramEntry_symm 28 27]
  exact G27_28_formula

theorem G28_27_interval :
    ((((42502771/972290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 27) ∧
    (baezDuarteGramEntry 28 27 ≤ (((42697229/972290000) : ℚ) : ℝ)) := by
  rw [G28_27_formula]
  exact vasyuninBEntry_27_28_eval

def interval_28_27 : NamedVasyuninInterval :=
{
  h := 28
  k := 27
  lower := (42502771/972290000)
  upper := (42697229/972290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_27_interval
}

theorem G28_28_formula_eq : baezDuarteGramEntry 28 28 = (1 / (28 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 28 := by norm_num
  rw [baez_duarte_diagonal_scaling 28 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G28_28_log_gamma_interval :
  ((((14168461/315390000) : ℚ) : ℝ) ≤ (1 / (28 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (28 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((14231539/315390000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 28 (by norm_num)
  constructor
  · have : ((((14168461/315390000) : ℚ) : ℝ) ≤ (1 / (28 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (28 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((14231539/315390000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G28_28_interval : ((((14168461/315390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 28) ∧ (baezDuarteGramEntry 28 28 ≤ (((14231539/315390000) : ℚ) : ℝ)) := by
  rw [G28_28_formula_eq]
  exact G28_28_log_gamma_interval

def interval_28_28 : NamedVasyuninInterval :=
{
  h := 28
  k := 28
  lower := (14168461/315390000)
  upper := (14231539/315390000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G28_28_interval
}

theorem G28_29_formula : baezDuarteGramEntry 28 29 = vasyuninBEntry 28 29 := vasyuninBEntry_correct_axiom 28 29 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_29_eval :
    ((((6881203/162970000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 29) ∧
    (vasyuninBEntry 28 29 ≤ (((6913797/162970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2829_formula_bound
  constructor <;> linarith

theorem G28_29_interval :
    ((((6881203/162970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 29) ∧
    (baezDuarteGramEntry 28 29 ≤ (((6913797/162970000) : ℚ) : ℝ)) := by
  rw [G28_29_formula]
  exact vasyuninBEntry_28_29_eval

def interval_28_29 : NamedVasyuninInterval :=
{
  h := 28
  k := 29
  lower := (6881203/162970000)
  upper := (6913797/162970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_29_interval
}

theorem G28_30_formula : baezDuarteGramEntry 28 30 = vasyuninBEntry 28 30 := vasyuninBEntry_correct_axiom 28 30 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_30_eval :
    ((((24539363/606370000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 30) ∧
    (vasyuninBEntry 28 30 ≤ (((24660637/606370000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_14_15_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 14 15 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G28_30_interval :
    ((((24539363/606370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 30) ∧
    (baezDuarteGramEntry 28 30 ≤ (((24660637/606370000) : ℚ) : ℝ)) := by
  rw [G28_30_formula]
  exact vasyuninBEntry_28_30_eval

def interval_28_30 : NamedVasyuninInterval :=
{
  h := 28
  k := 30
  lower := (24539363/606370000)
  upper := (24660637/606370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_30_interval
}

theorem G28_31_formula : baezDuarteGramEntry 28 31 = vasyuninBEntry 28 31 := vasyuninBEntry_correct_axiom 28 31 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_31_eval :
    ((((35299649/903510000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 31) ∧
    (vasyuninBEntry 28 31 ≤ (((35480351/903510000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2831_formula_bound
  constructor <;> linarith

theorem G28_31_interval :
    ((((35299649/903510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 31) ∧
    (baezDuarteGramEntry 28 31 ≤ (((35480351/903510000) : ℚ) : ℝ)) := by
  rw [G28_31_formula]
  exact vasyuninBEntry_28_31_eval

def interval_28_31 : NamedVasyuninInterval :=
{
  h := 28
  k := 31
  lower := (35299649/903510000)
  upper := (35480351/903510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_31_interval
}

theorem G28_32_formula : baezDuarteGramEntry 28 32 = vasyuninBEntry 28 32 := vasyuninBEntry_correct_axiom 28 32 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_32_eval :
    ((((3290071/86790000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 32) ∧
    (vasyuninBEntry 28 32 ≤ (((3307429/86790000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 8 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G28_32_interval :
    ((((3290071/86790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 32) ∧
    (baezDuarteGramEntry 28 32 ≤ (((3307429/86790000) : ℚ) : ℝ)) := by
  rw [G28_32_formula]
  exact vasyuninBEntry_28_32_eval

def interval_28_32 : NamedVasyuninInterval :=
{
  h := 28
  k := 32
  lower := (3290071/86790000)
  upper := (3307429/86790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_32_interval
}

theorem G28_33_formula : baezDuarteGramEntry 28 33 = vasyuninBEntry 28 33 := vasyuninBEntry_correct_axiom 28 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_33_eval :
    ((((19158051/519490000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 33) ∧
    (vasyuninBEntry 28 33 ≤ (((19261949/519490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2833_formula_bound
  constructor <;> linarith

theorem G28_33_interval :
    ((((19158051/519490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 33) ∧
    (baezDuarteGramEntry 28 33 ≤ (((19261949/519490000) : ℚ) : ℝ)) := by
  rw [G28_33_formula]
  exact vasyuninBEntry_28_33_eval

def interval_28_33 : NamedVasyuninInterval :=
{
  h := 28
  k := 33
  lower := (19158051/519490000)
  upper := (19261949/519490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_33_interval
}

theorem G28_34_formula : baezDuarteGramEntry 28 34 = vasyuninBEntry 28 34 := vasyuninBEntry_correct_axiom 28 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_34_eval :
    ((((1914679/53210000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 34) ∧
    (vasyuninBEntry 28 34 ≤ (((1925321/53210000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_14_17_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 14 17 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G28_34_interval :
    ((((1914679/53210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 34) ∧
    (baezDuarteGramEntry 28 34 ≤ (((1925321/53210000) : ℚ) : ℝ)) := by
  rw [G28_34_formula]
  exact vasyuninBEntry_28_34_eval

def interval_28_34 : NamedVasyuninInterval :=
{
  h := 28
  k := 34
  lower := (1914679/53210000)
  upper := (1925321/53210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_34_interval
}

theorem G28_35_formula : baezDuarteGramEntry 28 35 = vasyuninBEntry 28 35 := vasyuninBEntry_correct_axiom 28 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_35_eval :
    ((((16752461/475390000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 35) ∧
    (vasyuninBEntry 28 35 ≤ (((16847539/475390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 5 7 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 7)
  constructor <;> linarith

theorem G28_35_interval :
    ((((16752461/475390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 35) ∧
    (baezDuarteGramEntry 28 35 ≤ (((16847539/475390000) : ℚ) : ℝ)) := by
  rw [G28_35_formula]
  exact vasyuninBEntry_28_35_eval

def interval_28_35 : NamedVasyuninInterval :=
{
  h := 28
  k := 35
  lower := (16752461/475390000)
  upper := (16847539/475390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_35_interval
}

theorem G28_36_formula : baezDuarteGramEntry 28 36 = vasyuninBEntry 28 36 := vasyuninBEntry_correct_axiom 28 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_36_eval :
    ((((5837061/169390000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 36) ∧
    (vasyuninBEntry 28 36 ≤ (((5870939/169390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 9 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G28_36_interval :
    ((((5837061/169390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 36) ∧
    (baezDuarteGramEntry 28 36 ≤ (((5870939/169390000) : ℚ) : ℝ)) := by
  rw [G28_36_formula]
  exact vasyuninBEntry_28_36_eval

def interval_28_36 : NamedVasyuninInterval :=
{
  h := 28
  k := 36
  lower := (5837061/169390000)
  upper := (5870939/169390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_36_interval
}

theorem G28_37_formula : baezDuarteGramEntry 28 37 = vasyuninBEntry 28 37 := vasyuninBEntry_correct_axiom 28 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_37_eval :
    ((((2367003/69970000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 37) ∧
    (vasyuninBEntry 28 37 ≤ (((2380997/69970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2837_formula_bound
  constructor <;> linarith

theorem G28_37_interval :
    ((((2367003/69970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 37) ∧
    (baezDuarteGramEntry 28 37 ≤ (((2380997/69970000) : ℚ) : ℝ)) := by
  rw [G28_37_formula]
  exact vasyuninBEntry_28_37_eval

def interval_28_37 : NamedVasyuninInterval :=
{
  h := 28
  k := 37
  lower := (2367003/69970000)
  upper := (2380997/69970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_37_interval
}

theorem G28_38_formula : baezDuarteGramEntry 28 38 = vasyuninBEntry 28 38 := vasyuninBEntry_correct_axiom 28 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_38_eval :
    ((((9915119/298810000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 38) ∧
    (vasyuninBEntry 28 38 ≤ (((9974881/298810000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_14_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 14 19 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G28_38_interval :
    ((((9915119/298810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 38) ∧
    (baezDuarteGramEntry 28 38 ≤ (((9974881/298810000) : ℚ) : ℝ)) := by
  rw [G28_38_formula]
  exact vasyuninBEntry_28_38_eval

def interval_28_38 : NamedVasyuninInterval :=
{
  h := 28
  k := 38
  lower := (9915119/298810000)
  upper := (9974881/298810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_38_interval
}

theorem G28_39_formula : baezDuarteGramEntry 28 39 = vasyuninBEntry 28 39 := vasyuninBEntry_correct_axiom 28 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_39_eval :
    ((((30426651/933490000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 39) ∧
    (vasyuninBEntry 28 39 ≤ (((30613349/933490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2839_formula_bound
  constructor <;> linarith

theorem G28_39_interval :
    ((((30426651/933490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 39) ∧
    (baezDuarteGramEntry 28 39 ≤ (((30613349/933490000) : ℚ) : ℝ)) := by
  rw [G28_39_formula]
  exact vasyuninBEntry_28_39_eval

def interval_28_39 : NamedVasyuninInterval :=
{
  h := 28
  k := 39
  lower := (30426651/933490000)
  upper := (30613349/933490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_39_interval
}

theorem G28_40_formula : baezDuarteGramEntry 28 40 = vasyuninBEntry 28 40 := vasyuninBEntry_correct_axiom 28 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_40_eval :
    ((((3686509/114910000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 40) ∧
    (vasyuninBEntry 28 40 ≤ (((3709491/114910000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 10 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G28_40_interval :
    ((((3686509/114910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 40) ∧
    (baezDuarteGramEntry 28 40 ≤ (((3709491/114910000) : ℚ) : ℝ)) := by
  rw [G28_40_formula]
  exact vasyuninBEntry_28_40_eval

def interval_28_40 : NamedVasyuninInterval :=
{
  h := 28
  k := 40
  lower := (3686509/114910000)
  upper := (3709491/114910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_40_interval
}

theorem G28_41_formula : baezDuarteGramEntry 28 41 = vasyuninBEntry 28 41 := vasyuninBEntry_correct_axiom 28 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_41_eval :
    ((((30324157/958430000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 41) ∧
    (vasyuninBEntry 28 41 ≤ (((30515843/958430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2841_formula_bound
  constructor <;> linarith

theorem G28_41_interval :
    ((((30324157/958430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 41) ∧
    (baezDuarteGramEntry 28 41 ≤ (((30515843/958430000) : ℚ) : ℝ)) := by
  rw [G28_41_formula]
  exact vasyuninBEntry_28_41_eval

def interval_28_41 : NamedVasyuninInterval :=
{
  h := 28
  k := 41
  lower := (30324157/958430000)
  upper := (30515843/958430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_41_interval
}

theorem G28_42_formula : baezDuarteGramEntry 28 42 = vasyuninBEntry 28 42 := vasyuninBEntry_correct_axiom 28 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_42_eval :
    ((((29246879/931210000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 42) ∧
    (vasyuninBEntry 28 42 ≤ (((29433121/931210000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 14 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 14)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 14)
  constructor <;> linarith

theorem G28_42_interval :
    ((((29246879/931210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 42) ∧
    (baezDuarteGramEntry 28 42 ≤ (((29433121/931210000) : ℚ) : ℝ)) := by
  rw [G28_42_formula]
  exact vasyuninBEntry_28_42_eval

def interval_28_42 : NamedVasyuninInterval :=
{
  h := 28
  k := 42
  lower := (29246879/931210000)
  upper := (29433121/931210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_42_interval
}

theorem G28_43_formula : baezDuarteGramEntry 28 43 = vasyuninBEntry 28 43 := vasyuninBEntry_correct_axiom 28 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_43_eval :
    ((((10924419/355810000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 43) ∧
    (vasyuninBEntry 28 43 ≤ (((10995581/355810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2843_formula_bound
  constructor <;> linarith

theorem G28_43_interval :
    ((((10924419/355810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 43) ∧
    (baezDuarteGramEntry 28 43 ≤ (((10995581/355810000) : ℚ) : ℝ)) := by
  rw [G28_43_formula]
  exact vasyuninBEntry_28_43_eval

def interval_28_43 : NamedVasyuninInterval :=
{
  h := 28
  k := 43
  lower := (10924419/355810000)
  upper := (10995581/355810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_43_interval
}

theorem G28_44_formula : baezDuarteGramEntry 28 44 = vasyuninBEntry 28 44 := vasyuninBEntry_correct_axiom 28 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_44_eval :
    ((((29223251/967490000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 44) ∧
    (vasyuninBEntry 28 44 ≤ (((29416749/967490000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 11 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G28_44_interval :
    ((((29223251/967490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 44) ∧
    (baezDuarteGramEntry 28 44 ≤ (((29416749/967490000) : ℚ) : ℝ)) := by
  rw [G28_44_formula]
  exact vasyuninBEntry_28_44_eval

def interval_28_44 : NamedVasyuninInterval :=
{
  h := 28
  k := 44
  lower := (29223251/967490000)
  upper := (29416749/967490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_44_interval
}

theorem G28_45_formula : baezDuarteGramEntry 28 45 = vasyuninBEntry 28 45 := vasyuninBEntry_correct_axiom 28 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_45_eval :
    ((((13135873/441270000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 45) ∧
    (vasyuninBEntry 28 45 ≤ (((13224127/441270000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2845_formula_bound
  constructor <;> linarith

theorem G28_45_interval :
    ((((13135873/441270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 45) ∧
    (baezDuarteGramEntry 28 45 ≤ (((13224127/441270000) : ℚ) : ℝ)) := by
  rw [G28_45_formula]
  exact vasyuninBEntry_28_45_eval

def interval_28_45 : NamedVasyuninInterval :=
{
  h := 28
  k := 45
  lower := (13135873/441270000)
  upper := (13224127/441270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_45_interval
}

theorem G28_46_formula : baezDuarteGramEntry 28 46 = vasyuninBEntry 28 46 := vasyuninBEntry_correct_axiom 28 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_46_eval :
    ((((17769529/604710000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 46) ∧
    (vasyuninBEntry 28 46 ≤ (((17890471/604710000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_14_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 14 23 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G28_46_interval :
    ((((17769529/604710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 46) ∧
    (baezDuarteGramEntry 28 46 ≤ (((17890471/604710000) : ℚ) : ℝ)) := by
  rw [G28_46_formula]
  exact vasyuninBEntry_28_46_eval

def interval_28_46 : NamedVasyuninInterval :=
{
  h := 28
  k := 46
  lower := (17769529/604710000)
  upper := (17890471/604710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_46_interval
}

theorem G28_47_formula : baezDuarteGramEntry 28 47 = vasyuninBEntry 28 47 := vasyuninBEntry_correct_axiom 28 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_47_eval :
    ((((4786019/164810000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 47) ∧
    (vasyuninBEntry 28 47 ≤ (((4818981/164810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2847_formula_bound
  constructor <;> linarith

theorem G28_47_interval :
    ((((4786019/164810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 47) ∧
    (baezDuarteGramEntry 28 47 ≤ (((4818981/164810000) : ℚ) : ℝ)) := by
  rw [G28_47_formula]
  exact vasyuninBEntry_28_47_eval

def interval_28_47 : NamedVasyuninInterval :=
{
  h := 28
  k := 47
  lower := (4786019/164810000)
  upper := (4818981/164810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_47_interval
}

theorem G28_48_formula : baezDuarteGramEntry 28 48 = vasyuninBEntry 28 48 := vasyuninBEntry_correct_axiom 28 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_48_eval :
    ((((23637571/824290000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 48) ∧
    (vasyuninBEntry 28 48 ≤ (((23802429/824290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_12_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 12 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G28_48_interval :
    ((((23637571/824290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 48) ∧
    (baezDuarteGramEntry 28 48 ≤ (((23802429/824290000) : ℚ) : ℝ)) := by
  rw [G28_48_formula]
  exact vasyuninBEntry_28_48_eval

def interval_28_48 : NamedVasyuninInterval :=
{
  h := 28
  k := 48
  lower := (23637571/824290000)
  upper := (23802429/824290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_48_interval
}

theorem G28_49_formula : baezDuarteGramEntry 28 49 = vasyuninBEntry 28 49 := vasyuninBEntry_correct_axiom 28 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_49_eval :
    ((((7035219/247810000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 49) ∧
    (vasyuninBEntry 28 49 ≤ (((7084781/247810000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 7 7 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 7)
  constructor <;> linarith

theorem G28_49_interval :
    ((((7035219/247810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 49) ∧
    (baezDuarteGramEntry 28 49 ≤ (((7084781/247810000) : ℚ) : ℝ)) := by
  rw [G28_49_formula]
  exact vasyuninBEntry_28_49_eval

def interval_28_49 : NamedVasyuninInterval :=
{
  h := 28
  k := 49
  lower := (7035219/247810000)
  upper := (7084781/247810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_49_interval
}

theorem G28_50_formula : baezDuarteGramEntry 28 50 = vasyuninBEntry 28 50 := vasyuninBEntry_correct_axiom 28 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_28_50_eval :
    ((((4421751/157490000) : ℚ) : ℝ) ≤ vasyuninBEntry 28 50) ∧
    (vasyuninBEntry 28 50 ≤ (((4453249/157490000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_14_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 14 25 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G28_50_interval :
    ((((4421751/157490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 28 50) ∧
    (baezDuarteGramEntry 28 50 ≤ (((4453249/157490000) : ℚ) : ℝ)) := by
  rw [G28_50_formula]
  exact vasyuninBEntry_28_50_eval

def interval_28_50 : NamedVasyuninInterval :=
{
  h := 28
  k := 50
  lower := (4421751/157490000)
  upper := (4453249/157490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G28_50_interval
}

theorem G29_1_formula : baezDuarteGramEntry 29 1 = vasyuninBEntry 1 29 := by
  rw [baezDuarteGramEntry_symm 29 1]
  exact G1_29_formula

theorem G29_1_interval :
    ((((81985563/844370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 1) ∧
    (baezDuarteGramEntry 29 1 ≤ (((82154437/844370000) : ℚ) : ℝ)) := by
  rw [G29_1_formula]
  exact vasyuninBEntry_1_29_eval

def interval_29_1 : NamedVasyuninInterval :=
{
  h := 29
  k := 1
  lower := (81985563/844370000)
  upper := (82154437/844370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_1_interval
}

theorem G29_2_formula : baezDuarteGramEntry 29 2 = vasyuninBEntry 2 29 := by
  rw [baezDuarteGramEntry_symm 29 2]
  exact G2_29_formula

theorem G29_2_interval :
    ((((37485869/441310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 2) ∧
    (baezDuarteGramEntry 29 2 ≤ (((37574131/441310000) : ℚ) : ℝ)) := by
  rw [G29_2_formula]
  exact vasyuninBEntry_2_29_eval

def interval_29_2 : NamedVasyuninInterval :=
{
  h := 29
  k := 2
  lower := (37485869/441310000)
  upper := (37574131/441310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_2_interval
}

theorem G29_3_formula : baezDuarteGramEntry 29 3 = vasyuninBEntry 3 29 := by
  rw [baezDuarteGramEntry_symm 29 3]
  exact G3_29_formula

theorem G29_3_interval :
    ((((11764897/151030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 3) ∧
    (baezDuarteGramEntry 29 3 ≤ (((11795103/151030000) : ℚ) : ℝ)) := by
  rw [G29_3_formula]
  exact vasyuninBEntry_3_29_eval

def interval_29_3 : NamedVasyuninInterval :=
{
  h := 29
  k := 3
  lower := (11764897/151030000)
  upper := (11795103/151030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_3_interval
}

theorem G29_4_formula : baezDuarteGramEntry 29 4 = vasyuninBEntry 4 29 := by
  rw [baezDuarteGramEntry_symm 29 4]
  exact G4_29_formula

theorem G29_4_interval :
    ((((686559/9410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 4) ∧
    (baezDuarteGramEntry 29 4 ≤ (((688441/9410000) : ℚ) : ℝ)) := by
  rw [G29_4_formula]
  exact vasyuninBEntry_4_29_eval

def interval_29_4 : NamedVasyuninInterval :=
{
  h := 29
  k := 4
  lower := (686559/9410000)
  upper := (688441/9410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_4_interval
}

theorem G29_5_formula : baezDuarteGramEntry 29 5 = vasyuninBEntry 5 29 := by
  rw [baezDuarteGramEntry_symm 29 5]
  exact G5_29_formula

theorem G29_5_interval :
    ((((12793493/185070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 5) ∧
    (baezDuarteGramEntry 29 5 ≤ (((12830507/185070000) : ℚ) : ℝ)) := by
  rw [G29_5_formula]
  exact vasyuninBEntry_5_29_eval

def interval_29_5 : NamedVasyuninInterval :=
{
  h := 29
  k := 5
  lower := (12793493/185070000)
  upper := (12830507/185070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_5_interval
}

theorem G29_6_formula : baezDuarteGramEntry 29 6 = vasyuninBEntry 6 29 := by
  rw [baezDuarteGramEntry_symm 29 6]
  exact G6_29_formula

theorem G29_6_interval :
    ((((17842981/270190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 6) ∧
    (baezDuarteGramEntry 29 6 ≤ (((17897019/270190000) : ℚ) : ℝ)) := by
  rw [G29_6_formula]
  exact vasyuninBEntry_6_29_eval

def interval_29_6 : NamedVasyuninInterval :=
{
  h := 29
  k := 6
  lower := (17842981/270190000)
  upper := (17897019/270190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_6_interval
}

theorem G29_7_formula : baezDuarteGramEntry 29 7 = vasyuninBEntry 7 29 := by
  rw [baezDuarteGramEntry_symm 29 7]
  exact G7_29_formula

theorem G29_7_interval :
    ((((58198369/916310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 7) ∧
    (baezDuarteGramEntry 29 7 ≤ (((58381631/916310000) : ℚ) : ℝ)) := by
  rw [G29_7_formula]
  exact vasyuninBEntry_7_29_eval

def interval_29_7 : NamedVasyuninInterval :=
{
  h := 29
  k := 7
  lower := (58198369/916310000)
  upper := (58381631/916310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_7_interval
}

theorem G29_8_formula : baezDuarteGramEntry 29 8 = vasyuninBEntry 8 29 := by
  rw [baezDuarteGramEntry_symm 29 8]
  exact G8_29_formula

theorem G29_8_interval :
    ((((19837337/326630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 8) ∧
    (baezDuarteGramEntry 29 8 ≤ (((19902663/326630000) : ℚ) : ℝ)) := by
  rw [G29_8_formula]
  exact vasyuninBEntry_8_29_eval

def interval_29_8 : NamedVasyuninInterval :=
{
  h := 29
  k := 8
  lower := (19837337/326630000)
  upper := (19902663/326630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_8_interval
}

theorem G29_9_formula : baezDuarteGramEntry 29 9 = vasyuninBEntry 9 29 := by
  rw [baezDuarteGramEntry_symm 29 9]
  exact G9_29_formula

theorem G29_9_interval :
    ((((699813/11870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 9) ∧
    (baezDuarteGramEntry 29 9 ≤ (((702187/11870000) : ℚ) : ℝ)) := by
  rw [G29_9_formula]
  exact vasyuninBEntry_9_29_eval

def interval_29_9 : NamedVasyuninInterval :=
{
  h := 29
  k := 9
  lower := (699813/11870000)
  upper := (702187/11870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_9_interval
}

theorem G29_10_formula : baezDuarteGramEntry 29 10 = vasyuninBEntry 10 29 := by
  rw [baezDuarteGramEntry_symm 29 10]
  exact G10_29_formula

theorem G29_10_interval :
    ((((10078489/175110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 10) ∧
    (baezDuarteGramEntry 29 10 ≤ (((10113511/175110000) : ℚ) : ℝ)) := by
  rw [G29_10_formula]
  exact vasyuninBEntry_10_29_eval

def interval_29_10 : NamedVasyuninInterval :=
{
  h := 29
  k := 10
  lower := (10078489/175110000)
  upper := (10113511/175110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_10_interval
}

theorem G29_11_formula : baezDuarteGramEntry 29 11 = vasyuninBEntry 11 29 := by
  rw [baezDuarteGramEntry_symm 29 11]
  exact G11_29_formula

theorem G29_11_interval :
    ((((54900389/996110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 11) ∧
    (baezDuarteGramEntry 29 11 ≤ (((55099611/996110000) : ℚ) : ℝ)) := by
  rw [G29_11_formula]
  exact vasyuninBEntry_11_29_eval

def interval_29_11 : NamedVasyuninInterval :=
{
  h := 29
  k := 11
  lower := (54900389/996110000)
  upper := (55099611/996110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_11_interval
}

theorem G29_12_formula : baezDuarteGramEntry 29 12 = vasyuninBEntry 12 29 := by
  rw [baezDuarteGramEntry_symm 29 12]
  exact G12_29_formula

theorem G29_12_interval :
    ((((47351681/883190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 12) ∧
    (baezDuarteGramEntry 29 12 ≤ (((47528319/883190000) : ℚ) : ℝ)) := by
  rw [G29_12_formula]
  exact vasyuninBEntry_12_29_eval

def interval_29_12 : NamedVasyuninInterval :=
{
  h := 29
  k := 12
  lower := (47351681/883190000)
  upper := (47528319/883190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_12_interval
}

theorem G29_13_formula : baezDuarteGramEntry 29 13 = vasyuninBEntry 13 29 := by
  rw [baezDuarteGramEntry_symm 29 13]
  exact G13_29_formula

theorem G29_13_interval :
    ((((9853757/187430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 13) ∧
    (baezDuarteGramEntry 29 13 ≤ (((9891243/187430000) : ℚ) : ℝ)) := by
  rw [G29_13_formula]
  exact vasyuninBEntry_13_29_eval

def interval_29_13 : NamedVasyuninInterval :=
{
  h := 29
  k := 13
  lower := (9853757/187430000)
  upper := (9891243/187430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_13_interval
}

theorem G29_14_formula : baezDuarteGramEntry 29 14 = vasyuninBEntry 14 29 := by
  rw [baezDuarteGramEntry_symm 29 14]
  exact G14_29_formula

theorem G29_14_interval :
    ((((43447003/829970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 14) ∧
    (baezDuarteGramEntry 29 14 ≤ (((43612997/829970000) : ℚ) : ℝ)) := by
  rw [G29_14_formula]
  exact vasyuninBEntry_14_29_eval

def interval_29_14 : NamedVasyuninInterval :=
{
  h := 29
  k := 14
  lower := (43447003/829970000)
  upper := (43612997/829970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_14_interval
}

theorem G29_15_formula : baezDuarteGramEntry 29 15 = vasyuninBEntry 15 29 := by
  rw [baezDuarteGramEntry_symm 29 15]
  exact G15_29_formula

theorem G29_15_interval :
    ((((14501609/283910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 15) ∧
    (baezDuarteGramEntry 29 15 ≤ (((14558391/283910000) : ℚ) : ℝ)) := by
  rw [G29_15_formula]
  exact vasyuninBEntry_15_29_eval

def interval_29_15 : NamedVasyuninInterval :=
{
  h := 29
  k := 15
  lower := (14501609/283910000)
  upper := (14558391/283910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_15_interval
}

theorem G29_16_formula : baezDuarteGramEntry 29 16 = vasyuninBEntry 16 29 := by
  rw [baezDuarteGramEntry_symm 29 16]
  exact G16_29_formula

theorem G29_16_interval :
    ((((2229189/45610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 16) ∧
    (baezDuarteGramEntry 29 16 ≤ (((2238311/45610000) : ℚ) : ℝ)) := by
  rw [G29_16_formula]
  exact vasyuninBEntry_16_29_eval

def interval_29_16 : NamedVasyuninInterval :=
{
  h := 29
  k := 16
  lower := (2229189/45610000)
  upper := (2238311/45610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_16_interval
}

theorem G29_17_formula : baezDuarteGramEntry 29 17 = vasyuninBEntry 17 29 := by
  rw [baezDuarteGramEntry_symm 29 17]
  exact G17_29_formula

theorem G29_17_interval :
    ((((202947/4280000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 17) ∧
    (baezDuarteGramEntry 29 17 ≤ (((203803/4280000) : ℚ) : ℝ)) := by
  rw [G29_17_formula]
  exact vasyuninBEntry_17_29_eval

def interval_29_17 : NamedVasyuninInterval :=
{
  h := 29
  k := 17
  lower := (202947/4280000)
  upper := (203803/4280000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_17_interval
}

theorem G29_18_formula : baezDuarteGramEntry 29 18 = vasyuninBEntry 18 29 := by
  rw [baezDuarteGramEntry_symm 29 18]
  exact G18_29_formula

theorem G29_18_interval :
    ((((29725781/642190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 18) ∧
    (baezDuarteGramEntry 29 18 ≤ (((29854219/642190000) : ℚ) : ℝ)) := by
  rw [G29_18_formula]
  exact vasyuninBEntry_18_29_eval

def interval_29_18 : NamedVasyuninInterval :=
{
  h := 29
  k := 18
  lower := (29725781/642190000)
  upper := (29854219/642190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_18_interval
}

theorem G29_19_formula : baezDuarteGramEntry 29 19 = vasyuninBEntry 19 29 := by
  rw [baezDuarteGramEntry_symm 29 19]
  exact G19_29_formula

theorem G29_19_interval :
    ((((7351849/161510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 19) ∧
    (baezDuarteGramEntry 29 19 ≤ (((7384151/161510000) : ℚ) : ℝ)) := by
  rw [G29_19_formula]
  exact vasyuninBEntry_19_29_eval

def interval_29_19 : NamedVasyuninInterval :=
{
  h := 29
  k := 19
  lower := (7351849/161510000)
  upper := (7384151/161510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_19_interval
}

theorem G29_20_formula : baezDuarteGramEntry 29 20 = vasyuninBEntry 20 29 := by
  rw [baezDuarteGramEntry_symm 29 20]
  exact G20_29_formula

theorem G29_20_interval :
    ((((5203323/116770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 20) ∧
    (baezDuarteGramEntry 29 20 ≤ (((5226677/116770000) : ℚ) : ℝ)) := by
  rw [G29_20_formula]
  exact vasyuninBEntry_20_29_eval

def interval_29_20 : NamedVasyuninInterval :=
{
  h := 29
  k := 20
  lower := (5203323/116770000)
  upper := (5226677/116770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_20_interval
}

theorem G29_21_formula : baezDuarteGramEntry 29 21 = vasyuninBEntry 21 29 := by
  rw [baezDuarteGramEntry_symm 29 21]
  exact G21_29_formula

theorem G29_21_interval :
    ((((32735151/748490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 21) ∧
    (baezDuarteGramEntry 29 21 ≤ (((32884849/748490000) : ℚ) : ℝ)) := by
  rw [G29_21_formula]
  exact vasyuninBEntry_21_29_eval

def interval_29_21 : NamedVasyuninInterval :=
{
  h := 29
  k := 21
  lower := (32735151/748490000)
  upper := (32884849/748490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_21_interval
}

theorem G29_22_formula : baezDuarteGramEntry 29 22 = vasyuninBEntry 22 29 := by
  rw [baezDuarteGramEntry_symm 29 22]
  exact G22_29_formula

theorem G29_22_interval :
    ((((40506113/938870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 22) ∧
    (baezDuarteGramEntry 29 22 ≤ (((40693887/938870000) : ℚ) : ℝ)) := by
  rw [G29_22_formula]
  exact vasyuninBEntry_22_29_eval

def interval_29_22 : NamedVasyuninInterval :=
{
  h := 29
  k := 22
  lower := (40506113/938870000)
  upper := (40693887/938870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_22_interval
}

theorem G29_23_formula : baezDuarteGramEntry 29 23 = vasyuninBEntry 23 29 := by
  rw [baezDuarteGramEntry_symm 29 23]
  exact G23_29_formula

theorem G29_23_interval :
    ((((25250703/592970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 23) ∧
    (baezDuarteGramEntry 29 23 ≤ (((25369297/592970000) : ℚ) : ℝ)) := by
  rw [G29_23_formula]
  exact vasyuninBEntry_23_29_eval

def interval_29_23 : NamedVasyuninInterval :=
{
  h := 29
  k := 23
  lower := (25250703/592970000)
  upper := (25369297/592970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_23_interval
}

theorem G29_24_formula : baezDuarteGramEntry 29 24 = vasyuninBEntry 24 29 := by
  rw [baezDuarteGramEntry_symm 29 24]
  exact G24_29_formula

theorem G29_24_interval :
    ((((3269247/77530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 24) ∧
    (baezDuarteGramEntry 29 24 ≤ (((3284753/77530000) : ℚ) : ℝ)) := by
  rw [G29_24_formula]
  exact vasyuninBEntry_24_29_eval

def interval_29_24 : NamedVasyuninInterval :=
{
  h := 29
  k := 24
  lower := (3269247/77530000)
  upper := (3284753/77530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_24_interval
}

theorem G29_25_formula : baezDuarteGramEntry 29 25 = vasyuninBEntry 25 29 := by
  rw [baezDuarteGramEntry_symm 29 25]
  exact G25_29_formula

theorem G29_25_interval :
    ((((38398339/916610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 25) ∧
    (baezDuarteGramEntry 29 25 ≤ (((38581661/916610000) : ℚ) : ℝ)) := by
  rw [G29_25_formula]
  exact vasyuninBEntry_25_29_eval

def interval_29_25 : NamedVasyuninInterval :=
{
  h := 29
  k := 25
  lower := (38398339/916610000)
  upper := (38581661/916610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_25_interval
}

theorem G29_26_formula : baezDuarteGramEntry 29 26 = vasyuninBEntry 26 29 := by
  rw [baezDuarteGramEntry_symm 29 26]
  exact G26_29_formula

theorem G29_26_interval :
    ((((37819463/905370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 26) ∧
    (baezDuarteGramEntry 29 26 ≤ (((38000537/905370000) : ℚ) : ℝ)) := by
  rw [G29_26_formula]
  exact vasyuninBEntry_26_29_eval

def interval_29_26 : NamedVasyuninInterval :=
{
  h := 29
  k := 26
  lower := (37819463/905370000)
  upper := (38000537/905370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_26_interval
}

theorem G29_27_formula : baezDuarteGramEntry 29 27 = vasyuninBEntry 27 29 := by
  rw [baezDuarteGramEntry_symm 29 27]
  exact G27_29_formula

theorem G29_27_interval :
    ((((40223891/961090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 27) ∧
    (baezDuarteGramEntry 29 27 ≤ (((40416109/961090000) : ℚ) : ℝ)) := by
  rw [G29_27_formula]
  exact vasyuninBEntry_27_29_eval

def interval_29_27 : NamedVasyuninInterval :=
{
  h := 29
  k := 27
  lower := (40223891/961090000)
  upper := (40416109/961090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_27_interval
}

theorem G29_28_formula : baezDuarteGramEntry 29 28 = vasyuninBEntry 28 29 := by
  rw [baezDuarteGramEntry_symm 29 28]
  exact G28_29_formula

theorem G29_28_interval :
    ((((6881203/162970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 28) ∧
    (baezDuarteGramEntry 29 28 ≤ (((6913797/162970000) : ℚ) : ℝ)) := by
  rw [G29_28_formula]
  exact vasyuninBEntry_28_29_eval

def interval_29_28 : NamedVasyuninInterval :=
{
  h := 29
  k := 28
  lower := (6881203/162970000)
  upper := (6913797/162970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_28_interval
}

theorem G29_29_formula_eq : baezDuarteGramEntry 29 29 = (1 / (29 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 29 := by norm_num
  rw [baez_duarte_diagonal_scaling 29 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G29_29_log_gamma_interval :
  ((((17075629/393710000) : ℚ) : ℝ) ≤ (1 / (29 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (29 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((17154371/393710000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 29 (by norm_num)
  constructor
  · have : ((((17075629/393710000) : ℚ) : ℝ) ≤ (1 / (29 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (29 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((17154371/393710000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G29_29_interval : ((((17075629/393710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 29) ∧ (baezDuarteGramEntry 29 29 ≤ (((17154371/393710000) : ℚ) : ℝ)) := by
  rw [G29_29_formula_eq]
  exact G29_29_log_gamma_interval

def interval_29_29 : NamedVasyuninInterval :=
{
  h := 29
  k := 29
  lower := (17075629/393710000)
  upper := (17154371/393710000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G29_29_interval
}

theorem G29_30_formula : baezDuarteGramEntry 29 30 = vasyuninBEntry 29 30 := vasyuninBEntry_correct_axiom 29 30 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_30_eval :
    ((((14474551/354490000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 30) ∧
    (vasyuninBEntry 29 30 ≤ (((14545449/354490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2930_formula_bound
  constructor <;> linarith

theorem G29_30_interval :
    ((((14474551/354490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 30) ∧
    (baezDuarteGramEntry 29 30 ≤ (((14545449/354490000) : ℚ) : ℝ)) := by
  rw [G29_30_formula]
  exact vasyuninBEntry_29_30_eval

def interval_29_30 : NamedVasyuninInterval :=
{
  h := 29
  k := 30
  lower := (14474551/354490000)
  upper := (14545449/354490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_30_interval
}

theorem G29_31_formula : baezDuarteGramEntry 29 31 = vasyuninBEntry 29 31 := vasyuninBEntry_correct_axiom 29 31 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_31_eval :
    ((((35140293/897070000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 31) ∧
    (vasyuninBEntry 29 31 ≤ (((35319707/897070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2931_formula_bound
  constructor <;> linarith

theorem G29_31_interval :
    ((((35140293/897070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 31) ∧
    (baezDuarteGramEntry 29 31 ≤ (((35319707/897070000) : ℚ) : ℝ)) := by
  rw [G29_31_formula]
  exact vasyuninBEntry_29_31_eval

def interval_29_31 : NamedVasyuninInterval :=
{
  h := 29
  k := 31
  lower := (35140293/897070000)
  upper := (35319707/897070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_31_interval
}

theorem G29_32_formula : baezDuarteGramEntry 29 32 = vasyuninBEntry 29 32 := vasyuninBEntry_correct_axiom 29 32 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_32_eval :
    ((((1323503/34970000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 32) ∧
    (vasyuninBEntry 29 32 ≤ (((1330497/34970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2932_formula_bound
  constructor <;> linarith

theorem G29_32_interval :
    ((((1323503/34970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 32) ∧
    (baezDuarteGramEntry 29 32 ≤ (((1330497/34970000) : ℚ) : ℝ)) := by
  rw [G29_32_formula]
  exact vasyuninBEntry_29_32_eval

def interval_29_32 : NamedVasyuninInterval :=
{
  h := 29
  k := 32
  lower := (1323503/34970000)
  upper := (1330497/34970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_32_interval
}

theorem G29_33_formula : baezDuarteGramEntry 29 33 = vasyuninBEntry 29 33 := vasyuninBEntry_correct_axiom 29 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_33_eval :
    ((((33758097/919030000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 33) ∧
    (vasyuninBEntry 29 33 ≤ (((33941903/919030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2933_formula_bound
  constructor <;> linarith

theorem G29_33_interval :
    ((((33758097/919030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 33) ∧
    (baezDuarteGramEntry 29 33 ≤ (((33941903/919030000) : ℚ) : ℝ)) := by
  rw [G29_33_formula]
  exact vasyuninBEntry_29_33_eval

def interval_29_33 : NamedVasyuninInterval :=
{
  h := 29
  k := 33
  lower := (33758097/919030000)
  upper := (33941903/919030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_33_interval
}

theorem G29_34_formula : baezDuarteGramEntry 29 34 = vasyuninBEntry 29 34 := vasyuninBEntry_correct_axiom 29 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_34_eval :
    ((((33945093/949070000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 34) ∧
    (vasyuninBEntry 29 34 ≤ (((34134907/949070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2934_formula_bound
  constructor <;> linarith

theorem G29_34_interval :
    ((((33945093/949070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 34) ∧
    (baezDuarteGramEntry 29 34 ≤ (((34134907/949070000) : ℚ) : ℝ)) := by
  rw [G29_34_formula]
  exact vasyuninBEntry_29_34_eval

def interval_29_34 : NamedVasyuninInterval :=
{
  h := 29
  k := 34
  lower := (33945093/949070000)
  upper := (34134907/949070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_34_interval
}

theorem G29_35_formula : baezDuarteGramEntry 29 35 = vasyuninBEntry 29 35 := vasyuninBEntry_correct_axiom 29 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_35_eval :
    ((((12259887/351130000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 35) ∧
    (vasyuninBEntry 29 35 ≤ (((12330113/351130000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2935_formula_bound
  constructor <;> linarith

theorem G29_35_interval :
    ((((12259887/351130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 35) ∧
    (baezDuarteGramEntry 29 35 ≤ (((12330113/351130000) : ℚ) : ℝ)) := by
  rw [G29_35_formula]
  exact vasyuninBEntry_29_35_eval

def interval_29_35 : NamedVasyuninInterval :=
{
  h := 29
  k := 35
  lower := (12259887/351130000)
  upper := (12330113/351130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_35_interval
}

theorem G29_36_formula : baezDuarteGramEntry 29 36 = vasyuninBEntry 29 36 := vasyuninBEntry_correct_axiom 29 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_36_eval :
    ((((6385307/186930000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 36) ∧
    (vasyuninBEntry 29 36 ≤ (((6422693/186930000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2936_formula_bound
  constructor <;> linarith

theorem G29_36_interval :
    ((((6385307/186930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 36) ∧
    (baezDuarteGramEntry 29 36 ≤ (((6422693/186930000) : ℚ) : ℝ)) := by
  rw [G29_36_formula]
  exact vasyuninBEntry_29_36_eval

def interval_29_36 : NamedVasyuninInterval :=
{
  h := 29
  k := 36
  lower := (6385307/186930000)
  upper := (6422693/186930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_36_interval
}

theorem G29_37_formula : baezDuarteGramEntry 29 37 = vasyuninBEntry 29 37 := vasyuninBEntry_correct_axiom 29 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_37_eval :
    ((((33160849/991510000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 37) ∧
    (vasyuninBEntry 29 37 ≤ (((33359151/991510000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2937_formula_bound
  constructor <;> linarith

theorem G29_37_interval :
    ((((33160849/991510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 37) ∧
    (baezDuarteGramEntry 29 37 ≤ (((33359151/991510000) : ℚ) : ℝ)) := by
  rw [G29_37_formula]
  exact vasyuninBEntry_29_37_eval

def interval_29_37 : NamedVasyuninInterval :=
{
  h := 29
  k := 37
  lower := (33160849/991510000)
  upper := (33359151/991510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_37_interval
}

theorem G29_38_formula : baezDuarteGramEntry 29 38 = vasyuninBEntry 29 38 := vasyuninBEntry_correct_axiom 29 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_38_eval :
    ((((30008583/914170000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 38) ∧
    (vasyuninBEntry 29 38 ≤ (((30191417/914170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2938_formula_bound
  constructor <;> linarith

theorem G29_38_interval :
    ((((30008583/914170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 38) ∧
    (baezDuarteGramEntry 29 38 ≤ (((30191417/914170000) : ℚ) : ℝ)) := by
  rw [G29_38_formula]
  exact vasyuninBEntry_29_38_eval

def interval_29_38 : NamedVasyuninInterval :=
{
  h := 29
  k := 38
  lower := (30008583/914170000)
  upper := (30191417/914170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_38_interval
}

theorem G29_39_formula : baezDuarteGramEntry 29 39 = vasyuninBEntry 29 39 := vasyuninBEntry_correct_axiom 29 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_39_eval :
    ((((20825453/645470000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 39) ∧
    (vasyuninBEntry 29 39 ≤ (((20954547/645470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2939_formula_bound
  constructor <;> linarith

theorem G29_39_interval :
    ((((20825453/645470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 39) ∧
    (baezDuarteGramEntry 29 39 ≤ (((20954547/645470000) : ℚ) : ℝ)) := by
  rw [G29_39_formula]
  exact vasyuninBEntry_29_39_eval

def interval_29_39 : NamedVasyuninInterval :=
{
  h := 29
  k := 39
  lower := (20825453/645470000)
  upper := (20954547/645470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_39_interval
}

theorem G29_40_formula : baezDuarteGramEntry 29 40 = vasyuninBEntry 29 40 := vasyuninBEntry_correct_axiom 29 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_40_eval :
    ((((28669469/905310000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 40) ∧
    (vasyuninBEntry 29 40 ≤ (((28850531/905310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2940_formula_bound
  constructor <;> linarith

theorem G29_40_interval :
    ((((28669469/905310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 40) ∧
    (baezDuarteGramEntry 29 40 ≤ (((28850531/905310000) : ℚ) : ℝ)) := by
  rw [G29_40_formula]
  exact vasyuninBEntry_29_40_eval

def interval_29_40 : NamedVasyuninInterval :=
{
  h := 29
  k := 40
  lower := (28669469/905310000)
  upper := (28850531/905310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_40_interval
}

theorem G29_41_formula : baezDuarteGramEntry 29 41 = vasyuninBEntry 29 41 := vasyuninBEntry_correct_axiom 29 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_41_eval :
    ((((27980213/897870000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 41) ∧
    (vasyuninBEntry 29 41 ≤ (((28159787/897870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2941_formula_bound
  constructor <;> linarith

theorem G29_41_interval :
    ((((27980213/897870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 41) ∧
    (baezDuarteGramEntry 29 41 ≤ (((28159787/897870000) : ℚ) : ℝ)) := by
  rw [G29_41_formula]
  exact vasyuninBEntry_29_41_eval

def interval_29_41 : NamedVasyuninInterval :=
{
  h := 29
  k := 41
  lower := (27980213/897870000)
  upper := (28159787/897870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_41_interval
}

theorem G29_42_formula : baezDuarteGramEntry 29 42 = vasyuninBEntry 29 42 := vasyuninBEntry_correct_axiom 29 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_42_eval :
    ((((1621721/52790000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 42) ∧
    (vasyuninBEntry 29 42 ≤ (((1632279/52790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2942_formula_bound
  constructor <;> linarith

theorem G29_42_interval :
    ((((1621721/52790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 42) ∧
    (baezDuarteGramEntry 29 42 ≤ (((1632279/52790000) : ℚ) : ℝ)) := by
  rw [G29_42_formula]
  exact vasyuninBEntry_29_42_eval

def interval_29_42 : NamedVasyuninInterval :=
{
  h := 29
  k := 42
  lower := (1621721/52790000)
  upper := (1632279/52790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_42_interval
}

theorem G29_43_formula : baezDuarteGramEntry 29 43 = vasyuninBEntry 29 43 := vasyuninBEntry_correct_axiom 29 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_43_eval :
    ((((5344907/175930000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 43) ∧
    (vasyuninBEntry 29 43 ≤ (((5380093/175930000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2943_formula_bound
  constructor <;> linarith

theorem G29_43_interval :
    ((((5344907/175930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 43) ∧
    (baezDuarteGramEntry 29 43 ≤ (((5380093/175930000) : ℚ) : ℝ)) := by
  rw [G29_43_formula]
  exact vasyuninBEntry_29_43_eval

def interval_29_43 : NamedVasyuninInterval :=
{
  h := 29
  k := 43
  lower := (5344907/175930000)
  upper := (5380093/175930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_43_interval
}

theorem G29_44_formula : baezDuarteGramEntry 29 44 = vasyuninBEntry 29 44 := vasyuninBEntry_correct_axiom 29 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_44_eval :
    ((((4195987/140130000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 44) ∧
    (vasyuninBEntry 29 44 ≤ (((4224013/140130000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2944_formula_bound
  constructor <;> linarith

theorem G29_44_interval :
    ((((4195987/140130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 44) ∧
    (baezDuarteGramEntry 29 44 ≤ (((4224013/140130000) : ℚ) : ℝ)) := by
  rw [G29_44_formula]
  exact vasyuninBEntry_29_44_eval

def interval_29_44 : NamedVasyuninInterval :=
{
  h := 29
  k := 44
  lower := (4195987/140130000)
  upper := (4224013/140130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_44_interval
}

theorem G29_45_formula : baezDuarteGramEntry 29 45 = vasyuninBEntry 29 45 := vasyuninBEntry_correct_axiom 29 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_45_eval :
    ((((9517639/323610000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 45) ∧
    (vasyuninBEntry 29 45 ≤ (((9582361/323610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2945_formula_bound
  constructor <;> linarith

theorem G29_45_interval :
    ((((9517639/323610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 45) ∧
    (baezDuarteGramEntry 29 45 ≤ (((9582361/323610000) : ℚ) : ℝ)) := by
  rw [G29_45_formula]
  exact vasyuninBEntry_29_45_eval

def interval_29_45 : NamedVasyuninInterval :=
{
  h := 29
  k := 45
  lower := (9517639/323610000)
  upper := (9582361/323610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_45_interval
}

theorem G29_46_formula : baezDuarteGramEntry 29 46 = vasyuninBEntry 29 46 := vasyuninBEntry_correct_axiom 29 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_46_eval :
    ((((4279231/147690000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 46) ∧
    (vasyuninBEntry 29 46 ≤ (((4308769/147690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2946_formula_bound
  constructor <;> linarith

theorem G29_46_interval :
    ((((4279231/147690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 46) ∧
    (baezDuarteGramEntry 29 46 ≤ (((4308769/147690000) : ℚ) : ℝ)) := by
  rw [G29_46_formula]
  exact vasyuninBEntry_29_46_eval

def interval_29_46 : NamedVasyuninInterval :=
{
  h := 29
  k := 46
  lower := (4279231/147690000)
  upper := (4308769/147690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_46_interval
}

theorem G29_47_formula : baezDuarteGramEntry 29 47 = vasyuninBEntry 29 47 := vasyuninBEntry_correct_axiom 29 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_47_eval :
    ((((1118089/39110000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 47) ∧
    (vasyuninBEntry 29 47 ≤ (((1125911/39110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2947_formula_bound
  constructor <;> linarith

theorem G29_47_interval :
    ((((1118089/39110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 47) ∧
    (baezDuarteGramEntry 29 47 ≤ (((1125911/39110000) : ℚ) : ℝ)) := by
  rw [G29_47_formula]
  exact vasyuninBEntry_29_47_eval

def interval_29_47 : NamedVasyuninInterval :=
{
  h := 29
  k := 47
  lower := (1118089/39110000)
  upper := (1125911/39110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_47_interval
}

theorem G29_48_formula : baezDuarteGramEntry 29 48 = vasyuninBEntry 29 48 := vasyuninBEntry_correct_axiom 29 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_48_eval :
    ((((10796799/382010000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 48) ∧
    (vasyuninBEntry 29 48 ≤ (((10873201/382010000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2948_formula_bound
  constructor <;> linarith

theorem G29_48_interval :
    ((((10796799/382010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 48) ∧
    (baezDuarteGramEntry 29 48 ≤ (((10873201/382010000) : ℚ) : ℝ)) := by
  rw [G29_48_formula]
  exact vasyuninBEntry_29_48_eval

def interval_29_48 : NamedVasyuninInterval :=
{
  h := 29
  k := 48
  lower := (10796799/382010000)
  upper := (10873201/382010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_48_interval
}

theorem G29_49_formula : baezDuarteGramEntry 29 49 = vasyuninBEntry 29 49 := vasyuninBEntry_correct_axiom 29 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_49_eval :
    ((((23535683/843170000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 49) ∧
    (vasyuninBEntry 29 49 ≤ (((23704317/843170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2949_formula_bound
  constructor <;> linarith

theorem G29_49_interval :
    ((((23535683/843170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 49) ∧
    (baezDuarteGramEntry 29 49 ≤ (((23704317/843170000) : ℚ) : ℝ)) := by
  rw [G29_49_formula]
  exact vasyuninBEntry_29_49_eval

def interval_29_49 : NamedVasyuninInterval :=
{
  h := 29
  k := 49
  lower := (23535683/843170000)
  upper := (23704317/843170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_49_interval
}

theorem G29_50_formula : baezDuarteGramEntry 29 50 = vasyuninBEntry 29 50 := vasyuninBEntry_correct_axiom 29 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_29_50_eval :
    ((((4379129/158710000) : ℚ) : ℝ) ≤ vasyuninBEntry 29 50) ∧
    (vasyuninBEntry 29 50 ≤ (((4410871/158710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2950_formula_bound
  constructor <;> linarith

theorem G29_50_interval :
    ((((4379129/158710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 29 50) ∧
    (baezDuarteGramEntry 29 50 ≤ (((4410871/158710000) : ℚ) : ℝ)) := by
  rw [G29_50_formula]
  exact vasyuninBEntry_29_50_eval

def interval_29_50 : NamedVasyuninInterval :=
{
  h := 29
  k := 50
  lower := (4379129/158710000)
  upper := (4410871/158710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G29_50_interval
}

theorem G30_1_formula : baezDuarteGramEntry 30 1 = vasyuninBEntry 1 30 := by
  rw [baezDuarteGramEntry_symm 30 1]
  exact G1_30_formula

theorem G30_1_interval :
    ((((42375119/448810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 1) ∧
    (baezDuarteGramEntry 30 1 ≤ (((42464881/448810000) : ℚ) : ℝ)) := by
  rw [G30_1_formula]
  exact vasyuninBEntry_1_30_eval

def interval_30_1 : NamedVasyuninInterval :=
{
  h := 30
  k := 1
  lower := (42375119/448810000)
  upper := (42464881/448810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_1_interval
}

theorem G30_2_formula : baezDuarteGramEntry 30 2 = vasyuninBEntry 2 30 := by
  rw [baezDuarteGramEntry_symm 30 2]
  exact G2_30_formula

theorem G30_2_interval :
    ((((13074251/157490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 2) ∧
    (baezDuarteGramEntry 30 2 ≤ (((13105749/157490000) : ℚ) : ℝ)) := by
  rw [G30_2_formula]
  exact vasyuninBEntry_2_30_eval

def interval_30_2 : NamedVasyuninInterval :=
{
  h := 30
  k := 2
  lower := (13074251/157490000)
  upper := (13105749/157490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_2_interval
}

theorem G30_3_formula : baezDuarteGramEntry 30 3 = vasyuninBEntry 3 30 := by
  rw [baezDuarteGramEntry_symm 30 3]
  exact G3_30_formula

theorem G30_3_interval :
    ((((5373967/70330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 3) ∧
    (baezDuarteGramEntry 30 3 ≤ (((5388033/70330000) : ℚ) : ℝ)) := by
  rw [G30_3_formula]
  exact vasyuninBEntry_3_30_eval

def interval_30_3 : NamedVasyuninInterval :=
{
  h := 30
  k := 3
  lower := (5373967/70330000)
  upper := (5388033/70330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_3_interval
}

theorem G30_4_formula : baezDuarteGramEntry 30 4 = vasyuninBEntry 4 30 := by
  rw [baezDuarteGramEntry_symm 30 4]
  exact G4_30_formula

theorem G30_4_interval :
    ((((4200341/59090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 4) ∧
    (baezDuarteGramEntry 30 4 ≤ (((4212159/59090000) : ℚ) : ℝ)) := by
  rw [G30_4_formula]
  exact vasyuninBEntry_4_30_eval

def interval_30_4 : NamedVasyuninInterval :=
{
  h := 30
  k := 4
  lower := (4200341/59090000)
  upper := (4212159/59090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_4_interval
}

theorem G30_5_formula : baezDuarteGramEntry 30 5 = vasyuninBEntry 5 30 := by
  rw [baezDuarteGramEntry_symm 30 5]
  exact G5_30_formula

theorem G30_5_interval :
    ((((5680421/83290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 5) ∧
    (baezDuarteGramEntry 30 5 ≤ (((5697079/83290000) : ℚ) : ℝ)) := by
  rw [G30_5_formula]
  exact vasyuninBEntry_5_30_eval

def interval_30_5 : NamedVasyuninInterval :=
{
  h := 30
  k := 5
  lower := (5680421/83290000)
  upper := (5697079/83290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_5_interval
}

theorem G30_6_formula : baezDuarteGramEntry 30 6 = vasyuninBEntry 6 30 := by
  rw [baezDuarteGramEntry_symm 30 6]
  exact G6_30_formula

theorem G30_6_interval :
    ((((21397239/327610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 6) ∧
    (baezDuarteGramEntry 30 6 ≤ (((21462761/327610000) : ℚ) : ℝ)) := by
  rw [G30_6_formula]
  exact vasyuninBEntry_6_30_eval

def interval_30_6 : NamedVasyuninInterval :=
{
  h := 30
  k := 6
  lower := (21397239/327610000)
  upper := (21462761/327610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_6_interval
}

theorem G30_7_formula : baezDuarteGramEntry 30 7 = vasyuninBEntry 7 30 := by
  rw [baezDuarteGramEntry_symm 30 7]
  exact G7_30_formula

theorem G30_7_interval :
    ((((10882351/176490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 7) ∧
    (baezDuarteGramEntry 30 7 ≤ (((10917649/176490000) : ℚ) : ℝ)) := by
  rw [G30_7_formula]
  exact vasyuninBEntry_7_30_eval

def interval_30_7 : NamedVasyuninInterval :=
{
  h := 30
  k := 7
  lower := (10882351/176490000)
  upper := (10917649/176490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_7_interval
}

theorem G30_8_formula : baezDuarteGramEntry 30 8 = vasyuninBEntry 8 30 := by
  rw [baezDuarteGramEntry_symm 30 8]
  exact G8_30_formula

theorem G30_8_interval :
    ((((36179113/608870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 8) ∧
    (baezDuarteGramEntry 30 8 ≤ (((36300887/608870000) : ℚ) : ℝ)) := by
  rw [G30_8_formula]
  exact vasyuninBEntry_8_30_eval

def interval_30_8 : NamedVasyuninInterval :=
{
  h := 30
  k := 8
  lower := (36179113/608870000)
  upper := (36300887/608870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_8_interval
}

theorem G30_9_formula : baezDuarteGramEntry 30 9 = vasyuninBEntry 9 30 := by
  rw [baezDuarteGramEntry_symm 30 9]
  exact G9_30_formula

theorem G30_9_interval :
    ((((7291303/126970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 9) ∧
    (baezDuarteGramEntry 30 9 ≤ (((7316697/126970000) : ℚ) : ℝ)) := by
  rw [G30_9_formula]
  exact vasyuninBEntry_9_30_eval

def interval_30_9 : NamedVasyuninInterval :=
{
  h := 30
  k := 9
  lower := (7291303/126970000)
  upper := (7316697/126970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_9_interval
}

theorem G30_10_formula : baezDuarteGramEntry 30 10 = vasyuninBEntry 10 30 := by
  rw [baezDuarteGramEntry_symm 30 10]
  exact G10_30_formula

theorem G30_10_interval :
    ((((53766331/936690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 10) ∧
    (baezDuarteGramEntry 30 10 ≤ (((53953669/936690000) : ℚ) : ℝ)) := by
  rw [G30_10_formula]
  exact vasyuninBEntry_10_30_eval

def interval_30_10 : NamedVasyuninInterval :=
{
  h := 30
  k := 10
  lower := (53766331/936690000)
  upper := (53953669/936690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_10_interval
}

theorem G30_11_formula : baezDuarteGramEntry 30 11 = vasyuninBEntry 11 30 := by
  rw [baezDuarteGramEntry_symm 30 11]
  exact G11_30_formula

theorem G30_11_interval :
    ((((19384071/359290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 11) ∧
    (baezDuarteGramEntry 30 11 ≤ (((19455929/359290000) : ℚ) : ℝ)) := by
  rw [G30_11_formula]
  exact vasyuninBEntry_11_30_eval

def interval_30_11 : NamedVasyuninInterval :=
{
  h := 30
  k := 11
  lower := (19384071/359290000)
  upper := (19455929/359290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_11_interval
}

theorem G30_12_formula : baezDuarteGramEntry 30 12 = vasyuninBEntry 12 30 := by
  rw [baezDuarteGramEntry_symm 30 12]
  exact G12_30_formula

theorem G30_12_interval :
    ((((6073461/115390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 12) ∧
    (baezDuarteGramEntry 30 12 ≤ (((6096539/115390000) : ℚ) : ℝ)) := by
  rw [G30_12_formula]
  exact vasyuninBEntry_12_30_eval

def interval_30_12 : NamedVasyuninInterval :=
{
  h := 30
  k := 12
  lower := (6073461/115390000)
  upper := (6096539/115390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_12_interval
}

theorem G30_13_formula : baezDuarteGramEntry 30 13 = vasyuninBEntry 13 30 := by
  rw [baezDuarteGramEntry_symm 30 13]
  exact G13_30_formula

theorem G30_13_interval :
    ((((297419/5810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 13) ∧
    (baezDuarteGramEntry 30 13 ≤ (((298581/5810000) : ℚ) : ℝ)) := by
  rw [G30_13_formula]
  exact vasyuninBEntry_13_30_eval

def interval_30_13 : NamedVasyuninInterval :=
{
  h := 30
  k := 13
  lower := (297419/5810000)
  upper := (298581/5810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_13_interval
}

theorem G30_14_formula : baezDuarteGramEntry 30 14 = vasyuninBEntry 14 30 := by
  rw [baezDuarteGramEntry_symm 30 14]
  exact G14_30_formula

theorem G30_14_interval :
    ((((14451421/285790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 14) ∧
    (baezDuarteGramEntry 30 14 ≤ (((14508579/285790000) : ℚ) : ℝ)) := by
  rw [G30_14_formula]
  exact vasyuninBEntry_14_30_eval

def interval_30_14 : NamedVasyuninInterval :=
{
  h := 30
  k := 14
  lower := (14451421/285790000)
  upper := (14508579/285790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_14_interval
}

theorem G30_15_formula : baezDuarteGramEntry 30 15 = vasyuninBEntry 15 30 := by
  rw [baezDuarteGramEntry_symm 30 15]
  exact G15_30_formula

theorem G30_15_interval :
    ((((16952007/329930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 15) ∧
    (baezDuarteGramEntry 30 15 ≤ (((17017993/329930000) : ℚ) : ℝ)) := by
  rw [G30_15_formula]
  exact vasyuninBEntry_15_30_eval

def interval_30_15 : NamedVasyuninInterval :=
{
  h := 30
  k := 15
  lower := (16952007/329930000)
  upper := (17017993/329930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_15_interval
}

theorem G30_16_formula : baezDuarteGramEntry 30 16 = vasyuninBEntry 16 30 := by
  rw [baezDuarteGramEntry_symm 30 16]
  exact G16_30_formula

theorem G30_16_interval :
    ((((26305471/545290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 16) ∧
    (baezDuarteGramEntry 30 16 ≤ (((26414529/545290000) : ℚ) : ℝ)) := by
  rw [G30_16_formula]
  exact vasyuninBEntry_16_30_eval

def interval_30_16 : NamedVasyuninInterval :=
{
  h := 30
  k := 16
  lower := (26305471/545290000)
  upper := (26414529/545290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_16_interval
}

theorem G30_17_formula : baezDuarteGramEntry 30 17 = vasyuninBEntry 17 30 := by
  rw [baezDuarteGramEntry_symm 30 17]
  exact G17_30_formula

theorem G30_17_interval :
    ((((25285717/542830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 17) ∧
    (baezDuarteGramEntry 30 17 ≤ (((25394283/542830000) : ℚ) : ℝ)) := by
  rw [G30_17_formula]
  exact vasyuninBEntry_17_30_eval

def interval_30_17 : NamedVasyuninInterval :=
{
  h := 30
  k := 17
  lower := (25285717/542830000)
  upper := (25394283/542830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_17_interval
}

theorem G30_18_formula : baezDuarteGramEntry 30 18 = vasyuninBEntry 18 30 := by
  rw [baezDuarteGramEntry_symm 30 18]
  exact G18_30_formula

theorem G30_18_interval :
    ((((40251521/884790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 18) ∧
    (baezDuarteGramEntry 30 18 ≤ (((40428479/884790000) : ℚ) : ℝ)) := by
  rw [G30_18_formula]
  exact vasyuninBEntry_18_30_eval

def interval_30_18 : NamedVasyuninInterval :=
{
  h := 30
  k := 18
  lower := (40251521/884790000)
  upper := (40428479/884790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_18_interval
}

theorem G30_19_formula : baezDuarteGramEntry 30 19 = vasyuninBEntry 19 30 := by
  rw [baezDuarteGramEntry_symm 30 19]
  exact G19_30_formula

theorem G30_19_interval :
    ((((9328993/210070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 19) ∧
    (baezDuarteGramEntry 30 19 ≤ (((9371007/210070000) : ℚ) : ℝ)) := by
  rw [G30_19_formula]
  exact vasyuninBEntry_19_30_eval

def interval_30_19 : NamedVasyuninInterval :=
{
  h := 30
  k := 19
  lower := (9328993/210070000)
  upper := (9371007/210070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_19_interval
}

theorem G30_20_formula : baezDuarteGramEntry 30 20 = vasyuninBEntry 20 30 := by
  rw [baezDuarteGramEntry_symm 30 20]
  exact G20_30_formula

theorem G30_20_interval :
    ((((38143331/866690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 20) ∧
    (baezDuarteGramEntry 30 20 ≤ (((38316669/866690000) : ℚ) : ℝ)) := by
  rw [G30_20_formula]
  exact vasyuninBEntry_20_30_eval

def interval_30_20 : NamedVasyuninInterval :=
{
  h := 30
  k := 20
  lower := (38143331/866690000)
  upper := (38316669/866690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_20_interval
}

theorem G30_21_formula : baezDuarteGramEntry 30 21 = vasyuninBEntry 21 30 := by
  rw [baezDuarteGramEntry_symm 30 21]
  exact G21_30_formula

theorem G30_21_interval :
    ((((531259/12410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 21) ∧
    (baezDuarteGramEntry 30 21 ≤ (((533741/12410000) : ℚ) : ℝ)) := by
  rw [G30_21_formula]
  exact vasyuninBEntry_21_30_eval

def interval_30_21 : NamedVasyuninInterval :=
{
  h := 30
  k := 21
  lower := (531259/12410000)
  upper := (533741/12410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_21_interval
}

theorem G30_22_formula : baezDuarteGramEntry 30 22 = vasyuninBEntry 22 30 := by
  rw [baezDuarteGramEntry_symm 30 22]
  exact G22_30_formula

theorem G30_22_interval :
    ((((260257/6180000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 22) ∧
    (baezDuarteGramEntry 30 22 ≤ (((261493/6180000) : ℚ) : ℝ)) := by
  rw [G30_22_formula]
  exact vasyuninBEntry_22_30_eval

def interval_30_22 : NamedVasyuninInterval :=
{
  h := 30
  k := 22
  lower := (260257/6180000)
  upper := (261493/6180000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_22_interval
}

theorem G30_23_formula : baezDuarteGramEntry 30 23 = vasyuninBEntry 23 30 := by
  rw [baezDuarteGramEntry_symm 30 23]
  exact G23_30_formula

theorem G30_23_interval :
    ((((40143363/966370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 23) ∧
    (baezDuarteGramEntry 30 23 ≤ (((40336637/966370000) : ℚ) : ℝ)) := by
  rw [G30_23_formula]
  exact vasyuninBEntry_23_30_eval

def interval_30_23 : NamedVasyuninInterval :=
{
  h := 30
  k := 23
  lower := (40143363/966370000)
  upper := (40336637/966370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_23_interval
}

theorem G30_24_formula : baezDuarteGramEntry 30 24 = vasyuninBEntry 24 30 := by
  rw [baezDuarteGramEntry_symm 30 24]
  exact G24_30_formula

theorem G30_24_interval :
    ((((19552461/475390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 24) ∧
    (baezDuarteGramEntry 30 24 ≤ (((19647539/475390000) : ℚ) : ℝ)) := by
  rw [G30_24_formula]
  exact vasyuninBEntry_24_30_eval

def interval_30_24 : NamedVasyuninInterval :=
{
  h := 30
  k := 24
  lower := (19552461/475390000)
  upper := (19647539/475390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_24_interval
}

theorem G30_25_formula : baezDuarteGramEntry 30 25 = vasyuninBEntry 25 30 := by
  rw [baezDuarteGramEntry_symm 30 25]
  exact G25_30_formula

theorem G30_25_interval :
    ((((6982859/171410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 25) ∧
    (baezDuarteGramEntry 30 25 ≤ (((7017141/171410000) : ℚ) : ℝ)) := by
  rw [G30_25_formula]
  exact vasyuninBEntry_25_30_eval

def interval_30_25 : NamedVasyuninInterval :=
{
  h := 30
  k := 25
  lower := (6982859/171410000)
  upper := (7017141/171410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_25_interval
}

theorem G30_26_formula : baezDuarteGramEntry 30 26 = vasyuninBEntry 26 30 := by
  rw [baezDuarteGramEntry_symm 30 26]
  exact G26_30_formula

theorem G30_26_interval :
    ((((19945711/492890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 26) ∧
    (baezDuarteGramEntry 30 26 ≤ (((20044289/492890000) : ℚ) : ℝ)) := by
  rw [G30_26_formula]
  exact vasyuninBEntry_26_30_eval

def interval_30_26 : NamedVasyuninInterval :=
{
  h := 30
  k := 26
  lower := (19945711/492890000)
  upper := (20044289/492890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_26_interval
}

theorem G30_27_formula : baezDuarteGramEntry 30 27 = vasyuninBEntry 27 30 := by
  rw [baezDuarteGramEntry_symm 30 27]
  exact G27_30_formula

theorem G30_27_interval :
    ((((29546831/731690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 27) ∧
    (baezDuarteGramEntry 30 27 ≤ (((29693169/731690000) : ℚ) : ℝ)) := by
  rw [G30_27_formula]
  exact vasyuninBEntry_27_30_eval

def interval_30_27 : NamedVasyuninInterval :=
{
  h := 30
  k := 27
  lower := (29546831/731690000)
  upper := (29693169/731690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_27_interval
}

theorem G30_28_formula : baezDuarteGramEntry 30 28 = vasyuninBEntry 28 30 := by
  rw [baezDuarteGramEntry_symm 30 28]
  exact G28_30_formula

theorem G30_28_interval :
    ((((24539363/606370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 28) ∧
    (baezDuarteGramEntry 30 28 ≤ (((24660637/606370000) : ℚ) : ℝ)) := by
  rw [G30_28_formula]
  exact vasyuninBEntry_28_30_eval

def interval_30_28 : NamedVasyuninInterval :=
{
  h := 30
  k := 28
  lower := (24539363/606370000)
  upper := (24660637/606370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_28_interval
}

theorem G30_29_formula : baezDuarteGramEntry 30 29 = vasyuninBEntry 29 30 := by
  rw [baezDuarteGramEntry_symm 30 29]
  exact G29_30_formula

theorem G30_29_interval :
    ((((14474551/354490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 29) ∧
    (baezDuarteGramEntry 30 29 ≤ (((14545449/354490000) : ℚ) : ℝ)) := by
  rw [G30_29_formula]
  exact vasyuninBEntry_29_30_eval

def interval_30_29 : NamedVasyuninInterval :=
{
  h := 30
  k := 29
  lower := (14474551/354490000)
  upper := (14545449/354490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_29_interval
}

theorem G30_30_formula_eq : baezDuarteGramEntry 30 30 = (1 / (30 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 30 := by norm_num
  rw [baez_duarte_diagonal_scaling 30 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G30_30_log_gamma_interval :
  ((((39665383/946170000) : ℚ) : ℝ) ≤ (1 / (30 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (30 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((39854617/946170000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 30 (by norm_num)
  constructor
  · have : ((((39665383/946170000) : ℚ) : ℝ) ≤ (1 / (30 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (30 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((39854617/946170000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G30_30_interval : ((((39665383/946170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 30) ∧ (baezDuarteGramEntry 30 30 ≤ (((39854617/946170000) : ℚ) : ℝ)) := by
  rw [G30_30_formula_eq]
  exact G30_30_log_gamma_interval

def interval_30_30 : NamedVasyuninInterval :=
{
  h := 30
  k := 30
  lower := (39665383/946170000)
  upper := (39854617/946170000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G30_30_interval
}

theorem G30_31_formula : baezDuarteGramEntry 30 31 = vasyuninBEntry 30 31 := vasyuninBEntry_correct_axiom 30 31 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_31_eval :
    ((((3872703/97970000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 31) ∧
    (vasyuninBEntry 30 31 ≤ (((3892297/97970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3031_formula_bound
  constructor <;> linarith

theorem G30_31_interval :
    ((((3872703/97970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 31) ∧
    (baezDuarteGramEntry 30 31 ≤ (((3892297/97970000) : ℚ) : ℝ)) := by
  rw [G30_31_formula]
  exact vasyuninBEntry_30_31_eval

def interval_30_31 : NamedVasyuninInterval :=
{
  h := 30
  k := 31
  lower := (3872703/97970000)
  upper := (3892297/97970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_31_interval
}

theorem G30_32_formula : baezDuarteGramEntry 30 32 = vasyuninBEntry 30 32 := vasyuninBEntry_correct_axiom 30 32 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_32_eval :
    ((((3841879/101210000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 32) ∧
    (vasyuninBEntry 30 32 ≤ (((3862121/101210000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_15_16_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 15 16 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G30_32_interval :
    ((((3841879/101210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 32) ∧
    (baezDuarteGramEntry 30 32 ≤ (((3862121/101210000) : ℚ) : ℝ)) := by
  rw [G30_32_formula]
  exact vasyuninBEntry_30_32_eval

def interval_30_32 : NamedVasyuninInterval :=
{
  h := 30
  k := 32
  lower := (3841879/101210000)
  upper := (3862121/101210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_32_interval
}

theorem G30_33_formula : baezDuarteGramEntry 30 33 = vasyuninBEntry 30 33 := vasyuninBEntry_correct_axiom 30 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_33_eval :
    ((((32920309/896910000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 33) ∧
    (vasyuninBEntry 30 33 ≤ (((33099691/896910000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_10_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 10 11 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G30_33_interval :
    ((((32920309/896910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 33) ∧
    (baezDuarteGramEntry 30 33 ≤ (((33099691/896910000) : ℚ) : ℝ)) := by
  rw [G30_33_formula]
  exact vasyuninBEntry_30_33_eval

def interval_30_33 : NamedVasyuninInterval :=
{
  h := 30
  k := 33
  lower := (32920309/896910000)
  upper := (33099691/896910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_33_interval
}

theorem G30_34_formula : baezDuarteGramEntry 30 34 = vasyuninBEntry 30 34 := vasyuninBEntry_correct_axiom 30 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_34_eval :
    ((((27572633/773670000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 34) ∧
    (vasyuninBEntry 30 34 ≤ (((27727367/773670000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_15_17_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 15 17 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G30_34_interval :
    ((((27572633/773670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 34) ∧
    (baezDuarteGramEntry 30 34 ≤ (((27727367/773670000) : ℚ) : ℝ)) := by
  rw [G30_34_formula]
  exact vasyuninBEntry_30_34_eval

def interval_30_34 : NamedVasyuninInterval :=
{
  h := 30
  k := 34
  lower := (27572633/773670000)
  upper := (27727367/773670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_34_interval
}

theorem G30_35_formula : baezDuarteGramEntry 30 35 = vasyuninBEntry 30 35 := vasyuninBEntry_correct_axiom 30 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_35_eval :
    ((((9243389/266110000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 35) ∧
    (vasyuninBEntry 30 35 ≤ (((9296611/266110000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_6_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 6 7 5 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G30_35_interval :
    ((((9243389/266110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 35) ∧
    (baezDuarteGramEntry 30 35 ≤ (((9296611/266110000) : ℚ) : ℝ)) := by
  rw [G30_35_formula]
  exact vasyuninBEntry_30_35_eval

def interval_30_35 : NamedVasyuninInterval :=
{
  h := 30
  k := 35
  lower := (9243389/266110000)
  upper := (9296611/266110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_35_interval
}

theorem G30_36_formula : baezDuarteGramEntry 30 36 = vasyuninBEntry 30 36 := vasyuninBEntry_correct_axiom 30 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_36_eval :
    ((((17448577/514230000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 36) ∧
    (vasyuninBEntry 30 36 ≤ (((17551423/514230000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_6_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 6 6 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G30_36_interval :
    ((((17448577/514230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 36) ∧
    (baezDuarteGramEntry 30 36 ≤ (((17551423/514230000) : ℚ) : ℝ)) := by
  rw [G30_36_formula]
  exact vasyuninBEntry_30_36_eval

def interval_30_36 : NamedVasyuninInterval :=
{
  h := 30
  k := 36
  lower := (17448577/514230000)
  upper := (17551423/514230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_36_interval
}

theorem G30_37_formula : baezDuarteGramEntry 30 37 = vasyuninBEntry 30 37 := vasyuninBEntry_correct_axiom 30 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_37_eval :
    ((((14600983/440170000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 37) ∧
    (vasyuninBEntry 30 37 ≤ (((14689017/440170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3037_formula_bound
  constructor <;> linarith

theorem G30_37_interval :
    ((((14600983/440170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 37) ∧
    (baezDuarteGramEntry 30 37 ≤ (((14689017/440170000) : ℚ) : ℝ)) := by
  rw [G30_37_formula]
  exact vasyuninBEntry_30_37_eval

def interval_30_37 : NamedVasyuninInterval :=
{
  h := 30
  k := 37
  lower := (14600983/440170000)
  upper := (14689017/440170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_37_interval
}

theorem G30_38_formula : baezDuarteGramEntry 30 38 = vasyuninBEntry 30 38 := vasyuninBEntry_correct_axiom 30 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_38_eval :
    ((((24135749/742510000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 38) ∧
    (vasyuninBEntry 30 38 ≤ (((24284251/742510000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_15_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 15 19 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G30_38_interval :
    ((((24135749/742510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 38) ∧
    (baezDuarteGramEntry 30 38 ≤ (((24284251/742510000) : ℚ) : ℝ)) := by
  rw [G30_38_formula]
  exact vasyuninBEntry_30_38_eval

def interval_30_38 : NamedVasyuninInterval :=
{
  h := 30
  k := 38
  lower := (24135749/742510000)
  upper := (24284251/742510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_38_interval
}

theorem G30_39_formula : baezDuarteGramEntry 30 39 = vasyuninBEntry 30 39 := vasyuninBEntry_correct_axiom 30 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_39_eval :
    ((((7648523/239770000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 39) ∧
    (vasyuninBEntry 30 39 ≤ (((7696477/239770000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_10_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 10 13 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G30_39_interval :
    ((((7648523/239770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 39) ∧
    (baezDuarteGramEntry 30 39 ≤ (((7696477/239770000) : ℚ) : ℝ)) := by
  rw [G30_39_formula]
  exact vasyuninBEntry_30_39_eval

def interval_30_39 : NamedVasyuninInterval :=
{
  h := 30
  k := 39
  lower := (7648523/239770000)
  upper := (7696477/239770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_39_interval
}

theorem G30_40_formula : baezDuarteGramEntry 30 40 = vasyuninBEntry 30 40 := vasyuninBEntry_correct_axiom 30 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_40_eval :
    ((((1259993/40070000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 40) ∧
    (vasyuninBEntry 30 40 ≤ (((1268007/40070000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 4 10 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 10)
  constructor <;> linarith

theorem G30_40_interval :
    ((((1259993/40070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 40) ∧
    (baezDuarteGramEntry 30 40 ≤ (((1268007/40070000) : ℚ) : ℝ)) := by
  rw [G30_40_formula]
  exact vasyuninBEntry_30_40_eval

def interval_30_40 : NamedVasyuninInterval :=
{
  h := 30
  k := 40
  lower := (1259993/40070000)
  upper := (1268007/40070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_40_interval
}

theorem G30_41_formula : baezDuarteGramEntry 30 41 = vasyuninBEntry 30 41 := vasyuninBEntry_correct_axiom 30 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_41_eval :
    ((((184521/5990000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 41) ∧
    (vasyuninBEntry 30 41 ≤ (((185719/5990000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3041_formula_bound
  constructor <;> linarith

theorem G30_41_interval :
    ((((184521/5990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 41) ∧
    (baezDuarteGramEntry 30 41 ≤ (((185719/5990000) : ℚ) : ℝ)) := by
  rw [G30_41_formula]
  exact vasyuninBEntry_30_41_eval

def interval_30_41 : NamedVasyuninInterval :=
{
  h := 30
  k := 41
  lower := (184521/5990000)
  upper := (185719/5990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_41_interval
}

theorem G30_42_formula : baezDuarteGramEntry 30 42 = vasyuninBEntry 30 42 := vasyuninBEntry_correct_axiom 30 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_42_eval :
    ((((6040087/199130000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 42) ∧
    (vasyuninBEntry 30 42 ≤ (((6079913/199130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 7 6 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G30_42_interval :
    ((((6040087/199130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 42) ∧
    (baezDuarteGramEntry 30 42 ≤ (((6079913/199130000) : ℚ) : ℝ)) := by
  rw [G30_42_formula]
  exact vasyuninBEntry_30_42_eval

def interval_30_42 : NamedVasyuninInterval :=
{
  h := 30
  k := 42
  lower := (6040087/199130000)
  upper := (6079913/199130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_42_interval
}

theorem G30_43_formula : baezDuarteGramEntry 30 43 = vasyuninBEntry 30 43 := vasyuninBEntry_correct_axiom 30 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_43_eval :
    ((((1092343/36570000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 43) ∧
    (vasyuninBEntry 30 43 ≤ (((1099657/36570000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3043_formula_bound
  constructor <;> linarith

theorem G30_43_interval :
    ((((1092343/36570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 43) ∧
    (baezDuarteGramEntry 30 43 ≤ (((1099657/36570000) : ℚ) : ℝ)) := by
  rw [G30_43_formula]
  exact vasyuninBEntry_30_43_eval

def interval_30_43 : NamedVasyuninInterval :=
{
  h := 30
  k := 43
  lower := (1092343/36570000)
  upper := (1099657/36570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_43_interval
}

theorem G30_44_formula : baezDuarteGramEntry 30 44 = vasyuninBEntry 30 44 := vasyuninBEntry_correct_axiom 30 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_44_eval :
    ((((17002367/576330000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 44) ∧
    (vasyuninBEntry 30 44 ≤ (((17117633/576330000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_15_22_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 15 22 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G30_44_interval :
    ((((17002367/576330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 44) ∧
    (baezDuarteGramEntry 30 44 ≤ (((17117633/576330000) : ℚ) : ℝ)) := by
  rw [G30_44_formula]
  exact vasyuninBEntry_30_44_eval

def interval_30_44 : NamedVasyuninInterval :=
{
  h := 30
  k := 44
  lower := (17002367/576330000)
  upper := (17117633/576330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_44_interval
}

theorem G30_45_formula : baezDuarteGramEntry 30 45 = vasyuninBEntry 30 45 := vasyuninBEntry_correct_axiom 30 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_45_eval :
    ((((14176627/483730000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 45) ∧
    (vasyuninBEntry 30 45 ≤ (((14273373/483730000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 15 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 15)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 15)
  constructor <;> linarith

theorem G30_45_interval :
    ((((14176627/483730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 45) ∧
    (baezDuarteGramEntry 30 45 ≤ (((14273373/483730000) : ℚ) : ℝ)) := by
  rw [G30_45_formula]
  exact vasyuninBEntry_30_45_eval

def interval_30_45 : NamedVasyuninInterval :=
{
  h := 30
  k := 45
  lower := (14176627/483730000)
  upper := (14273373/483730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_45_interval
}

theorem G30_46_formula : baezDuarteGramEntry 30 46 = vasyuninBEntry 30 46 := vasyuninBEntry_correct_axiom 30 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_46_eval :
    ((((23119403/805970000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 46) ∧
    (vasyuninBEntry 30 46 ≤ (((23280597/805970000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_15_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 15 23 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G30_46_interval :
    ((((23119403/805970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 46) ∧
    (baezDuarteGramEntry 30 46 ≤ (((23280597/805970000) : ℚ) : ℝ)) := by
  rw [G30_46_formula]
  exact vasyuninBEntry_30_46_eval

def interval_30_46 : NamedVasyuninInterval :=
{
  h := 30
  k := 46
  lower := (23119403/805970000)
  upper := (23280597/805970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_46_interval
}

theorem G30_47_formula : baezDuarteGramEntry 30 47 = vasyuninBEntry 30 47 := vasyuninBEntry_correct_axiom 30 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_47_eval :
    ((((28090519/994810000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 47) ∧
    (vasyuninBEntry 30 47 ≤ (((28289481/994810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3047_formula_bound
  constructor <;> linarith

theorem G30_47_interval :
    ((((28090519/994810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 47) ∧
    (baezDuarteGramEntry 30 47 ≤ (((28289481/994810000) : ℚ) : ℝ)) := by
  rw [G30_47_formula]
  exact vasyuninBEntry_30_47_eval

def interval_30_47 : NamedVasyuninInterval :=
{
  h := 30
  k := 47
  lower := (28090519/994810000)
  upper := (28289481/994810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_47_interval
}

theorem G30_48_formula : baezDuarteGramEntry 30 48 = vasyuninBEntry 30 48 := vasyuninBEntry_correct_axiom 30 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_48_eval :
    ((((417751/14990000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 48) ∧
    (vasyuninBEntry 30 48 ≤ (((420749/14990000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 8 6 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G30_48_interval :
    ((((417751/14990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 48) ∧
    (baezDuarteGramEntry 30 48 ≤ (((420749/14990000) : ℚ) : ℝ)) := by
  rw [G30_48_formula]
  exact vasyuninBEntry_30_48_eval

def interval_30_48 : NamedVasyuninInterval :=
{
  h := 30
  k := 48
  lower := (417751/14990000)
  upper := (420749/14990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_48_interval
}

theorem G30_49_formula : baezDuarteGramEntry 30 49 = vasyuninBEntry 30 49 := vasyuninBEntry_correct_axiom 30 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_49_eval :
    ((((6207433/225670000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 49) ∧
    (vasyuninBEntry 30 49 ≤ (((6252567/225670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3049_formula_bound
  constructor <;> linarith

theorem G30_49_interval :
    ((((6207433/225670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 49) ∧
    (baezDuarteGramEntry 30 49 ≤ (((6252567/225670000) : ℚ) : ℝ)) := by
  rw [G30_49_formula]
  exact vasyuninBEntry_30_49_eval

def interval_30_49 : NamedVasyuninInterval :=
{
  h := 30
  k := 49
  lower := (6207433/225670000)
  upper := (6252567/225670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_49_interval
}

theorem G30_50_formula : baezDuarteGramEntry 30 50 = vasyuninBEntry 30 50 := vasyuninBEntry_correct_axiom 30 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_30_50_eval :
    ((((169939/6235000) : ℚ) : ℝ) ≤ vasyuninBEntry 30 50) ∧
    (vasyuninBEntry 30 50 ≤ (((85593/3117500) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 5 10 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 10)
  constructor <;> linarith

theorem G30_50_interval :
    ((((169939/6235000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 30 50) ∧
    (baezDuarteGramEntry 30 50 ≤ (((85593/3117500) : ℚ) : ℝ)) := by
  rw [G30_50_formula]
  exact vasyuninBEntry_30_50_eval

def interval_30_50 : NamedVasyuninInterval :=
{
  h := 30
  k := 50
  lower := (169939/6235000)
  upper := (85593/3117500)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G30_50_interval
}

theorem G31_1_formula : baezDuarteGramEntry 31 1 = vasyuninBEntry 1 31 := by
  rw [baezDuarteGramEntry_symm 31 1]
  exact G1_31_formula

theorem G31_1_interval :
    ((((23764139/258610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 1) ∧
    (baezDuarteGramEntry 31 1 ≤ (((23815861/258610000) : ℚ) : ℝ)) := by
  rw [G31_1_formula]
  exact vasyuninBEntry_1_31_eval

def interval_31_1 : NamedVasyuninInterval :=
{
  h := 31
  k := 1
  lower := (23764139/258610000)
  upper := (23815861/258610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_1_interval
}

theorem G31_2_formula : baezDuarteGramEntry 31 2 = vasyuninBEntry 2 31 := by
  rw [baezDuarteGramEntry_symm 31 2]
  exact G2_31_formula

theorem G31_2_interval :
    ((((10839041/134590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 2) ∧
    (baezDuarteGramEntry 31 2 ≤ (((10865959/134590000) : ℚ) : ℝ)) := by
  rw [G31_2_formula]
  exact vasyuninBEntry_2_31_eval

def interval_31_2 : NamedVasyuninInterval :=
{
  h := 31
  k := 2
  lower := (10839041/134590000)
  upper := (10865959/134590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_2_interval
}

theorem G31_3_formula : baezDuarteGramEntry 31 3 = vasyuninBEntry 3 31 := by
  rw [baezDuarteGramEntry_symm 31 3]
  exact G3_31_formula

theorem G31_3_interval :
    ((((8773137/118630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 3) ∧
    (baezDuarteGramEntry 31 3 ≤ (((8796863/118630000) : ℚ) : ℝ)) := by
  rw [G31_3_formula]
  exact vasyuninBEntry_3_31_eval

def interval_31_3 : NamedVasyuninInterval :=
{
  h := 31
  k := 3
  lower := (8773137/118630000)
  upper := (8796863/118630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_3_interval
}

theorem G31_4_formula : baezDuarteGramEntry 31 4 = vasyuninBEntry 4 31 := by
  rw [baezDuarteGramEntry_symm 31 4]
  exact G4_31_formula

theorem G31_4_interval :
    ((((57127577/824230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 4) ∧
    (baezDuarteGramEntry 31 4 ≤ (((57292423/824230000) : ℚ) : ℝ)) := by
  rw [G31_4_formula]
  exact vasyuninBEntry_4_31_eval

def interval_31_4 : NamedVasyuninInterval :=
{
  h := 31
  k := 4
  lower := (57127577/824230000)
  upper := (57292423/824230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_4_interval
}

theorem G31_5_formula : baezDuarteGramEntry 31 5 = vasyuninBEntry 5 31 := by
  rw [baezDuarteGramEntry_symm 31 5]
  exact G5_31_formula

theorem G31_5_interval :
    ((((35955331/546690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 5) ∧
    (baezDuarteGramEntry 31 5 ≤ (((36064669/546690000) : ℚ) : ℝ)) := by
  rw [G31_5_formula]
  exact vasyuninBEntry_5_31_eval

def interval_31_5 : NamedVasyuninInterval :=
{
  h := 31
  k := 5
  lower := (35955331/546690000)
  upper := (36064669/546690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_5_interval
}

theorem G31_6_formula : baezDuarteGramEntry 31 6 = vasyuninBEntry 6 31 := by
  rw [baezDuarteGramEntry_symm 31 6]
  exact G6_31_formula

theorem G31_6_interval :
    ((((1077287/17130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 6) ∧
    (baezDuarteGramEntry 31 6 ≤ (((1080713/17130000) : ℚ) : ℝ)) := by
  rw [G31_6_formula]
  exact vasyuninBEntry_6_31_eval

def interval_31_6 : NamedVasyuninInterval :=
{
  h := 31
  k := 6
  lower := (1077287/17130000)
  upper := (1080713/17130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_6_interval
}

theorem G31_7_formula : baezDuarteGramEntry 31 7 = vasyuninBEntry 7 31 := by
  rw [baezDuarteGramEntry_symm 31 7]
  exact G7_31_formula

theorem G31_7_interval :
    ((((607739/10110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 7) ∧
    (baezDuarteGramEntry 31 7 ≤ (((609761/10110000) : ℚ) : ℝ)) := by
  rw [G31_7_formula]
  exact vasyuninBEntry_7_31_eval

def interval_31_7 : NamedVasyuninInterval :=
{
  h := 31
  k := 7
  lower := (607739/10110000)
  upper := (609761/10110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_7_interval
}

theorem G31_8_formula : baezDuarteGramEntry 31 8 = vasyuninBEntry 8 31 := by
  rw [baezDuarteGramEntry_symm 31 8]
  exact G8_31_formula

theorem G31_8_interval :
    ((((57152033/979670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 8) ∧
    (baezDuarteGramEntry 31 8 ≤ (((57347967/979670000) : ℚ) : ℝ)) := by
  rw [G31_8_formula]
  exact vasyuninBEntry_8_31_eval

def interval_31_8 : NamedVasyuninInterval :=
{
  h := 31
  k := 8
  lower := (57152033/979670000)
  upper := (57347967/979670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_8_interval
}

theorem G31_9_formula : baezDuarteGramEntry 31 9 = vasyuninBEntry 9 31 := by
  rw [baezDuarteGramEntry_symm 31 9]
  exact G9_31_formula

theorem G31_9_interval :
    ((((2748841/49090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 9) ∧
    (baezDuarteGramEntry 31 9 ≤ (((2758659/49090000) : ℚ) : ℝ)) := by
  rw [G31_9_formula]
  exact vasyuninBEntry_9_31_eval

def interval_31_9 : NamedVasyuninInterval :=
{
  h := 31
  k := 9
  lower := (2748841/49090000)
  upper := (2758659/49090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_9_interval
}

theorem G31_10_formula : baezDuarteGramEntry 31 10 = vasyuninBEntry 10 31 := by
  rw [baezDuarteGramEntry_symm 31 10]
  exact G10_31_formula

theorem G31_10_interval :
    ((((2198003/39970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 10) ∧
    (baezDuarteGramEntry 31 10 ≤ (((2205997/39970000) : ℚ) : ℝ)) := by
  rw [G31_10_formula]
  exact vasyuninBEntry_10_31_eval

def interval_31_10 : NamedVasyuninInterval :=
{
  h := 31
  k := 10
  lower := (2198003/39970000)
  upper := (2205997/39970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_10_interval
}

theorem G31_11_formula : baezDuarteGramEntry 31 11 = vasyuninBEntry 11 31 := by
  rw [baezDuarteGramEntry_symm 31 11]
  exact G11_31_formula

theorem G31_11_interval :
    ((((51792233/977670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 11) ∧
    (baezDuarteGramEntry 31 11 ≤ (((51987767/977670000) : ℚ) : ℝ)) := by
  rw [G31_11_formula]
  exact vasyuninBEntry_11_31_eval

def interval_31_11 : NamedVasyuninInterval :=
{
  h := 31
  k := 11
  lower := (51792233/977670000)
  upper := (51987767/977670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_11_interval
}

theorem G31_12_formula : baezDuarteGramEntry 31 12 = vasyuninBEntry 12 31 := by
  rw [baezDuarteGramEntry_symm 31 12]
  exact G12_31_formula

theorem G31_12_interval :
    ((((21053881/411190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 12) ∧
    (baezDuarteGramEntry 31 12 ≤ (((21136119/411190000) : ℚ) : ℝ)) := by
  rw [G31_12_formula]
  exact vasyuninBEntry_12_31_eval

def interval_31_12 : NamedVasyuninInterval :=
{
  h := 31
  k := 12
  lower := (21053881/411190000)
  upper := (21136119/411190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_12_interval
}

theorem G31_13_formula : baezDuarteGramEntry 31 13 = vasyuninBEntry 13 31 := by
  rw [baezDuarteGramEntry_symm 31 13]
  exact G13_31_formula

theorem G31_13_interval :
    ((((11080317/221830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 13) ∧
    (baezDuarteGramEntry 31 13 ≤ (((11124683/221830000) : ℚ) : ℝ)) := by
  rw [G31_13_formula]
  exact vasyuninBEntry_13_31_eval

def interval_31_13 : NamedVasyuninInterval :=
{
  h := 31
  k := 13
  lower := (11080317/221830000)
  upper := (11124683/221830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_13_interval
}

theorem G31_14_formula : baezDuarteGramEntry 31 14 = vasyuninBEntry 14 31 := by
  rw [baezDuarteGramEntry_symm 31 14]
  exact G14_31_formula

theorem G31_14_interval :
    ((((48012237/977630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 14) ∧
    (baezDuarteGramEntry 31 14 ≤ (((48207763/977630000) : ℚ) : ℝ)) := by
  rw [G31_14_formula]
  exact vasyuninBEntry_14_31_eval

def interval_31_14 : NamedVasyuninInterval :=
{
  h := 31
  k := 14
  lower := (48012237/977630000)
  upper := (48207763/977630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_14_interval
}

theorem G31_15_formula : baezDuarteGramEntry 31 15 = vasyuninBEntry 15 31 := by
  rw [baezDuarteGramEntry_symm 31 15]
  exact G15_31_formula

theorem G31_15_interval :
    ((((8036093/164070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 15) ∧
    (baezDuarteGramEntry 31 15 ≤ (((8068907/164070000) : ℚ) : ℝ)) := by
  rw [G31_15_formula]
  exact vasyuninBEntry_15_31_eval

def interval_31_15 : NamedVasyuninInterval :=
{
  h := 31
  k := 15
  lower := (8036093/164070000)
  upper := (8068907/164070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_15_interval
}

theorem G31_16_formula : baezDuarteGramEntry 31 16 = vasyuninBEntry 16 31 := by
  rw [baezDuarteGramEntry_symm 31 16]
  exact G16_31_formula

theorem G31_16_interval :
    ((((4036567/84330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 16) ∧
    (baezDuarteGramEntry 31 16 ≤ (((4053433/84330000) : ℚ) : ℝ)) := by
  rw [G31_16_formula]
  exact vasyuninBEntry_16_31_eval

def interval_31_16 : NamedVasyuninInterval :=
{
  h := 31
  k := 16
  lower := (4036567/84330000)
  upper := (4053433/84330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_16_interval
}

theorem G31_17_formula : baezDuarteGramEntry 31 17 = vasyuninBEntry 17 31 := by
  rw [baezDuarteGramEntry_symm 31 17]
  exact G17_31_formula

theorem G31_17_interval :
    ((((5416193/118070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 17) ∧
    (baezDuarteGramEntry 31 17 ≤ (((5439807/118070000) : ℚ) : ℝ)) := by
  rw [G31_17_formula]
  exact vasyuninBEntry_17_31_eval

def interval_31_17 : NamedVasyuninInterval :=
{
  h := 31
  k := 17
  lower := (5416193/118070000)
  upper := (5439807/118070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_17_interval
}

theorem G31_18_formula : baezDuarteGramEntry 31 18 = vasyuninBEntry 18 31 := by
  rw [baezDuarteGramEntry_symm 31 18]
  exact G18_31_formula

theorem G31_18_interval :
    ((((12506921/280790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 18) ∧
    (baezDuarteGramEntry 31 18 ≤ (((12563079/280790000) : ℚ) : ℝ)) := by
  rw [G31_18_formula]
  exact vasyuninBEntry_18_31_eval

def interval_31_18 : NamedVasyuninInterval :=
{
  h := 31
  k := 18
  lower := (12506921/280790000)
  upper := (12563079/280790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_18_interval
}

theorem G31_19_formula : baezDuarteGramEntry 31 19 = vasyuninBEntry 19 31 := by
  rw [baezDuarteGramEntry_symm 31 19]
  exact G19_31_formula

theorem G31_19_interval :
    ((((39698773/912270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 19) ∧
    (baezDuarteGramEntry 31 19 ≤ (((39881227/912270000) : ℚ) : ℝ)) := by
  rw [G31_19_formula]
  exact vasyuninBEntry_19_31_eval

def interval_31_19 : NamedVasyuninInterval :=
{
  h := 31
  k := 19
  lower := (39698773/912270000)
  upper := (39881227/912270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_19_interval
}

theorem G31_20_formula : baezDuarteGramEntry 31 20 = vasyuninBEntry 20 31 := by
  rw [baezDuarteGramEntry_symm 31 20]
  exact G20_31_formula

theorem G31_20_interval :
    ((((42580339/996610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 20) ∧
    (baezDuarteGramEntry 31 20 ≤ (((42779661/996610000) : ℚ) : ℝ)) := by
  rw [G31_20_formula]
  exact vasyuninBEntry_20_31_eval

def interval_31_20 : NamedVasyuninInterval :=
{
  h := 31
  k := 20
  lower := (42580339/996610000)
  upper := (42779661/996610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_20_interval
}

theorem G31_21_formula : baezDuarteGramEntry 31 21 = vasyuninBEntry 21 31 := by
  rw [baezDuarteGramEntry_symm 31 21]
  exact G21_31_formula

theorem G31_21_interval :
    ((((2075067/49330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 21) ∧
    (baezDuarteGramEntry 31 21 ≤ (((2084933/49330000) : ℚ) : ℝ)) := by
  rw [G31_21_formula]
  exact vasyuninBEntry_21_31_eval

def interval_31_21 : NamedVasyuninInterval :=
{
  h := 31
  k := 21
  lower := (2075067/49330000)
  upper := (2084933/49330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_21_interval
}

theorem G31_22_formula : baezDuarteGramEntry 31 22 = vasyuninBEntry 22 31 := by
  rw [baezDuarteGramEntry_symm 31 22]
  exact G22_31_formula

theorem G31_22_interval :
    ((((15776707/382930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 22) ∧
    (baezDuarteGramEntry 31 22 ≤ (((15853293/382930000) : ℚ) : ℝ)) := by
  rw [G31_22_formula]
  exact vasyuninBEntry_22_31_eval

def interval_31_22 : NamedVasyuninInterval :=
{
  h := 31
  k := 22
  lower := (15776707/382930000)
  upper := (15853293/382930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_22_interval
}

theorem G31_23_formula : baezDuarteGramEntry 31 23 = vasyuninBEntry 23 31 := by
  rw [baezDuarteGramEntry_symm 31 23]
  exact G23_31_formula

theorem G31_23_interval :
    ((((17816153/438470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 23) ∧
    (baezDuarteGramEntry 31 23 ≤ (((17903847/438470000) : ℚ) : ℝ)) := by
  rw [G31_23_formula]
  exact vasyuninBEntry_23_31_eval

def interval_31_23 : NamedVasyuninInterval :=
{
  h := 31
  k := 23
  lower := (17816153/438470000)
  upper := (17903847/438470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_23_interval
}

theorem G31_24_formula : baezDuarteGramEntry 31 24 = vasyuninBEntry 24 31 := by
  rw [baezDuarteGramEntry_symm 31 24]
  exact G24_31_formula

theorem G31_24_interval :
    ((((27082421/675790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 24) ∧
    (baezDuarteGramEntry 31 24 ≤ (((27217579/675790000) : ℚ) : ℝ)) := by
  rw [G31_24_formula]
  exact vasyuninBEntry_24_31_eval

def interval_31_24 : NamedVasyuninInterval :=
{
  h := 31
  k := 24
  lower := (27082421/675790000)
  upper := (27217579/675790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_24_interval
}

theorem G31_25_formula : baezDuarteGramEntry 31 25 = vasyuninBEntry 25 31 := by
  rw [baezDuarteGramEntry_symm 31 25]
  exact G25_31_formula

theorem G31_25_interval :
    ((((10244177/258230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 25) ∧
    (baezDuarteGramEntry 31 25 ≤ (((10295823/258230000) : ℚ) : ℝ)) := by
  rw [G31_25_formula]
  exact vasyuninBEntry_25_31_eval

def interval_31_25 : NamedVasyuninInterval :=
{
  h := 31
  k := 25
  lower := (10244177/258230000)
  upper := (10295823/258230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_25_interval
}

theorem G31_26_formula : baezDuarteGramEntry 31 26 = vasyuninBEntry 26 31 := by
  rw [baezDuarteGramEntry_symm 31 26]
  exact G26_31_formula

theorem G31_26_interval :
    ((((29036201/737990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 26) ∧
    (baezDuarteGramEntry 31 26 ≤ (((29183799/737990000) : ℚ) : ℝ)) := by
  rw [G31_26_formula]
  exact vasyuninBEntry_26_31_eval

def interval_31_26 : NamedVasyuninInterval :=
{
  h := 31
  k := 26
  lower := (29036201/737990000)
  upper := (29183799/737990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_26_interval
}

theorem G31_27_formula : baezDuarteGramEntry 31 27 = vasyuninBEntry 27 31 := by
  rw [baezDuarteGramEntry_symm 31 27]
  exact G27_31_formula

theorem G31_27_interval :
    ((((38950479/995210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 27) ∧
    (baezDuarteGramEntry 31 27 ≤ (((39149521/995210000) : ℚ) : ℝ)) := by
  rw [G31_27_formula]
  exact vasyuninBEntry_27_31_eval

def interval_31_27 : NamedVasyuninInterval :=
{
  h := 31
  k := 27
  lower := (38950479/995210000)
  upper := (39149521/995210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_27_interval
}

theorem G31_28_formula : baezDuarteGramEntry 31 28 = vasyuninBEntry 28 31 := by
  rw [baezDuarteGramEntry_symm 31 28]
  exact G28_31_formula

theorem G31_28_interval :
    ((((35299649/903510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 28) ∧
    (baezDuarteGramEntry 31 28 ≤ (((35480351/903510000) : ℚ) : ℝ)) := by
  rw [G31_28_formula]
  exact vasyuninBEntry_28_31_eval

def interval_31_28 : NamedVasyuninInterval :=
{
  h := 31
  k := 28
  lower := (35299649/903510000)
  upper := (35480351/903510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_28_interval
}

theorem G31_29_formula : baezDuarteGramEntry 31 29 = vasyuninBEntry 29 31 := by
  rw [baezDuarteGramEntry_symm 31 29]
  exact G29_31_formula

theorem G31_29_interval :
    ((((35140293/897070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 29) ∧
    (baezDuarteGramEntry 31 29 ≤ (((35319707/897070000) : ℚ) : ℝ)) := by
  rw [G31_29_formula]
  exact vasyuninBEntry_29_31_eval

def interval_31_29 : NamedVasyuninInterval :=
{
  h := 31
  k := 29
  lower := (35140293/897070000)
  upper := (35319707/897070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_29_interval
}

theorem G31_30_formula : baezDuarteGramEntry 31 30 = vasyuninBEntry 30 31 := by
  rw [baezDuarteGramEntry_symm 31 30]
  exact G30_31_formula

theorem G31_30_interval :
    ((((3872703/97970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 30) ∧
    (baezDuarteGramEntry 31 30 ≤ (((3892297/97970000) : ℚ) : ℝ)) := by
  rw [G31_30_formula]
  exact vasyuninBEntry_30_31_eval

def interval_31_30 : NamedVasyuninInterval :=
{
  h := 31
  k := 30
  lower := (3872703/97970000)
  upper := (3892297/97970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_30_interval
}

theorem G31_31_formula_eq : baezDuarteGramEntry 31 31 = (1 / (31 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 31 := by norm_num
  rw [baez_duarte_diagonal_scaling 31 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G31_31_log_gamma_interval :
  ((((36689557/904430000) : ℚ) : ℝ) ≤ (1 / (31 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (31 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((36870443/904430000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 31 (by norm_num)
  constructor
  · have : ((((36689557/904430000) : ℚ) : ℝ) ≤ (1 / (31 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (31 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((36870443/904430000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G31_31_interval : ((((36689557/904430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 31) ∧ (baezDuarteGramEntry 31 31 ≤ (((36870443/904430000) : ℚ) : ℝ)) := by
  rw [G31_31_formula_eq]
  exact G31_31_log_gamma_interval

def interval_31_31 : NamedVasyuninInterval :=
{
  h := 31
  k := 31
  lower := (36689557/904430000)
  upper := (36870443/904430000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G31_31_interval
}

theorem G31_32_formula : baezDuarteGramEntry 31 32 = vasyuninBEntry 31 32 := vasyuninBEntry_correct_axiom 31 32 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_32_eval :
    ((((3613567/94330000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 32) ∧
    (vasyuninBEntry 31 32 ≤ (((3632433/94330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3132_formula_bound
  constructor <;> linarith

theorem G31_32_interval :
    ((((3613567/94330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 32) ∧
    (baezDuarteGramEntry 31 32 ≤ (((3632433/94330000) : ℚ) : ℝ)) := by
  rw [G31_32_formula]
  exact vasyuninBEntry_31_32_eval

def interval_31_32 : NamedVasyuninInterval :=
{
  h := 31
  k := 32
  lower := (3613567/94330000)
  upper := (3632433/94330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_32_interval
}

theorem G31_33_formula : baezDuarteGramEntry 31 33 = vasyuninBEntry 31 33 := vasyuninBEntry_correct_axiom 31 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_33_eval :
    ((((32092833/871670000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 33) ∧
    (vasyuninBEntry 31 33 ≤ (((32267167/871670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3133_formula_bound
  constructor <;> linarith

theorem G31_33_interval :
    ((((32092833/871670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 33) ∧
    (baezDuarteGramEntry 31 33 ≤ (((32267167/871670000) : ℚ) : ℝ)) := by
  rw [G31_33_formula]
  exact vasyuninBEntry_31_33_eval

def interval_31_33 : NamedVasyuninInterval :=
{
  h := 31
  k := 33
  lower := (32092833/871670000)
  upper := (32267167/871670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_33_interval
}

theorem G31_34_formula : baezDuarteGramEntry 31 34 = vasyuninBEntry 31 34 := vasyuninBEntry_correct_axiom 31 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_34_eval :
    ((((24670741/692590000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 34) ∧
    (vasyuninBEntry 31 34 ≤ (((24809259/692590000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3134_formula_bound
  constructor <;> linarith

theorem G31_34_interval :
    ((((24670741/692590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 34) ∧
    (baezDuarteGramEntry 31 34 ≤ (((24809259/692590000) : ℚ) : ℝ)) := by
  rw [G31_34_formula]
  exact vasyuninBEntry_31_34_eval

def interval_31_34 : NamedVasyuninInterval :=
{
  h := 31
  k := 34
  lower := (24670741/692590000)
  upper := (24809259/692590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_34_interval
}

theorem G31_35_formula : baezDuarteGramEntry 31 35 = vasyuninBEntry 31 35 := vasyuninBEntry_correct_axiom 31 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_35_eval :
    ((((16671829/481710000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 35) ∧
    (vasyuninBEntry 31 35 ≤ (((16768171/481710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3135_formula_bound
  constructor <;> linarith

theorem G31_35_interval :
    ((((16671829/481710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 35) ∧
    (baezDuarteGramEntry 31 35 ≤ (((16768171/481710000) : ℚ) : ℝ)) := by
  rw [G31_35_formula]
  exact vasyuninBEntry_31_35_eval

def interval_31_35 : NamedVasyuninInterval :=
{
  h := 31
  k := 35
  lower := (16671829/481710000)
  upper := (16768171/481710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_35_interval
}

theorem G31_36_formula : baezDuarteGramEntry 31 36 = vasyuninBEntry 31 36 := vasyuninBEntry_correct_axiom 31 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_36_eval :
    ((((33510657/993430000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 36) ∧
    (vasyuninBEntry 31 36 ≤ (((33709343/993430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3136_formula_bound
  constructor <;> linarith

theorem G31_36_interval :
    ((((33510657/993430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 36) ∧
    (baezDuarteGramEntry 31 36 ≤ (((33709343/993430000) : ℚ) : ℝ)) := by
  rw [G31_36_formula]
  exact vasyuninBEntry_31_36_eval

def interval_31_36 : NamedVasyuninInterval :=
{
  h := 31
  k := 36
  lower := (33510657/993430000)
  upper := (33709343/993430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_36_interval
}

theorem G31_37_formula : baezDuarteGramEntry 31 37 = vasyuninBEntry 31 37 := vasyuninBEntry_correct_axiom 31 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_37_eval :
    ((((27466657/833430000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 37) ∧
    (vasyuninBEntry 31 37 ≤ (((27633343/833430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3137_formula_bound
  constructor <;> linarith

theorem G31_37_interval :
    ((((27466657/833430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 37) ∧
    (baezDuarteGramEntry 31 37 ≤ (((27633343/833430000) : ℚ) : ℝ)) := by
  rw [G31_37_formula]
  exact vasyuninBEntry_31_37_eval

def interval_31_37 : NamedVasyuninInterval :=
{
  h := 31
  k := 37
  lower := (27466657/833430000)
  upper := (27633343/833430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_37_interval
}

theorem G31_38_formula : baezDuarteGramEntry 31 38 = vasyuninBEntry 31 38 := vasyuninBEntry_correct_axiom 31 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_38_eval :
    ((((2618879/81210000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 38) ∧
    (vasyuninBEntry 31 38 ≤ (((2635121/81210000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3138_formula_bound
  constructor <;> linarith

theorem G31_38_interval :
    ((((2618879/81210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 38) ∧
    (baezDuarteGramEntry 31 38 ≤ (((2635121/81210000) : ℚ) : ℝ)) := by
  rw [G31_38_formula]
  exact vasyuninBEntry_31_38_eval

def interval_31_38 : NamedVasyuninInterval :=
{
  h := 31
  k := 38
  lower := (2618879/81210000)
  upper := (2635121/81210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_38_interval
}

theorem G31_39_formula : baezDuarteGramEntry 31 39 = vasyuninBEntry 31 39 := vasyuninBEntry_correct_axiom 31 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_39_eval :
    ((((6696327/211730000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 39) ∧
    (vasyuninBEntry 31 39 ≤ (((6738673/211730000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3139_formula_bound
  constructor <;> linarith

theorem G31_39_interval :
    ((((6696327/211730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 39) ∧
    (baezDuarteGramEntry 31 39 ≤ (((6738673/211730000) : ℚ) : ℝ)) := by
  rw [G31_39_formula]
  exact vasyuninBEntry_31_39_eval

def interval_31_39 : NamedVasyuninInterval :=
{
  h := 31
  k := 39
  lower := (6696327/211730000)
  upper := (6738673/211730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_39_interval
}

theorem G31_40_formula : baezDuarteGramEntry 31 40 = vasyuninBEntry 31 40 := vasyuninBEntry_correct_axiom 31 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_40_eval :
    ((((28258921/910790000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 40) ∧
    (vasyuninBEntry 31 40 ≤ (((28441079/910790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3140_formula_bound
  constructor <;> linarith

theorem G31_40_interval :
    ((((28258921/910790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 40) ∧
    (baezDuarteGramEntry 31 40 ≤ (((28441079/910790000) : ℚ) : ℝ)) := by
  rw [G31_40_formula]
  exact vasyuninBEntry_31_40_eval

def interval_31_40 : NamedVasyuninInterval :=
{
  h := 31
  k := 40
  lower := (28258921/910790000)
  upper := (28441079/910790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_40_interval
}

theorem G31_41_formula : baezDuarteGramEntry 31 41 = vasyuninBEntry 31 41 := vasyuninBEntry_correct_axiom 31 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_41_eval :
    ((((3650543/119570000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 41) ∧
    (vasyuninBEntry 31 41 ≤ (((3674457/119570000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3141_formula_bound
  constructor <;> linarith

theorem G31_41_interval :
    ((((3650543/119570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 41) ∧
    (baezDuarteGramEntry 31 41 ≤ (((3674457/119570000) : ℚ) : ℝ)) := by
  rw [G31_41_formula]
  exact vasyuninBEntry_31_41_eval

def interval_31_41 : NamedVasyuninInterval :=
{
  h := 31
  k := 41
  lower := (3650543/119570000)
  upper := (3674457/119570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_41_interval
}

theorem G31_42_formula : baezDuarteGramEntry 31 42 = vasyuninBEntry 31 42 := vasyuninBEntry_correct_axiom 31 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_42_eval :
    ((((3984717/132830000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 42) ∧
    (vasyuninBEntry 31 42 ≤ (((4011283/132830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3142_formula_bound
  constructor <;> linarith

theorem G31_42_interval :
    ((((3984717/132830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 42) ∧
    (baezDuarteGramEntry 31 42 ≤ (((4011283/132830000) : ℚ) : ℝ)) := by
  rw [G31_42_formula]
  exact vasyuninBEntry_31_42_eval

def interval_31_42 : NamedVasyuninInterval :=
{
  h := 31
  k := 42
  lower := (3984717/132830000)
  upper := (4011283/132830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_42_interval
}

theorem G31_43_formula : baezDuarteGramEntry 31 43 = vasyuninBEntry 31 43 := vasyuninBEntry_correct_axiom 31 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_43_eval :
    ((((27187861/921390000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 43) ∧
    (vasyuninBEntry 31 43 ≤ (((27372139/921390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3143_formula_bound
  constructor <;> linarith

theorem G31_43_interval :
    ((((27187861/921390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 43) ∧
    (baezDuarteGramEntry 31 43 ≤ (((27372139/921390000) : ℚ) : ℝ)) := by
  rw [G31_43_formula]
  exact vasyuninBEntry_31_43_eval

def interval_31_43 : NamedVasyuninInterval :=
{
  h := 31
  k := 43
  lower := (27187861/921390000)
  upper := (27372139/921390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_43_interval
}

theorem G31_44_formula : baezDuarteGramEntry 31 44 = vasyuninBEntry 31 44 := vasyuninBEntry_correct_axiom 31 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_44_eval :
    ((((2822791/97090000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 44) ∧
    (vasyuninBEntry 31 44 ≤ (((2842209/97090000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3144_formula_bound
  constructor <;> linarith

theorem G31_44_interval :
    ((((2822791/97090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 44) ∧
    (baezDuarteGramEntry 31 44 ≤ (((2842209/97090000) : ℚ) : ℝ)) := by
  rw [G31_44_formula]
  exact vasyuninBEntry_31_44_eval

def interval_31_44 : NamedVasyuninInterval :=
{
  h := 31
  k := 44
  lower := (2822791/97090000)
  upper := (2842209/97090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_44_interval
}

theorem G31_45_formula : baezDuarteGramEntry 31 45 = vasyuninBEntry 31 45 := vasyuninBEntry_correct_axiom 31 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_45_eval :
    ((((4934803/171970000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 45) ∧
    (vasyuninBEntry 31 45 ≤ (((4969197/171970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3145_formula_bound
  constructor <;> linarith

theorem G31_45_interval :
    ((((4934803/171970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 45) ∧
    (baezDuarteGramEntry 31 45 ≤ (((4969197/171970000) : ℚ) : ℝ)) := by
  rw [G31_45_formula]
  exact vasyuninBEntry_31_45_eval

def interval_31_45 : NamedVasyuninInterval :=
{
  h := 31
  k := 45
  lower := (4934803/171970000)
  upper := (4969197/171970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_45_interval
}

theorem G31_46_formula : baezDuarteGramEntry 31 46 = vasyuninBEntry 31 46 := vasyuninBEntry_correct_axiom 31 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_46_eval :
    ((((7608217/267830000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 46) ∧
    (vasyuninBEntry 31 46 ≤ (((7661783/267830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3146_formula_bound
  constructor <;> linarith

theorem G31_46_interval :
    ((((7608217/267830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 46) ∧
    (baezDuarteGramEntry 31 46 ≤ (((7661783/267830000) : ℚ) : ℝ)) := by
  rw [G31_46_formula]
  exact vasyuninBEntry_31_46_eval

def interval_31_46 : NamedVasyuninInterval :=
{
  h := 31
  k := 46
  lower := (7608217/267830000)
  upper := (7661783/267830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_46_interval
}

theorem G31_47_formula : baezDuarteGramEntry 31 47 = vasyuninBEntry 31 47 := vasyuninBEntry_correct_axiom 31 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_47_eval :
    ((((27491899/981010000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 47) ∧
    (vasyuninBEntry 31 47 ≤ (((27688101/981010000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3147_formula_bound
  constructor <;> linarith

theorem G31_47_interval :
    ((((27491899/981010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 47) ∧
    (baezDuarteGramEntry 31 47 ≤ (((27688101/981010000) : ℚ) : ℝ)) := by
  rw [G31_47_formula]
  exact vasyuninBEntry_31_47_eval

def interval_31_47 : NamedVasyuninInterval :=
{
  h := 31
  k := 47
  lower := (27491899/981010000)
  upper := (27688101/981010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_47_interval
}

theorem G31_48_formula : baezDuarteGramEntry 31 48 = vasyuninBEntry 31 48 := vasyuninBEntry_correct_axiom 31 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_48_eval :
    ((((2310613/83870000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 48) ∧
    (vasyuninBEntry 31 48 ≤ (((2327387/83870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3148_formula_bound
  constructor <;> linarith

theorem G31_48_interval :
    ((((2310613/83870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 48) ∧
    (baezDuarteGramEntry 31 48 ≤ (((2327387/83870000) : ℚ) : ℝ)) := by
  rw [G31_48_formula]
  exact vasyuninBEntry_31_48_eval

def interval_31_48 : NamedVasyuninInterval :=
{
  h := 31
  k := 48
  lower := (2310613/83870000)
  upper := (2327387/83870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_48_interval
}

theorem G31_49_formula : baezDuarteGramEntry 31 49 = vasyuninBEntry 31 49 := vasyuninBEntry_correct_axiom 31 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_49_eval :
    ((((687967/25330000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 49) ∧
    (vasyuninBEntry 31 49 ≤ (((693033/25330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3149_formula_bound
  constructor <;> linarith

theorem G31_49_interval :
    ((((687967/25330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 49) ∧
    (baezDuarteGramEntry 31 49 ≤ (((693033/25330000) : ℚ) : ℝ)) := by
  rw [G31_49_formula]
  exact vasyuninBEntry_31_49_eval

def interval_31_49 : NamedVasyuninInterval :=
{
  h := 31
  k := 49
  lower := (687967/25330000)
  upper := (693033/25330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_49_interval
}

theorem G31_50_formula : baezDuarteGramEntry 31 50 = vasyuninBEntry 31 50 := vasyuninBEntry_correct_axiom 31 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_31_50_eval :
    ((((4762241/177590000) : ℚ) : ℝ) ≤ vasyuninBEntry 31 50) ∧
    (vasyuninBEntry 31 50 ≤ (((4797759/177590000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3150_formula_bound
  constructor <;> linarith

theorem G31_50_interval :
    ((((4762241/177590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 31 50) ∧
    (baezDuarteGramEntry 31 50 ≤ (((4797759/177590000) : ℚ) : ℝ)) := by
  rw [G31_50_formula]
  exact vasyuninBEntry_31_50_eval

def interval_31_50 : NamedVasyuninInterval :=
{
  h := 31
  k := 50
  lower := (4762241/177590000)
  upper := (4797759/177590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G31_50_interval
}

theorem G32_1_formula : baezDuarteGramEntry 32 1 = vasyuninBEntry 1 32 := by
  rw [baezDuarteGramEntry_symm 32 1]
  exact G1_32_formula

theorem G32_1_interval :
    ((((8855107/98930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 1) ∧
    (baezDuarteGramEntry 32 1 ≤ (((8874893/98930000) : ℚ) : ℝ)) := by
  rw [G32_1_formula]
  exact vasyuninBEntry_1_32_eval

def interval_32_1 : NamedVasyuninInterval :=
{
  h := 32
  k := 1
  lower := (8855107/98930000)
  upper := (8874893/98930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_1_interval
}

theorem G32_2_formula : baezDuarteGramEntry 32 2 = vasyuninBEntry 2 32 := by
  rw [baezDuarteGramEntry_symm 32 2]
  exact G2_32_formula

theorem G32_2_interval :
    ((((74884983/950170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 2) ∧
    (baezDuarteGramEntry 32 2 ≤ (((75075017/950170000) : ℚ) : ℝ)) := by
  rw [G32_2_formula]
  exact vasyuninBEntry_2_32_eval

def interval_32_2 : NamedVasyuninInterval :=
{
  h := 32
  k := 2
  lower := (74884983/950170000)
  upper := (75075017/950170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_2_interval
}

theorem G32_3_formula : baezDuarteGramEntry 32 3 = vasyuninBEntry 3 32 := by
  rw [baezDuarteGramEntry_symm 32 3]
  exact G3_32_formula

theorem G32_3_interval :
    ((((38546561/534390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 3) ∧
    (baezDuarteGramEntry 32 3 ≤ (((38653439/534390000) : ℚ) : ℝ)) := by
  rw [G32_3_formula]
  exact vasyuninBEntry_3_32_eval

def interval_32_3 : NamedVasyuninInterval :=
{
  h := 32
  k := 3
  lower := (38546561/534390000)
  upper := (38653439/534390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_3_interval
}

theorem G32_4_formula : baezDuarteGramEntry 32 4 = vasyuninBEntry 4 32 := by
  rw [baezDuarteGramEntry_symm 32 4]
  exact G4_32_formula

theorem G32_4_interval :
    ((((233369/3419375) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 4) ∧
    (baezDuarteGramEntry 32 4 ≤ (((1872423/27355000) : ℚ) : ℝ)) := by
  rw [G32_4_formula]
  exact vasyuninBEntry_4_32_eval

def interval_32_4 : NamedVasyuninInterval :=
{
  h := 32
  k := 4
  lower := (233369/3419375)
  upper := (1872423/27355000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_4_interval
}

theorem G32_5_formula : baezDuarteGramEntry 32 5 = vasyuninBEntry 5 32 := by
  rw [baezDuarteGramEntry_symm 32 5]
  exact G5_32_formula

theorem G32_5_interval :
    ((((10091747/157530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 5) ∧
    (baezDuarteGramEntry 32 5 ≤ (((10123253/157530000) : ℚ) : ℝ)) := by
  rw [G32_5_formula]
  exact vasyuninBEntry_5_32_eval

def interval_32_5 : NamedVasyuninInterval :=
{
  h := 32
  k := 5
  lower := (10091747/157530000)
  upper := (10123253/157530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_5_interval
}

theorem G32_6_formula : baezDuarteGramEntry 32 6 = vasyuninBEntry 6 32 := by
  rw [baezDuarteGramEntry_symm 32 6]
  exact G6_32_formula

theorem G32_6_interval :
    ((((9888853/161470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 6) ∧
    (baezDuarteGramEntry 32 6 ≤ (((9921147/161470000) : ℚ) : ℝ)) := by
  rw [G32_6_formula]
  exact vasyuninBEntry_6_32_eval

def interval_32_6 : NamedVasyuninInterval :=
{
  h := 32
  k := 6
  lower := (9888853/161470000)
  upper := (9921147/161470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_6_interval
}

theorem G32_7_formula : baezDuarteGramEntry 32 7 = vasyuninBEntry 7 32 := by
  rw [baezDuarteGramEntry_symm 32 7]
  exact G7_32_formula

theorem G32_7_interval :
    ((((4100517/69830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 7) ∧
    (baezDuarteGramEntry 32 7 ≤ (((4114483/69830000) : ℚ) : ℝ)) := by
  rw [G32_7_formula]
  exact vasyuninBEntry_7_32_eval

def interval_32_7 : NamedVasyuninInterval :=
{
  h := 32
  k := 7
  lower := (4100517/69830000)
  upper := (4114483/69830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_7_interval
}

theorem G32_8_formula : baezDuarteGramEntry 32 8 = vasyuninBEntry 8 32 := by
  rw [baezDuarteGramEntry_symm 32 8]
  exact G8_32_formula

theorem G32_8_interval :
    ((((18957287/327130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 8) ∧
    (baezDuarteGramEntry 32 8 ≤ (((19022713/327130000) : ℚ) : ℝ)) := by
  rw [G32_8_formula]
  exact vasyuninBEntry_8_32_eval

def interval_32_8 : NamedVasyuninInterval :=
{
  h := 32
  k := 8
  lower := (18957287/327130000)
  upper := (19022713/327130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_8_interval
}

theorem G32_9_formula : baezDuarteGramEntry 32 9 = vasyuninBEntry 9 32 := by
  rw [baezDuarteGramEntry_symm 32 9]
  exact G9_32_formula

theorem G32_9_interval :
    ((((10301179/188210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 9) ∧
    (baezDuarteGramEntry 32 9 ≤ (((10338821/188210000) : ℚ) : ℝ)) := by
  rw [G32_9_formula]
  exact vasyuninBEntry_9_32_eval

def interval_32_9 : NamedVasyuninInterval :=
{
  h := 32
  k := 9
  lower := (10301179/188210000)
  upper := (10338821/188210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_9_interval
}

theorem G32_10_formula : baezDuarteGramEntry 32 10 = vasyuninBEntry 10 32 := by
  rw [baezDuarteGramEntry_symm 32 10]
  exact G10_32_formula

theorem G32_10_interval :
    ((((15825353/296470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 10) ∧
    (baezDuarteGramEntry 32 10 ≤ (((15884647/296470000) : ℚ) : ℝ)) := by
  rw [G32_10_formula]
  exact vasyuninBEntry_10_32_eval

def interval_32_10 : NamedVasyuninInterval :=
{
  h := 32
  k := 10
  lower := (15825353/296470000)
  upper := (15884647/296470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_10_interval
}

theorem G32_11_formula : baezDuarteGramEntry 32 11 = vasyuninBEntry 11 32 := by
  rw [baezDuarteGramEntry_symm 32 11]
  exact G11_32_formula

theorem G32_11_interval :
    ((((23729591/454090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 11) ∧
    (baezDuarteGramEntry 32 11 ≤ (((23820409/454090000) : ℚ) : ℝ)) := by
  rw [G32_11_formula]
  exact vasyuninBEntry_11_32_eval

def interval_32_11 : NamedVasyuninInterval :=
{
  h := 32
  k := 11
  lower := (23729591/454090000)
  upper := (23820409/454090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_11_interval
}

theorem G32_12_formula : baezDuarteGramEntry 32 12 = vasyuninBEntry 12 32 := by
  rw [baezDuarteGramEntry_symm 32 12]
  exact G12_32_formula

theorem G32_12_interval :
    ((((48912587/974130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 12) ∧
    (baezDuarteGramEntry 32 12 ≤ (((49107413/974130000) : ℚ) : ℝ)) := by
  rw [G32_12_formula]
  exact vasyuninBEntry_12_32_eval

def interval_32_12 : NamedVasyuninInterval :=
{
  h := 32
  k := 12
  lower := (48912587/974130000)
  upper := (49107413/974130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_12_interval
}

theorem G32_13_formula : baezDuarteGramEntry 32 13 = vasyuninBEntry 13 32 := by
  rw [baezDuarteGramEntry_symm 32 13]
  exact G13_32_formula

theorem G32_13_interval :
    ((((18312553/374470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 13) ∧
    (baezDuarteGramEntry 32 13 ≤ (((18387447/374470000) : ℚ) : ℝ)) := by
  rw [G32_13_formula]
  exact vasyuninBEntry_13_32_eval

def interval_32_13 : NamedVasyuninInterval :=
{
  h := 32
  k := 13
  lower := (18312553/374470000)
  upper := (18387447/374470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_13_interval
}

theorem G32_14_formula : baezDuarteGramEntry 32 14 = vasyuninBEntry 14 32 := by
  rw [baezDuarteGramEntry_symm 32 14]
  exact G14_32_formula

theorem G32_14_interval :
    ((((522309/10910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 14) ∧
    (baezDuarteGramEntry 32 14 ≤ (((524491/10910000) : ℚ) : ℝ)) := by
  rw [G32_14_formula]
  exact vasyuninBEntry_14_32_eval

def interval_32_14 : NamedVasyuninInterval :=
{
  h := 32
  k := 14
  lower := (522309/10910000)
  upper := (524491/10910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_14_interval
}

theorem G32_15_formula : baezDuarteGramEntry 32 15 = vasyuninBEntry 15 32 := by
  rw [baezDuarteGramEntry_symm 32 15]
  exact G15_32_formula

theorem G32_15_interval :
    ((((9438081/199190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 15) ∧
    (baezDuarteGramEntry 32 15 ≤ (((9477919/199190000) : ℚ) : ℝ)) := by
  rw [G32_15_formula]
  exact vasyuninBEntry_15_32_eval

def interval_32_15 : NamedVasyuninInterval :=
{
  h := 32
  k := 15
  lower := (9438081/199190000)
  upper := (9477919/199190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_15_interval
}

theorem G32_16_formula : baezDuarteGramEntry 32 16 = vasyuninBEntry 16 32 := by
  rw [baezDuarteGramEntry_symm 32 16]
  exact G16_32_formula

theorem G32_16_interval :
    ((((3507717/72830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 16) ∧
    (baezDuarteGramEntry 32 16 ≤ (((3522283/72830000) : ℚ) : ℝ)) := by
  rw [G32_16_formula]
  exact vasyuninBEntry_16_32_eval

def interval_32_16 : NamedVasyuninInterval :=
{
  h := 32
  k := 16
  lower := (3507717/72830000)
  upper := (3522283/72830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_16_interval
}

theorem G32_17_formula : baezDuarteGramEntry 32 17 = vasyuninBEntry 17 32 := by
  rw [baezDuarteGramEntry_symm 32 17]
  exact G17_32_formula

theorem G32_17_interval :
    ((((12412621/273790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 17) ∧
    (baezDuarteGramEntry 32 17 ≤ (((12467379/273790000) : ℚ) : ℝ)) := by
  rw [G32_17_formula]
  exact vasyuninBEntry_17_32_eval

def interval_32_17 : NamedVasyuninInterval :=
{
  h := 32
  k := 17
  lower := (12412621/273790000)
  upper := (12467379/273790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_17_interval
}

theorem G32_18_formula : baezDuarteGramEntry 32 18 = vasyuninBEntry 18 32 := by
  rw [baezDuarteGramEntry_symm 32 18]
  exact G18_32_formula

theorem G32_18_interval :
    ((((6014277/137230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 18) ∧
    (baezDuarteGramEntry 32 18 ≤ (((6041723/137230000) : ℚ) : ℝ)) := by
  rw [G32_18_formula]
  exact vasyuninBEntry_18_32_eval

def interval_32_18 : NamedVasyuninInterval :=
{
  h := 32
  k := 18
  lower := (6014277/137230000)
  upper := (6041723/137230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_18_interval
}

theorem G32_19_formula : baezDuarteGramEntry 32 19 = vasyuninBEntry 19 32 := by
  rw [baezDuarteGramEntry_symm 32 19]
  exact G19_32_formula

theorem G32_19_interval :
    ((((327593/7663750) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 19) ∧
    (baezDuarteGramEntry 32 19 ≤ (((1316503/30655000) : ℚ) : ℝ)) := by
  rw [G32_19_formula]
  exact vasyuninBEntry_19_32_eval

def interval_32_19 : NamedVasyuninInterval :=
{
  h := 32
  k := 19
  lower := (327593/7663750)
  upper := (1316503/30655000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_19_interval
}

theorem G32_20_formula : baezDuarteGramEntry 32 20 = vasyuninBEntry 20 32 := by
  rw [baezDuarteGramEntry_symm 32 20]
  exact G20_32_formula

theorem G32_20_interval :
    ((((40383511/964890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 20) ∧
    (baezDuarteGramEntry 32 20 ≤ (((40576489/964890000) : ℚ) : ℝ)) := by
  rw [G32_20_formula]
  exact vasyuninBEntry_20_32_eval

def interval_32_20 : NamedVasyuninInterval :=
{
  h := 32
  k := 20
  lower := (40383511/964890000)
  upper := (40576489/964890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_20_interval
}

theorem G32_21_formula : baezDuarteGramEntry 32 21 = vasyuninBEntry 21 32 := by
  rw [baezDuarteGramEntry_symm 32 21]
  exact G21_32_formula

theorem G32_21_interval :
    ((((359129/8710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 21) ∧
    (baezDuarteGramEntry 32 21 ≤ (((360871/8710000) : ℚ) : ℝ)) := by
  rw [G32_21_formula]
  exact vasyuninBEntry_21_32_eval

def interval_32_21 : NamedVasyuninInterval :=
{
  h := 32
  k := 21
  lower := (359129/8710000)
  upper := (360871/8710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_21_interval
}

theorem G32_22_formula : baezDuarteGramEntry 32 22 = vasyuninBEntry 22 32 := by
  rw [baezDuarteGramEntry_symm 32 22]
  exact G22_32_formula

theorem G32_22_interval :
    ((((10763381/266190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 22) ∧
    (baezDuarteGramEntry 32 22 ≤ (((10816619/266190000) : ℚ) : ℝ)) := by
  rw [G32_22_formula]
  exact vasyuninBEntry_22_32_eval

def interval_32_22 : NamedVasyuninInterval :=
{
  h := 32
  k := 22
  lower := (10763381/266190000)
  upper := (10816619/266190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_22_interval
}

theorem G32_23_formula : baezDuarteGramEntry 32 23 = vasyuninBEntry 23 32 := by
  rw [baezDuarteGramEntry_symm 32 23]
  exact G23_32_formula

theorem G32_23_interval :
    ((((36966953/930470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 23) ∧
    (baezDuarteGramEntry 32 23 ≤ (((37153047/930470000) : ℚ) : ℝ)) := by
  rw [G32_23_formula]
  exact vasyuninBEntry_23_32_eval

def interval_32_23 : NamedVasyuninInterval :=
{
  h := 32
  k := 23
  lower := (36966953/930470000)
  upper := (37153047/930470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_23_interval
}

theorem G32_24_formula : baezDuarteGramEntry 32 24 = vasyuninBEntry 24 32 := by
  rw [baezDuarteGramEntry_symm 32 24]
  exact G24_32_formula

theorem G32_24_interval :
    ((((1575993/40070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 24) ∧
    (baezDuarteGramEntry 32 24 ≤ (((1584007/40070000) : ℚ) : ℝ)) := by
  rw [G32_24_formula]
  exact vasyuninBEntry_24_32_eval

def interval_32_24 : NamedVasyuninInterval :=
{
  h := 32
  k := 24
  lower := (1575993/40070000)
  upper := (1584007/40070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_24_interval
}

theorem G32_25_formula : baezDuarteGramEntry 32 25 = vasyuninBEntry 25 32 := by
  rw [baezDuarteGramEntry_symm 32 25]
  exact G25_32_formula

theorem G32_25_interval :
    ((((195199/5041250) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 25) ∧
    (baezDuarteGramEntry 32 25 ≤ (((784829/20165000) : ℚ) : ℝ)) := by
  rw [G32_25_formula]
  exact vasyuninBEntry_25_32_eval

def interval_32_25 : NamedVasyuninInterval :=
{
  h := 32
  k := 25
  lower := (195199/5041250)
  upper := (784829/20165000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_25_interval
}

theorem G32_26_formula : baezDuarteGramEntry 32 26 = vasyuninBEntry 26 32 := by
  rw [baezDuarteGramEntry_symm 32 26]
  exact G26_32_formula

theorem G32_26_interval :
    ((((2070601/53990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 26) ∧
    (baezDuarteGramEntry 32 26 ≤ (((2081399/53990000) : ℚ) : ℝ)) := by
  rw [G32_26_formula]
  exact vasyuninBEntry_26_32_eval

def interval_32_26 : NamedVasyuninInterval :=
{
  h := 32
  k := 26
  lower := (2070601/53990000)
  upper := (2081399/53990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_26_interval
}

theorem G32_27_formula : baezDuarteGramEntry 32 27 = vasyuninBEntry 27 32 := by
  rw [baezDuarteGramEntry_symm 32 27]
  exact G27_32_formula

theorem G32_27_interval :
    ((((7598041/199590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 27) ∧
    (baezDuarteGramEntry 32 27 ≤ (((7637959/199590000) : ℚ) : ℝ)) := by
  rw [G32_27_formula]
  exact vasyuninBEntry_27_32_eval

def interval_32_27 : NamedVasyuninInterval :=
{
  h := 32
  k := 27
  lower := (7598041/199590000)
  upper := (7637959/199590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_27_interval
}

theorem G32_28_formula : baezDuarteGramEntry 32 28 = vasyuninBEntry 28 32 := by
  rw [baezDuarteGramEntry_symm 32 28]
  exact G28_32_formula

theorem G32_28_interval :
    ((((3290071/86790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 28) ∧
    (baezDuarteGramEntry 32 28 ≤ (((3307429/86790000) : ℚ) : ℝ)) := by
  rw [G32_28_formula]
  exact vasyuninBEntry_28_32_eval

def interval_32_28 : NamedVasyuninInterval :=
{
  h := 32
  k := 28
  lower := (3290071/86790000)
  upper := (3307429/86790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_28_interval
}

theorem G32_29_formula : baezDuarteGramEntry 32 29 = vasyuninBEntry 29 32 := by
  rw [baezDuarteGramEntry_symm 32 29]
  exact G29_32_formula

theorem G32_29_interval :
    ((((1323503/34970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 29) ∧
    (baezDuarteGramEntry 32 29 ≤ (((1330497/34970000) : ℚ) : ℝ)) := by
  rw [G32_29_formula]
  exact vasyuninBEntry_29_32_eval

def interval_32_29 : NamedVasyuninInterval :=
{
  h := 32
  k := 29
  lower := (1323503/34970000)
  upper := (1330497/34970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_29_interval
}

theorem G32_30_formula : baezDuarteGramEntry 32 30 = vasyuninBEntry 30 32 := by
  rw [baezDuarteGramEntry_symm 32 30]
  exact G30_32_formula

theorem G32_30_interval :
    ((((3841879/101210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 30) ∧
    (baezDuarteGramEntry 32 30 ≤ (((3862121/101210000) : ℚ) : ℝ)) := by
  rw [G32_30_formula]
  exact vasyuninBEntry_30_32_eval

def interval_32_30 : NamedVasyuninInterval :=
{
  h := 32
  k := 30
  lower := (3841879/101210000)
  upper := (3862121/101210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_30_interval
}

theorem G32_31_formula : baezDuarteGramEntry 32 31 = vasyuninBEntry 31 32 := by
  rw [baezDuarteGramEntry_symm 32 31]
  exact G31_32_formula

theorem G32_31_interval :
    ((((3613567/94330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 31) ∧
    (baezDuarteGramEntry 32 31 ≤ (((3632433/94330000) : ℚ) : ℝ)) := by
  rw [G32_31_formula]
  exact vasyuninBEntry_31_32_eval

def interval_32_31 : NamedVasyuninInterval :=
{
  h := 32
  k := 31
  lower := (3613567/94330000)
  upper := (3632433/94330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_31_interval
}

theorem G32_32_formula_eq : baezDuarteGramEntry 32 32 = (1 / (32 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 32 := by norm_num
  rw [baez_duarte_diagonal_scaling 32 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G32_32_log_gamma_interval :
  ((((12393461/315390000) : ℚ) : ℝ) ≤ (1 / (32 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (32 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((12456539/315390000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 32 (by norm_num)
  constructor
  · have : ((((12393461/315390000) : ℚ) : ℝ) ≤ (1 / (32 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (32 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((12456539/315390000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G32_32_interval : ((((12393461/315390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 32) ∧ (baezDuarteGramEntry 32 32 ≤ (((12456539/315390000) : ℚ) : ℝ)) := by
  rw [G32_32_formula_eq]
  exact G32_32_log_gamma_interval

def interval_32_32 : NamedVasyuninInterval :=
{
  h := 32
  k := 32
  lower := (12393461/315390000)
  upper := (12456539/315390000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G32_32_interval
}

theorem G32_33_formula : baezDuarteGramEntry 32 33 = vasyuninBEntry 32 33 := vasyuninBEntry_correct_axiom 32 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_32_33_eval :
    ((((2568089/69110000) : ℚ) : ℝ) ≤ vasyuninBEntry 32 33) ∧
    (vasyuninBEntry 32 33 ≤ (((2581911/69110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3233_formula_bound
  constructor <;> linarith

theorem G32_33_interval :
    ((((2568089/69110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 33) ∧
    (baezDuarteGramEntry 32 33 ≤ (((2581911/69110000) : ℚ) : ℝ)) := by
  rw [G32_33_formula]
  exact vasyuninBEntry_32_33_eval

def interval_32_33 : NamedVasyuninInterval :=
{
  h := 32
  k := 33
  lower := (2568089/69110000)
  upper := (2581911/69110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_33_interval
}

theorem G32_34_formula : baezDuarteGramEntry 32 34 = vasyuninBEntry 32 34 := vasyuninBEntry_correct_axiom 32 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_32_34_eval :
    ((((18029561/504390000) : ℚ) : ℝ) ≤ vasyuninBEntry 32 34) ∧
    (vasyuninBEntry 32 34 ≤ (((18130439/504390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_16_17_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 16 17 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G32_34_interval :
    ((((18029561/504390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 34) ∧
    (baezDuarteGramEntry 32 34 ≤ (((18130439/504390000) : ℚ) : ℝ)) := by
  rw [G32_34_formula]
  exact vasyuninBEntry_32_34_eval

def interval_32_34 : NamedVasyuninInterval :=
{
  h := 32
  k := 34
  lower := (18029561/504390000)
  upper := (18130439/504390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_34_interval
}

theorem G32_35_formula : baezDuarteGramEntry 32 35 = vasyuninBEntry 32 35 := vasyuninBEntry_correct_axiom 32 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_32_35_eval :
    ((((1774871/51290000) : ℚ) : ℝ) ≤ vasyuninBEntry 32 35) ∧
    (vasyuninBEntry 32 35 ≤ (((1785129/51290000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3235_formula_bound
  constructor <;> linarith

theorem G32_35_interval :
    ((((1774871/51290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 35) ∧
    (baezDuarteGramEntry 32 35 ≤ (((1785129/51290000) : ℚ) : ℝ)) := by
  rw [G32_35_formula]
  exact vasyuninBEntry_32_35_eval

def interval_32_35 : NamedVasyuninInterval :=
{
  h := 32
  k := 35
  lower := (1774871/51290000)
  upper := (1785129/51290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_35_interval
}

theorem G32_36_formula : baezDuarteGramEntry 32 36 = vasyuninBEntry 32 36 := vasyuninBEntry_correct_axiom 32 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_32_36_eval :
    ((((6638271/197290000) : ℚ) : ℝ) ≤ vasyuninBEntry 32 36) ∧
    (vasyuninBEntry 32 36 ≤ (((6677729/197290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_8_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 8 9 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G32_36_interval :
    ((((6638271/197290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 36) ∧
    (baezDuarteGramEntry 32 36 ≤ (((6677729/197290000) : ℚ) : ℝ)) := by
  rw [G32_36_formula]
  exact vasyuninBEntry_32_36_eval

def interval_32_36 : NamedVasyuninInterval :=
{
  h := 32
  k := 36
  lower := (6638271/197290000)
  upper := (6677729/197290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_36_interval
}

theorem G32_37_formula : baezDuarteGramEntry 32 37 = vasyuninBEntry 32 37 := vasyuninBEntry_correct_axiom 32 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_32_37_eval :
    ((((15652277/477230000) : ℚ) : ℝ) ≤ vasyuninBEntry 32 37) ∧
    (vasyuninBEntry 32 37 ≤ (((15747723/477230000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3237_formula_bound
  constructor <;> linarith

theorem G32_37_interval :
    ((((15652277/477230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 37) ∧
    (baezDuarteGramEntry 32 37 ≤ (((15747723/477230000) : ℚ) : ℝ)) := by
  rw [G32_37_formula]
  exact vasyuninBEntry_32_37_eval

def interval_32_37 : NamedVasyuninInterval :=
{
  h := 32
  k := 37
  lower := (15652277/477230000)
  upper := (15747723/477230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_37_interval
}

theorem G32_38_formula : baezDuarteGramEntry 32 38 = vasyuninBEntry 32 38 := vasyuninBEntry_correct_axiom 32 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_32_38_eval :
    ((((16817533/524670000) : ℚ) : ℝ) ≤ vasyuninBEntry 32 38) ∧
    (vasyuninBEntry 32 38 ≤ (((16922467/524670000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_16_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 16 19 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G32_38_interval :
    ((((16817533/524670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 38) ∧
    (baezDuarteGramEntry 32 38 ≤ (((16922467/524670000) : ℚ) : ℝ)) := by
  rw [G32_38_formula]
  exact vasyuninBEntry_32_38_eval

def interval_32_38 : NamedVasyuninInterval :=
{
  h := 32
  k := 38
  lower := (16817533/524670000)
  upper := (16922467/524670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_38_interval
}

theorem G32_39_formula : baezDuarteGramEntry 32 39 = vasyuninBEntry 32 39 := vasyuninBEntry_correct_axiom 32 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_32_39_eval :
    ((((2265281/72190000) : ℚ) : ℝ) ≤ vasyuninBEntry 32 39) ∧
    (vasyuninBEntry 32 39 ≤ (((2279719/72190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3239_formula_bound
  constructor <;> linarith

theorem G32_39_interval :
    ((((2265281/72190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 39) ∧
    (baezDuarteGramEntry 32 39 ≤ (((2279719/72190000) : ℚ) : ℝ)) := by
  rw [G32_39_formula]
  exact vasyuninBEntry_32_39_eval

def interval_32_39 : NamedVasyuninInterval :=
{
  h := 32
  k := 39
  lower := (2265281/72190000)
  upper := (2279719/72190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_39_interval
}

theorem G32_40_formula : baezDuarteGramEntry 32 40 = vasyuninBEntry 32 40 := vasyuninBEntry_correct_axiom 32 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_32_40_eval :
    ((((14652461/475390000) : ℚ) : ℝ) ≤ vasyuninBEntry 32 40) ∧
    (vasyuninBEntry 32 40 ≤ (((14747539/475390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 5 8 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 8)
  constructor <;> linarith

theorem G32_40_interval :
    ((((14652461/475390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 40) ∧
    (baezDuarteGramEntry 32 40 ≤ (((14747539/475390000) : ℚ) : ℝ)) := by
  rw [G32_40_formula]
  exact vasyuninBEntry_32_40_eval

def interval_32_40 : NamedVasyuninInterval :=
{
  h := 32
  k := 40
  lower := (14652461/475390000)
  upper := (14747539/475390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_40_interval
}

theorem G32_41_formula : baezDuarteGramEntry 32 41 = vasyuninBEntry 32 41 := vasyuninBEntry_correct_axiom 32 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_32_41_eval :
    ((((3695267/122330000) : ℚ) : ℝ) ≤ vasyuninBEntry 32 41) ∧
    (vasyuninBEntry 32 41 ≤ (((3719733/122330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3241_formula_bound
  constructor <;> linarith

theorem G32_41_interval :
    ((((3695267/122330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 41) ∧
    (baezDuarteGramEntry 32 41 ≤ (((3719733/122330000) : ℚ) : ℝ)) := by
  rw [G32_41_formula]
  exact vasyuninBEntry_32_41_eval

def interval_32_41 : NamedVasyuninInterval :=
{
  h := 32
  k := 41
  lower := (3695267/122330000)
  upper := (3719733/122330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_41_interval
}

theorem G32_42_formula : baezDuarteGramEntry 32 42 = vasyuninBEntry 32 42 := vasyuninBEntry_correct_axiom 32 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_32_42_eval :
    ((((391339/13172500) : ℚ) : ℝ) ≤ vasyuninBEntry 32 42) ∧
    (vasyuninBEntry 32 42 ≤ (((787947/26345000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_16_21_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 16 21 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G32_42_interval :
    ((((391339/13172500) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 42) ∧
    (baezDuarteGramEntry 32 42 ≤ (((787947/26345000) : ℚ) : ℝ)) := by
  rw [G32_42_formula]
  exact vasyuninBEntry_32_42_eval

def interval_32_42 : NamedVasyuninInterval :=
{
  h := 32
  k := 42
  lower := (391339/13172500)
  upper := (787947/26345000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_42_interval
}

theorem G32_43_formula : baezDuarteGramEntry 32 43 = vasyuninBEntry 32 43 := vasyuninBEntry_correct_axiom 32 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_32_43_eval :
    ((((12183347/416530000) : ℚ) : ℝ) ≤ vasyuninBEntry 32 43) ∧
    (vasyuninBEntry 32 43 ≤ (((12266653/416530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3243_formula_bound
  constructor <;> linarith

theorem G32_43_interval :
    ((((12183347/416530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 43) ∧
    (baezDuarteGramEntry 32 43 ≤ (((12266653/416530000) : ℚ) : ℝ)) := by
  rw [G32_43_formula]
  exact vasyuninBEntry_32_43_eval

def interval_32_43 : NamedVasyuninInterval :=
{
  h := 32
  k := 43
  lower := (12183347/416530000)
  upper := (12266653/416530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_43_interval
}

theorem G32_44_formula : baezDuarteGramEntry 32 44 = vasyuninBEntry 32 44 := vasyuninBEntry_correct_axiom 32 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_32_44_eval :
    ((((1903381/66190000) : ℚ) : ℝ) ≤ vasyuninBEntry 32 44) ∧
    (vasyuninBEntry 32 44 ≤ (((1916619/66190000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_8_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 8 11 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G32_44_interval :
    ((((1903381/66190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 44) ∧
    (baezDuarteGramEntry 32 44 ≤ (((1916619/66190000) : ℚ) : ℝ)) := by
  rw [G32_44_formula]
  exact vasyuninBEntry_32_44_eval

def interval_32_44 : NamedVasyuninInterval :=
{
  h := 32
  k := 44
  lower := (1903381/66190000)
  upper := (1916619/66190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_44_interval
}

theorem G32_45_formula : baezDuarteGramEntry 32 45 = vasyuninBEntry 32 45 := vasyuninBEntry_correct_axiom 32 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_32_45_eval :
    ((((4372567/154330000) : ℚ) : ℝ) ≤ vasyuninBEntry 32 45) ∧
    (vasyuninBEntry 32 45 ≤ (((4403433/154330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3245_formula_bound
  constructor <;> linarith

theorem G32_45_interval :
    ((((4372567/154330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 45) ∧
    (baezDuarteGramEntry 32 45 ≤ (((4403433/154330000) : ℚ) : ℝ)) := by
  rw [G32_45_formula]
  exact vasyuninBEntry_32_45_eval

def interval_32_45 : NamedVasyuninInterval :=
{
  h := 32
  k := 45
  lower := (4372567/154330000)
  upper := (4403433/154330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_45_interval
}

theorem G32_46_formula : baezDuarteGramEntry 32 46 = vasyuninBEntry 32 46 := vasyuninBEntry_correct_axiom 32 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_32_46_eval :
    ((((5154059/184410000) : ℚ) : ℝ) ≤ vasyuninBEntry 32 46) ∧
    (vasyuninBEntry 32 46 ≤ (((5190941/184410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_16_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 16 23 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G32_46_interval :
    ((((5154059/184410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 32 46) ∧
    (baezDuarteGramEntry 32 46 ≤ (((5190941/184410000) : ℚ) : ℝ)) := by
  rw [G32_46_formula]
  exact vasyuninBEntry_32_46_eval

def interval_32_46 : NamedVasyuninInterval :=
{
  h := 32
  k := 46
  lower := (5154059/184410000)
  upper := (5190941/184410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G32_46_interval
}

end RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
