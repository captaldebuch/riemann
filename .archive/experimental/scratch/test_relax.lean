import Mathlib
import RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBoundsGenerated

theorem vasyuninBEntry_12_formula_bound_test :
    (((3861 / 5000 : ℚ) : ℝ) ≤ RH.Criteria.NymanBeurling.VasyuninGram.vasyuninBEntryFormula 1 2) ∧
    (RH.Criteria.NymanBeurling.VasyuninGram.vasyuninBEntryFormula 1 2 ≤ ((7723 / 10000 : ℚ) : ℝ)) := by
  have h := RH.Certificates.Generated.vasyuninBEntry_12_formula_bound
  constructor
  · have h1 := h.1; linarith
  · have h2 := h.2; linarith
