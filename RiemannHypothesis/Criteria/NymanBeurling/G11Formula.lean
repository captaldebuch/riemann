import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula
import RiemannHypothesis.Criteria.NymanBeurling.G11IntegralEvaluation
import RiemannHypothesis.Certificates.TranscendentalBounds

namespace RH.Criteria.NymanBeurling.VasyuninGram

open scoped MeasureTheory
open RH.Certificates.TranscendentalBounds

theorem G11_equals_integral_axiom :
  baezDuarteGramEntry 1 1 = G11Integral := by
  unfold baezDuarteGramEntry G11Integral
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x _hx
  unfold G11OriginalIntegrand
  simp only [Nat.cast_one, one_mul]
  ring

theorem G11_formula_theorem :
  baezDuarteGramEntry 1 1 = Real.log (2 * Real.pi) - EulerGamma := by
  rw [G11_equals_integral_axiom, G11_integral_eval_theorem]

theorem G11_log_gamma_interval_theorem :
  (((6303 / 5000 : ℚ) : ℝ)
     ≤ Real.log (2 * Real.pi) - EulerGamma) ∧
  (Real.log (2 * Real.pi) - EulerGamma
     ≤ ((12607 / 10000 : ℚ) : ℝ)) := by
  have h_log := log_two_pi_interval_theorem
  have h_gamma : ((57721 / 100000 : ℚ) : ℝ) ≤ EulerGamma ∧ EulerGamma ≤ ((57722 / 100000 : ℚ) : ℝ) := euler_gamma_interval_theorem
  constructor
  · linarith [h_log.1, h_gamma.2]
  · linarith [h_log.2, h_gamma.1]

theorem G11_interval_axiom :
  (((6303 / 5000 : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 1) ∧
  (baezDuarteGramEntry 1 1 ≤ ((12607 / 10000 : ℚ) : ℝ)) := by
  rw [G11_formula_theorem]
  exact G11_log_gamma_interval_theorem

/-- The Vasyunin explicit formula at `h = k = 1` reduces to `log(2π) - γ`: the cotangent
    sum `cotangentSumVFormula 1 1` is an empty sum (`Finset.Ico 1 1 = ∅`), and the middle
    `(k - h)/(2hk) * log(h/k)` term vanishes since `k - h = 0`. -/
theorem vasyuninBEntryFormula_one_one :
    vasyuninBEntryFormula 1 1 = Real.log (2 * Real.pi) - Real.eulerMascheroniConstant := by
  unfold vasyuninBEntryFormula cotangentSumVFormula
  norm_num

/-- Base case (`h = k = 1`) of the diagonal bridge field `vasyuninBEntry_diagonal`.

    IMPORTANT SCOPE NOTE: this is *not* a proof of the general structure field
    `vasyuninBEntry_diagonal : ∀ h : ℕ, baezDuarteGramEntry h h = vasyuninBEntry h h`,
    which is a universal statement over all `h`. This lemma only establishes the `h = 1`
    instance, by combining the already-proved `G11_formula_theorem` (that
    `baezDuarteGramEntry 1 1 = Real.log (2 * Real.pi) - EulerGamma`, where `EulerGamma` is
    Mathlib's `Real.eulerMascheroniConstant` under a local alias, defeq/`rfl`-equal) with the
    formula reduction `vasyuninBEntryFormula_one_one` above. The fully general diagonal case
    (arbitrary `h`) requires genuinely new integral-evaluation work generalizing
    `G11IntegralEvaluation.lean` beyond `h = k = 1`, and is intentionally out of scope here. -/
theorem vasyuninBEntry_diagonal_one :
    baezDuarteGramEntry 1 1 = vasyuninBEntry 1 1 := by
  rw [G11_formula_theorem, vasyuninBEntry_eq_formula, vasyuninBEntryFormula_one_one]
  rfl

end RH.Criteria.NymanBeurling.VasyuninGram
