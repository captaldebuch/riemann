import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram

namespace RH.Criteria.NymanBeurling.VasyuninGram

/-- Individual cotangent term cot(πa/k). -/
noncomputable def cotangentTermV (a k : ℕ) : ℝ :=
  Real.cos (Real.pi * (a : ℝ) / (k : ℝ)) /
  Real.sin (Real.pi * (a : ℝ) / (k : ℝ))

/-- Cotangent sum: V(h, k) = Σ_{a=1}^{k-1} {ah/k} · cot(πa/k).
    Uses Finset.Ico 1 k so the index a ranges over {1, ..., k-1}. -/
noncomputable def cotangentSumVFormula (h k : ℕ) : ℝ :=
  ∑ a ∈ Finset.Ico 1 k,
    Int.fract (((a * h : ℕ) : ℝ) / (k : ℝ)) * cotangentTermV a k

/-- Vasyunin formula: b_{h,k} = (log(2π) − γ)/2 · (1/h + 1/k)
    + (k − h)/(2hk) · log(h/k) − π/(2hk) · (V(h,k) + V(k,h)). -/
noncomputable def vasyuninBEntryFormula (h k : ℕ) : ℝ :=
  (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 * (1 / (h : ℝ) + 1 / (k : ℝ)) +
  ((k : ℝ) - (h : ℝ)) / (2 * (h : ℝ) * (k : ℝ)) * Real.log ((h : ℝ) / (k : ℝ)) -
  Real.pi / (2 * (h : ℝ) * (k : ℝ)) *
    (cotangentSumVFormula h k + cotangentSumVFormula k h)

noncomputable def cotangentSumV (h k : ℕ) : ℝ :=
  cotangentSumVFormula h k

noncomputable def vasyuninBEntry (h k : ℕ) : ℝ :=
  vasyuninBEntryFormula h k

theorem vasyuninBEntry_eq_formula (h k : ℕ) :
    vasyuninBEntry h k = vasyuninBEntryFormula h k := rfl

/-- Unconditional symmetry of the Vasyunin explicit formula:
    `vasyuninBEntry h k = vasyuninBEntry k h` for *all* natural numbers `h k`,
    including `h = 0` or `k = 0`.

    The proof does not need to case-split on zero at all: the key fact
    `Real.log (h/k) = -Real.log (k/h)` holds unconditionally in Lean/Mathlib because
    `(h/k)⁻¹ = k/h` (`inv_div`) and `Real.log x⁻¹ = -Real.log x` (`Real.log_inv`) both hold
    unconditionally thanks to the junk-value conventions `x/0 = 0`, `0⁻¹ = 0`, `Real.log 0 = 0`.
    Once that identity is in hand, the remaining terms of `vasyuninBEntryFormula` are visibly
    symmetric under `h ↔ k` (the `1/h + 1/k` term by `add_comm`, the cotangent term by
    `add_comm` and `mul_comm`), so `ring` closes the goal after rewriting. -/
theorem vasyuninBEntry_symm_proof (h k : ℕ) :
    vasyuninBEntry h k = vasyuninBEntry k h := by
  unfold vasyuninBEntry vasyuninBEntryFormula
  have hlog : Real.log ((h : ℝ) / (k : ℝ)) = - Real.log ((k : ℝ) / (h : ℝ)) := by
    rw [show (h : ℝ) / (k : ℝ) = ((k : ℝ) / (h : ℝ))⁻¹ from (inv_div _ _).symm, Real.log_inv]
  rw [hlog]
  ring

end RH.Criteria.NymanBeurling.VasyuninGram
