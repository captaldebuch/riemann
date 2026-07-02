import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels
import Mathlib.Tactic.Ring

open RH.Criteria.NymanBeurling.CutoffMobiusKernels

namespace RH.Criteria.NymanBeurling.CutoffMobiusKernels

noncomputable def explicitLinearMobiusSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (1 - (k : ℝ) / ((N + 1 : ℕ) : ℝ)) *
      ((Real.log (k : ℝ) + 1 - Real.eulerMascheroniConstant) / (k : ℝ))

theorem explicitLinearCenteredRemainder_eq_sum (N : ℕ) :
    explicitLinearCenteredRemainder N =
      2 * (explicitLinearMobiusSum N + 1) := by
  unfold explicitLinearCenteredRemainder explicitLinearLogComponent explicitLinearMobiusSum
  unfold cutoffMobiusCoeff cutoffWeight explicitChiRhoKernel
  have h1 : (∑ k ∈ Finset.Icc 1 N,
      -((ArithmeticFunction.moebius k : ℤ) : ℝ) * (1 - (k : ℝ) / ((N + 1 : ℕ) : ℝ)) *
        ((Real.log (k : ℝ) + 1 - Real.eulerMascheroniConstant) / (k : ℝ))) =
    - ∑ k ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (1 - (k : ℝ) / ((N + 1 : ℕ) : ℝ)) *
        ((Real.log (k : ℝ) + 1 - Real.eulerMascheroniConstant) / (k : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [h1]
  ring

end RH.Criteria.NymanBeurling.CutoffMobiusKernels
