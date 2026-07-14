import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

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

structure LinearMobiusCenteredEstimate where
  C : ℝ
  C_pos : 0 < C
  bound :
    ∀ N : ℕ,
      |explicitLinearMobiusSum N + 1|
        ≤ C / Real.log (N + 2 : ℝ)

def linear_centered_remainder_bound_of_mobius_estimate
    (H : LinearMobiusCenteredEstimate) :
    ∃ C > 0, ∀ N, |explicitLinearCenteredRemainder N| ≤ C / Real.log (N + 2 : ℝ) := by
  use 2 * H.C
  constructor
  · linarith [H.C_pos]
  · intro N
    rw [explicitLinearCenteredRemainder_eq_sum]
    have h := H.bound N
    rw [abs_mul, abs_two]
    calc
      2 * |explicitLinearMobiusSum N + 1| ≤ 2 * (H.C / Real.log (N + 2 : ℝ)) := by linarith
      _ = (2 * H.C) / Real.log (N + 2 : ℝ) := by ring

end RH.Criteria.NymanBeurling.CutoffMobiusKernels
