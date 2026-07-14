import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open RH.Criteria.NymanBeurling.CutoffMobiusKernels

namespace RH.Criteria.NymanBeurling.CutoffMobiusKernels

noncomputable def cutoffMobiusOverKSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius k : ℤ) : ℝ)
      * (1 - (k : ℝ) / ((N + 1 : ℕ) : ℝ))
      / (k : ℝ)

noncomputable def cutoffMobiusLogOverKSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius k : ℤ) : ℝ)
      * (1 - (k : ℝ) / ((N + 1 : ℕ) : ℝ))
      * Real.log (k : ℝ)
      / (k : ℝ)

theorem explicitLinearMobiusSum_eq_dirichlet_pieces
    (N : ℕ) :
    explicitLinearMobiusSum N =
      cutoffMobiusLogOverKSum N
        + (1 - Real.eulerMascheroniConstant)
            * cutoffMobiusOverKSum N := by
  unfold explicitLinearMobiusSum cutoffMobiusLogOverKSum cutoffMobiusOverKSum
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

structure LinearMobiusDirichletEstimates where
  C_log : ℝ
  C_overK : ℝ
  C_pos : 0 < C_log + |1 - Real.eulerMascheroniConstant| * C_overK
  log_bound :
    ∀ N : ℕ,
      |cutoffMobiusLogOverKSum N + 1|
        ≤ C_log / Real.log (N + 2 : ℝ)
  overK_bound :
    ∀ N : ℕ,
      |cutoffMobiusOverKSum N|
        ≤ C_overK / Real.log (N + 2 : ℝ)

noncomputable def linear_mobius_centered_estimate_of_dirichlet_estimates
    (H : LinearMobiusDirichletEstimates) :
    LinearMobiusCenteredEstimate := by
  refine ⟨H.C_log + |1 - Real.eulerMascheroniConstant| * H.C_overK, H.C_pos, ?_⟩
  intro N
  rw [explicitLinearMobiusSum_eq_dirichlet_pieces]
  have hlog := H.log_bound N
  have hk := H.overK_bound N
  have h1 : |cutoffMobiusLogOverKSum N + (1 - Real.eulerMascheroniConstant) * cutoffMobiusOverKSum N + 1| =
            |cutoffMobiusLogOverKSum N + 1 + (1 - Real.eulerMascheroniConstant) * cutoffMobiusOverKSum N| := by
    congr 1; ring
  rw [h1]
  have h2 := abs_add_le (cutoffMobiusLogOverKSum N + 1) ((1 - Real.eulerMascheroniConstant) * cutoffMobiusOverKSum N)
  have h3 : |(1 - Real.eulerMascheroniConstant) * cutoffMobiusOverKSum N| = |1 - Real.eulerMascheroniConstant| * |cutoffMobiusOverKSum N| := abs_mul _ _
  rw [h3] at h2
  have h4 : |1 - Real.eulerMascheroniConstant| * |cutoffMobiusOverKSum N| ≤ |1 - Real.eulerMascheroniConstant| * (H.C_overK / Real.log (N + 2 : ℝ)) := mul_le_mul_of_nonneg_left hk (abs_nonneg _)
  have h5 : |cutoffMobiusLogOverKSum N + 1| + |1 - Real.eulerMascheroniConstant| * |cutoffMobiusOverKSum N| ≤ H.C_log / Real.log (N + 2 : ℝ) + |1 - Real.eulerMascheroniConstant| * (H.C_overK / Real.log (N + 2 : ℝ)) := add_le_add hlog h4
  have h6 : H.C_log / Real.log (N + 2 : ℝ) + |1 - Real.eulerMascheroniConstant| * (H.C_overK / Real.log (N + 2 : ℝ)) = (H.C_log + |1 - Real.eulerMascheroniConstant| * H.C_overK) / Real.log (N + 2 : ℝ) := by ring
  linarith

end RH.Criteria.NymanBeurling.CutoffMobiusKernels
