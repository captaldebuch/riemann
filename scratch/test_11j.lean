import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open RH.Criteria.NymanBeurling.CutoffMobiusKernels

namespace RH.Criteria.NymanBeurling.CutoffMobiusKernels

noncomputable def explicitQuadraticTotalComponent (N : ℕ) : ℝ :=
  explicitQuadraticLogGammaComponent N
    + explicitQuadraticLogRatioComponent N
    + explicitQuadraticCotangentComponent N
    + explicitCutoffResidueComponent N

noncomputable def explicitLinearCenteredRemainder (N : ℕ) : ℝ :=
  explicitLinearLogComponent N + 2

noncomputable def explicitQuadraticCenteredRemainder (N : ℕ) : ℝ :=
  explicitQuadraticTotalComponent N - 1

noncomputable def explicitTotalCenteredRemainder (N : ℕ) : ℝ :=
  explicitLinearCenteredRemainder N
    + explicitQuadraticCenteredRemainder N

theorem explicitCutoffMobiusComponentSum_eq_centered_remainders
    (N : ℕ) :
    explicitCutoffMobiusComponentSum N =
      explicitTotalCenteredRemainder N := by
  unfold explicitCutoffMobiusComponentSum
  unfold explicitTotalCenteredRemainder
  unfold explicitLinearCenteredRemainder
  unfold explicitQuadraticCenteredRemainder
  unfold explicitQuadraticTotalComponent
  ring

structure CenteredCutoffMobiusSplitEstimates where
  C_linear : ℝ
  C_quadratic : ℝ
  C_pos : 0 < C_linear + C_quadratic
  linear_bound :
    ∀ N : ℕ,
      |explicitLinearCenteredRemainder N|
        ≤ C_linear / Real.log (N + 2 : ℝ)
  quadratic_bound :
    ∀ N : ℕ,
      |explicitQuadraticCenteredRemainder N|
        ≤ C_quadratic / Real.log (N + 2 : ℝ)

def explicit_component_estimate_of_centered_split_estimates
    (H : CenteredCutoffMobiusSplitEstimates) :
    ExplicitCutoffMobiusComponentEstimates := by
  refine ⟨H.C_linear + H.C_quadratic, H.C_pos, ?_⟩
  intro N
  rw [explicitCutoffMobiusComponentSum_eq_centered_remainders]
  unfold explicitTotalCenteredRemainder
  have hlin := H.linear_bound N
  have hquad := H.quadratic_bound N
  have h1 : explicitLinearCenteredRemainder N ≤ H.C_linear / Real.log (N + 2 : ℝ) :=
    le_trans (le_abs_self _) hlin
  have h2 : explicitQuadraticCenteredRemainder N ≤ H.C_quadratic / Real.log (N + 2 : ℝ) :=
    le_trans (le_abs_self _) hquad
  have h3 : explicitLinearCenteredRemainder N + explicitQuadraticCenteredRemainder N ≤ H.C_linear / Real.log (N + 2 : ℝ) + H.C_quadratic / Real.log (N + 2 : ℝ) := add_le_add h1 h2
  have h4 : H.C_linear / Real.log (N + 2 : ℝ) + H.C_quadratic / Real.log (N + 2 : ℝ) = (H.C_linear + H.C_quadratic) / Real.log (N + 2 : ℝ) := by ring
  rwa [h4] at h3

structure CenteredCutoffMobiusGlobalEstimate where
  C : ℝ
  C_pos : 0 < C
  centered_bound :
    ∀ N : ℕ,
      explicitTotalCenteredRemainder N
        ≤ C / Real.log (N + 2 : ℝ)

def explicit_component_estimate_of_centered_global_estimate
    (H : CenteredCutoffMobiusGlobalEstimate) :
    ExplicitCutoffMobiusComponentEstimates := by
  refine ⟨H.C, H.C_pos, ?_⟩
  intro N
  rw [explicitCutoffMobiusComponentSum_eq_centered_remainders]
  exact H.centered_bound N

noncomputable def explicitQuadraticLogCotangentInteraction (N : ℕ) : ℝ :=
  explicitQuadraticLogRatioComponent N
    + explicitQuadraticCotangentComponent N

noncomputable def explicitQuadraticInteractionRemainder (N : ℕ) : ℝ :=
  explicitQuadraticLogCotangentInteraction N - 1

end RH.Criteria.NymanBeurling.CutoffMobiusKernels
