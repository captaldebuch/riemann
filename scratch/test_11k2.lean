import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open RH.Criteria.NymanBeurling.CutoffMobiusKernels

namespace RH.Criteria.NymanBeurling.CutoffMobiusKernels

theorem explicitQuadraticCenteredRemainder_eq_interaction_parts
    (N : ℕ) :
    explicitQuadraticCenteredRemainder N =
      explicitQuadraticLogGammaComponent N
        + explicitQuadraticInteractionRemainder N
        + explicitCutoffResidueComponent N := by
  unfold explicitQuadraticCenteredRemainder
  unfold explicitQuadraticTotalComponent
  unfold explicitQuadraticInteractionRemainder
  unfold explicitQuadraticLogCotangentInteraction
  ring

structure QuadraticInteractionEstimates where
  C_loggamma : ℝ
  C_interaction : ℝ
  C_residue : ℝ

  C_pos :
    0 < C_loggamma + C_interaction + C_residue

  loggamma_bound :
    ∀ N : ℕ,
      |explicitQuadraticLogGammaComponent N|
        ≤ C_loggamma / Real.log (N + 2 : ℝ)

  interaction_bound :
    ∀ N : ℕ,
      |explicitQuadraticInteractionRemainder N|
        ≤ C_interaction / Real.log (N + 2 : ℝ)

  residue_bound :
    ∀ N : ℕ,
      |explicitCutoffResidueComponent N|
        ≤ C_residue / Real.log (N + 2 : ℝ)

noncomputable def quadratic_centered_estimate_of_interaction_estimates
    (H : QuadraticInteractionEstimates) :
    ∃ C > 0,
      ∀ N : ℕ,
        |explicitQuadraticCenteredRemainder N|
          ≤ C / Real.log (N + 2 : ℝ) := by
  use H.C_loggamma + H.C_interaction + H.C_residue
  constructor
  · exact H.C_pos
  · intro N
    rw [explicitQuadraticCenteredRemainder_eq_interaction_parts]
    have h1 : |explicitQuadraticLogGammaComponent N + explicitQuadraticInteractionRemainder N + explicitCutoffResidueComponent N|
              = |explicitQuadraticLogGammaComponent N + (explicitQuadraticInteractionRemainder N + explicitCutoffResidueComponent N)| := by
      congr 1; ring
    rw [h1]
    have h2 := abs_add_le (explicitQuadraticLogGammaComponent N + explicitQuadraticInteractionRemainder N) (explicitCutoffResidueComponent N)
    have h3 := abs_add_le (explicitQuadraticLogGammaComponent N) (explicitQuadraticInteractionRemainder N)
    have hlG := H.loggamma_bound N
    have hint := H.interaction_bound N
    have hres := H.residue_bound N
    calc
      |explicitQuadraticLogGammaComponent N + (explicitQuadraticInteractionRemainder N + explicitCutoffResidueComponent N)|
        ≤ |explicitQuadraticLogGammaComponent N| + |explicitQuadraticInteractionRemainder N + explicitCutoffResidueComponent N| := abs_add_le _ _
      _ ≤ |explicitQuadraticLogGammaComponent N| + (|explicitQuadraticInteractionRemainder N| + |explicitCutoffResidueComponent N|) := add_le_add (le_refl _) (abs_add_le _ _)
      _ = |explicitQuadraticLogGammaComponent N| + |explicitQuadraticInteractionRemainder N| + |explicitCutoffResidueComponent N| := by ring
      _ ≤ (H.C_loggamma / Real.log (N + 2 : ℝ)) + (H.C_interaction / Real.log (N + 2 : ℝ)) + (H.C_residue / Real.log (N + 2 : ℝ)) := add_le_add (add_le_add hlG hint) hres
      _ = (H.C_loggamma + H.C_interaction + H.C_residue) / Real.log (N + 2 : ℝ) := by ring

noncomputable def centered_split_estimates_of_linear_and_quadratic
    (HL : LinearMobiusCenteredEstimate)
    (HQ : QuadraticInteractionEstimates) :
    CenteredCutoffMobiusSplitEstimates := by
  refine ⟨2 * HL.C, HQ.C_loggamma + HQ.C_interaction + HQ.C_residue, ?_, ?_, ?_⟩
  · have h1 := HL.C_pos
    have h2 := HQ.C_pos
    linarith
  · intro N
    rw [explicitLinearCenteredRemainder_eq_sum]
    have h := HL.bound N
    rw [abs_mul, abs_two]
    calc
      2 * |explicitLinearMobiusSum N + 1| ≤ 2 * (HL.C / Real.log (N + 2 : ℝ)) := by linarith
      _ = (2 * HL.C) / Real.log (N + 2 : ℝ) := by ring
  · intro N
    rw [explicitQuadraticCenteredRemainder_eq_interaction_parts]
    have h1 : |explicitQuadraticLogGammaComponent N + explicitQuadraticInteractionRemainder N + explicitCutoffResidueComponent N|
              = |explicitQuadraticLogGammaComponent N + (explicitQuadraticInteractionRemainder N + explicitCutoffResidueComponent N)| := by
      congr 1; ring
    rw [h1]
    have h2 := abs_add_le (explicitQuadraticLogGammaComponent N + explicitQuadraticInteractionRemainder N) (explicitCutoffResidueComponent N)
    have h3 := abs_add_le (explicitQuadraticLogGammaComponent N) (explicitQuadraticInteractionRemainder N)
    have hlG := HQ.loggamma_bound N
    have hint := HQ.interaction_bound N
    have hres := HQ.residue_bound N
    calc
      |explicitQuadraticLogGammaComponent N + (explicitQuadraticInteractionRemainder N + explicitCutoffResidueComponent N)|
        ≤ |explicitQuadraticLogGammaComponent N| + |explicitQuadraticInteractionRemainder N + explicitCutoffResidueComponent N| := abs_add_le _ _
      _ ≤ |explicitQuadraticLogGammaComponent N| + (|explicitQuadraticInteractionRemainder N| + |explicitCutoffResidueComponent N|) := add_le_add (le_refl _) (abs_add_le _ _)
      _ = |explicitQuadraticLogGammaComponent N| + |explicitQuadraticInteractionRemainder N| + |explicitCutoffResidueComponent N| := by ring
      _ ≤ (HQ.C_loggamma / Real.log (N + 2 : ℝ)) + (HQ.C_interaction / Real.log (N + 2 : ℝ)) + (HQ.C_residue / Real.log (N + 2 : ℝ)) := add_le_add (add_le_add hlG hint) hres
      _ = (HQ.C_loggamma + HQ.C_interaction + HQ.C_residue) / Real.log (N + 2 : ℝ) := by ring

end RH.Criteria.NymanBeurling.CutoffMobiusKernels
