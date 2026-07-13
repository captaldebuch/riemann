import RiemannHypothesis.Criteria.NymanBeurling.QuadraticInteraction
import RiemannHypothesis.Criteria.NymanBeurling.H15StructuredCorrelationEstimate
import RiemannHypothesis.Criteria.NymanBeurling.RHBridge

/-!
# Final conditional assembly

This module records the exact endgame wiring without asserting either of the
remaining analytic inputs.  A classical Mertens decay package supplies the
linear estimates, while the centered Bernoulli correlation package supplies
the quadratic estimates.  The Vasyunin local bridge is constructed from the
proved H13 period-reduction chain.  A forward Nyman--Beurling implication then
yields RH.  The correlation package and the forward implication remain
explicit hypotheses, so this theorem does not hide an analytic debt.
-/

namespace RH.Criteria.NymanBeurling.FinalAssembly

open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open RH.Criteria.NymanBeurling.MobiusSummatory
open RH.Criteria.NymanBeurling.RHBridge
open RH.Criteria.NymanBeurling.QuadraticInteraction
open RH.Criteria.NymanBeurling.VasyuninGram

/-- The local Vasyunin bridge is now an explicit inhabitant of the corrected
H13 debt structure.  The only nonstandard dependency in this constructor is
the already-documented inverse-substitution bridge used by the diagonal and
tail-integral proofs; no cotangent-recognition `sorryAx` is introduced here. -/
noncomputable def vasyuninBridgeLocalDebts_of_proved_chain :
    VasyuninBridgeLocalDebts :=
  { vasyuninBEntry_symm := vasyuninBEntry_symm_proof
    vasyuninBEntry_diagonal := vasyuninBEntry_diagonal_proof
    interval_sum_add_tail_eq_cotangent_formula := by
      intro h k hne hh hk
      exact interval_sum_add_tail_eq_cotangent_formula_unconditional h k hne hh hk }

/--
The final conditional RH wiring.  The first hypothesis is the single H14
decay input, the second is the centered H15 Bernoulli-correlation estimate,
and the third is the forward Nyman--Beurling implication.  The local
Vasyunin bridge is supplied by `vasyuninBridgeLocalDebts_of_proved_chain`;
no converse Nyman--Beurling implication is used.
-/
theorem riemannHypothesis_of_pair_and_NBforward
    (H_decay : ClassicalMertensDecay)
    (H_pair : QuadraticInteractionBernoulliCorrelationEstimate H_decay)
    (h_forward : NBForward) :
    RH.Basic.RiemannHypothesis := by
  let H_linear : LinearMobiusDirichletEstimates :=
    linear_mobius_dirichlet_estimates_of_classical_api
      (ClassicalMertensAPI.ofDecayOnly H_decay)
  let H_quadratic : QuadraticInteractionEstimates :=
    quadraticInteractionEstimates_of_decay_and_bernoulliCorrelation H_decay H_pair
  have h_baez : BaezDuarteCriterion :=
    baezDuarteCriterion_of_linear_dirichlet_and_quadratic_interaction_estimates
      vasyuninBridgeLocalDebts_of_proved_chain H_linear H_quadratic
  exact h_forward (nymanBeurlingCriterion_iff_baezDuarteCriterion.mpr h_baez)

/-- Parallel endgame wiring for the redesigned Farey-cell interface.  The
restricted binary correlation estimate is still a hypothesis, as are the
exact cell decomposition and the independently separated BBLS/smooth/residue
inputs; this theorem only connects those packages to the existing H15 and NB
bridges. -/
theorem riemannHypothesis_of_weight_restricted_correlation_and_NBforward
    (H_decay : ClassicalMertensDecay)
    (Hcorr : FareyCellMobiusCorrelationEstimate_Restricted)
    (HBBLS : BBLS_EstermannContourPackage)
    (D : FareyCellGcdSliceErrorDecomposition_Restricted Hcorr HBBLS.mainTerm)
    (C_loggamma C_residue : ℝ)
    (C_pos :
      0 < C_loggamma +
        (quadraticInteractionDiagonalEstimate_zero.C_diagonal + D.C_error +
          HBBLS.C_main) + C_residue)
    (loggamma_bound :
      ∀ N : ℕ,
        |explicitQuadraticLogGammaComponent N| ≤ C_loggamma /
          Real.log (N + 2 : ℝ))
    (residue_bound :
      ∀ N : ℕ,
        |explicitCutoffResidueComponent N| ≤ C_residue /
          Real.log (N + 2 : ℝ))
    (h_forward : NBForward) :
    RH.Basic.RiemannHypothesis := by
  let H_linear : LinearMobiusDirichletEstimates :=
    linear_mobius_dirichlet_estimates_of_classical_api
      (ClassicalMertensAPI.ofDecayOnly H_decay)
  let H_quadratic : QuadraticInteractionEstimates :=
    quadraticInteractionEstimates_of_weightRestrictedCorrelation
      Hcorr HBBLS D C_loggamma C_residue C_pos loggamma_bound residue_bound
  have h_baez : BaezDuarteCriterion :=
    baezDuarteCriterion_of_linear_dirichlet_and_quadratic_interaction_estimates
      vasyuninBridgeLocalDebts_of_proved_chain H_linear H_quadratic
  exact h_forward (nymanBeurlingCriterion_iff_baezDuarteCriterion.mpr h_baez)

end RH.Criteria.NymanBeurling.FinalAssembly
