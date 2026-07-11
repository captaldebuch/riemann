import RiemannHypothesis.Criteria.NymanBeurling.NymanBeurlingForward
import RiemannHypothesis.Criteria.NymanBeurling.QuadraticInteraction

/-!
# Final conditional assembly

This module records the exact endgame wiring without asserting either of the
remaining analytic inputs.  A classical Mertens decay package supplies the
linear estimates, while the centered Bernoulli correlation package supplies
the quadratic estimates.  A forward Nyman--Beurling implication then yields
RH.  The correlation package and the forward implication remain explicit
hypotheses, so this theorem does not hide an analytic debt.
-/

namespace RH.Criteria.NymanBeurling.FinalAssembly

open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open RH.Criteria.NymanBeurling.MobiusSummatory
open RH.Criteria.NymanBeurling.NymanBeurlingForward
open RH.Criteria.NymanBeurling.QuadraticInteraction
open RH.Criteria.NymanBeurling.VasyuninGram

/--
The final conditional RH wiring.  The first hypothesis is the single H14
decay input, the second is the centered H15 Bernoulli-correlation estimate,
the third is the local Vasyunin bridge, and the fourth is the forward
Nyman--Beurling implication.  No converse Nyman--Beurling implication is
used.
-/
theorem riemannHypothesis_of_pair_and_NBforward
    (H_decay : ClassicalMertensDecay)
    (H_pair : QuadraticInteractionBernoulliCorrelationEstimate H_decay)
    (H_vasyunin : VasyuninBridgeLocalDebts)
    (h_forward : NBForward) :
    RH.Basic.RiemannHypothesis := by
  let H_linear : LinearMobiusDirichletEstimates :=
    linear_mobius_dirichlet_estimates_of_classical_api
      (ClassicalMertensAPI.ofDecayOnly H_decay)
  let H_quadratic : QuadraticInteractionEstimates :=
    quadraticInteractionEstimates_of_decay_and_bernoulliCorrelation H_decay H_pair
  have h_baez : BaezDuarteCriterion :=
    baezDuarteCriterion_of_linear_dirichlet_and_quadratic_interaction_estimates
      H_vasyunin H_linear H_quadratic
  exact h_forward (nymanBeurlingCriterion_iff_baezDuarteCriterion.mpr h_baez)

end RH.Criteria.NymanBeurling.FinalAssembly
