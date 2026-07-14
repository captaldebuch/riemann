import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels
import RiemannHypothesis.Criteria.NymanBeurling.BaezDuarte

open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open RH.Criteria.NymanBeurling.CoefficientFamilies
open RH.Criteria.NymanBeurling.AsymptoticEnergy
open RH.Criteria.NymanBeurling.BaezDuarte

namespace RH.Criteria.NymanBeurling.CutoffMobiusKernels

theorem baezDuarteCriterion_of_linear_dirichlet_and_quadratic_interaction_estimates
    (HL : LinearMobiusDirichletEstimates)
    (HQ : QuadraticInteractionEstimates) :
    BaezDuarteCriterion := by
  have Hsplit :
      CenteredCutoffMobiusSplitEstimates :=
    centered_split_estimates_of_linear_and_quadratic
      (linear_mobius_centered_estimate_of_dirichlet_estimates HL)
      HQ

  have Hcomponents :
      ExplicitCutoffMobiusComponentEstimates :=
    explicit_component_estimate_of_centered_split_estimates Hsplit

  have Hexplicit :
      ExplicitCutoffMobiusKernelEstimate :=
    explicit_kernel_estimate_of_component_estimates Hcomponents

  have Hkernel :
      CutoffMobiusKernelEstimate :=
    cutoffMobius_kernel_estimate_of_explicit Hexplicit

  have Hlog :
      CutoffMobiusLogEnergyTarget :=
    cutoffMobius_log_energy_of_kernel_estimate Hkernel

  exact baezDuarteCriterion_of_cutoffMobius_log_energy Hlog

theorem RH_of_linear_dirichlet_and_quadratic_interaction_estimates
    (HL : LinearMobiusDirichletEstimates)
    (HQ : QuadraticInteractionEstimates) :
    RH.Basic.RiemannHypothesis := by
  exact baez_duarte_criterion_implies_RH
    (baezDuarteCriterion_of_linear_dirichlet_and_quadratic_interaction_estimates HL HQ)

end RH.Criteria.NymanBeurling.CutoffMobiusKernels
