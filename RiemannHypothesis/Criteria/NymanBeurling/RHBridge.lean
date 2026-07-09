import Mathlib
import RiemannHypothesis.Basic.CriticalStrip
import RiemannHypothesis.Criteria.NymanBeurling.BaezDuarte

namespace RH.Criteria.NymanBeurling.RHBridge

open RH.Criteria.NymanBeurling.BaezDuarte

/-!
# Phase NB-A: Nyman-Beurling / RH Bridge

We isolate the exact analytical implication needed to obtain RH from the
functional analysis criteria, replacing the old `nyman_beurling_criterion_iff_RH` axiom.
-/

/-- The exact analytical debt required to cross from Nyman-Beurling to RH.
    We only need the forward direction to complete the project's goal. -/
structure NymanBeurlingRHBridgeDebts where
  /-- The forward direction: Nyman-Beurling approximation rate implies RH.
      This is typically proved via Mellin transform and showing the zeta function
      cannot have zeros with Re(s) > 1/2. -/
  RH_of_nymanBeurlingCriterion : NymanBeurlingCriterion → RH.Basic.RiemannHypothesis

/-- If we have the bridge debt, we can cross from Nyman-Beurling to RH. -/
theorem RH_of_nymanBeurlingCriterion (debt : NymanBeurlingRHBridgeDebts)
    (h : NymanBeurlingCriterion) : RH.Basic.RiemannHypothesis :=
  debt.RH_of_nymanBeurlingCriterion h

/-- We expose the specific direction needed from the Phase 10A equivalence. -/
theorem nymanBeurlingCriterion_of_baezDuarteCriterion
    (h : BaezDuarteCriterion) : NymanBeurlingCriterion :=
  nymanBeurlingCriterion_iff_baezDuarteCriterion.mpr h

/-- The final bridge: Baez-Duarte criterion implies RH, given the analytical debt. -/
theorem RH_of_baezDuarteCriterion (debt : NymanBeurlingRHBridgeDebts)
    (h : BaezDuarteCriterion) : RH.Basic.RiemannHypothesis :=
  debt.RH_of_nymanBeurlingCriterion (nymanBeurlingCriterion_of_baezDuarteCriterion h)

end RH.Criteria.NymanBeurling.RHBridge
