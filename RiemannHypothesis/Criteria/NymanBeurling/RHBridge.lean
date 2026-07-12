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
  baez_duarte_criterion_implies_RH debt h

end RH.Criteria.NymanBeurling.RHBridge
