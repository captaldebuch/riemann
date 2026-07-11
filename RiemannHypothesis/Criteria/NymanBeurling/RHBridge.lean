import RiemannHypothesis.Criteria.NymanBeurling.NymanBeurlingForward

/-!
# Phase NB0 — structural Nyman--Beurling/RH bridge debts

This file separates the forward Nyman--Beurling implication into the two
mathematical debts that remain after the finite Báez--Duarte reduction.  The
first debt is the analytic implication from the approximation criterion to
zero-freeness in the right half of the critical strip.  The second is the
elementary symmetry step from that zero-free half-strip to RH; it is proved
here using the existing functional-equation symmetry axiom.

The Mellin structure below freezes the next analytic attack surface without
asserting any of its fields.  Its statements use the actual functions in
`BaezDuarte.lean`, including the zero-based `rhoBD` index used by `bdApprox`.
-/

namespace RH.Criteria.NymanBeurling.RHBridge

open scoped BigOperators

open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.NymanBeurlingForward

/-! ## NB0-b: the two-debt bridge -/

/-- The two analytic implications underlying the forward Nyman--Beurling
bridge.  The second field is discharged below from `zero_symmetry`. -/
structure NymanBeurlingRHBridgeDebts where
  nyman_implies_no_zeros_right_half :
    NymanBeurlingCriterion →
      ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0
  no_zeros_right_half_implies_RH :
    (∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0) →
      RH.Basic.RiemannHypothesis

/-- Mechanical composition of the two bridge debts into `NBForward`. -/
theorem NBForward_of_bridgeDebts (D : NymanBeurlingRHBridgeDebts) : NBForward := by
  intro hcriterion
  exact D.no_zeros_right_half_implies_RH
    (D.nyman_implies_no_zeros_right_half hcriterion)

/-! ## NB0-c: the symmetry half is unconditional relative to `zero_symmetry` -/

/-- If there are no nontrivial zeros in the open right half of the critical
strip, the existing functional-equation symmetry forces every nontrivial zero
onto the critical line. -/
theorem no_zeros_right_half_implies_RH :
    (∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0) →
      RH.Basic.RiemannHypothesis := by
  intro hright s hs
  rcases hs with ⟨hsstrip, hszero⟩
  rcases hsstrip with ⟨hspos, hslt⟩
  unfold RH.Basic.onCriticalLine
  by_contra hneq
  rcases lt_or_gt_of_ne hneq with hsleft | hsright
  · have hsym : RH.Basic.isNontrivialZero (1 - s) :=
      RH.Basic.zero_symmetry s ⟨⟨hspos, hslt⟩, hszero⟩
    have hsymstrip : 1 / 2 < (1 - s).re ∧ (1 - s).re < 1 := by
      constructor
      · norm_num [Complex.sub_re]
        linarith
      · norm_num [Complex.sub_re]
        linarith
    exact (hright (1 - s) hsymstrip.1 hsymstrip.2) hsym.2
  · exact (hright s hsright hslt) hszero

/-- Constructor for the two-debt package when only the analytic forward debt
has been supplied. -/
def NymanBeurlingRHBridgeDebts_of_forward_debt
    (hforward :
      NymanBeurlingCriterion →
        ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0) :
    NymanBeurlingRHBridgeDebts where
  nyman_implies_no_zeros_right_half := hforward
  no_zeros_right_half_implies_RH := no_zeros_right_half_implies_RH

end RH.Criteria.NymanBeurling.RHBridge
