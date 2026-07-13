import RiemannHypothesis.Criteria.NymanBeurling.FinalAssembly

/-!
# H15 Möbius correlation: an explicit open-problem boundary

The restricted Farey-cell interface already states the exact analytic estimate
needed by the quadratic-interaction assembly:

* two Möbius factors on distinct affine-linear forms;
* coprime Farey parameters and residue ranges;
* a geometric-decay weight class; and
* a logarithmic saving uniform in the cutoff.

Mathlib and the vendored project sources contain no formal result of this
strength.  In particular, the available arithmetic-function and Chebyshev
files do not contain Chowla, Tao--Teräväinen, or Harper--Klurman--Mangerel
correlation estimates.  The three plausible research routes are therefore
recorded as documentation, not silently converted into Lean proofs:

1. averaged Chowla / Matomäki--Radziwiłł--Tao;
2. logarithmically averaged correlations / Tao--Teräväinen; and
3. character-theoretic estimates / Harper--Klurman--Mangerel.

The proposition below is the existing content-bearing restricted interface,
wrapped in a named open-problem proposition.  This wrapper adds no analytic
claim and no `sorryAx`; it makes the remaining research assumption explicit
to downstream conditional theorems.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open RH.Criteria.NymanBeurling
open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open RH.Criteria.NymanBeurling.MobiusSummatory
open RH.Criteria.NymanBeurling.RHBridge

/-! ## Literature-route labels -/

/-- The three modern routes that could eventually discharge the open estimate.
These constructors are labels only; no route is asserted to be formalized. -/
inductive H15MobiusCorrelationRoute
  | averagedChowla
  | taoTeravainenLogAverage
  | characterTheoretic
  deriving DecidableEq, Repr

def h15MobiusCorrelationRoutes : List H15MobiusCorrelationRoute :=
  [.averagedChowla, .taoTeravainenLogAverage, .characterTheoretic]

/-! ## Named open proposition -/

/--
The H15 two-linear-forms Möbius correlation estimate as an explicit open
problem.  Its definition is intentionally `Nonempty` rather than an axiom:
an eventual proof must provide an inhabitant of the already-frozen
`FareyCellMobiusCorrelationEstimate_Restricted` structure.

The exact quantifiers and majorant are therefore inherited from that structure
instead of being duplicated here.  This avoids weakening or accidentally
strengthening the research target.
-/
def FareyCellMobiusCorrelationEstimate_Restricted_open_problem : Prop :=
  Nonempty FareyCellMobiusCorrelationEstimate_Restricted

theorem fareyCellMobiusCorrelationEstimate_Restricted_open_problem_iff :
    FareyCellMobiusCorrelationEstimate_Restricted_open_problem ↔
      Nonempty FareyCellMobiusCorrelationEstimate_Restricted :=
  Iff.rfl

/-- Extract the correlation estimate when the open problem is supplied. -/
noncomputable def fareyCellMobiusCorrelationEstimate_of_open_problem
    (H : FareyCellMobiusCorrelationEstimate_Restricted_open_problem) :
    FareyCellMobiusCorrelationEstimate_Restricted :=
  Classical.choice H

theorem open_problem_routes_are_documentary :
    h15MobiusCorrelationRoutes.length = 3 := by
  rfl

/-! ## Conditional endgame wiring -/

/--
The RH conditional result with the correlation debt named explicitly.

All other inputs use the project's existing assembly shape: H14 decay,
the BBLS main-term package, a Farey-cell decomposition, smooth/residue bounds,
and the forward Nyman--Beurling implication.  Supplying the open proposition
only supplies the correlation package; it does not discharge any other H15 or
NB field.
-/
theorem riemannHypothesis_assuming_correlation_open_problem
    (H_open : FareyCellMobiusCorrelationEstimate_Restricted_open_problem)
    (H_decay : MobiusSummatory.ClassicalMertensDecay)
    (HBBLS : BBLS_EstermannContourPackage)
    (D : FareyCellGcdSliceErrorDecomposition_Restricted
      (fareyCellMobiusCorrelationEstimate_of_open_problem H_open) HBBLS.mainTerm)
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
  exact FinalAssembly.riemannHypothesis_of_weight_restricted_correlation_and_NBforward
    H_decay (fareyCellMobiusCorrelationEstimate_of_open_problem H_open) HBBLS D
    C_loggamma C_residue C_pos loggamma_bound residue_bound h_forward

end RH.Criteria.NymanBeurling.QuadraticInteraction
