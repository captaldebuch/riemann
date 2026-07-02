import Mathlib
import RiemannHypothesis.Basic.CriticalStrip

/-!
# Weil Positivity Criterion

Weil's criterion reformulates RH (and GRH-like statements) as the positivity 
of a distribution or quadratic form coming from the explicit formula.
-/

namespace RH.Criteria.WeilPositivity

open scoped BigOperators

structure MultiplicativeTestFunction where
  -- eventually: smooth compact support on ℝ₊*
  carrier : Type
  admissible : Prop

structure WeilLocalTerms where
  W_infty : MultiplicativeTestFunction → ℝ
  W_p : ℕ → MultiplicativeTestFunction → ℝ

-- Placeholder for the finite prime support sum.
-- Declared as an axiom: the support depends on the test function's admissibility structure,
-- which requires formalization of smooth compact support on ℝ₊*.
axiom finitePrimeSupport (g : MultiplicativeTestFunction) : Finset ℕ

-- Placeholder for the convolution star operation g ↦ g * g̃.
-- Declared as an axiom: requires the multiplicative convolution formalism on ℝ₊*.
axiom convolutionStar (g₁ g₂ : MultiplicativeTestFunction) : MultiplicativeTestFunction

-- Placeholder for the default Weil local terms W_∞, W_p.
-- Declared as an axiom: the explicit formulae require the explicit formula for ζ.
axiom defaultWeilTerms : WeilLocalTerms

noncomputable def WeilDistribution
    (W : WeilLocalTerms)
    (g : MultiplicativeTestFunction) : ℝ :=
  W.W_infty g + ∑ p ∈ finitePrimeSupport g, W.W_p p g

def WeilAdmissible (g : MultiplicativeTestFunction) : Prop :=
  g.admissible
  -- later: g ∈ C_c^∞(ℝ₊*) and ĝ(± i/2) = 0

def WeilPositivity : Prop :=
  ∀ g, WeilAdmissible g →
    WeilDistribution defaultWeilTerms (convolutionStar g g) ≤ 0

axiom weil_positivity_implies_RH :
  WeilPositivity → RH.Basic.RiemannHypothesis

axiom compact_support_localizes_prime_sum : True -- Placeholder
axiom finite_test_family_dense_for_weil : True -- Placeholder

end RH.Criteria.WeilPositivity
