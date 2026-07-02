import Mathlib
import RiemannHypothesis.Basic.CriticalStrip

/-!
# Formal Mining of Failed RH Proof Attempts

Each failed attempt is formalized as:
  Assumption₁ → Assumption₂ → Assumption₃ → RH

Then the exact unprovable assumption is isolated as an axiom.
Aristotle then tries to mutate/weaken it.

References analyzed here:
- Turán's partial sums approach (refuted by Montgomery)
- de Branges' Hilbert space positivity (refuted by Conrey–Li)
- Li's criterion attempts (convergence gaps)
-/

namespace RH.Discovery.Failed

open RH.Basic

-- TURAN ATTEMPT
-- Turán: if partial sums Σ_{n≤N} n^{-s} have no zeros with Re(s) > 1 → RH
-- Refuted: Montgomery showed these DO have such zeros for large N
-- Lesson: the premise is false; the implication is vacuously trivial

-- Formalized failure: isolate the false assumption
def turanPremise (N : ℕ) : Prop :=
  ∀ s : ℂ, s.re > 1 →
    (∑ n ∈ Finset.range N, (n : ℂ)⁻¹ ^ s) ≠ 0

-- Turán's theorem (correct implication, false premise)
-- The implication holds but requires analytic theory of the Riemann zeta function.
axiom turan_if_premise (h : ∀ N, turanPremise N) : RH.Basic.RiemannHypothesis

-- Montgomery's refutation (the premise fails)
-- Montgomery (1983) proved the Turán partial sums DO have zeros in Re(s) > 1.
axiom montgomery_refutes_turan : ¬ ∀ N, turanPremise N

-- DE BRANGES ATTEMPT
-- de Branges: positivity on a specific Hilbert space of entire functions → RH
-- Refuted: Conrey–Li showed the positivity condition fails

def deBrangesPositivity : Prop :=
  True -- placeholder: positivity on de Branges space

-- De Branges' claim: positivity on his Hilbert space implies RH.
axiom de_branges_if_positive (h : deBrangesPositivity) : RH.Basic.RiemannHypothesis

-- Conrey–Li refutation
-- Conrey and Li (1998) showed de Branges' positivity condition fails.
axiom conrey_li_refutes_de_branges : ¬ deBrangesPositivity

-- LESSON FROM FAILURES:
-- The pattern is always: a plausible assumption that cannot be proven,
-- often because convergence, positivity, or operator properties fail.
-- → Each axiom here is a candidate for Aristotle to mutate.

end RH.Discovery.Failed
