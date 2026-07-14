import Mathlib
import RiemannHypothesis.Basic.CriticalStrip

/-!
# Li's Criterion

Li's criterion: RH is equivalent to λ_n ≥ 0 for all n ≥ 1,
where λ_n = (1/(n-1)!) · d^n/ds^n [s^(n-1) log ξ(s)] at s=1.

Reference: X.-J. Li, "The positivity of a sequence of numbers and the
Riemann Hypothesis", J. Number Theory 65 (1997), 325-333.
-/

namespace RH.Criteria

open RH.Basic

-- Li coefficients λ_n.
-- λ_n = (1/(n-1)!) · d^n/ds^n [s^(n-1) log ξ(s)] at s=1, where ξ is the completed zeta.
-- Declared as an axiom: requires Mathlib formalization of the completed zeta function.
axiom liCoefficient (n : ℕ) : ℝ

-- Li's Criterion: RH ↔ ∀ n ≥ 1, liCoefficient n ≥ 0
-- Reference: Li, J. Number Theory 65 (1997), 325-333.
axiom li_criterion :
    RH.Basic.RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoefficient n

-- Bridge: total positivity of a kernel implies positivity of all λ_n
-- DISCOVERY TARGET: find the right kernel and replace hK with a real condition.
axiom total_positivity_implies_li_positive (K : ℕ → ℕ → ℝ)
    (hK : True) -- placeholder: TotallyPositive K
    : ∀ n : ℕ, 0 ≤ liCoefficient n

end RH.Criteria
