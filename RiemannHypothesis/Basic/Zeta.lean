import Mathlib

/-!
# Riemann Zeta Function — Basic Definitions

Foundational definitions for ζ(s) on the critical strip.
-/

namespace RH.Basic

-- The completed zeta function ξ(s) = ½ s(s-1) π^(-s/2) Γ(s/2) ζ(s)
-- Defined in Mathlib as `Complex.riemannZeta`

-- The critical strip: 0 < Re(s) < 1
def inCriticalStrip (s : ℂ) : Prop := 0 < s.re ∧ s.re < 1

-- The critical line: Re(s) = 1/2
def onCriticalLine (s : ℂ) : Prop := s.re = 1 / 2

-- A nontrivial zero of ζ
def isNontrivialZero (s : ℂ) : Prop :=
  inCriticalStrip s ∧ riemannZeta s = 0

end RH.Basic
