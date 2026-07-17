/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import NBMellinTools.H15BCF.HadamardEndpoint

/-!
# The endpoint logarithmic derivative of the BCF xi function

Mathlib's zeta asymptotics already evaluate the entire pole-removed completed
zeta function at `1`.  The completed-zeta functional equation transports that
value to `0`; elementary differentiation of the project's entire xi
normalization then gives its logarithmic derivative at zero.  This proves the
archimedean/special-value half of the BCF Hadamard endpoint calculation.

The independent remaining input is the canonical-product endpoint formula
`BCFHadamardEndpointFormula`.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open Complex

/-- The pole-removed completed zeta has the same special value at zero as at
one, by its functional equation. -/
theorem completedRiemannZeta₀_zero :
    completedRiemannZeta₀ 0 =
      ((Real.eulerMascheroniConstant : ℂ) -
        Complex.log (4 * (Real.pi : ℂ))) / 2 + 1 := by
  rw [← completedRiemannZeta₀_one_sub 0]
  norm_num [completedRiemannZeta₀_one]

/-- Differentiating the entire xi normalization at zero requires no
meromorphic differentiation: the factor `s * (s - 1)` vanishes there. -/
theorem deriv_bcfXi_zero :
    deriv bcfXi 0 = -completedRiemannZeta₀ 0 / 2 := by
  have hfactor :
      HasDerivAt (fun s : ℂ ↦ s * (s - 1)) (-1) 0 := by
    convert ((hasDerivAt_id (𝕜 := ℂ) 0).mul
      ((hasDerivAt_id (𝕜 := ℂ) 0).sub_const 1)) using 1
    all_goals norm_num
  have hproduct :
      HasDerivAt (fun s : ℂ ↦ s * (s - 1) * completedRiemannZeta₀ s)
        (-completedRiemannZeta₀ 0) 0 := by
    convert hfactor.mul differentiable_completedZeta₀.differentiableAt.hasDerivAt using 1
    all_goals simp
  have hxi :
      HasDerivAt
        (fun s : ℂ ↦ (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2)
        (-completedRiemannZeta₀ 0 / 2) 0 := by
    exact (hproduct.add_const (1 : ℂ)).div_const (2 : ℂ)
  change deriv (fun s : ℂ ↦
    (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2) 0 =
      -completedRiemannZeta₀ 0 / 2
  exact hxi.deriv

/-- The logarithmic derivative of xi at zero is exactly minus the
pole-removed completed-zeta endpoint value. -/
theorem logDeriv_bcfXi_zero :
    logDeriv bcfXi 0 = -completedRiemannZeta₀ 0 := by
  rw [logDeriv_apply, deriv_bcfXi_zero, bcfXi_zero]
  ring

/-- The archimedean special-value calculation required by the BCF Hadamard
endpoint method. -/
theorem bcfXiLogDerivAtZeroFormula : BCFXiLogDerivAtZeroFormula := by
  unfold BCFXiLogDerivAtZeroFormula bcfAsymptoticConstant
  rw [logDeriv_bcfXi_zero, completedRiemannZeta₀_zero]
  have hlog : Complex.log (4 * (Real.pi : ℂ)) =
      (Real.log (4 * Real.pi) : ℂ) := by
    rw [Complex.ofReal_log (by positivity : 0 ≤ 4 * Real.pi)]
    congr 1
    push_cast
    ring
  rw [hlog]
  push_cast
  ring

/-- Once the canonical-product endpoint formula is supplied, the special
value is no longer an additional hypothesis: it is proved above. -/
theorem bcfZeroWeightFormula_of_canonicalEndpoint_of_simplicity
    (hRH : RiemannHypothesisHypothesis)
    (hsimple : ZeroSimplicityHypothesis)
    (hendpoint : BCFHadamardEndpointFormula) :
    BCFZeroWeightFormula :=
  bcfZeroWeightFormula_of_endpoint_of_simplicity hRH hsimple hendpoint
    bcfXiLogDerivAtZeroFormula

end

end NBMellinTools.H15BCF
