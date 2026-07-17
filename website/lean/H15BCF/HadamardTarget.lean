/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.HadamardPreparation

/-!
# Exact Hadamard target for the BCF zero-weight constant

The classical logarithmic derivative of the Hadamard product for the completed
Riemann xi function produces a complex, multiplicity-weighted zero sum.  This
file states that target in its natural form and proves the algebraic reduction
to the real BCF zero-weight formula under RH.

No canonical product is asserted.  `BCFHadamardLogDerivativeFormula` is the
remaining analytic result: it requires a canonical factorization of `bcfXi`
and justified logarithmic differentiation.  The results here make clear that
this missing theorem, together with the already explicit zero-simplicity
hypothesis, is sufficient for the existing Phase 7b.3 interface.

Primary source: S. Bettin, J. B. Conrey, and D. W. Farmer,
*An optimal choice of Dirichlet polynomials for the Nyman--Beurling
criterion*, arXiv:1211.5191, equation (1) and Lemma 2.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators Topology
open Complex Filter Set

/-- The complex zero weight naturally occurring after logarithmically
differentiating the Hadamard product of xi.  In contrast to the BCF
simple-zero contour sum, it counts a zero with its analytic multiplicity. -/
def bcfHadamardZeroWeightTerm (rho : ℂ) : ℂ :=
  bcfXiZeroMultiplicity rho / (rho * (1 - rho))

/-- A finite truncation of the complex, multiplicity-weighted Hadamard sum. -/
def bcfHadamardZeroWeightSumUpToHeight (T : ℝ) : ℂ :=
  ∑ rho ∈ bcfZerosUpToHeight T, bcfHadamardZeroWeightTerm rho

/-- The exact completed-xi/Hadamard logarithmic-derivative target.  Its proof
is not available in Mathlib: it needs a canonical product for `bcfXi` and the
associated convergence theorem. -/
def BCFHadamardLogDerivativeFormula : Prop :=
  Tendsto bcfHadamardZeroWeightSumUpToHeight atTop
    (𝓝 (bcfAsymptoticConstant : ℂ))

/-- On the critical line, the natural complex Hadamard denominator is the
real squared norm appearing in the BCF constant. -/
theorem rho_mul_one_sub_eq_norm_sq_of_re_eq_half {rho : ℂ}
    (hre : rho.re = 1 / 2) :
    rho * (1 - rho) = ((‖rho‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  apply Complex.ext
  · simp only [mul_re, sub_re, one_re, sub_im, one_im, zero_sub,
      ofReal_re]
    rw [hre]
    ring
  · simp only [mul_im, sub_re, one_re, sub_im, one_im, zero_sub,
      ofReal_im]
    rw [hre]
    ring

/-- Under RH, an individual complex Hadamard term is exactly the coercion of
the real multiplicity-weighted BCF term. -/
theorem bcfHadamardZeroWeightTerm_eq_real_of_rh
    (hRH : RiemannHypothesisHypothesis) {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ bcfZerosUpToHeight T) :
    bcfHadamardZeroWeightTerm rho =
      (((bcfXiZeroMultiplicity rho : ℝ) / ‖rho‖ ^ 2 : ℝ) : ℂ) := by
  unfold bcfHadamardZeroWeightTerm
  rw [rho_mul_one_sub_eq_norm_sq_of_re_eq_half (hRH.re_eq_half hrho)]
  norm_cast

/-- Under RH, every finite complex Hadamard sum is the coercion of the real,
multiplicity-weighted BCF zero sum. -/
theorem bcfHadamardZeroWeightSum_eq_realMultiplicity_of_rh
    (hRH : RiemannHypothesisHypothesis) (T : ℝ) :
    bcfHadamardZeroWeightSumUpToHeight T =
      (bcfMultiplicityZeroWeightSumUpToHeight T : ℂ) := by
  unfold bcfHadamardZeroWeightSumUpToHeight
    bcfMultiplicityZeroWeightSumUpToHeight
  push_cast
  apply Finset.sum_congr rfl
  intro rho hrho
  calc
    bcfHadamardZeroWeightTerm rho =
        (((bcfXiZeroMultiplicity rho : ℝ) / ‖rho‖ ^ 2 : ℝ) : ℂ) :=
      bcfHadamardZeroWeightTerm_eq_real_of_rh hRH hrho
    _ = (bcfXiZeroMultiplicity rho : ℂ) / (‖rho‖ : ℂ) ^ 2 := by
      norm_cast

/-- The genuinely complex Hadamard formula implies the real
multiplicity-weighted BCF formula under RH. -/
theorem bcfMultiplicityZeroWeightFormula_of_hadamard
    (hRH : RiemannHypothesisHypothesis)
    (hHadamard : BCFHadamardLogDerivativeFormula) :
    BCFMultiplicityZeroWeightFormula := by
  unfold BCFHadamardLogDerivativeFormula at hHadamard
  unfold BCFMultiplicityZeroWeightFormula
  have hreal :
      Tendsto (fun T : ℝ ↦ (bcfHadamardZeroWeightSumUpToHeight T).re)
        atTop (𝓝 bcfAsymptoticConstant) := by
    simpa using (Complex.continuous_re.tendsto (bcfAsymptoticConstant : ℂ)).comp hHadamard
  refine hreal.congr' ?_
  filter_upwards with T
  rw [bcfHadamardZeroWeightSum_eq_realMultiplicity_of_rh hRH]
  simp

/-- Combining the completed-xi Hadamard target with RH and the existing
explicit zero-simplicity hypothesis supplies precisely the distinct-zero
formula required by the BCF energy assembly. -/
theorem bcfZeroWeightFormula_of_hadamard_of_simplicity
    (hRH : RiemannHypothesisHypothesis)
    (hsimple : ZeroSimplicityHypothesis)
    (hHadamard : BCFHadamardLogDerivativeFormula) :
    BCFZeroWeightFormula :=
  bcfZeroWeightFormula_of_multiplicity_formula_of_simplicity hsimple
    (bcfMultiplicityZeroWeightFormula_of_hadamard hRH hHadamard)

end

end NBMellinTools.H15BCF
