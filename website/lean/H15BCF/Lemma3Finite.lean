/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib.Data.Real.Sqrt
import NBMellinTools.H15BCF.Hypotheses

/-!
# Finite Cauchy--Schwarz layer of BCF Lemma 3

BCF Lemma 3 separates a zero-residue sum into two factors: the reciprocal
zeta-derivative moment and a geometric kernel sum.  This file formalizes that
finite algebra exactly.  It does not assert the subsequent zero-counting,
partial-summation, or infinite-series estimates; those are the remaining
analytic content of Lemma 3.

Primary source: S. Bettin, J. B. Conrey, and D. W. Farmer,
*An optimal choice of Dirichlet polynomials for the Nyman--Beurling
criterion*, arXiv:1211.5191, Lemma 3, especially equations (4)--(5).
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators Topology
open Complex Filter Set

/-- The finite simple-zero residue sum truncated by imaginary height.  This
uses the same cutoff as the reciprocal-derivative moment in the hypotheses. -/
def bcfHeightTruncatedSimpleZeroResidueSum
    (N : ℕ) (s : ℂ) (T : ℝ) : ℂ :=
  ∑ rho ∈ bcfZerosUpToHeight T, bcfSimpleZeroResidue N s rho

/-- The non-derivative factor in the norm of a simple BCF zero residue. -/
def bcfZeroResidueGeometry (N : ℕ) (s rho : ℂ) : ℝ :=
  ‖bcfNPow N (rho - s)‖ / ‖rho - s‖ ^ 2

/-- At a simple zero away from `s`, the norm of the BCF residue separates
into its reciprocal-derivative and geometric factors. -/
theorem norm_bcfSimpleZeroResidue_eq_reciprocalDeriv_mul_geometry
    {N : ℕ} {s rho : ℂ}
    (hderiv : deriv riemannZeta rho ≠ 0) (hrho_s : rho ≠ s) :
    ‖bcfSimpleZeroResidue N s rho‖ =
      (1 / ‖deriv riemannZeta rho‖) * bcfZeroResidueGeometry N s rho := by
  unfold bcfSimpleZeroResidue bcfZeroResidueGeometry
  have hnorm_deriv : ‖deriv riemannZeta rho‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hderiv
  have hnorm_diff : ‖rho - s‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr hrho_s)
  rw [norm_div, norm_mul, norm_pow]
  field_simp [hnorm_deriv, hnorm_diff]

/-- The exact finite Cauchy--Schwarz inequality used at the first step of
BCF Lemma 3.  The first square sum is precisely the project's
reciprocal-zeta-derivative moment. -/
theorem bcf_reciprocalDeriv_cauchySchwarz
    (T : ℝ) (g : ℂ → ℝ) :
    (∑ rho ∈ bcfZerosUpToHeight T,
      (1 / ‖deriv riemannZeta rho‖) * g rho) ≤
      √(bcfReciprocalZetaDerivMoment T) *
        √(∑ rho ∈ bcfZerosUpToHeight T, (g rho) ^ 2) := by
  unfold bcfReciprocalZetaDerivMoment
  simpa only [one_div, inv_pow] using
    Real.sum_mul_le_sqrt_mul_sqrt (bcfZerosUpToHeight T)
      (fun rho : ℂ ↦ (‖deriv riemannZeta rho‖)⁻¹) g

/-- The norm of every finite height-truncated simple-zero residue sum is
bounded by the product of the reciprocal-derivative moment and the geometric
kernel square sum.  This is the fully formal finite part of BCF Lemma 3. -/
theorem norm_bcfHeightTruncatedSimpleZeroResidueSum_le
    (hsimple : ZeroSimplicityHypothesis)
    {N : ℕ} {s : ℂ} {T : ℝ}
    (hseparated : ∀ rho ∈ bcfZerosUpToHeight T, rho ≠ s) :
    ‖bcfHeightTruncatedSimpleZeroResidueSum N s T‖ ≤
      √(bcfReciprocalZetaDerivMoment T) *
        √(∑ rho ∈ bcfZerosUpToHeight T,
          (bcfZeroResidueGeometry N s rho) ^ 2) := by
  unfold bcfHeightTruncatedSimpleZeroResidueSum
  calc
    ‖∑ rho ∈ bcfZerosUpToHeight T, bcfSimpleZeroResidue N s rho‖ ≤
        ∑ rho ∈ bcfZerosUpToHeight T, ‖bcfSimpleZeroResidue N s rho‖ :=
      norm_sum_le (bcfZerosUpToHeight T)
        (fun rho ↦ bcfSimpleZeroResidue N s rho)
    _ = ∑ rho ∈ bcfZerosUpToHeight T,
        (1 / ‖deriv riemannZeta rho‖) * bcfZeroResidueGeometry N s rho := by
      apply Finset.sum_congr rfl
      intro rho hrho
      exact norm_bcfSimpleZeroResidue_eq_reciprocalDeriv_mul_geometry
        (hsimple.deriv_ne_zero hrho) (hseparated rho hrho)
    _ ≤ √(bcfReciprocalZetaDerivMoment T) *
        √(∑ rho ∈ bcfZerosUpToHeight T,
          (bcfZeroResidueGeometry N s rho) ^ 2) :=
      bcf_reciprocalDeriv_cauchySchwarz T (bcfZeroResidueGeometry N s)

end

end NBMellinTools.H15BCF
