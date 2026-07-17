/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import NBMellinTools.BaezDuarteTail

/-!
# Conditional BCF formalization: finite definitions

This file defines the logarithmically tapered Dirichlet polynomial used by
Bettin--Conrey--Farmer and its corresponding finite Nyman--Beurling
approximation error.  Everything here is unconditional finite algebra.

The index `k : Fin N` represents the positive integer `k + 1`.  This avoids
the spurious `n = 0` term in an initial draft of the specification.  The
analytic results will assume `2 ≤ N`, so that `log N` is nonzero, but the
definitions are total for every natural number.

Primary source: S. Bettin, J. B. Conrey, and D. W. Farmer,
*An optimal choice of Dirichlet polynomials for the Nyman--Beurling
criterion*, arXiv:1211.5191.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators
open MeasureTheory Set
open NBMellinTools.NB2

/-- The BCF logarithmic taper `1 - log n / log N`.

Only values with `1 ≤ n ≤ N` and `2 ≤ N` are used analytically. -/
def bcfWeight (N n : ℕ) : ℝ :=
  1 - Real.log n / Real.log N

/-- The real coefficient `μ(n) (1 - log n / log N)` in the BCF polynomial. -/
def bcfCoefficient (N n : ℕ) : ℝ :=
  ((μ n : ℤ) : ℝ) * bcfWeight N n

/-- The finite BCF Dirichlet polynomial
`V_N(s) = ∑_{1 ≤ n ≤ N} μ(n) (1 - log n / log N) / n^s`.

The `Fin N` indexing is zero-based, so the represented positive integer is
`k.val + 1`. -/
def bcfDirichletPolynomial (N : ℕ) (s : ℂ) : ℂ :=
  ∑ k : Fin N,
    (bcfCoefficient N (k.val + 1) : ℂ) /
      (((k.val + 1 : ℕ) : ℂ) ^ s)

/-- The finite BCF linear combination of Báez--Duarte generators. -/
def bcfApproximation (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k : Fin N,
    bcfCoefficient N (k.val + 1) * rhoBD k.val x

/-- The BCF Nyman--Beurling approximation error
`χ_(0,1] + ∑_{n≤N} μ(n) w_N(n) ρ_n`.

The plus sign is the one whose Mellin transform is
`(1 - ζ(s) V_N(s)) / s`, because each generator has Mellin transform
`-ζ(s) / (s n^s)`. -/
def bcfApproximationError (N : ℕ) (x : ℝ) : ℝ :=
  chi01 x + bcfApproximation N x

/-- The squared `L²(0,∞)` energy of the finite BCF error. -/
def bcfGramEnergy (N : ℕ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), (bcfApproximationError N x) ^ 2

/-- The BCF approximation is the existing generic finite approximant with
the BCF coefficients. -/
theorem bcfApproximation_eq_bdApprox (N : ℕ) (x : ℝ) :
    bcfApproximation N x =
      bdApprox N (fun k ↦ bcfCoefficient N (k.val + 1)) x := by
  rfl

/-- The plus-sign convention can equivalently be expressed through the
existing subtraction-based Báez--Duarte API by negating all coefficients. -/
theorem bcfApproximationError_eq_chi_sub_bdApprox (N : ℕ) (x : ℝ) :
    bcfApproximationError N x =
      chi01 x - bdApprox N (fun k ↦ -bcfCoefficient N (k.val + 1)) x := by
  simp [bcfApproximationError, bcfApproximation, bdApprox]

/-- The finite BCF Gram energy is nonnegative. -/
theorem bcfGramEnergy_nonneg (N : ℕ) :
    0 ≤ bcfGramEnergy N := by
  unfold bcfGramEnergy
  apply integral_nonneg
  intro x
  positivity

end

end NBMellinTools.H15BCF
