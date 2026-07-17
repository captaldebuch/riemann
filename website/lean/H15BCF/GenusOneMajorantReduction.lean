/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.GenusOneProduct

/-!
# Reducing the genus-one majorant to inverse-square zero summability

For a compact set of values of `s`, the classical genus-one estimate is of the
form

`‖E₁(s / rho) ^ m(rho) - 1‖ ≤ C_K * m(rho) / ‖rho‖²`.

Together with summability of the multiplicity-weighted inverse-square zero
weights, this gives the compact majorants required by `GenusOneProduct`.  This
file proves that reduction exactly.  The two displayed analytic estimates are
named targets: their proof requires the Riemann--von Mangoldt/partial
summation argument and the elementary complex-exponential bounds, neither of
which is currently supplied by Mathlib for the Riemann xi zero set.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators Topology
open Complex Filter Set

/-- The multiplicity-weighted inverse-square zero weight naturally associated
with the genus-one product. -/
def bcfXiMultiplicityInverseSquareWeight (rho : bcfNontrivialZetaZeros) : ℝ :=
  (bcfXiZeroMultiplicity (rho : ℂ) : ℝ) / ‖(rho : ℂ)‖ ^ 2

/-- The inverse-square summability conclusion supplied classically by
Riemann--von Mangoldt counting and partial summation. -/
def BCFXiMultiplicityInverseSquareSummable : Prop :=
  Summable bcfXiMultiplicityInverseSquareWeight

/-- Under the existing zero-simplicity assumption, the multiplicity weight is
the ordinary inverse-square weight. -/
theorem bcfXiMultiplicityInverseSquareWeight_eq_of_simplicity
    (hsimple : ZeroSimplicityHypothesis) (rho : bcfNontrivialZetaZeros) :
    bcfXiMultiplicityInverseSquareWeight rho = 1 / ‖(rho : ℂ)‖ ^ 2 := by
  unfold bcfXiMultiplicityInverseSquareWeight
  rw [hsimple.xiMultiplicityOneAtNontrivialZeros rho rho.property]
  norm_num

/-- The distinct-zero inverse-square summability form convenient after the
project's explicit zero-simplicity reduction. -/
def BCFDistinctInverseSquareSummable : Prop :=
  Summable (fun rho : bcfNontrivialZetaZeros ↦ 1 / ‖(rho : ℂ)‖ ^ 2)

/-- Simplicity transfers the distinct inverse-square summability target to the
multiplicity-weighted product target. -/
theorem BCFXiMultiplicityInverseSquareSummable.of_simplicity
    (hsimple : ZeroSimplicityHypothesis)
    (hsum : BCFDistinctInverseSquareSummable) :
    BCFXiMultiplicityInverseSquareSummable := by
  unfold BCFXiMultiplicityInverseSquareSummable
  exact hsum.congr fun rho ↦
    (bcfXiMultiplicityInverseSquareWeight_eq_of_simplicity hsimple rho).symm

/-- The elementary compact `E₁` estimate needed to turn inverse-square
summability into a genus-one product majorant. -/
def BCFGenusOneCompactInverseSquareBound (K : Set ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ rho : bcfNontrivialZetaZeros, ∀ s ∈ K,
      ‖bcfXiGenusOneDeviation rho s‖ ≤
        C * bcfXiMultiplicityInverseSquareWeight rho

/-- The two classical inputs assemble mechanically into the compact
Weierstrass majorant already used by the product construction. -/
theorem bcfGenusOneCompactMajorant_of_inverseSquare
    {K : Set ℂ} (hsum : BCFXiMultiplicityInverseSquareSummable)
    (hbound : BCFGenusOneCompactInverseSquareBound K) :
    BCFGenusOneCompactMajorant K := by
  rcases hbound with ⟨C, hC, hbound⟩
  refine ⟨fun rho ↦ C * bcfXiMultiplicityInverseSquareWeight rho,
    hsum.mul_left C, ?_⟩
  intro rho s hs
  exact hbound rho s hs

/-- The complete zero-counting input for the locally uniform genus-one
product, separated from factorization and logarithmic differentiation. -/
structure BCFGenusOneMajorantData : Prop where
  inverseSquareSummable : BCFXiMultiplicityInverseSquareSummable
  compactInverseSquareBound :
    ∀ K : Set ℂ, IsCompact K → BCFGenusOneCompactInverseSquareBound K

/-- The zero-counting majorant data supplies compact majorants on the full
complex plane. -/
theorem BCFGenusOneMajorantData.locallySummableMajorant
    (hdata : BCFGenusOneMajorantData) :
    BCFGenusOneLocallySummableMajorantOn Set.univ := by
  intro K _ hK
  exact bcfGenusOneCompactMajorant_of_inverseSquare hdata.inverseSquareSummable
    (hdata.compactInverseSquareBound K hK)

end

end NBMellinTools.H15BCF
