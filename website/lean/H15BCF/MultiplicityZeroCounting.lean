/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.HadamardPreparation
import NBMellinTools.H15BCF.Lemma3LimitAssembly

/-!
# Multiplicity-aware zero counting for the xi canonical product

The Riemann--von Mangoldt function counts nontrivial zeta zeros with their
multiplicities.  The genus-one xi product therefore needs a
multiplicity-weighted height count, whereas the BCF contour calculation is
indexed by a `Finset` of distinct zeros.  This file formalizes that distinction
and proves the two counts agree under the project's already explicit
zero-simplicity hypothesis.

Mathlib currently provides zero discreteness and finite truncations, but not
the Riemann--von Mangoldt estimate itself.  The latter remains a named target;
no count asymptotic is asserted here.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators Topology
open Asymptotics Filter

/-- The number of nontrivial xi zeros up to height `T`, counted by their
analytic multiplicities. -/
def bcfXiZeroMultiplicityCount (T : ℝ) : ℕ :=
  ∑ rho ∈ bcfZerosUpToHeight T, bcfXiZeroMultiplicity rho

/-- The multiplicity-weighted zero count is monotone in the height cutoff. -/
theorem bcfXiZeroMultiplicityCount_monotone :
    Monotone bcfXiZeroMultiplicityCount := by
  intro T U hTU
  unfold bcfXiZeroMultiplicityCount
  apply Finset.sum_le_sum_of_subset_of_nonneg (bcfZerosUpToHeight_mono hTU)
  intro rho _ _
  exact Nat.zero_le _

/-- Under zero simplicity, every finite multiplicity count is exactly the
cardinality of the corresponding distinct-zero truncation. -/
theorem bcfXiZeroMultiplicityCount_eq_zeroCount_of_simplicity
    (hsimple : ZeroSimplicityHypothesis) (T : ℝ) :
    bcfXiZeroMultiplicityCount T = bcfZeroCount T := by
  unfold bcfXiZeroMultiplicityCount bcfZeroCount
  calc
    ∑ rho ∈ bcfZerosUpToHeight T, bcfXiZeroMultiplicity rho =
        ∑ _rho ∈ bcfZerosUpToHeight T, 1 := by
      apply Finset.sum_congr rfl
      intro rho hrho
      exact hsimple.xiMultiplicity_one hrho
    _ = (bcfZerosUpToHeight T).card := by simp

/-- The exact multiplicity-aware Riemann--von Mangoldt strength target needed
for the genus-one product.  It is unconditional in classical mathematics;
RH enters later when the BCF zero weights are reduced to the critical line. -/
def BCFMultiplicityZeroCountingAsymptotic : Prop :=
  (fun T : ℝ ↦ (bcfXiZeroMultiplicityCount T : ℝ)) =O[atTop]
    fun T : ℝ ↦ (T + 1) * Real.log (T + 2)

/-- The existing distinct-zero target implies the product's
multiplicity-aware target when the separately stated zero-simplicity
hypothesis is available. -/
theorem BCFMultiplicityZeroCountingAsymptotic.of_simplicity
    (hsimple : ZeroSimplicityHypothesis)
    (hcount : BCFZeroCountingAsymptotic) :
    BCFMultiplicityZeroCountingAsymptotic := by
  unfold BCFMultiplicityZeroCountingAsymptotic
  have hfun : (fun T : ℝ ↦ (bcfXiZeroMultiplicityCount T : ℝ)) =
      fun T : ℝ ↦ (bcfZeroCount T : ℝ) := by
    funext T
    rw [bcfXiZeroMultiplicityCount_eq_zeroCount_of_simplicity hsimple]
  rw [hfun]
  exact hcount

end

end NBMellinTools.H15BCF
