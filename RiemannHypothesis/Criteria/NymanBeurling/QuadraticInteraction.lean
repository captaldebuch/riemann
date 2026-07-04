import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open RH.Criteria.NymanBeurling.VasyuninGram

-- ---------------------------------------------------------------------------
-- 1. Unified Interaction Kernel
-- ---------------------------------------------------------------------------

/--
  The central arithmetic interaction kernel independent of the Möbius cutoff weights.
  It combines the log-ratio and the fractional cotangent sum, which are individually large
  but cancel heavily to approximate 1 when summed against the Möbius cutoff.
-/
noncomputable def quadraticInteractionKernel (h k : ℕ) : ℝ :=
  (((k : ℝ) - (h : ℝ)) / (2 * (h : ℝ) * (k : ℝ)) * Real.log ((h : ℝ) / (k : ℝ)))
    - (Real.pi / (2 * (h : ℝ) * (k : ℝ)) * (cotangentSumVFormula h k + cotangentSumVFormula k h))

theorem quadraticInteractionKernel_symm (h k : ℕ) :
    quadraticInteractionKernel h k = quadraticInteractionKernel k h := by
  by_cases hh : h = 0
  · subst h
    simp [quadraticInteractionKernel]
  by_cases hk : k = 0
  · subst k
    simp [quadraticInteractionKernel]
  unfold quadraticInteractionKernel
  rw [Real.log_div (Nat.cast_ne_zero.mpr hh) (Nat.cast_ne_zero.mpr hk),
    Real.log_div (Nat.cast_ne_zero.mpr hk) (Nat.cast_ne_zero.mpr hh)]
  ring

-- ---------------------------------------------------------------------------
-- 2. Diagonal / Off-Diagonal Split
-- ---------------------------------------------------------------------------

/-- The terms in the weighted interaction sum with equal indices. -/
noncomputable def quadraticInteractionDiagonal (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N h * quadraticInteractionKernel h h

/-- The terms in the weighted interaction sum with distinct indices. -/
noncomputable def quadraticInteractionOffDiagonal (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ (Finset.Icc 1 N).erase h,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k

theorem quadraticInteractionKernelSum_eq_diagonal_add_offDiagonal (N : ℕ) :
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k) =
      quadraticInteractionDiagonal N + quadraticInteractionOffDiagonal N := by
  unfold quadraticInteractionDiagonal quadraticInteractionOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  exact (Finset.add_sum_erase (Finset.Icc 1 N)
    (fun k => cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
      quadraticInteractionKernel h k) hh).symm

-- ---------------------------------------------------------------------------
-- 3. Formal Reductions
-- ---------------------------------------------------------------------------

theorem explicitQuadraticLogCotangentInteraction_eq_unified_sum (N : ℕ) :
    explicitQuadraticLogCotangentInteraction N =
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k := by
  unfold explicitQuadraticLogCotangentInteraction
  unfold explicitQuadraticLogRatioComponent explicitQuadraticCotangentComponent
  unfold quadraticInteractionKernel
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

-- ---------------------------------------------------------------------------
-- 4. The Isolated Hard Remainder Target
-- ---------------------------------------------------------------------------

/--
  The core remaining analytic estimate target:
  The double sum over the interaction kernel must converge to 1
  with an error rate of O(1/log N).
-/
theorem explicitQuadraticInteractionRemainder_eq_kernel_sum (N : ℕ) :
    explicitQuadraticInteractionRemainder N =
      (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k) - 1 := by
  unfold explicitQuadraticInteractionRemainder
  rw [explicitQuadraticLogCotangentInteraction_eq_unified_sum N]

theorem explicitQuadraticInteractionRemainder_eq_diagonal_add_offDiagonal (N : ℕ) :
    explicitQuadraticInteractionRemainder N =
      quadraticInteractionDiagonal N + quadraticInteractionOffDiagonal N - 1 := by
  rw [explicitQuadraticInteractionRemainder_eq_kernel_sum,
    quadraticInteractionKernelSum_eq_diagonal_add_offDiagonal]

end RH.Criteria.NymanBeurling.QuadraticInteraction
