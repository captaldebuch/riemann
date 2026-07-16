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

-- ---------------------------------------------------------------------------
-- 2. Formal Reductions
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
-- 3. The Isolated Hard Remainder Target
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

end RH.Criteria.NymanBeurling.QuadraticInteraction
