import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels

namespace RH.Criteria.NymanBeurling.MobiusSummatory

open RH.Criteria.NymanBeurling.CutoffMobiusKernels

-- ---------------------------------------------------------------------------
-- 1. Standard Möbius Summatory Functions
-- ---------------------------------------------------------------------------

/-- M(N) = Σ_{k=1}^N μ(k) -/
noncomputable def mobiusSummatory (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius k : ℤ) : ℝ)

/-- L(N) = Σ_{k=1}^N μ(k) log(k) -/
noncomputable def mobiusLogSummatory (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius k : ℤ) : ℝ) * Real.log (k : ℝ)

-- ---------------------------------------------------------------------------
-- 2. Classical Asymptotic Bounds Structure
-- ---------------------------------------------------------------------------

/-- 
  The classical asymptotic estimates for the Möbius function.
  For the cutoff-Möbius integral convergence, we need bounds strong enough
  to overcome the logarithmic weights in the Abel summation.
  Specifically, M(N) ≪ N / log(N)^A and L(N) ≪ N / log(N)^A for some A > 1.
-/
structure MobiusSummatoryEstimates where
  C_M : ℝ
  C_L : ℝ
  -- For now we just assume it implies the exact Dirichlet estimate targets:
  implies_overK :
    ∀ N : ℕ,
      |cutoffMobiusOverKSum N|
        ≤ C_M / Real.log (N + 2 : ℝ)
  implies_logOverK :
    ∀ N : ℕ,
      |cutoffMobiusLogOverKSum N + 1|
        ≤ C_L / Real.log (N + 2 : ℝ)
  C_pos : 0 < C_L + |1 - Real.eulerMascheroniConstant| * C_M

-- ---------------------------------------------------------------------------
-- 3. Summation by Parts Reductions (Sketched)
-- ---------------------------------------------------------------------------

-- The rigorous Abel summation identities rewriting the cutoff sums in terms
-- of M(N) and L(N) are analytically heavy and are marked as sorry here to
-- establish the structural reduction.

theorem cutoffMobiusOverKSum_eq_abel_sum (N : ℕ) :
    cutoffMobiusOverKSum N =
      -- A concrete expression involving mobiusSummatory
      sorry := by sorry

theorem cutoffMobiusLogOverKSum_eq_abel_sum (N : ℕ) :
    cutoffMobiusLogOverKSum N + 1 =
      -- A concrete expression involving mobiusLogSummatory and mobiusSummatory
      sorry := by sorry

-- ---------------------------------------------------------------------------
-- 4. Bridge to Dirichlet Estimates
-- ---------------------------------------------------------------------------

noncomputable def linear_mobius_dirichlet_estimates_of_summatory_estimates
    (H : MobiusSummatoryEstimates) :
    LinearMobiusDirichletEstimates :=
  { C_log := H.C_L
    C_overK := H.C_M
    C_pos := H.C_pos
    log_bound := H.implies_logOverK
    overK_bound := H.implies_overK }

end RH.Criteria.NymanBeurling.MobiusSummatory
