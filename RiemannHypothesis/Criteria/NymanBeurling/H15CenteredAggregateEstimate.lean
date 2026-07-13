import RiemannHypothesis.Criteria.NymanBeurling.QuadraticInteraction

/-!
# Corrected H15 centered aggregate interface

The earlier Farey-cell correlation interfaces quantified over independent
weights (including point masses) and demanded a logarithmic saving for every
individual cell.  Such an estimate cannot be the H15 input: the actual
kernel produces one coupled, `N`-dependent aggregate, and its main terms must
remain paired before cancellation is estimated.

This module freezes that exact aggregate in the normalization already used by
the quadratic-interaction finish.  It is deliberately a single analytic
number-theory target.  In particular, it does not claim that a generic
averaged-Chowla, logarithmically averaged, or DFI statement implies the
bound; theorem matching is a prerequisite for any such bridge.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open RH.Criteria.NymanBeurling.CutoffMobiusKernels

/-- The signed, centered H15 expression after the finite Farey and Fourier
bookkeeping has been aggregated with the specific cutoff-Möbius weights.  The
log-ratio, Bernoulli, and linear terms are intentionally kept in one absolute
value: bounding them separately loses the cancellation required by H15. -/
noncomputable def h15CenteredSawtoothResidual (N : ℕ) : ℝ :=
  explicitQuadraticLogRatioComponent N +
    cutoffMobiusBernoulliCorrelationValue N - 1 +
      2 * (explicitLinearMobiusSum N + 1)

/-- The complete aggregate controlled by the corrected H15 estimate.  The
smooth log-gamma component is included because the norm-residual endgame
needs the total mass of this package, not a cellwise estimate. -/
noncomputable def h15CenteredAggregateResidual (N : ℕ) : ℝ :=
  |explicitQuadraticLogGammaComponent N| + |h15CenteredSawtoothResidual N|

/--
The sole content-bearing H15 input in the corrected final route.

It is an aggregate estimate for the specific cutoff-Möbius kernel, uniformly
in its cutoff `N`; it has no quantification over arbitrary weights, Farey
cells, or affine forms.  A future analytic proof may derive it through a
Vaaler reciprocal-phase reduction, but that derivation is not asserted here.
-/
structure H15CenteredAggregateEstimate where
  C_aggregate : ℝ
  C_aggregate_nonneg : 0 ≤ C_aggregate
  aggregate_bound :
    ∀ N : ℕ,
      h15CenteredAggregateResidual N ≤
        C_aggregate / Real.log (N + 2 : ℝ) ^ 2

/-- The corrected aggregate is definitionally the existing centered
Möbius--Bernoulli package.  This is a bookkeeping conversion, not an
additional analytic assertion. -/
noncomputable def quadraticInteractionBernoulliCorrelationEstimate_of_h15CenteredAggregate
    (H_decay : MobiusSummatory.ClassicalMertensDecay)
    (H_aggregate : H15CenteredAggregateEstimate) :
    QuadraticInteractionBernoulliCorrelationEstimate H_decay :=
  { C_correlation := H_aggregate.C_aggregate
    C_correlation_nonneg := H_aggregate.C_aggregate_nonneg
    centered_correlation_bound := by
      intro N
      simpa [h15CenteredAggregateResidual, h15CenteredSawtoothResidual] using
        H_aggregate.aggregate_bound N }

/-- The corrected aggregate directly discharges the norm-residual interface
used by the established H15 finish. -/
noncomputable def quadraticInteractionNormResidual_of_h15CenteredAggregate
    (H_decay : MobiusSummatory.ClassicalMertensDecay)
    (H_aggregate : H15CenteredAggregateEstimate) :
    QuadraticInteractionNormResidual :=
  quadraticInteractionNormResidual_of_bernoulliCorrelation H_decay
    (quadraticInteractionBernoulliCorrelationEstimate_of_h15CenteredAggregate
      H_decay H_aggregate)

/-- H14 decay and the corrected H15 aggregate yield the existing quadratic
interaction estimates. -/
noncomputable def quadraticInteractionEstimates_of_decay_and_h15CenteredAggregate
    (H_decay : MobiusSummatory.ClassicalMertensDecay)
    (H_aggregate : H15CenteredAggregateEstimate) :
    QuadraticInteractionEstimates :=
  quadraticInteractionEstimates_of_mertens_and_normResidual
    (MobiusSummatory.ClassicalMertensAPI.ofDecayOnly H_decay)
    (quadraticInteractionNormResidual_of_h15CenteredAggregate H_decay H_aggregate)

end RH.Criteria.NymanBeurling.QuadraticInteraction
