import RiemannHypothesis.Criteria.NymanBeurling.QuadraticInteraction
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPeriodReduction

/-!
# H15 forward spine: Vaaler → exponential sums → DFI/Kloosterman

This module is deliberately a forward-facing interface, not an attempted
proof of the remaining quadratic estimate.  The existing
`FareyCellMobiusCorrelationEstimate` is the arithmetic endpoint already
identified for H15.  Here we record the two earlier stages that a future
analytic argument must supply:

* a Vaaler-type finite Fourier approximation to the Dedekind sawtooth
  `bernoulliB1`; and
* Type-I/Type-II exponential-sum estimates, including the Kloosterman-fraction
  form appearing after the Vaaler expansion.

The exact Farey-cell decomposition and weight bookkeeping remain the existing
`FareyCellGcdSliceErrorDecomposition` field.  Consequently the final bridge in
this file is purely structural and has no hidden analytic claim.
-/

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open RH.Criteria.NymanBeurling.VasyuninGram

/-! ## Explicit phase notation used by the exponential-sum stage -/

noncomputable def h15ExponentialPhase (α : ℝ) (n : ℕ) : ℂ :=
  Complex.exp ((((2 * Real.pi * α * (n : ℝ)) : ℝ) : ℂ) * Complex.I)

noncomputable def h15WeightedExponentialSum
    (M : ℕ) (α : ℝ) (w : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M, w n * h15ExponentialPhase α n

noncomputable def h15KloostermanFractionPhase
    (A m n : ℕ) : ℂ :=
  Complex.exp ((((2 * Real.pi * (A : ℝ) /
      ((m : ℝ) * (n : ℝ))) : ℝ) : ℂ) * Complex.I)

noncomputable def h15BilinearKloostermanFractionSum
    (M₁ M₂ A : ℕ) (u v : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M₁, ∑ n ∈ Finset.Icc 1 M₂,
    u m * v n * h15KloostermanFractionPhase A m n

/-! ## The Vaaler stage -/

/--
A content-bearing Vaaler package for the project’s Dedekind-sawtooth
convention.  `finite_fourier_expansion` is kept as a proposition-valued field
because the exact coefficient normalization (and the endpoint convention at
integers) must be fixed from the chosen Vaaler theorem before formalization.
The sandwich and nonnegativity fields are the statements used by the later
error bookkeeping.
-/
structure H15VaalerSawtoothPackage where
  approximant : ℕ → ℝ → ℝ
  errorMajorant : ℕ → ℝ → ℝ
  errorMajorant_nonneg : ∀ J : ℕ, ∀ x : ℝ, 0 ≤ errorMajorant J x
  uniform_error :
    ∀ J : ℕ, ∀ x : ℝ,
      |bernoulliB1 x - approximant J x| ≤ errorMajorant J x
  finite_fourier_expansion : Prop
  finite_fourier_expansion_holds : finite_fourier_expansion

/-! ## The exponential-sum stage -/

/--
The exponential-sum obligations exposed by the Vaaler expansion.  The three
fields are intentionally propositions rather than guessed universal
inequalities: their admissible smooth weights, dyadic ranges, and savings must
be frozen from the DFI/Kloosterman theorem actually selected.  Their intended
objects are `h15WeightedExponentialSum` (Type I) and
`h15BilinearKloostermanFractionSum` (Type II/Kloosterman fractions).
-/
structure H15ExponentialSumPackage where
  typeI_estimate : Prop
  typeI_estimate_holds : typeI_estimate
  typeII_estimate : Prop
  typeII_estimate_holds : typeII_estimate
  kloosterman_fraction_estimate : Prop
  kloosterman_fraction_estimate_holds : kloosterman_fraction_estimate

/-! ## Assembly into the existing Farey-cell endpoint -/

/--
The forward-spine package.  `mainTerm` is the same BBLS main term used by
`QuadraticInteractionGcdSliceErrorEstimate`.  The Vaaler and exponential
packages document the analytic route; `decomposition` is the exact finite
Farey-cell reduction and mass bookkeeping that turns its output into the
existing gcd-slice error interface.
-/
structure H15VaalerExponentialDFIPackage
    (H : MobiusSummatory.ClassicalMertensDecay)
    (mainTerm : ℕ → ℝ) where
  vaaler : H15VaalerSawtoothPackage
  exponentialSums : H15ExponentialSumPackage
  fareyCorrelation : FareyCellMobiusCorrelationEstimate
  decomposition :
    FareyCellGcdSliceErrorDecomposition fareyCorrelation mainTerm

/-- The DFI/Farey reduction discharges the abstract H15 gcd-slice error field. -/
noncomputable def quadraticInteractionGcdSliceErrorEstimate_of_forward_spine
    {H : MobiusSummatory.ClassicalMertensDecay} {mainTerm : ℕ → ℝ}
    (S : H15VaalerExponentialDFIPackage H mainTerm) :
    QuadraticInteractionGcdSliceErrorEstimate mainTerm :=
  quadraticInteractionGcdSliceErrorEstimate_of_fareyCellCorrelation
    S.fareyCorrelation mainTerm S.decomposition

/--
With the BBLS main-term package, the forward spine reaches the already-proved
analytic-subestimate assembly.  The only non-mechanical content remains in
the Vaaler, exponential-sum, and Farey decomposition fields above.
-/
noncomputable def quadraticInteractionAnalyticSubEstimates_of_forward_spine
    {H : MobiusSummatory.ClassicalMertensDecay}
    (B : BBLS_EstermannContourPackage)
    (S : H15VaalerExponentialDFIPackage H B.mainTerm) :
    QuadraticInteractionAnalyticSubEstimates := by
  exact quadraticInteractionAnalyticSubEstimates_of_BBLS_and_gcdError B
    (quadraticInteractionGcdSliceErrorEstimate_of_forward_spine S)

end RH.Criteria.NymanBeurling.QuadraticInteraction
