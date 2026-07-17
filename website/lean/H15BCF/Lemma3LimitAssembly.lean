/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib.NumberTheory.AbelSummation
import NBMellinTools.H15BCF.Lemma2Assembly
import NBMellinTools.H15BCF.Lemma3Finite

/-!
# Zero counting, partial summation, and the infinite-residue limit for BCF Lemma 3

This module fixes the three remaining interfaces in the analytic part of BCF
Lemma 3.

* `bcfZeroCount` is the actual finite count of distinct nontrivial zeta zeros
  in the height truncation, and is proved monotone.
* `bcf_abel_partial_summation` is the exact Abel-summation formula needed to
  turn a shellwise geometric-kernel estimate into an integral estimate.  It is
  a direct specialization of Mathlib's theorem, not a new analytic axiom.
* `BCFNontrivialResidueCauchy` is the precise tail assertion needed for the
  infinite residue sum.  Completeness of `ℂ` turns it into the convergence data
  consumed by the already-proved global Lemma 2 assembly.

The missing number-theoretic input is deliberately isolated as
`BCFZeroCountingAsymptotic` together with
`BCFGeometricKernelSquareBound`.  Mathlib currently proves that zeta zeros are
discrete (and therefore each truncation is finite), but does not provide the
Riemann--von Mangoldt asymptotic or its local interval consequence.  Thus this
file does *not* claim either estimate.  The subsequent residue-limit theorem
is fully proved once a Cauchy estimate has actually been supplied.

Primary source: S. Bettin, J. B. Conrey, and D. W. Farmer,
*An optimal choice of Dirichlet polynomials for the Nyman--Beurling
criterion*, arXiv:1211.5191, Lemma 3 and the proof of Theorem 1.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators Topology
open Asymptotics Complex Filter MeasureTheory Set

/-- The number of distinct nontrivial zeta zeros with `|im rho| ≤ T`. -/
def bcfZeroCount (T : ℝ) : ℕ :=
  (bcfZerosUpToHeight T).card

/-- Zero counts are monotone when the height cutoff increases. -/
theorem bcfZeroCount_monotone : Monotone bcfZeroCount := by
  intro T U hTU
  apply Finset.card_le_card
  intro rho hrho
  rw [mem_bcfZerosUpToHeight] at hrho ⊢
  exact ⟨hrho.1, hrho.2.1, hrho.2.2.1, hrho.2.2.2.trans hTU⟩

/-- A disk truncation is contained in the height truncation with height equal
to the absolute disk radius.  This is the concrete bridge between the disk
cutoff used by the contour deformation and the height cutoff used by BCF's
zero-count and reciprocal-derivative estimates. -/
theorem bcfTruncatedZeros_subset_bcfZerosUpToHeight_abs (R : ℝ) :
    bcfTruncatedZeros R ⊆ bcfZerosUpToHeight |R| := by
  intro rho hrho
  rw [mem_bcfTruncatedZeros] at hrho
  rw [mem_bcfZerosUpToHeight]
  refine ⟨hrho.2.1, hrho.2.2.1, hrho.2.2.2, ?_⟩
  have hnorm : ‖rho‖ ≤ R := by
    simpa [Metric.mem_closedBall] using hrho.1
  exact (abs_im_le_norm rho).trans (hnorm.trans (le_abs_self R))

/-- The reciprocal-derivative moment over the contour's disk truncation is
bounded by the corresponding height-truncated BCF moment. -/
theorem bcfDiskReciprocalZetaDerivMoment_le (R : ℝ) :
    (∑ rho ∈ bcfTruncatedZeros R,
      1 / ‖deriv riemannZeta rho‖ ^ 2) ≤
      bcfReciprocalZetaDerivMoment |R| := by
  unfold bcfReciprocalZetaDerivMoment
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (bcfTruncatedZeros_subset_bcfZerosUpToHeight_abs R)
  intro rho _ _
  positivity

/-- The fourth-power geometric kernel occurring after the first
Cauchy--Schwarz step in BCF Lemma 3.  This is a finite sum for every height
cutoff, independently of any zero-counting asymptotic. -/
def bcfZeroKernelFourthMoment (s : ℂ) (T : ℝ) : ℝ :=
  ∑ rho ∈ bcfZerosUpToHeight T, (‖rho - s‖ ^ 4)⁻¹

/-- Cauchy--Schwarz for an arbitrary finite zero set.  The height-truncated
version in `Lemma3Finite` is the special case used for BCF's moment
hypothesis; this form is useful for the disk truncations of Lemma 2. -/
theorem bcf_reciprocalDeriv_cauchySchwarz_finset
    (U : Finset ℂ) (g : ℂ → ℝ) :
    (∑ rho ∈ U, (1 / ‖deriv riemannZeta rho‖) * g rho) ≤
      √(∑ rho ∈ U, 1 / ‖deriv riemannZeta rho‖ ^ 2) *
        √(∑ rho ∈ U, (g rho) ^ 2) := by
  simpa only [one_div, inv_pow] using
    Real.sum_mul_le_sqrt_mul_sqrt U
      (fun rho : ℂ ↦ (‖deriv riemannZeta rho‖)⁻¹) g

/-- The fully finite Lemma 3 bound for the disk truncation used by the
contour-shift residue sum.  It turns the contour cutoff into the same
height-moment factor used by the BCF hypothesis, leaving only the geometric
kernel square sum for zero-counting and partial summation. -/
theorem norm_bcfTruncatedSimpleZeroResidueSum_le
    (hsimple : ZeroSimplicityHypothesis)
    {N : ℕ} {s : ℂ} {R : ℝ}
    (hseparated : ∀ rho ∈ bcfTruncatedZeros R, rho ≠ s) :
    ‖bcfTruncatedSimpleZeroResidueSum N s R‖ ≤
      √(bcfReciprocalZetaDerivMoment |R|) *
        √(∑ rho ∈ bcfTruncatedZeros R,
          (bcfZeroResidueGeometry N s rho) ^ 2) := by
  calc
    ‖bcfTruncatedSimpleZeroResidueSum N s R‖ ≤
        ∑ rho ∈ bcfTruncatedZeros R, ‖bcfSimpleZeroResidue N s rho‖ := by
      unfold bcfTruncatedSimpleZeroResidueSum
      exact norm_sum_le _ _
    _ = ∑ rho ∈ bcfTruncatedZeros R,
        (1 / ‖deriv riemannZeta rho‖) * bcfZeroResidueGeometry N s rho := by
      apply Finset.sum_congr rfl
      intro rho hrho
      exact norm_bcfSimpleZeroResidue_eq_reciprocalDeriv_mul_geometry
        (hsimple.deriv_ne_zero
          (bcfTruncatedZeros_subset_bcfZerosUpToHeight_abs R hrho))
        (hseparated rho hrho)
    _ ≤ √(∑ rho ∈ bcfTruncatedZeros R,
          1 / ‖deriv riemannZeta rho‖ ^ 2) *
        √(∑ rho ∈ bcfTruncatedZeros R,
          (bcfZeroResidueGeometry N s rho) ^ 2) :=
      bcf_reciprocalDeriv_cauchySchwarz_finset _ _
    _ ≤ √(bcfReciprocalZetaDerivMoment |R|) *
        √(∑ rho ∈ bcfTruncatedZeros R,
          (bcfZeroResidueGeometry N s rho) ^ 2) := by
      apply mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt (bcfDiskReciprocalZetaDerivMoment_le R))
      exact Real.sqrt_nonneg _

/-- The global Riemann--von Mangoldt strength estimate needed by the BCF
argument.  It is an explicit future theorem target, rather than a hypothesis
silently attached to the formal development. -/
def BCFZeroCountingAsymptotic : Prop :=
  (fun T : ℝ ↦ (bcfZeroCount T : ℝ)) =O[atTop]
    fun T : ℝ ↦ (T + 1) * Real.log (T + 2)

/-- The output of the local zero-counting plus partial-summation argument.
This is the geometric-kernel estimate which must be combined with the
reciprocal-derivative moment bound in order to control the residue tails.

It is intentionally named as a target: a global count alone does not control
zeros near the moving point `s`; the classical proof needs the corresponding
local zero-count estimate. -/
def BCFGeometricKernelSquareBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, |s.re - 1 / 2| = ε →
        ∀ T : ℝ, 1 ≤ T →
          bcfZeroKernelFourthMoment s T ≤
            C * (Real.log (‖s‖ + 2) + Real.log (T + 2))

/-- The exact finite partial-summation identity used after discretizing a
height shell.  This makes the conversion from a shell count to an integral
available without reproving Abel summation in the H15 development. -/
theorem bcf_abel_partial_summation
    (c : ℕ → ℝ) (f : ℝ → ℝ) (m : ℕ)
    (hf_diff : ∀ t ∈ Set.Icc (0 : ℝ) m, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc (0 : ℝ) m)) :
    ∑ k ∈ Finset.Icc 0 m, f k * c k =
      f m * (∑ k ∈ Finset.Icc 0 m, c k) -
        ∫ t in Set.Ioc (0 : ℝ) m,
          deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k := by
  exact sum_mul_eq_sub_integral_mul' c m hf_diff hf_int

/-- The exact Cauchy-tail statement required to pass from finite disk
residue sums to the full nontrivial residue sum. -/
def BCFNontrivialResidueCauchy (N : ℕ) (s : ℂ) : Prop :=
  Cauchy (Filter.map (bcfTruncatedSimpleZeroResidueSum N s) atTop)

/-- Pack the nontrivial half of the residue-limit data used by global Lemma 2.
The trivial-zero contribution is intentionally kept separate: its convergence
uses a different, elementary estimate. -/
structure BCFNontrivialResidueLimitData (N : ℕ) (s : ℂ) where
  nontrivialLimit : ℂ
  nontrivial_tendsto :
    Tendsto (bcfTruncatedSimpleZeroResidueSum N s) atTop
      (𝓝 nontrivialLimit)

/-- In the complete space `ℂ`, a proved Cauchy estimate for the disk-truncated
nontrivial residue sums produces their exact infinite-residue limit. -/
theorem exists_bcfNontrivialResidueLimitData_of_cauchy
    {N : ℕ} {s : ℂ} (h : BCFNontrivialResidueCauchy N s) :
    Nonempty (BCFNontrivialResidueLimitData N s) := by
  rcases (cauchy_map_iff_exists_tendsto.mp h) with ⟨limit, hlimit⟩
  exact ⟨{ nontrivialLimit := limit, nontrivial_tendsto := hlimit }⟩

/-- Combine the nontrivial residue limit with an independently proved limit
for the trivial residues.  This is a construction, not an extra assumption. -/
def BCFNontrivialResidueLimitData.withTrivial
    {N : ℕ} {s : ℂ} (h : BCFNontrivialResidueLimitData N s)
    (trivialLimit : ℂ)
    (htrivial : Tendsto (bcfTruncatedTrivialZeroContribution N s) atTop
      (𝓝 trivialLimit)) :
    BCFResidueLimitData N s :=
  { nontrivialLimit := h.nontrivialLimit
    trivialLimit := trivialLimit
    nontrivial_tendsto := h.nontrivial_tendsto
    trivial_tendsto := htrivial }

/-- The infinite-residue portion of global Lemma 2 is now a direct assembly:
a finite contour witness, a Cauchy proof for the nontrivial residues, and the
elementary trivial-residue limit yield the closed-form identity. -/
theorem BCFContourShiftWitness.assembledLemma2_of_cauchy
    {N : ℕ} {s : ℂ} (hshift : BCFContourShiftWitness N s)
    (hCauchy : BCFNontrivialResidueCauchy N s)
    (trivialLimit : ℂ)
    (htrivial : Tendsto (bcfTruncatedTrivialZeroContribution N s) atTop
      (𝓝 trivialLimit)) :
    ∃ hlimits : BCFResidueLimitData N s,
      bcfDirichletPolynomial N s = hlimits.assembledLimit := by
  rcases exists_bcfNontrivialResidueLimitData_of_cauchy hCauchy with ⟨hnontrivial⟩
  let hlimits := hnontrivial.withTrivial trivialLimit htrivial
  exact ⟨hlimits, hshift.assembledLemma2 hlimits⟩

end

end NBMellinTools.H15BCF
