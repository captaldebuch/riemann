/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.ContourShift

/-!
# Conditional BCF formalization: global Lemma 2 assembly

This file proves the filter-theoretic assembly step for the simple-zero form
of BCF Lemma 2.  It separates the genuinely analytic work from the exact
limit algebra:

* `BCFContourShiftWitness` records a *finite* contour identity together with
  its error term tending to zero as both truncations tend to infinity;
* `BCFResidueLimitData` records the two separately convergent residue sums;
* the theorems below derive the existing global proposition
  `BCFLemma2SimpleZeroExpansion` and its closed-form limit.

No contour-shift equality is assumed globally.  Constructing a
`BCFContourShiftWitness` remains the outstanding analytic task: it requires a
deleted-disk rectangle argument and estimates for the horizontal and shifted
vertical contour edges.  Once constructed, the global assembly and limit
convergence are now proved rather than left informal.

Primary source: S. Bettin, J. B. Conrey, and D. W. Farmer,
*An optimal choice of Dirichlet polynomials for the Nyman--Beurling
criterion*, arXiv:1211.5191, Lemma 2.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped Topology
open Complex Filter

/-- A finite contour-shift certificate for the simple-zero BCF expansion.

For each pair `(R, M)`, `finiteIdentity` is the result of shifting a finite
contour, including every boundary and deleted-disk contribution in `error`.
The second field is the precise statement that those remaining contributions
vanish as both truncation parameters tend to infinity. -/
structure BCFContourShiftWitness (N : ℕ) (s : ℂ) where
  error : ℝ × ℕ → ℂ
  finiteIdentity : ∀ p : ℝ × ℕ,
  /- The local circle at the order-two pole `z = s` has already been
  normalized to `bcfLemma2MainTerm` in `OuterBoundary.lean`; the remaining
  finite identity is therefore precisely the deleted-rectangle/outer-edge
  calculation. -/
  bcfDirichletPolynomial N s =
      bcfLemma2TruncatedRHS N s p.1 p.2 + error p
  error_tendsto_zero :
    Tendsto error (atTop ×ˢ atTop) (𝓝 0)

/-- The pair of independently convergent residue sums occurring in BCF
Lemma 2.  The first sum is over disk-truncated distinct nontrivial zeros; the
second is the direct trivial-zero residue sum. -/
structure BCFResidueLimitData (N : ℕ) (s : ℂ) where
  nontrivialLimit : ℂ
  trivialLimit : ℂ
  nontrivial_tendsto :
    Tendsto (bcfTruncatedSimpleZeroResidueSum N s) atTop
      (𝓝 nontrivialLimit)
  trivial_tendsto :
    Tendsto (bcfTruncatedTrivialZeroContribution N s) atTop
      (𝓝 trivialLimit)

/-- The closed-form limit of the finite BCF right-hand sides, provided the
two residue sums converge separately. -/
def BCFResidueLimitData.assembledLimit
    {N : ℕ} {s : ℂ} (h : BCFResidueLimitData N s) : ℂ :=
  bcfLemma2MainTerm N s +
    (Real.log N : ℂ)⁻¹ * h.nontrivialLimit +
    (Real.log N : ℂ)⁻¹ * h.trivialLimit

/-- Separate convergence of the nontrivial and trivial residue sums gives
two-parameter convergence of the finite BCF Lemma 2 right-hand side. -/
theorem BCFResidueLimitData.tendsto_truncatedRHS
    {N : ℕ} {s : ℂ} (h : BCFResidueLimitData N s) :
    Tendsto
      (fun p : ℝ × ℕ ↦ bcfLemma2TruncatedRHS N s p.1 p.2)
      (atTop ×ˢ atTop) (𝓝 h.assembledLimit) := by
  have hnontrivial :
      Tendsto
        (fun p : ℝ × ℕ ↦ bcfTruncatedSimpleZeroResidueSum N s p.1)
        (atTop ×ˢ atTop) (𝓝 h.nontrivialLimit) :=
    h.nontrivial_tendsto.comp tendsto_fst
  have htrivial :
      Tendsto
        (fun p : ℝ × ℕ ↦ bcfTruncatedTrivialZeroContribution N s p.2)
        (atTop ×ˢ atTop) (𝓝 h.trivialLimit) :=
    h.trivial_tendsto.comp tendsto_snd
  have hmain :
      Tendsto (fun _ : ℝ × ℕ ↦ bcfLemma2MainTerm N s)
        (atTop ×ˢ atTop) (𝓝 (bcfLemma2MainTerm N s)) :=
    tendsto_const_nhds
  have hscaledNontrivial :
      Tendsto
        (fun p : ℝ × ℕ ↦
          (Real.log N : ℂ)⁻¹ * bcfTruncatedSimpleZeroResidueSum N s p.1)
        (atTop ×ˢ atTop) (𝓝 ((Real.log N : ℂ)⁻¹ * h.nontrivialLimit)) :=
    tendsto_const_nhds.mul hnontrivial
  have hscaledTrivial :
      Tendsto
        (fun p : ℝ × ℕ ↦
          (Real.log N : ℂ)⁻¹ * bcfTruncatedTrivialZeroContribution N s p.2)
        (atTop ×ˢ atTop) (𝓝 ((Real.log N : ℂ)⁻¹ * h.trivialLimit)) :=
    tendsto_const_nhds.mul htrivial
  change Tendsto
    (fun p : ℝ × ℕ ↦
      bcfLemma2MainTerm N s +
        (Real.log N : ℂ)⁻¹ * bcfTruncatedSimpleZeroResidueSum N s p.1 +
        (Real.log N : ℂ)⁻¹ * bcfTruncatedTrivialZeroContribution N s p.2)
    (atTop ×ˢ atTop)
    (𝓝 (bcfLemma2MainTerm N s +
      (Real.log N : ℂ)⁻¹ * h.nontrivialLimit +
      (Real.log N : ℂ)⁻¹ * h.trivialLimit))
  convert (hmain.add (hscaledNontrivial.add hscaledTrivial)) using 1 <;> ring_nf

/-- A finite contour-shift witness proves the global simple-zero form of BCF
Lemma 2, with the exact product-filter convergence convention fixed in
`ContourShift.lean`. -/
theorem BCFContourShiftWitness.globalLemma2
    {N : ℕ} {s : ℂ} (h : BCFContourShiftWitness N s) :
    BCFLemma2SimpleZeroExpansion N s := by
  unfold BCFLemma2SimpleZeroExpansion
  have hrewrite :
      (fun p : ℝ × ℕ ↦ bcfLemma2TruncatedRHS N s p.1 p.2) =
        fun p ↦ bcfDirichletPolynomial N s - h.error p := by
    funext p
    rw [h.finiteIdentity p]
    ring
  rw [hrewrite]
  simpa using (tendsto_const_nhds.sub h.error_tendsto_zero)

/-- Given convergent residue sums, the global Lemma 2 expansion is equivalent
to its closed-form limiting equality. -/
theorem bcfLemma2SimpleZeroExpansion_iff_assembledLimit
    {N : ℕ} {s : ℂ} (h : BCFResidueLimitData N s) :
    BCFLemma2SimpleZeroExpansion N s ↔
      bcfDirichletPolynomial N s = h.assembledLimit := by
  constructor
  · intro hglobal
    unfold BCFLemma2SimpleZeroExpansion at hglobal
    exact tendsto_nhds_unique hglobal h.tendsto_truncatedRHS
  · intro hvalue
    unfold BCFLemma2SimpleZeroExpansion
    simpa [hvalue] using h.tendsto_truncatedRHS

/-- Combining a finite contour witness with residue-limit data yields the
closed-form simple-zero BCF Lemma 2 identity. -/
theorem BCFContourShiftWitness.assembledLemma2
    {N : ℕ} {s : ℂ} (hshift : BCFContourShiftWitness N s)
    (hlimits : BCFResidueLimitData N s) :
    bcfDirichletPolynomial N s = hlimits.assembledLimit :=
  (bcfLemma2SimpleZeroExpansion_iff_assembledLimit hlimits).mp
    hshift.globalLemma2

end

end NBMellinTools.H15BCF
