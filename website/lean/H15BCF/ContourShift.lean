/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.LSeries.ZetaZeros
import NBMellinTools.H15BCF.MellinPlancherel

/-!
# Conditional BCF formalization: contour and residue data

This file provides the exact finite and local infrastructure needed for the
contour shift in Lemma 2 of Bettin--Conrey--Farmer.  In particular it defines
the Perron kernel, its shifted zero kernel, compact truncations of the
nontrivial zeta-zero set, vertical contour integrals, and the residue at a
simple zeta zero.

The local residue theorem is proved directly from the derivative of zeta.  It
does not assume RH.  Simplicity is needed only to replace the abstract residue
at a zero by the familiar reciprocal-derivative formula.

The global infinite contour shift is deliberately not asserted here: Mathlib
does not currently expose a general residue theorem with the convergence and
improper-contour API needed by BCF Lemma 2.  The definitions below make that
remaining dependency precise without introducing an axiom or a placeholder.

Primary source: S. Bettin, J. B. Conrey, and D. W. Farmer,
*An optimal choice of Dirichlet polynomials for the Nyman--Beurling
criterion*, arXiv:1211.5191, Lemma 2.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators Interval Topology
open Complex Filter MeasureTheory Metric Set

/-- The complex power `N^z` occurring in the BCF Perron kernel. -/
def bcfNPow (N : ℕ) (z : ℂ) : ℂ :=
  (N : ℂ) ^ z

/-- The BCF Perron kernel
`N^w / (ζ(s+w) w²)` on the initial vertical line. -/
def bcfPerronKernel (N : ℕ) (s w : ℂ) : ℂ :=
  bcfNPow N w / (riemannZeta (s + w) * w ^ 2)

/-- The same kernel after the change of variables `z = s + w`.  Its poles at
nontrivial zeros of zeta give the zero-residue term in BCF Lemma 2. -/
def bcfShiftedZeroKernel (N : ℕ) (s z : ℂ) : ℂ :=
  bcfNPow N (z - s) / (riemannZeta z * (z - s) ^ 2)

/-- Changing variables from `w` to `z = s + w` gives the shifted zero kernel. -/
theorem bcfPerronKernel_sub (N : ℕ) (s z : ℂ) :
    bcfPerronKernel N s (z - s) = bcfShiftedZeroKernel N s z := by
  simp [bcfPerronKernel, bcfShiftedZeroKernel]

/-- The distinct nontrivial zeta zeros in the open critical strip.

BCF Lemma 2 sums over distinct zeros and takes the genuine residue at each
zero; it does not repeat a zero according to multiplicity. -/
def bcfNontrivialZetaZeros : Set ℂ :=
  {z | z ∈ riemannZetaZeros ∧ 0 < z.re ∧ z.re < 1}

theorem mem_bcfNontrivialZetaZeros {z : ℂ} :
    z ∈ bcfNontrivialZetaZeros ↔
      riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 := by
  rfl

/-- Nontrivial zeta zeros in the closed disk of radius `R`. -/
def bcfZerosInDisk (R : ℝ) : Set ℂ :=
  closedBall 0 R ∩ bcfNontrivialZetaZeros

/-- Every disk contains only finitely many nontrivial zeta zeros. -/
theorem bcfZerosInDisk_finite (R : ℝ) :
    (bcfZerosInDisk R).Finite := by
  have hcompact : IsCompact (closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
  apply (IsCompact.inter_riemannZetaZeros_finite hcompact).subset
  intro z hz
  exact ⟨hz.1, hz.2.1⟩

/-- The finite set used for a radius-truncated zero sum. -/
def bcfTruncatedZeros (R : ℝ) : Finset ℂ :=
  (bcfZerosInDisk_finite R).toFinset

@[simp]
theorem mem_bcfTruncatedZeros {R : ℝ} {z : ℂ} :
    z ∈ bcfTruncatedZeros R ↔
      z ∈ closedBall (0 : ℂ) R ∧
        riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 := by
  simp [bcfTruncatedZeros, bcfZerosInDisk, mem_bcfNontrivialZetaZeros]

/-- A finite vertical segment of the BCF Perron contour, parametrized upward.
The factor `I` is the derivative `dw/dt`. -/
def bcfTruncatedVerticalIntegral
    (N : ℕ) (s : ℂ) (c T : ℝ) : ℂ :=
  ∫ t in (-T)..T,
    bcfPerronKernel N s ((c : ℂ) + (t : ℂ) * I) * I

/-- The oriented boundary integral of the Perron kernel around the rectangle
with opposite corners `z` and `w`.  This is the convention used by Mathlib's
rectangle form of Cauchy--Goursat. -/
def bcfRectangleBoundaryIntegral
    (N : ℕ) (s z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re,
      bcfPerronKernel N s (x + z.im * I)) -
    (∫ x : ℝ in z.re..w.re,
      bcfPerronKernel N s (x + w.im * I)) +
    I * (∫ y : ℝ in z.im..w.im,
      bcfPerronKernel N s (w.re + y * I)) -
    I * (∫ y : ℝ in z.im..w.im,
      bcfPerronKernel N s (z.re + y * I))

/-- A pole-free rectangular BCF contour has zero boundary integral.  This is
the exact Cauchy--Goursat component used when a shifted contour is decomposed
into small pole circles and a holomorphic remainder. -/
theorem bcfRectangleBoundaryIntegral_eq_zero
    {N : ℕ} {s z w : ℂ}
    (h : DifferentiableOn ℂ (bcfPerronKernel N s)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    bcfRectangleBoundaryIntegral N s z w = 0 := by
  simpa [bcfRectangleBoundaryIntegral, smul_eq_mul] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (bcfPerronKernel N s) z w h

/-- A local simple-pole residue expressed by its defining punctured limit.

This deliberately has `SimplePole` in its name: for a pole of higher order,
the limit below need not exist and is not the general Laurent residue. -/
def HasSimplePoleResidueAt (f : ℂ → ℂ) (rho residue : ℂ) : Prop :=
  Tendsto (fun z ↦ (z - rho) * f z) (𝓝[≠] rho) (𝓝 residue)

/-- A punctured-limit residue, together with holomorphy away from its center,
computes the integral around any admissible small circle. -/
theorem circleIntegral_eq_two_pi_I_mul_of_hasSimplePoleResidueAt
    {f : ℂ → ℂ} {rho residue : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hc : ContinuousOn (fun z ↦ (z - rho) * f z)
      (closedBall rho R \ {rho}))
    (hd : ∀ z ∈ ball rho R \ {rho},
      DifferentiableAt ℂ (fun w ↦ (w - rho) * f w) z)
    (hres : HasSimplePoleResidueAt f rho residue) :
    (∮ z in C(rho, R), f z) = 2 * Real.pi * I * residue := by
  have hregularized :=
    Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
      hR (s := (∅ : Set ℂ)) countable_empty hc (by simpa using hd) hres
  calc
    (∮ z in C(rho, R), f z) =
        ∮ z in C(rho, R), (z - rho)⁻¹ • ((z - rho) * f z) := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      have hzr : z ≠ rho := by
        intro h
        subst z
        rw [mem_sphere, dist_self] at hz
        exact hR.ne' hz.symm
      simp only [smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hzr), one_mul]
    _ = 2 * Real.pi * I * residue := by
      simpa [smul_eq_mul] using hregularized

/-- At a simple zero `rho` of zeta, the reciprocal of zeta has residue
`1 / ζ'(rho)`. -/
theorem hasSimplePoleResidueAt_inv_riemannZeta
    {rho : ℂ} (hrho_one : rho ≠ 1)
    (hrho_zero : riemannZeta rho = 0)
    (hrho_simple : deriv riemannZeta rho ≠ 0) :
    HasSimplePoleResidueAt (fun z ↦ (riemannZeta z)⁻¹) rho
      (deriv riemannZeta rho)⁻¹ := by
  have hzeta : HasDerivAt riemannZeta (deriv riemannZeta rho) rho :=
    (differentiableAt_riemannZeta hrho_one).hasDerivAt
  have hslope :
      Tendsto (fun z ↦ (slope riemannZeta rho z)⁻¹) (𝓝[≠] rho)
        (𝓝 (deriv riemannZeta rho)⁻¹) :=
    hzeta.tendsto_slope.inv₀ hrho_simple
  apply hslope.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzr : z ≠ rho := by simpa using hz
  simp [slope, hrho_zero, mul_comm]

/-- The explicit BCF residue at a simple nontrivial zero. -/
def bcfSimpleZeroResidue (N : ℕ) (s rho : ℂ) : ℂ :=
  bcfNPow N (rho - s) /
    (deriv riemannZeta rho * (rho - s) ^ 2)

/-- The radius-truncated simple-zero residue sum.  This is a genuine finite
sum and therefore has no hidden convergence convention. -/
def bcfTruncatedSimpleZeroResidueSum
    (N : ℕ) (s : ℂ) (R : ℝ) : ℂ :=
  ∑ rho ∈ bcfTruncatedZeros R, bcfSimpleZeroResidue N s rho

/-- The residue contribution of the trivial zeta zero `-2(n+1)`, written in
the form appearing directly after the BCF contour shift. -/
def bcfTrivialZeroResidueTerm (N : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  bcfNPow N (-2 * ((n + 1 : ℕ) : ℂ) - s) /
    (deriv riemannZeta (-2 * ((n + 1 : ℕ) : ℂ)) *
      (2 * ((n + 1 : ℕ) : ℂ) + s) ^ 2)

/-- The first `M` trivial-zero residues. -/
def bcfTruncatedTrivialZeroContribution
    (N : ℕ) (s : ℂ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.range M, bcfTrivialZeroResidueTerm N s n

/-- The regular main term of BCF Lemma 2. -/
def bcfLemma2MainTerm (N : ℕ) (s : ℂ) : ℂ :=
  (riemannZeta s)⁻¹ *
    (1 - (Real.log N : ℂ)⁻¹ * deriv riemannZeta s / riemannZeta s)

/-- A completely finite right-hand side for truncating BCF Lemma 2.  The
global theorem will identify the polynomial with the limit of this expression
as the zero radius and number of trivial-zero terms tend to infinity. -/
def bcfLemma2TruncatedRHS
    (N : ℕ) (s : ℂ) (R : ℝ) (M : ℕ) : ℂ :=
  bcfLemma2MainTerm N s +
    (Real.log N : ℂ)⁻¹ * bcfTruncatedSimpleZeroResidueSum N s R +
    (Real.log N : ℂ)⁻¹ * bcfTruncatedTrivialZeroContribution N s M

/-- The exact improper-integral statement from which BCF begin Lemma 2:
`V_N(s)` is the limit of the Perron integral on `re w = 2`.

It is a named proposition, not an assumption or theorem. -/
def BCFPerronRepresentation (N : ℕ) (s : ℂ) : Prop :=
  Tendsto
    (fun T : ℝ ↦
      (Real.log N : ℂ)⁻¹ * (2 * Real.pi * I)⁻¹ *
        bcfTruncatedVerticalIntegral N s 2 T)
    atTop (𝓝 (bcfDirichletPolynomial N s))

/-- A precise convergence convention for the simple-zero version of BCF
Lemma 2: take disk-truncated distinct zero residues and truncated trivial-zero
residues independently to infinity.

The proposition is the remaining global Phase 4 theorem.  It is intentionally
separate from the local residue results proved in this file. -/
def BCFLemma2SimpleZeroExpansion (N : ℕ) (s : ℂ) : Prop :=
  Tendsto
    (fun p : ℝ × ℕ ↦ bcfLemma2TruncatedRHS N s p.1 p.2)
    (atTop ×ˢ atTop) (𝓝 (bcfDirichletPolynomial N s))

/-- Away from the zeta zeros, `s`, and the pole `1` of zeta, the shifted BCF
kernel is holomorphic. -/
theorem bcfShiftedZeroKernel_differentiableAt
    {N : ℕ} {s z : ℂ}
    (hN : N ≠ 0) (hz_one : z ≠ 1)
    (hz_zero : riemannZeta z ≠ 0) (hz_s : z ≠ s) :
    DifferentiableAt ℂ (bcfShiftedZeroKernel N s) z := by
  have hpow :
      DifferentiableAt ℂ (fun w ↦ bcfNPow N (w - s)) z := by
    unfold bcfNPow
    exact (differentiableAt_id.sub_const s).const_cpow
      (Or.inl (by exact_mod_cast hN))
  have hden :
      DifferentiableAt ℂ
        (fun w ↦ riemannZeta w * (w - s) ^ 2) z :=
    (differentiableAt_riemannZeta hz_one).mul
      ((differentiableAt_id.sub_const s).pow 2)
  exact hpow.div hden
    (mul_ne_zero hz_zero (pow_ne_zero 2 (sub_ne_zero.mpr hz_s)))

/-- The shifted BCF kernel has the expected reciprocal-derivative residue at
a simple zeta zero distinct from `s`. -/
theorem bcfShiftedZeroKernel_hasSimplePoleResidueAt
    {N : ℕ} {s rho : ℂ}
    (hN : N ≠ 0) (hrho_one : rho ≠ 1)
    (hrho_zero : riemannZeta rho = 0)
    (hrho_simple : deriv riemannZeta rho ≠ 0)
    (hrho_s : rho ≠ s) :
    HasSimplePoleResidueAt (bcfShiftedZeroKernel N s) rho
      (bcfSimpleZeroResidue N s rho) := by
  have hpow :
      Tendsto (fun z ↦ bcfNPow N (z - s)) (𝓝[≠] rho)
        (𝓝 (bcfNPow N (rho - s))) :=
    ((continuousAt_const_cpow (by exact_mod_cast hN)).comp
      (continuousAt_id.sub continuousAt_const)).tendsto.mono_left nhdsWithin_le_nhds
  have hden :
      Tendsto (fun z : ℂ ↦ ((z - s) ^ 2)⁻¹) (𝓝[≠] rho)
        (𝓝 (((rho - s) ^ 2)⁻¹)) :=
    (((continuousAt_id.sub continuousAt_const).pow 2).inv₀
      (pow_ne_zero 2 (sub_ne_zero.mpr hrho_s))).tendsto.mono_left nhdsWithin_le_nhds
  have hzeta := hasSimplePoleResidueAt_inv_riemannZeta
    hrho_one hrho_zero hrho_simple
  have hprod := (hpow.mul hden).mul hzeta
  unfold HasSimplePoleResidueAt
  rw [show bcfSimpleZeroResidue N s rho =
      bcfNPow N (rho - s) * ((rho - s) ^ 2)⁻¹ *
        (deriv riemannZeta rho)⁻¹ by
    simp only [bcfSimpleZeroResidue, div_eq_mul_inv, mul_inv_rev]
    ring]
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  simp only [bcfShiftedZeroKernel, div_eq_mul_inv, mul_inv_rev]
  ring

/-- If a closed disk isolates a simple zeta zero from every other pole of the
shifted BCF kernel, its circle integral is exactly `2πi` times the explicit
BCF residue. -/
theorem bcfShiftedZeroKernel_circleIntegral
    {N : ℕ} {s rho : ℂ} {R : ℝ}
    (hR : 0 < R) (hN : N ≠ 0)
    (hrho_one : rho ≠ 1)
    (hrho_zero : riemannZeta rho = 0)
    (hrho_simple : deriv riemannZeta rho ≠ 0)
    (hrho_s : rho ≠ s)
    (hone : ∀ z ∈ closedBall rho R, z ≠ rho → z ≠ 1)
    (hzero : ∀ z ∈ closedBall rho R, z ≠ rho → riemannZeta z ≠ 0)
    (hs : ∀ z ∈ closedBall rho R, z ≠ rho → z ≠ s) :
    (∮ z in C(rho, R), bcfShiftedZeroKernel N s z) =
      2 * Real.pi * I * bcfSimpleZeroResidue N s rho := by
  apply circleIntegral_eq_two_pi_I_mul_of_hasSimplePoleResidueAt hR
  · intro z hz
    have hzr : z ≠ rho := by simpa using hz.2
    exact ((continuousAt_id.sub continuousAt_const).mul
      (bcfShiftedZeroKernel_differentiableAt hN
        (hone z hz.1 hzr) (hzero z hz.1 hzr) (hs z hz.1 hzr)).continuousAt).continuousWithinAt
  · intro z hz
    have hzr : z ≠ rho := by simpa using hz.2
    have hzclosed : z ∈ closedBall rho R := ball_subset_closedBall hz.1
    exact (differentiableAt_id.sub_const rho).mul
      (bcfShiftedZeroKernel_differentiableAt hN
        (hone z hzclosed hzr) (hzero z hzclosed hzr) (hs z hzclosed hzr))
  · exact bcfShiftedZeroKernel_hasSimplePoleResidueAt
      hN hrho_one hrho_zero hrho_simple hrho_s

end

end NBMellinTools.H15BCF
