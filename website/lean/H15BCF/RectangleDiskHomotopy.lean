/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.FiniteDeletedRectangle
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Smooth-strip Cauchy--Goursat assembly

This file supplies the analytic assembly required for a polygonal
rectangle-to-circle deformation.  Mathlib's homotopy-invariance theorem for
curve integrals requires a `C²` homotopy.  Hence a rectangle boundary cannot
be fed to it as a single contour: its four corners are not `C¹`.

The correct interface is a finite collection of smooth strips.  Each strip
compares one outer boundary path to one inner path.  Its two radial side paths
occur with opposite algebraic roles in adjacent strips; summing the four
strip identities cancels them exactly.

The remaining geometric task is deliberately separate: construct four
explicit `SmoothCauchyStrip`s filling the region between a given axis-aligned
rectangle and a contained disk, and identify their outer and inner sums with
`rectangleBoundaryIntegral` and `circleIntegral`.  No such construction is
postulated here.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped unitInterval Topology
open Complex Filter MeasureTheory Set

/-- Data for one smooth strip in a contour deformation.  The fields are the
precise hypotheses of Mathlib's `C²` homotopy Cauchy theorem, together with
the two oriented side paths of the strip. -/
structure SmoothCauchyStrip
    (t : Set ℂ) (ω : ℂ → ℂ →L[ℂ] ℂ)
    (dω : ℂ → ℂ →L[ℝ] ℂ →L[ℂ] ℂ) where
  outerStart : ℂ
  outerEnd : ℂ
  innerStart : ℂ
  innerEnd : ℂ
  outer : Path outerStart outerEnd
  inner : Path innerStart innerEnd
  startSide : Path outerStart innerStart
  endSide : Path outerEnd innerEnd
  homotopy : outer.toContinuousMap.Homotopy inner.toContinuousMap
  startSideIntegral :
    (∫ᶜ z in homotopy.evalAt 0, ω z) = ∫ᶜ z in startSide, ω z
  endSideIntegral :
    (∫ᶜ z in homotopy.evalAt 1, ω z) = ∫ᶜ z in endSide, ω z
  mapsTo : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, homotopy (a, b) ∈ t
  hasFDerivWithinAt : ∀ x ∈ t, HasFDerivWithinAt ω (dω x) t x
  continuousOn : ContinuousOn ω (closure t)
  derivative_symmetric : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x,
    ∀ v ∈ tangentConeAt ℝ t x, dω x u v = dω x v u
  contDiff : ContDiffOn ℝ 2
    (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (homotopy.extend xy.1) xy.2)
    (Icc 0 1)

/-- The Cauchy identity carried by one smooth strip.  This is Mathlib's
homotopy theorem with its two transverse sides made explicit. -/
theorem SmoothCauchyStrip.curveIntegral_outer_add_endSide_eq_inner_add_startSide
    {t : Set ℂ} {ω : ℂ → ℂ →L[ℂ] ℂ}
    {dω : ℂ → ℂ →L[ℝ] ℂ →L[ℂ] ℂ}
    (S : SmoothCauchyStrip t ω dω) :
    (∫ᶜ z in S.outer, ω z) + ∫ᶜ z in S.endSide, ω z =
      (∫ᶜ z in S.inner, ω z) + ∫ᶜ z in S.startSide, ω z := by
  calc
    (∫ᶜ z in S.outer, ω z) + ∫ᶜ z in S.endSide, ω z =
        (∫ᶜ z in S.outer, ω z) + ∫ᶜ z in S.homotopy.evalAt 1, ω z := by
      rw [S.endSideIntegral]
    _ = (∫ᶜ z in S.inner, ω z) + ∫ᶜ z in S.homotopy.evalAt 0, ω z :=
      S.homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
        S.mapsTo S.hasFDerivWithinAt S.continuousOn S.derivative_symmetric S.contDiff
    _ = (∫ᶜ z in S.inner, ω z) + ∫ᶜ z in S.startSide, ω z := by
      rw [S.startSideIntegral]

/-- Algebraic cancellation of the side integrals in a finite cyclic family
of strips.  `e` is the cyclic permutation taking the end side of one strip
to the start side of its successor. -/
theorem sum_eq_of_cyclic_strip_identities
    (e : Equiv.Perm (Fin 4))
    (outer inner side : Fin 4 → ℂ)
    (hstrip : ∀ i, outer i + side (e i) = inner i + side i) :
    (∑ i, outer i) = ∑ i, inner i := by
  calc
    (∑ i, outer i) =
        (∑ i, outer i) + (∑ i, side (e i)) - ∑ i, side i := by
      rw [Equiv.sum_comp e side]
      ring
    _ = (∑ i, (outer i + side (e i))) - ∑ i, side i := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i, (inner i + side i)) - ∑ i, side i := by
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ hstrip i
    _ = ∑ i, inner i := by
      rw [Finset.sum_add_distrib]
      ring

/-- **Finite smooth-strip Cauchy--Goursat.**  When the end side of each strip
is the start side of the next one, the total outer curve integral equals the
total inner curve integral.  This is the analytic core of the
rectangle-to-disk comparison; it contains no assumptions about the special
BCF kernel. -/
theorem sum_curveIntegral_outer_eq_sum_curveIntegral_inner_of_smooth_strips
    {t : Set ℂ} {ω : ℂ → ℂ →L[ℂ] ℂ}
    {dω : ℂ → ℂ →L[ℝ] ℂ →L[ℂ] ℂ}
    (e : Equiv.Perm (Fin 4)) (S : Fin 4 → SmoothCauchyStrip t ω dω)
    (side : Fin 4 → ℂ)
    (hstart : ∀ i, (∫ᶜ z in (S i).startSide, ω z) = side i)
    (hend : ∀ i, (∫ᶜ z in (S i).endSide, ω z) = side (e i)) :
    (∑ i, ∫ᶜ z in (S i).outer, ω z) =
      ∑ i, ∫ᶜ z in (S i).inner, ω z := by
  apply sum_eq_of_cyclic_strip_identities e
    (fun i ↦ ∫ᶜ z in (S i).outer, ω z)
    (fun i ↦ ∫ᶜ z in (S i).inner, ω z) side
  intro i
  rw [← hend i, ← hstart i]
  exact (S i).curveIntegral_outer_add_endSide_eq_inner_add_startSide

/-- Equality passes to limits along the natural-number approximation filter.
This is the topological step turning exact identities for smooth contours into
an exact identity for their limiting (possibly polygonal) contours. -/
theorem eq_of_forall_eq_of_tendsto_atTop
    {outer inner : ℕ → ℂ} {outerLimit innerLimit : ℂ}
    (hEq : ∀ n, outer n = inner n)
    (houter : Tendsto outer atTop (𝓝 outerLimit))
    (hinner : Tendsto inner atTop (𝓝 innerLimit)) :
    outerLimit = innerLimit :=
  tendsto_nhds_unique houter (hinner.congr fun n ↦ (hEq n).symm)

/-- **Rectangle-to-disk limit bridge.**  Suppose four smooth-strip
deformations give equal outer and inner boundary integrals at every stage,
and these sums converge respectively to the project's rectangular boundary
integral and to the circle integral.  Then the two exact boundary integrals
are equal.

The hypotheses isolate only the two genuine analytic approximation estimates:
the theorem itself contains no geometric axiom or unproved contour equality. -/
theorem rectangleBoundaryIntegral_eq_circleIntegral_of_smooth_strip_approximation
    {t : Set ℂ} {ω : ℂ → ℂ →L[ℂ] ℂ}
    {dω : ℂ → ℂ →L[ℝ] ℂ →L[ℂ] ℂ}
    {f : ℂ → ℂ} {z w c : ℂ} {r : ℝ}
    (e : Equiv.Perm (Fin 4))
    (S : ℕ → Fin 4 → SmoothCauchyStrip t ω dω)
    (side : ℕ → Fin 4 → ℂ)
    (hstart : ∀ n i, (∫ᶜ u in (S n i).startSide, ω u) = side n i)
    (hend : ∀ n i, (∫ᶜ u in (S n i).endSide, ω u) = side n (e i))
    (houter : Tendsto (fun n ↦ ∑ i, ∫ᶜ u in (S n i).outer, ω u)
      atTop (𝓝 (rectangleBoundaryIntegral f z w)))
    (hinner : Tendsto (fun n ↦ ∑ i, ∫ᶜ u in (S n i).inner, ω u)
      atTop (𝓝 (∮ u in C(c, r), f u))) :
    rectangleBoundaryIntegral f z w = ∮ u in C(c, r), f u := by
  apply eq_of_forall_eq_of_tendsto_atTop _ houter hinner
  intro n
  exact sum_curveIntegral_outer_eq_sum_curveIntegral_inner_of_smooth_strips
    e (S n) (side n) (hstart n) (hend n)

end

end NBMellinTools.H15BCF
