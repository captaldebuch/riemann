/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.OuterBoundary

/-!
# Cauchy--Goursat infrastructure for finite deleted rectangles

This file begins the geometric foundation needed by the BCF contour shift.
Mathlib provides Cauchy--Goursat for one pole-free rectangle.  The first
ingredient for a finite deleted-rectangle theorem is an exact subdivision
identity: cutting a rectangle by a vertical or horizontal grid line replaces
its boundary integral by the sum of the two smaller boundary integrals, with
the shared edge cancelling by orientation.

The subsequent finite-grid induction and the comparison between a rectangular
hole and a circular hole remain separate work.  In particular, an annulus
theorem cannot by itself make that comparison, because a rectangle minus a
disk is not an annulus.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped Interval Topology
open Complex MeasureTheory intervalIntegral

/-- The counterclockwise boundary integral of an axis-aligned rectangle with
opposite corners `z` and `w`.  It is the generic form of the BCF Perron
rectangle boundary integral. -/
def rectangleBoundaryIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) -
    (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
        I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- The BCF-specific rectangle boundary is the generic boundary integral of
the Perron kernel. -/
theorem bcfRectangleBoundaryIntegral_eq_rectangleBoundaryIntegral
    (N : ℕ) (s z w : ℂ) :
    bcfRectangleBoundaryIntegral N s z w =
      rectangleBoundaryIntegral (bcfPerronKernel N s) z w := by
  rfl

/-- Cauchy--Goursat for the generic rectangle boundary functional.  This is
the cell-level theorem used after a grid avoids all deleted disks. -/
theorem rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    {f : ℂ → ℂ} {z w : ℂ}
    (h : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    rectangleBoundaryIntegral f z w = 0 := by
  simpa [rectangleBoundaryIntegral, smul_eq_mul] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w h

/-- Cutting a rectangle by the vertical line `re z = u` is exactly additive.
The two integrals along the new internal edge occur with opposite signs and
cancel. -/
theorem rectangleBoundaryIntegral_vertical_split
    (f : ℂ → ℂ) (z w : ℂ) (u : ℝ)
    (hbottom_left : IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re u)
    (hbottom_right : IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume u w.re)
    (htop_left : IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re u)
    (htop_right : IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume u w.re) :
    rectangleBoundaryIntegral f z w =
      rectangleBoundaryIntegral f z ((u : ℂ) + w.im * I) +
        rectangleBoundaryIntegral f ((u : ℂ) + z.im * I) w := by
  unfold rectangleBoundaryIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals hbottom_left hbottom_right,
    ← intervalIntegral.integral_add_adjacent_intervals htop_left htop_right]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring_nf
  have hbottom_right :
      (∫ x : ℝ in u..w.re, f ((z.im : ℂ) * I + x)) =
        ∫ x : ℝ in u..w.re, f (x + (z.im : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    change f ((z.im : ℂ) * I + x) = f (x + (z.im : ℂ) * I)
    exact congrArg f (add_comm _ _)
  have hbottom_left :
      (∫ x : ℝ in z.re..u, f ((z.im : ℂ) * I + x)) =
        ∫ x : ℝ in z.re..u, f (x + (z.im : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    change f ((z.im : ℂ) * I + x) = f (x + (z.im : ℂ) * I)
    exact congrArg f (add_comm _ _)
  have htop_left :
      (∫ x : ℝ in z.re..u, f (I * (w.im : ℂ) + x)) =
        ∫ x : ℝ in z.re..u, f (x + (w.im : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    change f (I * (w.im : ℂ) + x) = f (x + (w.im : ℂ) * I)
    apply congrArg f
    calc
      I * (w.im : ℂ) + x = (w.im : ℂ) * I + x := by rw [mul_comm]
      _ = x + (w.im : ℂ) * I := add_comm _ _
  have htop_right :
      (∫ x : ℝ in u..w.re, f (I * (w.im : ℂ) + x)) =
        ∫ x : ℝ in u..w.re, f (x + (w.im : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    change f (I * (w.im : ℂ) + x) = f (x + (w.im : ℂ) * I)
    apply congrArg f
    calc
      I * (w.im : ℂ) + x = (w.im : ℂ) * I + x := by rw [mul_comm]
      _ = x + (w.im : ℂ) * I := add_comm _ _
  rw [hbottom_right, hbottom_left, htop_left, htop_right]
  ring

/-- Cutting a rectangle by the horizontal line `im z = v` is exactly
additive.  As in the vertical case, the two orientations of the new internal
edge cancel. -/
theorem rectangleBoundaryIntegral_horizontal_split
    (f : ℂ → ℂ) (z w : ℂ) (v : ℝ)
    (hleft_lower : IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im v)
    (hleft_upper : IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume v w.im)
    (hright_lower : IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im v)
    (hright_upper : IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume v w.im) :
    rectangleBoundaryIntegral f z w =
      rectangleBoundaryIntegral f z ((w.re : ℂ) + v * I) +
        rectangleBoundaryIntegral f ((z.re : ℂ) + v * I) w := by
  unfold rectangleBoundaryIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals hright_lower hright_upper,
    ← intervalIntegral.integral_add_adjacent_intervals hleft_lower hleft_upper]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring_nf
  have hbottom :
      (∫ x : ℝ in z.re..w.re, f ((z.im : ℂ) * I + x)) =
        ∫ x : ℝ in z.re..w.re, f (x + (z.im : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    change f ((z.im : ℂ) * I + x) = f (x + (z.im : ℂ) * I)
    exact congrArg f (add_comm _ _)
  rw [hbottom]
  ring

/-- A finite axis-aligned subdivision of a rectangle.  The constructor keeps
the line-integrability facts needed by the exact split theorems, so every
finite subdivision carries a proof-ready edge-cancellation certificate. -/
inductive RectangleSubdivision (f : ℂ → ℂ) : ℂ → ℂ → Type
  | leaf (z w : ℂ) : RectangleSubdivision f z w
  | vertical {z w : ℂ} (u : ℝ)
      (hbottom_left : IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re u)
      (hbottom_right : IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume u w.re)
      (htop_left : IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re u)
      (htop_right : IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume u w.re)
      (left : RectangleSubdivision f z ((u : ℂ) + w.im * I))
      (right : RectangleSubdivision f ((u : ℂ) + z.im * I) w) :
      RectangleSubdivision f z w
  | horizontal {z w : ℂ} (v : ℝ)
      (hleft_lower : IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im v)
      (hleft_upper : IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume v w.im)
      (hright_lower : IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im v)
      (hright_upper : IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume v w.im)
      (lower : RectangleSubdivision f z ((w.re : ℂ) + v * I))
      (upper : RectangleSubdivision f ((z.re : ℂ) + v * I) w) :
      RectangleSubdivision f z w

/-- The leaf rectangles of a finite subdivision. -/
def RectangleSubdivision.cells {f : ℂ → ℂ} {z w : ℂ} :
    RectangleSubdivision f z w → List (ℂ × ℂ)
  | .leaf z w => [(z, w)]
  | .vertical _ _ _ _ _ left right => left.cells ++ right.cells
  | .horizontal _ _ _ _ _ lower upper => lower.cells ++ upper.cells

/-- The sum of the boundary integrals of all leaf rectangles. -/
def RectangleSubdivision.boundarySum {f : ℂ → ℂ} {z w : ℂ} :
    RectangleSubdivision f z w → ℂ
  | .leaf z w => rectangleBoundaryIntegral f z w
  | .vertical _ _ _ _ _ left right => left.boundarySum + right.boundarySum
  | .horizontal _ _ _ _ _ lower upper => lower.boundarySum + upper.boundarySum

/-- Edge cancellation for an arbitrary finite recursive grid. -/
theorem RectangleSubdivision.boundary_eq_boundarySum
    {f : ℂ → ℂ} {z w : ℂ} (S : RectangleSubdivision f z w) :
    rectangleBoundaryIntegral f z w = S.boundarySum := by
  induction S with
  | leaf => rfl
  | vertical u hbottom_left hbottom_right htop_left htop_right left right ihleft ihright =>
      rw [rectangleBoundaryIntegral_vertical_split f _ _ u
        hbottom_left hbottom_right htop_left htop_right]
      simp only [boundarySum, ihleft, ihright]
  | horizontal v hleft_lower hleft_upper hright_lower hright_upper lower upper ihlower ihupper =>
      rw [rectangleBoundaryIntegral_horizontal_split f _ _ v
        hleft_lower hleft_upper hright_lower hright_upper]
      simp only [boundarySum, ihlower, ihupper]

/-- The recursive boundary sum is the explicit finite sum over the leaf
rectangles. -/
theorem RectangleSubdivision.boundarySum_eq_cellsSum
    {f : ℂ → ℂ} {z w : ℂ} (S : RectangleSubdivision f z w) :
    S.boundarySum =
      (S.cells.map fun cell => rectangleBoundaryIntegral f cell.1 cell.2).sum := by
  induction S with
  | leaf => simp [boundarySum, cells]
  | vertical _ _ _ _ _ left right ihleft ihright =>
      simp only [boundarySum, cells, ihleft, ihright, List.map_append, List.sum_append]
  | horizontal _ _ _ _ _ lower upper ihlower ihupper =>
      simp only [boundarySum, cells, ihlower, ihupper, List.map_append, List.sum_append]

/-- **Finite-grid Cauchy--Goursat edge cancellation.**  Every finite
axis-aligned recursive subdivision has the same outer boundary integral as
the finite sum of its leaf-rectangle boundary integrals. -/
theorem RectangleSubdivision.boundary_eq_cellsSum
    {f : ℂ → ℂ} {z w : ℂ} (S : RectangleSubdivision f z w) :
    rectangleBoundaryIntegral f z w =
      (S.cells.map fun cell => rectangleBoundaryIntegral f cell.1 cell.2).sum :=
  S.boundary_eq_boundarySum.trans S.boundarySum_eq_cellsSum

end

end NBMellinTools.H15BCF
