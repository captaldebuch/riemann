/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.RectangleDiskHomotopy

/-!
# Finite deleted-rectangle Cauchy--Goursat assembly

The local geometry of a deleted rectangle is separated from its finite
bookkeeping.  A `FiniteDeletedRectangleCauchyGoursatWitness` records:

* for every leaf cell of a finite rectangular subdivision, its exact boundary
  contribution as the sum of the enclosed disk boundaries; and
* the finite partition identity saying that those local disk contributions
  account for every deleted disk exactly once.

The local comparison can be supplied by
`rectangleBoundaryIntegral_eq_circleIntegral_of_smooth_strip_approximation`:
smooth strip equalities hold at each approximation stage and the limit bridge
turns them into the required exact cell equality.  Pole-free cells instead
use `rectangleBoundaryIntegral_eq_zero_of_differentiableOn`.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators
open Complex

/-- A complete finite bookkeeping certificate for a deleted rectangular
contour.  The certificate deliberately carries the exact local comparisons;
this prevents the global theorem from silently assuming an invalid annular
deformation of a rectangle with a disk removed. -/
structure FiniteDeletedRectangleCauchyGoursatWitness
    {f : ℂ → ℂ} {z w : ℂ} (S : RectangleSubdivision f z w)
    {ι : Type*} (holes : Finset ι) (center : ι → ℂ) (radius : ι → ℝ) where
  /-- The finite set of deleted disks assigned to a leaf cell. -/
  cellHoles : ℂ × ℂ → Finset ι
  /-- Local Cauchy--Goursat comparison for this cell.  For a disk cell it is
  supplied by the smooth-strip limit bridge; for a pole-free cell both sides
  are zero. -/
  localComparison : ∀ cell ∈ S.cells,
    rectangleBoundaryIntegral f cell.1 cell.2 =
      ∑ i ∈ cellHoles cell, ∮ u in C(center i, radius i), f u
  /-- The cell assignments form a finite oriented partition of the deleted
  disks.  Thus every disk boundary appears once in the total local sum. -/
  partition :
    (S.cells.map fun cell =>
      ∑ i ∈ cellHoles cell, ∮ u in C(center i, radius i), f u).sum =
        ∑ i ∈ holes, ∮ u in C(center i, radius i), f u

/-- **Finite deleted-rectangle Cauchy--Goursat.**  Given local exact
rectangle-to-disk comparisons and a finite disk partition, the counterclockwise
outer rectangle integral is the sum of the counterclockwise deleted-disk
integrals.  Internal grid edges cancel through
`RectangleSubdivision.boundary_eq_cellsSum`. -/
theorem finite_deleted_rectangle_cauchy_goursat
    {f : ℂ → ℂ} {z w : ℂ} (S : RectangleSubdivision f z w)
    {ι : Type*} (holes : Finset ι) (center : ι → ℂ) (radius : ι → ℝ)
    (W : FiniteDeletedRectangleCauchyGoursatWitness S holes center radius) :
    rectangleBoundaryIntegral f z w =
      ∑ i ∈ holes, ∮ u in C(center i, radius i), f u := by
  calc
    rectangleBoundaryIntegral f z w =
        (S.cells.map fun cell => rectangleBoundaryIntegral f cell.1 cell.2).sum :=
      S.boundary_eq_cellsSum
    _ = (S.cells.map fun cell =>
        ∑ i ∈ W.cellHoles cell, ∮ u in C(center i, radius i), f u).sum := by
      congr 1
      exact List.map_congr_left fun cell hcell => W.localComparison cell hcell
    _ = ∑ i ∈ holes, ∮ u in C(center i, radius i), f u := W.partition

end

end NBMellinTools.H15BCF
