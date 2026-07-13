/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import RiemannHypothesis.Criteria.NymanBeurling.BaezDuarte

/-!
# Exact reciprocal tails of Báez--Duarte approximants

The full-half-line model has extra structure beyond arbitrary `L²` functions:
each generator is exactly reciprocal for `x > 1`.  The tail input
needed to complement Cauchy--Schwarz on `(0, 1]`.
-/

namespace NBMellinTools

open scoped BigOperators
open RH.Criteria.NymanBeurling.BaezDuarte

/-- For `x > 1`, the zero-based Báez--Duarte generator is exactly
`1 / ((k+1)x)`. -/
theorem rhoBD_eq_one_div_of_one_lt (k : ℕ) {x : ℝ} (hx : 1 < x) :
    rhoBD k x = 1 / ((k + 1 : ℝ) * x) := by
  unfold rhoBD
  rw [Int.fract]
  have hpos : 0 < 1 / ((k + 1 : ℝ) * x) := by positivity
  have hlt : 1 / ((k + 1 : ℝ) * x) < 1 := by
    rw [div_lt_one (by positivity)]
    have hk : (1 : ℝ) ≤ (k + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    nlinarith
  rw [Int.floor_eq_zero_iff.mpr ⟨le_of_lt hpos, hlt⟩]
  norm_num

/-- Every finite Báez--Duarte approximation has one scalar reciprocal tail. -/
theorem bdApprox_eq_tail_of_one_lt
    (N : ℕ) (coeffs : Fin N → ℝ) {x : ℝ} (hx : 1 < x) :
    bdApprox N coeffs x =
      (∑ k, coeffs k / (k.val + 1 : ℝ)) / x := by
  simp_rw [bdApprox, rhoBD_eq_one_div_of_one_lt _ hx]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  field_simp

/-- Consequently, the approximation error has an exact reciprocal tail. -/
theorem chi_sub_bdApprox_eq_tail_of_one_lt
    (N : ℕ) (coeffs : Fin N → ℝ) {x : ℝ} (hx : 1 < x) :
    chi01 x - bdApprox N coeffs x =
      -(∑ k, coeffs k / (k.val + 1 : ℝ)) / x := by
  rw [bdApprox_eq_tail_of_one_lt N coeffs hx]
  simp [chi01, not_le_of_gt hx]
  ring

end NBMellinTools
