import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula
import RiemannHypothesis.Certificates.TrigIntervalSweep

/-!
# Structural helper lemmas for `cotangentTermV a k = cot(π a / k)` bounds

This file provides three "free" reduction lemmas used to discharge the majority of the
`2 ≤ k ≤ 10` cotangent-bound axioms in `VasyuninPrimitiveBoundsCore.lean` without any new
halving analysis:

1. `cotangentTermV_exact_of_two_mul_eq` : when `2 * a = k` the angle is exactly `π/2`, so
   `cotangentTermV a k = 0` by `Real.cos_pi_div_two` / `Real.sin_pi_div_two`.
2. `cotangentTermV_obtuse_eq_neg` : when `2 * a > k` (angle `> π/2`), rewrites
   `cotangentTermV a k = - cotangentTermV (k - a) k` via `Real.cos_pi_sub` / `Real.sin_pi_sub`,
   reducing an obtuse pair to an acute companion pair with a sign flip.
3. `cotangentTermV_gcd_reduce` : when `a` and `k` share a common factor, rewrites
   `cotangentTermV a k = cotangentTermV (a / g) (k / g)` since `π * a / k = π * (a/g) / (k/g)`.

These let the ~12 genuinely new halving proofs (for coprime acute pairs) cover many more
than 12 of the 45 `(a, k)` pairs with `2 ≤ k ≤ 10`.
-/

namespace RH.Certificates.Generated

open RH.Criteria.NymanBeurling.VasyuninGram

/-- Exact case: when the angle `π a / k` is exactly `π/2` (i.e. `2 * a = k`),
`cotangentTermV a k = 0`. -/
theorem cotangentTermV_exact_of_two_mul_eq {a k : ℕ} (ha0 : 0 < a) (h : 2 * a = k) :
    cotangentTermV a k = 0 := by
  unfold cotangentTermV
  have hk : (k : ℝ) = 2 * (a : ℝ) := by
    exact_mod_cast h.symm
  have hangle : Real.pi * (a : ℝ) / (k : ℝ) = Real.pi / 2 := by
    rw [hk]
    have ha0' : (a : ℝ) ≠ 0 := by
      have : a ≠ 0 := by omega
      exact_mod_cast this
    field_simp
  rw [hangle, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- Obtuse reduction: when `2 * a > k` (so `π a / k > π / 2`), the cotangent term equals
minus the cotangent term of the acute companion pair `(k - a, k)`, since
`π * a / k = π - π * (k - a) / k`. -/
theorem cotangentTermV_obtuse_eq_neg {a k : ℕ} (ha : a < k) (hobtuse : k < 2 * a) :
    cotangentTermV a k = - cotangentTermV (k - a) k := by
  unfold cotangentTermV
  have hk0 : (k : ℝ) ≠ 0 := by
    have : k ≠ 0 := by omega
    exact_mod_cast this
  have hangle : Real.pi * ((k - a : ℕ) : ℝ) / (k : ℝ) = Real.pi - Real.pi * (a : ℝ) / (k : ℝ) := by
    have hka : (k - a : ℕ) = k - a := rfl
    have hcast : ((k - a : ℕ) : ℝ) = (k : ℝ) - (a : ℝ) := by
      have hle : a ≤ k := le_of_lt ha
      exact_mod_cast (Nat.cast_sub hle : ((k - a : ℕ) : ℝ) = (k : ℝ) - (a : ℝ))
    rw [hcast]
    field_simp
  rw [hangle, Real.cos_pi_sub, Real.sin_pi_sub]
  ring

/-- gcd-reduction: if `a = a' * g` and `k = k' * g` with `g ≠ 0`, then
`cotangentTermV a k = cotangentTermV a' k'` since the two angles `π a / k` and `π a' / k'`
are equal. -/
theorem cotangentTermV_gcd_reduce {a k a' k' g : ℕ} (hg : 0 < g)
    (ha : a = a' * g) (hk : k = k' * g) (hk' : k' ≠ 0) :
    cotangentTermV a k = cotangentTermV a' k' := by
  unfold cotangentTermV
  have hangle : Real.pi * (a : ℝ) / (k : ℝ) = Real.pi * (a' : ℝ) / (k' : ℝ) := by
    have hg0 : (g : ℝ) ≠ 0 := by
      have : g ≠ 0 := by omega
      exact_mod_cast this
    have hk'0 : (k' : ℝ) ≠ 0 := by exact_mod_cast hk'
    have hacast : (a : ℝ) = (a' : ℝ) * (g : ℝ) := by exact_mod_cast ha
    have hkcast : (k : ℝ) = (k' : ℝ) * (g : ℝ) := by exact_mod_cast hk
    rw [hacast, hkcast]
    field_simp
  rw [hangle]

end RH.Certificates.Generated
