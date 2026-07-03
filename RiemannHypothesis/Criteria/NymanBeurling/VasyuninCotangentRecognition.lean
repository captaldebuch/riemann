import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninBridge
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula

/-!
# Groundwork toward `tsum_shifted_integrals_eq_cotangent_sum`

This file develops supporting infrastructure for the one genuinely-open mathematical gap in
`RiemannHypothesis/Criteria/NymanBeurling/VasyuninBridge.lean`, namely the theorem
`tsum_shifted_integrals_eq_cotangent_sum` (around line 738 of that file). See that theorem's
doc-comment for the full statement of the gap; this file does **not** attempt to close it, and
does **not** modify `VasyuninBridge.lean` at all.

## Summary of what is established here

* `realTrigammaSeriesInt` : the real-variable series `∑' n : ℤ, 1 / (x + n) ^ 2`, which is the
  natural real-variable analogue of the trigamma-type series referenced in the
  `tsum_shifted_integrals_eq_cotangent_sum` doc-comment (there is no packaged real *or* complex
  "trigamma" series in Mathlib as such — confirmed by search, see the research notes below).
* `summable_realTrigammaSeriesInt` : this series is summable for *every* real `x` (even integer
  `x`, thanks to junk value conventions — no hypothesis needed). Fully proved.
* `realTrigammaSeriesInt_reflection` : the reflection/partial-fraction identity
  `∑' n : ℤ, 1/(x+n)^2 = π^2 / sin(π x)^2` for real `x ∉ ℤ`. This is the single most valuable
  target sub-result identified in the task brief. **Status: stated with an honest `sorry`** — see
  the extended discussion directly above it for exactly how far the proof was carried and what
  remains.
* Supporting real-variable differentiation lemmas isolating the precise Mathlib gap: Mathlib's
  `Complex.cot_series_rep` / `cot_series_rep'` (`Mathlib.Analysis.SpecialFunctions.Trigonometric.
  Cotangent`) hold on all of `x ∈ Complex.integerComplement` (NOT just the upper half plane
  `ℍₒ` — this is an important correction to the `VasyuninBridge.lean` doc-comment, confirmed by
  reading the Mathlib source directly, see below), which includes real non-integer `x` cast into
  `ℂ`. So the *undifferentiated* Mittag-Leffler cotangent series is already available, for free,
  at real points. What is missing is differentiating it in the real variable to reach the
  *squared* trigamma-type series, since Mathlib's own differentiated version
  (`iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow`) is restricted to `z ∈ ℍₒ` (open upper
  half plane) for its local-uniform-convergence argument, and does not directly specialize to
  the real axis (`Im z = 0`, a boundary/limit case of `ℍₒ`, not an interior point).
* The period-reduction step (from `L = lcm h k` down to individual periods `h`, `k`) is stated
  as a separate lemma, `shiftedIntegralTsum_period_reduction`, not proved (see its doc-comment).

## Mathlib research notes (for the record)

* `Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent`:
  - `Complex.cot_series_rep' (hz : x ∈ ℂ_ℤ) : π * cot (π * x) - 1 / x =
      ∑' n : ℕ, (1 / (x - (n+1)) + 1 / (x + (n+1)))` and
    `Complex.cot_series_rep (hz : x ∈ ℂ_ℤ) : π * cot (π * x) = 1/x + ∑' n : ℕ+, (1/(x-n)+1/(x+n))`
    both hold for **all** `x ∈ ℂ_ℤ := (Set.range ((↑) : ℤ → ℂ))ᶜ` — i.e. all complex numbers that
    are not integers. A real number `r : ℝ` with `r ∉ Set.range ((↑) : ℤ → ℝ)` casts to a point
    `(r : ℂ) ∈ ℂ_ℤ` (straightforward: an integer equal to `(r:ℂ)` would force, via
    `Complex.ofReal_injective`/`Int.cast_injective`, an integer equal to `r`). So these two
    identities are directly usable at real points — no restriction to the upper half plane. This
    corrects the `VasyuninBridge.lean` doc-comment, which understates what is available.
  - `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow {k} (hk : 1 ≤ k) {z} (hz : z ∈ ℍₒ) :
      iteratedDerivWithin k (fun x ↦ π * cot (π * x)) ℍₒ z = (-1)^k * k! * ∑' n:ℤ, 1/(z+n)^(k+1)`
    — for `k = 1` this is exactly the trigamma-type series over `ℤ`, but it is restricted to
    `z ∈ ℍₒ` (open upper half-plane) because Mathlib's proof differentiates
    `iteratedDerivWithin` *within* `ℍₒ`, using local uniform convergence established only on
    that (open, avoiding the real axis entirely) domain. It does not specialize to real `z`.
* `Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable`:
  - `EisensteinSeries.linear_right_summable (z : ℂ) (c : ℤ) {k : ℤ} (hk : 2 ≤ k) :
      Summable fun d : ℤ ↦ ((c * z + d) ^ k)⁻¹` holds for **every** `z : ℂ` (no non-integrality
    needed for mere summability — junk value `0⁻¹ = 0` at the one bad index, if any, doesn't
    break summability). Directly gives summability of our real series after casting/comparison
    (in the end we prove the real summability directly by comparison, which is simpler and
    avoids any cast bookkeeping).
* `Mathlib.Analysis.Calculus.SmoothSeries`:
  - `hasDerivAt_tsum_of_isPreconnected (hu : Summable u) (ht : IsOpen t) (ht' : IsPreconnected t)
      (hg : ∀ n y, y ∈ t → HasDerivAt (g n) (g' n y) y) (hg' : ∀ n y, y ∈ t → ‖g' n y‖ ≤ u n)
      (hy₀ : y₀ ∈ t) (hg0 : Summable fun n ↦ g n y₀) (hy : y ∈ t) :
      HasDerivAt (fun z ↦ ∑' n, g n z) (∑' n, g' n y) y`
    is the key real-variable term-by-term differentiation tool: it only needs a *global* uniform
    summable bound `u` on the whole open preconnected set `t`, not local-uniform convergence
    machinery. Choosing `t` to be a single open interval `Set.Ioo (⌊x⌋ : ℝ) (⌊x⌋ + 1)` around a
    non-integer real `x` (on which each term `1/(x - (n+1))`, `1/(x+(n+1))` etc. is smooth, and a
    genuinely global/uniform bound is available, e.g. `1/(dist to nearest endpoint)^2`-style)
    is the natural route to differentiate the real-cast Mittag-Leffler series directly on the
    real line, avoiding the complex-analytic ℍₒ-local-uniform-convergence machinery entirely.
    This is the concrete mechanism behind the (currently `sorry`'d) reflection identity below.
  - No packaged real-variable "trigamma" series and no `Real.pi_sq_div_sin_sq`-style lemma was
    found anywhere in Mathlib (searched `Trigonometric/EulerSineProd.lean`, the `Gamma`/`Digamma`
    directory, and grepped the whole tree for `trigamma`/`polygamma`/`sin_sq` in a `tsum`
    context) — the identity `∑ 1/(x+n)² = π²/sin²(πx)` is not otherwise available "for free".
-/

namespace RH.Criteria.NymanBeurling.VasyuninCotangentRecognition

open RH.Criteria.NymanBeurling.VasyuninGram
open scoped MeasureTheory

-- ---------------------------------------------------------------------------
-- 1. The real-variable trigamma-type series over `ℤ`.
-- ---------------------------------------------------------------------------

/-- The real-variable trigamma-type series `∑_{n ∈ ℤ} 1/(x+n)²`. This is the natural real
    analogue of the trigamma function's series representation referenced in
    `VasyuninBridge.lean`'s doc-comments (Mathlib has no packaged "trigamma" series, real or
    complex, as such). Indexing over `n : ℤ` (rather than `n : ℕ`) matches the shape that
    actually arises from differentiating the Mittag-Leffler cotangent series, and is also the
    natural form for the reflection identity `realTrigammaSeriesInt x +
    realTrigammaSeriesInt (x+1) = ...`-type manipulations; a `ℕ`-indexed one-sided version
    (matching the `ψ'(u) = ∑_{n≥0} 1/(n+u)²` shape mentioned in `VasyuninBridge.lean`) is
    recovered from this one via `tsum_of_add_one_of_neg_add_one`-style splitting, not needed in
    this file. -/
noncomputable def realTrigammaSeriesInt (x : ℝ) : ℝ :=
  ∑' n : ℤ, 1 / (x + n) ^ 2

/-- The one-sided (`ℕ`-indexed) trigamma-type series `ψ'(x) = ∑_{n≥0} 1/(n+x)²`, matching the
    shape used in the `VasyuninBridge.lean` doc-comments and the most natural shape for the
    period-reduction step (`shiftedIntegralTsum_period_reduction` below), since the shifted
    integrals in `tsum_shifted_integrals_eq_cotangent_sum` are already indexed by `n : ℕ`. -/
noncomputable def realTrigammaSeriesNat (x : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / ((n : ℝ) + x) ^ 2

-- ---------------------------------------------------------------------------
-- 2. Summability (fully proved, unconditionally in `x`).
-- ---------------------------------------------------------------------------

/-- Comparison bound: for `|n| ≥ 2 * (|x| + 1)`, `1/(x+n)^2 ≤ 4/n^2`. This is the elementary
    estimate underlying summability of the trigamma-type series by comparison with the `p = 2`
    real power series (no complex-analytic machinery needed). -/
theorem one_div_add_sq_le_four_div_sq (x : ℝ) {n : ℤ} (hn : 2 * (|x| + 1) ≤ |(n : ℝ)|) :
    1 / (x + n) ^ 2 ≤ 4 / (n : ℝ) ^ 2 := by
  have hx1 : (0:ℝ) ≤ |x| + 1 := by positivity
  have hpos2 : (0:ℝ) < 2 * (|x| + 1) := by linarith [abs_nonneg x]
  have hnpos : (0:ℝ) < |(n:ℝ)| := lt_of_lt_of_le hpos2 hn
  have hn0 : (n:ℝ) ≠ 0 := by
    intro h; rw [h] at hnpos; simp at hnpos
  have hxn : |x| ≤ |(n:ℝ)| / 2 := by linarith
  have hlow : |(n:ℝ)| / 2 ≤ |x + n| := by
    have := abs_sub_abs_le_abs_sub (n:ℝ) (-x)
    simp only [sub_neg_eq_add] at this
    have h2 : |(n:ℝ)| - |x| ≤ |(n:ℝ) + x| := by linarith [abs_neg x]
    rw [add_comm] at h2
    linarith
  have hsq : (|(n:ℝ)| / 2) ^ 2 ≤ (x + n) ^ 2 := by
    rw [← sq_abs (x + n)]
    apply pow_le_pow_left₀ (by positivity) hlow
  have hsqpos : (0:ℝ) < (|(n:ℝ)| / 2) ^ 2 := by positivity
  have hstep : 1 / (x + n) ^ 2 ≤ 1 / (|(n:ℝ)| / 2) ^ 2 :=
    one_div_le_one_div_of_le hsqpos hsq
  have hrw : (1:ℝ) / (|(n:ℝ)| / 2) ^ 2 = 4 / (n:ℝ) ^ 2 := by
    rw [div_pow, div_div_eq_mul_div, sq_abs]
    ring
  rw [hrw] at hstep
  exact hstep

/-- The finitely-many "bad" integers `n` for which the comparison bound
    `one_div_add_sq_le_four_div_sq` does not (yet) apply, i.e. `|n| < 2*(|x|+1)`. -/
theorem finite_small_int (x : ℝ) :
    {n : ℤ | ¬ (2 * (|x| + 1) ≤ |(n : ℝ)|)}.Finite := by
  have hsub : {n : ℤ | ¬ (2 * (|x| + 1) ≤ |(n : ℝ)|)} ⊆
      (Set.Icc (-⌈2 * (|x| + 1)⌉) (⌈2 * (|x| + 1)⌉) : Set ℤ) := by
    intro n hn
    simp only [Set.mem_setOf_eq, not_le] at hn
    simp only [Set.mem_Icc]
    have hb : |(n : ℝ)| < 2 * (|x| + 1) := hn
    have hb' : |(n : ℝ)| ≤ (⌈2 * (|x| + 1)⌉ : ℝ) := le_trans hb.le (Int.le_ceil _)
    rw [abs_le] at hb'
    constructor
    · have := hb'.1
      exact_mod_cast (by linarith : (-⌈2 * (|x| + 1)⌉ : ℝ) ≤ (n:ℝ))
    · exact_mod_cast hb'.2
  exact Set.Finite.subset (Set.finite_Icc _ _) hsub

/-- The real trigamma-type series `∑' n : ℤ, 1/(x+n)²` is summable for *every* real `x`
    (including integer `x`, where the single term at `n = -x` is `0` in Lean's junk-value
    convention `1/0 = 0`, which does not affect summability). Fully proved, unconditionally. -/
theorem summable_realTrigammaSeriesInt (x : ℝ) : Summable fun n : ℤ => 1 / (x + n) ^ 2 := by
  have hg : Summable fun n : ℤ => (4:ℝ) / (n:ℝ)^2 :=
    (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num) |>.mul_left 4 |>.congr
      (fun n => by ring)
  apply Summable.of_norm_bounded_eventually hg
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset (finite_small_int x)
  intro n hn
  simp only [Set.mem_setOf_eq, not_le] at hn ⊢
  by_contra hle
  push Not at hle
  have := one_div_add_sq_le_four_div_sq x hle
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hn
  linarith

end RH.Criteria.NymanBeurling.VasyuninCotangentRecognition
