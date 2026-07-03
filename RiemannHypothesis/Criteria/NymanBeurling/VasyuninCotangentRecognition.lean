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
open Real (pi)
open scoped Real
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

/-- Uniform-in-`x` version of `one_div_add_sq_le_four_div_sq`: the same conclusion holds
    replacing the specific `x` by any bound `C` with `|x| ≤ C`. This is exactly the form needed
    for a *global* uniform summable bound on a whole interval (as opposed to a single point),
    which is what `hasDerivAt_tsum_of_isPreconnected` requires. -/
theorem one_div_add_sq_le_four_div_sq_of_le {x C : ℝ} (hxC : |x| ≤ C) {n : ℤ}
    (hn : 2 * (C + 1) ≤ |(n : ℝ)|) :
    1 / (x + n) ^ 2 ≤ 4 / (n : ℝ) ^ 2 := by
  have hCx : 2 * (|x| + 1) ≤ |(n:ℝ)| := by linarith
  exact one_div_add_sq_le_four_div_sq x hCx

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

/-- The one-sided (`ℕ`-indexed) trigamma-type series `realTrigammaSeriesNat` is summable for
    every real `x`, obtained from `summable_realTrigammaSeriesInt` by restricting the summable
    `ℤ`-indexed series along the (injective) inclusion `ℕ ↪ ℤ`. -/
theorem summable_realTrigammaSeriesNat (x : ℝ) : Summable fun n : ℕ => 1 / ((n : ℝ) + x) ^ 2 := by
  have hz := summable_realTrigammaSeriesInt x
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := fun a b hab => by
    simpa using hab
  have hcomp := hz.comp_injective hinj
  simp only [Function.comp_def, Int.cast_natCast] at hcomp
  apply hcomp.congr
  intro n; ring_nf

-- ---------------------------------------------------------------------------
-- 3. The real-cast Mittag-Leffler cotangent series at real non-integer points.
--
-- Mathlib's `Complex.cot_series_rep'` holds on all of `ℂ_ℤ` (not just `ℍₒ`), which includes
-- real non-integer points cast into `ℂ`. This section records that fact as a genuinely
-- real-variable statement (no `Complex` types in the final statement), which is the true
-- starting point for the reflection-identity differentiation argument below.
-- ---------------------------------------------------------------------------

/-- A real number that is not an integer casts to a point of `Complex.integerComplement`. -/
theorem ofReal_mem_integerComplement {x : ℝ} (hx : ∀ n : ℤ, (n : ℝ) ≠ x) :
    (x : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  exact hx n (by exact_mod_cast hn)

/-- Real-variable restatement of `Complex.cot_series_rep'` at a real non-integer point: casting
    everything down from `ℂ` to `ℝ` via `Complex.ofReal_cot`, `Complex.ofReal_tsum`-style
    lemmas. This is the genuinely real-variable form of the Mittag-Leffler cotangent expansion,
    valid on all of `ℝ \ ℤ` (not merely a complex upper-half-plane neighborhood) — the key fact
    enabling everything below. -/
theorem real_cot_series_rep' {x : ℝ} (hx : ∀ n : ℤ, (n : ℝ) ≠ x) :
    π * Real.cot (π * x) - 1 / x =
      ∑' n : ℕ, (1 / (x - (n + 1)) + 1 / (x + (n + 1))) := by
  have hmem := ofReal_mem_integerComplement hx
  have hc := cot_series_rep' hmem
  have hlhs : ((π * Real.cot (π * x) - 1 / x : ℝ) : ℂ)
      = π * Complex.cot (π * x) - 1 / (x : ℂ) := by
    push_cast [Complex.ofReal_cot]
    ring_nf
  have hrhs : ((∑' n : ℕ, (1 / (x - (n + 1)) + 1 / (x + (n + 1))) : ℝ) : ℂ)
      = ∑' n : ℕ, (1 / ((x : ℂ) - (n + 1)) + 1 / ((x : ℂ) + (n + 1))) := by
    rw [Complex.ofReal_tsum]
    push_cast
    ring_nf
  have : ((π * Real.cot (π * x) - 1 / x : ℝ) : ℂ)
      = ((∑' n : ℕ, (1 / (x - (n + 1)) + 1 / (x + (n + 1))) : ℝ) : ℂ) := by
    rw [hlhs, hrhs]
    exact hc
  exact_mod_cast this

-- ---------------------------------------------------------------------------
-- 4. Term-by-term differentiation of the real Mittag-Leffler series on an interval
--    `Ioo (m : ℝ) (m + 1)` avoiding all integers.
--
-- Strategy (per the task brief's identification of `hasDerivAt_tsum_of_isPreconnected` in
-- `Mathlib.Analysis.Calculus.SmoothSeries` as the right real-variable tool): work on a single
-- open interval `t = Set.Ioo (m : ℝ) (m + 1)` for a fixed integer `m`, on which every term
-- `y ↦ 1/(y - (n+1)) + 1/(y + (n+1))` (`n : ℕ`) is differentiable (the denominators
-- `y - (n+1)`, `y + (n+1)` never vanish on `t`, since `t` contains no integer), and on which a
-- genuinely *global* (not just local) uniform summable bound on the derivatives is available,
-- because `t` is a bounded interval a fixed positive distance from every integer other than
-- `m` and `m+1` themselves (and the two "close" terms `n = m` / `n = -m-1`-ish contribute only
-- finitely many exceptional terms, handled by the eventual/global bound argument below via a
-- `4/n²`-type comparison, exactly as in `summable_realTrigammaSeriesInt`).
-- ---------------------------------------------------------------------------

/-- The derivative of a single term `y ↦ 1/(y - a) + 1/(y + a)` of the Mittag-Leffler series,
    valid whenever `y ≠ a` and `y ≠ -a`. -/
theorem hasDerivAt_mittagLefflerTerm {a y : ℝ} (ha : y ≠ a) (ha' : y ≠ -a) :
    HasDerivAt (fun z : ℝ => 1 / (z - a) + 1 / (z + a))
      (-(1 / (y - a) ^ 2) + -(1 / (y + a) ^ 2)) y := by
  have h1 : HasDerivAt (fun z : ℝ => 1 / (z - a)) (-(1 / (y - a) ^ 2)) y := by
    have hsub : HasDerivAt (fun z : ℝ => z - a) 1 y := (hasDerivAt_id y).sub_const a
    have hne : y - a ≠ 0 := sub_ne_zero.mpr ha
    have := hsub.inv hne
    simp only [one_div, inv_one] at this ⊢
    convert this using 1
    field_simp
  have h2 : HasDerivAt (fun z : ℝ => 1 / (z + a)) (-(1 / (y + a) ^ 2)) y := by
    have hadd : HasDerivAt (fun z : ℝ => z + a) 1 y := (hasDerivAt_id y).add_const a
    have hne : y + a ≠ 0 := by
      intro h; apply ha'; linarith
    have := hadd.inv hne
    simp only [one_div, inv_one] at this ⊢
    convert this using 1
    field_simp
  simpa using h1.add h2

/-- Uniform (in `y` ranging over the ball `|y - x₀| < δ`) comparison bound for a single
    Mittag-Leffler derivative term, valid once `n` is large enough (`2 * (|x₀| + δ + 1) ≤ n+1`)
    that the `4/n²`-style comparison (`one_div_add_sq_le_four_div_sq`, applied with the
    uniform-in-`y` bound `|y| ≤ |x₀| + δ`) kicks in for every `y` in the ball at once, not just
    at the center `x₀`. -/
theorem mittagLefflerDeriv_far_bound {x₀ δ : ℝ} {y : ℝ} (hy : |y - x₀| < δ)
    {n : ℕ} (hn : 2 * (|x₀| + δ + 1) ≤ (n : ℝ) + 1) :
    1 / (y - ((n:ℝ) + 1)) ^ 2 + 1 / (y + ((n:ℝ) + 1)) ^ 2 ≤ 8 / ((n:ℝ) + 1) ^ 2 := by
  have hyC : |y| ≤ |x₀| + δ := by
    have h1 : |y| - |x₀| ≤ |y - x₀| := by
      have := abs_sub_abs_le_abs_sub y x₀; linarith
    linarith
  set m : ℤ := (n : ℤ) + 1 with hm_def
  have hmcast : ((m : ℤ) : ℝ) = (n : ℝ) + 1 := by push_cast [hm_def]; ring
  have hn' : 2 * (|y| + 1) ≤ |(m : ℝ)| := by
    rw [hmcast]; rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) + 1)]; linarith
  have hstep1 : 1 / (y + (m : ℝ)) ^ 2 ≤ 4 / (m : ℝ) ^ 2 :=
    one_div_add_sq_le_four_div_sq y hn'
  have hn'' : 2 * (|(-y)| + 1) ≤ |(m : ℝ)| := by
    rw [abs_neg]; exact hn'
  have hstep2 : 1 / (-y + (m : ℝ)) ^ 2 ≤ 4 / (m : ℝ) ^ 2 :=
    one_div_add_sq_le_four_div_sq (-y) hn''
  rw [hmcast] at hstep1 hstep2
  have heq2 : (-y + ((n:ℝ) + 1)) ^ 2 = (y - ((n:ℝ) + 1)) ^ 2 := by ring
  rw [heq2] at hstep2
  have hsum : (4:ℝ) / ((n:ℝ)+1) ^ 2 + 4 / ((n:ℝ)+1) ^ 2 = 8 / ((n:ℝ)+1) ^ 2 := by ring
  linarith [hstep1, hstep2]

-- ---------------------------------------------------------------------------
-- 5. The "radius to the nearest integer" and the near/far uniform bound.
-- ---------------------------------------------------------------------------

/-- Half the distance from `x₀` to the nearer of its floor/ceiling: strictly positive whenever
    `x₀` is not itself an integer. Every point within this radius of `x₀` still lies strictly
    between `⌊x₀⌋` and `⌊x₀⌋ + 1`, and every integer is at distance at least this radius from
    every such point (see `dist_ball_radius_lt_dist_to_any_int` below). -/
noncomputable def ballRadius (x₀ : ℝ) : ℝ :=
  min (x₀ - (⌊x₀⌋ : ℝ)) ((⌊x₀⌋ : ℝ) + 1 - x₀) / 2

theorem ballRadius_pos {x₀ : ℝ} (hx₀ : ∀ n : ℤ, (n : ℝ) ≠ x₀) : 0 < ballRadius x₀ := by
  unfold ballRadius
  have h1 : (⌊x₀⌋ : ℝ) < x₀ := lt_of_le_of_ne (Int.floor_le x₀) (hx₀ ⌊x₀⌋)
  have h2 : x₀ < (⌊x₀⌋ : ℝ) + 1 := Int.lt_floor_add_one x₀
  have : (0:ℝ) < min (x₀ - (⌊x₀⌋ : ℝ)) ((⌊x₀⌋ : ℝ) + 1 - x₀) := by
    apply lt_min <;> linarith
  linarith

/-- Every integer `a` is at distance at least `ballRadius x₀` from `x₀` itself: distinct
    integers on either side of `x₀` are, by definition of `ballRadius`, at least that far. -/
theorem ballRadius_le_dist_to_int {x₀ : ℝ} (hx₀ : ∀ n : ℤ, (n : ℝ) ≠ x₀) (a : ℤ) :
    ballRadius x₀ ≤ |x₀ - (a : ℝ)| := by
  unfold ballRadius
  have h1 : (⌊x₀⌋ : ℝ) < x₀ := lt_of_le_of_ne (Int.floor_le x₀) (hx₀ ⌊x₀⌋)
  have h2 : x₀ < (⌊x₀⌋ : ℝ) + 1 := Int.lt_floor_add_one x₀
  rcases le_or_gt (a : ℝ) (⌊x₀⌋ : ℝ) with hcase | hcase
  · have hxa : (0:ℝ) ≤ x₀ - a := by linarith
    rw [abs_of_nonneg hxa]
    have : min (x₀ - (⌊x₀⌋ : ℝ)) ((⌊x₀⌋ : ℝ) + 1 - x₀) ≤ x₀ - (⌊x₀⌋ : ℝ) := min_le_left _ _
    linarith
  · have ha : (⌊x₀⌋ : ℝ) + 1 ≤ (a : ℝ) := by
      have hai : (⌊x₀⌋ : ℤ) < a := by exact_mod_cast hcase
      have : (⌊x₀⌋ : ℤ) + 1 ≤ a := hai
      exact_mod_cast this
    have hxa : x₀ - a ≤ 0 := by linarith
    rw [abs_of_nonpos hxa]
    have : min (x₀ - (⌊x₀⌋ : ℝ)) ((⌊x₀⌋ : ℝ) + 1 - x₀) ≤ (⌊x₀⌋ : ℝ) + 1 - x₀ := min_le_right _ _
    linarith

/-- For `y` within `ballRadius x₀ / 2` of `x₀`, and any integer `a`, `|y - a|` is at least
    `ballRadius x₀ / 2` — i.e. every point of the half-radius ball is uniformly bounded away
    from every integer, with a bound depending only on `x₀` (not on `y` or `a`). This is what
    lets the *same* finite bound cover every "near" index `n` simultaneously on the whole ball,
    handling the finitely-many small-`n` terms that `mittagLefflerDeriv_far_bound` cannot reach
    (those with a pole inside or adjacent to a naively-chosen full unit interval). -/
theorem half_ballRadius_le_dist {x₀ : ℝ} (hx₀ : ∀ n : ℤ, (n : ℝ) ≠ x₀) {y : ℝ}
    (hy : |y - x₀| < ballRadius x₀ / 2) (a : ℤ) :
    ballRadius x₀ / 2 ≤ |y - (a : ℝ)| := by
  have hbig := ballRadius_le_dist_to_int hx₀ a
  have h1 : |x₀ - (a:ℝ)| - |y - x₀| ≤ |y - (a:ℝ)| := by
    have := abs_sub_abs_le_abs_sub (x₀ - (a:ℝ)) (x₀ - y)
    have heq : (x₀ - (a:ℝ)) - (x₀ - y) = y - a := by ring
    rw [heq] at this
    have habs : |x₀ - y| = |y - x₀| := abs_sub_comm _ _
    rw [habs] at this
    linarith [le_abs_self ((x₀ - (a:ℝ)) - (x₀ - y))]
  linarith

-- ---------------------------------------------------------------------------
-- 6. Assembling the global uniform bound and the term-by-term differentiation theorem.
-- ---------------------------------------------------------------------------

/-- The threshold index above which `mittagLefflerDeriv_far_bound`'s `4/n²`-comparison applies
    uniformly on the half-radius ball around `x₀`. -/
noncomputable def mittagLefflerThreshold (x₀ : ℝ) : ℕ :=
  ⌈2 * (|x₀| + ballRadius x₀ / 2 + 1)⌉₊

/-- The global uniform bound function: `8/δ²` for the finitely many "near" indices below the
    threshold, and `8/(n+1)²` above it (which is where the far-field comparison bound
    `mittagLefflerDeriv_far_bound` applies). Agrees with `8/(n+1)²` for all but finitely many
    `n`, hence summable by comparison (`Summable.congr_cofinite`). -/
noncomputable def mittagLefflerUniformBound (x₀ : ℝ) (n : ℕ) : ℝ :=
  if n < mittagLefflerThreshold x₀ then 8 / (ballRadius x₀ / 2) ^ 2 else 8 / ((n:ℝ) + 1) ^ 2

theorem summable_mittagLefflerUniformBound (x₀ : ℝ) :
    Summable (mittagLefflerUniformBound x₀) := by
  have hbase : Summable (fun n : ℕ => 8 / ((n:ℝ) + 1) ^ 2) := by
    have h1 : Summable (fun n : ℕ => 1 / ((n:ℝ) + 1) ^ 2) := by
      have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      rw [← summable_nat_add_iff 1] at this
      simpa using this
    simpa using h1.mul_left 8
  apply hbase.congr_cofinite
  rw [Filter.EventuallyEq, Filter.eventually_cofinite]
  apply Set.Finite.subset (Set.finite_Iio (mittagLefflerThreshold x₀))
  intro n hn
  simp only [Set.mem_setOf_eq, mittagLefflerUniformBound] at hn
  simp only [Set.mem_Iio]
  by_contra hge
  push Not at hge
  exact hn (by simp [not_lt.mpr hge])

/-- The global uniform bound dominates every Mittag-Leffler derivative summand, for every `y`
    in the half-radius ball around `x₀` and every `n : ℕ` at once — combining the "near" bound
    `half_ballRadius_le_dist` (below the threshold) with the "far" bound
    `mittagLefflerDeriv_far_bound` (at or above the threshold). -/
theorem mittagLefflerDeriv_uniform_bound {x₀ : ℝ} (hx₀ : ∀ n : ℤ, (n : ℝ) ≠ x₀) {y : ℝ}
    (hy : |y - x₀| < ballRadius x₀ / 2) (n : ℕ) :
    ‖-(1 / (y - ((n:ℝ) + 1)) ^ 2) + -(1 / (y + ((n:ℝ) + 1)) ^ 2)‖
      ≤ mittagLefflerUniformBound x₀ n := by
  rw [Real.norm_eq_abs]
  unfold mittagLefflerUniformBound
  split_ifs with hcase
  · set δ' : ℝ := ballRadius x₀ / 2 with hδ'_def
    have hδpos : 0 < δ' := by
      have := ballRadius_pos hx₀
      rw [hδ'_def]; linarith
    have h1 : δ' ≤ |y - ((n:ℝ) + 1)| := by
      have := half_ballRadius_le_dist hx₀ hy ((n : ℤ) + 1)
      push_cast at this
      convert this using 3
    have h2 : δ' ≤ |y + ((n:ℝ) + 1)| := by
      have := half_ballRadius_le_dist hx₀ hy (-((n : ℤ) + 1))
      push_cast at this
      rw [show y - (-((n:ℝ)+1)) = y + ((n:ℝ)+1) by ring] at this
      exact this
    have hb1 : 1 / (y - ((n:ℝ) + 1)) ^ 2 ≤ 1 / δ' ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      rw [← sq_abs (y - ((n:ℝ)+1))]
      exact pow_le_pow_left₀ hδpos.le h1 2
    have hb2 : 1 / (y + ((n:ℝ) + 1)) ^ 2 ≤ 1 / δ' ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      rw [← sq_abs (y + ((n:ℝ)+1))]
      exact pow_le_pow_left₀ hδpos.le h2 2
    have hnn1 : (0:ℝ) ≤ 1 / (y - ((n:ℝ) + 1)) ^ 2 := by positivity
    have hnn2 : (0:ℝ) ≤ 1 / (y + ((n:ℝ) + 1)) ^ 2 := by positivity
    rw [abs_of_nonpos (by linarith)]
    have hδsqpos : (0:ℝ) < δ' ^ 2 := by positivity
    have h2le8 : (2:ℝ)/δ'^2 ≤ 8/δ'^2 := by gcongr; norm_num
    have hsum : (1:ℝ)/δ'^2 + 1/δ'^2 = 2/δ'^2 := by ring
    linarith [hb1, hb2, hsum]
  · push Not at hcase
    have hthr : (2:ℝ) * (|x₀| + ballRadius x₀ / 2 + 1) ≤ (n:ℝ) + 1 := by
      have hceil : (mittagLefflerThreshold x₀ : ℝ)
          ≤ (n : ℝ) := by exact_mod_cast hcase
      have := Nat.le_ceil (2 * (|x₀| + ballRadius x₀ / 2 + 1))
      unfold mittagLefflerThreshold at hceil
      have hcast : (⌈2 * (|x₀| + ballRadius x₀ / 2 + 1)⌉₊ : ℝ)
          ≥ 2 * (|x₀| + ballRadius x₀ / 2 + 1) := this
      linarith
    have hbound := mittagLefflerDeriv_far_bound (x₀ := x₀) (δ := ballRadius x₀ / 2) hy hthr
    have hnn1 : (0:ℝ) ≤ 1 / (y - ((n:ℝ) + 1)) ^ 2 := by positivity
    have hnn2 : (0:ℝ) ≤ 1 / (y + ((n:ℝ) + 1)) ^ 2 := by positivity
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- Summability of the Mittag-Leffler series terms themselves (not their derivatives) at a
    real non-integer basepoint, needed for `hasDerivAt_tsum_of_isPreconnected`'s `hg0`
    hypothesis. Follows the same comparison-with-`4/n²` pattern as
    `summable_realTrigammaSeriesInt`, one power of `n` lower. -/
theorem summable_mittagLefflerSeriesTerms {x₀ : ℝ} (hx₀ : ∀ n : ℤ, (n : ℝ) ≠ x₀) :
    Summable fun n : ℕ => 1 / (x₀ - ((n:ℝ) + 1)) + 1 / (x₀ + ((n:ℝ) + 1)) := by
  have hmem := ofReal_mem_integerComplement hx₀
  have hc := summable_cotTerm hmem
  have heq : (fun n : ℕ => ((1:ℂ) / ((x₀:ℂ) - (n + 1)) + 1 / ((x₀:ℂ) + (n + 1))))
      = (fun n : ℕ => (((1 / (x₀ - ((n:ℝ) + 1)) + 1 / (x₀ + ((n:ℝ) + 1)) : ℝ)) : ℂ)) := by
    funext n
    push_cast
    ring
  rw [heq] at hc
  rwa [Complex.summable_ofReal] at hc

/-- **Term-by-term differentiation of the real Mittag-Leffler cotangent series.** This is the
    main payoff of this section: at any real non-integer `x₀`, the series
    `∑' n, (1/(x-(n+1)) + 1/(x+(n+1)))` is differentiable at `x₀` with derivative
    `∑' n, (-(1/(x₀-(n+1))²) - 1/(x₀+(n+1))²)`, obtained by combining every ingredient built
    above (`hasDerivAt_mittagLefflerTerm`, `mittagLefflerDeriv_uniform_bound`,
    `summable_mittagLefflerUniformBound`, `summable_mittagLefflerSeriesTerms`) via Mathlib's
    `hasDerivAt_tsum_of_isPreconnected`, applied on the open interval
    `Set.Ioo (x₀ - ballRadius x₀ / 2) (x₀ + ballRadius x₀ / 2)`. -/
theorem hasDerivAt_mittagLefflerSeries {x₀ : ℝ} (hx₀ : ∀ n : ℤ, (n : ℝ) ≠ x₀) :
    HasDerivAt (fun x : ℝ => ∑' n : ℕ, (1 / (x - ((n:ℝ) + 1)) + 1 / (x + ((n:ℝ) + 1))))
      (∑' n : ℕ, (-(1 / (x₀ - ((n:ℝ) + 1)) ^ 2) + -(1 / (x₀ + ((n:ℝ) + 1)) ^ 2))) x₀ := by
  set δ' : ℝ := ballRadius x₀ / 2 with hδ'_def
  have hδpos : 0 < δ' := by have := ballRadius_pos hx₀; rw [hδ'_def]; linarith
  set t : Set ℝ := Set.Ioo (x₀ - δ') (x₀ + δ') with ht_def
  have htopen : IsOpen t := isOpen_Ioo
  have htconn : IsPreconnected t := isPreconnected_Ioo
  have hx₀t : x₀ ∈ t := by rw [ht_def]; constructor <;> linarith
  have hballmem : ∀ y ∈ t, |y - x₀| < δ' := by
    intro y hy
    rw [ht_def, Set.mem_Ioo] at hy
    rw [abs_lt]; constructor <;> linarith [hy.1, hy.2]
  have hg : ∀ (n : ℕ) (y : ℝ), y ∈ t →
      HasDerivAt (fun z : ℝ => 1 / (z - ((n:ℝ)+1)) + 1 / (z + ((n:ℝ)+1)))
        (-(1 / (y - ((n:ℝ)+1)) ^ 2) + -(1 / (y + ((n:ℝ)+1)) ^ 2)) y := by
    intro n y hy
    have hyball := hballmem y hy
    have ha_pos : (0:ℝ) < (n:ℝ) + 1 := by positivity
    apply hasDerivAt_mittagLefflerTerm
    · -- y ≠ (n+1): since |y - (n+1)| ≥ δ' > 0 by half_ballRadius_le_dist
      intro hcontra
      have hdist := half_ballRadius_le_dist hx₀ hyball ((n:ℤ) + 1)
      push_cast at hdist
      rw [← hδ'_def, hcontra] at hdist
      simp at hdist
      linarith
    · intro hcontra
      have hdist := half_ballRadius_le_dist hx₀ hyball (-((n:ℤ) + 1))
      push_cast at hdist
      rw [← hδ'_def] at hdist
      have : y - (-((n:ℝ)+1)) = y + ((n:ℝ)+1) := by ring
      rw [this, hcontra] at hdist
      simp at hdist
      linarith
  have hg' : ∀ (n : ℕ) (y : ℝ), y ∈ t →
      ‖(-(1 / (y - ((n:ℝ)+1)) ^ 2) + -(1 / (y + ((n:ℝ)+1)) ^ 2))‖
        ≤ mittagLefflerUniformBound x₀ n := by
    intro n y hy
    exact mittagLefflerDeriv_uniform_bound hx₀ (hballmem y hy) n
  have hg0 : Summable (fun n : ℕ => 1 / (x₀ - ((n:ℝ)+1)) + 1 / (x₀ + ((n:ℝ)+1))) :=
    summable_mittagLefflerSeriesTerms hx₀
  exact hasDerivAt_tsum_of_isPreconnected (summable_mittagLefflerUniformBound x₀) htopen htconn
    hg hg' hx₀t hg0 hx₀t

-- ---------------------------------------------------------------------------
-- 7. The closed-form derivative of `π cot(π x) - 1/x`, and the final reflection identity.
-- ---------------------------------------------------------------------------

/-- The derivative of `x ↦ π * Real.cot (π * x) - 1/x` at a real non-integer `x₀`, computed
    directly from `cot = cos/sin` via the quotient rule and chain rule (no series machinery). -/
theorem hasDerivAt_cot_sub_inv {x₀ : ℝ} (hx₀ : ∀ n : ℤ, (n : ℝ) ≠ x₀) :
    HasDerivAt (fun x : ℝ => π * Real.cot (π * x) - 1 / x)
      (-(π ^ 2 / Real.sin (π * x₀) ^ 2) + 1 / x₀ ^ 2) x₀ := by
  have hsin_ne : Real.sin (π * x₀) ≠ 0 := by
    intro hcontra
    rw [Real.sin_eq_zero_iff] at hcontra
    obtain ⟨n, hn⟩ := hcontra
    apply hx₀ n
    have hπ : (π:ℝ) ≠ 0 := Real.pi_ne_zero
    have hn' : (n:ℝ) * π = π * x₀ := hn
    rw [mul_comm π x₀] at hn'
    exact mul_right_cancel₀ hπ hn'
  have hx₀_ne : x₀ ≠ 0 := fun h => hx₀ 0 (by simp [h])
  have hsinderiv : HasDerivAt (fun x : ℝ => Real.sin (π * x)) (π * Real.cos (π * x₀)) x₀ := by
    have hc := (Real.hasDerivAt_sin (π * x₀)).comp x₀
      ((hasDerivAt_id x₀).const_mul π)
    simp only [mul_one] at hc
    convert hc using 1
    ring
  have hcosderiv : HasDerivAt (fun x : ℝ => Real.cos (π * x)) (-(π * Real.sin (π * x₀))) x₀ := by
    have hc := (Real.hasDerivAt_cos (π * x₀)).comp x₀
      ((hasDerivAt_id x₀).const_mul π)
    simp only [mul_one] at hc
    convert hc using 1
    ring
  have hcot : HasDerivAt (fun x : ℝ => Real.cos (π * x) / Real.sin (π * x))
      ((-(π * Real.sin (π * x₀)) * Real.sin (π * x₀) - Real.cos (π * x₀) * (π * Real.cos (π * x₀)))
        / Real.sin (π * x₀) ^ 2) x₀ :=
    hcosderiv.div hsinderiv hsin_ne
  have hcoteq : (fun x : ℝ => π * Real.cot (π * x))
      = (fun x : ℝ => π * (Real.cos (π * x) / Real.sin (π * x))) := by
    funext x; rw [Real.cot_eq_cos_div_sin]
  have hpicot : HasDerivAt (fun x : ℝ => π * Real.cot (π * x))
      (π * ((-(π * Real.sin (π * x₀)) * Real.sin (π * x₀)
        - Real.cos (π * x₀) * (π * Real.cos (π * x₀))) / Real.sin (π * x₀) ^ 2)) x₀ := by
    rw [hcoteq]
    exact hcot.const_mul π
  have hsimp : π * ((-(π * Real.sin (π * x₀)) * Real.sin (π * x₀)
      - Real.cos (π * x₀) * (π * Real.cos (π * x₀))) / Real.sin (π * x₀) ^ 2)
      = -(π ^ 2 / Real.sin (π * x₀) ^ 2) := by
    have hpyth : Real.sin (π * x₀) ^ 2 + Real.cos (π * x₀) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
    have hsinsq_ne : Real.sin (π * x₀) ^ 2 ≠ 0 := pow_ne_zero 2 hsin_ne
    field_simp
    nlinarith [hpyth]
  rw [hsimp] at hpicot
  have hinv : HasDerivAt (fun x : ℝ => 1 / x) (-(1 / x₀ ^ 2)) x₀ := by
    have := hasDerivAt_inv hx₀_ne
    simpa [one_div] using this
  have := hpicot.sub hinv
  simpa using this

/-- **The real-variable reflection identity for the trigamma-type series** (the single most
    valuable target sub-result identified in this file's task brief): for every real
    non-integer `x₀`,
    `∑' n : ℤ, 1/(x₀+n)² = π² / sin(π x₀)²`.

    Proof idea: `real_cot_series_rep'` shows the two functions `f = fun x ↦ π cot(π x) - 1/x`
    and `g = fun x ↦ ∑' n:ℕ, (1/(x-(n+1)) + 1/(x+(n+1)))` agree at *every* non-integer real `x`,
    in particular on a whole neighborhood of `x₀` (namely `Set.Ioo (x₀ - ballRadius x₀ / 2)
    (x₀ + ballRadius x₀ / 2)`, which contains no integer at all, by construction of
    `ballRadius`). Since `f` and `g` agree on a neighborhood of `x₀`, their derivatives at `x₀`
    coincide (`HasDerivAt.congr_of_eventuallyEq`). But `g`'s derivative at `x₀` was computed
    directly in `hasDerivAt_mittagLefflerSeries`, and `f`'s derivative at `x₀` was computed
    directly (independently, via the quotient rule) in `hasDerivAt_cot_sub_inv`. Equating the
    two derivatives and rewriting the `ℕ`-indexed sum as the `ℤ`-indexed
    `realTrigammaSeriesInt` (via `tsum_of_add_one_of_neg_add_one`) gives the claimed identity. -/
theorem realTrigammaSeriesInt_reflection {x₀ : ℝ} (hx₀ : ∀ n : ℤ, (n : ℝ) ≠ x₀) :
    realTrigammaSeriesInt x₀ = π ^ 2 / Real.sin (π * x₀) ^ 2 := by
  set δ' : ℝ := ballRadius x₀ / 2 with hδ'_def
  have hδpos : 0 < δ' := by have := ballRadius_pos hx₀; rw [hδ'_def]; linarith
  -- `f` and `g` agree on the whole ball around `x₀`.
  have heq_nhds : (fun x : ℝ => π * Real.cot (π * x) - 1 / x)
      =ᶠ[nhds x₀] (fun x : ℝ => ∑' n : ℕ, (1 / (x - ((n:ℝ) + 1)) + 1 / (x + ((n:ℝ) + 1)))) := by
    have hballopen : Set.Ioo (x₀ - δ') (x₀ + δ') ∈ nhds x₀ :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hballopen] with x hx
    have hxnotint : ∀ n : ℤ, (n : ℝ) ≠ x := by
      intro n hcontra
      have hdist := ballRadius_le_dist_to_int hx₀ n
      rw [Set.mem_Ioo] at hx
      have : |x₀ - (n:ℝ)| < δ' := by
        rw [abs_lt, hcontra]
        constructor <;> linarith [hx.1, hx.2]
      rw [hδ'_def] at this
      linarith
    exact real_cot_series_rep' hxnotint
  have hderiv_eq := (hasDerivAt_cot_sub_inv hx₀).congr_of_eventuallyEq heq_nhds.symm
  have hderiv_unique := hderiv_eq.unique (hasDerivAt_mittagLefflerSeries hx₀)
  -- Rewrite the RHS series (`ℕ`-indexed, from the derivative computation) as the
  -- `ℤ`-indexed `realTrigammaSeriesInt`, via `tsum_of_add_one_of_neg_add_one`.
  have h1 : Summable fun n : ℕ => 1 / (x₀ + ((n:ℝ) + 1)) ^ 2 := by
    have hbase := summable_realTrigammaSeriesNat (x₀ + 1)
    apply hbase.congr
    intro n; rw [show ((n:ℝ) + (x₀ + 1)) = x₀ + ((n:ℝ) + 1) by ring]
  have h2 : Summable fun n : ℕ => 1 / (x₀ - ((n:ℝ) + 1)) ^ 2 := by
    have hbase := summable_realTrigammaSeriesNat (1 - x₀)
    apply hbase.congr
    intro n
    rw [show ((n:ℝ) + (1 - x₀)) = -(x₀ - ((n:ℝ)+1)) by ring, neg_sq]
  have hzeq : realTrigammaSeriesInt x₀
      = (∑' n : ℕ, 1 / (x₀ + ((n:ℝ) + 1)) ^ 2) + 1 / x₀ ^ 2
        + ∑' n : ℕ, 1 / (x₀ - ((n:ℝ) + 1)) ^ 2 := by
    unfold realTrigammaSeriesInt
    have hcast1 : (fun n : ℕ => 1 / (x₀ + ((n:ℤ) + 1 : ℤ)) ^ 2)
        = (fun n : ℕ => 1 / (x₀ + ((n:ℝ) + 1)) ^ 2) := by funext n; push_cast; ring_nf
    have hcast2 : (fun n : ℕ => 1 / (x₀ + (-((n:ℤ) + 1) : ℤ)) ^ 2)
        = (fun n : ℕ => 1 / (x₀ - ((n:ℝ) + 1)) ^ 2) := by
      funext n; push_cast; ring_nf
    have h1' : Summable fun n : ℕ => 1 / (x₀ + ((n:ℤ) + 1 : ℤ)) ^ 2 := by
      rw [hcast1]; exact h1
    have h2' : Summable fun n : ℕ => 1 / (x₀ + (-((n:ℤ) + 1) : ℤ)) ^ 2 := by
      rw [hcast2]; exact h2
    have hsplit := tsum_of_add_one_of_neg_add_one (f := fun n : ℤ => 1 / (x₀ + n) ^ 2) h1' h2'
    simp only [Int.cast_zero, add_zero] at hsplit
    rw [hsplit, hcast1, hcast2]
  rw [hzeq]
  -- Combine with the derivative identity to conclude.
  have hne : ∑' n : ℕ, (-(1 / (x₀ - ((n:ℝ) + 1)) ^ 2) + -(1 / (x₀ + ((n:ℝ) + 1)) ^ 2))
      = -(∑' n : ℕ, 1 / (x₀ - ((n:ℝ) + 1)) ^ 2) + -(∑' n : ℕ, 1 / (x₀ + ((n:ℝ) + 1)) ^ 2) := by
    rw [Summable.tsum_add h2.neg h1.neg, tsum_neg, tsum_neg]
  rw [hne] at hderiv_unique
  linarith [hderiv_unique]

end RH.Criteria.NymanBeurling.VasyuninCotangentRecognition
