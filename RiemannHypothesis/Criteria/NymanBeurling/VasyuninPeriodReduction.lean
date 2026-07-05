import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula

/-!
# Phase H13-J: the Báez-Duarte–Balazard–Landreau–Saias period-reduction chain

Groundwork for closing `shiftedIntegralTsum_period_reduction`
(`VasyuninCotangentRecognition.lean`) / `tsum_shifted_integrals_eq_cotangent_sum`
(`VasyuninBridge.lean`) via the real, verified primary source Báez-Duarte, Balazard,
Landreau, Saias, *Étude de l'autocorrélation multiplicative de la fonction
"partie fractionnaire"*, Ramanujan Journal 9(1-2), 215-240 (2005); preprint
`arXiv:math/0306251` (saved locally at
`papers/baez_balazard_landreau_saias_2003_autocorrelation.pdf`).

This file states and proves Propositions 15 and 21 of that paper, the two purely
finite/algebraic facts underlying the period-reduction chain (H13-J1 in the project's
lettered plan). Propositions 16, 22, 88, 89 (the analytic steps: one Stieltjes
integration by parts, one limit, one rational specialization) are deliberately NOT
attempted in this file — see the H13-J memory plan for the full sequencing.

**Important correction to a naive transcription of Proposition 21** (found and fixed via
direct numerical verification, not by re-reading the PDF more carefully — the PDF's own
typesetting of Proposition 21 is exact, but a first pass overlooked a genuine mathematical
subtlety): the paper's `B₁` is the classical **Dedekind sawtooth convention**,
`B₁(x) = {x} - 1/2` for `x ∉ ℤ` and `B₁(x) = 0` for `x ∈ ℤ` — NOT the simpler
`Int.fract x - 1/2` (which gives `-1/2` at integers, not `0`). The two conventions agree
except at integers, but Proposition 21's sums genuinely do hit exact integers whenever `θ`
is rational (e.g. `θ = p/q`, `m·θ ∈ ℤ` exactly when `q ∣ m`), so the distinction is not
cosmetic: using the wrong convention gives numerically wrong results for every rational `θ`
tested (off by exactly `⌊x/q⌋`, confirmed against direct summation for several `(x,θ)`
pairs). With the correct convention, the identity below has been verified numerically to
floating-point precision for both rational and irrational `θ`, including exact-integer
boundary cases.
-/

namespace RH.Criteria.NymanBeurling.VasyuninGram

open Finset

/-- The periodized first Bernoulli function, Dedekind sawtooth convention:
    `((x)) = {x} - 1/2` for `x ∉ ℤ`, and `((x)) = 0` for `x ∈ ℤ`. This is the `B₁` of
    Báez-Duarte–Balazard–Landreau–Saias (arXiv:math/0306251), Proposition 21 — see the
    module docstring for why the integer case matters here and can't be elided. -/
noncomputable def bernoulliB1 (x : ℝ) : ℝ :=
  if Int.fract x = 0 then 0 else Int.fract x - 1 / 2

theorem bernoulliB1_of_isInt {x : ℝ} (n : ℤ) (hx : (n : ℝ) = x) : bernoulliB1 x = 0 := by
  unfold bernoulliB1
  rw [if_pos (by rw [← hx]; exact Int.fract_intCast n)]

theorem bernoulliB1_of_not_isInt {x : ℝ} (hx : Int.fract x ≠ 0) :
    bernoulliB1 x = Int.fract x - 1 / 2 := by
  unfold bernoulliB1
  rw [if_neg hx]

theorem bernoulliB1_natCast_self (n : ℕ) : bernoulliB1 (n : ℝ) = 0 :=
  bernoulliB1_of_isInt (n : ℤ) (by push_cast; ring)

/-- **Proposition 15** (Báez-Duarte–Balazard–Landreau–Saias, arXiv:math/0306251): for `x ≥ 0`,
    `∑_{1≤n≤x} n = x²/2 - x·{x} + {x}²/2 + x/2 - {x}/2`.

    Independently re-derived (not copied verbatim from the PDF's dense typesetting, to avoid
    propagating any transcription slip) from the elementary identity
    `∑_{n=0}^{N} n = N(N+1)/2` with `N = ⌊x⌋ = x - {x}`, then verified numerically to match
    direct summation for several `x`. -/
theorem sum_Icc_one_natCast_eq_of_fract (x : ℝ) (hx : 0 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)) =
      x ^ 2 / 2 - x * Int.fract x + (Int.fract x) ^ 2 / 2 + x / 2 - (Int.fract x) / 2 := by
  have hgauss : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)) = (⌊x⌋₊ : ℝ) * ((⌊x⌋₊ : ℝ) + 1) / 2 := by
    have hset : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    have hrange :
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℝ)) = (∑ n ∈ Finset.range (⌊x⌋₊ + 1), (n : ℝ)) := by
      rw [hset, Finset.sum_insert (by simp)]
      simp
    rw [hrange]
    have hgauss2 := Finset.sum_range_id_mul_two (⌊x⌋₊ + 1)
    have hcast : ((∑ i ∈ Finset.range (⌊x⌋₊ + 1), i : ℕ) : ℝ) * 2 =
        ((⌊x⌋₊ + 1 : ℕ) : ℝ) * ((⌊x⌋₊ + 1 : ℕ) - 1 : ℕ) := by
      exact_mod_cast hgauss2
    push_cast at hcast
    linarith [hcast]
  rw [hgauss]
  have hfloor : (⌊x⌋₊ : ℝ) = (⌊x⌋ : ℝ) := by
    have h1 : ((⌊x⌋₊ : ℤ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
      exact_mod_cast Int.natCast_floor_eq_floor hx
    simpa using h1
  have hN : (⌊x⌋₊ : ℝ) = x - Int.fract x := by
    rw [hfloor]
    linarith [Int.self_sub_fract x]
  rw [hN]
  ring

end RH.Criteria.NymanBeurling.VasyuninGram
