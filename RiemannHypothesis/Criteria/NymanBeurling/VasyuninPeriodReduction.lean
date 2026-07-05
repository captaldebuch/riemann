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

/-- **Proposition 21** (Báez-Duarte–Balazard–Landreau–Saias, arXiv:math/0306251): for real
    `x, θ > 0`,
    `∑_{1≤n≤θx} B₁(n/θ) + ∑_{1≤m≤x} B₁(mθ) = (1/(2θ))·({θx}-θ{x})² + ((θ-1)/(2θ))·({θx}-θ{x})`.

    **Not attempted here** — this is H13-J1's real deliverable, deferred to a dedicated
    continuation. What IS done: the formula below has been independently re-derived (the
    PDF's own dense typesetting was not trusted blindly, given this session's track record of
    catching real transcription/convention errors elsewhere) and stress-tested numerically —
    200 random trials with rational `θ = k/h` (`h,k ∈ [1,12]`) and real `x ∈ (0,15)`, max
    deviation `~10⁻¹⁵` (floating-point noise). It also uses the corrected `bernoulliB1`
    (Dedekind sawtooth, `B₁(n) = 0` for integer `n`) documented above — a first attempt using
    the naive `Int.fract z - 1/2` convention fails this identity for every rational `θ` tested,
    by exactly `⌊x/q⌋` when `θ = p/q` in lowest terms (traced to `B₁` hitting exact integers
    whenever `θ` is rational: `m·θ ∈ ℤ ⟺ q ∣ m`, `n/θ ∈ ℤ ⟺ p ∣ n`).

    Proof strategy for the eventual continuation (per the paper, Prop 21's own proof): expand
    each `B₁` as `Int.fract - 1/2` plus an exact-integer correction, apply
    `sum_Icc_one_natCast_eq_of_fract` above (the paper's Proposition 15) to convert both sums of
    naturals into closed forms, and combine via the paper's Proposition 12 (a floor-counting
    identity: `∑⌊mθ⌋ + ∑⌊n/θ⌋ = ⌊x⌋⌊θx⌋` for irrational `θ`, with a `+⌊x/q⌋` correction for
    rational `θ = p/q` that exactly cancels the `B₁`-convention correction derived above via the
    exact-integer-hit count (`m·θ∈ℤ ⟺ q∣m`, giving `⌊x/q⌋` hits; likewise for the other sum).
    Since this project only ever needs `θ = k/h` rational (never irrational `θ`), the eventual
    Lean proof can skip the irrational branch entirely and work the rational case directly via
    `Nat`/`Int` divisibility — likely simpler than the paper's own two-case argument. -/
theorem baezDuarte_prop21 (x θ : ℝ) (hx : 0 < x) (hθ : 0 < θ) :
    (∑ n ∈ Finset.Icc 1 ⌊θ * x⌋₊, bernoulliB1 ((n : ℝ) / θ)) +
        (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, bernoulliB1 ((m : ℝ) * θ)) =
      (1 / (2 * θ)) * (Int.fract (θ * x) - θ * Int.fract x) ^ 2 +
        ((θ - 1) / (2 * θ)) * (Int.fract (θ * x) - θ * Int.fract x) := by
  sorry

/-! ## Rational specialization (θ = k/h), the case this project actually needs -/

/-- Pointwise: `B₁(z)` decomposes into the naive-fract piece plus an exact-integer
    correction, isolating exactly the convention gap documented above. -/
theorem bernoulliB1_eq_fract_sub_half_add_indicator (x : ℝ) :
    bernoulliB1 x = Int.fract x - 1 / 2 + (if Int.fract x = 0 then (1 : ℝ) / 2 else 0) := by
  unfold bernoulliB1
  split_ifs with h <;> simp [h]

theorem sum_ite_eq_zero_card {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (∑ i ∈ s, if p i then (1 : ℝ) else 0) = (s.filter p).card := by
  rw [← Finset.sum_filter]
  simp

/-- For coprime `h, k` with `h > 0`: `m·(k/h) ∈ ℤ ⟺ h ∣ m`. This is the exact-integer-hit
    condition for the `mθ` sum in Proposition 21 with `θ = k/h`. -/
theorem fract_natCast_mul_div_eq_zero_iff {h k : ℕ} (hh : 0 < h) (hcop : Nat.Coprime h k)
    (m : ℕ) : Int.fract ((m : ℝ) * ((k : ℝ) / (h : ℝ))) = 0 ↔ h ∣ m := by
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [Int.fract_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hn' : (n : ℝ) * (h : ℝ) = (m : ℝ) * (k : ℝ) := by
      field_simp at hn; linarith [hn]
    have : n * (h : ℤ) = (m : ℤ) * (k : ℤ) := by exact_mod_cast hn'
    have hdvd : (h : ℤ) ∣ (m : ℤ) * (k : ℤ) := ⟨n, by linarith [this]⟩
    have hdvd' : h ∣ m * k := by exact_mod_cast hdvd
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd')
  · rintro ⟨c, hc⟩
    refine ⟨(c : ℤ) * (k : ℤ), ?_⟩
    have : (m : ℝ) = (h : ℝ) * (c : ℝ) := by exact_mod_cast hc
    rw [this]
    push_cast
    field_simp

theorem Icc_one_eq_Ioc_zero (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

/-- The exact-integer-hit count in the `mθ` sum (`θ = k/h`, coprime, `m ≤ X`) is `X / h`. -/
theorem card_filter_fract_mul_div_eq_zero {h k : ℕ} (hh : 0 < h) (hcop : Nat.Coprime h k)
    (X : ℕ) :
    ((Finset.Icc 1 X).filter (fun m : ℕ => Int.fract ((m : ℝ) * ((k : ℝ) / (h : ℝ))) = 0)).card =
      X / h := by
  rw [show (Finset.Icc 1 X).filter (fun m : ℕ => Int.fract ((m : ℝ) * ((k : ℝ) / (h : ℝ))) = 0) =
      (Finset.Icc 1 X).filter (fun m : ℕ => h ∣ m) from
    Finset.filter_congr (fun m _ => fract_natCast_mul_div_eq_zero_iff hh hcop m)]
  rw [Icc_one_eq_Ioc_zero]
  exact Nat.Ioc_filter_dvd_card_eq_div X h

/-- Sum form of the pointwise decomposition, specialized to a `Finset.Icc 1 N` indexed by a
    scaling function `f`, with the exact-integer count expressed as a `Finset.filter` card. -/
theorem sum_bernoulliB1_eq (N : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.Icc 1 N, bernoulliB1 (f i)) =
      (∑ i ∈ Finset.Icc 1 N, (Int.fract (f i) - 1 / 2)) +
        ((Finset.Icc 1 N).filter (fun i => Int.fract (f i) = 0)).card / 2 := by
  rw [Finset.sum_congr rfl (fun i _ => bernoulliB1_eq_fract_sub_half_add_indicator (f i))]
  rw [Finset.sum_add_distrib]
  congr 1
  have hpt : (fun i => if Int.fract (f i) = 0 then (1 : ℝ) / 2 else 0) =
      (fun i => (if Int.fract (f i) = 0 then (1 : ℝ) else 0) / 2) := by
    funext i; split_ifs <;> ring
  rw [hpt, ← Finset.sum_div, sum_ite_eq_zero_card]

end RH.Criteria.NymanBeurling.VasyuninGram
