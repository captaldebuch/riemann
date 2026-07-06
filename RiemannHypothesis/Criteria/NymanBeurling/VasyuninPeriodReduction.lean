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
lettered plan). Proposition 21 is fully proved for the rational case this project
actually needs (`θ = k/h`, see `baezDuarte_prop21_rat_of_prop12`), taking Proposition 12's
floor-sum identity as an explicit hypothesis (a genuine separate classical fact, not yet
proved — see that theorem's docstring). Proposition 22 is frozen below as a rational
`sorry`-bodied statement after direct PDF extraction and numerical verification. Its proof,
plus Propositions 16, 88, and 89 (the remaining analytic steps: Stieltjes integration by
parts, one limit, and one rational specialization), is deliberately NOT attempted in this
file — see the H13-J memory plan for the full sequencing.

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

/-- Floor-nesting: `⌊x⌋₊ / h = ⌊x/h⌋₊` (Nat division), a direct specialization of
    `Nat.floor_div_natCast`. -/
theorem natFloor_div_eq_natFloor_div (x : ℝ) (h : ℕ) : ⌊x⌋₊ / h = ⌊x / h⌋₊ :=
  (Nat.floor_div_natCast x h).symm

/-- Floor-nesting for the `θx = k·(x/h)` scaling: `⌊θx⌋₊ / k = ⌊x/h⌋₊` for `θ = k/h`, `h,k > 0`. -/
theorem natFloor_theta_mul_div_eq_natFloor_div {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (x : ℝ) :
    ⌊(k : ℝ) / (h : ℝ) * x⌋₊ / k = ⌊x / h⌋₊ := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have heq : (k : ℝ) / (h : ℝ) * x = (k : ℝ) * (x / h) := by ring
  have hdiv : (k : ℝ) * (x / h) / k = x / h := by field_simp
  have hnest := Nat.floor_div_natCast ((k : ℝ) * (x / h)) k
  rw [hdiv] at hnest
  rw [heq]
  exact hnest.symm

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

/-- Pure linear-algebra restatement of `Int.fract`'s definition, summed: turns
    `∑(Int.fract(f i) - 1/2)` into `∑f i - ∑⌊f i⌋ - N/2`. -/
theorem sum_fract_sub_half_eq (N : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.Icc 1 N, (Int.fract (f i) - 1 / 2)) =
      (∑ i ∈ Finset.Icc 1 N, f i) - (∑ i ∈ Finset.Icc 1 N, (⌊f i⌋ : ℝ)) - (N : ℝ) / 2 := by
  have h1 : (∑ i ∈ Finset.Icc 1 N, (Int.fract (f i) - 1 / 2)) =
      (∑ i ∈ Finset.Icc 1 N, Int.fract (f i)) - (Finset.Icc 1 N).card * (1 / 2 : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [h1, Nat.card_Icc]
  have h2 : (∑ i ∈ Finset.Icc 1 N, Int.fract (f i)) =
      (∑ i ∈ Finset.Icc 1 N, f i) - (∑ i ∈ Finset.Icc 1 N, (⌊f i⌋ : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold Int.fract
    ring
  rw [h2]
  push_cast
  ring

/-- Rewrites a sum of natural divisions as a count of lattice points under a rational slope,
    over the full rectangle `Finset.Icc 1 X ×ˢ Finset.Icc 1 Y`. -/
theorem sum_Icc_mul_div_eq_card_filter {h k X Y : ℕ} (hh : 0 < h)
    (hXY : ∀ m ∈ Finset.Icc 1 X, m * k / h ≤ Y) :
    ∑ m ∈ Finset.Icc 1 X, m * k / h =
      #{p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.2 * h ≤ p.1 * k} := by
  calc
    ∑ m ∈ Finset.Icc 1 X, m * k / h =
        ∑ m ∈ Finset.Icc 1 X, #{j ∈ Finset.Icc 1 Y | j * h ≤ m * k} := by
          apply Finset.sum_congr rfl
          intro m hm
          simpa [Finset.Ico_add_one_right_eq_Icc] using
            (ZMod.div_eq_filter_card (a := m * k) (b := h) (c := Y) hh (hXY m hm))
    _ = #{p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.2 * h ≤ p.1 * k} := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

/-- Symmetric variant of `sum_Icc_mul_div_eq_card_filter`, with the two coordinates swapped so
    both sums land in the same rectangle `Finset.Icc 1 X ×ˢ Finset.Icc 1 Y`. -/
theorem sum_Icc_mul_div_eq_card_filter_swap {h k X Y : ℕ} (hk : 0 < k)
    (hYX : ∀ n ∈ Finset.Icc 1 Y, n * h / k ≤ X) :
    ∑ n ∈ Finset.Icc 1 Y, n * h / k =
      #{p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.1 * k ≤ p.2 * h} := by
  calc
    ∑ n ∈ Finset.Icc 1 Y, n * h / k =
        #{p ∈ Finset.Icc 1 Y ×ˢ Finset.Icc 1 X | p.2 * k ≤ p.1 * h} := by
          simpa [mul_comm] using
            (sum_Icc_mul_div_eq_card_filter (h := k) (k := h) (X := Y) (Y := X) hk hYX)
    _ = #{p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.1 * k ≤ p.2 * h} := by
      apply Finset.card_equiv (Equiv.prodComm _ _)
      intro p
      simp [and_left_comm, and_assoc, mul_comm]

/-- The diagonal overlap in the lattice-point decomposition is exactly `X / h` when
    `gcd(h,k)=1` and `X / h = Y / k`. -/
theorem card_filter_mul_eq_eq_div {h k X Y : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hcop : Nat.Coprime h k) (hdiv : X / h = Y / k) :
    #{p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.1 * k = p.2 * h} = X / h := by
  calc
    #{p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.1 * k = p.2 * h} =
        #(Finset.Icc 1 (X / h)) := by
          symm
          apply Finset.card_bij (fun t _ => (h * t, k * t))
          · intro t ht
            rcases Finset.mem_Icc.mp ht with ⟨ht1, ht2⟩
            have htpos : 0 < t := lt_of_lt_of_le Nat.zero_lt_one ht1
            have hht : t * h ≤ X := (Nat.le_div_iff_mul_le hh).1 ht2
            have hkt : t * k ≤ Y := (Nat.le_div_iff_mul_le hk).1 (by simpa [hdiv] using ht2)
            refine Finset.mem_filter.mpr ?_
            refine ⟨Finset.mem_product.mpr ?_, ?_⟩
            · exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.mul_pos hh htpos),
                by simpa [Nat.mul_comm] using hht⟩,
                Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.mul_pos hk htpos),
                  by simpa [Nat.mul_comm] using hkt⟩⟩
            · simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          · intro t₁ ht₁ t₂ ht₂ hEq
            exact Nat.eq_of_mul_eq_mul_left hh (by simpa using congrArg Prod.fst hEq)
          · intro p hp
            rcases Finset.mem_filter.mp hp with ⟨hpRect, hpEq⟩
            rcases Finset.mem_product.mp hpRect with ⟨hpX, hpY⟩
            rcases Finset.mem_Icc.mp hpX with ⟨hp1lo, hp1hi⟩
            rcases Finset.mem_Icc.mp hpY with ⟨_, hp2hi⟩
            have hdvd : h ∣ p.1 := hcop.dvd_of_dvd_mul_right <| by
              refine ⟨p.2, ?_⟩
              simpa [Nat.mul_comm] using hpEq
            rcases hdvd with ⟨t, ht⟩
            have htpos : 0 < t := by
              have : 0 < h * t := by simpa [ht] using lt_of_lt_of_le Nat.zero_lt_one hp1lo
              exact Nat.pos_of_mul_pos_left this
            have htle : t ≤ X / h := (Nat.le_div_iff_mul_le hh).2 (by simpa [ht, Nat.mul_comm] using hp1hi)
            have hkeq : k * t = p.2 := by
              apply Nat.eq_of_mul_eq_mul_right hh
              calc
                (k * t) * h = (h * t) * k := by ac_rfl
                _ = p.2 * h := by simpa [ht] using hpEq
            refine ⟨t, Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt htpos, htle⟩, ?_⟩
            ext <;> simp [ht, hkeq]
    _ = X / h := by simpa using Nat.card_Icc 1 (X / h)

/-- Purely finite/natural-number form of Báez-Duarte–Balazard–Landreau–Saias Proposition 12,
    assuming the two monotonicity bounds needed to realize both floor sums on the full rectangle. -/
theorem baezDuarte_prop12_nat_aux {h k X Y : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hcop : Nat.Coprime h k)
    (hXY : ∀ m ∈ Finset.Icc 1 X, m * k / h ≤ Y)
    (hYX : ∀ n ∈ Finset.Icc 1 Y, n * h / k ≤ X)
    (hdiv : X / h = Y / k) :
    (∑ m ∈ Finset.Icc 1 X, m * k / h) + (∑ n ∈ Finset.Icc 1 Y, n * h / k) =
      X * Y + X / h := by
  let A := {p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.2 * h ≤ p.1 * k}
  let B := {p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.1 * k ≤ p.2 * h}
  rw [sum_Icc_mul_div_eq_card_filter hh hXY, sum_Icc_mul_div_eq_card_filter_swap hk hYX]
  have hAB : A = {p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.2 * h ≤ p.1 * k} := rfl
  have hBB : B = {p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.1 * k ≤ p.2 * h} := rfl
  rw [← Finset.card_union_add_card_inter A B]
  have hUnion : A ∪ B = Finset.Icc 1 X ×ˢ Finset.Icc 1 Y := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_union.mp hp with hpA | hpB
      · exact (Finset.mem_filter.mp hpA).1
      · exact (Finset.mem_filter.mp hpB).1
    · intro hp
      rcases le_total (p.2 * h) (p.1 * k) with hle | hle
      · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_filter.mpr ⟨hp, hle⟩
      · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_filter.mpr ⟨hp, hle⟩
  have hInter : A ∩ B = {p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.1 * k = p.2 * h} := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_inter.mp hp with ⟨hpA, hpB⟩
      rcases Finset.mem_filter.mp hpA with ⟨hpRect, hAineq⟩
      rcases Finset.mem_filter.mp hpB with ⟨_, hBineq⟩
      exact Finset.mem_filter.mpr ⟨hpRect, le_antisymm hBineq hAineq⟩
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpRect, hpEq⟩
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨hpRect, hpEq.ge⟩, Finset.mem_filter.mpr ⟨hpRect, hpEq.le⟩⟩
  calc
    #(A ∪ B) + #(A ∩ B) =
        #(Finset.Icc 1 X ×ˢ Finset.Icc 1 Y) +
          #{p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y | p.1 * k = p.2 * h} := by
            rw [hUnion, hInter]
    _ = #(Finset.Icc 1 X ×ˢ Finset.Icc 1 Y) + X / h := by
          rw [card_filter_mul_eq_eq_div hh hk hcop hdiv]
    _ = X * Y + X / h := by
          rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc]
          simp

/-- **Proposition 12, rational case** (Báez-Duarte–Balazard–Landreau–Saias): for coprime
    positive naturals `h, k` and real `x > 0`,
    `∑_{m≤⌊x⌋} ⌊m·k/h⌋ + ∑_{n≤⌊(k/h)x⌋} ⌊n·h/k⌋ = ⌊x⌋⌊(k/h)x⌋ + ⌊x/h⌋`.

    The proof is purely combinatorial: each floor sum becomes the cardinality of one triangle of
    lattice points in the rectangle `[1,⌊x⌋] × [1,⌊(k/h)x⌋]`; the two triangles cover the whole
    rectangle and overlap exactly on the diagonal `m*k = n*h`, whose cardinality is
    `⌊x / h⌋ = ⌊(k/h)x⌋ / k = ⌊x⌋ / h`. -/
theorem baezDuarte_prop12_rat {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hcop : Nat.Coprime h k) (x : ℝ) (hx : 0 < x) :
    (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (⌊(m : ℝ) * ((k : ℝ) / (h : ℝ))⌋ : ℝ)) +
        (∑ n ∈ Finset.Icc 1 ⌊(k : ℝ) / (h : ℝ) * x⌋₊, (⌊(n : ℝ) / ((k : ℝ) / (h : ℝ))⌋ : ℝ)) =
      (⌊x⌋₊ : ℝ) * (⌊(k : ℝ) / (h : ℝ) * x⌋₊ : ℝ) + (⌊x / (h : ℝ)⌋₊ : ℝ) := by
  set θ : ℝ := (k : ℝ) / (h : ℝ) with hθdef
  set X : ℕ := ⌊x⌋₊ with hXdef
  set Y : ℕ := ⌊θ * x⌋₊ with hYdef
  clear_value θ X Y
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hθpos : 0 < θ := by
    rw [hθdef]
    positivity
  have hθnonneg : 0 ≤ θ := hθpos.le
  have hXdiv : X / h = ⌊x / (h : ℝ)⌋₊ := by
    rw [hXdef]
    exact natFloor_div_eq_natFloor_div x h
  have hYdiv : Y / k = ⌊x / (h : ℝ)⌋₊ := by
    rw [hYdef, hθdef]
    exact natFloor_theta_mul_div_eq_natFloor_div hh hk x
  have hdiv : X / h = Y / k := by rw [hXdiv, hYdiv]
  have hXY : ∀ m ∈ Finset.Icc 1 X, m * k / h ≤ Y := by
    intro m hm
    have hmX : (m : ℝ) ≤ X := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    have hXx : (X : ℝ) ≤ x := by rw [hXdef]; exact Nat.floor_le hx.le
    have hmx : (m : ℝ) ≤ x := hmX.trans hXx
    have hle : ((m * k : ℕ) : ℝ) / (h : ℝ) ≤ θ * x := by
      rw [show ((m * k : ℕ) : ℝ) / (h : ℝ) = (m : ℝ) * θ by
        rw [hθdef]
        push_cast
        ring]
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hmx hθnonneg
    rw [show m * k / h = ⌊((m * k : ℕ) : ℝ) / (h : ℝ)⌋₊ by
      simpa using (Nat.floor_div_eq_div (K := ℝ) (m * k) h).symm, hYdef]
    exact Nat.floor_le_floor hle
  have hYX : ∀ n ∈ Finset.Icc 1 Y, n * h / k ≤ X := by
    intro n hn
    have hnY : (n : ℝ) ≤ Y := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hYθx : (Y : ℝ) ≤ θ * x := by
      rw [hYdef]
      exact Nat.floor_le (by positivity : (0 : ℝ) ≤ θ * x)
    have hnθx : (n : ℝ) ≤ θ * x := hnY.trans hYθx
    have hscaled :
        (n : ℝ) * ((h : ℝ) / (k : ℝ)) ≤ (θ * x) * ((h : ℝ) / (k : ℝ)) :=
      mul_le_mul_of_nonneg_right hnθx (by positivity)
    have hle : ((n * h : ℕ) : ℝ) / (k : ℝ) ≤ x := by
      have hleft : ((n * h : ℕ) : ℝ) / (k : ℝ) = (n : ℝ) * ((h : ℝ) / (k : ℝ)) := by
        push_cast
        ring
      have hright : (θ * x) * ((h : ℝ) / (k : ℝ)) = x := by
        rw [hθdef]
        field_simp [hhR, hkR]
      rw [hright] at hscaled
      have hle' : (n : ℝ) * ((h : ℝ) / (k : ℝ)) ≤ x := hscaled
      simpa [hleft, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hle'
    rw [show n * h / k = ⌊((n * h : ℕ) : ℝ) / (k : ℝ)⌋₊ by
      simpa using (Nat.floor_div_eq_div (K := ℝ) (n * h) k).symm, hXdef]
    exact Nat.floor_le_floor hle
  have hnat :
      (∑ m ∈ Finset.Icc 1 X, m * k / h) + (∑ n ∈ Finset.Icc 1 Y, n * h / k) =
        X * Y + X / h :=
    baezDuarte_prop12_nat_aux hh hk hcop hXY hYX hdiv
  have hsumX :
      (∑ m ∈ Finset.Icc 1 X, (⌊(m : ℝ) * θ⌋ : ℝ)) =
        ∑ m ∈ Finset.Icc 1 X, ((m * k / h : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [← natCast_floor_eq_intCast_floor (show (0 : ℝ) ≤ (m : ℝ) * θ by positivity)]
    have hfloor : ⌊(m : ℝ) * θ⌋₊ = m * k / h := by
      calc
        ⌊(m : ℝ) * θ⌋₊ = ⌊((m * k : ℕ) : ℝ) / (h : ℝ)⌋₊ := by
          congr 1
          rw [hθdef]
          push_cast
          ring
        _ = m * k / h := Nat.floor_div_eq_div (K := ℝ) (m * k) h
    rw [hfloor]
  have hsumY :
      (∑ n ∈ Finset.Icc 1 Y, (⌊(n : ℝ) / θ⌋ : ℝ)) =
        ∑ n ∈ Finset.Icc 1 Y, ((n * h / k : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [← natCast_floor_eq_intCast_floor (show (0 : ℝ) ≤ (n : ℝ) / θ by
      exact div_nonneg (by positivity) hθnonneg)]
    have hfloor : ⌊(n : ℝ) / θ⌋₊ = n * h / k := by
      calc
        ⌊(n : ℝ) / θ⌋₊ = ⌊((n * h : ℕ) : ℝ) / (k : ℝ)⌋₊ := by
          congr 1
          rw [hθdef]
          field_simp [hhR, hkR]
          push_cast
          ring
        _ = n * h / k := Nat.floor_div_eq_div (K := ℝ) (n * h) k
    rw [hfloor]
  have hFreal : ((X / h : ℕ) : ℝ) = (⌊x / (h : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast hXdiv
  have hXreal : (X : ℝ) = (⌊x⌋₊ : ℝ) := by rw [hXdef]
  have hYreal : (Y : ℝ) = (⌊(k : ℝ) / (h : ℝ) * x⌋₊ : ℝ) := by
    rw [hYdef, hθdef]
  have hprod :
      (X : ℝ) * (Y : ℝ) =
        (⌊x⌋₊ : ℝ) * (⌊(k : ℝ) / (h : ℝ) * x⌋₊ : ℝ) := by
    rw [hXreal, hYreal]
  have hmain :
      (∑ m ∈ Finset.Icc 1 X, (⌊(m : ℝ) * θ⌋ : ℝ)) +
          (∑ n ∈ Finset.Icc 1 Y, (⌊(n : ℝ) / θ⌋ : ℝ)) =
        (⌊x⌋₊ : ℝ) * (⌊(k : ℝ) / (h : ℝ) * x⌋₊ : ℝ) + (⌊x / (h : ℝ)⌋₊ : ℝ) := by
    rw [hsumY, hsumX]
    calc
      (∑ m ∈ Finset.Icc 1 X, ((m * k / h : ℕ) : ℝ)) +
          (∑ n ∈ Finset.Icc 1 Y, ((n * h / k : ℕ) : ℝ)) =
          (X : ℝ) * (Y : ℝ) + ((X / h : ℕ) : ℝ) := by
            exact_mod_cast hnat
      _ = (X : ℝ) * (Y : ℝ) + (⌊x / (h : ℝ)⌋₊ : ℝ) := by rw [hFreal]
      _ = (⌊x⌋₊ : ℝ) * (⌊(k : ℝ) / (h : ℝ) * x⌋₊ : ℝ) + (⌊x / (h : ℝ)⌋₊ : ℝ) := by
        simpa using congrArg (fun t : ℝ => t + (⌊x / (h : ℝ)⌋₊ : ℝ)) hprod
  simpa [hXdef, hYdef, hθdef] using hmain

/-- **Proposition 21, rational case** (`θ = k/h`, coprime, `h,k > 0` — the only case this
    project needs), assembled from Proposition 15 (`sum_Icc_one_natCast_eq_of_fract`, proved
    above) and Proposition 12's rational-case floor-sum identity, taken here as an explicit
    hypothesis (`hprop12`) rather than proved — a genuine, separate classical lattice-point
    counting fact (the BBLS paper itself cites Hardy-Littlewood, *The lattice-points of a
    right-angled triangle*, for this style of result), deliberately isolated rather than
    attempted here. This mirrors the project's own established discipline of taking hard,
    separable analytic content as an explicit hypothesis (e.g.
    `QuadraticInteractionAnalyticSubEstimates` in `QuadraticInteraction.lean`).

    Once `hprop12` is available, everything else is finite real-number algebra: expand both
    `bernoulliB1` sums via `sum_bernoulliB1_eq`, convert the resulting `Int.fract` sums via
    `sum_fract_sub_half_eq`, apply Proposition 15 to the two natural-number sums, substitute
    `hprop12` for the two floor sums, and simplify the exact-integer-hit correction terms via
    `card_filter_fract_mul_div_eq_zero` and the floor-nesting lemmas (both hit counts reduce to
    `⌊x/h⌋₊`, which is exactly `hprop12`'s own correction term — this is the "cancellation"
    the paper's own proof describes for the general case, made explicit and direct here for the
    rational case). Hand-verified symbolically (not just numerically) before writing this
    proof: every non-cancelling term matches the target RHS exactly. -/
theorem baezDuarte_prop21_rat_of_prop12_aux {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hcop : Nat.Coprime h k) (x : ℝ) (hx : 0 < x)
    (hprop12 :
      (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (⌊(m : ℝ) * ((k : ℝ) / (h : ℝ))⌋ : ℝ)) +
          (∑ n ∈ Finset.Icc 1 ⌊(k : ℝ) / (h : ℝ) * x⌋₊, (⌊(n : ℝ) / ((k : ℝ) / (h : ℝ))⌋ : ℝ)) =
        (⌊x⌋₊ : ℝ) * (⌊(k : ℝ) / (h : ℝ) * x⌋₊ : ℝ) + (⌊x / (h : ℝ)⌋₊ : ℝ)) :
    (∑ n ∈ Finset.Icc 1 ⌊(k : ℝ) / (h : ℝ) * x⌋₊, bernoulliB1 ((n : ℝ) / ((k : ℝ) / (h : ℝ)))) +
        (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, bernoulliB1 ((m : ℝ) * ((k : ℝ) / (h : ℝ)))) =
      (1 / (2 * ((k : ℝ) / (h : ℝ)))) *
          (Int.fract ((k : ℝ) / (h : ℝ) * x) - (k : ℝ) / (h : ℝ) * Int.fract x) ^ 2 +
        ((((k : ℝ) / (h : ℝ)) - 1) / (2 * ((k : ℝ) / (h : ℝ)))) *
          (Int.fract ((k : ℝ) / (h : ℝ) * x) - (k : ℝ) / (h : ℝ) * Int.fract x) := by
  set θ : ℝ := (k : ℝ) / (h : ℝ) with hθdef
  set X : ℕ := ⌊x⌋₊ with hXdef
  set Y : ℕ := ⌊θ * x⌋₊ with hYdef
  clear_value θ X Y
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  have hθR : θ ≠ 0 := hθpos.ne'
  -- Step 1+2: expand both B1 sums into fract-sums, then into plain sums minus floor-sums.
  have hB1n := sum_bernoulliB1_eq Y (fun n => (n : ℝ) / θ)
  have hB1m := sum_bernoulliB1_eq X (fun m => (m : ℝ) * θ)
  have hfn := sum_fract_sub_half_eq Y (fun n => (n : ℝ) / θ)
  have hfm := sum_fract_sub_half_eq X (fun m => (m : ℝ) * θ)
  -- Step 3: Proposition 15 applied to both index sets.
  have hP15n : (∑ n ∈ Finset.Icc 1 Y, (n : ℝ)) =
      (θ * x) ^ 2 / 2 - (θ * x) * Int.fract (θ * x) + (Int.fract (θ * x)) ^ 2 / 2 +
        (θ * x) / 2 - (Int.fract (θ * x)) / 2 := by
    have hh15 := sum_Icc_one_natCast_eq_of_fract (θ * x) (by positivity)
    rwa [← hYdef] at hh15
  have hP15m : (∑ m ∈ Finset.Icc 1 X, (m : ℝ)) =
      x ^ 2 / 2 - x * Int.fract x + (Int.fract x) ^ 2 / 2 + x / 2 - (Int.fract x) / 2 := by
    have hh15 := sum_Icc_one_natCast_eq_of_fract x hx.le
    rwa [← hXdef] at hh15
  -- Step 4: the two exact-integer-hit filter cards both reduce to ⌊x/h⌋₊.
  have hcardm : ((Finset.Icc 1 X).filter (fun m : ℕ => Int.fract ((m : ℝ) * θ) = 0)).card =
      X / h := by
    rw [hθdef]; exact card_filter_fract_mul_div_eq_zero hh hcop X
  have hcardn : ((Finset.Icc 1 Y).filter (fun n : ℕ => Int.fract ((n : ℝ) / θ) = 0)).card =
      Y / k := by
    rw [show (Finset.Icc 1 Y).filter (fun n : ℕ => Int.fract ((n : ℝ) / θ) = 0) =
        (Finset.Icc 1 Y).filter (fun n : ℕ => Int.fract ((n : ℝ) * ((h : ℝ) / (k : ℝ))) = 0) from
      Finset.filter_congr (fun n _ => by
        have heq : (n : ℝ) / θ = (n : ℝ) * ((h : ℝ) / (k : ℝ)) := by rw [hθdef]; field_simp
        rw [heq])]
    exact card_filter_fract_mul_div_eq_zero hk hcop.symm Y
  have hFdef : ((X / h : ℕ) : ℝ) = (⌊x / (h : ℝ)⌋₊ : ℝ) := by
    have := natFloor_div_eq_natFloor_div x h
    rw [← hXdef] at this
    exact_mod_cast this
  have hFdef2 : ((Y / k : ℕ) : ℝ) = (⌊x / (h : ℝ)⌋₊ : ℝ) := by
    have hnest := natFloor_theta_mul_div_eq_natFloor_div hh hk x
    rw [← hθdef, ← hYdef] at hnest
    exact_mod_cast hnest
  -- Split the two `∑ i, i/θ` and `∑ i, i*θ` sums into `(∑ i, i)` scaled by `θ`.
  have hsplitn : (∑ n ∈ Finset.Icc 1 Y, (n : ℝ) / θ) = (∑ n ∈ Finset.Icc 1 Y, (n : ℝ)) / θ := by
    rw [Finset.sum_div]
  have hsplitm : (∑ m ∈ Finset.Icc 1 X, (m : ℝ) * θ) = (∑ m ∈ Finset.Icc 1 X, (m : ℝ)) * θ := by
    rw [Finset.sum_mul]
  -- Assemble: rewrite both B1 sums, combine, substitute Proposition 12, cancel the F-terms.
  rw [hB1n, hB1m, hfn, hfm, hsplitn, hsplitm, hP15n, hP15m, hcardm, hcardn, hFdef, hFdef2]
  have hXR : (X : ℝ) = x - Int.fract x := by
    have h1 : ((X : ℤ) : ℝ) = x - Int.fract x := by
      rw [hXdef]
      have := Int.natCast_floor_eq_floor hx.le
      have h2 : ((⌊x⌋₊ : ℤ) : ℝ) = (⌊x⌋ : ℝ) := by exact_mod_cast this
      rw [h2]; linarith [Int.self_sub_fract x]
    exact_mod_cast h1
  have hYR : (Y : ℝ) = θ * x - Int.fract (θ * x) := by
    have h1 : ((Y : ℤ) : ℝ) = θ * x - Int.fract (θ * x) := by
      rw [hYdef]
      have := Int.natCast_floor_eq_floor (by positivity : (0:ℝ) ≤ θ * x)
      have h2 : ((⌊θ * x⌋₊ : ℤ) : ℝ) = (⌊θ * x⌋ : ℝ) := by exact_mod_cast this
      rw [h2]; linarith [Int.self_sub_fract (θ * x)]
    exact_mod_cast h1
  rw [hXR, hYR] at hprop12 ⊢
  linear_combination (norm := (field_simp; ring)) -hprop12

/-- **Proposition 21, rational case** (`θ = k/h`, coprime, `h,k > 0`), now unconditional:
    the classical floor-sum input is supplied by `baezDuarte_prop12_rat`. -/
theorem baezDuarte_prop21_rat_of_prop12 {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hcop : Nat.Coprime h k) (x : ℝ) (hx : 0 < x) :
    (∑ n ∈ Finset.Icc 1 ⌊(k : ℝ) / (h : ℝ) * x⌋₊, bernoulliB1 ((n : ℝ) / ((k : ℝ) / (h : ℝ)))) +
        (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, bernoulliB1 ((m : ℝ) * ((k : ℝ) / (h : ℝ)))) =
      (1 / (2 * ((k : ℝ) / (h : ℝ)))) *
          (Int.fract ((k : ℝ) / (h : ℝ) * x) - (k : ℝ) / (h : ℝ) * Int.fract x) ^ 2 +
        ((((k : ℝ) / (h : ℝ)) - 1) / (2 * ((k : ℝ) / (h : ℝ)))) *
          (Int.fract ((k : ℝ) / (h : ℝ) * x) - (k : ℝ) / (h : ℝ) * Int.fract x) := by
  exact baezDuarte_prop21_rat_of_prop12_aux hh hk hcop x hx
    (baezDuarte_prop12_rat hh hk hcop x hx)

/-! ## Proposition 22 statement (rational θ = k/h)

The next BBLS step is Proposition 22: a Riemann--Stieltjes integration-by-parts
identity obtained from Proposition 21.  This project only needs the rational
specialization `θ = k/h`, so the frozen statement below follows the same convention as
`baezDuarte_prop21_rat_of_prop12`.

The statement was extracted directly from the saved PDF, visually checked against the
rendered page, and numerically verified by exact piecewise integration for several
rational `(x, θ)` test cases before being introduced here.  The proof is deliberately
left for the next continuation: it should be a discrete Abel/Stieltjes summation-by-parts
argument, not a new analytic estimate.
-/

/-- **Proposition 22, rational case** (`θ = k/h`, coprime, `h,k > 0`), from
    Báez-Duarte--Balazard--Landreau--Saias, arXiv:math/0306251.

    The paper's statement for real positive `x, θ` is:
    `∑_{1≤m≤x} B₁(mθ)/m + θ ∑_{1≤n≤θx} B₁(n/θ)/n`
    equals the displayed integral expression.  Here it is specialized to the rational
    parameter `θ = k/h`, the only case needed downstream for Vasyunin period reduction.
-/
theorem baezDuarte_prop22_rat {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hcop : Nat.Coprime h k) (x : ℝ) (hx : 0 < x) :
    let θ : ℝ := (k : ℝ) / (h : ℝ)
    (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, bernoulliB1 ((m : ℝ) * θ) / (m : ℝ)) +
        θ * (∑ n ∈ Finset.Icc 1 ⌊θ * x⌋₊, bernoulliB1 ((n : ℝ) / θ) / (n : ℝ)) =
      (θ / 2) * (∫ t in (0 : ℝ)..x, (Int.fract t) ^ 2 / t ^ 2) +
        (1 / 2) * (∫ t in (0 : ℝ)..(θ * x), (Int.fract t) ^ 2 / t ^ 2) -
        (∫ t in (0 : ℝ)..x, (Int.fract t * Int.fract (θ * t)) / t ^ 2) +
        ((θ - 1) / 2) * Real.log (1 / θ) +
        ((θ - 1) / 2) * (∫ t in x..(θ * x), Int.fract t / t ^ 2) +
        (1 / (2 * θ * x)) * (Int.fract (θ * x) - θ * Int.fract x) ^ 2 +
        ((θ - 1) / (2 * θ * x)) * (Int.fract (θ * x) - θ * Int.fract x) := by
  sorry

end RH.Criteria.NymanBeurling.VasyuninGram
