import RiemannHypothesis.Criteria.NymanBeurling.MobiusSummatoryClassical
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-! # H14M-B: de la Vallée Poussin zero-free-region assembly -/

namespace RH.Criteria.NymanBeurling.MobiusSummatory

open Filter Finset Topology
open scoped ArithmeticFunction BigOperators LSeries.notation

section ThreeFourOneLogDerivative

open Complex

private noncomputable def vonMangoldtCosTerm (σ t : ℝ) (n : ℕ) : ℝ :=
  if _ : n = 0 then 0
  else Λ n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n)

private lemma summable_vonMangoldtCosTerm {σ t : ℝ} (hσ : 1 < σ) :
    Summable (vonMangoldtCosTerm σ t) := by
  have hs : 1 < (σ + Complex.I * t : ℂ).re := by simpa using hσ
  have hsum : Summable (fun n : ℕ =>
      (LSeries.term ↗Λ (σ + Complex.I * t : ℂ) n).re) :=
    (Complex.hasSum_re
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).hasSum).summable
  apply hsum.congr
  intro n
  by_cases hn : n = 0
  · simp [hn, vonMangoldtCosTerm, LSeries.term]
  · simpa [hn, vonMangoldtCosTerm] using
      deLaValleePoussin_vonMangoldt_term_re_eq_cos
        (σ := σ) (t := t) hn

private lemma neg_zeta_logDeriv_re_eq_tsum_vonMangoldtCosTerm
    {σ t : ℝ} (hσ : 1 < σ) :
    (-deriv riemannZeta (σ + Complex.I * t : ℂ) /
        riemannZeta (σ + Complex.I * t : ℂ)).re =
      ∑' n : ℕ, vonMangoldtCosTerm σ t n := by
  simpa [vonMangoldtCosTerm] using
    deLaValleePoussin_neg_zeta_logDeriv_re_eq_tsum_cos
      (σ := σ) (t := t) hσ

/-- Z1: the logarithmic-derivative form of the de la Vallée Poussin
`3-4-1` positivity inequality. -/
theorem deLaValleePoussin_logDeriv_three_four_one_nonneg
    {σ t : ℝ} (hσ : 1 < σ) :
    0 ≤
      3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re +
      4 * (-deriv riemannZeta (σ + Complex.I * t : ℂ) /
        riemannZeta (σ + Complex.I * t : ℂ)).re +
      (-deriv riemannZeta (σ + Complex.I * (2 * t) : ℂ) /
        riemannZeta (σ + Complex.I * (2 * t) : ℂ)).re := by
  have hzero :
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re =
        ∑' n : ℕ, vonMangoldtCosTerm σ 0 n := by
    simpa using
      neg_zeta_logDeriv_re_eq_tsum_vonMangoldtCosTerm
        (σ := σ) (t := 0) hσ
  have hdouble :
      (-deriv riemannZeta (σ + Complex.I * (2 * t) : ℂ) /
          riemannZeta (σ + Complex.I * (2 * t) : ℂ)).re =
        ∑' n : ℕ, vonMangoldtCosTerm σ (2 * t) n := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
      neg_zeta_logDeriv_re_eq_tsum_vonMangoldtCosTerm
        (σ := σ) (t := 2 * t) hσ
  rw [hzero,
    neg_zeta_logDeriv_re_eq_tsum_vonMangoldtCosTerm
      (σ := σ) (t := t) hσ,
    hdouble]
  have hsum₀ : Summable (vonMangoldtCosTerm σ 0) :=
    summable_vonMangoldtCosTerm hσ
  have hsum₁ : Summable (vonMangoldtCosTerm σ t) :=
    summable_vonMangoldtCosTerm hσ
  have hsum₂ : Summable (vonMangoldtCosTerm σ (2 * t)) :=
    summable_vonMangoldtCosTerm hσ
  rw [← hsum₀.tsum_mul_left 3, ← hsum₁.tsum_mul_left 4,
    ← (hsum₀.mul_left 3).tsum_add (hsum₁.mul_left 4),
    ← ((hsum₀.mul_left 3).add (hsum₁.mul_left 4)).tsum_add hsum₂]
  apply tsum_nonneg
  intro n
  by_cases hn : n = 0
  · simp [hn, vonMangoldtCosTerm]
  · simp only [vonMangoldtCosTerm, hn, ↓reduceDIte, zero_mul, Real.cos_zero,
      mul_one]
    have hΛ : 0 ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    have hpow : 0 ≤ (n : ℝ) ^ (-σ) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    have htrig :=
      deLaValleePoussin_three_four_one_trig_nonneg (t * Real.log n)
    have htwo : (2 * t) * Real.log n = 2 * (t * Real.log n) := by ring
    rw [htwo]
    calc
      3 * (Λ n * (n : ℝ) ^ (-σ)) +
            4 * (Λ n * (n : ℝ) ^ (-σ) *
              Real.cos (t * Real.log n)) +
            Λ n * (n : ℝ) ^ (-σ) *
              Real.cos (2 * (t * Real.log n)) =
          (Λ n * (n : ℝ) ^ (-σ)) *
            (3 + 4 * Real.cos (t * Real.log n) +
              Real.cos (2 * (t * Real.log n))) := by ring
      _ ≥ 0 := mul_nonneg (mul_nonneg hΛ hpow) htrig

end ThreeFourOneLogDerivative

section PoleLogDerivativeBound

open Complex

/-- The pole-removed zeta function is analytic at every point. -/
lemma zetaPoleRemoved_analyticAt (s : ℂ) :
    AnalyticAt ℂ zetaPoleRemoved s := by
  by_cases hs : s = 1
  · simpa [hs] using zetaPoleRemoved_analyticAt_one
  · have hprod : AnalyticAt ℂ
        (fun z : ℂ => (z - 1) * riemannZeta z) s :=
      (analyticAt_id.sub analyticAt_const).mul
        (analyticOn_riemannZeta s (by simpa using hs))
    apply hprod.congr
    filter_upwards [eventually_ne_nhds hs] with z hz
    exact (zetaPoleRemoved_of_ne_one hz).symm

/-- On the real interval `[1, 2]`, removing the pole introduces no zero. -/
lemma zetaPoleRemoved_ne_zero_of_real_mem_Icc {σ : ℝ}
    (hσ : σ ∈ Set.Icc (1 : ℝ) 2) :
    zetaPoleRemoved (σ : ℂ) ≠ 0 := by
  rcases hσ with ⟨hσ1, _⟩
  by_cases heq : σ = 1
  · subst σ
    simp
  · have hσgt : 1 < σ := lt_of_le_of_ne hσ1 (Ne.symm heq)
    rw [zetaPoleRemoved_of_ne_one (by exact_mod_cast heq)]
    exact mul_ne_zero
      (sub_ne_zero.mpr (by exact_mod_cast heq))
      (riemannZeta_ne_zero_of_one_lt_re (by simpa using hσgt))

/-- The bounded regular contribution to `-ζ'/ζ` after its pole is removed. -/
noncomputable def zetaPoleLogDerivRemainder (σ : ℝ) : ℝ :=
  -(deriv zetaPoleRemoved (σ : ℂ) / zetaPoleRemoved (σ : ℂ)).re

lemma continuousOn_zetaPoleLogDerivRemainder :
    ContinuousOn zetaPoleLogDerivRemainder (Set.Icc (1 : ℝ) 2) := by
  intro σ hσ
  have hGne := zetaPoleRemoved_ne_zero_of_real_mem_Icc hσ
  have hcoe : ContinuousAt (fun x : ℝ => (x : ℂ)) σ :=
    Complex.continuous_ofReal.continuousAt
  have hG : ContinuousAt (fun x : ℝ => zetaPoleRemoved (x : ℂ)) σ :=
    (zetaPoleRemoved_analyticAt (σ : ℂ)).continuousAt.comp hcoe
  have hG' : ContinuousAt
      (fun x : ℝ => deriv zetaPoleRemoved (x : ℂ)) σ :=
    (zetaPoleRemoved_analyticAt (σ : ℂ)).deriv.continuousAt.comp hcoe
  have hre : ContinuousAt (fun x : ℝ =>
      (deriv zetaPoleRemoved (x : ℂ) / zetaPoleRemoved (x : ℂ)).re) σ :=
    Complex.continuous_re.continuousAt.comp (hG'.div hG hGne)
  exact hre.neg.continuousWithinAt

/-- Algebraic separation of the pole contribution from the logarithmic
derivative of zeta. -/
lemma neg_zeta_logDeriv_eq_inv_sub_poleRemovedLogDeriv
    {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    -deriv riemannZeta s / riemannZeta s =
      1 / (s - 1) - deriv zetaPoleRemoved s / zetaPoleRemoved s := by
  rw [zetaPoleRemoved_of_ne_one hs, deriv_zetaPoleRemoved_of_ne_one hs]
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp [hsub, hz]
  ring

/-- Z2: the real pole term dominates `-ζ'/ζ` up to one fixed constant on
`1 < σ ≤ 2`.  Compactness absorbs the portion away from the pole. -/
theorem deLaValleePoussin_neg_logDeriv_real_le_pole_add_const :
    ∃ A > 0, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤
        1 / (σ - 1) + A := by
  rcases isCompact_Icc.bddAbove_image
      continuousOn_zetaPoleLogDerivRemainder with ⟨A₀, hA₀⟩
  refine ⟨max 1 A₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro σ hσ1 hσ2
  have hmem : σ ∈ Set.Icc (1 : ℝ) 2 := ⟨hσ1.le, hσ2⟩
  have hrem : zetaPoleLogDerivRemainder σ ≤ max 1 A₀ :=
    (hA₀ (Set.mem_image_of_mem zetaPoleLogDerivRemainder hmem)).trans
      (le_max_right _ _)
  have hs : (σ : ℂ) ≠ 1 := by exact_mod_cast ne_of_gt hσ1
  have hz : riemannZeta (σ : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ1)
  have hid := neg_zeta_logDeriv_eq_inv_sub_poleRemovedLogDeriv hs hz
  have hinv :
      1 / ((σ : ℂ) - 1) = ((1 / (σ - 1) : ℝ) : ℂ) := by
    calc
      1 / ((σ : ℂ) - 1) = 1 / ((σ - 1 : ℝ) : ℂ) := by norm_num
      _ = ((1 / (σ - 1) : ℝ) : ℂ) :=
        (Complex.ofReal_div 1 (σ - 1)).symm
  have hre :
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re =
        1 / (σ - 1) + zetaPoleLogDerivRemainder σ := by
    calc
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re =
          (1 / ((σ : ℂ) - 1) -
            deriv zetaPoleRemoved (σ : ℂ) /
              zetaPoleRemoved (σ : ℂ)).re := congrArg Complex.re hid
      _ = (1 / ((σ : ℂ) - 1)).re -
            (deriv zetaPoleRemoved (σ : ℂ) /
              zetaPoleRemoved (σ : ℂ)).re := rfl
      _ = (((1 / (σ - 1) : ℝ) : ℂ)).re -
            (deriv zetaPoleRemoved (σ : ℂ) /
              zetaPoleRemoved (σ : ℂ)).re := by rw [hinv]
      _ = 1 / (σ - 1) + zetaPoleLogDerivRemainder σ := by
        change (1 / (σ - 1) : ℝ) -
            (deriv zetaPoleRemoved (σ : ℂ) /
              zetaPoleRemoved (σ : ℂ)).re =
          1 / (σ - 1) -
            (deriv zetaPoleRemoved (σ : ℂ) /
              zetaPoleRemoved (σ : ℂ)).re
        rfl
  rw [hre]
  linarith

end PoleLogDerivativeBound

section ZetaLogDerivativeDiscBound

open Complex

/--
Z3: the one quantitative complex-analytic input still missing from Mathlib for
the classical de la Vallée Poussin argument.

Mathlib supplies Borel--Carathéodory, Jensen's formula, discreteness of the
zeta zeros, and analytic order/factorization.  What is not currently supplied
is the quantitative application of those tools to zeta in a disc centered at
height `t`: a logarithmic vertical bound for `-ζ'/ζ`, together with the same
bound after retaining the contribution of a specified zero.  The latter is
stated with coefficient one, so it applies to zeros of arbitrary positive
multiplicity (and deliberately does not assume a simple zero).

The companion diagnostic checks the normalization on the first twenty
critical-line zeros; it suggests that `C = 1` has a wide numerical margin.
No numerical observation is used in this hypothesis package.
-/
structure ZetaLogDerivDiscBound where
  C : ℝ
  C_nonneg : 0 ≤ C
  vertical_bound :
    ∀ {σ t : ℝ}, 1 < σ → σ ≤ 2 → t ≠ 0 →
      (-deriv riemannZeta (σ + Complex.I * t : ℂ) /
          riemannZeta (σ + Complex.I * t : ℂ)).re ≤
        C * Real.log (|t| + 2)
  zero_contribution_bound :
    ∀ {σ β t : ℝ}, 1 < σ → σ ≤ 2 → β ≤ 1 → t ≠ 0 →
      riemannZeta (β + Complex.I * t : ℂ) = 0 →
      (-deriv riemannZeta (σ + Complex.I * t : ℂ) /
          riemannZeta (σ + Complex.I * t : ℂ)).re ≤
        -1 / (σ - β) + C * Real.log (|t| + 2)

private lemma three_four_one_forces_repulsion
    {A C l logHeight delta x : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hl : 0 < l)
    (hlL : l ≤ logHeight) (hL : 0 < logHeight)
    (hδ : 0 < delta) (hx : 0 ≤ x)
    (hδsmall : delta ≤ 1 / (10 * (3 * A / l + 6 * C + 1)))
    (hmain :
      0 ≤ 3 * logHeight / delta + 3 * A -
        4 / (delta / logHeight + x) + 6 * C * logHeight) :
    delta / 4 ≤ x * logHeight := by
  by_contra hn
  have hxlt : x * logHeight < delta / 4 := lt_of_not_ge hn
  have hqpos : 0 < delta / logHeight + x :=
    add_pos_of_pos_of_nonneg (div_pos hδ hL) hx
  have hqLt :
      delta / logHeight + x < 5 * delta / (4 * logHeight) := by
    calc
      delta / logHeight + x =
          (delta + x * logHeight) / logHeight := by field_simp
      _ < (delta + delta / 4) / logHeight :=
        (div_lt_div_iff_of_pos_right hL).2 (by linarith)
      _ = 5 * delta / (4 * logHeight) := by field_simp; norm_num
  have hinv :
      4 * logHeight / (5 * delta) < 1 / (delta / logHeight + x) := by
    have h := one_div_lt_one_div_of_lt hqpos hqLt
    calc
      4 * logHeight / (5 * delta) =
          1 / (5 * delta / (4 * logHeight)) := by field_simp
      _ < 1 / (delta / logHeight + x) := h
  have hBpos : 0 < 3 * A / l + 6 * C + 1 := by positivity
  have hδB : delta * (3 * A / l + 6 * C + 1) ≤ 1 / 10 := by
    have h := (le_div_iff₀
      (by positivity : 0 < 10 * (3 * A / l + 6 * C + 1))).mp hδsmall
    nlinarith
  have hAl : A / logHeight ≤ A / l :=
    div_le_div_of_nonneg_left hA hl hlL
  have htarget :
      3 * A + 6 * C * logHeight < logHeight / (5 * delta) := by
    have haux : delta * (3 * A / logHeight + 6 * C) < 1 / 5 := by
      have hcomp : delta * (3 * A / logHeight + 6 * C) ≤
          delta * (3 * A / l + 6 * C) := by gcongr
      nlinarith
    apply (lt_div_iff₀ (by positivity : 0 < 5 * delta)).2
    calc
      (3 * A + 6 * C * logHeight) * (5 * delta) =
          5 * logHeight * (delta * (3 * A / logHeight + 6 * C)) := by
        field_simp
      _ < 5 * logHeight * (1 / 5) := by gcongr
      _ = logHeight := by ring
  have hfour :
      16 * logHeight / (5 * delta) < 4 / (delta / logHeight + x) := by
    calc
      16 * logHeight / (5 * delta) =
          4 * (4 * logHeight / (5 * delta)) := by ring
      _ < 4 * (1 / (delta / logHeight + x)) := by gcongr
      _ = 4 / (delta / logHeight + x) := by ring
  have hneg :
      -4 / (delta / logHeight + x) <
        -16 * logHeight / (5 * delta) := by
    calc
      -4 / (delta / logHeight + x) =
          -(4 / (delta / logHeight + x)) := by ring
      _ < -(16 * logHeight / (5 * delta)) := neg_lt_neg hfour
      _ = -16 * logHeight / (5 * delta) := by ring
  have hbad :
      0 < 3 * logHeight / delta + 3 * A -
        16 * logHeight / (5 * delta) + 6 * C * logHeight := by
    linarith
  have hid :
      3 * logHeight / delta + 3 * A -
          16 * logHeight / (5 * delta) + 6 * C * logHeight =
        3 * A + 6 * C * logHeight - logHeight / (5 * delta) := by
    field_simp
    ring
  rw [hid] at hbad
  linarith

/--
Z4, nonreal part: the disc logarithmic-derivative package and the proved
`3-4-1`/pole estimates repel every nonreal zeta zero from the line `Re s = 1`
by a uniform logarithmic distance.  No assumption on the zero's multiplicity
is made.
-/
theorem deLaValleePoussin_nonreal_zero_repulsion
    (H : ZetaLogDerivDiscBound) :
    ∃ c > 0, ∀ {β t : ℝ}, β ≤ 1 → t ≠ 0 →
      riemannZeta (β + Complex.I * t : ℂ) = 0 →
      c ≤ (1 - β) * Real.log (|t| + 2) := by
  rcases deLaValleePoussin_neg_logDeriv_real_le_pole_add_const with
    ⟨A, hA, hApole⟩
  let l : ℝ := Real.log 2
  let B : ℝ := 3 * A / l + 6 * H.C + 1
  let delta : ℝ := min (l / 2) (1 / (10 * B))
  have hl : 0 < l := by
    dsimp [l]
    exact Real.log_pos (by norm_num)
  have hB : 0 < B := by
    dsimp [B]
    have hquot : 0 ≤ 3 * A / l := div_nonneg (by positivity) hl.le
    nlinarith [H.C_nonneg]
  have hδ : 0 < delta := by
    dsimp [delta]
    exact lt_min (div_pos hl (by norm_num)) (one_div_pos.mpr (by positivity))
  refine ⟨delta / 4, div_pos hδ (by norm_num), ?_⟩
  intro β t hβ ht hz
  let logHeight : ℝ := Real.log (|t| + 2)
  let x : ℝ := 1 - β
  let σ : ℝ := 1 + delta / logHeight
  have hL : 0 < logHeight := by
    dsimp [logHeight]
    exact Real.log_pos (by linarith [abs_nonneg t])
  have hlL : l ≤ logHeight := by
    dsimp [l, logHeight]
    exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hδsmall : delta ≤ 1 / (10 * B) := by
    dsimp [delta]
    exact min_le_right _ _
  have hδhalf : delta ≤ l / 2 := by
    dsimp [delta]
    exact min_le_left _ _
  have hσ1 : 1 < σ := by
    dsimp [σ]
    exact lt_add_of_pos_right 1 (div_pos hδ hL)
  have hσ2 : σ ≤ 2 := by
    have hδL : delta ≤ logHeight / 2 := hδhalf.trans (by linarith)
    dsimp [σ]
    have hquot : delta / logHeight ≤ 1 / 2 := by
      apply (div_le_iff₀ hL).2
      simpa [div_eq_mul_inv, mul_comm] using hδL
    linarith
  have hzero := H.zero_contribution_bound hσ1 hσ2 hβ ht hz
  have hzero' :
      (-deriv riemannZeta (σ + Complex.I * t : ℂ) /
          riemannZeta (σ + Complex.I * t : ℂ)).re ≤
        -1 / (delta / logHeight + x) + H.C * logHeight := by
    calc
      _ ≤ -1 / (σ - β) + H.C * Real.log (|t| + 2) := hzero
      _ = -1 / (delta / logHeight + x) + H.C * logHeight := by
        dsimp [σ, x, logHeight]
        congr 2
        ring
  have hpole := hApole σ hσ1 hσ2
  have hpole' :
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤
        logHeight / delta + A := by
    calc
      _ ≤ 1 / (σ - 1) + A := hpole
      _ = logHeight / delta + A := by
        dsimp [σ]
        field_simp [ne_of_gt hL, ne_of_gt hδ]
        ring
  have htwo_ne : 2 * t ≠ 0 := mul_ne_zero (by norm_num) ht
  have hdouble := H.vertical_bound hσ1 hσ2 htwo_ne
  have hlogdouble : Real.log (|2 * t| + 2) ≤ 2 * logHeight := by
    have habs : |2 * t| = 2 * |t| := by rw [abs_mul]; norm_num
    have harg : 2 * |t| + 2 ≤ (|t| + 2) ^ 2 := by
      nlinarith [abs_nonneg t, sq_nonneg (|t| + 1)]
    calc
      Real.log (|2 * t| + 2) = Real.log (2 * |t| + 2) := by rw [habs]
      _ ≤ Real.log ((|t| + 2) ^ 2) :=
        Real.log_le_log (by positivity) harg
      _ = 2 * logHeight := by simp [Real.log_pow, logHeight]
  have hdouble' :
      (-deriv riemannZeta (σ + Complex.I * (2 * t) : ℂ) /
          riemannZeta (σ + Complex.I * (2 * t) : ℂ)).re ≤
        H.C * (2 * logHeight) := by
    calc
      _ ≤ H.C * Real.log (|2 * t| + 2) := by
        simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hdouble
      _ ≤ H.C * (2 * logHeight) :=
        mul_le_mul_of_nonneg_left hlogdouble H.C_nonneg
  have hpos := deLaValleePoussin_logDeriv_three_four_one_nonneg
    (σ := σ) (t := t) hσ1
  have hmain :
      0 ≤ 3 * logHeight / delta + 3 * A -
        4 / (delta / logHeight + x) + 6 * H.C * logHeight := by
    have hmain' :
        0 ≤ 3 * (logHeight / delta + A) +
          4 * (-1 / (delta / logHeight + x) + H.C * logHeight) +
          H.C * (2 * logHeight) := by
      linarith
    convert hmain' using 1 <;> ring
  exact three_four_one_forces_repulsion hA.le H.C_nonneg hl hlL hL hδ hx
    (by simpa [B] using hδsmall) hmain

/--
Z5: the isolated logarithmic-derivative disc estimate is sufficient to
construct the frozen de la Vallée Poussin zero-free-region package.

The nonreal case is `deLaValleePoussin_nonreal_zero_repulsion`.  On the real
axis, continuity and the value `zetaPoleRemoved 1 = 1` give a zero-free
neighborhood of the pole; shrinking the same positive constant absorbs this
compact low-height case.  The closed half-plane `Re s ≥ 1` is Mathlib's
unconditional zeta nonvanishing theorem.
-/
noncomputable def deLaValleePoussinZeroFreeRegion_of_logDerivDiscBound
    (H : ZetaLogDerivDiscBound) :
    DeLaValleePoussinZeroFreeRegion := by
  let hrepExists := deLaValleePoussin_nonreal_zero_repulsion H
  let c₀ : ℝ := Classical.choose hrepExists
  have hc₀ : 0 < c₀ := (Classical.choose_spec hrepExists).1
  have hrepel :
      ∀ {β t : ℝ}, β ≤ 1 → t ≠ 0 →
        riemannZeta (β + Complex.I * t : ℂ) = 0 →
        c₀ ≤ (1 - β) * Real.log (|t| + 2) :=
    (Classical.choose_spec hrepExists).2
  have hG_eventually :
      ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), zetaPoleRemoved z ≠ 0 :=
    (zetaPoleRemoved_analyticAt (1 : ℂ)).continuousAt.eventually_ne (by simp)
  let hlocalExists := Metric.eventually_nhds_iff.mp hG_eventually
  let ε : ℝ := Classical.choose hlocalExists
  have hε : 0 < ε := (Classical.choose_spec hlocalExists).1
  have hG_ne :
      ∀ ⦃z : ℂ⦄, dist z (1 : ℂ) < ε → zetaPoleRemoved z ≠ 0 :=
    (Classical.choose_spec hlocalExists).2
  let l : ℝ := Real.log 2
  let c : ℝ := min c₀ (ε * l / 2)
  have hl : 0 < l := by
    dsimp [l]
    exact Real.log_pos (by norm_num)
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min hc₀ (div_pos (mul_pos hε hl) (by norm_num))
  refine
    { c := c
      c_pos := hc
      zeta_ne_zero := ?_ }
  intro s hs
  by_cases hre : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hre
  have hre_lt : s.re < 1 := lt_of_not_ge hre
  by_cases him : s.im = 0
  · have hs_real : s = (s.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa [him]
    have hregion : 1 - c / l < s.re := by
      simpa [deLaValleePoussinRegion, him, l] using hs
    have hgap : 1 - s.re < c / l := by linarith
    have hcε : c ≤ ε * l / 2 := by
      dsimp [c]
      exact min_le_right _ _
    have hcdiv : c / l ≤ ε / 2 := by
      apply (div_le_iff₀ hl).2
      calc
        c ≤ ε * l / 2 := hcε
        _ = (ε / 2) * l := by ring
    have hdist : dist s (1 : ℂ) < ε := by
      rw [hs_real]
      have hreal : dist s.re (1 : ℝ) = 1 - s.re := by
        rw [Real.dist_eq, abs_of_nonpos (by linarith)]
        ring
      have hsmall : 1 - s.re < ε := by linarith [hε]
      have hcoe : dist (s.re : ℂ) (1 : ℂ) = dist s.re (1 : ℝ) := by
        rw [dist_eq_norm, dist_eq_norm]
        calc
          ‖(s.re : ℂ) - 1‖ = ‖((s.re - 1 : ℝ) : ℂ)‖ := by
            rw [Complex.ofReal_sub, Complex.ofReal_one]
          _ = ‖s.re - 1‖ := Complex.norm_real _
      rw [hcoe, hreal]
      exact hsmall
    have hG := hG_ne hdist
    intro hz
    have hs_ne : s ≠ 1 := by
      intro h
      have : s.re = 1 := by simpa [h]
      linarith
    rw [zetaPoleRemoved_of_ne_one hs_ne] at hG
    exact hG (by rw [hz]; simp)
  · intro hz
    have hs_cart : s = (s.re + Complex.I * s.im : ℂ) := by
      apply Complex.ext <;> simp
    rw [hs_cart] at hz
    have hrep := hrepel hre_lt.le him hz
    have hL : 0 < Real.log (|s.im| + 2) := log_abs_im_add_two_pos s
    have hregion :
        1 - c / Real.log (|s.im| + 2) < s.re := by
      simpa [deLaValleePoussinRegion] using hs
    have hgap :
        (1 - s.re) * Real.log (|s.im| + 2) < c := by
      apply (lt_div_iff₀ hL).mp
      linarith
    have hc₀c : c ≤ c₀ := by
      dsimp [c]
      exact min_le_left _ _
    linarith

end ZetaLogDerivativeDiscBound

end RH.Criteria.NymanBeurling.MobiusSummatory
