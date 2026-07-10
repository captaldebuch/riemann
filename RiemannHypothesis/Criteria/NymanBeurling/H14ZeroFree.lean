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

end RH.Criteria.NymanBeurling.MobiusSummatory
