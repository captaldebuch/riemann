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

end RH.Criteria.NymanBeurling.MobiusSummatory
