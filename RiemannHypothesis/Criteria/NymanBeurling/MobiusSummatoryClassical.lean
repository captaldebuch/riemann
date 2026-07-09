import RiemannHypothesis.Criteria.NymanBeurling.MobiusSummatory
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace RH.Criteria.NymanBeurling.MobiusSummatory

open Filter Finset Topology
open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open scoped BigOperators

-- ---------------------------------------------------------------------------
-- H14M-A. de la Vallée Poussin zero-free-region API
-- ---------------------------------------------------------------------------

/--
The normalized de la Vallée Poussin zero-free strip used for the future
quantitative Mertens bound.

The `+ 2` keeps the logarithmic denominator positive uniformly, including on
the real axis.  The point `s = 1` needs no separate exclusion in this project
because Mathlib's `riemannZeta` is total and has a nonzero junk value there.
-/
noncomputable def deLaValleePoussinRegion (c : ℝ) (s : ℂ) : Prop :=
  1 - c / Real.log (|s.im| + 2) < s.re

lemma log_abs_im_add_two_pos (s : ℂ) :
    0 < Real.log (|s.im| + 2) := by
  exact Real.log_pos (by linarith [abs_nonneg s.im])

lemma deLaValleePoussinRegion_of_one_le_re {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : 1 ≤ s.re) :
    deLaValleePoussinRegion c s := by
  unfold deLaValleePoussinRegion
  have hden : 0 < Real.log (|s.im| + 2) := log_abs_im_add_two_pos s
  have hquot : 0 < c / Real.log (|s.im| + 2) := div_pos hc hden
  linarith

/--
H14M-A frozen statement of the classical de la Vallée Poussin zero-free
region needed by the later effective Perron/contour-shift development.

This is intentionally only an API package: constructing it is the substantive
future analytic-number-theory work.  The constant is existential rather than
numeric, since the downstream `mertens_bound` only needs some positive
zero-free-region width.
-/
structure DeLaValleePoussinZeroFreeRegion where
  c : ℝ
  c_pos : 0 < c
  zeta_ne_zero :
    ∀ s : ℂ, deLaValleePoussinRegion c s → riemannZeta s ≠ 0

/--
The frozen package extends Mathlib's already-formalized closed half-plane
nonvanishing into the logarithmically thin region to the left of `Re s = 1`.
-/
lemma DeLaValleePoussinZeroFreeRegion.ne_zero_of_one_le_re
    (H : DeLaValleePoussinZeroFreeRegion) {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  H.zeta_ne_zero s (deLaValleePoussinRegion_of_one_le_re H.c_pos hs)

-- ---------------------------------------------------------------------------
-- H14M-B0. Elementary 3-4-1 trigonometric ingredient
-- ---------------------------------------------------------------------------

/--
The elementary trigonometric inequality underlying the classical
de la Vallée Poussin `3-4-1` positivity trick.

This is only the real-variable algebraic ingredient.  The analytic use in the
zero-free-region proof still requires the von Mangoldt logarithmic-derivative
identity, pole control at `s = 1`, and uniform vertical growth estimates.
-/
lemma deLaValleePoussin_three_four_one_trig_nonneg (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]
  nlinarith [sq_nonneg (Real.cos θ + 1)]

-- ---------------------------------------------------------------------------
-- H14M-B1. Public 3-4-1 positivity package
-- ---------------------------------------------------------------------------

section ThreeFourOnePositivity

open Complex

/--
Complex unit-circle form of the de la Vallée Poussin `3-4-1` positivity
identity.

For `‖z‖ = 1`, the left side is `2 * (z.re + 1)^2`.  This is the algebraic
core behind the nonnegative Euler-factor/logarithmic combinations used in the
classical zero-free-region argument.
-/
lemma deLaValleePoussin_three_four_one_unit_re_nonneg {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have hnormSq : z.re * z.re + z.im * z.im = 1 := by
    have hsq : ‖z‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [hz]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hsq
    norm_num at hsq
    simpa [sq] using hsq
  have hre : (z ^ 2).re = z.re * z.re - z.im * z.im := by
    simp [pow_two, Complex.mul_re]
  rw [hre]
  nlinarith [sq_nonneg (z.re + 1)]

/--
Reusable logarithmic Euler-factor positivity lemma.

This is the public project-facing analogue of Mathlib's private
`re_log_comb_nonneg'` lemma in `Mathlib.NumberTheory.LSeries.Nonvanishing`.
It packages the Taylor-series proof of the `3-4-1` trick for any real
`0 ≤ a < 1` and any unit complex number `z`.
-/
lemma deLaValleePoussin_re_log_comb_nonneg_unit {a : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re +
      (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    have hzpow : ‖z ^ n‖ = 1 := by rw [norm_pow, hz, one_pow]
    have hunit : 0 ≤ 3 + 4 * (z ^ n).re + ((z ^ n) ^ 2).re :=
      deLaValleePoussin_three_four_one_unit_re_nonneg hzpow
    have hpoweq : ((z ^ 2) ^ n).re = ((z ^ n) ^ 2).re := by
      congr 1
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hpoweq]
    nlinarith [mul_nonneg (pow_nonneg ha₀ n) hunit]

end ThreeFourOnePositivity

-- ---------------------------------------------------------------------------
-- H14M-B2. Public von Mangoldt logarithmic-derivative wrappers
-- ---------------------------------------------------------------------------

section VonMangoldtLogDerivative

open Complex
open scoped ArithmeticFunction LSeries.notation

/--
Project-facing wrapper for Mathlib's von Mangoldt logarithmic-derivative
identity.

For `Re s > 1`, the Dirichlet series of the von Mangoldt function is the
negative logarithmic derivative of the Riemann zeta function.  This is the
analytic bridge used by the de la Vallée Poussin `3-4-1` argument.
-/
lemma deLaValleePoussin_vonMangoldt_LSeries_eq_neg_zeta_logDeriv
    {s : ℂ} (hs : 1 < s.re) :
    L ↗Λ s =
      - deriv riemannZeta s / riemannZeta s :=
  ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/--
The same identity in the orientation most often used when substituting
`ζ'/ζ` into the positivity argument.
-/
lemma deLaValleePoussin_neg_zeta_logDeriv_eq_vonMangoldt_LSeries
    {s : ℂ} (hs : 1 < s.re) :
    - deriv riemannZeta s / riemannZeta s =
      L ↗Λ s :=
  (deLaValleePoussin_vonMangoldt_LSeries_eq_neg_zeta_logDeriv hs).symm

/--
Termwise real-part expansion of the von Mangoldt L-series in the half-plane
`Re s > 1`.

This is the public project hook for the later cosine expansion
`Λ(n) n^{-σ} cos(t log n)`: that last syntactic simplification is separate
`cpow` algebra, while this lemma provides the justified interchange of real
part and infinite sum.
-/
lemma deLaValleePoussin_vonMangoldt_LSeries_re_eq_tsum_term_re
    {s : ℂ} (hs : 1 < s.re) :
    (L ↗Λ s).re =
      ∑' n : ℕ, (LSeries.term ↗Λ s n).re := by
  have hsum :
      HasSum (LSeries.term ↗Λ s) (L ↗Λ s) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).hasSum
  exact (Complex.hasSum_re hsum).tsum_eq.symm

/--
Real-part form of the logarithmic-derivative identity, with the von Mangoldt
series expanded termwise.
-/
lemma deLaValleePoussin_neg_zeta_logDeriv_re_eq_tsum_term_re
    {s : ℂ} (hs : 1 < s.re) :
    (- deriv riemannZeta s / riemannZeta s).re =
      ∑' n : ℕ, (LSeries.term ↗Λ s n).re := by
  rw [deLaValleePoussin_neg_zeta_logDeriv_eq_vonMangoldt_LSeries hs,
    deLaValleePoussin_vonMangoldt_LSeries_re_eq_tsum_term_re hs]

/--
Real part of a negative complex power with positive real base.

This is the elementary `cpow` algebra behind the cosine form of the
von Mangoldt Dirichlet series.
-/
lemma deLaValleePoussin_real_cpow_neg_re {x σ t : ℝ} (hx : 0 < x) :
    (((x : ℂ) ^ (-(σ + Complex.I * t : ℂ))).re) =
      x ^ (-σ) * Real.cos (t * Real.log x) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) :=
    (Complex.ofReal_log hx.le).symm
  rw [hlog]
  simp [Complex.exp_re, Real.cos_neg, mul_comm]
  rw [Real.rpow_def_of_pos hx]
  ring

/--
Term-level cosine form of the von Mangoldt L-series at `s = σ + it`.
-/
lemma deLaValleePoussin_vonMangoldt_term_re_eq_cos
    {σ t : ℝ} {n : ℕ} (hn : n ≠ 0) :
    (LSeries.term ↗Λ (σ + Complex.I * t : ℂ) n).re =
      Λ n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
  rw [← Complex.ofReal_natCast n]
  change ((((Λ n : ℂ) * (((n : ℝ) : ℂ) ^ (-(σ + Complex.I * t : ℂ)))).re) =
    Λ n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n))
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpow := deLaValleePoussin_real_cpow_neg_re
    (x := (n : ℝ)) (σ := σ) (t := t) hnpos
  calc
    (((Λ n : ℂ) * (((n : ℝ) : ℂ) ^ (-(σ + Complex.I * t : ℂ)))).re)
        = Λ n * ((((n : ℝ) : ℂ) ^ (-(σ + Complex.I * t : ℂ))).re) := by
          simp [Complex.mul_re]
    _ = Λ n * ((n : ℝ) ^ (-σ) * Real.cos (t * Real.log n)) := by
          rw [hpow]
    _ = Λ n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by ring

/--
Cosine expansion of the real part of `-ζ'/ζ(σ + it)` for `σ > 1`.
-/
lemma deLaValleePoussin_neg_zeta_logDeriv_re_eq_tsum_cos
    {σ t : ℝ} (hσ : 1 < σ) :
    (- deriv riemannZeta (σ + Complex.I * t : ℂ) /
        riemannZeta (σ + Complex.I * t : ℂ)).re =
      ∑' n : ℕ,
        if _ : n = 0 then 0
        else Λ n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  have hs : 1 < (σ + Complex.I * t : ℂ).re := by simpa using hσ
  rw [deLaValleePoussin_neg_zeta_logDeriv_re_eq_tsum_term_re hs]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn, LSeries.term]
  · simpa [hn] using
      deLaValleePoussin_vonMangoldt_term_re_eq_cos (σ := σ) (t := t) hn

end VonMangoldtLogDerivative

-- ---------------------------------------------------------------------------
-- H14M-B3. Local zeta pole and hypothetical-zero contribution wrappers
-- ---------------------------------------------------------------------------

section ZetaLocalContributions

open Filter

/--
Project-facing residue statement for the simple pole of `ζ` at `s = 1`.

This is the local pole input available in Mathlib.  Turning it into the full
quantitative `ζ'/ζ` pole contribution used in a de la Vallée Poussin contour
argument still needs additional Laurent/log-derivative control.
-/
lemma deLaValleePoussin_zeta_residue_one :
    Tendsto (fun s : ℂ => (s - 1) * riemannZeta s)
      (nhdsWithin 1 ({1}ᶜ : Set ℂ)) (nhds 1) :=
  riemannZeta_residue_one

/--
The regular part `ζ(s) - 1/(s-1)` is locally bounded at `s = 1`.

This is a useful pole-neighborhood estimate already formalized in Mathlib.
It is not by itself the full logarithmic-derivative pole estimate.
-/
lemma deLaValleePoussin_zeta_regular_part_isBigO_one :
    Asymptotics.IsBigO (nhds (1 : ℂ))
      (fun s : ℂ => riemannZeta s - 1 / (s - 1))
      (fun _ : ℂ => (1 : ℂ)) :=
  isBigO_riemannZeta_sub_one_div

/--
Hypothetical simple-zero contribution to the logarithmic derivative of `ζ`.

If `ρ ≠ 1` is a simple zero of `ζ`, then the logarithmic residue of `ζ'/ζ`
at `ρ` is `1`.  This is the clean local contribution theorem currently
available from Mathlib's generic analytic simple-zero API.

The zero-free-region proof ultimately needs an arbitrary-multiplicity and
quantitative version; that stronger statement is deliberately not claimed here.
-/
lemma deLaValleePoussin_zeta_simple_zero_logDeriv_residue
    {ρ : ℂ} (hρ : ρ ≠ 1) (hz : riemannZeta ρ = 0)
    (hsimple : deriv riemannZeta ρ ≠ 0) :
    Tendsto (fun s : ℂ => (s - ρ) * logDeriv riemannZeta s)
      (nhdsWithin ρ ({ρ}ᶜ : Set ℂ)) (nhds 1) := by
  have han : AnalyticAt ℂ riemannZeta ρ := by
    exact analyticOn_riemannZeta ρ (by simpa [Set.mem_compl_iff] using hρ)
  exact han.tendsto_mul_logDeriv_simple_zero hz hsimple

end ZetaLocalContributions

lemma log_tail_term_le_telescoping (k : ℕ) :
    1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2) ≤
      6 * (1 / Real.log (k + 2 : ℝ) - 1 / Real.log (k + 3 : ℝ)) := by
  have hk2 : (1 : ℝ) < (k : ℝ) + 2 := by norm_cast; omega
  have hlog2 : 0 < Real.log (k + 2 : ℝ) := Real.log_pos hk2
  have hlog3 : 0 < Real.log (k + 3 : ℝ) := Real.log_pos (by norm_cast; omega)
  have hratio : 0 < ((k + 3 : ℕ) : ℝ) / (k + 2 : ℝ) := by positivity
  have hdelta :
      1 / ((k + 3 : ℕ) : ℝ) ≤
        Real.log (k + 3 : ℝ) - Real.log (k + 2 : ℝ) := by
    calc
      1 / ((k + 3 : ℕ) : ℝ) =
          1 - ((((k + 3 : ℕ) : ℝ) / (k + 2 : ℝ))⁻¹) := by
            field_simp
            norm_num [Nat.cast_add]
      _ ≤ Real.log (((k + 3 : ℕ) : ℝ) / (k + 2 : ℝ)) :=
        Real.one_sub_inv_le_log_of_pos hratio
      _ = _ := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using
          (Real.log_div
            (x := ((k + 3 : ℕ) : ℝ)) (y := ((k + 2 : ℕ) : ℝ))
            (by positivity) (by positivity))
  have hlog3_le : Real.log (k + 3 : ℝ) ≤ 2 * Real.log (k + 2 : ℝ) := by
    have hnat : ((k + 3 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) ^ 2 := by
      norm_num
      nlinarith [sq_nonneg (k : ℝ)]
    have hlog := Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < (k + 3 : ℕ) by positivity)
      (show (0 : ℝ) < ((k + 2 : ℕ) : ℝ) ^ 2 by positivity) hnat
    rw [Real.log_pow] at hlog
    norm_num at hlog
    simpa using hlog
  have hk3_le : ((k + 3 : ℕ) : ℝ) ≤ 3 * ((k + 1 : ℕ) : ℝ) := by
    norm_num
    linarith
  rw [show 1 / Real.log (k + 2 : ℝ) - 1 / Real.log (k + 3 : ℝ) =
      (Real.log (k + 3 : ℝ) - Real.log (k + 2 : ℝ)) /
        (Real.log (k + 2 : ℝ) * Real.log (k + 3 : ℝ)) by
          field_simp]
  calc
    1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2)
        ≤ 3 / (((k + 3 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          have hmul := mul_le_mul_of_nonneg_right hk3_le
            (sq_nonneg (Real.log (k + 2 : ℝ)))
          nlinarith
    _ ≤ 6 / (((k + 3 : ℕ) : ℝ) *
          (Real.log (k + 2 : ℝ) * Real.log (k + 3 : ℝ))) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          have hmul := mul_le_mul_of_nonneg_left hlog3_le
            (mul_nonneg (by positivity) hlog2.le)
          nlinarith
    _ ≤ 6 * ((Real.log (k + 3 : ℝ) - Real.log (k + 2 : ℝ)) /
          (Real.log (k + 2 : ℝ) * Real.log (k + 3 : ℝ))) := by
          calc
            _ = 6 * (1 / ((k + 3 : ℕ) : ℝ)) /
                (Real.log (k + 2 : ℝ) * Real.log (k + 3 : ℝ)) := by
                  field_simp
            _ ≤ 6 * (Real.log (k + 3 : ℝ) - Real.log (k + 2 : ℝ)) /
                (Real.log (k + 2 : ℝ) * Real.log (k + 3 : ℝ)) := by
                  gcongr
            _ = _ := by ring
    _ = _ := by ring

lemma sum_Icc_sub_succ (a : ℕ → ℝ) (m n : ℕ) (hmn : m ≤ n) :
    (∑ k ∈ Finset.Icc m n, (a k - a (k + 1))) = a m - a (n + 1) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      ring

lemma finite_log_tail_bound (N R : ℕ) :
    (∑ k ∈ Finset.Icc (N + 1) R,
      1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2)) ≤
        6 / Real.log (N + 2 : ℝ) := by
  by_cases hNR : N + 1 ≤ R
  · calc
      _ ≤ ∑ k ∈ Finset.Icc (N + 1) R,
          6 * (1 / Real.log (k + 2 : ℝ) - 1 / Real.log (k + 3 : ℝ)) := by
            apply Finset.sum_le_sum
            intro k _
            exact log_tail_term_le_telescoping k
      _ = 6 * (1 / Real.log (N + 3 : ℝ) - 1 / Real.log (R + 3 : ℝ)) := by
            rw [← Finset.mul_sum]
            have htel := sum_Icc_sub_succ (fun k => 1 / Real.log (k + 2 : ℝ))
              (N + 1) R hNR
            congr 1
            convert htel using 1 <;> norm_num [Nat.cast_add] <;> ring
      _ ≤ 6 / Real.log (N + 3 : ℝ) := by
            have hlog : 0 < Real.log (R + 3 : ℝ) := Real.log_pos (by norm_cast; omega)
            have hnonneg : 0 ≤ 1 / Real.log (R + 3 : ℝ) := by positivity
            calc
              6 * (1 / Real.log (N + 3 : ℝ) - 1 / Real.log (R + 3 : ℝ)) ≤
                  6 * (1 / Real.log (N + 3 : ℝ)) := by nlinarith
              _ = _ := by ring
      _ ≤ 6 / Real.log (N + 2 : ℝ) := by
            have hlogN2 : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
            have hN2pos : (0 : ℝ) < (N : ℝ) + 2 := by positivity
            have hN3pos : (0 : ℝ) < (N : ℝ) + 3 := by positivity
            have hmono : Real.log (N + 2 : ℝ) ≤ Real.log (N + 3 : ℝ) := by
              exact Real.strictMonoOn_log.monotoneOn hN2pos hN3pos (by norm_num)
            simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left
              (one_div_le_one_div_of_le hlogN2 hmono) (show (0 : ℝ) ≤ 6 by norm_num)
  · simp [Finset.Icc_eq_empty (by omega)]
    exact div_nonneg (by norm_num) (Real.log_pos (by norm_cast; omega)).le

lemma finite_log_cubed_tail_bound (N R : ℕ) :
    (∑ k ∈ Finset.Icc (N + 1) R,
      1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 3)) ≤
        12 / Real.log (N + 2 : ℝ) := by
  calc
    _ ≤ ∑ k ∈ Finset.Icc (N + 1) R,
        2 * (1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2)) := by
          apply Finset.sum_le_sum
          intro k _
          have hlog : (1 / 2 : ℝ) ≤ Real.log (k + 2 : ℝ) := by
            have hbase := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
            have hk2pos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
            have hmono : Real.log (2 : ℝ) ≤ Real.log (k + 2 : ℝ) := by
              exact Real.strictMonoOn_log.monotoneOn (by norm_num) hk2pos (by norm_num)
            norm_num at hbase
            linarith
          have hlogpos : 0 < Real.log (k + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
          field_simp
          nlinarith
    _ = 2 * (∑ k ∈ Finset.Icc (N + 1) R,
        1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2)) := by
          rw [Finset.mul_sum]
    _ ≤ 2 * (6 / Real.log (N + 2 : ℝ)) := by
          gcongr
          exact finite_log_tail_bound N R
    _ = _ := by ring

noncomputable def mobiusOverKPartial (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k : ℝ)

noncomputable def mobiusLogOverKPartial (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius k : ℤ) : ℝ) * Real.log (k : ℝ) / (k : ℝ)

/--
Quantitative and boundary-value inputs for the linear Mobius/Dirichlet bridge.
This isolates the still-unformalized classical analytic number theory from the
mechanical Abel-summation consequences used by Phase 14.
-/
structure ClassicalMertensAPI where
  C_M : ℝ
  C_L : ℝ
  C_M_pos : 0 < C_M
  C_L_pos : 0 < C_L
  mertens_bound :
    ∀ N : ℕ,
      |mobiusSummatory N| ≤ C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 3
  mobiusLogSummatory_bound :
    ∀ N : ℕ,
      |mobiusLogSummatory N| ≤ C_L * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2
  mobius_sum_zero : Tendsto mobiusOverKPartial atTop (𝓝 0)
  mobiusLog_sum_neg_one : Tendsto mobiusLogOverKPartial atTop (𝓝 (-1))

/--
Single classical de la Vallée Poussin decay input for the Mertens summatory
function.

This is the intended final quantitative H14 debt: proving this structure from
the zero-free region/effective Perron contour argument is classical analytic
number theory.  The remaining wrappers below convert it into the polynomial-log
Mertens bound used by the finite Abel estimates.
-/
structure ClassicalMertensDecay where
  C : ℝ
  a : ℝ
  C_pos : 0 < C
  a_pos : 0 < a
  mertens_decay :
    ∀ N : ℕ, 2 ≤ N →
      |mobiusSummatory N| ≤ C * (N : ℝ) * Real.exp (-a * Real.sqrt (Real.log N))

/--
Residual non-Mertens inputs needed to assemble the existing
`ClassicalMertensAPI`.

The logarithmic summatory estimate is classically a separate Abel consequence
of sufficiently strong Mertens decay, but formalizing that derivation is not
part of this wrapper.  The two boundary values are Tauberian/residue inputs
(`1 / ζ(1) = 0` and the `ζ'/ζ` residue) rather than mere decay estimates.
-/
structure ClassicalMertensResidualInputs where
  C_L : ℝ
  C_L_pos : 0 < C_L
  mobiusLogSummatory_bound :
    ∀ N : ℕ,
      |mobiusLogSummatory N| ≤ C_L * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2
  mobius_sum_zero : Tendsto mobiusOverKPartial atTop (𝓝 0)
  mobiusLog_sum_neg_one : Tendsto mobiusLogOverKPartial atTop (𝓝 (-1))

lemma tendsto_rpow_mul_exp_neg_mul_sqrt_atTop_nhds_zero
    (A a : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => t ^ A * Real.exp (-a * Real.sqrt t)) atTop (𝓝 0) := by
  have hbase :
      Tendsto (fun x : ℝ => x ^ (2 * A) * Real.exp (-a * x)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * A) a ha
  refine (hbase.comp Real.tendsto_sqrt_atTop).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hsqrt : t ^ A = Real.sqrt t ^ (2 * A) := by
    rw [← Real.rpow_div_two_eq_sqrt (2 * A) ht]
    congr 1
    ring
  simp [hsqrt]

/--
Exponential decay in `√t` dominates every real power of `t`, uniformly on
`[1, ∞)`.

This is the calculus conversion used to turn the classical de la Vallée
Poussin decay `exp (-a √log N)` into any desired power of `1 / log N`.
-/
lemma exists_pos_bound_rpow_mul_exp_neg_mul_sqrt
    (A a : ℝ) (ha : 0 < a) :
    ∃ C_A : ℝ, 0 < C_A ∧
      ∀ t : ℝ, 1 ≤ t → t ^ A * Real.exp (-a * Real.sqrt t) ≤ C_A := by
  have hlim := tendsto_rpow_mul_exp_neg_mul_sqrt_atTop_nhds_zero A a ha
  have hsmall :
      ∀ᶠ t : ℝ in atTop, t ^ A * Real.exp (-a * Real.sqrt t) ≤ 1 := by
    have hball : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds _ zero_lt_one
    filter_upwards [hlim hball] with t ht
    have habs : |t ^ A * Real.exp (-a * Real.sqrt t)| < 1 := by
      simpa [Real.dist_eq] using ht
    exact (le_abs_self _).trans habs.le
  rcases eventually_atTop.1 hsmall with ⟨B, hB⟩
  let R : ℝ := max 1 B
  have hcont :
      ContinuousOn (fun t : ℝ => t ^ A * Real.exp (-a * Real.sqrt t))
        (Set.Icc 1 R) := by
    have hpow : ContinuousOn (fun t : ℝ => t ^ A) (Set.Icc 1 R) := by
      refine ContinuousOn.rpow_const continuousOn_id ?_
      intro t ht
      exact Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
    have hexp : ContinuousOn (fun t : ℝ => Real.exp (-a * Real.sqrt t))
        (Set.Icc 1 R) := by
      fun_prop
    exact hpow.mul hexp
  rcases isCompact_Icc.exists_bound_of_continuousOn hcont with ⟨C₀, hC₀⟩
  refine ⟨max C₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right C₀ 1), ?_⟩
  intro t ht
  by_cases htR : t ≤ R
  · have hnorm := hC₀ t ⟨ht, htR⟩
    exact (le_abs_self _).trans <| hnorm.trans (le_max_left C₀ 1)
  · have hRt : R ≤ t := le_of_not_ge htR
    have hBt : B ≤ t := (le_max_right 1 B).trans hRt
    exact (hB t hBt).trans (le_max_right C₀ 1)

/--
Natural-number logarithmic form of
`exists_pos_bound_rpow_mul_exp_neg_mul_sqrt`.
-/
lemma exists_pos_exp_neg_mul_sqrt_log_nat_le_const_div_log_pow
    (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C_A : ℝ, 0 < C_A ∧
      ∀ N : ℕ, 3 ≤ N →
        Real.exp (-a * Real.sqrt (Real.log (N : ℝ))) ≤
          C_A / Real.log (N : ℝ) ^ m := by
  rcases exists_pos_bound_rpow_mul_exp_neg_mul_sqrt (m : ℝ) a ha with
    ⟨C_A, hC_A_pos, hC_A⟩
  refine ⟨C_A, hC_A_pos, ?_⟩
  intro N hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hlog_one : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le hNpos]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hN)
  have hlog_pos : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le zero_lt_one hlog_one
  have hprod := hC_A (Real.log (N : ℝ)) hlog_one
  have hprod_nat :
      Real.log (N : ℝ) ^ m * Real.exp (-a * Real.sqrt (Real.log (N : ℝ))) ≤ C_A := by
    simpa [Real.rpow_natCast] using hprod
  have hpow_pos : 0 < Real.log (N : ℝ) ^ m := pow_pos hlog_pos m
  calc
    Real.exp (-a * Real.sqrt (Real.log (N : ℝ)))
        = (Real.log (N : ℝ) ^ m *
            Real.exp (-a * Real.sqrt (Real.log (N : ℝ)))) /
            Real.log (N : ℝ) ^ m := by
          field_simp [hpow_pos.ne']
    _ ≤ C_A / Real.log (N : ℝ) ^ m := by
          exact div_le_div_of_nonneg_right hprod_nat hpow_pos.le

lemma tendsto_inv_log_nat_add_two :
    Tendsto (fun N : ℕ => 1 / Real.log (N + 2 : ℝ)) atTop (𝓝 0) := by
  have harg : Tendsto (fun N : ℕ => ((N + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  simpa [one_div] using (Real.tendsto_log_atTop.comp harg).inv_tendsto_atTop

lemma cutoffMobiusOverKSum_eq_partial_sub (N : ℕ) :
    cutoffMobiusOverKSum N =
      mobiusOverKPartial N - mobiusSummatory N / ((N + 1 : ℕ) : ℝ) := by
  unfold cutoffMobiusOverKSum mobiusOverKPartial mobiusSummatory
  calc
    _ = ∑ k ∈ Finset.Icc 1 N,
        (((ArithmeticFunction.moebius k : ℤ) : ℝ) / (k : ℝ) -
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) / ((N + 1 : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk0 : (k : ℝ) ≠ 0 := by
            exact_mod_cast (ne_of_gt (Finset.mem_Icc.mp hk).1)
          field_simp
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_div]

lemma cutoffMobiusLogOverKSum_eq_partial_sub (N : ℕ) :
    cutoffMobiusLogOverKSum N =
      mobiusLogOverKPartial N - mobiusLogSummatory N / ((N + 1 : ℕ) : ℝ) := by
  unfold cutoffMobiusLogOverKSum mobiusLogOverKPartial mobiusLogSummatory
  calc
    _ = ∑ k ∈ Finset.Icc 1 N,
        (((ArithmeticFunction.moebius k : ℤ) : ℝ) * Real.log (k : ℝ) / (k : ℝ) -
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) * Real.log (k : ℝ) /
            ((N + 1 : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk0 : (k : ℝ) ≠ 0 := by
            exact_mod_cast (ne_of_gt (Finset.mem_Icc.mp hk).1)
          field_simp
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_div]

lemma sum_Icc_one_sub_sum_Icc_one (f : ℕ → ℝ) (N R : ℕ) (hNR : N ≤ R) :
    (∑ k ∈ Finset.Icc 1 R, f k) - (∑ k ∈ Finset.Icc 1 N, f k) =
      ∑ k ∈ Finset.Icc (N + 1) R, f k := by
  induction R, hNR using Nat.le_induction with
  | base => simp
  | succ R hNR ih =>
      have h1R : 1 ≤ R + 1 := by omega
      have hNR' : N + 1 ≤ R + 1 := by omega
      rw [Finset.sum_Icc_succ_top h1R, Finset.sum_Icc_succ_top hNR']
      calc
        _ = ((∑ k ∈ Finset.Icc 1 R, f k) - (∑ k ∈ Finset.Icc 1 N, f k)) +
            f (R + 1) := by ring
        _ = _ := by rw [ih]

lemma ClassicalMertensAPI.mobius_ratio_tendsto_zero (api : ClassicalMertensAPI) :
    Tendsto (fun N : ℕ => mobiusSummatory N / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hmajorant :
      Tendsto (fun N : ℕ => api.C_M * (1 / Real.log (N + 2 : ℝ)) ^ 3) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_inv_log_nat_add_two.pow 3))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N : ℕ => abs_nonneg _)
    (Eventually.of_forall fun N : ℕ => ?_) hmajorant
  calc
    |mobiusSummatory N / ((N + 1 : ℕ) : ℝ)| =
        |mobiusSummatory N| / ((N + 1 : ℕ) : ℝ) := by
          rw [abs_div]
          congr 1
          exact abs_of_pos (by exact_mod_cast Nat.succ_pos N)
    _ ≤ (api.C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 3) /
          ((N + 1 : ℕ) : ℝ) := by
            gcongr
            exact api.mertens_bound N
    _ ≤ api.C_M * (1 / Real.log (N + 2 : ℝ)) ^ 3 := by
          have hlog : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
          have hN : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by norm_cast; omega
          field_simp
          nlinarith [api.C_M_pos]

lemma ClassicalMertensAPI.mobiusLog_ratio_tendsto_zero (api : ClassicalMertensAPI) :
    Tendsto (fun N : ℕ => mobiusLogSummatory N / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hmajorant :
      Tendsto (fun N : ℕ => api.C_L * (1 / Real.log (N + 2 : ℝ)) ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_inv_log_nat_add_two.pow 2))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N : ℕ => abs_nonneg _)
    (Eventually.of_forall fun N : ℕ => ?_) hmajorant
  calc
    |mobiusLogSummatory N / ((N + 1 : ℕ) : ℝ)| =
        |mobiusLogSummatory N| / ((N + 1 : ℕ) : ℝ) := by
          rw [abs_div]
          congr 1
          exact abs_of_pos (by exact_mod_cast Nat.succ_pos N)
    _ ≤ (api.C_L * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2) /
          ((N + 1 : ℕ) : ℝ) := by
            gcongr
            exact api.mobiusLogSummatory_bound N
    _ ≤ api.C_L * (1 / Real.log (N + 2 : ℝ)) ^ 2 := by
          have hlog : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
          have hN : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by norm_cast; omega
          field_simp
          nlinarith [api.C_L_pos]

lemma ClassicalMertensAPI.cutoff_overK_tendsto_zero (api : ClassicalMertensAPI) :
    Tendsto cutoffMobiusOverKSum atTop (𝓝 0) := by
  have h : Tendsto (fun N =>
      mobiusOverKPartial N - mobiusSummatory N / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa using api.mobius_sum_zero.sub api.mobius_ratio_tendsto_zero
  exact h.congr' (Eventually.of_forall fun N => (cutoffMobiusOverKSum_eq_partial_sub N).symm)

lemma ClassicalMertensAPI.cutoff_log_plus_one_tendsto_zero (api : ClassicalMertensAPI) :
    Tendsto (fun N : ℕ => cutoffMobiusLogOverKSum N + 1) atTop (𝓝 0) := by
  have h : Tendsto (fun N =>
      mobiusLogOverKPartial N - mobiusLogSummatory N / ((N + 1 : ℕ) : ℝ) + 1) atTop (𝓝 0) := by
    simpa [add_assoc] using
      (api.mobiusLog_sum_neg_one.sub api.mobiusLog_ratio_tendsto_zero).add
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  exact h.congr' (Eventually.of_forall fun N => by
    simp [cutoffMobiusLogOverKSum_eq_partial_sub, add_comm])

lemma ClassicalMertensAPI.overK_difference_bound (api : ClassicalMertensAPI)
    (N R : ℕ) (hNR : N ≤ R) :
    |cutoffMobiusOverKSum R - cutoffMobiusOverKSum N| ≤
      12 * api.C_M / Real.log (N + 2 : ℝ) := by
  rw [cutoffMobiusOverKSum_eq_abel_sum, cutoffMobiusOverKSum_eq_abel_sum,
    sum_Icc_one_sub_sum_Icc_one _ N R hNR]
  calc
    |∑ k ∈ Finset.Icc (N + 1) R,
        mobiusSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))|
      ≤ ∑ k ∈ Finset.Icc (N + 1) R,
          |mobiusSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc (N + 1) R,
        api.C_M * (1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 3)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkpos : 0 < k := lt_of_lt_of_le (by omega) (Finset.mem_Icc.mp hk).1
          have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
          have hdiff : 0 ≤ 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
            exact sub_nonneg.mpr (one_div_le_one_div_of_le hkR (by norm_cast; omega))
          rw [abs_mul, abs_of_nonneg hdiff]
          calc
            |mobiusSummatory k| * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))
              ≤ (api.C_M * (k : ℝ) / Real.log (k + 2 : ℝ) ^ 3) *
                  (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
                    exact mul_le_mul_of_nonneg_right (api.mertens_bound k) hdiff
            _ = api.C_M * (1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 3)) := by
                  field_simp
                  norm_num [Nat.cast_add]
    _ = api.C_M * (∑ k ∈ Finset.Icc (N + 1) R,
        1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 3)) := by
          rw [Finset.mul_sum]
    _ ≤ api.C_M * (12 / Real.log (N + 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (finite_log_cubed_tail_bound N R) api.C_M_pos.le
    _ = _ := by ring

lemma ClassicalMertensAPI.logOverK_difference_bound (api : ClassicalMertensAPI)
    (N R : ℕ) (hNR : N ≤ R) :
    |(cutoffMobiusLogOverKSum R + 1) - (cutoffMobiusLogOverKSum N + 1)| ≤
      6 * api.C_L / Real.log (N + 2 : ℝ) := by
  rw [cutoffMobiusLogOverKSum_eq_abel_sum, cutoffMobiusLogOverKSum_eq_abel_sum]
  have hshift :
      (1 + ∑ k ∈ Finset.Icc 1 R,
          mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))) -
        (1 + ∑ k ∈ Finset.Icc 1 N,
          mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))) =
      (∑ k ∈ Finset.Icc 1 R,
          mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))) -
        (∑ k ∈ Finset.Icc 1 N,
          mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))) := by ring
  rw [hshift, sum_Icc_one_sub_sum_Icc_one _ N R hNR]
  calc
    |∑ k ∈ Finset.Icc (N + 1) R,
        mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))|
      ≤ ∑ k ∈ Finset.Icc (N + 1) R,
          |mobiusLogSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc (N + 1) R,
        api.C_L * (1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkpos : 0 < k := lt_of_lt_of_le (by omega) (Finset.mem_Icc.mp hk).1
          have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
          have hdiff : 0 ≤ 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
            exact sub_nonneg.mpr (one_div_le_one_div_of_le hkR (by norm_cast; omega))
          rw [abs_mul, abs_of_nonneg hdiff]
          calc
            |mobiusLogSummatory k| * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))
              ≤ (api.C_L * (k : ℝ) / Real.log (k + 2 : ℝ) ^ 2) *
                  (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
                    exact mul_le_mul_of_nonneg_right (api.mobiusLogSummatory_bound k) hdiff
            _ = api.C_L * (1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2)) := by
                  field_simp
                  norm_num [Nat.cast_add]
    _ = api.C_L * (∑ k ∈ Finset.Icc (N + 1) R,
        1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 2)) := by
          rw [Finset.mul_sum]
    _ ≤ api.C_L * (6 / Real.log (N + 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (finite_log_tail_bound N R) api.C_L_pos.le
    _ = _ := by ring

lemma ClassicalMertensAPI.overK_bound (api : ClassicalMertensAPI) (N : ℕ) :
    |cutoffMobiusOverKSum N| ≤ 12 * api.C_M / Real.log (N + 2 : ℝ) := by
  have htendsto := (api.cutoff_overK_tendsto_zero.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => cutoffMobiusOverKSum N) atTop (𝓝 _))).abs
  have hle : ∀ᶠ R : ℕ in atTop,
      |cutoffMobiusOverKSum R - cutoffMobiusOverKSum N| ≤
        12 * api.C_M / Real.log (N + 2 : ℝ) := by
    filter_upwards [eventually_ge_atTop N] with R hNR
    exact api.overK_difference_bound N R hNR
  have hlimit := le_of_tendsto htendsto hle
  simpa using hlimit

lemma ClassicalMertensAPI.logOverK_bound (api : ClassicalMertensAPI) (N : ℕ) :
    |cutoffMobiusLogOverKSum N + 1| ≤ 6 * api.C_L / Real.log (N + 2 : ℝ) := by
  have htendsto := (api.cutoff_log_plus_one_tendsto_zero.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => cutoffMobiusLogOverKSum N + 1) atTop (𝓝 _))).abs
  have hle : ∀ᶠ R : ℕ in atTop,
      |(cutoffMobiusLogOverKSum R + 1) - (cutoffMobiusLogOverKSum N + 1)| ≤
        6 * api.C_L / Real.log (N + 2 : ℝ) := by
    filter_upwards [eventually_ge_atTop N] with R hNR
    exact api.logOverK_difference_bound N R hNR
  have hlimit := le_of_tendsto htendsto hle
  have hrewrite : |0 - (cutoffMobiusLogOverKSum N + 1)| = |cutoffMobiusLogOverKSum N + 1| := by
    rw [zero_sub, abs_neg]
  rw [← hrewrite]
  exact hlimit

noncomputable def mobius_pnt_style_of_classical_api (api : ClassicalMertensAPI) :
    MobiusPNTStyleEstimates :=
  { C_M := 12 * api.C_M
    C_L := 6 * api.C_L
    C_M_nonneg := mul_nonneg (by norm_num) api.C_M_pos.le
    C_L_pos := mul_pos (by norm_num) api.C_L_pos
    mobius_abel_bound := by
      intro N
      rw [← cutoffMobiusOverKSum_eq_abel_sum]
      exact api.overK_bound N
    mobiusLog_abel_bound := by
      intro N
      rw [← cutoffMobiusLogOverKSum_eq_abel_sum]
      exact api.logOverK_bound N }

noncomputable def linear_mobius_dirichlet_estimates_of_classical_api
    (api : ClassicalMertensAPI) :
    LinearMobiusDirichletEstimates :=
  linear_mobius_dirichlet_estimates_of_pnt_style
    (mobius_pnt_style_of_classical_api api)

end RH.Criteria.NymanBeurling.MobiusSummatory
