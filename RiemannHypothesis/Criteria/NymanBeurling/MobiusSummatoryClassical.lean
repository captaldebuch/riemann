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

/--
Finite Abel summation for a cutoff that vanishes at `N + 1`.

This is the public H14-classical copy of the private finite Abel lemma in
`MobiusSummatory.lean`; it is kept here so the residual-reduction layer can use
the same summation-by-parts shape without changing the earlier file.
-/
theorem finite_abel_sum_Icc_mul_sub_endpoint_eq_sum_partial
    (a b : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, a k * (b k - b (N + 1))) =
      ∑ k ∈ Finset.Icc 1 N,
        (∑ j ∈ Finset.Icc 1 k, a j) * (b k - b (k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hone : 1 ≤ N + 1 := by omega
      rw [Finset.sum_Icc_succ_top hone, Finset.sum_Icc_succ_top hone]
      have hshift :
          (∑ k ∈ Finset.Icc 1 N, a k * (b k - b (N + 1 + 1))) =
            (∑ k ∈ Finset.Icc 1 N, a k * (b k - b (N + 1))) +
              (∑ k ∈ Finset.Icc 1 N, a k) * (b (N + 1) - b (N + 1 + 1)) := by
        calc
          _ = ∑ k ∈ Finset.Icc 1 N,
                (a k * (b k - b (N + 1)) +
                  a k * (b (N + 1) - b (N + 1 + 1))) := by
              apply Finset.sum_congr rfl
              intro k _
              ring
          _ = _ := by
              rw [Finset.sum_add_distrib, Finset.sum_mul]
      rw [hshift, ih, Finset.sum_Icc_succ_top hone]
      ring

/--
Finite Abel summation in endpoint-plus-differences form.
-/
theorem finite_abel_sum_Icc_mul_eq_endpoint_add_sum_partial
    (a b : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, a k * b k) =
      (∑ k ∈ Finset.Icc 1 N, a k) * b (N + 1) +
        ∑ k ∈ Finset.Icc 1 N,
          (∑ j ∈ Finset.Icc 1 k, a j) * (b k - b (k + 1)) := by
  have habel := finite_abel_sum_Icc_mul_sub_endpoint_eq_sum_partial a b N
  calc
    (∑ k ∈ Finset.Icc 1 N, a k * b k)
        = (∑ k ∈ Finset.Icc 1 N, a k * b (N + 1)) +
            ∑ k ∈ Finset.Icc 1 N, a k * (b k - b (N + 1)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = (∑ k ∈ Finset.Icc 1 N, a k) * b (N + 1) +
            ∑ k ∈ Finset.Icc 1 N, a k * (b k - b (N + 1)) := by
          rw [Finset.sum_mul]
    _ = (∑ k ∈ Finset.Icc 1 N, a k) * b (N + 1) +
            ∑ k ∈ Finset.Icc 1 N,
              (∑ j ∈ Finset.Icc 1 k, a j) * (b k - b (k + 1)) := by
          rw [habel]

/--
Exact Abel-summation expansion for the logarithmic Möbius summatory function.
-/
theorem mobiusLogSummatory_eq_abel_endpoint_add_sum (N : ℕ) :
    mobiusLogSummatory N =
      mobiusSummatory N * Real.log (N + 1 : ℝ) +
        ∑ k ∈ Finset.Icc 1 N,
          mobiusSummatory k *
            (Real.log (k : ℝ) - Real.log ((k + 1 : ℕ) : ℝ)) := by
  simpa [mobiusLogSummatory, mobiusSummatory] using
    finite_abel_sum_Icc_mul_eq_endpoint_add_sum_partial
      (fun k ↦ ((ArithmeticFunction.moebius k : ℤ) : ℝ))
      (fun k ↦ Real.log (k : ℝ)) N

lemma abs_mobiusSummatory_le_nat (N : ℕ) :
    |mobiusSummatory N| ≤ (N : ℝ) := by
  unfold mobiusSummatory
  calc
    |∑ k ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius k : ℤ) : ℝ)|
      ≤ ∑ k ∈ Finset.Icc 1 N, |((ArithmeticFunction.moebius k : ℤ) : ℝ)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 N, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k _hk
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
    _ ≤ N := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          have hcard : (Finset.Icc 1 N).card ≤ N := by
            rw [Nat.card_Icc]
            omega
          exact_mod_cast hcard

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

lemma log_nat_add_two_le_two_log_nat {N : ℕ} (hN : 3 ≤ N) :
    Real.log (N + 2 : ℝ) ≤ 2 * Real.log (N : ℝ) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hargpos : 0 < (N + 2 : ℝ) := by positivity
  have hle_sq : (N + 2 : ℝ) ≤ (N : ℝ) ^ 2 := by
    norm_num [sq]
    nlinarith [show (3 : ℝ) ≤ N by exact_mod_cast hN]
  have hlog := Real.log_le_log hargpos hle_sq
  have hlog_sq : Real.log ((N : ℝ) ^ 2) = 2 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  exact hlog.trans_eq hlog_sq

/--
The classical de la Vallée Poussin decay form implies the polynomial-log
Mertens bound used by `ClassicalMertensAPI`.

The proof is deliberately lossy in constants: large `N` uses
`exp (-a √log N) ≪ 1 / log(N)^3`, and the finitely many small values are
absorbed by a harmless absolute constant.
-/
lemma mertens_bound_of_decay (H : ClassicalMertensDecay) :
    ∃ C_M : ℝ, 0 < C_M ∧
      ∀ N : ℕ,
        |mobiusSummatory N| ≤ C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 3 := by
  rcases exists_pos_exp_neg_mul_sqrt_log_nat_le_const_div_log_pow 3 H.a H.a_pos with
    ⟨C₃, hC₃_pos, hC₃⟩
  refine ⟨max (8 * H.C * C₃) 100, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro N
  by_cases hN0 : N = 0
  · subst N
    simp [mobiusSummatory]
  by_cases hNlarge : 3 ≤ N
  · have hN2 : 2 ≤ N := by omega
    have hNpos : 0 ≤ (N : ℝ) := by positivity
    have hlogN_pos : 0 < Real.log (N : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hlogN2_pos : 0 < Real.log (N + 2 : ℝ) := by
      exact Real.log_pos (by norm_cast; omega)
    have hlogN2_nonneg : 0 ≤ Real.log (N + 2 : ℝ) := hlogN2_pos.le
    have hlog_compare := log_nat_add_two_le_two_log_nat hNlarge
    have hcube :
        Real.log (N + 2 : ℝ) ^ 3 ≤ 8 * Real.log (N : ℝ) ^ 3 := by
      have hpow :=
        pow_le_pow_left₀ hlogN2_nonneg hlog_compare 3
      have hrewrite :
          (2 * Real.log (N : ℝ)) ^ 3 = 8 * Real.log (N : ℝ) ^ 3 := by ring
      simpa [hrewrite] using hpow
    have hpowN_pos : 0 < Real.log (N : ℝ) ^ 3 := pow_pos hlogN_pos 3
    have hpowN2_pos : 0 < Real.log (N + 2 : ℝ) ^ 3 := pow_pos hlogN2_pos 3
    have hinv :
        (1 : ℝ) / Real.log (N : ℝ) ^ 3 ≤
          8 / Real.log (N + 2 : ℝ) ^ 3 := by
      rw [div_le_div_iff₀ hpowN_pos hpowN2_pos]
      nlinarith
    have hdecay := H.mertens_decay N hN2
    have hpoly := hC₃ N hNlarge
    have hCN_nonneg : 0 ≤ H.C * (N : ℝ) :=
      mul_nonneg H.C_pos.le hNpos
    have hcoeff_nonneg : 0 ≤ H.C * C₃ * (N : ℝ) :=
      mul_nonneg (mul_nonneg H.C_pos.le hC₃_pos.le) hNpos
    calc
      |mobiusSummatory N|
          ≤ H.C * (N : ℝ) *
              Real.exp (-H.a * Real.sqrt (Real.log (N : ℝ))) := hdecay
      _ ≤ H.C * (N : ℝ) * (C₃ / Real.log (N : ℝ) ^ 3) := by
            exact mul_le_mul_of_nonneg_left hpoly hCN_nonneg
      _ = (H.C * C₃ * (N : ℝ)) * (1 / Real.log (N : ℝ) ^ 3) := by ring
      _ ≤ (H.C * C₃ * (N : ℝ)) * (8 / Real.log (N + 2 : ℝ) ^ 3) := by
            exact mul_le_mul_of_nonneg_left hinv hcoeff_nonneg
      _ = (8 * H.C * C₃) * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 3 := by ring
      _ ≤ max (8 * H.C * C₃) 100 * (N : ℝ) /
            Real.log (N + 2 : ℝ) ^ 3 := by
            gcongr
            exact le_max_left _ _
  · have hNsmall : N ≤ 2 := by omega
    have hNpos_nat : 0 < N := Nat.pos_of_ne_zero hN0
    have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
    have hlog_pos : 0 < Real.log (N + 2 : ℝ) := by
      exact Real.log_pos (by norm_cast; omega)
    have hlog_nonneg : 0 ≤ Real.log (N + 2 : ℝ) := hlog_pos.le
    have hlog_le_four : Real.log (N + 2 : ℝ) ≤ 4 := by
      have hle : (N + 2 : ℝ) ≤ 4 := by exact_mod_cast (by omega : N + 2 ≤ 4)
      exact (Real.log_le_log (by positivity) hle).trans
        (Real.log_le_self (by norm_num : (0 : ℝ) ≤ 4))
    have hlog_cube_le : Real.log (N + 2 : ℝ) ^ 3 ≤ 100 := by
      nlinarith [sq_nonneg (Real.log (N + 2 : ℝ)), hlog_nonneg, hlog_le_four]
    have hpow_pos : 0 < Real.log (N + 2 : ℝ) ^ 3 := pow_pos hlog_pos 3
    have hone_le :
        (1 : ℝ) ≤ max (8 * H.C * C₃) 100 / Real.log (N + 2 : ℝ) ^ 3 := by
      rw [le_div_iff₀ hpow_pos]
      simpa [one_mul] using hlog_cube_le.trans (le_max_right _ _)
    calc
      |mobiusSummatory N| ≤ (N : ℝ) := abs_mobiusSummatory_le_nat N
      _ = 1 * (N : ℝ) := by ring
      _ ≤ (max (8 * H.C * C₃) 100 / Real.log (N + 2 : ℝ) ^ 3) * (N : ℝ) := by
            exact mul_le_mul_of_nonneg_right hone_le hN_nonneg
      _ = max (8 * H.C * C₃) 100 * (N : ℝ) /
            Real.log (N + 2 : ℝ) ^ 3 := by ring

lemma log_nat_succ_sub_log_nat_le_inv (k : ℕ) (hk : 1 ≤ k) :
    Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) ≤ 1 / (k : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hksuccpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  calc
    Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) =
        Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
          rw [Real.log_div hksuccpos.ne' hkpos.ne']
    _ ≤ (((k + 1 : ℕ) : ℝ) / (k : ℝ)) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hksuccpos hkpos)
    _ = 1 / (k : ℝ) := by
      push_cast
      field_simp
      ring

lemma one_le_log_nat_add_two (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ Real.log (k + 2 : ℝ) := by
  have hargpos : (0 : ℝ) < k + 2 := by positivity
  rw [Real.le_log_iff_exp_le hargpos]
  exact Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ k + 2 by omega))

lemma finite_inv_log_cube_head_le (S : ℕ) :
    (∑ k ∈ Finset.Icc 1 S, 1 / Real.log (k + 2 : ℝ) ^ 3) ≤ (S : ℝ) := by
  calc
    (∑ k ∈ Finset.Icc 1 S, 1 / Real.log (k + 2 : ℝ) ^ 3)
        ≤ ∑ _k ∈ Finset.Icc 1 S, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
          have hlog := one_le_log_nat_add_two k hk1
          have hlogpos : 0 < Real.log (k + 2 : ℝ) := zero_lt_one.trans_le hlog
          rw [div_le_one (pow_pos hlogpos 3)]
          nlinarith [sq_nonneg (Real.log (k + 2 : ℝ))]
    _ ≤ S := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          have hcard : (Finset.Icc 1 S).card ≤ S := by
            rw [Nat.card_Icc]
            omega
          exact_mod_cast hcard

lemma finite_inv_log_cube_tail_le (S N : ℕ) :
    (∑ k ∈ Finset.Icc (S + 1) N, 1 / Real.log (k + 2 : ℝ) ^ 3) ≤
      (N : ℝ) / Real.log (S + 2 : ℝ) ^ 3 := by
  have hlogSpos : 0 < Real.log (S + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
  calc
    (∑ k ∈ Finset.Icc (S + 1) N, 1 / Real.log (k + 2 : ℝ) ^ 3)
        ≤ ∑ _k ∈ Finset.Icc (S + 1) N,
            1 / Real.log (S + 2 : ℝ) ^ 3 := by
          apply Finset.sum_le_sum
          intro k hk
          have hSk : S + 1 ≤ k := (Finset.mem_Icc.mp hk).1
          have hlogpos : 0 < Real.log (k + 2 : ℝ) :=
            Real.log_pos (by norm_cast; omega)
          have hlogle : Real.log (S + 2 : ℝ) ≤ Real.log (k + 2 : ℝ) := by
            exact Real.log_le_log (by positivity) (by exact_mod_cast (show S + 2 ≤ k + 2 by omega))
          have hpowle : Real.log (S + 2 : ℝ) ^ 3 ≤ Real.log (k + 2 : ℝ) ^ 3 := by
            gcongr
          exact one_div_le_one_div_of_le (pow_pos hlogSpos 3) hpowle
    _ ≤ N * (1 / Real.log (S + 2 : ℝ) ^ 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
          rw [Nat.card_Icc]
          omega
    _ = (N : ℝ) / Real.log (S + 2 : ℝ) ^ 3 := by ring

lemma log_nat_add_two_le_two_log_sqrt_add_two (N : ℕ) :
    Real.log (N + 2 : ℝ) ≤ 2 * Real.log (Nat.sqrt N + 2 : ℝ) := by
  have hsquare : (N + 2 : ℝ) ≤ (Nat.sqrt N + 2 : ℝ) ^ 2 := by
    have hsqrt := Nat.lt_succ_sqrt' N
    have hsqrtNat : N + 1 ≤ (Nat.sqrt N + 1) ^ 2 := by
      simpa [Nat.succ_eq_add_one] using (Nat.succ_le_iff.mpr hsqrt)
    have hsqrtReal : ((N + 1 : ℕ) : ℝ) ≤ ((Nat.sqrt N + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hsqrtNat
    have hsqrt_nonneg : (0 : ℝ) ≤ Nat.sqrt N := by positivity
    push_cast at hsqrtReal ⊢
    nlinarith
  have hargpos : (0 : ℝ) < N + 2 := by positivity
  calc
    Real.log (N + 2 : ℝ) ≤ Real.log ((Nat.sqrt N + 2 : ℝ) ^ 2) :=
      Real.log_le_log hargpos hsquare
    _ = 2 * Real.log (Nat.sqrt N + 2 : ℝ) := by
      rw [Real.log_pow]
      norm_num

lemma log_nat_add_two_sq_le_sixteen_sqrt (N : ℕ) :
    Real.log (N + 2 : ℝ) ^ 2 ≤ 16 * Real.sqrt (N + 2 : ℝ) := by
  have hx : (0 : ℝ) ≤ N + 2 := by positivity
  have hlog_nonneg : 0 ≤ Real.log (N + 2 : ℝ) :=
    Real.log_nonneg (by norm_cast; omega)
  have hpow_nonneg : 0 ≤ (N + 2 : ℝ) ^ (1 / 4 : ℝ) :=
    (Real.rpow_nonneg hx _)
  have hlog := Real.log_le_rpow_div hx (show (0 : ℝ) < 1 / 4 by norm_num)
  have hpow_sq : ((N + 2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (N + 2 : ℝ) := by
    calc
      ((N + 2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 =
          (N + 2 : ℝ) ^ ((1 / 4 : ℝ) * 2) :=
            (Real.rpow_mul_natCast hx (1 / 4 : ℝ) 2).symm
      _ = Real.sqrt (N + 2 : ℝ) := by
            rw [show (1 / 4 : ℝ) * 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  rw [show (N + 2 : ℝ) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) =
      4 * (N + 2 : ℝ) ^ (1 / 4 : ℝ) by ring] at hlog
  nlinarith

lemma nat_sqrt_le_fortyeight_mul_div_log_sq (N : ℕ) (hN : 1 ≤ N) :
    (Nat.sqrt N : ℝ) ≤ 48 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
  have hlogpos : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
  rw [le_div_iff₀ (pow_pos hlogpos 2)]
  have hsqrtN : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have hsqrtmono : Real.sqrt (N : ℝ) ≤ Real.sqrt (N + 2 : ℝ) := by
    gcongr
    norm_num
  have hsqrt_nonneg : 0 ≤ (Nat.sqrt N : ℝ) := by positivity
  have hlog_sq_nonneg : 0 ≤ Real.log (N + 2 : ℝ) ^ 2 := sq_nonneg _
  have hprod := mul_le_mul (hsqrtN.trans hsqrtmono)
    (log_nat_add_two_sq_le_sixteen_sqrt N) hlog_sq_nonneg (Real.sqrt_nonneg _)
  have hsqrt_sq : Real.sqrt (N + 2 : ℝ) * Real.sqrt (N + 2 : ℝ) = N + 2 := by
    rw [Real.mul_self_sqrt]
    positivity
  have hN2 : (N + 2 : ℝ) ≤ 3 * N := by
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  nlinarith [hprod, hsqrt_sq]

lemma sum_Icc_one_eq_head_add_tail (f : ℕ → ℝ) (S N : ℕ) (hSN : S ≤ N) :
    (∑ k ∈ Finset.Icc 1 N, f k) =
      (∑ k ∈ Finset.Icc 1 S, f k) + ∑ k ∈ Finset.Icc (S + 1) N, f k := by
  have hdiff :
      (∑ k ∈ Finset.Icc 1 N, f k) - (∑ k ∈ Finset.Icc 1 S, f k) =
        ∑ k ∈ Finset.Icc (S + 1) N, f k := by
    induction N, hSN using Nat.le_induction with
    | base => simp
    | succ N hSN ih =>
        have h1N : 1 ≤ N + 1 := by omega
        have hSN' : S + 1 ≤ N + 1 := by omega
        rw [Finset.sum_Icc_succ_top h1N, Finset.sum_Icc_succ_top hSN']
        linarith
  linarith

lemma finite_inv_log_cube_sum_bound (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, 1 / Real.log (k + 2 : ℝ) ^ 3) ≤
      100 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
  by_cases hN0 : N = 0
  · subst N
    simp
  have hN : 1 ≤ N := Nat.pos_of_ne_zero hN0
  let S := Nat.sqrt N
  have hSN : S ≤ N := Nat.sqrt_le_self N
  have hsplit := sum_Icc_one_eq_head_add_tail
    (fun k : ℕ => 1 / Real.log (k + 2 : ℝ) ^ 3) S N hSN
  have hhead := finite_inv_log_cube_head_le S
  have htail := finite_inv_log_cube_tail_le S N
  have hlogNpos : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
  have hlogSpos : 0 < Real.log (S + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
  have hlogcompare : Real.log (N + 2 : ℝ) ≤ 2 * Real.log (S + 2 : ℝ) := by
    simpa [S] using log_nat_add_two_le_two_log_sqrt_add_two N
  have hhead' :
      (∑ k ∈ Finset.Icc 1 S, 1 / Real.log (k + 2 : ℝ) ^ 3) ≤
        48 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 :=
    hhead.trans (by simpa [S] using nat_sqrt_le_fortyeight_mul_div_log_sq N hN)
  have htail' :
      (∑ k ∈ Finset.Icc (S + 1) N, 1 / Real.log (k + 2 : ℝ) ^ 3) ≤
        48 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
    calc
      _ ≤ (N : ℝ) / Real.log (S + 2 : ℝ) ^ 3 := htail
      _ ≤ 48 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
            have hlogN_one : 1 ≤ Real.log (N + 2 : ℝ) := one_le_log_nat_add_two N hN
            rw [div_le_div_iff₀ (pow_pos hlogSpos 3) (pow_pos hlogNpos 2)]
            have hNnonneg : 0 ≤ (N : ℝ) := by positivity
            have hscalar :
                Real.log (N + 2 : ℝ) ^ 2 ≤
                  48 * Real.log (S + 2 : ℝ) ^ 3 := by
              nlinarith [sq_nonneg (Real.log (S + 2 : ℝ)),
                sq_nonneg (Real.log (N + 2 : ℝ))]
            convert mul_le_mul_of_nonneg_left hscalar hNnonneg using 1
            all_goals ring
  have htotal :
      (∑ k ∈ Finset.Icc 1 N, 1 / Real.log (k + 2 : ℝ) ^ 3) =
        (∑ k ∈ Finset.Icc 1 S, 1 / Real.log (k + 2 : ℝ) ^ 3) +
          ∑ k ∈ Finset.Icc (S + 1) N, 1 / Real.log (k + 2 : ℝ) ^ 3 := by
    linarith
  rw [htotal]
  calc
    _ ≤ 48 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 +
          48 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := add_le_add hhead' htail'
    _ = 96 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by ring
    _ ≤ 100 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
      gcongr
      norm_num

/--
The classical Mertens decay also gives the logarithmic Möbius summatory bound
needed by `ClassicalMertensAPI`.

The proof first applies finite Abel summation. The endpoint is controlled by
the existing cubic-log Mertens estimate, while the difference sum is reduced
to `finite_inv_log_cube_sum_bound` using
`log (k + 1) - log k ≤ 1 / k`.
-/
theorem mobiusLogSummatory_bound_of_decay (H : ClassicalMertensDecay) :
    ∃ C_L : ℝ, 0 < C_L ∧
      ∀ N : ℕ,
        |mobiusLogSummatory N| ≤
          C_L * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
  rcases mertens_bound_of_decay H with ⟨C_M, hC_M_pos, hM⟩
  refine ⟨max (101 * C_M) 1,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro N
  by_cases hN0 : N = 0
  · subst N
    simp [mobiusLogSummatory]
  have hN : 1 ≤ N := Nat.pos_of_ne_zero hN0
  have hlogN2pos : 0 < Real.log (N + 2 : ℝ) :=
    Real.log_pos (by norm_cast; omega)
  have hlogN1nonneg : 0 ≤ Real.log (N + 1 : ℝ) :=
    Real.log_nonneg (by norm_cast; omega)
  have hlogN1leN2 : Real.log (N + 1 : ℝ) ≤ Real.log (N + 2 : ℝ) := by
    exact Real.log_le_log (by positivity) (by norm_num)
  have hendpoint :
      |mobiusSummatory N * Real.log (N + 1 : ℝ)| ≤
        C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
    rw [abs_mul, abs_of_nonneg hlogN1nonneg]
    calc
      |mobiusSummatory N| * Real.log (N + 1 : ℝ)
          ≤ (C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 3) *
              Real.log (N + 1 : ℝ) := by
            gcongr
            exact hM N
      _ ≤ (C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 3) *
              Real.log (N + 2 : ℝ) := by
            gcongr
      _ = C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
            field_simp
  have hterm :
      ∀ k ∈ Finset.Icc 1 N,
        |mobiusSummatory k *
            (Real.log (k : ℝ) - Real.log ((k + 1 : ℕ) : ℝ))| ≤
          C_M * (1 / Real.log (k + 2 : ℝ) ^ 3) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
    have hksuccpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hlogmono : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hkpos hksuccpos (by norm_num)
    have hdiff_nonneg :
        0 ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := sub_nonneg.mpr hlogmono
    have hdiff := log_nat_succ_sub_log_nat_le_inv k hk1
    have hlogpos : 0 < Real.log (k + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
    have hupper_nonneg :
        0 ≤ C_M * (k : ℝ) / Real.log (k + 2 : ℝ) ^ 3 := by positivity
    calc
      |mobiusSummatory k *
          (Real.log (k : ℝ) - Real.log ((k + 1 : ℕ) : ℝ))| =
          |mobiusSummatory k| *
            (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) := by
            rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hlogmono)]
            ring
      _ ≤ (C_M * (k : ℝ) / Real.log (k + 2 : ℝ) ^ 3) *
            (1 / (k : ℝ)) := by
            exact mul_le_mul (hM k) hdiff hdiff_nonneg hupper_nonneg
      _ = C_M * (1 / Real.log (k + 2 : ℝ) ^ 3) := by
            field_simp
  have hsum :
      |∑ k ∈ Finset.Icc 1 N,
          mobiusSummatory k *
            (Real.log (k : ℝ) - Real.log ((k + 1 : ℕ) : ℝ))| ≤
        100 * C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
    calc
      |∑ k ∈ Finset.Icc 1 N,
          mobiusSummatory k *
            (Real.log (k : ℝ) - Real.log ((k + 1 : ℕ) : ℝ))| ≤
          ∑ k ∈ Finset.Icc 1 N,
            |mobiusSummatory k *
              (Real.log (k : ℝ) - Real.log ((k + 1 : ℕ) : ℝ))| :=
            abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 N,
            C_M * (1 / Real.log (k + 2 : ℝ) ^ 3) := by
            exact Finset.sum_le_sum hterm
      _ = C_M *
          (∑ k ∈ Finset.Icc 1 N, 1 / Real.log (k + 2 : ℝ) ^ 3) := by
            rw [Finset.mul_sum]
      _ ≤ C_M * (100 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2) := by
            exact mul_le_mul_of_nonneg_left (finite_inv_log_cube_sum_bound N) hC_M_pos.le
      _ = 100 * C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by ring
  rw [mobiusLogSummatory_eq_abel_endpoint_add_sum]
  calc
    |mobiusSummatory N * Real.log (N + 1 : ℝ) +
        ∑ k ∈ Finset.Icc 1 N,
          mobiusSummatory k *
            (Real.log (k : ℝ) - Real.log ((k + 1 : ℕ) : ℝ))| ≤
        |mobiusSummatory N * Real.log (N + 1 : ℝ)| +
          |∑ k ∈ Finset.Icc 1 N,
            mobiusSummatory k *
              (Real.log (k : ℝ) - Real.log ((k + 1 : ℕ) : ℝ))| := abs_add_le _ _
    _ ≤ C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 +
          100 * C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 :=
      add_le_add hendpoint hsum
    _ = 101 * C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by ring
    _ ≤ max (101 * C_M) 1 * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2 := by
      gcongr
      exact le_max_left _ _

/--
Constructor bridge from the single classical Mertens decay hypothesis plus the
remaining non-Mertens residual inputs to the existing Phase 14 API.
-/
noncomputable def ClassicalMertensAPI.ofDecay
    (H : ClassicalMertensDecay) (R : ClassicalMertensResidualInputs) :
    ClassicalMertensAPI :=
  { C_M := Classical.choose (mertens_bound_of_decay H)
    C_L := R.C_L
    C_M_pos := (Classical.choose_spec (mertens_bound_of_decay H)).1
    C_L_pos := R.C_L_pos
    mertens_bound := (Classical.choose_spec (mertens_bound_of_decay H)).2
    mobiusLogSummatory_bound := R.mobiusLogSummatory_bound
    mobius_sum_zero := R.mobius_sum_zero
    mobiusLog_sum_neg_one := R.mobiusLog_sum_neg_one }

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

/--
The Mertens ratio `M(N)/(N+1)` tends to zero under the single de la Vallée
Poussin decay input.
-/
lemma mobius_ratio_tendsto_zero_of_decay (H : ClassicalMertensDecay) :
    Tendsto (fun N : ℕ => mobiusSummatory N / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  rcases mertens_bound_of_decay H with ⟨C_M, hC_M_pos, hM⟩
  have hmajorant :
      Tendsto (fun N : ℕ => C_M * (1 / Real.log (N + 2 : ℝ)) ^ 3) atTop (𝓝 0) := by
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
    _ ≤ (C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 3) /
          ((N + 1 : ℕ) : ℝ) := by
            gcongr
            exact hM N
    _ ≤ C_M * (1 / Real.log (N + 2 : ℝ)) ^ 3 := by
          have hlog : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
          have hN : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by norm_cast; omega
          field_simp
          nlinarith [hC_M_pos]

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

/--
Tail Cauchy bound for the cutoff Abel transform, using only an explicit
polynomial-log Mertens bound.
-/
lemma cutoffMobiusOverKSum_difference_bound_of_mertens_bound
    {C_M : ℝ} (hC_M_nonneg : 0 ≤ C_M)
    (hM : ∀ N : ℕ,
      |mobiusSummatory N| ≤ C_M * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 3)
    (N R : ℕ) (hNR : N ≤ R) :
    |cutoffMobiusOverKSum R - cutoffMobiusOverKSum N| ≤
      12 * C_M / Real.log (N + 2 : ℝ) := by
  rw [cutoffMobiusOverKSum_eq_abel_sum, cutoffMobiusOverKSum_eq_abel_sum,
    sum_Icc_one_sub_sum_Icc_one _ N R hNR]
  calc
    |∑ k ∈ Finset.Icc (N + 1) R,
        mobiusSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))|
      ≤ ∑ k ∈ Finset.Icc (N + 1) R,
          |mobiusSummatory k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc (N + 1) R,
        C_M * (1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 3)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkpos : 0 < k := lt_of_lt_of_le (by omega) (Finset.mem_Icc.mp hk).1
          have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
          have hdiff : 0 ≤ 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
            exact sub_nonneg.mpr (one_div_le_one_div_of_le hkR (by norm_cast; omega))
          rw [abs_mul, abs_of_nonneg hdiff]
          calc
            |mobiusSummatory k| * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))
              ≤ (C_M * (k : ℝ) / Real.log (k + 2 : ℝ) ^ 3) *
                  (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
                    exact mul_le_mul_of_nonneg_right (hM k) hdiff
            _ = C_M * (1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 3)) := by
                  field_simp
                  norm_num [Nat.cast_add]
    _ = C_M * (∑ k ∈ Finset.Icc (N + 1) R,
        1 / (((k + 1 : ℕ) : ℝ) * Real.log (k + 2 : ℝ) ^ 3)) := by
          rw [Finset.mul_sum]
    _ ≤ C_M * (12 / Real.log (N + 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (finite_log_cubed_tail_bound N R) hC_M_nonneg
    _ = _ := by ring

/--
The cutoff Abel transform is Cauchy under the single de la Vallée Poussin decay
input.  This is the convergence half of the classical Axer step; it does not
identify the limiting value.
-/
lemma cutoffMobiusOverKSum_cauchySeq_of_decay (H : ClassicalMertensDecay) :
    CauchySeq cutoffMobiusOverKSum := by
  rcases mertens_bound_of_decay H with ⟨C_M, hC_M_pos, hM⟩
  refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => 12 * C_M / Real.log (N + 2 : ℝ)) ?_ ?_
  · intro n m N hNn hNm
    have hlogN : 0 < Real.log (N + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
    by_cases hnm : n ≤ m
    · have hdiff :=
        cutoffMobiusOverKSum_difference_bound_of_mertens_bound hC_M_pos.le hM n m hnm
      have hlogn : 0 < Real.log (n + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
      have hmono : Real.log (N + 2 : ℝ) ≤ Real.log (n + 2 : ℝ) := by
        exact Real.log_le_log (by positivity) (by norm_cast; omega)
      have htail :
          12 * C_M / Real.log (n + 2 : ℝ) ≤
            12 * C_M / Real.log (N + 2 : ℝ) := by
        have hcoeff : 0 ≤ 12 * C_M := by positivity
        exact mul_le_mul_of_nonneg_left
          (by simpa [one_div] using one_div_le_one_div_of_le hlogN hmono) hcoeff
      calc
        dist (cutoffMobiusOverKSum n) (cutoffMobiusOverKSum m)
            = |cutoffMobiusOverKSum m - cutoffMobiusOverKSum n| := by
              rw [Real.dist_eq, abs_sub_comm]
        _ ≤ 12 * C_M / Real.log (n + 2 : ℝ) := hdiff
        _ ≤ 12 * C_M / Real.log (N + 2 : ℝ) := htail
    · have hmn : m ≤ n := le_of_not_ge hnm
      have hdiff :=
        cutoffMobiusOverKSum_difference_bound_of_mertens_bound hC_M_pos.le hM m n hmn
      have hlogm : 0 < Real.log (m + 2 : ℝ) := Real.log_pos (by norm_cast; omega)
      have hmono : Real.log (N + 2 : ℝ) ≤ Real.log (m + 2 : ℝ) := by
        exact Real.log_le_log (by positivity) (by norm_cast; omega)
      have htail :
          12 * C_M / Real.log (m + 2 : ℝ) ≤
            12 * C_M / Real.log (N + 2 : ℝ) := by
        have hcoeff : 0 ≤ 12 * C_M := by positivity
        exact mul_le_mul_of_nonneg_left
          (by simpa [one_div] using one_div_le_one_div_of_le hlogN hmono) hcoeff
      calc
        dist (cutoffMobiusOverKSum n) (cutoffMobiusOverKSum m)
            = |cutoffMobiusOverKSum n - cutoffMobiusOverKSum m| := by
              rw [Real.dist_eq]
        _ ≤ 12 * C_M / Real.log (m + 2 : ℝ) := hdiff
        _ ≤ 12 * C_M / Real.log (N + 2 : ℝ) := htail
  · simpa [div_eq_mul_inv, mul_assoc] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 12 * C_M) atTop (𝓝 (12 * C_M))).mul
        tendsto_inv_log_nat_add_two)

/--
R2a: under classical de la Vallée Poussin decay, the partial sums
`∑_{k≤N} μ(k)/k` converge to some real limit.

The Axer normalization identifying this limit with `0` is not claimed here.
-/
lemma mobiusOverKPartial_convergent_of_decay (H : ClassicalMertensDecay) :
    ∃ ℓ : ℝ, Tendsto mobiusOverKPartial atTop (𝓝 ℓ) := by
  rcases cauchySeq_tendsto_of_complete (cutoffMobiusOverKSum_cauchySeq_of_decay H) with
    ⟨ℓ, hℓ⟩
  refine ⟨ℓ, ?_⟩
  have hsum := hℓ.add (mobius_ratio_tendsto_zero_of_decay H)
  simpa using hsum.congr' (Eventually.of_forall fun N => by
    rw [cutoffMobiusOverKSum_eq_partial_sub]
    ring)

/--
Residual Axer normalization after the convergence half has been proved from
`ClassicalMertensDecay`.

This is intentionally weaker and more precise than assuming
`mobius_sum_zero` directly: the remaining classical content is only that the
already-existing limit of `∑_{k≤N} μ(k)/k` is the value `0`.
-/
structure MobiusOverKLimitIsZero where
  limit_eq_zero :
    ∀ ℓ : ℝ, Tendsto mobiusOverKPartial atTop (𝓝 ℓ) → ℓ = 0

/--
The old `mobius_sum_zero` field follows from decay plus the remaining Axer
normalization residual.
-/
lemma mobius_sum_zero_of_decay_and_limit_zero
    (H : ClassicalMertensDecay) (Z : MobiusOverKLimitIsZero) :
    Tendsto mobiusOverKPartial atTop (𝓝 0) := by
  rcases mobiusOverKPartial_convergent_of_decay H with ⟨ℓ, hℓ⟩
  simpa [Z.limit_eq_zero ℓ hℓ] using hℓ

/--
Slimmed residual inputs after deriving the Mertens polynomial-log bound and
the convergence half of the `μ(k)/k` boundary value from
`ClassicalMertensDecay`.

Compared with `ClassicalMertensResidualInputs`, the `mobius_sum_zero` field is
replaced by the narrower `mobius_overK_limit_zero` normalization statement.
The logarithmic summatory bound and the logarithmic boundary value remain
separate residuals.
-/
structure ClassicalMertensResidualInputsOfDecay where
  C_L : ℝ
  C_L_pos : 0 < C_L
  mobiusLogSummatory_bound :
    ∀ N : ℕ,
      |mobiusLogSummatory N| ≤ C_L * (N : ℝ) / Real.log (N + 2 : ℝ) ^ 2
  mobius_overK_limit_zero : MobiusOverKLimitIsZero
  mobiusLog_sum_neg_one : Tendsto mobiusLogOverKPartial atTop (𝓝 (-1))

/--
Additive constructor exposing the residual shrinkage achieved by the H14
decay/convergence work.  The original `ClassicalMertensAPI.ofDecay` is left
unchanged.
-/
noncomputable def ClassicalMertensAPI.ofDecay'
    (H : ClassicalMertensDecay) (R : ClassicalMertensResidualInputsOfDecay) :
    ClassicalMertensAPI :=
  { C_M := Classical.choose (mertens_bound_of_decay H)
    C_L := R.C_L
    C_M_pos := (Classical.choose_spec (mertens_bound_of_decay H)).1
    C_L_pos := R.C_L_pos
    mertens_bound := (Classical.choose_spec (mertens_bound_of_decay H)).2
    mobiusLogSummatory_bound := R.mobiusLogSummatory_bound
    mobius_sum_zero :=
      mobius_sum_zero_of_decay_and_limit_zero H R.mobius_overK_limit_zero
    mobiusLog_sum_neg_one := R.mobiusLog_sum_neg_one }

/--
The two boundary normalizations still needed after deriving both quantitative
summatory bounds from `ClassicalMertensDecay`.

The first field records the Axer identification of the already-proved limit of
`mobiusOverKPartial`; the second is the logarithmic boundary normalization.
-/
structure ClassicalMertensBoundaryResidualInputs where
  mobius_overK_limit_zero : MobiusOverKLimitIsZero
  mobiusLog_sum_neg_one : Tendsto mobiusLogOverKPartial atTop (𝓝 (-1))

/--
Assemble `ClassicalMertensAPI` from Mertens decay and only the two remaining
boundary normalizations.

This is additive: the earlier residual structures and constructors remain
available unchanged.
-/
noncomputable def ClassicalMertensAPI.ofDecay''
    (H : ClassicalMertensDecay) (R : ClassicalMertensBoundaryResidualInputs) :
    ClassicalMertensAPI :=
  { C_M := Classical.choose (mertens_bound_of_decay H)
    C_L := Classical.choose (mobiusLogSummatory_bound_of_decay H)
    C_M_pos := (Classical.choose_spec (mertens_bound_of_decay H)).1
    C_L_pos := (Classical.choose_spec (mobiusLogSummatory_bound_of_decay H)).1
    mertens_bound := (Classical.choose_spec (mertens_bound_of_decay H)).2
    mobiusLogSummatory_bound :=
      (Classical.choose_spec (mobiusLogSummatory_bound_of_decay H)).2
    mobius_sum_zero :=
      mobius_sum_zero_of_decay_and_limit_zero H R.mobius_overK_limit_zero
    mobiusLog_sum_neg_one := R.mobiusLog_sum_neg_one }

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
