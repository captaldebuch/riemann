import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPeriodReduction
import RiemannHypothesis.Criteria.NymanBeurling.BBLSPhiOne

/-!
# BBLS §9: the autocorrelation function `A(λ)` and its value at `λ = 1`

Formalizes Proposition 87 of Báez-Duarte–Balazard–Landreau–Saias
(arXiv:math/0306251): `A(1) = ∫₀^∞ {t}²/t² dt = log 2π − γ`, plus the
integrability facts for the autocorrelation integrands on `(0, ∞)` needed by
the `x → ∞` limit of Proposition 22 (Proposition 88).

The evaluation follows the classical route: block integrals
`∫_n^{n+1} (t−n)²/t² dt = 1 − 2n·log((n+1)/n) + n/(n+1)` telescope to
`2N − H_N − 2N log N + 2 log N!`, and Stirling's formula
(`Stirling.tendsto_stirlingSeq_sqrt_pi`) together with the Euler–Mascheroni
limit (`Real.tendsto_eulerMascheroniSeq`) give the constant. All statements
were numerically verified (exact piecewise integration) before formalization.
-/

namespace RH.Criteria.NymanBeurling.VasyuninGram

open Finset Filter Topology MeasureTheory

/-! ## Integrability of the autocorrelation integrands on `(0, ∞)` -/

/-- The product integrand `{t}·{θt}/t²` is integrable on `(0, ∞)`. -/
theorem integrableOn_fract_mul_fract_div_sq {θ : ℝ} (hθ : 0 < θ) :
    IntegrableOn (fun t : ℝ => Int.fract t * Int.fract (θ * t) / t ^ 2)
      (Set.Ioi (0 : ℝ)) := by
  have hfle : ∀ y : ℝ, 0 ≤ y → Int.fract y ≤ y := by
    intro y hy
    have h0 : (0 : ℝ) ≤ (⌊y⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr hy
    linarith [Int.self_sub_fract y]
  have hmeas : Measurable (fun t : ℝ => Int.fract t * Int.fract (θ * t) / t ^ 2) :=
    (measurable_fract.mul (measurable_id.const_mul θ).fract).div
      (measurable_id.pow_const 2)
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) :=
    (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  apply IntegrableOn.union
  · -- bounded by θ on (0, 1]
    have h01 : IntervalIntegrable (fun t : ℝ => Int.fract t * Int.fract (θ * t) / t ^ 2)
        MeasureTheory.volume (0 : ℝ) 1 := by
      refine intervalIntegrable_of_bound_on_Ioc zero_le_one hmeas (C := θ) ?_
      intro u hu
      have hupos : 0 < u := hu.1
      have h1 := hfle u hupos.le
      have h2 := hfle (θ * u) (by positivity)
      have h3 := Int.fract_nonneg (θ * u)
      have h4 := Int.fract_nonneg u
      have hprod : Int.fract u * Int.fract (θ * u) ≤ u * (θ * u) :=
        mul_le_mul h1 h2 h3 hupos.le
      have hle : Int.fract u * Int.fract (θ * u) / u ^ 2 ≤ θ := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < u ^ 2)]
        nlinarith
      have hnn : 0 ≤ Int.fract u * Int.fract (θ * u) / u ^ 2 := by positivity
      rwa [abs_of_nonneg hnn]
    have := intervalIntegrable_iff.mp h01
    rwa [Set.uIoc_of_le zero_le_one] at this
  · -- dominated by t^(-2) on (1, ∞)
    have hmaj : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
    apply Integrable.mono' hmaj
    · exact hmeas.aestronglyMeasurable.restrict
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with t ht
      have ht1 : (1 : ℝ) < t := ht
      have htpos : 0 < t := lt_trans one_pos ht1
      have hf1 : Int.fract t < 1 := Int.fract_lt_one t
      have hf2 : Int.fract (θ * t) < 1 := Int.fract_lt_one (θ * t)
      have hf3 := Int.fract_nonneg t
      have hf4 := Int.fract_nonneg (θ * t)
      have hnn : 0 ≤ Int.fract t * Int.fract (θ * t) / t ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn,
        Real.rpow_neg htpos.le, Real.rpow_two]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < t ^ 2)]
      have hinv : (t ^ 2)⁻¹ * t ^ 2 = 1 := by
        field_simp
      rw [hinv]
      nlinarith

/-- The square integrand `{t}²/t²` is integrable on `(0, ∞)`. -/
theorem integrableOn_fract_sq_div_sq :
    IntegrableOn (fun t : ℝ => (Int.fract t) ^ 2 / t ^ 2) (Set.Ioi (0 : ℝ)) := by
  have h := integrableOn_fract_mul_fract_div_sq (θ := 1) one_pos
  apply h.congr_fun ?_ measurableSet_Ioi
  intro t _
  simp [sq]

/-- Interval integrability of `{t}²/t²` from `0` to any nonnegative endpoint. -/
theorem intervalIntegrable_fract_sq_div_sq {x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable (fun t : ℝ => (Int.fract t) ^ 2 / t ^ 2)
      MeasureTheory.volume (0 : ℝ) x := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
  exact integrableOn_fract_sq_div_sq.mono_set Set.Ioc_subset_Ioi_self

/-! ## Block evaluation of `∫_n^{n+1} {t}²/t² dt` -/

/-- On `[n, n+1]` with `n ≥ 1`, the block integral evaluates in closed form. -/
theorem fract_sq_block {n : ℕ} (hn : 1 ≤ n) :
    (∫ t in (n : ℝ)..((n : ℝ) + 1), (Int.fract t) ^ 2 / t ^ 2) =
      1 - 2 * n * Real.log (((n : ℝ) + 1) / n) + n / ((n : ℝ) + 1) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le one_pos hnR
  -- a.e. congruence to the polynomial-over-t² integrand
  have hcongr : (∫ t in (n : ℝ)..((n : ℝ) + 1), (Int.fract t) ^ 2 / t ^ 2) =
      ∫ t in (n : ℝ)..((n : ℝ) + 1), ((t - n) ^ 2 / t ^ 2) := by
    apply intervalIntegral.integral_congr_ae'
    · filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume ((n : ℝ) + 1)]
        with t ht_ne ht
      have htIoc : t ∈ Set.Ioc (n : ℝ) ((n : ℝ) + 1) := ht
      have hfr : Int.fract t = t - n := by
        have hlt : t < (n : ℝ) + 1 := lt_of_le_of_ne htIoc.2 ht_ne
        have hfloor : ⌊t⌋ = (n : ℤ) := by
          apply Int.floor_eq_iff.mpr
          constructor
          · exact_mod_cast htIoc.1.le
          · exact_mod_cast hlt
        rw [Int.fract, hfloor]
        push_cast
        ring
      rw [hfr]
    · filter_upwards with t ht
      exfalso
      have h1 : ((n : ℝ) + 1) < t := ht.1
      have h2 : t ≤ (n : ℝ) := ht.2
      linarith
  rw [hcongr]
  -- FTC with the explicit antiderivative F(t) = t − 2n log t − n²/t
  have hderiv : ∀ t ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1),
      HasDerivAt (fun t : ℝ => t - 2 * n * Real.log t - (n : ℝ) ^ 2 / t)
        ((t - n) ^ 2 / t ^ 2) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1) := by
      rwa [Set.uIcc_of_le (by linarith)] at ht
    have htpos : 0 < t := lt_of_lt_of_le hnpos htIcc.1
    have h1 : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
    have h2 : HasDerivAt (fun t : ℝ => Real.log t) (1 / t) t := by
      simpa [one_div] using Real.hasDerivAt_log htpos.ne'
    have h3 : HasDerivAt (fun t : ℝ => (n : ℝ) ^ 2 / t) (-(n : ℝ) ^ 2 / t ^ 2) t := by
      have hinv := hasDerivAt_inv htpos.ne'
      have h4 := hinv.const_mul ((n : ℝ) ^ 2)
      have hfun : (fun y : ℝ => (n : ℝ) ^ 2 * y⁻¹) = fun y : ℝ => (n : ℝ) ^ 2 / y := by
        funext y
        rw [div_eq_mul_inv]
      rw [hfun] at h4
      convert h4 using 1
      field_simp
    have hcomb := (h1.sub ((h2.const_mul (2 * (n : ℝ))))).sub h3
    convert hcomb using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ => (t - n) ^ 2 / t ^ 2)
      MeasureTheory.volume (n : ℝ) ((n : ℝ) + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t ht
      have htIcc : t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1) := by
        rwa [Set.uIcc_of_le (by linarith)] at ht
      have : 0 < t := lt_of_lt_of_le hnpos htIcc.1
      positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hlog : Real.log (((n : ℝ) + 1) / n) = Real.log ((n : ℝ) + 1) - Real.log n :=
    Real.log_div (by positivity) (by positivity)
  rw [hlog]
  field_simp
  ring

/-- The first block `∫_0^1 {t}²/t² dt = 1`. -/
theorem fract_sq_block_zero :
    (∫ t in (0 : ℝ)..1, (Int.fract t) ^ 2 / t ^ 2) = 1 := by
  have hcongr : (∫ t in (0 : ℝ)..1, (Int.fract t) ^ 2 / t ^ 2) =
      ∫ _t in (0 : ℝ)..1, (1 : ℝ) := by
    apply intervalIntegral.integral_congr_ae'
    · filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (1 : ℝ)]
        with t ht_ne ht
      have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := ht
      have hlt : t < 1 := lt_of_le_of_ne htIoc.2 ht_ne
      have hfr : Int.fract t = t := Int.fract_eq_self.mpr ⟨htIoc.1.le, hlt⟩
      rw [hfr]
      have htpos : 0 < t := htIoc.1
      field_simp
    · filter_upwards with t ht
      exfalso
      have h1 : (1 : ℝ) < t := ht.1
      have h2 : t ≤ 0 := ht.2
      linarith
  rw [hcongr]
  simp

/-! ## The partial-sum closed form and the limit -/

/-- `∫_0^N {t}²/t² dt = 2N − H_N − 2N·log N + 2·log N!`. -/
theorem fract_sq_integral_nat (N : ℕ) :
    (∫ t in (0 : ℝ)..(N : ℝ), (Int.fract t) ^ 2 / t ^ 2) =
      2 * N - (harmonic N : ℝ) - 2 * N * Real.log N + 2 * Real.log ((Nat.factorial N : ℕ) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hsplit : (∫ t in (0 : ℝ)..((N + 1 : ℕ) : ℝ), (Int.fract t) ^ 2 / t ^ 2) =
          (∫ t in (0 : ℝ)..(N : ℝ), (Int.fract t) ^ 2 / t ^ 2) +
            ∫ t in (N : ℝ)..((N : ℝ) + 1), (Int.fract t) ^ 2 / t ^ 2 := by
        have h1 : IntervalIntegrable (fun t : ℝ => (Int.fract t) ^ 2 / t ^ 2)
            MeasureTheory.volume (0 : ℝ) (N : ℝ) :=
          intervalIntegrable_fract_sq_div_sq (by positivity)
        have h2 : IntervalIntegrable (fun t : ℝ => (Int.fract t) ^ 2 / t ^ 2)
            MeasureTheory.volume (N : ℝ) ((N : ℝ) + 1) := by
          have h3 := intervalIntegrable_fract_sq_div_sq
            (x := (N : ℝ) + 1) (by positivity)
          have h4 := intervalIntegrable_fract_sq_div_sq (x := (N : ℝ)) (by positivity)
          exact (h4.symm.trans h3)
        have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
        rw [show (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 by push_cast; ring]
        exact hadd.symm
      rw [hsplit, ih]
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      · subst hN0
        have hz1 : (∫ t in ((0 : ℕ) : ℝ)..(((0 : ℕ) : ℝ) + 1), (Int.fract t) ^ 2 / t ^ 2) =
            (1 : ℝ) := by
          rw [show ((0 : ℕ) : ℝ) = (0 : ℝ) by norm_num]
          rw [show (0 : ℝ) + 1 = 1 by norm_num]
          exact fract_sq_block_zero
        rw [hz1]
        norm_num [harmonic_succ, harmonic_zero, Nat.factorial]
      · rw [fract_sq_block hNpos]
        have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
        have hlog_div : Real.log (((N : ℝ) + 1) / N) =
            Real.log ((N : ℝ) + 1) - Real.log N := Real.log_div (by positivity) (by positivity)
        have hfact : Real.log ((Nat.factorial (N + 1) : ℕ) : ℝ) =
            Real.log ((N : ℝ) + 1) + Real.log ((Nat.factorial N : ℕ) : ℝ) := by
          have hfp : (0 : ℝ) < ((Nat.factorial N : ℕ) : ℝ) := by
            exact_mod_cast Nat.factorial_pos N
          rw [Nat.factorial_succ]
          push_cast
          rw [Real.log_mul (by positivity) hfp.ne']
        have hharm : ((harmonic (N + 1) : ℚ) : ℝ) = (harmonic N : ℝ) + 1 / ((N : ℝ) + 1) := by
          rw [harmonic_succ]
          push_cast
          ring
        rw [hharm, hfact, hlog_div]
        have h1N : ((N : ℝ) + 1) ≠ 0 := by positivity
        push_cast
        field_simp
        ring

/-- The `N → ∞` limit: `∫_0^N {t}²/t² dt → log 2π − γ`. -/
theorem tendsto_fract_sq_integral_nat :
    Tendsto (fun N : ℕ => ∫ t in (0 : ℝ)..(N : ℝ), (Int.fract t) ^ 2 / t ^ 2) atTop
      (𝓝 (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant)) := by
  -- rewrite via the closed form and Stirling
  have hstirling := Stirling.tendsto_stirlingSeq_sqrt_pi
  have hlogstirling : Tendsto (fun N : ℕ => Real.log (Stirling.stirlingSeq N)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) := by
    apply Filter.Tendsto.log hstirling
    positivity
  have hgamma := Real.tendsto_eulerMascheroniSeq
  -- log(N+1) − log N → 0
  have hlogshift : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) - Real.log N) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / N) atTop (𝓝 1) := by
      have h2 : (fun N : ℕ => ((N : ℝ) + 1) / N) =ᶠ[atTop] fun N : ℕ => 1 + 1 / N := by
        filter_upwards [eventually_ge_atTop 1] with N hN
        have hNR : (0 : ℝ) < N := by exact_mod_cast hN
        field_simp
      rw [tendsto_congr' h2]
      have h3 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := by
        simpa [one_div] using tendsto_natCast_atTop_atTop.inv_tendsto_atTop
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add h3
    have h4 : Tendsto (fun N : ℕ => Real.log (((N : ℝ) + 1) / N)) atTop (𝓝 0) := by
      have := Filter.Tendsto.log h1 one_ne_zero
      simpa using this
    apply h4.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.log_div (by positivity) (by positivity)]
  -- (log N − H_N) → −γ
  have hHN : Tendsto (fun N : ℕ => Real.log N - (harmonic N : ℝ)) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) := by
    have h1 : (fun N : ℕ => Real.log N - (harmonic N : ℝ)) =
        fun N : ℕ => -(Real.eulerMascheroniSeq N) - (Real.log ((N : ℝ) + 1) - Real.log N) := by
      funext N
      unfold Real.eulerMascheroniSeq
      push_cast
      ring
    rw [h1]
    have := (hgamma.neg).sub hlogshift
    simpa using this
  -- combine
  have hcomb : Tendsto (fun N : ℕ =>
      (Real.log N - (harmonic N : ℝ)) + 2 * Real.log (Stirling.stirlingSeq N) + Real.log 2)
      atTop (𝓝 (-Real.eulerMascheroniConstant + 2 * Real.log (Real.sqrt Real.pi) +
        Real.log 2)) := by
    exact (hHN.add (hlogstirling.const_mul 2)).add tendsto_const_nhds
  have hconst : -Real.eulerMascheroniConstant + 2 * Real.log (Real.sqrt Real.pi) +
      Real.log 2 = Real.log (2 * Real.pi) - Real.eulerMascheroniConstant := by
    rw [Real.log_sqrt Real.pi_pos.le, Real.log_mul (by norm_num) Real.pi_pos.ne']
    ring
  rw [hconst] at hcomb
  -- identify with the closed form, eventually in N
  apply hcomb.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hfactpos : (0 : ℝ) < ((Nat.factorial N : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos N
  rw [fract_sq_integral_nat N]
  have hstirlingN := Stirling.log_stirlingSeq_formula N
  have hlogNe : Real.log ((N : ℝ) / Real.exp 1) = Real.log N - 1 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_exp]
  have hlog2N : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log N :=
    Real.log_mul (by norm_num) (by positivity)
  rw [hlogNe, hlog2N] at hstirlingN
  -- hstirlingN : log stirlingSeq N = log N! − 1/2(log2 + logN) − N(logN − 1)
  have hexpand : Real.log ((Nat.factorial N : ℕ) : ℝ) =
      Real.log (Stirling.stirlingSeq N) + 1 / 2 * (Real.log 2 + Real.log N) +
        (N : ℝ) * (Real.log N - 1) := by
    linarith [hstirlingN]
  rw [hexpand]
  ring

/-- **BBLS Proposition 87**: `A(1) = ∫_{(0,∞)} {t}²/t² dt = log 2π − γ`. -/
theorem bbls_A_one :
    (∫ t in Set.Ioi (0 : ℝ), (Int.fract t) ^ 2 / t ^ 2) =
      Real.log (2 * Real.pi) - Real.eulerMascheroniConstant := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h1 := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
    integrableOn_fract_sq_div_sq hcast
  exact tendsto_nhds_unique h1 tendsto_fract_sq_integral_nat

end RH.Criteria.NymanBeurling.VasyuninGram
