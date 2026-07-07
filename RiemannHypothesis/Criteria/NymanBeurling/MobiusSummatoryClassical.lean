import RiemannHypothesis.Criteria.NymanBeurling.MobiusSummatory

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
