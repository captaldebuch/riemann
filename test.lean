import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import RiemannHypothesis.Criteria.NymanBeurling.G11IntegralEvaluation

noncomputable def LogStirlingRemainder (m : ℕ) : ℝ :=
  Real.log ((Nat.factorial m : ℝ))
    - ((m : ℝ) * Real.log m - (m : ℝ)
       + (1 / 2 : ℝ) * Real.log m
       + (1 / 2 : ℝ) * Real.log (2 * Real.pi))

open Filter

theorem log_stirling_remainder_eq (m : ℕ) (hm : 0 < m) :
  LogStirlingRemainder m = Real.log (Stirling.stirlingSeq m) - (1 / 2) * Real.log Real.pi := by
  unfold LogStirlingRemainder
  have h_form := Stirling.log_stirlingSeq_formula m
  have h_exp : Real.log (Real.exp 1) = 1 := Real.log_exp 1
  have hm_real : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_real
  have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hexp_ne : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
  have h_log_2n : Real.log (2 * m) = Real.log 2 + Real.log m := Real.log_mul h2_ne hm_ne
  have h_log_div : Real.log (m / Real.exp 1) = Real.log m - Real.log (Real.exp 1) := Real.log_div hm_ne hexp_ne
  have h_log_2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi := Real.log_mul h2_ne hpi_ne
  rw [h_form]
  rw [h_exp] at h_log_div
  rw [h_log_2n, h_log_div, h_log_2pi]
  ring

theorem log_stirling_remainder_tendsto_zero :
  Filter.Tendsto
    (fun m : ℕ => LogStirlingRemainder m)
    Filter.atTop
    (nhds 0) := by
  have h_eq : (fun m : ℕ => LogStirlingRemainder (m + 1)) = (fun m : ℕ => Real.log (Stirling.stirlingSeq (m + 1)) - (1 / 2) * Real.log Real.pi) := by
    ext m
    exact log_stirling_remainder_eq (m + 1) (Nat.succ_pos m)
  have h_lim1 : Tendsto (fun m : ℕ => Stirling.stirlingSeq (m + 1)) atTop (nhds (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)
  have h_lim2 : Tendsto (fun m : ℕ => Real.log (Stirling.stirlingSeq (m + 1))) atTop (nhds (Real.log (Real.sqrt Real.pi))) :=
    Tendsto.log h_lim1 (by positivity)
  have h_log_sqrt : Real.log (Real.sqrt Real.pi) = (1 / 2) * Real.log Real.pi := by
    rw [Real.log_sqrt (by positivity)]
    ring
  rw [h_log_sqrt] at h_lim2
  have h_lim3 : Tendsto (fun m : ℕ => Real.log (Stirling.stirlingSeq (m + 1)) - (1 / 2) * Real.log Real.pi) atTop (nhds 0) := by
    have h_sub := Tendsto.sub h_lim2 (tendsto_const_nhds (x := (1 / 2) * Real.log Real.pi))
    rw [sub_self] at h_sub
    exact h_sub
  rw [← h_eq] at h_lim3
  exact (tendsto_add_atTop_iff_nat 1).mp h_lim3

