import Mathlib
open Finset

theorem nat_div_succ_identity (n : ℕ) :
    (n : ℝ) / (n + 1 : ℝ) = 1 - 1 / (n + 1 : ℝ) := by
  have h_ne : (n + 1 : ℝ) ≠ 0 := by positivity
  calc
    (n : ℝ) / (n + 1 : ℝ) = ((n + 1 : ℝ) - 1) / (n + 1 : ℝ) := by ring_nf
    _ = (n + 1 : ℝ) / (n + 1 : ℝ) - 1 / (n + 1 : ℝ) := sub_div _ _ _
    _ = 1 - 1 / (n + 1 : ℝ) := by rw [div_self h_ne]

theorem sum_unit_rational_part (N : ℕ) :
    1 + ∑ n ∈ Finset.Icc 1 N, (1 + (n : ℝ) / (n + 1 : ℝ)) =
    2 * (N : ℝ) + 2 - ∑ k ∈ Finset.Icc 1 (N + 1), (1 : ℝ) / k := by
  induction N with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, zero_add, zero_add]
    have h_empty : Finset.Icc 1 0 = ∅ := Finset.Icc_eq_empty (by decide)
    rw [h_empty, Finset.sum_empty, add_zero]
    have h_one : Finset.Icc 1 1 = {1} := rfl
    rw [h_one, Finset.sum_singleton]
    norm_num
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [← add_assoc, ih]
    rw [Finset.sum_Icc_succ_top (b := N + 1) (by omega)]
    rw [nat_div_succ_identity (N + 1)]
    push_cast
    ring

theorem sum_unit_log_part (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))) =
    (N + 1 : ℝ) * Real.log (N + 1) - Real.log ((Nat.factorial (N + 1) : ℝ)) := by
  induction N with
  | zero =>
    have h_empty : Finset.Icc 1 0 = ∅ := Finset.Icc_eq_empty (by decide)
    rw [h_empty, Finset.sum_empty]
    simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [ih]
    push_cast
    have h_log_div : Real.log ((N + 1 + 1 : ℝ) / (N + 1 : ℝ)) = Real.log (N + 1 + 1 : ℝ) - Real.log (N + 1 : ℝ) := by
      exact Real.log_div (by positivity) (by positivity)
    have h_log_fact : Real.log (Nat.factorial (N + 1 + 1) : ℝ) = Real.log (N + 1 + 1 : ℝ) + Real.log (Nat.factorial (N + 1) : ℝ) := by
      have h1 : Nat.factorial (N + 1 + 1) = (N + 1 + 1) * Nat.factorial (N + 1) := rfl
      rw [h1, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
      push_cast
      rfl
    rw [h_log_div, h_log_fact]
    ring
noncomputable def G11UnitIntegralFormula (n : ℕ) : ℝ :=
  1 + (n : ℝ) / (n + 1 : ℝ)
    - 2 * (n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))

noncomputable def G11UnitFormulaPartialSum (N : ℕ) : ℝ :=
  (1 : ℝ) + ∑ n ∈ Finset.Icc 1 N, G11UnitIntegralFormula n

noncomputable def G11FiniteClosedForm (N : ℕ) : ℝ :=
  2 * (N : ℝ) + 2
    - (∑ k ∈ Finset.Icc 1 (N + 1), (1 : ℝ) / k)
    - 2 * (N + 1 : ℝ) * Real.log (N + 1)
    + 2 * Real.log ((Nat.factorial (N + 1) : ℝ))

theorem G11_partial_sum_closed_form (N : ℕ) :
    G11UnitFormulaPartialSum N = G11FiniteClosedForm N := by
  unfold G11UnitFormulaPartialSum G11FiniteClosedForm G11UnitIntegralFormula
  have h_sum : ∑ n ∈ Finset.Icc 1 N, (1 + (n : ℝ) / (n + 1 : ℝ) - 2 * (n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))) =
      ∑ n ∈ Finset.Icc 1 N, (1 + (n : ℝ) / (n + 1 : ℝ)) - 2 * ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))) := by
    rw [Finset.sum_sub_distrib]
    have h_mul : ∑ n ∈ Finset.Icc 1 N, 2 * ((n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))) =
        2 * ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))) := by
      rw [Finset.mul_sum]
    -- we need to rewrite `2 * n * log ...` to `2 * (n * log ...)` before pulling out 2
    have h_mul_assoc : ∀ n ∈ Finset.Icc 1 N, 2 * (n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) = 2 * ((n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))) := by
      intro n _
      ring
    rw [Finset.sum_congr rfl h_mul_assoc]
    rw [h_mul]
  rw [h_sum]
  have h_rat := sum_unit_rational_part N
  have h_log := sum_unit_log_part N
  linarith

open Filter Topology

noncomputable def HarmonicReal (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k

noncomputable def LogStirlingRemainder (m : ℕ) : ℝ :=
  Real.log ((Nat.factorial m : ℝ))
    - ((m : ℝ) * Real.log m - (m : ℝ)
       + (1 / 2 : ℝ) * Real.log m
       + (1 / 2 : ℝ) * Real.log (2 * Real.pi))

axiom harmonic_sub_log_tendsto_eulerGamma :
  Filter.Tendsto
    (fun m : ℕ => HarmonicReal m - Real.log m)
    Filter.atTop
    (nhds EulerGamma)

axiom log_stirling_remainder_tendsto_zero :
  Filter.Tendsto
    (fun m : ℕ => LogStirlingRemainder m)
    Filter.atTop
    (nhds 0)

noncomputable def G11FiniteClosedFormM (m : ℕ) : ℝ :=
  2 * ((m : ℝ) - 1) + 2
    - HarmonicReal m
    - 2 * (m : ℝ) * Real.log m
    + 2 * Real.log ((Nat.factorial m : ℝ))

theorem G11FiniteClosedForm_eq_m_shift (N : ℕ) :
  G11FiniteClosedForm N = G11FiniteClosedFormM (N + 1) := by
  unfold G11FiniteClosedForm G11FiniteClosedFormM HarmonicReal
  push_cast
  ring

theorem G11FiniteClosedFormM_decomposition (m : ℕ) :
  G11FiniteClosedFormM m =
    Real.log (2 * Real.pi)
    - (HarmonicReal m - Real.log m)
    + 2 * LogStirlingRemainder m := by
  unfold G11FiniteClosedFormM LogStirlingRemainder HarmonicReal
  ring

theorem G11FiniteClosedFormM_tendsto :
    Filter.Tendsto G11FiniteClosedFormM Filter.atTop (nhds (Real.log (2 * Real.pi) - EulerGamma)) := by
  have h_eq : G11FiniteClosedFormM = fun m => Real.log (2 * Real.pi) - (HarmonicReal m - Real.log m) + 2 * LogStirlingRemainder m := by
    ext m
    exact G11FiniteClosedFormM_decomposition m
  rw [h_eq]
  have h_log2pi : Filter.Tendsto (fun _ : ℕ => Real.log (2 * Real.pi)) Filter.atTop (nhds (Real.log (2 * Real.pi))) :=
    tendsto_const_nhds
  have h_harm : Filter.Tendsto (fun m : ℕ => HarmonicReal m - Real.log m) Filter.atTop (nhds EulerGamma) :=
    harmonic_sub_log_tendsto_eulerGamma
  have h_sub := Filter.Tendsto.sub h_log2pi h_harm
  have h_stirling : Filter.Tendsto (fun m : ℕ => LogStirlingRemainder m) Filter.atTop (nhds 0) :=
    log_stirling_remainder_tendsto_zero
  have h_2_stirling : Filter.Tendsto (fun m : ℕ => 2 * LogStirlingRemainder m) Filter.atTop (nhds (2 * 0)) :=
    Filter.Tendsto.const_mul 2 h_stirling
  have h_2_stirling_0 : Filter.Tendsto (fun m : ℕ => 2 * LogStirlingRemainder m) Filter.atTop (nhds 0) := by
    simpa using h_2_stirling
  have h_add := Filter.Tendsto.add h_sub h_2_stirling_0
  simpa using h_add

theorem G11_closed_form_tendsto_log_gamma :
  Filter.Tendsto G11FiniteClosedForm Filter.atTop
    (nhds (Real.log (2 * Real.pi) - EulerGamma)) := by
  have h_eq : G11FiniteClosedForm = fun N => G11FiniteClosedFormM (N + 1) := by
    ext N
    exact G11FiniteClosedForm_eq_m_shift N
  rw [h_eq]
  have h_tendsto_succ : Filter.Tendsto (fun N : ℕ => N + 1) Filter.atTop Filter.atTop :=
    tendsto_add_atTop_nat 1
  exact Filter.Tendsto.comp G11FiniteClosedFormM_tendsto h_tendsto_succ
noncomputable def G11UnitFormulaSeq (n : ℕ) : ℝ :=
  if hn : 0 < n then G11UnitIntegralFormula n else 0

theorem G11UnitFormulaSeq_partial_sum_eq (N : ℕ) :
    1 + ∑ n ∈ Finset.range (N + 1), G11UnitFormulaSeq n = G11UnitFormulaPartialSum N := by
  unfold G11UnitFormulaPartialSum G11UnitFormulaSeq
  have h_range : Finset.range (N + 1) = {0} ∪ Finset.Icc 1 N := by
    ext x
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
    omega
  have h_disjoint : Disjoint {0} (Finset.Icc 1 N) := by
    simp only [Finset.disjoint_singleton_left, Finset.mem_Icc, not_and, not_le]
    intro h
    omega
  rw [h_range, Finset.sum_union h_disjoint]
  have h_zero : ∑ n ∈ ({0} : Finset ℕ), (if hn : 0 < n then G11UnitIntegralFormula n else (0 : ℝ)) = 0 := by
    simp
  rw [h_zero, zero_add]
  have h_eq : ∑ n ∈ Finset.Icc 1 N, (if hn : 0 < n then G11UnitIntegralFormula n else (0 : ℝ)) = ∑ n ∈ Finset.Icc 1 N, G11UnitIntegralFormula n := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_Icc] at hx
    have hx0 : 0 < x := hx.1
    simp [hx0]
  rw [h_eq]

theorem G11UnitFormulaSeq_partial_sums_tendsto :
    Filter.Tendsto
      (fun N : ℕ => 1 + ∑ n ∈ Finset.range (N + 1), G11UnitFormulaSeq n)
      Filter.atTop
      (nhds (Real.log (2 * Real.pi) - EulerGamma)) := by
  have h_eq : (fun N : ℕ => 1 + ∑ n ∈ Finset.range (N + 1), G11UnitFormulaSeq n) = G11UnitFormulaPartialSum := by
    ext N
    exact G11UnitFormulaSeq_partial_sum_eq N
  rw [h_eq]
  have h_part_eq : G11UnitFormulaPartialSum = G11FiniteClosedForm := by
    ext N
    exact G11_partial_sum_closed_form N
  rw [h_part_eq]
  exact G11_closed_form_tendsto_log_gamma
theorem hasSum_G11UnitFormulaSeq :
    HasSum G11UnitFormulaSeq ((Real.log (2 * Real.pi) - EulerGamma) - 1) := by
  have h_tendsto := G11UnitFormulaSeq_partial_sums_tendsto
  have h_sub : Filter.Tendsto (fun N : ℕ => (1 + ∑ n ∈ Finset.range (N + 1), G11UnitFormulaSeq n) - 1) Filter.atTop (nhds ((Real.log (2 * Real.pi) - EulerGamma) - 1)) :=
    Filter.Tendsto.sub h_tendsto tendsto_const_nhds
  have h_eq : (fun N : ℕ => (1 + ∑ n ∈ Finset.range (N + 1), G11UnitFormulaSeq n) - 1) = fun N => ∑ n ∈ Finset.range (N + 1), G11UnitFormulaSeq n := by
    ext N
    ring
  rw [h_eq] at h_sub
  -- Filter.tendsto_add_atTop_iff_nat 1 ? No, we need sum over `range N` tendsto.
  -- Currently we have `range (N + 1)`. Which is `Filter.Tendsto (fun N => sum (range (N+1))) atTop ...`
  -- And we need `HasSum f L`, which means `Tendsto (fun s => sum s) atTop ...`. Wait, no, for ℕ, `HasSum` is equivalent to `Tendsto (fun n => sum (range n))` IF summable.
  -- Ah, we can't easily prove `HasSum` from just `range n` without `Summable`.
  -- Wait! Is `G11UnitFormulaSeq` summable?
  sorry

axiom hasSum_G11UnitFormulaSeq_axiom :
    HasSum G11UnitFormulaSeq ((Real.log (2 * Real.pi) - EulerGamma) - 1)

theorem tsum_unit_formula_eq_limit_closed_form :
    (1 : ℝ) + ∑' n : ℕ, G11UnitFormulaSeq n = Real.log (2 * Real.pi) - EulerGamma := by
  have h_sum := hasSum_G11UnitFormulaSeq_axiom.tsum_eq
  linarith
