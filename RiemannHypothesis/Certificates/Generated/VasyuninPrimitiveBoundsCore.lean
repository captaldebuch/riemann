import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula
import RiemannHypothesis.Certificates.Generated.ChiRhoBoundsN50
import RiemannHypothesis.Certificates.Generated.TranscendentalBoundsGenerated
import RiemannHypothesis.Certificates.Generated.CotangentBoundsCore
import RiemannHypothesis.Certificates.Generated.CotangentBoundsK10
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals

namespace RH.Certificates.Generated
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Certificates.Generated.ChiRhoBoundsN50
open scoped Finset

lemma vasyunin_log_div (h k : ℕ) (h_pos : 0 < h) (k_pos : 0 < k) :
  Real.log ((h : ℝ) / (k : ℝ)) = Real.log (h : ℝ) - Real.log (k : ℝ) := by
  exact Real.log_div (by exact_mod_cast ne_of_gt h_pos) (by exact_mod_cast ne_of_gt k_pos)

lemma sum_Ico_1_3 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 3, f a = f 1 + f 2 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_4 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 4, f a = f 1 + f 2 + f 3 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_5 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 5, f a = f 1 + f 2 + f 3 + f 4 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_6 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 6, f a = f 1 + f 2 + f 3 + f 4 + f 5 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_7 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 7, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_8 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 8, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_9 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 9, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_10 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 10, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_11 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 11, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_12 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 12, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_13 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 13, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_14 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 14, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_15 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 15, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_16 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 16, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_17 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 17, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_18 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 18, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_19 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 19, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_20 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 20, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_21 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 21, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_22 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 22, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_23 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 23, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_24 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 24, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_25 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 25, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_26 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 26, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_27 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 27, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_28 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 28, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_29 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 29, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_30 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 30, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_31 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 31, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_32 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 32, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_33 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 33, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_34 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 34, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_35 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 35, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_36 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 36, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_37 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 37, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_38 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 38, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_39 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 39, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_40 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 40, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_41 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 41, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_42 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 42, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_43 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 43, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_44 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 44, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_45 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 45, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_46 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 46, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 + f 45 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_47 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 47, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 + f 45 + f 46 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_48 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 48, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 + f 45 + f 46 + f 47 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_49 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 49, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 + f 45 + f 46 + f 47 + f 48 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

lemma sum_Ico_1_50 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 50, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 + f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 + f 33 + f 34 + f 35 + f 36 + f 37 + f 38 + f 39 + f 40 + f 41 + f 42 + f 43 + f 44 + f 45 + f 46 + f 47 + f 48 + f 49 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

def prim_pi_lower : ℚ := 884279719003555 / 281474976710656
def prim_pi_upper : ℚ := 884279719003555 / 281474976710656
axiom prim_pi_bounds : ((prim_pi_lower : ℚ) : ℝ) ≤ Real.pi ∧ Real.pi ≤ ((prim_pi_upper : ℚ) : ℝ)

def prim_log_1_lower : ℚ := 0 / 1
def prim_log_1_upper : ℚ := 0 / 1
axiom prim_log_1_bounds : ((prim_log_1_lower : ℚ) : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ ((prim_log_1_upper : ℚ) : ℝ)

def prim_log_4_lower : ℚ := 6243314768165359 / 4503599627370496
def prim_log_4_upper : ℚ := 6243314768165359 / 4503599627370496
axiom prim_log_4_bounds : ((prim_log_4_lower : ℚ) : ℝ) ≤ Real.log 4 ∧ Real.log 4 ≤ ((prim_log_4_upper : ℚ) : ℝ)

def prim_log_6_lower : ℚ := 4034683638976513 / 2251799813685248
def prim_log_6_upper : ℚ := 4034683638976513 / 2251799813685248
axiom prim_log_6_bounds : ((prim_log_6_lower : ℚ) : ℝ) ≤ Real.log 6 ∧ Real.log 6 ≤ ((prim_log_6_upper : ℚ) : ℝ)

def prim_log_8_lower : ℚ := 4682486076124019 / 2251799813685248
def prim_log_8_upper : ℚ := 4682486076124019 / 2251799813685248
axiom prim_log_8_bounds : ((prim_log_8_lower : ℚ) : ℝ) ≤ Real.log 8 ∧ Real.log 8 ≤ ((prim_log_8_upper : ℚ) : ℝ)

def prim_log_9_lower : ℚ := 4947709893870347 / 2251799813685248
def prim_log_9_upper : ℚ := 4947709893870347 / 2251799813685248
axiom prim_log_9_bounds : ((prim_log_9_lower : ℚ) : ℝ) ≤ Real.log 9 ∧ Real.log 9 ≤ ((prim_log_9_upper : ℚ) : ℝ)

def prim_log_10_lower : ℚ := 2592480341699211 / 1125899906842624
def prim_log_10_upper : ℚ := 2592480341699211 / 1125899906842624
axiom prim_log_10_bounds : ((prim_log_10_lower : ℚ) : ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ ((prim_log_10_upper : ℚ) : ℝ)

def prim_log_12_lower : ℚ := 5595512331017853 / 2251799813685248
def prim_log_12_upper : ℚ := 5595512331017853 / 2251799813685248
axiom prim_log_12_bounds : ((prim_log_12_lower : ℚ) : ℝ) ≤ Real.log 12 ∧ Real.log 12 ≤ ((prim_log_12_upper : ℚ) : ℝ)

def prim_log_14_lower : ℚ := 5942628803132327 / 2251799813685248
def prim_log_14_upper : ℚ := 5942628803132327 / 2251799813685248
axiom prim_log_14_bounds : ((prim_log_14_lower : ℚ) : ℝ) ≤ Real.log 14 ∧ Real.log 14 ≤ ((prim_log_14_upper : ℚ) : ℝ)

def prim_log_15_lower : ℚ := 6097986938292255 / 2251799813685248
def prim_log_15_upper : ℚ := 6097986938292255 / 2251799813685248
axiom prim_log_15_bounds : ((prim_log_15_lower : ℚ) : ℝ) ≤ Real.log 15 ∧ Real.log 15 ≤ ((prim_log_15_upper : ℚ) : ℝ)

def prim_log_16_lower : ℚ := 6243314768165359 / 2251799813685248
def prim_log_16_upper : ℚ := 6243314768165359 / 2251799813685248
axiom prim_log_16_bounds : ((prim_log_16_lower : ℚ) : ℝ) ≤ Real.log 16 ∧ Real.log 16 ≤ ((prim_log_16_upper : ℚ) : ℝ)

def prim_log_18_lower : ℚ := 3254269292955843 / 1125899906842624
def prim_log_18_upper : ℚ := 3254269292955843 / 1125899906842624
axiom prim_log_18_bounds : ((prim_log_18_lower : ℚ) : ℝ) ≤ Real.log 18 ∧ Real.log 18 ≤ ((prim_log_18_upper : ℚ) : ℝ)

def prim_log_20_lower : ℚ := 6745789375439761 / 2251799813685248
def prim_log_20_upper : ℚ := 6745789375439761 / 2251799813685248
axiom prim_log_20_bounds : ((prim_log_20_lower : ℚ) : ℝ) ≤ Real.log 20 ∧ Real.log 20 ≤ ((prim_log_20_upper : ℚ) : ℝ)

def prim_log_21_lower : ℚ := 6855655058026161 / 2251799813685248
def prim_log_21_upper : ℚ := 6855655058026161 / 2251799813685248
axiom prim_log_21_bounds : ((prim_log_21_lower : ℚ) : ℝ) ≤ Real.log 21 ∧ Real.log 21 ≤ ((prim_log_21_upper : ℚ) : ℝ)

def prim_log_22_lower : ℚ := 870051102570681 / 281474976710656
def prim_log_22_upper : ℚ := 870051102570681 / 281474976710656
axiom prim_log_22_bounds : ((prim_log_22_lower : ℚ) : ℝ) ≤ Real.log 22 ∧ Real.log 22 ≤ ((prim_log_22_upper : ℚ) : ℝ)

def prim_log_24_lower : ℚ := 7156341023059193 / 2251799813685248
def prim_log_24_upper : ℚ := 7156341023059193 / 2251799813685248
axiom prim_log_24_bounds : ((prim_log_24_lower : ℚ) : ℝ) ≤ Real.log 24 ∧ Real.log 24 ≤ ((prim_log_24_upper : ℚ) : ℝ)

def prim_log_25_lower : ℚ := 7248263982714163 / 2251799813685248
def prim_log_25_upper : ℚ := 7248263982714163 / 2251799813685248
axiom prim_log_25_bounds : ((prim_log_25_lower : ℚ) : ℝ) ≤ Real.log 25 ∧ Real.log 25 ≤ ((prim_log_25_upper : ℚ) : ℝ)

def prim_log_26_lower : ℚ := 7336581177285325 / 2251799813685248
def prim_log_26_upper : ℚ := 7336581177285325 / 2251799813685248
axiom prim_log_26_bounds : ((prim_log_26_lower : ℚ) : ℝ) ≤ Real.log 26 ∧ Real.log 26 ≤ ((prim_log_26_upper : ℚ) : ℝ)

def prim_log_27_lower : ℚ := 463847802550345 / 140737488355328
def prim_log_27_upper : ℚ := 463847802550345 / 140737488355328
axiom prim_log_27_bounds : ((prim_log_27_lower : ℚ) : ℝ) ≤ Real.log 27 ∧ Real.log 27 ≤ ((prim_log_27_upper : ℚ) : ℝ)

def prim_log_28_lower : ℚ := 7503457495173667 / 2251799813685248
def prim_log_28_upper : ℚ := 7503457495173667 / 2251799813685248
axiom prim_log_28_bounds : ((prim_log_28_lower : ℚ) : ℝ) ≤ Real.log 28 ∧ Real.log 28 ≤ ((prim_log_28_upper : ℚ) : ℝ)

def prim_log_30_lower : ℚ := 7658815630333595 / 2251799813685248
def prim_log_30_upper : ℚ := 7658815630333595 / 2251799813685248
axiom prim_log_30_bounds : ((prim_log_30_lower : ℚ) : ℝ) ≤ Real.log 30 ∧ Real.log 30 ≤ ((prim_log_30_upper : ℚ) : ℝ)

def prim_log_32_lower : ℚ := 7804143460206699 / 2251799813685248
def prim_log_32_upper : ℚ := 7804143460206699 / 2251799813685248
axiom prim_log_32_bounds : ((prim_log_32_lower : ℚ) : ℝ) ≤ Real.log 32 ∧ Real.log 32 ≤ ((prim_log_32_upper : ℚ) : ℝ)

def prim_log_33_lower : ℚ := 7873435075459281 / 2251799813685248
def prim_log_33_upper : ℚ := 7873435075459281 / 2251799813685248
axiom prim_log_33_bounds : ((prim_log_33_lower : ℚ) : ℝ) ≤ Real.log 33 ∧ Real.log 33 ≤ ((prim_log_33_upper : ℚ) : ℝ)

def prim_log_34_lower : ℚ := 3970328986158843 / 1125899906842624
def prim_log_34_upper : ℚ := 3970328986158843 / 1125899906842624
axiom prim_log_34_bounds : ((prim_log_34_lower : ℚ) : ℝ) ≤ Real.log 34 ∧ Real.log 34 ≤ ((prim_log_34_upper : ℚ) : ℝ)

def prim_log_35_lower : ℚ := 8005932102448069 / 2251799813685248
def prim_log_35_upper : ℚ := 8005932102448069 / 2251799813685248
axiom prim_log_35_bounds : ((prim_log_35_lower : ℚ) : ℝ) ≤ Real.log 35 ∧ Real.log 35 ≤ ((prim_log_35_upper : ℚ) : ℝ)

def prim_log_36_lower : ℚ := 4034683638976513 / 1125899906842624
def prim_log_36_upper : ℚ := 4034683638976513 / 1125899906842624
axiom prim_log_36_bounds : ((prim_log_36_lower : ℚ) : ℝ) ≤ Real.log 36 ∧ Real.log 36 ≤ ((prim_log_36_upper : ℚ) : ℝ)

def prim_log_38_lower : ℚ := 1023889479591989 / 281474976710656
def prim_log_38_upper : ℚ := 1023889479591989 / 281474976710656
axiom prim_log_38_bounds : ((prim_log_38_lower : ℚ) : ℝ) ≤ Real.log 38 ∧ Real.log 38 ≤ ((prim_log_38_upper : ℚ) : ℝ)

def prim_log_39_lower : ℚ := 4124803716089579 / 1125899906842624
def prim_log_39_upper : ℚ := 4124803716089579 / 1125899906842624
axiom prim_log_39_bounds : ((prim_log_39_lower : ℚ) : ℝ) ≤ Real.log 39 ∧ Real.log 39 ≤ ((prim_log_39_upper : ℚ) : ℝ)

def prim_log_40_lower : ℚ := 8306618067481101 / 2251799813685248
def prim_log_40_upper : ℚ := 8306618067481101 / 2251799813685248
axiom prim_log_40_bounds : ((prim_log_40_lower : ℚ) : ℝ) ≤ Real.log 40 ∧ Real.log 40 ≤ ((prim_log_40_upper : ℚ) : ℝ)

def prim_log_42_lower : ℚ := 8416483750067501 / 2251799813685248
def prim_log_42_upper : ℚ := 8416483750067501 / 2251799813685248
axiom prim_log_42_bounds : ((prim_log_42_lower : ℚ) : ℝ) ≤ Real.log 42 ∧ Real.log 42 ≤ ((prim_log_42_upper : ℚ) : ℝ)

def prim_log_44_lower : ℚ := 8521237512606787 / 2251799813685248
def prim_log_44_upper : ℚ := 8521237512606787 / 2251799813685248
axiom prim_log_44_bounds : ((prim_log_44_lower : ℚ) : ℝ) ≤ Real.log 44 ∧ Real.log 44 ≤ ((prim_log_44_upper : ℚ) : ℝ)

def prim_log_45_lower : ℚ := 2142960471306857 / 562949953421312
def prim_log_45_upper : ℚ := 2142960471306857 / 562949953421312
axiom prim_log_45_bounds : ((prim_log_45_lower : ℚ) : ℝ) ≤ Real.log 45 ∧ Real.log 45 ≤ ((prim_log_45_upper : ℚ) : ℝ)

def prim_log_46_lower : ℚ := 2155333495820443 / 562949953421312
def prim_log_46_upper : ℚ := 2155333495820443 / 562949953421312
axiom prim_log_46_bounds : ((prim_log_46_lower : ℚ) : ℝ) ≤ Real.log 46 ∧ Real.log 46 ≤ ((prim_log_46_upper : ℚ) : ℝ)

def prim_log_48_lower : ℚ := 8717169715100533 / 2251799813685248
def prim_log_48_upper : ℚ := 8717169715100533 / 2251799813685248
axiom prim_log_48_bounds : ((prim_log_48_lower : ℚ) : ℝ) ≤ Real.log 48 ∧ Real.log 48 ≤ ((prim_log_48_upper : ℚ) : ℝ)

def prim_log_49_lower : ℚ := 8763600222181975 / 2251799813685248
def prim_log_49_upper : ℚ := 8763600222181975 / 2251799813685248
axiom prim_log_49_bounds : ((prim_log_49_lower : ℚ) : ℝ) ≤ Real.log 49 ∧ Real.log 49 ≤ ((prim_log_49_upper : ℚ) : ℝ)

def prim_log_50_lower : ℚ := 8809092674755503 / 2251799813685248
def prim_log_50_upper : ℚ := 8809092674755503 / 2251799813685248
axiom prim_log_50_bounds : ((prim_log_50_lower : ℚ) : ℝ) ≤ Real.log 50 ∧ Real.log 50 ≤ ((prim_log_50_upper : ℚ) : ℝ)

def cot_pi_1_2_lower : ℚ := -488112139 / 9671406556917033397649408
def cot_pi_1_2_upper : ℚ := 1671954449 / 9671406556917033397649408
theorem cot_pi_1_2_bounds :
  ((cot_pi_1_2_lower : ℚ) : ℝ) ≤ cotangentTermV 1 2 ∧
  cotangentTermV 1 2 ≤ ((cot_pi_1_2_upper : ℚ) : ℝ) := by
  have h0 : cotangentTermV 1 2 = 0 :=
    cotangentTermV_exact_of_two_mul_eq (by norm_num) (by norm_num)
  rw [h0]; constructor <;> norm_num [cot_pi_1_2_lower, cot_pi_1_2_upper]

def cot_pi_1_3_lower : ℚ := 5200308914369303 / 9007199254740992
def cot_pi_1_3_upper : ℚ := 5200308914369315 / 9007199254740992
theorem cot_pi_1_3_bounds :
  ((cot_pi_1_3_lower : ℚ) : ℝ) ≤ cotangentTermV 1 3 ∧
  cotangentTermV 1 3 ≤ ((cot_pi_1_3_upper : ℚ) : ℝ) := by
  have h := cot_pi_div_1_3_mem_interval_v2
  constructor
  · norm_num [cot_pi_1_3_lower]; linarith [h.1]
  · norm_num [cot_pi_1_3_upper]; linarith [h.2]

def cot_pi_2_3_lower : ℚ := -2600154457184657 / 4503599627370496
def cot_pi_2_3_upper : ℚ := -325019307148081 / 562949953421312
theorem cot_pi_2_3_bounds :
  ((cot_pi_2_3_lower : ℚ) : ℝ) ≤ cotangentTermV 2 3 ∧
  cotangentTermV 2 3 ≤ ((cot_pi_2_3_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 2 3 = - cotangentTermV 1 3 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have h := cot_pi_div_1_3_mem_interval_v2
  rw [hobtuse]
  constructor
  · norm_num [cot_pi_2_3_lower]; linarith [h.2]
  · norm_num [cot_pi_2_3_upper]; linarith [h.1]

def cot_pi_1_4_lower : ℚ := 2251799813685247 / 2251799813685248
def cot_pi_1_4_upper : ℚ := 2251799813685249 / 2251799813685248
theorem cot_pi_1_4_bounds :
  ((cot_pi_1_4_lower : ℚ) : ℝ) ≤ cotangentTermV 1 4 ∧
  cotangentTermV 1 4 ≤ ((cot_pi_1_4_upper : ℚ) : ℝ) := by
  have h := cot_pi_div_1_4_mem_interval_v2
  constructor
  · norm_num [cot_pi_1_4_lower]; linarith [h.1]
  · norm_num [cot_pi_1_4_upper]; linarith [h.2]

def cot_pi_2_4_lower : ℚ := -488112139 / 9671406556917033397649408
def cot_pi_2_4_upper : ℚ := 1671954449 / 9671406556917033397649408
theorem cot_pi_2_4_bounds :
  ((cot_pi_2_4_lower : ℚ) : ℝ) ≤ cotangentTermV 2 4 ∧
  cotangentTermV 2 4 ≤ ((cot_pi_2_4_upper : ℚ) : ℝ) := by
  have h0 : cotangentTermV 2 4 = 0 :=
    cotangentTermV_exact_of_two_mul_eq (by norm_num) (by norm_num)
  rw [h0]; constructor <;> norm_num [cot_pi_2_4_lower, cot_pi_2_4_upper]

def cot_pi_3_4_lower : ℚ := -2251799813685249 / 2251799813685248
def cot_pi_3_4_upper : ℚ := -4503599627370491 / 4503599627370496
theorem cot_pi_3_4_bounds :
  ((cot_pi_3_4_lower : ℚ) : ℝ) ≤ cotangentTermV 3 4 ∧
  cotangentTermV 3 4 ≤ ((cot_pi_3_4_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 3 4 = - cotangentTermV 1 4 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have h := cot_pi_div_1_4_mem_interval_v2
  rw [hobtuse]
  constructor
  · norm_num [cot_pi_3_4_lower]; linarith [h.2]
  · norm_num [cot_pi_3_4_upper]; linarith [h.1]

def cot_pi_1_5_lower : ℚ := 6198673104153461 / 4503599627370496
def cot_pi_1_5_upper : ℚ := 6198673104153469 / 4503599627370496
theorem cot_pi_1_5_bounds :
  ((cot_pi_1_5_lower : ℚ) : ℝ) ≤ cotangentTermV 1 5 ∧
  cotangentTermV 1 5 ≤ ((cot_pi_1_5_upper : ℚ) : ℝ) := by
  have h := cot_pi_div_1_5_mem_interval_v2
  constructor
  · norm_num [cot_pi_1_5_lower]; linarith [h.1]
  · norm_num [cot_pi_1_5_upper]; linarith [h.2]

def cot_pi_2_5_lower : ℚ := 2926616445759701 / 9007199254740992
def cot_pi_2_5_upper : ℚ := 1463308222879853 / 4503599627370496
theorem cot_pi_2_5_bounds :
  ((cot_pi_2_5_lower : ℚ) : ℝ) ≤ cotangentTermV 2 5 ∧
  cotangentTermV 2 5 ≤ ((cot_pi_2_5_upper : ℚ) : ℝ) := by
  have h := cot_pi_div_2_5_mem_interval_v2
  constructor
  · norm_num [cot_pi_2_5_lower]; linarith [h.1]
  · norm_num [cot_pi_2_5_upper]; linarith [h.2]

def cot_pi_3_5_lower : ℚ := -2926616445759705 / 9007199254740992
def cot_pi_3_5_upper : ℚ := -731654111439925 / 2251799813685248
theorem cot_pi_3_5_bounds :
  ((cot_pi_3_5_lower : ℚ) : ℝ) ≤ cotangentTermV 3 5 ∧
  cotangentTermV 3 5 ≤ ((cot_pi_3_5_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 3 5 = - cotangentTermV 2 5 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have h := cot_pi_div_2_5_mem_interval_v2
  rw [hobtuse]
  constructor
  · norm_num [cot_pi_3_5_lower]; linarith [h.2]
  · norm_num [cot_pi_3_5_upper]; linarith [h.1]

def cot_pi_4_5_lower : ℚ := -6198673104153469 / 4503599627370496
def cot_pi_4_5_upper : ℚ := -6198673104153459 / 4503599627370496
theorem cot_pi_4_5_bounds :
  ((cot_pi_4_5_lower : ℚ) : ℝ) ≤ cotangentTermV 4 5 ∧
  cotangentTermV 4 5 ≤ ((cot_pi_4_5_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 4 5 = - cotangentTermV 1 5 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have h := cot_pi_div_1_5_mem_interval_v2
  rw [hobtuse]
  constructor
  · norm_num [cot_pi_4_5_lower]; linarith [h.2]
  · norm_num [cot_pi_4_5_upper]; linarith [h.1]

def cot_pi_1_6_lower : ℚ := 1950115842888489 / 1125899906842624
def cot_pi_1_6_upper : ℚ := 487528960722123 / 281474976710656
theorem cot_pi_1_6_bounds :
  ((cot_pi_1_6_lower : ℚ) : ℝ) ≤ cotangentTermV 1 6 ∧
  cotangentTermV 1 6 ≤ ((cot_pi_1_6_upper : ℚ) : ℝ) := by
  have h := cot_pi_div_1_6_mem_interval_v2
  constructor
  · norm_num [cot_pi_1_6_lower]; linarith [h.1]
  · norm_num [cot_pi_1_6_upper]; linarith [h.2]

def cot_pi_2_6_lower : ℚ := 5200308914369303 / 9007199254740992
def cot_pi_2_6_upper : ℚ := 5200308914369315 / 9007199254740992
theorem cot_pi_2_6_bounds :
  ((cot_pi_2_6_lower : ℚ) : ℝ) ≤ cotangentTermV 2 6 ∧
  cotangentTermV 2 6 ≤ ((cot_pi_2_6_upper : ℚ) : ℝ) := by
  have hred : cotangentTermV 2 6 = cotangentTermV 1 3 :=
    cotangentTermV_gcd_reduce (g := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [hred]
  have h := cot_pi_div_1_3_mem_interval_v2
  constructor
  · norm_num [cot_pi_2_6_lower]; linarith [h.1]
  · norm_num [cot_pi_2_6_upper]; linarith [h.2]

def cot_pi_3_6_lower : ℚ := -488112137 / 9671406556917033397649408
def cot_pi_3_6_upper : ℚ := 1671954447 / 9671406556917033397649408
theorem cot_pi_3_6_bounds :
  ((cot_pi_3_6_lower : ℚ) : ℝ) ≤ cotangentTermV 3 6 ∧
  cotangentTermV 3 6 ≤ ((cot_pi_3_6_upper : ℚ) : ℝ) := by
  have h0 : cotangentTermV 3 6 = 0 :=
    cotangentTermV_exact_of_two_mul_eq (by norm_num) (by norm_num)
  rw [h0]; constructor <;> norm_num [cot_pi_3_6_lower, cot_pi_3_6_upper]

def cot_pi_4_6_lower : ℚ := -2600154457184657 / 4503599627370496
def cot_pi_4_6_upper : ℚ := -325019307148081 / 562949953421312
theorem cot_pi_4_6_bounds :
  ((cot_pi_4_6_lower : ℚ) : ℝ) ≤ cotangentTermV 4 6 ∧
  cotangentTermV 4 6 ≤ ((cot_pi_4_6_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 4 6 = - cotangentTermV 2 6 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have hred : cotangentTermV 2 6 = cotangentTermV 1 3 :=
    cotangentTermV_gcd_reduce (g := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [hobtuse, hred]
  have h := cot_pi_div_1_3_mem_interval_v2
  constructor
  · norm_num [cot_pi_4_6_lower]; linarith [h.2]
  · norm_num [cot_pi_4_6_upper]; linarith [h.1]

def cot_pi_5_6_lower : ℚ := -7800463371553969 / 4503599627370496
def cot_pi_5_6_upper : ℚ := -7800463371553939 / 4503599627370496
theorem cot_pi_5_6_bounds :
  ((cot_pi_5_6_lower : ℚ) : ℝ) ≤ cotangentTermV 5 6 ∧
  cotangentTermV 5 6 ≤ ((cot_pi_5_6_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 5 6 = - cotangentTermV 1 6 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have h := cot_pi_div_1_6_mem_interval_v2
  rw [hobtuse]
  constructor
  · norm_num [cot_pi_5_6_lower]; linarith [h.2]
  · norm_num [cot_pi_5_6_upper]; linarith [h.1]

def cot_pi_1_7_lower : ℚ := 4675910493915015 / 2251799813685248
def cot_pi_1_7_upper : ℚ := 4675910493915021 / 2251799813685248
theorem cot_pi_1_7_bounds :
  ((cot_pi_1_7_lower : ℚ) : ℝ) ≤ cotangentTermV 1 7 ∧
  cotangentTermV 1 7 ≤ ((cot_pi_1_7_upper : ℚ) : ℝ) := by
  have h := cot_pi_div_1_7_mem_interval_v2
  constructor
  · norm_num [cot_pi_1_7_lower]; linarith [h.1]
  · norm_num [cot_pi_1_7_upper]; linarith [h.2]

def cot_pi_2_7_lower : ℚ := 3591500857008679 / 4503599627370496
def cot_pi_2_7_upper : ℚ := 3591500857008683 / 4503599627370496
theorem cot_pi_2_7_bounds :
  ((cot_pi_2_7_lower : ℚ) : ℝ) ≤ cotangentTermV 2 7 ∧
  cotangentTermV 2 7 ≤ ((cot_pi_2_7_upper : ℚ) : ℝ) := by
  have h := cot_pi_div_2_7_mem_interval_v2
  constructor
  · norm_num [cot_pi_2_7_lower]; linarith [h.1]
  · norm_num [cot_pi_2_7_upper]; linarith [h.2]

def cot_pi_3_7_lower : ℚ := 513958613106613 / 2251799813685248
def cot_pi_3_7_upper : ℚ := 4111668904852911 / 18014398509481984
theorem cot_pi_3_7_bounds :
  ((cot_pi_3_7_lower : ℚ) : ℝ) ≤ cotangentTermV 3 7 ∧
  cotangentTermV 3 7 ≤ ((cot_pi_3_7_upper : ℚ) : ℝ) := by
  have h := cot_pi_div_3_7_mem_interval_v2
  constructor
  · norm_num [cot_pi_3_7_lower]; linarith [h.1]
  · norm_num [cot_pi_3_7_upper]; linarith [h.2]

def cot_pi_4_7_lower : ℚ := -8223337809705817 / 36028797018963968
def cot_pi_4_7_upper : ℚ := -8223337809705801 / 36028797018963968
theorem cot_pi_4_7_bounds :
  ((cot_pi_4_7_lower : ℚ) : ℝ) ≤ cotangentTermV 4 7 ∧
  cotangentTermV 4 7 ≤ ((cot_pi_4_7_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 4 7 = - cotangentTermV 3 7 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have h := cot_pi_div_3_7_mem_interval_v2
  rw [hobtuse]
  constructor
  · norm_num [cot_pi_4_7_lower]; linarith [h.2]
  · norm_num [cot_pi_4_7_upper]; linarith [h.1]

def cot_pi_5_7_lower : ℚ := -3591500857008683 / 4503599627370496
def cot_pi_5_7_upper : ℚ := -3591500857008677 / 4503599627370496
theorem cot_pi_5_7_bounds :
  ((cot_pi_5_7_lower : ℚ) : ℝ) ≤ cotangentTermV 5 7 ∧
  cotangentTermV 5 7 ≤ ((cot_pi_5_7_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 5 7 = - cotangentTermV 2 7 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have h := cot_pi_div_2_7_mem_interval_v2
  rw [hobtuse]
  constructor
  · norm_num [cot_pi_5_7_lower]; linarith [h.2]
  · norm_num [cot_pi_5_7_upper]; linarith [h.1]

def cot_pi_6_7_lower : ℚ := -2337955246957511 / 1125899906842624
def cot_pi_6_7_upper : ℚ := -1168977623478753 / 562949953421312
theorem cot_pi_6_7_bounds :
  ((cot_pi_6_7_lower : ℚ) : ℝ) ≤ cotangentTermV 6 7 ∧
  cotangentTermV 6 7 ≤ ((cot_pi_6_7_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 6 7 = - cotangentTermV 1 7 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have h := cot_pi_div_1_7_mem_interval_v2
  rw [hobtuse]
  constructor
  · norm_num [cot_pi_6_7_lower]; linarith [h.2]
  · norm_num [cot_pi_6_7_upper]; linarith [h.1]

def cot_pi_1_8_lower : ℚ := 5436325649948131 / 2251799813685248
def cot_pi_1_8_upper : ℚ := 5436325649948137 / 2251799813685248
theorem cot_pi_1_8_bounds :
  ((cot_pi_1_8_lower : ℚ) : ℝ) ≤ cotangentTermV 1 8 ∧
  cotangentTermV 1 8 ≤ ((cot_pi_1_8_upper : ℚ) : ℝ) := by
  have h := cot_pi_div_1_8_mem_interval_v2
  constructor
  · norm_num [cot_pi_1_8_lower]; linarith [h.1]
  · norm_num [cot_pi_1_8_upper]; linarith [h.2]

def cot_pi_2_8_lower : ℚ := 2251799813685247 / 2251799813685248
def cot_pi_2_8_upper : ℚ := 2251799813685249 / 2251799813685248
theorem cot_pi_2_8_bounds :
  ((cot_pi_2_8_lower : ℚ) : ℝ) ≤ cotangentTermV 2 8 ∧
  cotangentTermV 2 8 ≤ ((cot_pi_2_8_upper : ℚ) : ℝ) := by
  have hred : cotangentTermV 2 8 = cotangentTermV 1 4 :=
    cotangentTermV_gcd_reduce (g := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [hred]
  have h := cot_pi_div_1_4_mem_interval_v2
  constructor
  · norm_num [cot_pi_2_8_lower]; linarith [h.1]
  · norm_num [cot_pi_2_8_upper]; linarith [h.2]

def cot_pi_3_8_lower : ℚ := 7461808180621101 / 18014398509481984
def cot_pi_3_8_upper : ℚ := 7461808180621111 / 18014398509481984
theorem cot_pi_3_8_bounds :
  ((cot_pi_3_8_lower : ℚ) : ℝ) ≤ cotangentTermV 3 8 ∧
  cotangentTermV 3 8 ≤ ((cot_pi_3_8_upper : ℚ) : ℝ) := by
  have h := cot_pi_div_3_8_mem_interval_v2
  constructor
  · norm_num [cot_pi_3_8_lower]; linarith [h.1]
  · norm_num [cot_pi_3_8_upper]; linarith [h.2]

def cot_pi_4_8_lower : ℚ := -488112139 / 9671406556917033397649408
def cot_pi_4_8_upper : ℚ := 1671954449 / 9671406556917033397649408
theorem cot_pi_4_8_bounds :
  ((cot_pi_4_8_lower : ℚ) : ℝ) ≤ cotangentTermV 4 8 ∧
  cotangentTermV 4 8 ≤ ((cot_pi_4_8_upper : ℚ) : ℝ) := by
  have h0 : cotangentTermV 4 8 = 0 :=
    cotangentTermV_exact_of_two_mul_eq (by norm_num) (by norm_num)
  rw [h0]; constructor <;> norm_num [cot_pi_4_8_lower, cot_pi_4_8_upper]

def cot_pi_5_8_lower : ℚ := -3730904090310555 / 9007199254740992
def cot_pi_5_8_upper : ℚ := -3730904090310549 / 9007199254740992
theorem cot_pi_5_8_bounds :
  ((cot_pi_5_8_lower : ℚ) : ℝ) ≤ cotangentTermV 5 8 ∧
  cotangentTermV 5 8 ≤ ((cot_pi_5_8_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 5 8 = - cotangentTermV 3 8 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have h := cot_pi_div_3_8_mem_interval_v2
  rw [hobtuse]
  constructor
  · norm_num [cot_pi_5_8_lower]; linarith [h.2]
  · norm_num [cot_pi_5_8_upper]; linarith [h.1]

def cot_pi_6_8_lower : ℚ := -2251799813685249 / 2251799813685248
def cot_pi_6_8_upper : ℚ := -4503599627370491 / 4503599627370496
theorem cot_pi_6_8_bounds :
  ((cot_pi_6_8_lower : ℚ) : ℝ) ≤ cotangentTermV 6 8 ∧
  cotangentTermV 6 8 ≤ ((cot_pi_6_8_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 6 8 = - cotangentTermV 2 8 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have hred : cotangentTermV 2 8 = cotangentTermV 1 4 :=
    cotangentTermV_gcd_reduce (g := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [hobtuse, hred]
  have h := cot_pi_div_1_4_mem_interval_v2
  constructor
  · norm_num [cot_pi_6_8_lower]; linarith [h.2]
  · norm_num [cot_pi_6_8_upper]; linarith [h.1]

def cot_pi_7_8_lower : ℚ := -5436325649948137 / 2251799813685248
def cot_pi_7_8_upper : ℚ := -5436325649948127 / 2251799813685248
theorem cot_pi_7_8_bounds :
  ((cot_pi_7_8_lower : ℚ) : ℝ) ≤ cotangentTermV 7 8 ∧
  cotangentTermV 7 8 ≤ ((cot_pi_7_8_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 7 8 = - cotangentTermV 1 8 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have h := cot_pi_div_1_8_mem_interval_v2
  rw [hobtuse]
  constructor
  · norm_num [cot_pi_7_8_lower]; linarith [h.2]
  · norm_num [cot_pi_7_8_upper]; linarith [h.1]

def cot_pi_1_9_lower : ℚ := 1546692285308085 / 562949953421312
def cot_pi_1_9_upper : ℚ := 1546692285308087 / 562949953421312
theorem cot_pi_1_9_bounds :
  ((cot_pi_1_9_lower : ℚ) : ℝ) ≤ cotangentTermV 1 9 ∧
  cotangentTermV 1 9 ≤ ((cot_pi_1_9_upper : ℚ) : ℝ) := by
  have h := cot_pi_div_1_9_mem_interval_v2
  constructor
  · norm_num [cot_pi_1_9_lower]; linarith [h.1]
  · norm_num [cot_pi_1_9_upper]; linarith [h.2]

def cot_pi_2_9_lower : ℚ := 2683590517762365 / 2251799813685248
def cot_pi_2_9_upper : ℚ := 2683590517762369 / 2251799813685248
theorem cot_pi_2_9_bounds :
  ((cot_pi_2_9_lower : ℚ) : ℝ) ≤ cotangentTermV 2 9 ∧
  cotangentTermV 2 9 ≤ ((cot_pi_2_9_upper : ℚ) : ℝ) := by
  have h := cot_pi_div_2_9_mem_interval_v2
  constructor
  · norm_num [cot_pi_2_9_lower]; linarith [h.1]
  · norm_num [cot_pi_2_9_upper]; linarith [h.2]

def cot_pi_3_9_lower : ℚ := 5200308914369303 / 9007199254740992
def cot_pi_3_9_upper : ℚ := 5200308914369315 / 9007199254740992
theorem cot_pi_3_9_bounds :
  ((cot_pi_3_9_lower : ℚ) : ℝ) ≤ cotangentTermV 3 9 ∧
  cotangentTermV 3 9 ≤ ((cot_pi_3_9_upper : ℚ) : ℝ) := by
  have hred : cotangentTermV 3 9 = cotangentTermV 1 3 :=
    cotangentTermV_gcd_reduce (g := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [hred]
  have h := cot_pi_div_1_3_mem_interval_v2
  constructor
  · norm_num [cot_pi_3_9_lower]; linarith [h.1]
  · norm_num [cot_pi_3_9_upper]; linarith [h.2]

def cot_pi_4_9_lower : ℚ := 6352848996912047 / 36028797018963968
def cot_pi_4_9_upper : ℚ := 6352848996912077 / 36028797018963968
theorem cot_pi_4_9_bounds :
  ((cot_pi_4_9_lower : ℚ) : ℝ) ≤ cotangentTermV 4 9 ∧
  cotangentTermV 4 9 ≤ ((cot_pi_4_9_upper : ℚ) : ℝ) := by
  have h := cot_pi_div_4_9_mem_interval_v2
  constructor
  · norm_num [cot_pi_4_9_lower]; linarith [h.1]
  · norm_num [cot_pi_4_9_upper]; linarith [h.2]

def cot_pi_5_9_lower : ℚ := -3176424498456033 / 18014398509481984
def cot_pi_5_9_upper : ℚ := -3176424498456017 / 18014398509481984
theorem cot_pi_5_9_bounds :
  ((cot_pi_5_9_lower : ℚ) : ℝ) ≤ cotangentTermV 5 9 ∧
  cotangentTermV 5 9 ≤ ((cot_pi_5_9_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 5 9 = - cotangentTermV 4 9 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have h := cot_pi_div_4_9_mem_interval_v2
  rw [hobtuse]
  constructor
  · norm_num [cot_pi_5_9_lower]; linarith [h.2]
  · norm_num [cot_pi_5_9_upper]; linarith [h.1]

def cot_pi_6_9_lower : ℚ := -2600154457184657 / 4503599627370496
def cot_pi_6_9_upper : ℚ := -325019307148081 / 562949953421312
theorem cot_pi_6_9_bounds :
  ((cot_pi_6_9_lower : ℚ) : ℝ) ≤ cotangentTermV 6 9 ∧
  cotangentTermV 6 9 ≤ ((cot_pi_6_9_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 6 9 = - cotangentTermV 3 9 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have hred : cotangentTermV 3 9 = cotangentTermV 1 3 :=
    cotangentTermV_gcd_reduce (g := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [hobtuse, hred]
  have h := cot_pi_div_1_3_mem_interval_v2
  constructor
  · norm_num [cot_pi_6_9_lower]; linarith [h.2]
  · norm_num [cot_pi_6_9_upper]; linarith [h.1]

def cot_pi_7_9_lower : ℚ := -5367181035524741 / 4503599627370496
def cot_pi_7_9_upper : ℚ := -5367181035524721 / 4503599627370496
theorem cot_pi_7_9_bounds :
  ((cot_pi_7_9_lower : ℚ) : ℝ) ≤ cotangentTermV 7 9 ∧
  cotangentTermV 7 9 ≤ ((cot_pi_7_9_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 7 9 = - cotangentTermV 2 9 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have h := cot_pi_div_2_9_mem_interval_v2
  rw [hobtuse]
  constructor
  · norm_num [cot_pi_7_9_lower]; linarith [h.2]
  · norm_num [cot_pi_7_9_upper]; linarith [h.1]

def cot_pi_8_9_lower : ℚ := -1546692285308089 / 562949953421312
def cot_pi_8_9_upper : ℚ := -3093384570616163 / 1125899906842624
theorem cot_pi_8_9_bounds :
  ((cot_pi_8_9_lower : ℚ) : ℝ) ≤ cotangentTermV 8 9 ∧
  cotangentTermV 8 9 ≤ ((cot_pi_8_9_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 8 9 = - cotangentTermV 1 9 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have h := cot_pi_div_1_9_mem_interval_v2
  rw [hobtuse]
  constructor
  · norm_num [cot_pi_8_9_lower]; linarith [h.2]
  · norm_num [cot_pi_8_9_upper]; linarith [h.1]

def cot_pi_1_10_lower : ℚ := 3465163607796693 / 1125899906842624
def cot_pi_1_10_upper : ℚ := 3465163607796697 / 1125899906842624
theorem cot_pi_1_10_bounds :
  ((cot_pi_1_10_lower : ℚ) : ℝ) ≤ cotangentTermV 1 10 ∧
  cotangentTermV 1 10 ≤ ((cot_pi_1_10_upper : ℚ) : ℝ) := by
  have h := cot_pi_div_1_10_mem_interval_v2
  constructor
  · norm_num [cot_pi_1_10_lower]; linarith [h.1]
  · norm_num [cot_pi_1_10_upper]; linarith [h.2]

def cot_pi_2_10_lower : ℚ := 6198673104153461 / 4503599627370496
def cot_pi_2_10_upper : ℚ := 6198673104153469 / 4503599627370496
theorem cot_pi_2_10_bounds :
  ((cot_pi_2_10_lower : ℚ) : ℝ) ≤ cotangentTermV 2 10 ∧
  cotangentTermV 2 10 ≤ ((cot_pi_2_10_upper : ℚ) : ℝ) := by
  have hred : cotangentTermV 2 10 = cotangentTermV 1 5 :=
    cotangentTermV_gcd_reduce (g := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [hred]
  have h := cot_pi_div_1_5_mem_interval_v2
  constructor
  · norm_num [cot_pi_2_10_lower]; linarith [h.1]
  · norm_num [cot_pi_2_10_upper]; linarith [h.2]

def cot_pi_3_10_lower : ℚ := 6544113316787519 / 9007199254740992
def cot_pi_3_10_upper : ℚ := 6544113316787527 / 9007199254740992
theorem cot_pi_3_10_bounds :
  ((cot_pi_3_10_lower : ℚ) : ℝ) ≤ cotangentTermV 3 10 ∧
  cotangentTermV 3 10 ≤ ((cot_pi_3_10_upper : ℚ) : ℝ) := by
  have h := cot_pi_div_3_10_mem_interval_v2
  constructor
  · norm_num [cot_pi_3_10_lower]; linarith [h.1]
  · norm_num [cot_pi_3_10_upper]; linarith [h.2]

def cot_pi_4_10_lower : ℚ := 2926616445759701 / 9007199254740992
def cot_pi_4_10_upper : ℚ := 1463308222879853 / 4503599627370496
theorem cot_pi_4_10_bounds :
  ((cot_pi_4_10_lower : ℚ) : ℝ) ≤ cotangentTermV 4 10 ∧
  cotangentTermV 4 10 ≤ ((cot_pi_4_10_upper : ℚ) : ℝ) := by
  have hred : cotangentTermV 4 10 = cotangentTermV 2 5 :=
    cotangentTermV_gcd_reduce (g := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [hred]
  have h := cot_pi_div_2_5_mem_interval_v2
  constructor
  · norm_num [cot_pi_4_10_lower]; linarith [h.1]
  · norm_num [cot_pi_4_10_upper]; linarith [h.2]

def cot_pi_5_10_lower : ℚ := -488112139 / 9671406556917033397649408
def cot_pi_5_10_upper : ℚ := 1671954449 / 9671406556917033397649408
theorem cot_pi_5_10_bounds :
  ((cot_pi_5_10_lower : ℚ) : ℝ) ≤ cotangentTermV 5 10 ∧
  cotangentTermV 5 10 ≤ ((cot_pi_5_10_upper : ℚ) : ℝ) := by
  have h0 : cotangentTermV 5 10 = 0 :=
    cotangentTermV_exact_of_two_mul_eq (by norm_num) (by norm_num)
  rw [h0]; constructor <;> norm_num [cot_pi_5_10_lower, cot_pi_5_10_upper]

def cot_pi_6_10_lower : ℚ := -2926616445759705 / 9007199254740992
def cot_pi_6_10_upper : ℚ := -731654111439925 / 2251799813685248
theorem cot_pi_6_10_bounds :
  ((cot_pi_6_10_lower : ℚ) : ℝ) ≤ cotangentTermV 6 10 ∧
  cotangentTermV 6 10 ≤ ((cot_pi_6_10_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 6 10 = - cotangentTermV 4 10 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have hred : cotangentTermV 4 10 = cotangentTermV 2 5 :=
    cotangentTermV_gcd_reduce (g := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [hobtuse, hred]
  have h := cot_pi_div_2_5_mem_interval_v2
  constructor
  · norm_num [cot_pi_6_10_lower]; linarith [h.2]
  · norm_num [cot_pi_6_10_upper]; linarith [h.1]

def cot_pi_7_10_lower : ℚ := -3272056658393763 / 4503599627370496
def cot_pi_7_10_upper : ℚ := -1636028329196879 / 2251799813685248
theorem cot_pi_7_10_bounds :
  ((cot_pi_7_10_lower : ℚ) : ℝ) ≤ cotangentTermV 7 10 ∧
  cotangentTermV 7 10 ≤ ((cot_pi_7_10_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 7 10 = - cotangentTermV 3 10 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have h := cot_pi_div_3_10_mem_interval_v2
  rw [hobtuse]
  constructor
  · norm_num [cot_pi_7_10_lower]; linarith [h.2]
  · norm_num [cot_pi_7_10_upper]; linarith [h.1]

def cot_pi_8_10_lower : ℚ := -6198673104153469 / 4503599627370496
def cot_pi_8_10_upper : ℚ := -6198673104153459 / 4503599627370496
theorem cot_pi_8_10_bounds :
  ((cot_pi_8_10_lower : ℚ) : ℝ) ≤ cotangentTermV 8 10 ∧
  cotangentTermV 8 10 ≤ ((cot_pi_8_10_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 8 10 = - cotangentTermV 2 10 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have hred : cotangentTermV 2 10 = cotangentTermV 1 5 :=
    cotangentTermV_gcd_reduce (g := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [hobtuse, hred]
  have h := cot_pi_div_1_5_mem_interval_v2
  constructor
  · norm_num [cot_pi_8_10_lower]; linarith [h.2]
  · norm_num [cot_pi_8_10_upper]; linarith [h.1]

def cot_pi_9_10_lower : ℚ := -1732581803898349 / 562949953421312
def cot_pi_9_10_upper : ℚ := -1732581803898345 / 562949953421312
theorem cot_pi_9_10_bounds :
  ((cot_pi_9_10_lower : ℚ) : ℝ) ≤ cotangentTermV 9 10 ∧
  cotangentTermV 9 10 ≤ ((cot_pi_9_10_upper : ℚ) : ℝ) := by
  have hobtuse : cotangentTermV 9 10 = - cotangentTermV 1 10 :=
    cotangentTermV_obtuse_eq_neg (by norm_num) (by norm_num)
  have h := cot_pi_div_1_10_mem_interval_v2
  rw [hobtuse]
  constructor
  · norm_num [cot_pi_9_10_lower]; linarith [h.2]
  · norm_num [cot_pi_9_10_upper]; linarith [h.1]

def cot_pi_1_11_lower : ℚ := 7668925890001035 / 2251799813685248
def cot_pi_1_11_upper : ℚ := 7668925890001047 / 2251799813685248
axiom cot_pi_1_11_bounds :
  ((cot_pi_1_11_lower : ℚ) : ℝ) ≤ cotangentTermV 1 11 ∧
  cotangentTermV 1 11 ≤ ((cot_pi_1_11_upper : ℚ) : ℝ)

def cot_pi_2_11_lower : ℚ := 7007737807909369 / 4503599627370496
def cot_pi_2_11_upper : ℚ := 7007737807909381 / 4503599627370496
axiom cot_pi_2_11_bounds :
  ((cot_pi_2_11_lower : ℚ) : ℝ) ≤ cotangentTermV 2 11 ∧
  cotangentTermV 2 11 ≤ ((cot_pi_2_11_upper : ℚ) : ℝ)

def cot_pi_3_11_lower : ℚ := 7804782582631265 / 9007199254740992
def cot_pi_3_11_upper : ℚ := 7804782582631277 / 9007199254740992
axiom cot_pi_3_11_bounds :
  ((cot_pi_3_11_lower : ℚ) : ℝ) ≤ cotangentTermV 3 11 ∧
  cotangentTermV 3 11 ≤ ((cot_pi_3_11_upper : ℚ) : ℝ)

def cot_pi_4_11_lower : ℚ := 8226900141217031 / 18014398509481984
def cot_pi_4_11_upper : ℚ := 8226900141217051 / 18014398509481984
axiom cot_pi_4_11_bounds :
  ((cot_pi_4_11_lower : ℚ) : ℝ) ≤ cotangentTermV 4 11 ∧
  cotangentTermV 4 11 ≤ ((cot_pi_4_11_upper : ℚ) : ℝ)

def cot_pi_5_11_lower : ℚ := 5180158970077811 / 36028797018963968
def cot_pi_5_11_upper : ℚ := 5180158970077841 / 36028797018963968
axiom cot_pi_5_11_bounds :
  ((cot_pi_5_11_lower : ℚ) : ℝ) ≤ cotangentTermV 5 11 ∧
  cotangentTermV 5 11 ≤ ((cot_pi_5_11_upper : ℚ) : ℝ)

def cot_pi_6_11_lower : ℚ := -1295039742519457 / 9007199254740992
def cot_pi_6_11_upper : ℚ := -2590079485038899 / 18014398509481984
axiom cot_pi_6_11_bounds :
  ((cot_pi_6_11_lower : ℚ) : ℝ) ≤ cotangentTermV 6 11 ∧
  cotangentTermV 6 11 ≤ ((cot_pi_6_11_upper : ℚ) : ℝ)

def cot_pi_7_11_lower : ℚ := -8226900141217045 / 18014398509481984
def cot_pi_7_11_upper : ℚ := -8226900141217023 / 18014398509481984
axiom cot_pi_7_11_bounds :
  ((cot_pi_7_11_lower : ℚ) : ℝ) ≤ cotangentTermV 7 11 ∧
  cotangentTermV 7 11 ≤ ((cot_pi_7_11_upper : ℚ) : ℝ)

def cot_pi_8_11_lower : ℚ := -3902391291315637 / 4503599627370496
def cot_pi_8_11_upper : ℚ := -487798911414453 / 562949953421312
axiom cot_pi_8_11_bounds :
  ((cot_pi_8_11_lower : ℚ) : ℝ) ≤ cotangentTermV 8 11 ∧
  cotangentTermV 8 11 ≤ ((cot_pi_8_11_upper : ℚ) : ℝ)

def cot_pi_9_11_lower : ℚ := -7007737807909383 / 4503599627370496
def cot_pi_9_11_upper : ℚ := -7007737807909357 / 4503599627370496
axiom cot_pi_9_11_bounds :
  ((cot_pi_9_11_lower : ℚ) : ℝ) ≤ cotangentTermV 9 11 ∧
  cotangentTermV 9 11 ≤ ((cot_pi_9_11_upper : ℚ) : ℝ)

def cot_pi_10_11_lower : ℚ := -3834462945000525 / 1125899906842624
def cot_pi_10_11_upper : ℚ := -3834462945000503 / 1125899906842624
axiom cot_pi_10_11_bounds :
  ((cot_pi_10_11_lower : ℚ) : ℝ) ≤ cotangentTermV 10 11 ∧
  cotangentTermV 10 11 ≤ ((cot_pi_10_11_upper : ℚ) : ℝ)

def cot_pi_1_12_lower : ℚ := 8403831313147473 / 2251799813685248
def cot_pi_1_12_upper : ℚ := 8403831313147485 / 2251799813685248
axiom cot_pi_1_12_bounds :
  ((cot_pi_1_12_lower : ℚ) : ℝ) ≤ cotangentTermV 1 12 ∧
  cotangentTermV 1 12 ≤ ((cot_pi_1_12_upper : ℚ) : ℝ)

def cot_pi_2_12_lower : ℚ := 1950115842888489 / 1125899906842624
def cot_pi_2_12_upper : ℚ := 487528960722123 / 281474976710656
axiom cot_pi_2_12_bounds :
  ((cot_pi_2_12_lower : ℚ) : ℝ) ≤ cotangentTermV 2 12 ∧
  cotangentTermV 2 12 ≤ ((cot_pi_2_12_upper : ℚ) : ℝ)

def cot_pi_3_12_lower : ℚ := 2251799813685247 / 2251799813685248
def cot_pi_3_12_upper : ℚ := 2251799813685249 / 2251799813685248
axiom cot_pi_3_12_bounds :
  ((cot_pi_3_12_lower : ℚ) : ℝ) ≤ cotangentTermV 3 12 ∧
  cotangentTermV 3 12 ≤ ((cot_pi_3_12_upper : ℚ) : ℝ)

def cot_pi_4_12_lower : ℚ := 5200308914369303 / 9007199254740992
def cot_pi_4_12_upper : ℚ := 5200308914369315 / 9007199254740992
axiom cot_pi_4_12_bounds :
  ((cot_pi_4_12_lower : ℚ) : ℝ) ≤ cotangentTermV 4 12 ∧
  cotangentTermV 4 12 ≤ ((cot_pi_4_12_upper : ℚ) : ℝ)

def cot_pi_5_12_lower : ℚ := 301683970796757 / 1125899906842624
def cot_pi_5_12_upper : ℚ := 2413471766374065 / 9007199254740992
axiom cot_pi_5_12_bounds :
  ((cot_pi_5_12_lower : ℚ) : ℝ) ≤ cotangentTermV 5 12 ∧
  cotangentTermV 5 12 ≤ ((cot_pi_5_12_upper : ℚ) : ℝ)

def cot_pi_6_12_lower : ℚ := -488112137 / 9671406556917033397649408
def cot_pi_6_12_upper : ℚ := 1671954447 / 9671406556917033397649408
axiom cot_pi_6_12_bounds :
  ((cot_pi_6_12_lower : ℚ) : ℝ) ≤ cotangentTermV 6 12 ∧
  cotangentTermV 6 12 ≤ ((cot_pi_6_12_upper : ℚ) : ℝ)

def cot_pi_7_12_lower : ℚ := -4826943532748123 / 18014398509481984
def cot_pi_7_12_upper : ℚ := -4826943532748105 / 18014398509481984
axiom cot_pi_7_12_bounds :
  ((cot_pi_7_12_lower : ℚ) : ℝ) ≤ cotangentTermV 7 12 ∧
  cotangentTermV 7 12 ≤ ((cot_pi_7_12_upper : ℚ) : ℝ)

def cot_pi_8_12_lower : ℚ := -2600154457184657 / 4503599627370496
def cot_pi_8_12_upper : ℚ := -325019307148081 / 562949953421312
axiom cot_pi_8_12_bounds :
  ((cot_pi_8_12_lower : ℚ) : ℝ) ≤ cotangentTermV 8 12 ∧
  cotangentTermV 8 12 ≤ ((cot_pi_8_12_upper : ℚ) : ℝ)

def cot_pi_9_12_lower : ℚ := -2251799813685249 / 2251799813685248
def cot_pi_9_12_upper : ℚ := -4503599627370491 / 4503599627370496
axiom cot_pi_9_12_bounds :
  ((cot_pi_9_12_lower : ℚ) : ℝ) ≤ cotangentTermV 9 12 ∧
  cotangentTermV 9 12 ≤ ((cot_pi_9_12_upper : ℚ) : ℝ)

def cot_pi_10_12_lower : ℚ := -7800463371553969 / 4503599627370496
def cot_pi_10_12_upper : ℚ := -7800463371553939 / 4503599627370496
axiom cot_pi_10_12_bounds :
  ((cot_pi_10_12_lower : ℚ) : ℝ) ≤ cotangentTermV 10 12 ∧
  cotangentTermV 10 12 ≤ ((cot_pi_10_12_upper : ℚ) : ℝ)

def cot_pi_11_12_lower : ℚ := -2100957828286875 / 562949953421312
def cot_pi_11_12_upper : ℚ := -525239457071713 / 140737488355328
axiom cot_pi_11_12_bounds :
  ((cot_pi_11_12_lower : ℚ) : ℝ) ≤ cotangentTermV 11 12 ∧
  cotangentTermV 11 12 ≤ ((cot_pi_11_12_upper : ℚ) : ℝ)

def cot_pi_1_13_lower : ℚ := 4567955486925621 / 1125899906842624
def cot_pi_1_13_upper : ℚ := 4567955486925627 / 1125899906842624
axiom cot_pi_1_13_bounds :
  ((cot_pi_1_13_lower : ℚ) : ℝ) ≤ cotangentTermV 1 13 ∧
  cotangentTermV 1 13 ≤ ((cot_pi_1_13_upper : ℚ) : ℝ)

def cot_pi_2_13_lower : ℚ := 4290446083899149 / 2251799813685248
def cot_pi_2_13_upper : ℚ := 2145223041949577 / 1125899906842624
axiom cot_pi_2_13_bounds :
  ((cot_pi_2_13_lower : ℚ) : ℝ) ≤ cotangentTermV 2 13 ∧
  cotangentTermV 2 13 ≤ ((cot_pi_2_13_upper : ℚ) : ℝ)

def cot_pi_3_13_lower : ℚ := 5083513109760297 / 4503599627370496
def cot_pi_3_13_upper : ℚ := 5083513109760305 / 4503599627370496
axiom cot_pi_3_13_bounds :
  ((cot_pi_3_13_lower : ℚ) : ℝ) ≤ cotangentTermV 3 13 ∧
  cotangentTermV 3 13 ≤ ((cot_pi_3_13_upper : ℚ) : ℝ)

def cot_pi_4_13_lower : ℚ := 3108610372237027 / 4503599627370496
def cot_pi_4_13_upper : ℚ := 388576296529629 / 562949953421312
axiom cot_pi_4_13_bounds :
  ((cot_pi_4_13_lower : ℚ) : ℝ) ≤ cotangentTermV 4 13 ∧
  cotangentTermV 4 13 ≤ ((cot_pi_4_13_upper : ℚ) : ℝ)

def cot_pi_5_13_lower : ℚ := 6831960191672637 / 18014398509481984
def cot_pi_5_13_upper : ℚ := 6831960191672655 / 18014398509481984
axiom cot_pi_5_13_bounds :
  ((cot_pi_5_13_lower : ℚ) : ℝ) ≤ cotangentTermV 5 13 ∧
  cotangentTermV 5 13 ≤ ((cot_pi_5_13_upper : ℚ) : ℝ)

def cot_pi_6_13_lower : ℚ := 2187343993577433 / 18014398509481984
def cot_pi_6_13_upper : ℚ := 4374687987154893 / 36028797018963968
axiom cot_pi_6_13_bounds :
  ((cot_pi_6_13_lower : ℚ) : ℝ) ≤ cotangentTermV 6 13 ∧
  cotangentTermV 6 13 ≤ ((cot_pi_6_13_upper : ℚ) : ℝ)

def cot_pi_7_13_lower : ℚ := -8749375974309761 / 72057594037927936
def cot_pi_7_13_upper : ℚ := -8749375974309705 / 72057594037927936
axiom cot_pi_7_13_bounds :
  ((cot_pi_7_13_lower : ℚ) : ℝ) ≤ cotangentTermV 7 13 ∧
  cotangentTermV 7 13 ≤ ((cot_pi_7_13_upper : ℚ) : ℝ)

def cot_pi_8_13_lower : ℚ := -6831960191672649 / 18014398509481984
def cot_pi_8_13_upper : ℚ := -6831960191672629 / 18014398509481984
axiom cot_pi_8_13_bounds :
  ((cot_pi_8_13_lower : ℚ) : ℝ) ≤ cotangentTermV 8 13 ∧
  cotangentTermV 8 13 ≤ ((cot_pi_8_13_upper : ℚ) : ℝ)

def cot_pi_9_13_lower : ℚ := -3108610372237033 / 4503599627370496
def cot_pi_9_13_upper : ℚ := -1554305186118511 / 2251799813685248
axiom cot_pi_9_13_bounds :
  ((cot_pi_9_13_lower : ℚ) : ℝ) ≤ cotangentTermV 9 13 ∧
  cotangentTermV 9 13 ≤ ((cot_pi_9_13_upper : ℚ) : ℝ)

def cot_pi_10_13_lower : ℚ := -5083513109760305 / 4503599627370496
def cot_pi_10_13_upper : ℚ := -5083513109760287 / 4503599627370496
axiom cot_pi_10_13_bounds :
  ((cot_pi_10_13_lower : ℚ) : ℝ) ≤ cotangentTermV 10 13 ∧
  cotangentTermV 10 13 ≤ ((cot_pi_10_13_upper : ℚ) : ℝ)

def cot_pi_11_13_lower : ℚ := -4290446083899159 / 2251799813685248
def cot_pi_11_13_upper : ℚ := -4290446083899131 / 2251799813685248
axiom cot_pi_11_13_bounds :
  ((cot_pi_11_13_lower : ℚ) : ℝ) ≤ cotangentTermV 11 13 ∧
  cotangentTermV 11 13 ≤ ((cot_pi_11_13_upper : ℚ) : ℝ)

def cot_pi_12_13_lower : ℚ := -4567955486925631 / 1125899906842624
def cot_pi_12_13_upper : ℚ := -4567955486925601 / 1125899906842624
axiom cot_pi_12_13_bounds :
  ((cot_pi_12_13_lower : ℚ) : ℝ) ≤ cotangentTermV 12 13 ∧
  cotangentTermV 12 13 ≤ ((cot_pi_12_13_upper : ℚ) : ℝ)

def cot_pi_1_14_lower : ℚ := 4932889800468321 / 1125899906842624
def cot_pi_1_14_upper : ℚ := 4932889800468327 / 1125899906842624
axiom cot_pi_1_14_bounds :
  ((cot_pi_1_14_lower : ℚ) : ℝ) ≤ cotangentTermV 1 14 ∧
  cotangentTermV 1 14 ≤ ((cot_pi_1_14_upper : ℚ) : ℝ)

def cot_pi_2_14_lower : ℚ := 4675910493915015 / 2251799813685248
def cot_pi_2_14_upper : ℚ := 4675910493915021 / 2251799813685248
axiom cot_pi_2_14_bounds :
  ((cot_pi_2_14_lower : ℚ) : ℝ) ≤ cotangentTermV 2 14 ∧
  cotangentTermV 2 14 ≤ ((cot_pi_2_14_upper : ℚ) : ℝ)

def cot_pi_3_14_lower : ℚ := 5647335309435131 / 4503599627370496
def cot_pi_3_14_upper : ℚ := 5647335309435137 / 4503599627370496
axiom cot_pi_3_14_bounds :
  ((cot_pi_3_14_lower : ℚ) : ℝ) ≤ cotangentTermV 3 14 ∧
  cotangentTermV 3 14 ≤ ((cot_pi_3_14_upper : ℚ) : ℝ)

def cot_pi_4_14_lower : ℚ := 3591500857008679 / 4503599627370496
def cot_pi_4_14_upper : ℚ := 3591500857008683 / 4503599627370496
axiom cot_pi_4_14_bounds :
  ((cot_pi_4_14_lower : ℚ) : ℝ) ≤ cotangentTermV 4 14 ∧
  cotangentTermV 4 14 ≤ ((cot_pi_4_14_upper : ℚ) : ℝ)

def cot_pi_5_14_lower : ℚ := 4337638547625347 / 9007199254740992
def cot_pi_5_14_upper : ℚ := 542204818453169 / 1125899906842624
axiom cot_pi_5_14_bounds :
  ((cot_pi_5_14_lower : ℚ) : ℝ) ≤ cotangentTermV 5 14 ∧
  cotangentTermV 5 14 ≤ ((cot_pi_5_14_upper : ℚ) : ℝ)

def cot_pi_6_14_lower : ℚ := 513958613106613 / 2251799813685248
def cot_pi_6_14_upper : ℚ := 4111668904852911 / 18014398509481984
axiom cot_pi_6_14_bounds :
  ((cot_pi_6_14_lower : ℚ) : ℝ) ≤ cotangentTermV 6 14 ∧
  cotangentTermV 6 14 ≤ ((cot_pi_6_14_upper : ℚ) : ℝ)

def cot_pi_7_14_lower : ℚ := -488112137 / 9671406556917033397649408
def cot_pi_7_14_upper : ℚ := 1671954447 / 9671406556917033397649408
axiom cot_pi_7_14_bounds :
  ((cot_pi_7_14_lower : ℚ) : ℝ) ≤ cotangentTermV 7 14 ∧
  cotangentTermV 7 14 ≤ ((cot_pi_7_14_upper : ℚ) : ℝ)

def cot_pi_8_14_lower : ℚ := -8223337809705817 / 36028797018963968
def cot_pi_8_14_upper : ℚ := -8223337809705801 / 36028797018963968
axiom cot_pi_8_14_bounds :
  ((cot_pi_8_14_lower : ℚ) : ℝ) ≤ cotangentTermV 8 14 ∧
  cotangentTermV 8 14 ≤ ((cot_pi_8_14_upper : ℚ) : ℝ)

def cot_pi_9_14_lower : ℚ := -4337638547625351 / 9007199254740992
def cot_pi_9_14_upper : ℚ := -4337638547625345 / 9007199254740992
axiom cot_pi_9_14_bounds :
  ((cot_pi_9_14_lower : ℚ) : ℝ) ≤ cotangentTermV 9 14 ∧
  cotangentTermV 9 14 ≤ ((cot_pi_9_14_upper : ℚ) : ℝ)

def cot_pi_10_14_lower : ℚ := -3591500857008683 / 4503599627370496
def cot_pi_10_14_upper : ℚ := -3591500857008677 / 4503599627370496
axiom cot_pi_10_14_bounds :
  ((cot_pi_10_14_lower : ℚ) : ℝ) ≤ cotangentTermV 10 14 ∧
  cotangentTermV 10 14 ≤ ((cot_pi_10_14_upper : ℚ) : ℝ)

def cot_pi_11_14_lower : ℚ := -705916913679393 / 562949953421312
def cot_pi_11_14_upper : ℚ := -705916913679389 / 562949953421312
axiom cot_pi_11_14_bounds :
  ((cot_pi_11_14_lower : ℚ) : ℝ) ≤ cotangentTermV 11 14 ∧
  cotangentTermV 11 14 ≤ ((cot_pi_11_14_upper : ℚ) : ℝ)

def cot_pi_12_14_lower : ℚ := -2337955246957511 / 1125899906842624
def cot_pi_12_14_upper : ℚ := -1168977623478753 / 562949953421312
axiom cot_pi_12_14_bounds :
  ((cot_pi_12_14_lower : ℚ) : ℝ) ≤ cotangentTermV 12 14 ∧
  cotangentTermV 12 14 ≤ ((cot_pi_12_14_upper : ℚ) : ℝ)

def cot_pi_13_14_lower : ℚ := -4932889800468339 / 1125899906842624
def cot_pi_13_14_upper : ℚ := -4932889800468283 / 1125899906842624
axiom cot_pi_13_14_bounds :
  ((cot_pi_13_14_lower : ℚ) : ℝ) ≤ cotangentTermV 13 14 ∧
  cotangentTermV 13 14 ≤ ((cot_pi_13_14_upper : ℚ) : ℝ)

def cot_pi_1_15_lower : ℚ := 662117825248849 / 140737488355328
def cot_pi_1_15_upper : ℚ := 2648471300995399 / 562949953421312
axiom cot_pi_1_15_bounds :
  ((cot_pi_1_15_lower : ℚ) : ℝ) ≤ cotangentTermV 1 15 ∧
  cotangentTermV 1 15 ≤ ((cot_pi_1_15_upper : ℚ) : ℝ)

def cot_pi_2_15_lower : ℚ := 2528812594503863 / 1125899906842624
def cot_pi_2_15_upper : ℚ := 1264406297251933 / 562949953421312
axiom cot_pi_2_15_bounds :
  ((cot_pi_2_15_lower : ℚ) : ℝ) ≤ cotangentTermV 2 15 ∧
  cotangentTermV 2 15 ≤ ((cot_pi_2_15_upper : ℚ) : ℝ)

def cot_pi_3_15_lower : ℚ := 6198673104153461 / 4503599627370496
def cot_pi_3_15_upper : ℚ := 6198673104153469 / 4503599627370496
axiom cot_pi_3_15_bounds :
  ((cot_pi_3_15_lower : ℚ) : ℝ) ≤ cotangentTermV 3 15 ∧
  cotangentTermV 3 15 ≤ ((cot_pi_3_15_upper : ℚ) : ℝ)

def cot_pi_4_15_lower : ℚ := 4055059318382637 / 4503599627370496
def cot_pi_4_15_upper : ℚ := 4055059318382643 / 4503599627370496
axiom cot_pi_4_15_bounds :
  ((cot_pi_4_15_lower : ℚ) : ℝ) ≤ cotangentTermV 4 15 ∧
  cotangentTermV 4 15 ≤ ((cot_pi_4_15_upper : ℚ) : ℝ)

def cot_pi_5_15_lower : ℚ := 5200308914369303 / 9007199254740992
def cot_pi_5_15_upper : ℚ := 5200308914369315 / 9007199254740992
axiom cot_pi_5_15_bounds :
  ((cot_pi_5_15_lower : ℚ) : ℝ) ≤ cotangentTermV 5 15 ∧
  cotangentTermV 5 15 ≤ ((cot_pi_5_15_upper : ℚ) : ℝ)

def cot_pi_6_15_lower : ℚ := 2926616445759701 / 9007199254740992
def cot_pi_6_15_upper : ℚ := 1463308222879853 / 4503599627370496
axiom cot_pi_6_15_bounds :
  ((cot_pi_6_15_lower : ℚ) : ℝ) ≤ cotangentTermV 6 15 ∧
  cotangentTermV 6 15 ≤ ((cot_pi_6_15_upper : ℚ) : ℝ)

def cot_pi_7_15_lower : ℚ := 3786779158220485 / 36028797018963968
def cot_pi_7_15_upper : ℚ := 118336848694391 / 1125899906842624
axiom cot_pi_7_15_bounds :
  ((cot_pi_7_15_lower : ℚ) : ℝ) ≤ cotangentTermV 7 15 ∧
  cotangentTermV 7 15 ≤ ((cot_pi_7_15_upper : ℚ) : ℝ)

def cot_pi_8_15_lower : ℚ := -7573558316441001 / 72057594037927936
def cot_pi_8_15_upper : ℚ := -7573558316440945 / 72057594037927936
axiom cot_pi_8_15_bounds :
  ((cot_pi_8_15_lower : ℚ) : ℝ) ≤ cotangentTermV 8 15 ∧
  cotangentTermV 8 15 ≤ ((cot_pi_8_15_upper : ℚ) : ℝ)

def cot_pi_9_15_lower : ℚ := -2926616445759705 / 9007199254740992
def cot_pi_9_15_upper : ℚ := -731654111439925 / 2251799813685248
axiom cot_pi_9_15_bounds :
  ((cot_pi_9_15_lower : ℚ) : ℝ) ≤ cotangentTermV 9 15 ∧
  cotangentTermV 9 15 ≤ ((cot_pi_9_15_upper : ℚ) : ℝ)

def cot_pi_10_15_lower : ℚ := -2600154457184657 / 4503599627370496
def cot_pi_10_15_upper : ℚ := -325019307148081 / 562949953421312
axiom cot_pi_10_15_bounds :
  ((cot_pi_10_15_lower : ℚ) : ℝ) ≤ cotangentTermV 10 15 ∧
  cotangentTermV 10 15 ≤ ((cot_pi_10_15_upper : ℚ) : ℝ)

def cot_pi_11_15_lower : ℚ := -8110118636765293 / 9007199254740992
def cot_pi_11_15_upper : ℚ := -8110118636765251 / 9007199254740992
axiom cot_pi_11_15_bounds :
  ((cot_pi_11_15_lower : ℚ) : ℝ) ≤ cotangentTermV 11 15 ∧
  cotangentTermV 11 15 ≤ ((cot_pi_11_15_upper : ℚ) : ℝ)

def cot_pi_12_15_lower : ℚ := -6198673104153469 / 4503599627370496
def cot_pi_12_15_upper : ℚ := -6198673104153459 / 4503599627370496
axiom cot_pi_12_15_bounds :
  ((cot_pi_12_15_lower : ℚ) : ℝ) ≤ cotangentTermV 12 15 ∧
  cotangentTermV 12 15 ≤ ((cot_pi_12_15_upper : ℚ) : ℝ)

def cot_pi_13_15_lower : ℚ := -5057625189007737 / 2251799813685248
def cot_pi_13_15_upper : ℚ := -5057625189007701 / 2251799813685248
axiom cot_pi_13_15_bounds :
  ((cot_pi_13_15_lower : ℚ) : ℝ) ≤ cotangentTermV 13 15 ∧
  cotangentTermV 13 15 ≤ ((cot_pi_13_15_upper : ℚ) : ℝ)

def cot_pi_14_15_lower : ℚ := -5296942601990803 / 1125899906842624
def cot_pi_14_15_upper : ℚ := -5296942601990765 / 1125899906842624
axiom cot_pi_14_15_bounds :
  ((cot_pi_14_15_lower : ℚ) : ℝ) ≤ cotangentTermV 14 15 ∧
  cotangentTermV 14 15 ≤ ((cot_pi_14_15_upper : ℚ) : ℝ)

def cot_pi_1_16_lower : ℚ := 2830140532925367 / 562949953421312
def cot_pi_1_16_upper : ℚ := 1415070266462685 / 281474976710656
axiom cot_pi_1_16_bounds :
  ((cot_pi_1_16_lower : ℚ) : ℝ) ≤ cotangentTermV 1 16 ∧
  cotangentTermV 1 16 ≤ ((cot_pi_1_16_upper : ℚ) : ℝ)

def cot_pi_2_16_lower : ℚ := 5436325649948131 / 2251799813685248
def cot_pi_2_16_upper : ℚ := 5436325649948137 / 2251799813685248
axiom cot_pi_2_16_bounds :
  ((cot_pi_2_16_lower : ℚ) : ℝ) ≤ cotangentTermV 2 16 ∧
  cotangentTermV 2 16 ≤ ((cot_pi_2_16_upper : ℚ) : ℝ)

def cot_pi_3_16_lower : ℚ := 6740113155060829 / 4503599627370496
def cot_pi_3_16_upper : ℚ := 6740113155060837 / 4503599627370496
axiom cot_pi_3_16_bounds :
  ((cot_pi_3_16_lower : ℚ) : ℝ) ≤ cotangentTermV 3 16 ∧
  cotangentTermV 3 16 ≤ ((cot_pi_3_16_upper : ℚ) : ℝ)

def cot_pi_4_16_lower : ℚ := 2251799813685247 / 2251799813685248
def cot_pi_4_16_upper : ℚ := 2251799813685249 / 2251799813685248
axiom cot_pi_4_16_bounds :
  ((cot_pi_4_16_lower : ℚ) : ℝ) ≤ cotangentTermV 4 16 ∧
  cotangentTermV 4 16 ≤ ((cot_pi_4_16_upper : ℚ) : ℝ)

def cot_pi_5_16_lower : ℚ := 1504604532375139 / 2251799813685248
def cot_pi_5_16_upper : ℚ := 1504604532375141 / 2251799813685248
axiom cot_pi_5_16_bounds :
  ((cot_pi_5_16_lower : ℚ) : ℝ) ≤ cotangentTermV 5 16 ∧
  cotangentTermV 5 16 ≤ ((cot_pi_5_16_upper : ℚ) : ℝ)

def cot_pi_6_16_lower : ℚ := 7461808180621101 / 18014398509481984
def cot_pi_6_16_upper : ℚ := 7461808180621111 / 18014398509481984
axiom cot_pi_6_16_bounds :
  ((cot_pi_6_16_lower : ℚ) : ℝ) ≤ cotangentTermV 6 16 ∧
  cotangentTermV 6 16 ≤ ((cot_pi_6_16_upper : ℚ) : ℝ)

def cot_pi_7_16_lower : ℚ := 3583286654441641 / 18014398509481984
def cot_pi_7_16_upper : ℚ := 223955415902603 / 1125899906842624
axiom cot_pi_7_16_bounds :
  ((cot_pi_7_16_lower : ℚ) : ℝ) ≤ cotangentTermV 7 16 ∧
  cotangentTermV 7 16 ≤ ((cot_pi_7_16_upper : ℚ) : ℝ)

def cot_pi_8_16_lower : ℚ := -488112139 / 9671406556917033397649408
def cot_pi_8_16_upper : ℚ := 1671954449 / 9671406556917033397649408
axiom cot_pi_8_16_bounds :
  ((cot_pi_8_16_lower : ℚ) : ℝ) ≤ cotangentTermV 8 16 ∧
  cotangentTermV 8 16 ≤ ((cot_pi_8_16_upper : ℚ) : ℝ)

def cot_pi_9_16_lower : ℚ := -7166573308883293 / 36028797018963968
def cot_pi_9_16_upper : ℚ := -7166573308883277 / 36028797018963968
axiom cot_pi_9_16_bounds :
  ((cot_pi_9_16_lower : ℚ) : ℝ) ≤ cotangentTermV 9 16 ∧
  cotangentTermV 9 16 ≤ ((cot_pi_9_16_upper : ℚ) : ℝ)

def cot_pi_10_16_lower : ℚ := -3730904090310555 / 9007199254740992
def cot_pi_10_16_upper : ℚ := -3730904090310549 / 9007199254740992
axiom cot_pi_10_16_bounds :
  ((cot_pi_10_16_lower : ℚ) : ℝ) ≤ cotangentTermV 10 16 ∧
  cotangentTermV 10 16 ≤ ((cot_pi_10_16_upper : ℚ) : ℝ)

def cot_pi_11_16_lower : ℚ := -6018418129500567 / 9007199254740992
def cot_pi_11_16_upper : ℚ := -6018418129500545 / 9007199254740992
axiom cot_pi_11_16_bounds :
  ((cot_pi_11_16_lower : ℚ) : ℝ) ≤ cotangentTermV 11 16 ∧
  cotangentTermV 11 16 ≤ ((cot_pi_11_16_upper : ℚ) : ℝ)

def cot_pi_12_16_lower : ℚ := -2251799813685249 / 2251799813685248
def cot_pi_12_16_upper : ℚ := -4503599627370491 / 4503599627370496
axiom cot_pi_12_16_bounds :
  ((cot_pi_12_16_lower : ℚ) : ℝ) ≤ cotangentTermV 12 16 ∧
  cotangentTermV 12 16 ≤ ((cot_pi_12_16_upper : ℚ) : ℝ)

def cot_pi_13_16_lower : ℚ := -3370056577530421 / 2251799813685248
def cot_pi_13_16_upper : ℚ := -421257072191301 / 281474976710656
axiom cot_pi_13_16_bounds :
  ((cot_pi_13_16_lower : ℚ) : ℝ) ≤ cotangentTermV 13 16 ∧
  cotangentTermV 13 16 ≤ ((cot_pi_13_16_upper : ℚ) : ℝ)

def cot_pi_14_16_lower : ℚ := -5436325649948137 / 2251799813685248
def cot_pi_14_16_upper : ℚ := -5436325649948127 / 2251799813685248
axiom cot_pi_14_16_bounds :
  ((cot_pi_14_16_lower : ℚ) : ℝ) ≤ cotangentTermV 14 16 ∧
  cotangentTermV 14 16 ≤ ((cot_pi_14_16_upper : ℚ) : ℝ)

def cot_pi_15_16_lower : ℚ := -5660281065850749 / 1125899906842624
def cot_pi_15_16_upper : ℚ := -5660281065850705 / 1125899906842624
axiom cot_pi_15_16_bounds :
  ((cot_pi_15_16_lower : ℚ) : ℝ) ≤ cotangentTermV 15 16 ∧
  cotangentTermV 15 16 ≤ ((cot_pi_15_16_upper : ℚ) : ℝ)

def cot_pi_1_17_lower : ℚ := 6023032520105509 / 1125899906842624
def cot_pi_1_17_upper : ℚ := 6023032520105517 / 1125899906842624
axiom cot_pi_1_17_bounds :
  ((cot_pi_1_17_lower : ℚ) : ℝ) ≤ cotangentTermV 1 17 ∧
  cotangentTermV 1 17 ≤ ((cot_pi_1_17_upper : ℚ) : ℝ)

def cot_pi_2_17_lower : ℚ := 5812565351615769 / 2251799813685248
def cot_pi_2_17_upper : ℚ := 5812565351615777 / 2251799813685248
axiom cot_pi_2_17_bounds :
  ((cot_pi_2_17_lower : ℚ) : ℝ) ≤ cotangentTermV 2 17 ∧
  cotangentTermV 2 17 ≤ ((cot_pi_2_17_upper : ℚ) : ℝ)

def cot_pi_3_17_lower : ℚ := 7273563140077287 / 4503599627370496
def cot_pi_3_17_upper : ℚ := 7273563140077299 / 4503599627370496
axiom cot_pi_3_17_bounds :
  ((cot_pi_3_17_lower : ℚ) : ℝ) ≤ cotangentTermV 3 17 ∧
  cotangentTermV 3 17 ≤ ((cot_pi_3_17_upper : ℚ) : ℝ)

def cot_pi_4_17_lower : ℚ := 2470106728168569 / 2251799813685248
def cot_pi_4_17_upper : ℚ := 2470106728168573 / 2251799813685248
axiom cot_pi_4_17_bounds :
  ((cot_pi_4_17_lower : ℚ) : ℝ) ≤ cotangentTermV 4 17 ∧
  cotangentTermV 4 17 ≤ ((cot_pi_4_17_upper : ℚ) : ℝ)

def cot_pi_5_17_lower : ℚ := 6801921139191367 / 9007199254740992
def cot_pi_5_17_upper : ℚ := 6801921139191379 / 9007199254740992
axiom cot_pi_5_17_bounds :
  ((cot_pi_5_17_lower : ℚ) : ℝ) ≤ cotangentTermV 5 17 ∧
  cotangentTermV 5 17 ≤ ((cot_pi_5_17_upper : ℚ) : ℝ)

def cot_pi_6_17_lower : ℚ := 8970104616069279 / 18014398509481984
def cot_pi_6_17_upper : ℚ := 8970104616069299 / 18014398509481984
axiom cot_pi_6_17_bounds :
  ((cot_pi_6_17_lower : ℚ) : ℝ) ≤ cotangentTermV 6 17 ∧
  cotangentTermV 6 17 ≤ ((cot_pi_6_17_upper : ℚ) : ℝ)

def cot_pi_7_17_lower : ℚ := 5125538287992095 / 18014398509481984
def cot_pi_7_17_upper : ℚ := 5125538287992113 / 18014398509481984
axiom cot_pi_7_17_bounds :
  ((cot_pi_7_17_lower : ℚ) : ℝ) ≤ cotangentTermV 7 17 ∧
  cotangentTermV 7 17 ≤ ((cot_pi_7_17_upper : ℚ) : ℝ)

def cot_pi_8_17_lower : ℚ := 3338559701491169 / 36028797018963968
def cot_pi_8_17_upper : ℚ := 834639925372799 / 9007199254740992
axiom cot_pi_8_17_bounds :
  ((cot_pi_8_17_lower : ℚ) : ℝ) ≤ cotangentTermV 8 17 ∧
  cotangentTermV 8 17 ≤ ((cot_pi_8_17_upper : ℚ) : ℝ)

def cot_pi_9_17_lower : ℚ := -6677119402982369 / 72057594037927936
def cot_pi_9_17_upper : ℚ := -6677119402982313 / 72057594037927936
axiom cot_pi_9_17_bounds :
  ((cot_pi_9_17_lower : ℚ) : ℝ) ≤ cotangentTermV 9 17 ∧
  cotangentTermV 9 17 ≤ ((cot_pi_9_17_upper : ℚ) : ℝ)

def cot_pi_10_17_lower : ℚ := -5125538287992107 / 18014398509481984
def cot_pi_10_17_upper : ℚ := -5125538287992087 / 18014398509481984
axiom cot_pi_10_17_bounds :
  ((cot_pi_10_17_lower : ℚ) : ℝ) ≤ cotangentTermV 10 17 ∧
  cotangentTermV 10 17 ≤ ((cot_pi_10_17_upper : ℚ) : ℝ)

def cot_pi_11_17_lower : ℚ := -8970104616069303 / 18014398509481984
def cot_pi_11_17_upper : ℚ := -8970104616069251 / 18014398509481984
axiom cot_pi_11_17_bounds :
  ((cot_pi_11_17_lower : ℚ) : ℝ) ≤ cotangentTermV 11 17 ∧
  cotangentTermV 11 17 ≤ ((cot_pi_11_17_upper : ℚ) : ℝ)

def cot_pi_12_17_lower : ℚ := -6801921139191381 / 9007199254740992
def cot_pi_12_17_upper : ℚ := -6801921139191357 / 9007199254740992
axiom cot_pi_12_17_bounds :
  ((cot_pi_12_17_lower : ℚ) : ℝ) ≤ cotangentTermV 12 17 ∧
  cotangentTermV 12 17 ≤ ((cot_pi_12_17_upper : ℚ) : ℝ)

def cot_pi_13_17_lower : ℚ := -1235053364084287 / 1125899906842624
def cot_pi_13_17_upper : ℚ := -2470106728168561 / 2251799813685248
axiom cot_pi_13_17_bounds :
  ((cot_pi_13_17_lower : ℚ) : ℝ) ≤ cotangentTermV 13 17 ∧
  cotangentTermV 13 17 ≤ ((cot_pi_13_17_upper : ℚ) : ℝ)

def cot_pi_14_17_lower : ℚ := -1818390785019325 / 1125899906842624
def cot_pi_14_17_upper : ℚ := -909195392509659 / 562949953421312
axiom cot_pi_14_17_bounds :
  ((cot_pi_14_17_lower : ℚ) : ℝ) ≤ cotangentTermV 14 17 ∧
  cotangentTermV 14 17 ≤ ((cot_pi_14_17_upper : ℚ) : ℝ)

def cot_pi_15_17_lower : ℚ := -2906282675807893 / 1125899906842624
def cot_pi_15_17_upper : ℚ := -22705333404749 / 8796093022208
axiom cot_pi_15_17_bounds :
  ((cot_pi_15_17_lower : ℚ) : ℝ) ≤ cotangentTermV 15 17 ∧
  cotangentTermV 15 17 ≤ ((cot_pi_15_17_upper : ℚ) : ℝ)

def cot_pi_16_17_lower : ℚ := -6023032520105521 / 1125899906842624
def cot_pi_16_17_upper : ℚ := -6023032520105471 / 1125899906842624
axiom cot_pi_16_17_bounds :
  ((cot_pi_16_17_lower : ℚ) : ℝ) ≤ cotangentTermV 16 17 ∧
  cotangentTermV 16 17 ≤ ((cot_pi_16_17_upper : ℚ) : ℝ)

def cot_pi_1_18_lower : ℚ := 3192647836192921 / 562949953421312
def cot_pi_1_18_upper : ℚ := 3192647836192925 / 562949953421312
axiom cot_pi_1_18_bounds :
  ((cot_pi_1_18_lower : ℚ) : ℝ) ≤ cotangentTermV 1 18 ∧
  cotangentTermV 1 18 ≤ ((cot_pi_1_18_upper : ℚ) : ℝ)

def cot_pi_2_18_lower : ℚ := 1546692285308085 / 562949953421312
def cot_pi_2_18_upper : ℚ := 1546692285308087 / 562949953421312
axiom cot_pi_2_18_bounds :
  ((cot_pi_2_18_lower : ℚ) : ℝ) ≤ cotangentTermV 2 18 ∧
  cotangentTermV 2 18 ≤ ((cot_pi_2_18_upper : ℚ) : ℝ)

def cot_pi_3_18_lower : ℚ := 1950115842888489 / 1125899906842624
def cot_pi_3_18_upper : ℚ := 487528960722123 / 281474976710656
axiom cot_pi_3_18_bounds :
  ((cot_pi_3_18_lower : ℚ) : ℝ) ≤ cotangentTermV 3 18 ∧
  cotangentTermV 3 18 ≤ ((cot_pi_3_18_upper : ℚ) : ℝ)

def cot_pi_4_18_lower : ℚ := 2683590517762365 / 2251799813685248
def cot_pi_4_18_upper : ℚ := 2683590517762369 / 2251799813685248
axiom cot_pi_4_18_bounds :
  ((cot_pi_4_18_lower : ℚ) : ℝ) ≤ cotangentTermV 4 18 ∧
  cotangentTermV 4 18 ≤ ((cot_pi_4_18_upper : ℚ) : ℝ)

def cot_pi_5_18_lower : ℚ := 7557937572593433 / 9007199254740992
def cot_pi_5_18_upper : ℚ := 7557937572593445 / 9007199254740992
axiom cot_pi_5_18_bounds :
  ((cot_pi_5_18_lower : ℚ) : ℝ) ≤ cotangentTermV 5 18 ∧
  cotangentTermV 5 18 ≤ ((cot_pi_5_18_upper : ℚ) : ℝ)

def cot_pi_6_18_lower : ℚ := 5200308914369303 / 9007199254740992
def cot_pi_6_18_upper : ℚ := 5200308914369315 / 9007199254740992
axiom cot_pi_6_18_bounds :
  ((cot_pi_6_18_lower : ℚ) : ℝ) ≤ cotangentTermV 6 18 ∧
  cotangentTermV 6 18 ≤ ((cot_pi_6_18_upper : ℚ) : ℝ)

def cot_pi_7_18_lower : ℚ := 6556704845660877 / 18014398509481984
def cot_pi_7_18_upper : ℚ := 6556704845660895 / 18014398509481984
axiom cot_pi_7_18_bounds :
  ((cot_pi_7_18_lower : ℚ) : ℝ) ≤ cotangentTermV 7 18 ∧
  cotangentTermV 7 18 ≤ ((cot_pi_7_18_upper : ℚ) : ℝ)

def cot_pi_8_18_lower : ℚ := 6352848996912047 / 36028797018963968
def cot_pi_8_18_upper : ℚ := 6352848996912077 / 36028797018963968
axiom cot_pi_8_18_bounds :
  ((cot_pi_8_18_lower : ℚ) : ℝ) ≤ cotangentTermV 8 18 ∧
  cotangentTermV 8 18 ≤ ((cot_pi_8_18_upper : ℚ) : ℝ)

def cot_pi_9_18_lower : ℚ := -488112139 / 9671406556917033397649408
def cot_pi_9_18_upper : ℚ := 1671954449 / 9671406556917033397649408
axiom cot_pi_9_18_bounds :
  ((cot_pi_9_18_lower : ℚ) : ℝ) ≤ cotangentTermV 9 18 ∧
  cotangentTermV 9 18 ≤ ((cot_pi_9_18_upper : ℚ) : ℝ)

def cot_pi_10_18_lower : ℚ := -3176424498456033 / 18014398509481984
def cot_pi_10_18_upper : ℚ := -3176424498456017 / 18014398509481984
axiom cot_pi_10_18_bounds :
  ((cot_pi_10_18_lower : ℚ) : ℝ) ≤ cotangentTermV 10 18 ∧
  cotangentTermV 10 18 ≤ ((cot_pi_10_18_upper : ℚ) : ℝ)

def cot_pi_11_18_lower : ℚ := -1639176211415223 / 4503599627370496
def cot_pi_11_18_upper : ℚ := -819588105707607 / 2251799813685248
axiom cot_pi_11_18_bounds :
  ((cot_pi_11_18_lower : ℚ) : ℝ) ≤ cotangentTermV 11 18 ∧
  cotangentTermV 11 18 ≤ ((cot_pi_11_18_upper : ℚ) : ℝ)

def cot_pi_12_18_lower : ℚ := -2600154457184657 / 4503599627370496
def cot_pi_12_18_upper : ℚ := -325019307148081 / 562949953421312
axiom cot_pi_12_18_bounds :
  ((cot_pi_12_18_lower : ℚ) : ℝ) ≤ cotangentTermV 12 18 ∧
  cotangentTermV 12 18 ≤ ((cot_pi_12_18_upper : ℚ) : ℝ)

def cot_pi_13_18_lower : ℚ := -3778968786296725 / 4503599627370496
def cot_pi_13_18_upper : ℚ := -1889484393148353 / 2251799813685248
axiom cot_pi_13_18_bounds :
  ((cot_pi_13_18_lower : ℚ) : ℝ) ≤ cotangentTermV 13 18 ∧
  cotangentTermV 13 18 ≤ ((cot_pi_13_18_upper : ℚ) : ℝ)

def cot_pi_14_18_lower : ℚ := -5367181035524741 / 4503599627370496
def cot_pi_14_18_upper : ℚ := -5367181035524721 / 4503599627370496
axiom cot_pi_14_18_bounds :
  ((cot_pi_14_18_lower : ℚ) : ℝ) ≤ cotangentTermV 14 18 ∧
  cotangentTermV 14 18 ≤ ((cot_pi_14_18_upper : ℚ) : ℝ)

def cot_pi_15_18_lower : ℚ := -975057921444247 / 562949953421312
def cot_pi_15_18_upper : ℚ := -1950115842888483 / 1125899906842624
axiom cot_pi_15_18_bounds :
  ((cot_pi_15_18_lower : ℚ) : ℝ) ≤ cotangentTermV 15 18 ∧
  cotangentTermV 15 18 ≤ ((cot_pi_15_18_upper : ℚ) : ℝ)

def cot_pi_16_18_lower : ℚ := -1546692285308089 / 562949953421312
def cot_pi_16_18_upper : ℚ := -3093384570616163 / 1125899906842624
axiom cot_pi_16_18_bounds :
  ((cot_pi_16_18_lower : ℚ) : ℝ) ≤ cotangentTermV 16 18 ∧
  cotangentTermV 16 18 ≤ ((cot_pi_16_18_upper : ℚ) : ℝ)

def cot_pi_17_18_lower : ℚ := -3192647836192937 / 562949953421312
def cot_pi_17_18_upper : ℚ := -3192647836192895 / 562949953421312
axiom cot_pi_17_18_bounds :
  ((cot_pi_17_18_lower : ℚ) : ℝ) ≤ cotangentTermV 17 18 ∧
  cotangentTermV 17 18 ≤ ((cot_pi_17_18_upper : ℚ) : ℝ)

def cot_pi_1_19_lower : ℚ := 105424191201407 / 17592186044416
def cot_pi_1_19_upper : ℚ := 3373574118445029 / 562949953421312
axiom cot_pi_1_19_bounds :
  ((cot_pi_1_19_lower : ℚ) : ℝ) ≤ cotangentTermV 1 19 ∧
  cotangentTermV 1 19 ≤ ((cot_pi_1_19_upper : ℚ) : ℝ)

def cot_pi_2_19_lower : ℚ := 6559268772007781 / 2251799813685248
def cot_pi_2_19_upper : ℚ := 6559268772007791 / 2251799813685248
axiom cot_pi_2_19_bounds :
  ((cot_pi_2_19_lower : ℚ) : ℝ) ≤ cotangentTermV 2 19 ∧
  cotangentTermV 2 19 ≤ ((cot_pi_2_19_upper : ℚ) : ℝ)

def cot_pi_3_19_lower : ℚ := 4160961606430263 / 2251799813685248
def cot_pi_3_19_upper : ℚ := 1040240401607567 / 562949953421312
axiom cot_pi_3_19_bounds :
  ((cot_pi_3_19_lower : ℚ) : ℝ) ≤ cotangentTermV 3 19 ∧
  cotangentTermV 3 19 ≤ ((cot_pi_3_19_upper : ℚ) : ℝ)

def cot_pi_4_19_lower : ℚ := 2893112459767835 / 2251799813685248
def cot_pi_4_19_upper : ℚ := 90409764367745 / 70368744177664
axiom cot_pi_4_19_bounds :
  ((cot_pi_4_19_lower : ℚ) : ℝ) ≤ cotangentTermV 4 19 ∧
  cotangentTermV 4 19 ≤ ((cot_pi_4_19_upper : ℚ) : ℝ)

def cot_pi_5_19_lower : ℚ := 2072927758191169 / 2251799813685248
def cot_pi_5_19_upper : ℚ := 4145855516382345 / 4503599627370496
axiom cot_pi_5_19_bounds :
  ((cot_pi_5_19_lower : ℚ) : ℝ) ≤ cotangentTermV 5 19 ∧
  cotangentTermV 5 19 ≤ ((cot_pi_5_19_upper : ℚ) : ℝ)

def cot_pi_6_19_lower : ℚ := 5884696975023141 / 9007199254740992
def cot_pi_6_19_upper : ℚ := 5884696975023151 / 9007199254740992
axiom cot_pi_6_19_bounds :
  ((cot_pi_6_19_lower : ℚ) : ℝ) ≤ cotangentTermV 6 19 ∧
  cotangentTermV 6 19 ≤ ((cot_pi_6_19_upper : ℚ) : ℝ)

def cot_pi_7_19_lower : ℚ := 7901847813765667 / 18014398509481984
def cot_pi_7_19_upper : ℚ := 7901847813765687 / 18014398509481984
axiom cot_pi_7_19_bounds :
  ((cot_pi_7_19_lower : ℚ) : ℝ) ≤ cotangentTermV 7 19 ∧
  cotangentTermV 7 19 ≤ ((cot_pi_7_19_upper : ℚ) : ℝ)

def cot_pi_8_19_lower : ℚ := 2280932628671999 / 9007199254740992
def cot_pi_8_19_upper : ℚ := 2280932628672007 / 9007199254740992
axiom cot_pi_8_19_bounds :
  ((cot_pi_8_19_lower : ℚ) : ℝ) ≤ cotangentTermV 8 19 ∧
  cotangentTermV 8 19 ≤ ((cot_pi_8_19_upper : ℚ) : ℝ)

def cot_pi_9_19_lower : ℚ := 2985431237250487 / 36028797018963968
def cot_pi_9_19_upper : ℚ := 1492715618625257 / 18014398509481984
axiom cot_pi_9_19_bounds :
  ((cot_pi_9_19_lower : ℚ) : ℝ) ≤ cotangentTermV 9 19 ∧
  cotangentTermV 9 19 ≤ ((cot_pi_9_19_upper : ℚ) : ℝ)

def cot_pi_10_19_lower : ℚ := -2985431237250501 / 36028797018963968
def cot_pi_10_19_upper : ℚ := -1492715618625237 / 18014398509481984
axiom cot_pi_10_19_bounds :
  ((cot_pi_10_19_lower : ℚ) : ℝ) ≤ cotangentTermV 10 19 ∧
  cotangentTermV 10 19 ≤ ((cot_pi_10_19_upper : ℚ) : ℝ)

def cot_pi_11_19_lower : ℚ := -1140466314336003 / 4503599627370496
def cot_pi_11_19_upper : ℚ := -1140466314335997 / 4503599627370496
axiom cot_pi_11_19_bounds :
  ((cot_pi_11_19_lower : ℚ) : ℝ) ≤ cotangentTermV 11 19 ∧
  cotangentTermV 11 19 ≤ ((cot_pi_11_19_upper : ℚ) : ℝ)

def cot_pi_12_19_lower : ℚ := -7901847813765681 / 18014398509481984
def cot_pi_12_19_upper : ℚ := -7901847813765659 / 18014398509481984
axiom cot_pi_12_19_bounds :
  ((cot_pi_12_19_lower : ℚ) : ℝ) ≤ cotangentTermV 12 19 ∧
  cotangentTermV 12 19 ≤ ((cot_pi_12_19_upper : ℚ) : ℝ)

def cot_pi_13_19_lower : ℚ := -367793560938947 / 562949953421312
def cot_pi_13_19_upper : ℚ := -367793560938945 / 562949953421312
axiom cot_pi_13_19_bounds :
  ((cot_pi_13_19_lower : ℚ) : ℝ) ≤ cotangentTermV 13 19 ∧
  cotangentTermV 13 19 ≤ ((cot_pi_13_19_upper : ℚ) : ℝ)

def cot_pi_14_19_lower : ℚ := -2072927758191173 / 2251799813685248
def cot_pi_14_19_upper : ℚ := -1036463879095583 / 1125899906842624
axiom cot_pi_14_19_bounds :
  ((cot_pi_14_19_lower : ℚ) : ℝ) ≤ cotangentTermV 14 19 ∧
  cotangentTermV 14 19 ≤ ((cot_pi_14_19_upper : ℚ) : ℝ)

def cot_pi_15_19_lower : ℚ := -2893112459767841 / 2251799813685248
def cot_pi_15_19_upper : ℚ := -1446556229883913 / 1125899906842624
axiom cot_pi_15_19_bounds :
  ((cot_pi_15_19_lower : ℚ) : ℝ) ≤ cotangentTermV 15 19 ∧
  cotangentTermV 15 19 ≤ ((cot_pi_15_19_upper : ℚ) : ℝ)

def cot_pi_16_19_lower : ℚ := -4160961606430271 / 2251799813685248
def cot_pi_16_19_upper : ℚ := -4160961606430255 / 2251799813685248
axiom cot_pi_16_19_bounds :
  ((cot_pi_16_19_lower : ℚ) : ℝ) ≤ cotangentTermV 16 19 ∧
  cotangentTermV 16 19 ≤ ((cot_pi_16_19_upper : ℚ) : ℝ)

def cot_pi_17_19_lower : ℚ := -6559268772007799 / 2251799813685248
def cot_pi_17_19_upper : ℚ := -6559268772007749 / 2251799813685248
axiom cot_pi_17_19_bounds :
  ((cot_pi_17_19_lower : ℚ) : ℝ) ≤ cotangentTermV 17 19 ∧
  cotangentTermV 17 19 ≤ ((cot_pi_17_19_upper : ℚ) : ℝ)

def cot_pi_18_19_lower : ℚ := -6747148236890077 / 1125899906842624
def cot_pi_18_19_upper : ℚ := -6747148236890017 / 1125899906842624
axiom cot_pi_18_19_bounds :
  ((cot_pi_18_19_lower : ℚ) : ℝ) ≤ cotangentTermV 18 19 ∧
  cotangentTermV 18 19 ≤ ((cot_pi_18_19_upper : ℚ) : ℝ)

def cot_pi_1_20_lower : ℚ := 7108652242200103 / 1125899906842624
def cot_pi_1_20_upper : ℚ := 7108652242200111 / 1125899906842624
axiom cot_pi_1_20_bounds :
  ((cot_pi_1_20_lower : ℚ) : ℝ) ≤ cotangentTermV 1 20 ∧
  cotangentTermV 1 20 ≤ ((cot_pi_1_20_upper : ℚ) : ℝ)

def cot_pi_2_20_lower : ℚ := 3465163607796693 / 1125899906842624
def cot_pi_2_20_upper : ℚ := 3465163607796697 / 1125899906842624
axiom cot_pi_2_20_bounds :
  ((cot_pi_2_20_lower : ℚ) : ℝ) ≤ cotangentTermV 2 20 ∧
  cotangentTermV 2 20 ≤ ((cot_pi_2_20_upper : ℚ) : ℝ)

def cot_pi_3_20_lower : ℚ := 8838811941266413 / 4503599627370496
def cot_pi_3_20_upper : ℚ := 8838811941266421 / 4503599627370496
axiom cot_pi_3_20_bounds :
  ((cot_pi_3_20_lower : ℚ) : ℝ) ≤ cotangentTermV 3 20 ∧
  cotangentTermV 3 20 ≤ ((cot_pi_3_20_upper : ℚ) : ℝ)

def cot_pi_4_20_lower : ℚ := 6198673104153461 / 4503599627370496
def cot_pi_4_20_upper : ℚ := 6198673104153469 / 4503599627370496
axiom cot_pi_4_20_bounds :
  ((cot_pi_4_20_lower : ℚ) : ℝ) ≤ cotangentTermV 4 20 ∧
  cotangentTermV 4 20 ≤ ((cot_pi_4_20_upper : ℚ) : ℝ)

def cot_pi_5_20_lower : ℚ := 2251799813685247 / 2251799813685248
def cot_pi_5_20_upper : ℚ := 2251799813685249 / 2251799813685248
axiom cot_pi_5_20_bounds :
  ((cot_pi_5_20_lower : ℚ) : ℝ) ≤ cotangentTermV 5 20 ∧
  cotangentTermV 5 20 ≤ ((cot_pi_5_20_upper : ℚ) : ℝ)

def cot_pi_6_20_lower : ℚ := 6544113316787519 / 9007199254740992
def cot_pi_6_20_upper : ℚ := 6544113316787527 / 9007199254740992
axiom cot_pi_6_20_bounds :
  ((cot_pi_6_20_lower : ℚ) : ℝ) ≤ cotangentTermV 6 20 ∧
  cotangentTermV 6 20 ≤ ((cot_pi_6_20_upper : ℚ) : ℝ)

def cot_pi_7_20_lower : ℚ := 4589397248957785 / 9007199254740992
def cot_pi_7_20_upper : ℚ := 4589397248957791 / 9007199254740992
axiom cot_pi_7_20_bounds :
  ((cot_pi_7_20_lower : ℚ) : ℝ) ≤ cotangentTermV 7 20 ∧
  cotangentTermV 7 20 ≤ ((cot_pi_7_20_upper : ℚ) : ℝ)

def cot_pi_8_20_lower : ℚ := 2926616445759701 / 9007199254740992
def cot_pi_8_20_upper : ℚ := 1463308222879853 / 4503599627370496
axiom cot_pi_8_20_bounds :
  ((cot_pi_8_20_lower : ℚ) : ℝ) ≤ cotangentTermV 8 20 ∧
  cotangentTermV 8 20 ≤ ((cot_pi_8_20_upper : ℚ) : ℝ)

def cot_pi_9_20_lower : ℚ := 5706400851414925 / 36028797018963968
def cot_pi_9_20_upper : ℚ := 5706400851414937 / 36028797018963968
axiom cot_pi_9_20_bounds :
  ((cot_pi_9_20_lower : ℚ) : ℝ) ≤ cotangentTermV 9 20 ∧
  cotangentTermV 9 20 ≤ ((cot_pi_9_20_upper : ℚ) : ℝ)

def cot_pi_10_20_lower : ℚ := -488112139 / 9671406556917033397649408
def cot_pi_10_20_upper : ℚ := 1671954449 / 9671406556917033397649408
axiom cot_pi_10_20_bounds :
  ((cot_pi_10_20_lower : ℚ) : ℝ) ≤ cotangentTermV 10 20 ∧
  cotangentTermV 10 20 ≤ ((cot_pi_10_20_upper : ℚ) : ℝ)

def cot_pi_11_20_lower : ℚ := -5706400851414947 / 36028797018963968
def cot_pi_11_20_upper : ℚ := -5706400851414889 / 36028797018963968
axiom cot_pi_11_20_bounds :
  ((cot_pi_11_20_lower : ℚ) : ℝ) ≤ cotangentTermV 11 20 ∧
  cotangentTermV 11 20 ≤ ((cot_pi_11_20_upper : ℚ) : ℝ)

def cot_pi_12_20_lower : ℚ := -2926616445759705 / 9007199254740992
def cot_pi_12_20_upper : ℚ := -731654111439925 / 2251799813685248
axiom cot_pi_12_20_bounds :
  ((cot_pi_12_20_lower : ℚ) : ℝ) ≤ cotangentTermV 12 20 ∧
  cotangentTermV 12 20 ≤ ((cot_pi_12_20_upper : ℚ) : ℝ)

def cot_pi_13_20_lower : ℚ := -4589397248957795 / 9007199254740992
def cot_pi_13_20_upper : ℚ := -4589397248957769 / 9007199254740992
axiom cot_pi_13_20_bounds :
  ((cot_pi_13_20_lower : ℚ) : ℝ) ≤ cotangentTermV 13 20 ∧
  cotangentTermV 13 20 ≤ ((cot_pi_13_20_upper : ℚ) : ℝ)

def cot_pi_14_20_lower : ℚ := -3272056658393763 / 4503599627370496
def cot_pi_14_20_upper : ℚ := -1636028329196879 / 2251799813685248
axiom cot_pi_14_20_bounds :
  ((cot_pi_14_20_lower : ℚ) : ℝ) ≤ cotangentTermV 14 20 ∧
  cotangentTermV 14 20 ≤ ((cot_pi_14_20_upper : ℚ) : ℝ)

def cot_pi_15_20_lower : ℚ := -2251799813685251 / 2251799813685248
def cot_pi_15_20_upper : ℚ := -9007199254740961 / 9007199254740992
axiom cot_pi_15_20_bounds :
  ((cot_pi_15_20_lower : ℚ) : ℝ) ≤ cotangentTermV 15 20 ∧
  cotangentTermV 15 20 ≤ ((cot_pi_15_20_upper : ℚ) : ℝ)

def cot_pi_16_20_lower : ℚ := -6198673104153469 / 4503599627370496
def cot_pi_16_20_upper : ℚ := -6198673104153459 / 4503599627370496
axiom cot_pi_16_20_bounds :
  ((cot_pi_16_20_lower : ℚ) : ℝ) ≤ cotangentTermV 16 20 ∧
  cotangentTermV 16 20 ≤ ((cot_pi_16_20_upper : ℚ) : ℝ)

def cot_pi_17_20_lower : ℚ := -4419405970633215 / 2251799813685248
def cot_pi_17_20_upper : ℚ := -2209702985316595 / 1125899906842624
axiom cot_pi_17_20_bounds :
  ((cot_pi_17_20_lower : ℚ) : ℝ) ≤ cotangentTermV 17 20 ∧
  cotangentTermV 17 20 ≤ ((cot_pi_17_20_upper : ℚ) : ℝ)

def cot_pi_18_20_lower : ℚ := -1732581803898349 / 562949953421312
def cot_pi_18_20_upper : ℚ := -1732581803898345 / 562949953421312
axiom cot_pi_18_20_bounds :
  ((cot_pi_18_20_lower : ℚ) : ℝ) ≤ cotangentTermV 18 20 ∧
  cotangentTermV 18 20 ≤ ((cot_pi_18_20_upper : ℚ) : ℝ)

def cot_pi_19_20_lower : ℚ := -7108652242200131 / 1125899906842624
def cot_pi_19_20_upper : ℚ := -7108652242200031 / 1125899906842624
axiom cot_pi_19_20_bounds :
  ((cot_pi_19_20_lower : ℚ) : ℝ) ≤ cotangentTermV 19 20 ∧
  cotangentTermV 19 20 ≤ ((cot_pi_19_20_upper : ℚ) : ℝ)

def cot_pi_1_21_lower : ℚ := 7469857804053975 / 1125899906842624
def cot_pi_1_21_upper : ℚ := 7469857804053985 / 1125899906842624
axiom cot_pi_1_21_bounds :
  ((cot_pi_1_21_lower : ℚ) : ℝ) ≤ cotangentTermV 1 21 ∧
  cotangentTermV 1 21 ≤ ((cot_pi_1_21_upper : ℚ) : ℝ)

def cot_pi_2_21_lower : ℚ := 912519462267461 / 281474976710656
def cot_pi_2_21_upper : ℚ := 3650077849069849 / 1125899906842624
axiom cot_pi_2_21_bounds :
  ((cot_pi_2_21_lower : ℚ) : ℝ) ≤ cotangentTermV 2 21 ∧
  cotangentTermV 2 21 ≤ ((cot_pi_2_21_upper : ℚ) : ℝ)

def cot_pi_3_21_lower : ℚ := 4675910493915015 / 2251799813685248
def cot_pi_3_21_upper : ℚ := 4675910493915021 / 2251799813685248
axiom cot_pi_3_21_bounds :
  ((cot_pi_3_21_lower : ℚ) : ℝ) ≤ cotangentTermV 3 21 ∧
  cotangentTermV 3 21 ≤ ((cot_pi_3_21_upper : ℚ) : ℝ)

def cot_pi_4_21_lower : ℚ := 6605567444055593 / 4503599627370496
def cot_pi_4_21_upper : ℚ := 6605567444055603 / 4503599627370496
axiom cot_pi_4_21_bounds :
  ((cot_pi_4_21_lower : ℚ) : ℝ) ≤ cotangentTermV 4 21 ∧
  cotangentTermV 4 21 ≤ ((cot_pi_4_21_upper : ℚ) : ℝ)

def cot_pi_5_21_lower : ℚ := 4853726051466565 / 4503599627370496
def cot_pi_5_21_upper : ℚ := 4853726051466573 / 4503599627370496
axiom cot_pi_5_21_bounds :
  ((cot_pi_5_21_lower : ℚ) : ℝ) ≤ cotangentTermV 5 21 ∧
  cotangentTermV 5 21 ≤ ((cot_pi_5_21_upper : ℚ) : ℝ)

def cot_pi_6_21_lower : ℚ := 3591500857008679 / 4503599627370496
def cot_pi_6_21_upper : ℚ := 3591500857008683 / 4503599627370496
axiom cot_pi_6_21_bounds :
  ((cot_pi_6_21_lower : ℚ) : ℝ) ≤ cotangentTermV 6 21 ∧
  cotangentTermV 6 21 ≤ ((cot_pi_6_21_upper : ℚ) : ℝ)

def cot_pi_7_21_lower : ℚ := 5200308914369303 / 9007199254740992
def cot_pi_7_21_upper : ℚ := 5200308914369315 / 9007199254740992
axiom cot_pi_7_21_bounds :
  ((cot_pi_7_21_lower : ℚ) : ℝ) ≤ cotangentTermV 7 21 ∧
  cotangentTermV 7 21 ≤ ((cot_pi_7_21_upper : ℚ) : ℝ)

def cot_pi_8_21_lower : ℚ := 3535065208565745 / 9007199254740992
def cot_pi_8_21_upper : ℚ := 1767532604282877 / 4503599627370496
axiom cot_pi_8_21_bounds :
  ((cot_pi_8_21_lower : ℚ) : ℝ) ≤ cotangentTermV 8 21 ∧
  cotangentTermV 8 21 ≤ ((cot_pi_8_21_upper : ℚ) : ℝ)

def cot_pi_9_21_lower : ℚ := 513958613106613 / 2251799813685248
def cot_pi_9_21_upper : ℚ := 4111668904852911 / 18014398509481984
axiom cot_pi_9_21_bounds :
  ((cot_pi_9_21_lower : ℚ) : ℝ) ≤ cotangentTermV 9 21 ∧
  cotangentTermV 9 21 ≤ ((cot_pi_9_21_upper : ℚ) : ℝ)

def cot_pi_10_21_lower : ℚ := 5399970157843809 / 72057594037927936
def cot_pi_10_21_upper : ℚ := 5399970157843863 / 72057594037927936
axiom cot_pi_10_21_bounds :
  ((cot_pi_10_21_lower : ℚ) : ℝ) ≤ cotangentTermV 10 21 ∧
  cotangentTermV 10 21 ≤ ((cot_pi_10_21_upper : ℚ) : ℝ)

def cot_pi_11_21_lower : ℚ := -5399970157843847 / 72057594037927936
def cot_pi_11_21_upper : ℚ := -5399970157843743 / 72057594037927936
axiom cot_pi_11_21_bounds :
  ((cot_pi_11_21_lower : ℚ) : ℝ) ≤ cotangentTermV 11 21 ∧
  cotangentTermV 11 21 ≤ ((cot_pi_11_21_upper : ℚ) : ℝ)

def cot_pi_12_21_lower : ℚ := -8223337809705817 / 36028797018963968
def cot_pi_12_21_upper : ℚ := -8223337809705801 / 36028797018963968
axiom cot_pi_12_21_bounds :
  ((cot_pi_12_21_lower : ℚ) : ℝ) ≤ cotangentTermV 12 21 ∧
  cotangentTermV 12 21 ≤ ((cot_pi_12_21_upper : ℚ) : ℝ)

def cot_pi_13_21_lower : ℚ := -3535065208565753 / 9007199254740992
def cot_pi_13_21_upper : ℚ := -3535065208565735 / 9007199254740992
axiom cot_pi_13_21_bounds :
  ((cot_pi_13_21_lower : ℚ) : ℝ) ≤ cotangentTermV 13 21 ∧
  cotangentTermV 13 21 ≤ ((cot_pi_13_21_upper : ℚ) : ℝ)

def cot_pi_14_21_lower : ℚ := -2600154457184657 / 4503599627370496
def cot_pi_14_21_upper : ℚ := -325019307148081 / 562949953421312
axiom cot_pi_14_21_bounds :
  ((cot_pi_14_21_lower : ℚ) : ℝ) ≤ cotangentTermV 14 21 ∧
  cotangentTermV 14 21 ≤ ((cot_pi_14_21_upper : ℚ) : ℝ)

def cot_pi_15_21_lower : ℚ := -3591500857008685 / 4503599627370496
def cot_pi_15_21_upper : ℚ := -897875214252167 / 1125899906842624
axiom cot_pi_15_21_bounds :
  ((cot_pi_15_21_lower : ℚ) : ℝ) ≤ cotangentTermV 15 21 ∧
  cotangentTermV 15 21 ≤ ((cot_pi_15_21_upper : ℚ) : ℝ)

def cot_pi_16_21_lower : ℚ := -2426863025733287 / 2251799813685248
def cot_pi_16_21_upper : ℚ := -1213431512866639 / 1125899906842624
axiom cot_pi_16_21_bounds :
  ((cot_pi_16_21_lower : ℚ) : ℝ) ≤ cotangentTermV 16 21 ∧
  cotangentTermV 16 21 ≤ ((cot_pi_16_21_upper : ℚ) : ℝ)

def cot_pi_17_21_lower : ℚ := -1651391861013901 / 1125899906842624
def cot_pi_17_21_upper : ℚ := -3302783722027785 / 2251799813685248
axiom cot_pi_17_21_bounds :
  ((cot_pi_17_21_lower : ℚ) : ℝ) ≤ cotangentTermV 17 21 ∧
  cotangentTermV 17 21 ≤ ((cot_pi_17_21_upper : ℚ) : ℝ)

def cot_pi_18_21_lower : ℚ := -2337955246957511 / 1125899906842624
def cot_pi_18_21_upper : ℚ := -1168977623478753 / 562949953421312
axiom cot_pi_18_21_bounds :
  ((cot_pi_18_21_lower : ℚ) : ℝ) ≤ cotangentTermV 18 21 ∧
  cotangentTermV 18 21 ≤ ((cot_pi_18_21_upper : ℚ) : ℝ)

def cot_pi_19_21_lower : ℚ := -7300155698139711 / 2251799813685248
def cot_pi_19_21_upper : ℚ := -7300155698139653 / 2251799813685248
axiom cot_pi_19_21_bounds :
  ((cot_pi_19_21_lower : ℚ) : ℝ) ≤ cotangentTermV 19 21 ∧
  cotangentTermV 19 21 ≤ ((cot_pi_19_21_upper : ℚ) : ℝ)

def cot_pi_20_21_lower : ℚ := -7469857804054003 / 1125899906842624
def cot_pi_20_21_upper : ℚ := -7469857804053929 / 1125899906842624
axiom cot_pi_20_21_bounds :
  ((cot_pi_20_21_lower : ℚ) : ℝ) ≤ cotangentTermV 20 21 ∧
  cotangentTermV 20 21 ≤ ((cot_pi_20_21_upper : ℚ) : ℝ)

def cot_pi_1_22_lower : ℚ := 244712683056749 / 35184372088832
def cot_pi_1_22_upper : ℚ := 1957701464453995 / 281474976710656
axiom cot_pi_1_22_bounds :
  ((cot_pi_1_22_lower : ℚ) : ℝ) ≤ cotangentTermV 1 22 ∧
  cotangentTermV 1 22 ≤ ((cot_pi_1_22_upper : ℚ) : ℝ)

def cot_pi_2_22_lower : ℚ := 7668925890001035 / 2251799813685248
def cot_pi_2_22_upper : ℚ := 7668925890001047 / 2251799813685248
axiom cot_pi_2_22_bounds :
  ((cot_pi_2_22_lower : ℚ) : ℝ) ≤ cotangentTermV 2 22 ∧
  cotangentTermV 2 22 ≤ ((cot_pi_2_22_upper : ℚ) : ℝ)

def cot_pi_3_22_lower : ℚ := 4930753808967761 / 2251799813685248
def cot_pi_3_22_upper : ℚ := 4930753808967767 / 2251799813685248
axiom cot_pi_3_22_bounds :
  ((cot_pi_3_22_lower : ℚ) : ℝ) ≤ cotangentTermV 3 22 ∧
  cotangentTermV 3 22 ≤ ((cot_pi_3_22_upper : ℚ) : ℝ)

def cot_pi_4_22_lower : ℚ := 7007737807909369 / 4503599627370496
def cot_pi_4_22_upper : ℚ := 7007737807909381 / 4503599627370496
axiom cot_pi_4_22_bounds :
  ((cot_pi_4_22_lower : ℚ) : ℝ) ≤ cotangentTermV 4 22 ∧
  cotangentTermV 4 22 ≤ ((cot_pi_4_22_upper : ℚ) : ℝ)

def cot_pi_5_22_lower : ℚ := 5197431033835087 / 4503599627370496
def cot_pi_5_22_upper : ℚ := 5197431033835095 / 4503599627370496
axiom cot_pi_5_22_bounds :
  ((cot_pi_5_22_lower : ℚ) : ℝ) ≤ cotangentTermV 5 22 ∧
  cotangentTermV 5 22 ≤ ((cot_pi_5_22_upper : ℚ) : ℝ)

def cot_pi_6_22_lower : ℚ := 7804782582631265 / 9007199254740992
def cot_pi_6_22_upper : ℚ := 7804782582631277 / 9007199254740992
axiom cot_pi_6_22_bounds :
  ((cot_pi_6_22_lower : ℚ) : ℝ) ≤ cotangentTermV 6 22 ∧
  cotangentTermV 6 22 ≤ ((cot_pi_6_22_upper : ℚ) : ℝ)

def cot_pi_7_22_lower : ℚ := 723571934325213 / 1125899906842624
def cot_pi_7_22_upper : ℚ := 2894287737300857 / 4503599627370496
axiom cot_pi_7_22_bounds :
  ((cot_pi_7_22_lower : ℚ) : ℝ) ≤ cotangentTermV 7 22 ∧
  cotangentTermV 7 22 ≤ ((cot_pi_7_22_upper : ℚ) : ℝ)

def cot_pi_8_22_lower : ℚ := 8226900141217031 / 18014398509481984
def cot_pi_8_22_upper : ℚ := 8226900141217051 / 18014398509481984
axiom cot_pi_8_22_bounds :
  ((cot_pi_8_22_lower : ℚ) : ℝ) ≤ cotangentTermV 8 22 ∧
  cotangentTermV 8 22 ≤ ((cot_pi_8_22_upper : ℚ) : ℝ)

def cot_pi_9_22_lower : ℚ := 330594041045833 / 1125899906842624
def cot_pi_9_22_upper : ℚ := 2644752328366673 / 9007199254740992
axiom cot_pi_9_22_bounds :
  ((cot_pi_9_22_lower : ℚ) : ℝ) ≤ cotangentTermV 9 22 ∧
  cotangentTermV 9 22 ≤ ((cot_pi_9_22_upper : ℚ) : ℝ)

def cot_pi_10_22_lower : ℚ := 5180158970077811 / 36028797018963968
def cot_pi_10_22_upper : ℚ := 5180158970077841 / 36028797018963968
axiom cot_pi_10_22_bounds :
  ((cot_pi_10_22_lower : ℚ) : ℝ) ≤ cotangentTermV 10 22 ∧
  cotangentTermV 10 22 ≤ ((cot_pi_10_22_upper : ℚ) : ℝ)

def cot_pi_11_22_lower : ℚ := -225732797 / 604462909807314587353088
def cot_pi_11_22_upper : ℚ := 568158399 / 604462909807314587353088
axiom cot_pi_11_22_bounds :
  ((cot_pi_11_22_lower : ℚ) : ℝ) ≤ cotangentTermV 11 22 ∧
  cotangentTermV 11 22 ≤ ((cot_pi_11_22_upper : ℚ) : ℝ)

def cot_pi_12_22_lower : ℚ := -1295039742519457 / 9007199254740992
def cot_pi_12_22_upper : ℚ := -2590079485038899 / 18014398509481984
axiom cot_pi_12_22_bounds :
  ((cot_pi_12_22_lower : ℚ) : ℝ) ≤ cotangentTermV 12 22 ∧
  cotangentTermV 12 22 ≤ ((cot_pi_12_22_upper : ℚ) : ℝ)

def cot_pi_13_22_lower : ℚ := -5289504656733343 / 18014398509481984
def cot_pi_13_22_upper : ℚ := -5289504656733319 / 18014398509481984
axiom cot_pi_13_22_bounds :
  ((cot_pi_13_22_lower : ℚ) : ℝ) ≤ cotangentTermV 13 22 ∧
  cotangentTermV 13 22 ≤ ((cot_pi_13_22_upper : ℚ) : ℝ)

def cot_pi_14_22_lower : ℚ := -8226900141217045 / 18014398509481984
def cot_pi_14_22_upper : ℚ := -8226900141217023 / 18014398509481984
axiom cot_pi_14_22_bounds :
  ((cot_pi_14_22_lower : ℚ) : ℝ) ≤ cotangentTermV 14 22 ∧
  cotangentTermV 14 22 ≤ ((cot_pi_14_22_upper : ℚ) : ℝ)

def cot_pi_15_22_lower : ℚ := -5788575474601719 / 9007199254740992
def cot_pi_15_22_upper : ℚ := -5788575474601689 / 9007199254740992
axiom cot_pi_15_22_bounds :
  ((cot_pi_15_22_lower : ℚ) : ℝ) ≤ cotangentTermV 15 22 ∧
  cotangentTermV 15 22 ≤ ((cot_pi_15_22_upper : ℚ) : ℝ)

def cot_pi_16_22_lower : ℚ := -3902391291315637 / 4503599627370496
def cot_pi_16_22_upper : ℚ := -487798911414453 / 562949953421312
axiom cot_pi_16_22_bounds :
  ((cot_pi_16_22_lower : ℚ) : ℝ) ≤ cotangentTermV 16 22 ∧
  cotangentTermV 16 22 ≤ ((cot_pi_16_22_upper : ℚ) : ℝ)

def cot_pi_17_22_lower : ℚ := -649678879229387 / 562949953421312
def cot_pi_17_22_upper : ℚ := -2598715516917535 / 2251799813685248
axiom cot_pi_17_22_bounds :
  ((cot_pi_17_22_lower : ℚ) : ℝ) ≤ cotangentTermV 17 22 ∧
  cotangentTermV 17 22 ≤ ((cot_pi_17_22_upper : ℚ) : ℝ)

def cot_pi_18_22_lower : ℚ := -7007737807909383 / 4503599627370496
def cot_pi_18_22_upper : ℚ := -7007737807909357 / 4503599627370496
axiom cot_pi_18_22_bounds :
  ((cot_pi_18_22_lower : ℚ) : ℝ) ≤ cotangentTermV 18 22 ∧
  cotangentTermV 18 22 ≤ ((cot_pi_18_22_upper : ℚ) : ℝ)

def cot_pi_19_22_lower : ℚ := -4930753808967775 / 2251799813685248
def cot_pi_19_22_upper : ℚ := -4930753808967745 / 2251799813685248
axiom cot_pi_19_22_bounds :
  ((cot_pi_19_22_lower : ℚ) : ℝ) ≤ cotangentTermV 19 22 ∧
  cotangentTermV 19 22 ≤ ((cot_pi_19_22_upper : ℚ) : ℝ)

def cot_pi_20_22_lower : ℚ := -3834462945000525 / 1125899906842624
def cot_pi_20_22_upper : ℚ := -3834462945000503 / 1125899906842624
axiom cot_pi_20_22_bounds :
  ((cot_pi_20_22_lower : ℚ) : ℝ) ≤ cotangentTermV 20 22 ∧
  cotangentTermV 20 22 ≤ ((cot_pi_20_22_upper : ℚ) : ℝ)

def cot_pi_21_22_lower : ℚ := -3915402928907999 / 562949953421312
def cot_pi_21_22_upper : ℚ := -1957701464453961 / 281474976710656
axiom cot_pi_21_22_bounds :
  ((cot_pi_21_22_lower : ℚ) : ℝ) ≤ cotangentTermV 21 22 ∧
  cotangentTermV 21 22 ≤ ((cot_pi_21_22_upper : ℚ) : ℝ)

def cot_pi_1_23_lower : ℚ := 8191530170975963 / 1125899906842624
def cot_pi_1_23_upper : ℚ := 8191530170975975 / 1125899906842624
axiom cot_pi_1_23_bounds :
  ((cot_pi_1_23_lower : ℚ) : ℝ) ≤ cotangentTermV 1 23 ∧
  cotangentTermV 1 23 ≤ ((cot_pi_1_23_upper : ℚ) : ℝ)

def cot_pi_2_23_lower : ℚ := 8036778790736929 / 2251799813685248
def cot_pi_2_23_upper : ℚ := 8036778790736941 / 2251799813685248
axiom cot_pi_2_23_bounds :
  ((cot_pi_2_23_lower : ℚ) : ℝ) ≤ cotangentTermV 2 23 ∧
  cotangentTermV 2 23 ≤ ((cot_pi_2_23_upper : ℚ) : ℝ)

def cot_pi_3_23_lower : ℚ := 5184163122237167 / 2251799813685248
def cot_pi_3_23_upper : ℚ := 5184163122237175 / 2251799813685248
axiom cot_pi_3_23_bounds :
  ((cot_pi_3_23_lower : ℚ) : ℝ) ≤ cotangentTermV 3 23 ∧
  cotangentTermV 3 23 ≤ ((cot_pi_3_23_upper : ℚ) : ℝ)

def cot_pi_4_23_lower : ℚ := 7405854071649573 / 4503599627370496
def cot_pi_4_23_upper : ℚ := 7405854071649585 / 4503599627370496
axiom cot_pi_4_23_bounds :
  ((cot_pi_4_23_lower : ℚ) : ℝ) ≤ cotangentTermV 4 23 ∧
  cotangentTermV 4 23 ≤ ((cot_pi_4_23_upper : ℚ) : ℝ)

def cot_pi_5_23_lower : ℚ := 5535667589870151 / 4503599627370496
def cot_pi_5_23_upper : ℚ := 5535667589870161 / 4503599627370496
axiom cot_pi_5_23_bounds :
  ((cot_pi_5_23_lower : ℚ) : ℝ) ≤ cotangentTermV 5 23 ∧
  cotangentTermV 5 23 ≤ ((cot_pi_5_23_upper : ℚ) : ℝ)

def cot_pi_6_23_lower : ℚ := 8412136872591781 / 9007199254740992
def cot_pi_6_23_upper : ℚ := 8412136872591795 / 9007199254740992
axiom cot_pi_6_23_bounds :
  ((cot_pi_6_23_lower : ℚ) : ℝ) ≤ cotangentTermV 6 23 ∧
  cotangentTermV 6 23 ≤ ((cot_pi_6_23_upper : ℚ) : ℝ)

def cot_pi_7_23_lower : ℚ := 6357975504380591 / 9007199254740992
def cot_pi_7_23_upper : ℚ := 6357975504380603 / 9007199254740992
axiom cot_pi_7_23_bounds :
  ((cot_pi_7_23_lower : ℚ) : ℝ) ≤ cotangentTermV 7 23 ∧
  cotangentTermV 7 23 ≤ ((cot_pi_7_23_upper : ℚ) : ℝ)

def cot_pi_8_23_lower : ℚ := 4667154468953517 / 9007199254740992
def cot_pi_8_23_upper : ℚ := 4667154468953529 / 9007199254740992
axiom cot_pi_8_23_bounds :
  ((cot_pi_8_23_lower : ℚ) : ℝ) ≤ cotangentTermV 8 23 ∧
  cotangentTermV 8 23 ≤ ((cot_pi_8_23_upper : ℚ) : ℝ)

def cot_pi_9_23_lower : ℚ := 3201159384166939 / 9007199254740992
def cot_pi_9_23_upper : ℚ := 800289846041737 / 2251799813685248
axiom cot_pi_9_23_bounds :
  ((cot_pi_9_23_lower : ℚ) : ℝ) ≤ cotangentTermV 9 23 ∧
  cotangentTermV 9 23 ≤ ((cot_pi_9_23_upper : ℚ) : ℝ)

def cot_pi_10_23_lower : ℚ := 1871717528857293 / 9007199254740992
def cot_pi_10_23_upper : ℚ := 3743435057714601 / 18014398509481984
axiom cot_pi_10_23_bounds :
  ((cot_pi_10_23_lower : ℚ) : ℝ) ≤ cotangentTermV 10 23 ∧
  cotangentTermV 10 23 ≤ ((cot_pi_10_23_upper : ℚ) : ℝ)

def cot_pi_11_23_lower : ℚ := 4928874462402615 / 72057594037927936
def cot_pi_11_23_upper : ℚ := 4928874462402713 / 72057594037927936
axiom cot_pi_11_23_bounds :
  ((cot_pi_11_23_lower : ℚ) : ℝ) ≤ cotangentTermV 11 23 ∧
  cotangentTermV 11 23 ≤ ((cot_pi_11_23_upper : ℚ) : ℝ)

def cot_pi_12_23_lower : ℚ := -2464437231201333 / 36028797018963968
def cot_pi_12_23_upper : ℚ := -1232218615600653 / 18014398509481984
axiom cot_pi_12_23_bounds :
  ((cot_pi_12_23_lower : ℚ) : ℝ) ≤ cotangentTermV 12 23 ∧
  cotangentTermV 12 23 ≤ ((cot_pi_12_23_upper : ℚ) : ℝ)

def cot_pi_13_23_lower : ℚ := -3743435057714597 / 18014398509481984
def cot_pi_13_23_upper : ℚ := -3743435057714569 / 18014398509481984
axiom cot_pi_13_23_bounds :
  ((cot_pi_13_23_lower : ℚ) : ℝ) ≤ cotangentTermV 13 23 ∧
  cotangentTermV 13 23 ≤ ((cot_pi_13_23_upper : ℚ) : ℝ)

def cot_pi_14_23_lower : ℚ := -6402318768333891 / 18014398509481984
def cot_pi_14_23_upper : ℚ := -6402318768333871 / 18014398509481984
axiom cot_pi_14_23_bounds :
  ((cot_pi_14_23_lower : ℚ) : ℝ) ≤ cotangentTermV 14 23 ∧
  cotangentTermV 14 23 ≤ ((cot_pi_14_23_upper : ℚ) : ℝ)

def cot_pi_15_23_lower : ℚ := -4667154468953529 / 9007199254740992
def cot_pi_15_23_upper : ℚ := -4667154468953503 / 9007199254740992
axiom cot_pi_15_23_bounds :
  ((cot_pi_15_23_lower : ℚ) : ℝ) ≤ cotangentTermV 15 23 ∧
  cotangentTermV 15 23 ≤ ((cot_pi_15_23_upper : ℚ) : ℝ)

def cot_pi_16_23_lower : ℚ := -6357975504380605 / 9007199254740992
def cot_pi_16_23_upper : ℚ := -6357975504380583 / 9007199254740992
axiom cot_pi_16_23_bounds :
  ((cot_pi_16_23_lower : ℚ) : ℝ) ≤ cotangentTermV 16 23 ∧
  cotangentTermV 16 23 ≤ ((cot_pi_16_23_upper : ℚ) : ℝ)

def cot_pi_17_23_lower : ℚ := -2103034218147949 / 2251799813685248
def cot_pi_17_23_upper : ℚ := -4206068436295879 / 4503599627370496
axiom cot_pi_17_23_bounds :
  ((cot_pi_17_23_lower : ℚ) : ℝ) ≤ cotangentTermV 17 23 ∧
  cotangentTermV 17 23 ≤ ((cot_pi_17_23_upper : ℚ) : ℝ)

def cot_pi_18_23_lower : ℚ := -2767833794935081 / 2251799813685248
def cot_pi_18_23_upper : ℚ := -2767833794935071 / 2251799813685248
axiom cot_pi_18_23_bounds :
  ((cot_pi_18_23_lower : ℚ) : ℝ) ≤ cotangentTermV 18 23 ∧
  cotangentTermV 18 23 ≤ ((cot_pi_18_23_upper : ℚ) : ℝ)

def cot_pi_19_23_lower : ℚ := -925731758956199 / 562949953421312
def cot_pi_19_23_upper : ℚ := -3702927035824777 / 2251799813685248
axiom cot_pi_19_23_bounds :
  ((cot_pi_19_23_lower : ℚ) : ℝ) ≤ cotangentTermV 19 23 ∧
  cotangentTermV 19 23 ≤ ((cot_pi_19_23_upper : ℚ) : ℝ)

def cot_pi_20_23_lower : ℚ := -5184163122237177 / 2251799813685248
def cot_pi_20_23_upper : ℚ := -5184163122237153 / 2251799813685248
axiom cot_pi_20_23_bounds :
  ((cot_pi_20_23_lower : ℚ) : ℝ) ≤ cotangentTermV 20 23 ∧
  cotangentTermV 20 23 ≤ ((cot_pi_20_23_upper : ℚ) : ℝ)

def cot_pi_21_23_lower : ℚ := -8036778790736949 / 2251799813685248
def cot_pi_21_23_upper : ℚ := -8036778790736863 / 2251799813685248
axiom cot_pi_21_23_bounds :
  ((cot_pi_21_23_lower : ℚ) : ℝ) ≤ cotangentTermV 21 23 ∧
  cotangentTermV 21 23 ≤ ((cot_pi_21_23_upper : ℚ) : ℝ)

def cot_pi_22_23_lower : ℚ := -8191530170976021 / 1125899906842624
def cot_pi_22_23_upper : ℚ := -8191530170975857 / 1125899906842624
axiom cot_pi_22_23_bounds :
  ((cot_pi_22_23_lower : ℚ) : ℝ) ≤ cotangentTermV 22 23 ∧
  cotangentTermV 22 23 ≤ ((cot_pi_22_23_upper : ℚ) : ℝ)

def cot_pi_1_24_lower : ℚ := 8552058847916719 / 1125899906842624
def cot_pi_1_24_upper : ℚ := 8552058847916731 / 1125899906842624
axiom cot_pi_1_24_bounds :
  ((cot_pi_1_24_lower : ℚ) : ℝ) ≤ cotangentTermV 1 24 ∧
  cotangentTermV 1 24 ≤ ((cot_pi_1_24_upper : ℚ) : ℝ)

def cot_pi_2_24_lower : ℚ := 8403831313147473 / 2251799813685248
def cot_pi_2_24_upper : ℚ := 8403831313147485 / 2251799813685248
axiom cot_pi_2_24_bounds :
  ((cot_pi_2_24_lower : ℚ) : ℝ) ≤ cotangentTermV 2 24 ∧
  cotangentTermV 2 24 ≤ ((cot_pi_2_24_upper : ℚ) : ℝ)

def cot_pi_3_24_lower : ℚ := 5436325649948131 / 2251799813685248
def cot_pi_3_24_upper : ℚ := 5436325649948137 / 2251799813685248
axiom cot_pi_3_24_bounds :
  ((cot_pi_3_24_lower : ℚ) : ℝ) ≤ cotangentTermV 3 24 ∧
  cotangentTermV 3 24 ≤ ((cot_pi_3_24_upper : ℚ) : ℝ)

def cot_pi_4_24_lower : ℚ := 1950115842888489 / 1125899906842624
def cot_pi_4_24_upper : ℚ := 487528960722123 / 281474976710656
axiom cot_pi_4_24_bounds :
  ((cot_pi_4_24_lower : ℚ) : ℝ) ≤ cotangentTermV 4 24 ∧
  cotangentTermV 4 24 ≤ ((cot_pi_4_24_upper : ℚ) : ℝ)

def cot_pi_5_24_lower : ℚ := 5869205303507425 / 4503599627370496
def cot_pi_5_24_upper : ℚ := 5869205303507435 / 4503599627370496
axiom cot_pi_5_24_bounds :
  ((cot_pi_5_24_lower : ℚ) : ℝ) ≤ cotangentTermV 5 24 ∧
  cotangentTermV 5 24 ≤ ((cot_pi_5_24_upper : ℚ) : ℝ)

def cot_pi_6_24_lower : ℚ := 2251799813685247 / 2251799813685248
def cot_pi_6_24_upper : ℚ := 2251799813685249 / 2251799813685248
axiom cot_pi_6_24_bounds :
  ((cot_pi_6_24_lower : ℚ) : ℝ) ≤ cotangentTermV 6 24 ∧
  cotangentTermV 6 24 ≤ ((cot_pi_6_24_upper : ℚ) : ℝ)

def cot_pi_7_24_lower : ℚ := 431966692141671 / 562949953421312
def cot_pi_7_24_upper : ℚ := 1727866768566687 / 2251799813685248
axiom cot_pi_7_24_bounds :
  ((cot_pi_7_24_lower : ℚ) : ℝ) ≤ cotangentTermV 7 24 ∧
  cotangentTermV 7 24 ≤ ((cot_pi_7_24_upper : ℚ) : ℝ)

def cot_pi_8_24_lower : ℚ := 5200308914369303 / 9007199254740992
def cot_pi_8_24_upper : ℚ := 5200308914369315 / 9007199254740992
axiom cot_pi_8_24_bounds :
  ((cot_pi_8_24_lower : ℚ) : ℝ) ≤ cotangentTermV 8 24 ∧
  cotangentTermV 8 24 ≤ ((cot_pi_8_24_upper : ℚ) : ℝ)

def cot_pi_9_24_lower : ℚ := 7461808180621101 / 18014398509481984
def cot_pi_9_24_upper : ℚ := 7461808180621111 / 18014398509481984
axiom cot_pi_9_24_bounds :
  ((cot_pi_9_24_lower : ℚ) : ℝ) ≤ cotangentTermV 9 24 ∧
  cotangentTermV 9 24 ≤ ((cot_pi_9_24_upper : ℚ) : ℝ)

def cot_pi_10_24_lower : ℚ := 301683970796757 / 1125899906842624
def cot_pi_10_24_upper : ℚ := 2413471766374065 / 9007199254740992
axiom cot_pi_10_24_bounds :
  ((cot_pi_10_24_lower : ℚ) : ℝ) ≤ cotangentTermV 10 24 ∧
  cotangentTermV 10 24 ≤ ((cot_pi_10_24_upper : ℚ) : ℝ)

def cot_pi_11_24_lower : ℚ := 1185820278153979 / 9007199254740992
def cot_pi_11_24_upper : ℚ := 2371640556307983 / 18014398509481984
axiom cot_pi_11_24_bounds :
  ((cot_pi_11_24_lower : ℚ) : ℝ) ≤ cotangentTermV 11 24 ∧
  cotangentTermV 11 24 ≤ ((cot_pi_11_24_upper : ℚ) : ℝ)

def cot_pi_12_24_lower : ℚ := -488112137 / 9671406556917033397649408
def cot_pi_12_24_upper : ℚ := 1671954447 / 9671406556917033397649408
axiom cot_pi_12_24_bounds :
  ((cot_pi_12_24_lower : ℚ) : ℝ) ≤ cotangentTermV 12 24 ∧
  cotangentTermV 12 24 ≤ ((cot_pi_12_24_upper : ℚ) : ℝ)

def cot_pi_13_24_lower : ℚ := -2371640556307969 / 18014398509481984
def cot_pi_13_24_upper : ℚ := -2371640556307951 / 18014398509481984
axiom cot_pi_13_24_bounds :
  ((cot_pi_13_24_lower : ℚ) : ℝ) ≤ cotangentTermV 13 24 ∧
  cotangentTermV 13 24 ≤ ((cot_pi_13_24_upper : ℚ) : ℝ)

def cot_pi_14_24_lower : ℚ := -4826943532748123 / 18014398509481984
def cot_pi_14_24_upper : ℚ := -4826943532748105 / 18014398509481984
axiom cot_pi_14_24_bounds :
  ((cot_pi_14_24_lower : ℚ) : ℝ) ≤ cotangentTermV 14 24 ∧
  cotangentTermV 14 24 ≤ ((cot_pi_14_24_upper : ℚ) : ℝ)

def cot_pi_15_24_lower : ℚ := -1865452045155279 / 4503599627370496
def cot_pi_15_24_upper : ℚ := -3730904090310541 / 9007199254740992
axiom cot_pi_15_24_bounds :
  ((cot_pi_15_24_lower : ℚ) : ℝ) ≤ cotangentTermV 15 24 ∧
  cotangentTermV 15 24 ≤ ((cot_pi_15_24_upper : ℚ) : ℝ)

def cot_pi_16_24_lower : ℚ := -2600154457184657 / 4503599627370496
def cot_pi_16_24_upper : ℚ := -325019307148081 / 562949953421312
axiom cot_pi_16_24_bounds :
  ((cot_pi_16_24_lower : ℚ) : ℝ) ≤ cotangentTermV 16 24 ∧
  cotangentTermV 16 24 ≤ ((cot_pi_16_24_upper : ℚ) : ℝ)

def cot_pi_17_24_lower : ℚ := -53995836517709 / 70368744177664
def cot_pi_17_24_upper : ℚ := -215983346070835 / 281474976710656
axiom cot_pi_17_24_bounds :
  ((cot_pi_17_24_lower : ℚ) : ℝ) ≤ cotangentTermV 17 24 ∧
  cotangentTermV 17 24 ≤ ((cot_pi_17_24_upper : ℚ) : ℝ)

def cot_pi_18_24_lower : ℚ := -2251799813685249 / 2251799813685248
def cot_pi_18_24_upper : ℚ := -4503599627370491 / 4503599627370496
axiom cot_pi_18_24_bounds :
  ((cot_pi_18_24_lower : ℚ) : ℝ) ≤ cotangentTermV 18 24 ∧
  cotangentTermV 18 24 ≤ ((cot_pi_18_24_upper : ℚ) : ℝ)

def cot_pi_19_24_lower : ℚ := -1467301325876859 / 1125899906842624
def cot_pi_19_24_upper : ℚ := -2934602651753709 / 2251799813685248
axiom cot_pi_19_24_bounds :
  ((cot_pi_19_24_lower : ℚ) : ℝ) ≤ cotangentTermV 19 24 ∧
  cotangentTermV 19 24 ≤ ((cot_pi_19_24_upper : ℚ) : ℝ)

def cot_pi_20_24_lower : ℚ := -7800463371553969 / 4503599627370496
def cot_pi_20_24_upper : ℚ := -7800463371553939 / 4503599627370496
axiom cot_pi_20_24_bounds :
  ((cot_pi_20_24_lower : ℚ) : ℝ) ≤ cotangentTermV 20 24 ∧
  cotangentTermV 20 24 ≤ ((cot_pi_20_24_upper : ℚ) : ℝ)

def cot_pi_21_24_lower : ℚ := -5436325649948141 / 2251799813685248
def cot_pi_21_24_upper : ℚ := -5436325649948111 / 2251799813685248
axiom cot_pi_21_24_bounds :
  ((cot_pi_21_24_lower : ℚ) : ℝ) ≤ cotangentTermV 21 24 ∧
  cotangentTermV 21 24 ≤ ((cot_pi_21_24_upper : ℚ) : ℝ)

def cot_pi_22_24_lower : ℚ := -2100957828286875 / 562949953421312
def cot_pi_22_24_upper : ℚ := -525239457071713 / 140737488355328
axiom cot_pi_22_24_bounds :
  ((cot_pi_22_24_lower : ℚ) : ℝ) ≤ cotangentTermV 22 24 ∧
  cotangentTermV 22 24 ≤ ((cot_pi_22_24_upper : ℚ) : ℝ)

def cot_pi_23_24_lower : ℚ := -534503677994799 / 70368744177664
def cot_pi_23_24_upper : ℚ := -4276029423958305 / 562949953421312
axiom cot_pi_23_24_bounds :
  ((cot_pi_23_24_lower : ℚ) : ℝ) ≤ cotangentTermV 23 24 ∧
  cotangentTermV 23 24 ≤ ((cot_pi_23_24_upper : ℚ) : ℝ)

def cot_pi_1_25_lower : ℚ := 8912415470506963 / 1125899906842624
def cot_pi_1_25_upper : ℚ := 8912415470506977 / 1125899906842624
axiom cot_pi_1_25_bounds :
  ((cot_pi_1_25_lower : ℚ) : ℝ) ≤ cotangentTermV 1 25 ∧
  cotangentTermV 1 25 ≤ ((cot_pi_1_25_upper : ℚ) : ℝ)

def cot_pi_2_25_lower : ℚ := 8770181235083003 / 2251799813685248
def cot_pi_2_25_upper : ℚ := 8770181235083015 / 2251799813685248
axiom cot_pi_2_25_bounds :
  ((cot_pi_2_25_lower : ℚ) : ℝ) ≤ cotangentTermV 2 25 ∧
  cotangentTermV 2 25 ≤ ((cot_pi_2_25_upper : ℚ) : ℝ)

def cot_pi_3_25_lower : ℚ := 2843698555860045 / 1125899906842624
def cot_pi_3_25_upper : ℚ := 2843698555860049 / 1125899906842624
axiom cot_pi_3_25_bounds :
  ((cot_pi_3_25_lower : ℚ) : ℝ) ≤ cotangentTermV 3 25 ∧
  cotangentTermV 3 25 ≤ ((cot_pi_3_25_upper : ℚ) : ℝ)

def cot_pi_4_25_lower : ℚ := 4096008655322227 / 2251799813685248
def cot_pi_4_25_upper : ℚ := 4096008655322233 / 2251799813685248
axiom cot_pi_4_25_bounds :
  ((cot_pi_4_25_lower : ℚ) : ℝ) ≤ cotangentTermV 4 25 ∧
  cotangentTermV 4 25 ≤ ((cot_pi_4_25_upper : ℚ) : ℝ)

def cot_pi_5_25_lower : ℚ := 6198673104153461 / 4503599627370496
def cot_pi_5_25_upper : ℚ := 6198673104153469 / 4503599627370496
axiom cot_pi_5_25_bounds :
  ((cot_pi_5_25_lower : ℚ) : ℝ) ≤ cotangentTermV 5 25 ∧
  cotangentTermV 5 25 ≤ ((cot_pi_5_25_upper : ℚ) : ℝ)

def cot_pi_6_25_lower : ℚ := 2397923247638305 / 2251799813685248
def cot_pi_6_25_upper : ℚ := 2397923247638309 / 2251799813685248
axiom cot_pi_6_25_bounds :
  ((cot_pi_6_25_lower : ℚ) : ℝ) ≤ cotangentTermV 6 25 ∧
  cotangentTermV 6 25 ≤ ((cot_pi_6_25_upper : ℚ) : ℝ)

def cot_pi_7_25_lower : ℚ := 7451403255231407 / 9007199254740992
def cot_pi_7_25_upper : ℚ := 7451403255231419 / 9007199254740992
axiom cot_pi_7_25_bounds :
  ((cot_pi_7_25_lower : ℚ) : ℝ) ≤ cotangentTermV 7 25 ∧
  cotangentTermV 7 25 ≤ ((cot_pi_7_25_upper : ℚ) : ℝ)

def cot_pi_8_25_lower : ℚ := 714517807985487 / 1125899906842624
def cot_pi_8_25_upper : ℚ := 2858071231941955 / 4503599627370496
axiom cot_pi_8_25_bounds :
  ((cot_pi_8_25_lower : ℚ) : ℝ) ≤ cotangentTermV 8 25 ∧
  cotangentTermV 8 25 ≤ ((cot_pi_8_25_upper : ℚ) : ℝ)

def cot_pi_9_25_lower : ℚ := 8476932486085439 / 18014398509481984
def cot_pi_9_25_upper : ℚ := 8476932486085459 / 18014398509481984
axiom cot_pi_9_25_bounds :
  ((cot_pi_9_25_lower : ℚ) : ℝ) ≤ cotangentTermV 9 25 ∧
  cotangentTermV 9 25 ≤ ((cot_pi_9_25_upper : ℚ) : ℝ)

def cot_pi_10_25_lower : ℚ := 2926616445759701 / 9007199254740992
def cot_pi_10_25_upper : ℚ := 1463308222879853 / 4503599627370496
axiom cot_pi_10_25_bounds :
  ((cot_pi_10_25_lower : ℚ) : ℝ) ≤ cotangentTermV 10 25 ∧
  cotangentTermV 10 25 ≤ ((cot_pi_10_25_upper : ℚ) : ℝ)

def cot_pi_11_25_lower : ℚ := 6872860605029247 / 36028797018963968
def cot_pi_11_25_upper : ℚ := 6872860605029299 / 36028797018963968
axiom cot_pi_11_25_bounds :
  ((cot_pi_11_25_lower : ℚ) : ℝ) ≤ cotangentTermV 11 25 ∧
  cotangentTermV 11 25 ≤ ((cot_pi_11_25_upper : ℚ) : ℝ)

def cot_pi_12_25_lower : ℚ := 4533479551994797 / 72057594037927936
def cot_pi_12_25_upper : ℚ := 4533479551994849 / 72057594037927936
axiom cot_pi_12_25_bounds :
  ((cot_pi_12_25_lower : ℚ) : ℝ) ≤ cotangentTermV 12 25 ∧
  cotangentTermV 12 25 ≤ ((cot_pi_12_25_upper : ℚ) : ℝ)

def cot_pi_13_25_lower : ℚ := -2266739775997415 / 36028797018963968
def cot_pi_13_25_upper : ℚ := -2266739775997367 / 36028797018963968
axiom cot_pi_13_25_bounds :
  ((cot_pi_13_25_lower : ℚ) : ℝ) ≤ cotangentTermV 13 25 ∧
  cotangentTermV 13 25 ≤ ((cot_pi_13_25_upper : ℚ) : ℝ)

def cot_pi_14_25_lower : ℚ := -6872860605029267 / 36028797018963968
def cot_pi_14_25_upper : ℚ := -6872860605029235 / 36028797018963968
axiom cot_pi_14_25_bounds :
  ((cot_pi_14_25_lower : ℚ) : ℝ) ≤ cotangentTermV 14 25 ∧
  cotangentTermV 14 25 ≤ ((cot_pi_14_25_upper : ℚ) : ℝ)

def cot_pi_15_25_lower : ℚ := -731654111439927 / 2251799813685248
def cot_pi_15_25_upper : ℚ := -731654111439923 / 2251799813685248
axiom cot_pi_15_25_bounds :
  ((cot_pi_15_25_lower : ℚ) : ℝ) ≤ cotangentTermV 15 25 ∧
  cotangentTermV 15 25 ≤ ((cot_pi_15_25_upper : ℚ) : ℝ)

def cot_pi_16_25_lower : ℚ := -8476932486085453 / 18014398509481984
def cot_pi_16_25_upper : ℚ := -8476932486085421 / 18014398509481984
axiom cot_pi_16_25_bounds :
  ((cot_pi_16_25_lower : ℚ) : ℝ) ≤ cotangentTermV 16 25 ∧
  cotangentTermV 16 25 ≤ ((cot_pi_16_25_upper : ℚ) : ℝ)

def cot_pi_17_25_lower : ℚ := -5716142463883907 / 9007199254740992
def cot_pi_17_25_upper : ℚ := -5716142463883879 / 9007199254740992
axiom cot_pi_17_25_bounds :
  ((cot_pi_17_25_lower : ℚ) : ℝ) ≤ cotangentTermV 17 25 ∧
  cotangentTermV 17 25 ≤ ((cot_pi_17_25_upper : ℚ) : ℝ)

def cot_pi_18_25_lower : ℚ := -3725701627615709 / 4503599627370496
def cot_pi_18_25_upper : ℚ := -232856351725981 / 281474976710656
axiom cot_pi_18_25_bounds :
  ((cot_pi_18_25_lower : ℚ) : ℝ) ≤ cotangentTermV 18 25 ∧
  cotangentTermV 18 25 ≤ ((cot_pi_18_25_upper : ℚ) : ℝ)

def cot_pi_19_25_lower : ℚ := -2397923247638311 / 2251799813685248
def cot_pi_19_25_upper : ℚ := -599480811909575 / 562949953421312
axiom cot_pi_19_25_bounds :
  ((cot_pi_19_25_lower : ℚ) : ℝ) ≤ cotangentTermV 19 25 ∧
  cotangentTermV 19 25 ≤ ((cot_pi_19_25_upper : ℚ) : ℝ)

def cot_pi_20_25_lower : ℚ := -6198673104153469 / 4503599627370496
def cot_pi_20_25_upper : ℚ := -6198673104153459 / 4503599627370496
axiom cot_pi_20_25_bounds :
  ((cot_pi_20_25_lower : ℚ) : ℝ) ≤ cotangentTermV 20 25 ∧
  cotangentTermV 20 25 ≤ ((cot_pi_20_25_upper : ℚ) : ℝ)

def cot_pi_21_25_lower : ℚ := -8192017310644469 / 4503599627370496
def cot_pi_21_25_upper : ℚ := -8192017310644417 / 4503599627370496
axiom cot_pi_21_25_bounds :
  ((cot_pi_21_25_lower : ℚ) : ℝ) ≤ cotangentTermV 21 25 ∧
  cotangentTermV 21 25 ≤ ((cot_pi_21_25_upper : ℚ) : ℝ)

def cot_pi_22_25_lower : ℚ := -2843698555860053 / 1125899906842624
def cot_pi_22_25_upper : ℚ := -1421849277930015 / 562949953421312
axiom cot_pi_22_25_bounds :
  ((cot_pi_22_25_lower : ℚ) : ℝ) ≤ cotangentTermV 22 25 ∧
  cotangentTermV 22 25 ≤ ((cot_pi_22_25_upper : ℚ) : ℝ)

def cot_pi_23_25_lower : ℚ := -4385090617541519 / 1125899906842624
def cot_pi_23_25_upper : ℚ := -4385090617541471 / 1125899906842624
axiom cot_pi_23_25_bounds :
  ((cot_pi_23_25_lower : ℚ) : ℝ) ≤ cotangentTermV 23 25 ∧
  cotangentTermV 23 25 ≤ ((cot_pi_23_25_upper : ℚ) : ℝ)

def cot_pi_24_25_lower : ℚ := -4456207735253499 / 562949953421312
def cot_pi_24_25_upper : ℚ := -4456207735253447 / 562949953421312
axiom cot_pi_24_25_bounds :
  ((cot_pi_24_25_lower : ℚ) : ℝ) ≤ cotangentTermV 24 25 ∧
  cotangentTermV 24 25 ≤ ((cot_pi_24_25_upper : ℚ) : ℝ)

def cot_pi_1_26_lower : ℚ := 1159077496681229 / 140737488355328
def cot_pi_1_26_upper : ℚ := 2318154993362461 / 281474976710656
axiom cot_pi_1_26_bounds :
  ((cot_pi_1_26_lower : ℚ) : ℝ) ≤ cotangentTermV 1 26 ∧
  cotangentTermV 1 26 ≤ ((cot_pi_1_26_upper : ℚ) : ℝ)

def cot_pi_2_26_lower : ℚ := 4567955486925621 / 1125899906842624
def cot_pi_2_26_upper : ℚ := 4567955486925627 / 1125899906842624
axiom cot_pi_2_26_bounds :
  ((cot_pi_2_26_lower : ℚ) : ℝ) ≤ cotangentTermV 2 26 ∧
  cotangentTermV 2 26 ≤ ((cot_pi_2_26_upper : ℚ) : ℝ)

def cot_pi_3_26_lower : ℚ := 2968754066859689 / 1125899906842624
def cot_pi_3_26_upper : ℚ := 2968754066859693 / 1125899906842624
axiom cot_pi_3_26_bounds :
  ((cot_pi_3_26_lower : ℚ) : ℝ) ≤ cotangentTermV 3 26 ∧
  cotangentTermV 3 26 ≤ ((cot_pi_3_26_upper : ℚ) : ℝ)

def cot_pi_4_26_lower : ℚ := 4290446083899149 / 2251799813685248
def cot_pi_4_26_upper : ℚ := 2145223041949577 / 1125899906842624
axiom cot_pi_4_26_bounds :
  ((cot_pi_4_26_lower : ℚ) : ℝ) ≤ cotangentTermV 4 26 ∧
  cotangentTermV 4 26 ≤ ((cot_pi_4_26_upper : ℚ) : ℝ)

def cot_pi_5_26_lower : ℚ := 3262295234036673 / 2251799813685248
def cot_pi_5_26_upper : ℚ := 1631147617018339 / 1125899906842624
axiom cot_pi_5_26_bounds :
  ((cot_pi_5_26_lower : ℚ) : ℝ) ≤ cotangentTermV 5 26 ∧
  cotangentTermV 5 26 ≤ ((cot_pi_5_26_upper : ℚ) : ℝ)

def cot_pi_6_26_lower : ℚ := 5083513109760297 / 4503599627370496
def cot_pi_6_26_upper : ℚ := 5083513109760305 / 4503599627370496
axiom cot_pi_6_26_bounds :
  ((cot_pi_6_26_lower : ℚ) : ℝ) ≤ cotangentTermV 6 26 ∧
  cotangentTermV 6 26 ≤ ((cot_pi_6_26_upper : ℚ) : ℝ)

def cot_pi_7_26_lower : ℚ := 997460278242895 / 1125899906842624
def cot_pi_7_26_upper : ℚ := 1994920556485793 / 2251799813685248
axiom cot_pi_7_26_bounds :
  ((cot_pi_7_26_lower : ℚ) : ℝ) ≤ cotangentTermV 7 26 ∧
  cotangentTermV 7 26 ≤ ((cot_pi_7_26_upper : ℚ) : ℝ)

def cot_pi_8_26_lower : ℚ := 3108610372237027 / 4503599627370496
def cot_pi_8_26_upper : ℚ := 388576296529629 / 562949953421312
axiom cot_pi_8_26_bounds :
  ((cot_pi_8_26_lower : ℚ) : ℝ) ≤ cotangentTermV 8 26 ∧
  cotangentTermV 8 26 ≤ ((cot_pi_8_26_upper : ℚ) : ℝ)

def cot_pi_9_26_lower : ℚ := 2363671423324241 / 4503599627370496
def cot_pi_9_26_upper : ℚ := 2363671423324247 / 4503599627370496
axiom cot_pi_9_26_bounds :
  ((cot_pi_9_26_lower : ℚ) : ℝ) ≤ cotangentTermV 9 26 ∧
  cotangentTermV 9 26 ≤ ((cot_pi_9_26_upper : ℚ) : ℝ)

def cot_pi_10_26_lower : ℚ := 6831960191672637 / 18014398509481984
def cot_pi_10_26_upper : ℚ := 6831960191672655 / 18014398509481984
axiom cot_pi_10_26_bounds :
  ((cot_pi_10_26_lower : ℚ) : ℝ) ≤ cotangentTermV 10 26 ∧
  cotangentTermV 10 26 ≤ ((cot_pi_10_26_upper : ℚ) : ℝ)

def cot_pi_11_26_lower : ℚ := 4440150448423553 / 18014398509481984
def cot_pi_11_26_upper : ℚ := 4440150448423579 / 18014398509481984
axiom cot_pi_11_26_bounds :
  ((cot_pi_11_26_lower : ℚ) : ℝ) ≤ cotangentTermV 11 26 ∧
  cotangentTermV 11 26 ≤ ((cot_pi_11_26_upper : ℚ) : ℝ)

def cot_pi_12_26_lower : ℚ := 2187343993577433 / 18014398509481984
def cot_pi_12_26_upper : ℚ := 4374687987154893 / 36028797018963968
axiom cot_pi_12_26_bounds :
  ((cot_pi_12_26_lower : ℚ) : ℝ) ≤ cotangentTermV 12 26 ∧
  cotangentTermV 12 26 ≤ ((cot_pi_12_26_upper : ℚ) : ℝ)

def cot_pi_13_26_lower : ℚ := -48924515 / 151115727451828646838272
def cot_pi_13_26_upper : ℚ := 538123663 / 604462909807314587353088
axiom cot_pi_13_26_bounds :
  ((cot_pi_13_26_lower : ℚ) : ℝ) ≤ cotangentTermV 13 26 ∧
  cotangentTermV 13 26 ≤ ((cot_pi_13_26_upper : ℚ) : ℝ)

def cot_pi_14_26_lower : ℚ := -8749375974309761 / 72057594037927936
def cot_pi_14_26_upper : ℚ := -8749375974309705 / 72057594037927936
axiom cot_pi_14_26_bounds :
  ((cot_pi_14_26_lower : ℚ) : ℝ) ≤ cotangentTermV 14 26 ∧
  cotangentTermV 14 26 ≤ ((cot_pi_14_26_upper : ℚ) : ℝ)

def cot_pi_15_26_lower : ℚ := -8880300896847137 / 36028797018963968
def cot_pi_15_26_upper : ℚ := -8880300896847083 / 36028797018963968
axiom cot_pi_15_26_bounds :
  ((cot_pi_15_26_lower : ℚ) : ℝ) ≤ cotangentTermV 15 26 ∧
  cotangentTermV 15 26 ≤ ((cot_pi_15_26_upper : ℚ) : ℝ)

def cot_pi_16_26_lower : ℚ := -6831960191672649 / 18014398509481984
def cot_pi_16_26_upper : ℚ := -6831960191672629 / 18014398509481984
axiom cot_pi_16_26_bounds :
  ((cot_pi_16_26_lower : ℚ) : ℝ) ≤ cotangentTermV 16 26 ∧
  cotangentTermV 16 26 ≤ ((cot_pi_16_26_upper : ℚ) : ℝ)

def cot_pi_17_26_lower : ℚ := -2363671423324247 / 4503599627370496
def cot_pi_17_26_upper : ℚ := -2363671423324235 / 4503599627370496
axiom cot_pi_17_26_bounds :
  ((cot_pi_17_26_lower : ℚ) : ℝ) ≤ cotangentTermV 17 26 ∧
  cotangentTermV 17 26 ≤ ((cot_pi_17_26_upper : ℚ) : ℝ)

def cot_pi_18_26_lower : ℚ := -3108610372237033 / 4503599627370496
def cot_pi_18_26_upper : ℚ := -1554305186118511 / 2251799813685248
axiom cot_pi_18_26_bounds :
  ((cot_pi_18_26_lower : ℚ) : ℝ) ≤ cotangentTermV 18 26 ∧
  cotangentTermV 18 26 ≤ ((cot_pi_18_26_upper : ℚ) : ℝ)

def cot_pi_19_26_lower : ℚ := -7979682225943179 / 9007199254740992
def cot_pi_19_26_upper : ℚ := -7979682225943143 / 9007199254740992
axiom cot_pi_19_26_bounds :
  ((cot_pi_19_26_lower : ℚ) : ℝ) ≤ cotangentTermV 19 26 ∧
  cotangentTermV 19 26 ≤ ((cot_pi_19_26_upper : ℚ) : ℝ)

def cot_pi_20_26_lower : ℚ := -5083513109760305 / 4503599627370496
def cot_pi_20_26_upper : ℚ := -5083513109760287 / 4503599627370496
axiom cot_pi_20_26_bounds :
  ((cot_pi_20_26_lower : ℚ) : ℝ) ≤ cotangentTermV 20 26 ∧
  cotangentTermV 20 26 ≤ ((cot_pi_20_26_upper : ℚ) : ℝ)

def cot_pi_21_26_lower : ℚ := -3262295234036679 / 2251799813685248
def cot_pi_21_26_upper : ℚ := -3262295234036659 / 2251799813685248
axiom cot_pi_21_26_bounds :
  ((cot_pi_21_26_lower : ℚ) : ℝ) ≤ cotangentTermV 21 26 ∧
  cotangentTermV 21 26 ≤ ((cot_pi_21_26_upper : ℚ) : ℝ)

def cot_pi_22_26_lower : ℚ := -4290446083899159 / 2251799813685248
def cot_pi_22_26_upper : ℚ := -4290446083899131 / 2251799813685248
axiom cot_pi_22_26_bounds :
  ((cot_pi_22_26_lower : ℚ) : ℝ) ≤ cotangentTermV 22 26 ∧
  cotangentTermV 22 26 ≤ ((cot_pi_22_26_upper : ℚ) : ℝ)

def cot_pi_23_26_lower : ℚ := -5937508133719393 / 2251799813685248
def cot_pi_23_26_upper : ℚ := -5937508133719361 / 2251799813685248
axiom cot_pi_23_26_bounds :
  ((cot_pi_23_26_lower : ℚ) : ℝ) ≤ cotangentTermV 23 26 ∧
  cotangentTermV 23 26 ≤ ((cot_pi_23_26_upper : ℚ) : ℝ)

def cot_pi_24_26_lower : ℚ := -4567955486925631 / 1125899906842624
def cot_pi_24_26_upper : ℚ := -4567955486925601 / 1125899906842624
axiom cot_pi_24_26_bounds :
  ((cot_pi_24_26_lower : ℚ) : ℝ) ≤ cotangentTermV 24 26 ∧
  cotangentTermV 24 26 ≤ ((cot_pi_24_26_upper : ℚ) : ℝ)

def cot_pi_25_26_lower : ℚ := -1159077496681233 / 140737488355328
def cot_pi_25_26_upper : ℚ := -2318154993362417 / 281474976710656
axiom cot_pi_25_26_bounds :
  ((cot_pi_25_26_lower : ℚ) : ℝ) ≤ cotangentTermV 25 26 ∧
  cotangentTermV 25 26 ≤ ((cot_pi_25_26_upper : ℚ) : ℝ)

def cot_pi_1_27_lower : ℚ := 602043082732783 / 70368744177664
def cot_pi_1_27_upper : ℚ := 2408172330931135 / 281474976710656
axiom cot_pi_1_27_bounds :
  ((cot_pi_1_27_lower : ℚ) : ℝ) ≤ cotangentTermV 1 27 ∧
  cotangentTermV 1 27 ≤ ((cot_pi_1_27_upper : ℚ) : ℝ)

def cot_pi_2_27_lower : ℚ := 2375272624586765 / 562949953421312
def cot_pi_2_27_upper : ℚ := 148454539036673 / 35184372088832
axiom cot_pi_2_27_bounds :
  ((cot_pi_2_27_lower : ℚ) : ℝ) ≤ cotangentTermV 2 27 ∧
  cotangentTermV 2 27 ≤ ((cot_pi_2_27_upper : ℚ) : ℝ)

def cot_pi_3_27_lower : ℚ := 1546692285308085 / 562949953421312
def cot_pi_3_27_upper : ℚ := 1546692285308087 / 562949953421312
axiom cot_pi_3_27_bounds :
  ((cot_pi_3_27_lower : ℚ) : ℝ) ≤ cotangentTermV 3 27 ∧
  cotangentTermV 3 27 ≤ ((cot_pi_3_27_upper : ℚ) : ℝ)

def cot_pi_4_27_lower : ℚ := 8967404138681815 / 4503599627370496
def cot_pi_4_27_upper : ℚ := 8967404138681825 / 4503599627370496
axiom cot_pi_4_27_bounds :
  ((cot_pi_4_27_lower : ℚ) : ℝ) ≤ cotangentTermV 4 27 ∧
  cotangentTermV 4 27 ≤ ((cot_pi_4_27_upper : ℚ) : ℝ)

def cot_pi_5_27_lower : ℚ := 6847390572874411 / 4503599627370496
def cot_pi_5_27_upper : ℚ := 6847390572874423 / 4503599627370496
axiom cot_pi_5_27_bounds :
  ((cot_pi_5_27_lower : ℚ) : ℝ) ≤ cotangentTermV 5 27 ∧
  cotangentTermV 5 27 ≤ ((cot_pi_5_27_upper : ℚ) : ℝ)

def cot_pi_6_27_lower : ℚ := 2683590517762365 / 2251799813685248
def cot_pi_6_27_upper : ℚ := 2683590517762369 / 2251799813685248
axiom cot_pi_6_27_bounds :
  ((cot_pi_6_27_lower : ℚ) : ℝ) ≤ cotangentTermV 6 27 ∧
  cotangentTermV 6 27 ≤ ((cot_pi_6_27_upper : ℚ) : ℝ)

def cot_pi_7_27_lower : ℚ := 4248927109742355 / 4503599627370496
def cot_pi_7_27_upper : ℚ := 2124463554871181 / 2251799813685248
axiom cot_pi_7_27_bounds :
  ((cot_pi_7_27_lower : ℚ) : ℝ) ≤ cotangentTermV 7 27 ∧
  cotangentTermV 7 27 ≤ ((cot_pi_7_27_upper : ℚ) : ℝ)

def cot_pi_8_27_lower : ℚ := 6705611395767349 / 9007199254740992
def cot_pi_8_27_upper : ℚ := 6705611395767361 / 9007199254740992
axiom cot_pi_8_27_bounds :
  ((cot_pi_8_27_lower : ℚ) : ℝ) ≤ cotangentTermV 8 27 ∧
  cotangentTermV 8 27 ≤ ((cot_pi_8_27_upper : ℚ) : ℝ)

def cot_pi_9_27_lower : ℚ := 5200308914369303 / 9007199254740992
def cot_pi_9_27_upper : ℚ := 5200308914369315 / 9007199254740992
axiom cot_pi_9_27_bounds :
  ((cot_pi_9_27_lower : ℚ) : ℝ) ≤ cotangentTermV 9 27 ∧
  cotangentTermV 9 27 ≤ ((cot_pi_9_27_upper : ℚ) : ℝ)

def cot_pi_10_27_lower : ℚ := 1942663250379603 / 4503599627370496
def cot_pi_10_27_upper : ℚ := 242832906297451 / 562949953421312
axiom cot_pi_10_27_bounds :
  ((cot_pi_10_27_lower : ℚ) : ℝ) ≤ cotangentTermV 10 27 ∧
  cotangentTermV 10 27 ≤ ((cot_pi_10_27_upper : ℚ) : ℝ)

def cot_pi_11_27_lower : ℚ := 5393156878489699 / 18014398509481984
def cot_pi_11_27_upper : ℚ := 5393156878489727 / 18014398509481984
axiom cot_pi_11_27_bounds :
  ((cot_pi_11_27_lower : ℚ) : ℝ) ≤ cotangentTermV 11 27 ∧
  cotangentTermV 11 27 ≤ ((cot_pi_11_27_upper : ℚ) : ℝ)

def cot_pi_12_27_lower : ℚ := 6352848996912047 / 36028797018963968
def cot_pi_12_27_upper : ℚ := 6352848996912077 / 36028797018963968
axiom cot_pi_12_27_bounds :
  ((cot_pi_12_27_lower : ℚ) : ℝ) ≤ cotangentTermV 12 27 ∧
  cotangentTermV 12 27 ≤ ((cot_pi_12_27_upper : ℚ) : ℝ)

def cot_pi_13_27_lower : ℚ := 2098438464276949 / 36028797018963968
def cot_pi_13_27_upper : ℚ := 4196876928553987 / 72057594037927936
axiom cot_pi_13_27_bounds :
  ((cot_pi_13_27_lower : ℚ) : ℝ) ≤ cotangentTermV 13 27 ∧
  cotangentTermV 13 27 ≤ ((cot_pi_13_27_upper : ℚ) : ℝ)

def cot_pi_14_27_lower : ℚ := -8393753857107855 / 144115188075855872
def cot_pi_14_27_upper : ℚ := -8393753857107751 / 144115188075855872
axiom cot_pi_14_27_bounds :
  ((cot_pi_14_27_lower : ℚ) : ℝ) ≤ cotangentTermV 14 27 ∧
  cotangentTermV 14 27 ≤ ((cot_pi_14_27_upper : ℚ) : ℝ)

def cot_pi_15_27_lower : ℚ := -1588212249228019 / 9007199254740992
def cot_pi_15_27_upper : ℚ := -794106124614003 / 4503599627370496
axiom cot_pi_15_27_bounds :
  ((cot_pi_15_27_lower : ℚ) : ℝ) ≤ cotangentTermV 15 27 ∧
  cotangentTermV 15 27 ≤ ((cot_pi_15_27_upper : ℚ) : ℝ)

def cot_pi_16_27_lower : ℚ := -5393156878489711 / 18014398509481984
def cot_pi_16_27_upper : ℚ := -5393156878489691 / 18014398509481984
axiom cot_pi_16_27_bounds :
  ((cot_pi_16_27_lower : ℚ) : ℝ) ≤ cotangentTermV 16 27 ∧
  cotangentTermV 16 27 ≤ ((cot_pi_16_27_upper : ℚ) : ℝ)

def cot_pi_17_27_lower : ℚ := -7770653001518431 / 18014398509481984
def cot_pi_17_27_upper : ℚ := -7770653001518397 / 18014398509481984
axiom cot_pi_17_27_bounds :
  ((cot_pi_17_27_lower : ℚ) : ℝ) ≤ cotangentTermV 17 27 ∧
  cotangentTermV 17 27 ≤ ((cot_pi_17_27_upper : ℚ) : ℝ)

def cot_pi_18_27_lower : ℚ := -2600154457184657 / 4503599627370496
def cot_pi_18_27_upper : ℚ := -325019307148081 / 562949953421312
axiom cot_pi_18_27_bounds :
  ((cot_pi_18_27_lower : ℚ) : ℝ) ≤ cotangentTermV 18 27 ∧
  cotangentTermV 18 27 ≤ ((cot_pi_18_27_upper : ℚ) : ℝ)

def cot_pi_19_27_lower : ℚ := -104775178058865 / 140737488355328
def cot_pi_19_27_upper : ℚ := -3352805697883671 / 4503599627370496
axiom cot_pi_19_27_bounds :
  ((cot_pi_19_27_lower : ℚ) : ℝ) ≤ cotangentTermV 19 27 ∧
  cotangentTermV 19 27 ≤ ((cot_pi_19_27_upper : ℚ) : ℝ)

def cot_pi_20_27_lower : ℚ := -4248927109742363 / 4503599627370496
def cot_pi_20_27_upper : ℚ := -4248927109742349 / 4503599627370496
axiom cot_pi_20_27_bounds :
  ((cot_pi_20_27_lower : ℚ) : ℝ) ≤ cotangentTermV 20 27 ∧
  cotangentTermV 20 27 ≤ ((cot_pi_20_27_upper : ℚ) : ℝ)

def cot_pi_21_27_lower : ℚ := -5367181035524741 / 4503599627370496
def cot_pi_21_27_upper : ℚ := -5367181035524711 / 4503599627370496
axiom cot_pi_21_27_bounds :
  ((cot_pi_21_27_lower : ℚ) : ℝ) ≤ cotangentTermV 21 27 ∧
  cotangentTermV 21 27 ≤ ((cot_pi_21_27_upper : ℚ) : ℝ)

def cot_pi_22_27_lower : ℚ := -6847390572874429 / 4503599627370496
def cot_pi_22_27_upper : ℚ := -6847390572874387 / 4503599627370496
axiom cot_pi_22_27_bounds :
  ((cot_pi_22_27_lower : ℚ) : ℝ) ≤ cotangentTermV 22 27 ∧
  cotangentTermV 22 27 ≤ ((cot_pi_22_27_upper : ℚ) : ℝ)

def cot_pi_23_27_lower : ℚ := -8967404138681835 / 4503599627370496
def cot_pi_23_27_upper : ℚ := -8967404138681775 / 4503599627370496
axiom cot_pi_23_27_bounds :
  ((cot_pi_23_27_lower : ℚ) : ℝ) ≤ cotangentTermV 23 27 ∧
  cotangentTermV 23 27 ≤ ((cot_pi_23_27_upper : ℚ) : ℝ)

def cot_pi_24_27_lower : ℚ := -1546692285308089 / 562949953421312
def cot_pi_24_27_upper : ℚ := -3093384570616163 / 1125899906842624
axiom cot_pi_24_27_bounds :
  ((cot_pi_24_27_lower : ℚ) : ℝ) ≤ cotangentTermV 24 27 ∧
  cotangentTermV 24 27 ≤ ((cot_pi_24_27_upper : ℚ) : ℝ)

def cot_pi_25_27_lower : ℚ := -4750545249173547 / 1125899906842624
def cot_pi_25_27_upper : ℚ := -4750545249173493 / 1125899906842624
axiom cot_pi_25_27_bounds :
  ((cot_pi_25_27_lower : ℚ) : ℝ) ≤ cotangentTermV 25 27 ∧
  cotangentTermV 25 27 ≤ ((cot_pi_25_27_upper : ℚ) : ℝ)

def cot_pi_26_27_lower : ℚ := -4816344661862295 / 562949953421312
def cot_pi_26_27_upper : ℚ := -4816344661862191 / 562949953421312
axiom cot_pi_26_27_bounds :
  ((cot_pi_26_27_lower : ℚ) : ℝ) ≤ cotangentTermV 26 27 ∧
  cotangentTermV 26 27 ≤ ((cot_pi_26_27_upper : ℚ) : ℝ)

def cot_pi_1_28_lower : ℚ := 1249079756684233 / 140737488355328
def cot_pi_1_28_upper : ℚ := 2498159513368469 / 281474976710656
axiom cot_pi_1_28_bounds :
  ((cot_pi_1_28_lower : ℚ) : ℝ) ≤ cotangentTermV 1 28 ∧
  cotangentTermV 1 28 ≤ ((cot_pi_1_28_upper : ℚ) : ℝ)

def cot_pi_2_28_lower : ℚ := 4932889800468321 / 1125899906842624
def cot_pi_2_28_upper : ℚ := 4932889800468327 / 1125899906842624
axiom cot_pi_2_28_bounds :
  ((cot_pi_2_28_lower : ℚ) : ℝ) ≤ cotangentTermV 2 28 ∧
  cotangentTermV 2 28 ≤ ((cot_pi_2_28_upper : ℚ) : ℝ)

def cot_pi_3_28_lower : ℚ := 6435274142862573 / 2251799813685248
def cot_pi_3_28_upper : ℚ := 6435274142862579 / 2251799813685248
axiom cot_pi_3_28_bounds :
  ((cot_pi_3_28_lower : ℚ) : ℝ) ≤ cotangentTermV 3 28 ∧
  cotangentTermV 3 28 ≤ ((cot_pi_3_28_upper : ℚ) : ℝ)

def cot_pi_4_28_lower : ℚ := 4675910493915015 / 2251799813685248
def cot_pi_4_28_upper : ℚ := 4675910493915021 / 2251799813685248
axiom cot_pi_4_28_bounds :
  ((cot_pi_4_28_lower : ℚ) : ℝ) ≤ cotangentTermV 4 28 ∧
  cotangentTermV 4 28 ≤ ((cot_pi_4_28_upper : ℚ) : ℝ)

def cot_pi_5_28_lower : ℚ := 3583718873781247 / 2251799813685248
def cot_pi_5_28_upper : ℚ := 3583718873781251 / 2251799813685248
axiom cot_pi_5_28_bounds :
  ((cot_pi_5_28_lower : ℚ) : ℝ) ≤ cotangentTermV 5 28 ∧
  cotangentTermV 5 28 ≤ ((cot_pi_5_28_upper : ℚ) : ℝ)

def cot_pi_6_28_lower : ℚ := 5647335309435131 / 4503599627370496
def cot_pi_6_28_upper : ℚ := 5647335309435137 / 4503599627370496
axiom cot_pi_6_28_bounds :
  ((cot_pi_6_28_lower : ℚ) : ℝ) ≤ cotangentTermV 6 28 ∧
  cotangentTermV 6 28 ≤ ((cot_pi_6_28_upper : ℚ) : ℝ)

def cot_pi_7_28_lower : ℚ := 2251799813685247 / 2251799813685248
def cot_pi_7_28_upper : ℚ := 2251799813685249 / 2251799813685248
axiom cot_pi_7_28_bounds :
  ((cot_pi_7_28_lower : ℚ) : ℝ) ≤ cotangentTermV 7 28 ∧
  cotangentTermV 7 28 ≤ ((cot_pi_7_28_upper : ℚ) : ℝ)

def cot_pi_8_28_lower : ℚ := 3591500857008679 / 4503599627370496
def cot_pi_8_28_upper : ℚ := 3591500857008683 / 4503599627370496
axiom cot_pi_8_28_bounds :
  ((cot_pi_8_28_lower : ℚ) : ℝ) ≤ cotangentTermV 8 28 ∧
  cotangentTermV 8 28 ≤ ((cot_pi_8_28_upper : ℚ) : ℝ)

def cot_pi_9_28_lower : ℚ := 1414899599968573 / 2251799813685248
def cot_pi_9_28_upper : ℚ := 1414899599968575 / 2251799813685248
axiom cot_pi_9_28_bounds :
  ((cot_pi_9_28_lower : ℚ) : ℝ) ≤ cotangentTermV 9 28 ∧
  cotangentTermV 9 28 ≤ ((cot_pi_9_28_upper : ℚ) : ℝ)

def cot_pi_10_28_lower : ℚ := 4337638547625347 / 9007199254740992
def cot_pi_10_28_upper : ℚ := 542204818453169 / 1125899906842624
axiom cot_pi_10_28_bounds :
  ((cot_pi_10_28_lower : ℚ) : ℝ) ≤ cotangentTermV 10 28 ∧
  cotangentTermV 10 28 ≤ ((cot_pi_10_28_upper : ℚ) : ℝ)

def cot_pi_11_28_lower : ℚ := 1575877666854881 / 4503599627370496
def cot_pi_11_28_upper : ℚ := 196984708356861 / 562949953421312
axiom cot_pi_11_28_bounds :
  ((cot_pi_11_28_lower : ℚ) : ℝ) ≤ cotangentTermV 11 28 ∧
  cotangentTermV 11 28 ≤ ((cot_pi_11_28_upper : ℚ) : ℝ)

def cot_pi_12_28_lower : ℚ := 513958613106613 / 2251799813685248
def cot_pi_12_28_upper : ℚ := 4111668904852911 / 18014398509481984
axiom cot_pi_12_28_bounds :
  ((cot_pi_12_28_lower : ℚ) : ℝ) ≤ cotangentTermV 12 28 ∧
  cotangentTermV 12 28 ≤ ((cot_pi_12_28_upper : ℚ) : ℝ)

def cot_pi_13_28_lower : ℚ := 8118940962382029 / 72057594037927936
def cot_pi_13_28_upper : ℚ := 8118940962382121 / 72057594037927936
axiom cot_pi_13_28_bounds :
  ((cot_pi_13_28_lower : ℚ) : ℝ) ≤ cotangentTermV 13 28 ∧
  cotangentTermV 13 28 ≤ ((cot_pi_13_28_upper : ℚ) : ℝ)

def cot_pi_14_28_lower : ℚ := -488112137 / 9671406556917033397649408
def cot_pi_14_28_upper : ℚ := 1671954447 / 9671406556917033397649408
axiom cot_pi_14_28_bounds :
  ((cot_pi_14_28_lower : ℚ) : ℝ) ≤ cotangentTermV 14 28 ∧
  cotangentTermV 14 28 ≤ ((cot_pi_14_28_upper : ℚ) : ℝ)

def cot_pi_15_28_lower : ℚ := -31714613134305 / 281474976710656
def cot_pi_15_28_upper : ℚ := -4059470481190993 / 36028797018963968
axiom cot_pi_15_28_bounds :
  ((cot_pi_15_28_lower : ℚ) : ℝ) ≤ cotangentTermV 15 28 ∧
  cotangentTermV 15 28 ≤ ((cot_pi_15_28_upper : ℚ) : ℝ)

def cot_pi_16_28_lower : ℚ := -8223337809705817 / 36028797018963968
def cot_pi_16_28_upper : ℚ := -8223337809705801 / 36028797018963968
axiom cot_pi_16_28_bounds :
  ((cot_pi_16_28_lower : ℚ) : ℝ) ≤ cotangentTermV 16 28 ∧
  cotangentTermV 16 28 ≤ ((cot_pi_16_28_upper : ℚ) : ℝ)

def cot_pi_17_28_lower : ℚ := -3151755333709771 / 9007199254740992
def cot_pi_17_28_upper : ℚ := -787938833427439 / 2251799813685248
axiom cot_pi_17_28_bounds :
  ((cot_pi_17_28_lower : ℚ) : ℝ) ≤ cotangentTermV 17 28 ∧
  cotangentTermV 17 28 ≤ ((cot_pi_17_28_upper : ℚ) : ℝ)

def cot_pi_18_28_lower : ℚ := -4337638547625351 / 9007199254740992
def cot_pi_18_28_upper : ℚ := -4337638547625345 / 9007199254740992
axiom cot_pi_18_28_bounds :
  ((cot_pi_18_28_lower : ℚ) : ℝ) ≤ cotangentTermV 18 28 ∧
  cotangentTermV 18 28 ≤ ((cot_pi_18_28_upper : ℚ) : ℝ)

def cot_pi_19_28_lower : ℚ := -5659598399874303 / 9007199254740992
def cot_pi_19_28_upper : ℚ := -5659598399874275 / 9007199254740992
axiom cot_pi_19_28_bounds :
  ((cot_pi_19_28_lower : ℚ) : ℝ) ≤ cotangentTermV 19 28 ∧
  cotangentTermV 19 28 ≤ ((cot_pi_19_28_upper : ℚ) : ℝ)

def cot_pi_20_28_lower : ℚ := -3591500857008683 / 4503599627370496
def cot_pi_20_28_upper : ℚ := -3591500857008677 / 4503599627370496
axiom cot_pi_20_28_bounds :
  ((cot_pi_20_28_lower : ℚ) : ℝ) ≤ cotangentTermV 20 28 ∧
  cotangentTermV 20 28 ≤ ((cot_pi_20_28_upper : ℚ) : ℝ)

def cot_pi_21_28_lower : ℚ := -562949953421313 / 562949953421312
def cot_pi_21_28_upper : ℚ := -9007199254740959 / 9007199254740992
axiom cot_pi_21_28_bounds :
  ((cot_pi_21_28_lower : ℚ) : ℝ) ≤ cotangentTermV 21 28 ∧
  cotangentTermV 21 28 ≤ ((cot_pi_21_28_upper : ℚ) : ℝ)

def cot_pi_22_28_lower : ℚ := -705916913679393 / 562949953421312
def cot_pi_22_28_upper : ℚ := -705916913679389 / 562949953421312
axiom cot_pi_22_28_bounds :
  ((cot_pi_22_28_lower : ℚ) : ℝ) ≤ cotangentTermV 22 28 ∧
  cotangentTermV 22 28 ≤ ((cot_pi_22_28_upper : ℚ) : ℝ)

def cot_pi_23_28_lower : ℚ := -3583718873781255 / 2251799813685248
def cot_pi_23_28_upper : ℚ := -3583718873781233 / 2251799813685248
axiom cot_pi_23_28_bounds :
  ((cot_pi_23_28_lower : ℚ) : ℝ) ≤ cotangentTermV 23 28 ∧
  cotangentTermV 23 28 ≤ ((cot_pi_23_28_upper : ℚ) : ℝ)

def cot_pi_24_28_lower : ℚ := -2337955246957511 / 1125899906842624
def cot_pi_24_28_upper : ℚ := -1168977623478753 / 562949953421312
axiom cot_pi_24_28_bounds :
  ((cot_pi_24_28_lower : ℚ) : ℝ) ≤ cotangentTermV 24 28 ∧
  cotangentTermV 24 28 ≤ ((cot_pi_24_28_upper : ℚ) : ℝ)

def cot_pi_25_28_lower : ℚ := -6435274142862591 / 2251799813685248
def cot_pi_25_28_upper : ℚ := -6435274142862537 / 2251799813685248
axiom cot_pi_25_28_bounds :
  ((cot_pi_25_28_lower : ℚ) : ℝ) ≤ cotangentTermV 25 28 ∧
  cotangentTermV 25 28 ≤ ((cot_pi_25_28_upper : ℚ) : ℝ)

def cot_pi_26_28_lower : ℚ := -4932889800468339 / 1125899906842624
def cot_pi_26_28_upper : ℚ := -4932889800468283 / 1125899906842624
axiom cot_pi_26_28_bounds :
  ((cot_pi_26_28_lower : ℚ) : ℝ) ≤ cotangentTermV 26 28 ∧
  cotangentTermV 26 28 ≤ ((cot_pi_26_28_upper : ℚ) : ℝ)

def cot_pi_27_28_lower : ℚ := -1249079756684241 / 140737488355328
def cot_pi_27_28_upper : ℚ := -2498159513368427 / 281474976710656
axiom cot_pi_27_28_bounds :
  ((cot_pi_27_28_lower : ℚ) : ℝ) ≤ cotangentTermV 27 28 ∧
  cotangentTermV 27 28 ≤ ((cot_pi_27_28_upper : ℚ) : ℝ)

def cot_pi_1_29_lower : ℚ := 5176239340982367 / 562949953421312
def cot_pi_1_29_upper : ℚ := 5176239340982373 / 562949953421312
axiom cot_pi_1_29_bounds :
  ((cot_pi_1_29_lower : ℚ) : ℝ) ≤ cotangentTermV 1 29 ∧
  cotangentTermV 1 29 ≤ ((cot_pi_1_29_upper : ℚ) : ℝ)

def cot_pi_2_29_lower : ℚ := 2557507421985987 / 562949953421312
def cot_pi_2_29_upper : ℚ := 1278753710992995 / 281474976710656
axiom cot_pi_2_29_bounds :
  ((cot_pi_2_29_lower : ℚ) : ℝ) ≤ cotangentTermV 2 29 ∧
  cotangentTermV 2 29 ≤ ((cot_pi_2_29_upper : ℚ) : ℝ)

def cot_pi_3_29_lower : ℚ := 6683103690104145 / 2251799813685248
def cot_pi_3_29_upper : ℚ := 6683103690104155 / 2251799813685248
axiom cot_pi_3_29_bounds :
  ((cot_pi_3_29_lower : ℚ) : ℝ) ≤ cotangentTermV 3 29 ∧
  cotangentTermV 3 29 ≤ ((cot_pi_3_29_upper : ℚ) : ℝ)

def cot_pi_4_29_lower : ℚ := 4867185533814223 / 2251799813685248
def cot_pi_4_29_upper : ℚ := 4867185533814229 / 2251799813685248
axiom cot_pi_4_29_bounds :
  ((cot_pi_4_29_lower : ℚ) : ℝ) ≤ cotangentTermV 4 29 ∧
  cotangentTermV 4 29 ≤ ((cot_pi_4_29_upper : ℚ) : ℝ)

def cot_pi_5_29_lower : ℚ := 3742520403618155 / 2251799813685248
def cot_pi_5_29_upper : ℚ := 3742520403618161 / 2251799813685248
axiom cot_pi_5_29_bounds :
  ((cot_pi_5_29_lower : ℚ) : ℝ) ≤ cotangentTermV 5 29 ∧
  cotangentTermV 5 29 ≤ ((cot_pi_5_29_upper : ℚ) : ℝ)

def cot_pi_6_29_lower : ℚ := 5924383993981355 / 4503599627370496
def cot_pi_6_29_upper : ℚ := 5924383993981365 / 4503599627370496
axiom cot_pi_6_29_bounds :
  ((cot_pi_6_29_lower : ℚ) : ℝ) ≤ cotangentTermV 6 29 ∧
  cotangentTermV 6 29 ≤ ((cot_pi_6_29_upper : ℚ) : ℝ)

def cot_pi_7_29_lower : ℚ := 4754392321827539 / 4503599627370496
def cot_pi_7_29_upper : ℚ := 4754392321827547 / 4503599627370496
axiom cot_pi_7_29_bounds :
  ((cot_pi_7_29_lower : ℚ) : ℝ) ≤ cotangentTermV 7 29 ∧
  cotangentTermV 7 29 ≤ ((cot_pi_7_29_upper : ℚ) : ℝ)

def cot_pi_8_29_lower : ℚ := 7650784006611159 / 9007199254740992
def cot_pi_8_29_upper : ℚ := 7650784006611171 / 9007199254740992
axiom cot_pi_8_29_bounds :
  ((cot_pi_8_29_lower : ℚ) : ℝ) ≤ cotangentTermV 8 29 ∧
  cotangentTermV 8 29 ≤ ((cot_pi_8_29_upper : ℚ) : ℝ)

def cot_pi_9_29_lower : ℚ := 6107032627180331 / 9007199254740992
def cot_pi_9_29_upper : ℚ := 6107032627180341 / 9007199254740992
axiom cot_pi_9_29_bounds :
  ((cot_pi_9_29_lower : ℚ) : ℝ) ≤ cotangentTermV 9 29 ∧
  cotangentTermV 9 29 ≤ ((cot_pi_9_29_upper : ℚ) : ℝ)

def cot_pi_10_29_lower : ℚ := 4775314818295377 / 9007199254740992
def cot_pi_10_29_upper : ℚ := 4775314818295389 / 9007199254740992
axiom cot_pi_10_29_bounds :
  ((cot_pi_10_29_lower : ℚ) : ℝ) ≤ cotangentTermV 10 29 ∧
  cotangentTermV 10 29 ≤ ((cot_pi_10_29_upper : ℚ) : ℝ)

def cot_pi_11_29_lower : ℚ := 7177592389153465 / 18014398509481984
def cot_pi_11_29_upper : ℚ := 7177592389153495 / 18014398509481984
axiom cot_pi_11_29_bounds :
  ((cot_pi_11_29_lower : ℚ) : ℝ) ≤ cotangentTermV 11 29 ∧
  cotangentTermV 11 29 ≤ ((cot_pi_11_29_upper : ℚ) : ℝ)

def cot_pi_12_29_lower : ℚ := 625209140711611 / 2251799813685248
def cot_pi_12_29_upper : ℚ := 2500836562846453 / 9007199254740992
axiom cot_pi_12_29_bounds :
  ((cot_pi_12_29_lower : ℚ) : ℝ) ≤ cotangentTermV 12 29 ∧
  cotangentTermV 12 29 ≤ ((cot_pi_12_29_upper : ℚ) : ℝ)

def cot_pi_13_29_lower : ℚ := 2953310729889203 / 18014398509481984
def cot_pi_13_29_upper : ℚ := 2953310729889227 / 18014398509481984
axiom cot_pi_13_29_bounds :
  ((cot_pi_13_29_lower : ℚ) : ℝ) ≤ cotangentTermV 13 29 ∧
  cotangentTermV 13 29 ≤ ((cot_pi_13_29_upper : ℚ) : ℝ)

def cot_pi_14_29_lower : ℚ := 7813698454934477 / 144115188075855872
def cot_pi_14_29_upper : ℚ := 7813698454934579 / 144115188075855872
axiom cot_pi_14_29_bounds :
  ((cot_pi_14_29_lower : ℚ) : ℝ) ≤ cotangentTermV 14 29 ∧
  cotangentTermV 14 29 ≤ ((cot_pi_14_29_upper : ℚ) : ℝ)

def cot_pi_15_29_lower : ℚ := -3906849227467283 / 72057594037927936
def cot_pi_15_29_upper : ℚ := -976712306866799 / 18014398509481984
axiom cot_pi_15_29_bounds :
  ((cot_pi_15_29_lower : ℚ) : ℝ) ≤ cotangentTermV 15 29 ∧
  cotangentTermV 15 29 ≤ ((cot_pi_15_29_upper : ℚ) : ℝ)

def cot_pi_16_29_lower : ℚ := -738327682472303 / 4503599627370496
def cot_pi_16_29_upper : ℚ := -738327682472299 / 4503599627370496
axiom cot_pi_16_29_bounds :
  ((cot_pi_16_29_lower : ℚ) : ℝ) ≤ cotangentTermV 16 29 ∧
  cotangentTermV 16 29 ≤ ((cot_pi_16_29_upper : ℚ) : ℝ)

def cot_pi_17_29_lower : ℚ := -1250418281423225 / 4503599627370496
def cot_pi_17_29_upper : ℚ := -625209140711609 / 2251799813685248
axiom cot_pi_17_29_bounds :
  ((cot_pi_17_29_lower : ℚ) : ℝ) ≤ cotangentTermV 17 29 ∧
  cotangentTermV 17 29 ≤ ((cot_pi_17_29_upper : ℚ) : ℝ)

def cot_pi_18_29_lower : ℚ := -1794398097288371 / 4503599627370496
def cot_pi_18_29_upper : ℚ := -3588796194576731 / 9007199254740992
axiom cot_pi_18_29_bounds :
  ((cot_pi_18_29_lower : ℚ) : ℝ) ≤ cotangentTermV 18 29 ∧
  cotangentTermV 18 29 ≤ ((cot_pi_18_29_upper : ℚ) : ℝ)

def cot_pi_19_29_lower : ℚ := -2387657409147693 / 4503599627370496
def cot_pi_19_29_upper : ℚ := -2387657409147681 / 4503599627370496
axiom cot_pi_19_29_bounds :
  ((cot_pi_19_29_lower : ℚ) : ℝ) ≤ cotangentTermV 19 29 ∧
  cotangentTermV 19 29 ≤ ((cot_pi_19_29_upper : ℚ) : ℝ)

def cot_pi_20_29_lower : ℚ := -6107032627180339 / 9007199254740992
def cot_pi_20_29_upper : ℚ := -6107032627180317 / 9007199254740992
axiom cot_pi_20_29_bounds :
  ((cot_pi_20_29_lower : ℚ) : ℝ) ≤ cotangentTermV 20 29 ∧
  cotangentTermV 20 29 ≤ ((cot_pi_20_29_upper : ℚ) : ℝ)

def cot_pi_21_29_lower : ℚ := -7650784006611171 / 9007199254740992
def cot_pi_21_29_upper : ℚ := -7650784006611143 / 9007199254740992
axiom cot_pi_21_29_bounds :
  ((cot_pi_21_29_lower : ℚ) : ℝ) ≤ cotangentTermV 21 29 ∧
  cotangentTermV 21 29 ≤ ((cot_pi_21_29_upper : ℚ) : ℝ)

def cot_pi_22_29_lower : ℚ := -148574760057111 / 140737488355328
def cot_pi_22_29_upper : ℚ := -2377196160913763 / 2251799813685248
axiom cot_pi_22_29_bounds :
  ((cot_pi_22_29_lower : ℚ) : ℝ) ≤ cotangentTermV 22 29 ∧
  cotangentTermV 22 29 ≤ ((cot_pi_22_29_upper : ℚ) : ℝ)

def cot_pi_23_29_lower : ℚ := -5924383993981371 / 4503599627370496
def cot_pi_23_29_upper : ℚ := -5924383993981337 / 4503599627370496
axiom cot_pi_23_29_bounds :
  ((cot_pi_23_29_lower : ℚ) : ℝ) ≤ cotangentTermV 23 29 ∧
  cotangentTermV 23 29 ≤ ((cot_pi_23_29_upper : ℚ) : ℝ)

def cot_pi_24_29_lower : ℚ := -7485040807236323 / 4503599627370496
def cot_pi_24_29_upper : ℚ := -7485040807236295 / 4503599627370496
axiom cot_pi_24_29_bounds :
  ((cot_pi_24_29_lower : ℚ) : ℝ) ≤ cotangentTermV 24 29 ∧
  cotangentTermV 24 29 ≤ ((cot_pi_24_29_upper : ℚ) : ℝ)

def cot_pi_25_29_lower : ℚ := -4867185533814233 / 2251799813685248
def cot_pi_25_29_upper : ℚ := -4867185533814199 / 2251799813685248
axiom cot_pi_25_29_bounds :
  ((cot_pi_25_29_lower : ℚ) : ℝ) ≤ cotangentTermV 25 29 ∧
  cotangentTermV 25 29 ≤ ((cot_pi_25_29_upper : ℚ) : ℝ)

def cot_pi_26_29_lower : ℚ := -6683103690104161 / 2251799813685248
def cot_pi_26_29_upper : ℚ := -6683103690104105 / 2251799813685248
axiom cot_pi_26_29_bounds :
  ((cot_pi_26_29_lower : ℚ) : ℝ) ≤ cotangentTermV 26 29 ∧
  cotangentTermV 26 29 ≤ ((cot_pi_26_29_upper : ℚ) : ℝ)

def cot_pi_27_29_lower : ℚ := -2557507421985995 / 562949953421312
def cot_pi_27_29_upper : ℚ := -2557507421985965 / 562949953421312
axiom cot_pi_27_29_bounds :
  ((cot_pi_27_29_lower : ℚ) : ℝ) ≤ cotangentTermV 27 29 ∧
  cotangentTermV 27 29 ≤ ((cot_pi_27_29_upper : ℚ) : ℝ)

def cot_pi_28_29_lower : ℚ := -5176239340982395 / 562949953421312
def cot_pi_28_29_upper : ℚ := -5176239340982327 / 562949953421312
axiom cot_pi_28_29_bounds :
  ((cot_pi_28_29_lower : ℚ) : ℝ) ≤ cotangentTermV 28 29 ∧
  cotangentTermV 28 29 ≤ ((cot_pi_28_29_upper : ℚ) : ℝ)

def cot_pi_1_30_lower : ℚ := 1339027756584497 / 140737488355328
def cot_pi_1_30_upper : ℚ := 2678055513168997 / 281474976710656
axiom cot_pi_1_30_bounds :
  ((cot_pi_1_30_lower : ℚ) : ℝ) ≤ cotangentTermV 1 30 ∧
  cotangentTermV 1 30 ≤ ((cot_pi_1_30_upper : ℚ) : ℝ)

def cot_pi_2_30_lower : ℚ := 662117825248849 / 140737488355328
def cot_pi_2_30_upper : ℚ := 2648471300995399 / 562949953421312
axiom cot_pi_2_30_bounds :
  ((cot_pi_2_30_lower : ℚ) : ℝ) ≤ cotangentTermV 2 30 ∧
  cotangentTermV 2 30 ≤ ((cot_pi_2_30_upper : ℚ) : ℝ)

def cot_pi_3_30_lower : ℚ := 3465163607796693 / 1125899906842624
def cot_pi_3_30_upper : ℚ := 3465163607796697 / 1125899906842624
axiom cot_pi_3_30_bounds :
  ((cot_pi_3_30_lower : ℚ) : ℝ) ≤ cotangentTermV 3 30 ∧
  cotangentTermV 3 30 ≤ ((cot_pi_3_30_upper : ℚ) : ℝ)

def cot_pi_4_30_lower : ℚ := 2528812594503863 / 1125899906842624
def cot_pi_4_30_upper : ℚ := 1264406297251933 / 562949953421312
axiom cot_pi_4_30_bounds :
  ((cot_pi_4_30_lower : ℚ) : ℝ) ≤ cotangentTermV 4 30 ∧
  cotangentTermV 4 30 ≤ ((cot_pi_4_30_upper : ℚ) : ℝ)

def cot_pi_5_30_lower : ℚ := 1950115842888489 / 1125899906842624
def cot_pi_5_30_upper : ℚ := 487528960722123 / 281474976710656
axiom cot_pi_5_30_bounds :
  ((cot_pi_5_30_lower : ℚ) : ℝ) ≤ cotangentTermV 5 30 ∧
  cotangentTermV 5 30 ≤ ((cot_pi_5_30_upper : ℚ) : ℝ)

def cot_pi_6_30_lower : ℚ := 6198673104153461 / 4503599627370496
def cot_pi_6_30_upper : ℚ := 6198673104153469 / 4503599627370496
axiom cot_pi_6_30_bounds :
  ((cot_pi_6_30_lower : ℚ) : ℝ) ≤ cotangentTermV 6 30 ∧
  cotangentTermV 6 30 ≤ ((cot_pi_6_30_upper : ℚ) : ℝ)

def cot_pi_7_30_lower : ℚ := 5001754107937759 / 4503599627370496
def cot_pi_7_30_upper : ℚ := 5001754107937767 / 4503599627370496
axiom cot_pi_7_30_bounds :
  ((cot_pi_7_30_lower : ℚ) : ℝ) ≤ cotangentTermV 7 30 ∧
  cotangentTermV 7 30 ≤ ((cot_pi_7_30_upper : ℚ) : ℝ)

def cot_pi_8_30_lower : ℚ := 4055059318382637 / 4503599627370496
def cot_pi_8_30_upper : ℚ := 4055059318382643 / 4503599627370496
axiom cot_pi_8_30_bounds :
  ((cot_pi_8_30_lower : ℚ) : ℝ) ≤ cotangentTermV 8 30 ∧
  cotangentTermV 8 30 ≤ ((cot_pi_8_30_upper : ℚ) : ℝ)

def cot_pi_9_30_lower : ℚ := 6544113316787519 / 9007199254740992
def cot_pi_9_30_upper : ℚ := 6544113316787527 / 9007199254740992
axiom cot_pi_9_30_bounds :
  ((cot_pi_9_30_lower : ℚ) : ℝ) ≤ cotangentTermV 9 30 ∧
  cotangentTermV 9 30 ≤ ((cot_pi_9_30_upper : ℚ) : ℝ)

def cot_pi_10_30_lower : ℚ := 5200308914369303 / 9007199254740992
def cot_pi_10_30_upper : ℚ := 5200308914369315 / 9007199254740992
axiom cot_pi_10_30_bounds :
  ((cot_pi_10_30_lower : ℚ) : ℝ) ≤ cotangentTermV 10 30 ∧
  cotangentTermV 10 30 ≤ ((cot_pi_10_30_upper : ℚ) : ℝ)

def cot_pi_11_30_lower : ℚ := 4010263482500353 / 9007199254740992
def cot_pi_11_30_upper : ℚ := 250641467656273 / 562949953421312
axiom cot_pi_11_30_bounds :
  ((cot_pi_11_30_lower : ℚ) : ℝ) ≤ cotangentTermV 11 30 ∧
  cotangentTermV 11 30 ≤ ((cot_pi_11_30_upper : ℚ) : ℝ)

def cot_pi_12_30_lower : ℚ := 2926616445759701 / 9007199254740992
def cot_pi_12_30_upper : ℚ := 1463308222879853 / 4503599627370496
axiom cot_pi_12_30_bounds :
  ((cot_pi_12_30_lower : ℚ) : ℝ) ≤ cotangentTermV 12 30 ∧
  cotangentTermV 12 30 ≤ ((cot_pi_12_30_upper : ℚ) : ℝ)

def cot_pi_13_30_lower : ℚ := 7658157215458113 / 36028797018963968
def cot_pi_13_30_upper : ℚ := 7658157215458161 / 36028797018963968
axiom cot_pi_13_30_bounds :
  ((cot_pi_13_30_lower : ℚ) : ℝ) ≤ cotangentTermV 13 30 ∧
  cotangentTermV 13 30 ≤ ((cot_pi_13_30_upper : ℚ) : ℝ)

def cot_pi_14_30_lower : ℚ := 3786779158220485 / 36028797018963968
def cot_pi_14_30_upper : ℚ := 118336848694391 / 1125899906842624
axiom cot_pi_14_30_bounds :
  ((cot_pi_14_30_lower : ℚ) : ℝ) ≤ cotangentTermV 14 30 ∧
  cotangentTermV 14 30 ≤ ((cot_pi_14_30_upper : ℚ) : ℝ)

def cot_pi_15_30_lower : ℚ := -173672587 / 604462909807314587353088
def cot_pi_15_30_upper : ℚ := 129024547 / 151115727451828646838272
axiom cot_pi_15_30_bounds :
  ((cot_pi_15_30_lower : ℚ) : ℝ) ≤ cotangentTermV 15 30 ∧
  cotangentTermV 15 30 ≤ ((cot_pi_15_30_upper : ℚ) : ℝ)

def cot_pi_16_30_lower : ℚ := -7573558316441001 / 72057594037927936
def cot_pi_16_30_upper : ℚ := -7573558316440945 / 72057594037927936
axiom cot_pi_16_30_bounds :
  ((cot_pi_16_30_lower : ℚ) : ℝ) ≤ cotangentTermV 16 30 ∧
  cotangentTermV 16 30 ≤ ((cot_pi_16_30_upper : ℚ) : ℝ)

def cot_pi_17_30_lower : ℚ := -7658157215458141 / 36028797018963968
def cot_pi_17_30_upper : ℚ := -7658157215458091 / 36028797018963968
axiom cot_pi_17_30_bounds :
  ((cot_pi_17_30_lower : ℚ) : ℝ) ≤ cotangentTermV 17 30 ∧
  cotangentTermV 17 30 ≤ ((cot_pi_17_30_upper : ℚ) : ℝ)

def cot_pi_18_30_lower : ℚ := -2926616445759705 / 9007199254740992
def cot_pi_18_30_upper : ℚ := -731654111439925 / 2251799813685248
axiom cot_pi_18_30_bounds :
  ((cot_pi_18_30_lower : ℚ) : ℝ) ≤ cotangentTermV 18 30 ∧
  cotangentTermV 18 30 ≤ ((cot_pi_18_30_upper : ℚ) : ℝ)

def cot_pi_19_30_lower : ℚ := -2005131741250181 / 4503599627370496
def cot_pi_19_30_upper : ℚ := -2005131741250173 / 4503599627370496
axiom cot_pi_19_30_bounds :
  ((cot_pi_19_30_lower : ℚ) : ℝ) ≤ cotangentTermV 19 30 ∧
  cotangentTermV 19 30 ≤ ((cot_pi_19_30_upper : ℚ) : ℝ)

def cot_pi_20_30_lower : ℚ := -2600154457184657 / 4503599627370496
def cot_pi_20_30_upper : ℚ := -325019307148081 / 562949953421312
axiom cot_pi_20_30_bounds :
  ((cot_pi_20_30_lower : ℚ) : ℝ) ≤ cotangentTermV 20 30 ∧
  cotangentTermV 20 30 ≤ ((cot_pi_20_30_upper : ℚ) : ℝ)

def cot_pi_21_30_lower : ℚ := -3272056658393767 / 4503599627370496
def cot_pi_21_30_upper : ℚ := -3272056658393749 / 4503599627370496
axiom cot_pi_21_30_bounds :
  ((cot_pi_21_30_lower : ℚ) : ℝ) ≤ cotangentTermV 21 30 ∧
  cotangentTermV 21 30 ≤ ((cot_pi_21_30_upper : ℚ) : ℝ)

def cot_pi_22_30_lower : ℚ := -8110118636765293 / 9007199254740992
def cot_pi_22_30_upper : ℚ := -8110118636765251 / 9007199254740992
axiom cot_pi_22_30_bounds :
  ((cot_pi_22_30_lower : ℚ) : ℝ) ≤ cotangentTermV 22 30 ∧
  cotangentTermV 22 30 ≤ ((cot_pi_22_30_upper : ℚ) : ℝ)

def cot_pi_23_30_lower : ℚ := -2500877053968887 / 2251799813685248
def cot_pi_23_30_upper : ℚ := -2500877053968873 / 2251799813685248
axiom cot_pi_23_30_bounds :
  ((cot_pi_23_30_lower : ℚ) : ℝ) ≤ cotangentTermV 23 30 ∧
  cotangentTermV 23 30 ≤ ((cot_pi_23_30_upper : ℚ) : ℝ)

def cot_pi_24_30_lower : ℚ := -6198673104153469 / 4503599627370496
def cot_pi_24_30_upper : ℚ := -6198673104153459 / 4503599627370496
axiom cot_pi_24_30_bounds :
  ((cot_pi_24_30_lower : ℚ) : ℝ) ≤ cotangentTermV 24 30 ∧
  cotangentTermV 24 30 ≤ ((cot_pi_24_30_upper : ℚ) : ℝ)

def cot_pi_25_30_lower : ℚ := -7800463371553971 / 4503599627370496
def cot_pi_25_30_upper : ℚ := -7800463371553923 / 4503599627370496
axiom cot_pi_25_30_bounds :
  ((cot_pi_25_30_lower : ℚ) : ℝ) ≤ cotangentTermV 25 30 ∧
  cotangentTermV 25 30 ≤ ((cot_pi_25_30_upper : ℚ) : ℝ)

def cot_pi_26_30_lower : ℚ := -5057625189007737 / 2251799813685248
def cot_pi_26_30_upper : ℚ := -5057625189007701 / 2251799813685248
axiom cot_pi_26_30_bounds :
  ((cot_pi_26_30_lower : ℚ) : ℝ) ≤ cotangentTermV 26 30 ∧
  cotangentTermV 26 30 ≤ ((cot_pi_26_30_upper : ℚ) : ℝ)

def cot_pi_27_30_lower : ℚ := -3465163607796703 / 1125899906842624
def cot_pi_27_30_upper : ℚ := -3465163607796673 / 1125899906842624
axiom cot_pi_27_30_bounds :
  ((cot_pi_27_30_lower : ℚ) : ℝ) ≤ cotangentTermV 27 30 ∧
  cotangentTermV 27 30 ≤ ((cot_pi_27_30_upper : ℚ) : ℝ)

def cot_pi_28_30_lower : ℚ := -5296942601990803 / 1125899906842624
def cot_pi_28_30_upper : ℚ := -5296942601990765 / 1125899906842624
axiom cot_pi_28_30_bounds :
  ((cot_pi_28_30_lower : ℚ) : ℝ) ≤ cotangentTermV 28 30 ∧
  cotangentTermV 28 30 ≤ ((cot_pi_28_30_upper : ℚ) : ℝ)

def cot_pi_29_30_lower : ℚ := -5356111026338015 / 562949953421312
def cot_pi_29_30_upper : ℚ := -5356111026337893 / 562949953421312
axiom cot_pi_29_30_bounds :
  ((cot_pi_29_30_lower : ℚ) : ℝ) ≤ cotangentTermV 29 30 ∧
  cotangentTermV 29 30 ≤ ((cot_pi_29_30_upper : ℚ) : ℝ)

def cot_pi_1_31_lower : ℚ := 5535938802398381 / 562949953421312
def cot_pi_1_31_upper : ℚ := 5535938802398389 / 562949953421312
axiom cot_pi_1_31_bounds :
  ((cot_pi_1_31_lower : ℚ) : ℝ) ≤ cotangentTermV 1 31 ∧
  cotangentTermV 1 31 ≤ ((cot_pi_1_31_upper : ℚ) : ℝ)

def cot_pi_2_31_lower : ℚ := 5478692387405543 / 1125899906842624
def cot_pi_2_31_upper : ℚ := 5478692387405551 / 1125899906842624
axiom cot_pi_2_31_bounds :
  ((cot_pi_2_31_lower : ℚ) : ℝ) ≤ cotangentTermV 2 31 ∧
  cotangentTermV 2 31 ≤ ((cot_pi_2_31_upper : ℚ) : ℝ)

def cot_pi_3_31_lower : ℚ := 897125612221207 / 281474976710656
def cot_pi_3_31_upper : ℚ := 3588502448884833 / 1125899906842624
axiom cot_pi_3_31_bounds :
  ((cot_pi_3_31_lower : ℚ) : ℝ) ≤ cotangentTermV 3 31 ∧
  cotangentTermV 3 31 ≤ ((cot_pi_3_31_upper : ℚ) : ℝ)

def cot_pi_4_31_lower : ℚ := 5247314074736937 / 2251799813685248
def cot_pi_4_31_upper : ℚ := 5247314074736945 / 2251799813685248
axiom cot_pi_4_31_bounds :
  ((cot_pi_4_31_lower : ℚ) : ℝ) ≤ cotangentTermV 4 31 ∧
  cotangentTermV 4 31 ≤ ((cot_pi_4_31_upper : ℚ) : ℝ)

def cot_pi_5_31_lower : ℚ := 8113931940691879 / 4503599627370496
def cot_pi_5_31_upper : ℚ := 8113931940691891 / 4503599627370496
axiom cot_pi_5_31_bounds :
  ((cot_pi_5_31_lower : ℚ) : ℝ) ≤ cotangentTermV 5 31 ∧
  cotangentTermV 5 31 ≤ ((cot_pi_5_31_upper : ℚ) : ℝ)

def cot_pi_6_31_lower : ℚ := 6470498148347113 / 4503599627370496
def cot_pi_6_31_upper : ℚ := 6470498148347123 / 4503599627370496
axiom cot_pi_6_31_bounds :
  ((cot_pi_6_31_lower : ℚ) : ℝ) ≤ cotangentTermV 6 31 ∧
  cotangentTermV 6 31 ≤ ((cot_pi_6_31_upper : ℚ) : ℝ)

def cot_pi_7_31_lower : ℚ := 2623032818597611 / 2251799813685248
def cot_pi_7_31_upper : ℚ := 2623032818597615 / 2251799813685248
axiom cot_pi_7_31_bounds :
  ((cot_pi_7_31_lower : ℚ) : ℝ) ≤ cotangentTermV 7 31 ∧
  cotangentTermV 7 31 ≤ ((cot_pi_7_31_upper : ℚ) : ℝ)

def cot_pi_8_31_lower : ℚ := 4280990670287945 / 4503599627370496
def cot_pi_8_31_upper : ℚ := 267561916892997 / 281474976710656
axiom cot_pi_8_31_bounds :
  ((cot_pi_8_31_lower : ℚ) : ℝ) ≤ cotangentTermV 8 31 ∧
  cotangentTermV 8 31 ≤ ((cot_pi_8_31_upper : ℚ) : ℝ)

def cot_pi_9_31_lower : ℚ := 1743022797834077 / 2251799813685248
def cot_pi_9_31_upper : ℚ := 54469462432315 / 70368744177664
axiom cot_pi_9_31_bounds :
  ((cot_pi_9_31_lower : ℚ) : ℝ) ≤ cotangentTermV 9 31 ∧
  cotangentTermV 9 31 ≤ ((cot_pi_9_31_upper : ℚ) : ℝ)

def cot_pi_10_31_lower : ℚ := 5614230223706295 / 9007199254740992
def cot_pi_10_31_upper : ℚ := 5614230223706309 / 9007199254740992
axiom cot_pi_10_31_bounds :
  ((cot_pi_10_31_lower : ℚ) : ℝ) ≤ cotangentTermV 10 31 ∧
  cotangentTermV 10 31 ≤ ((cot_pi_10_31_upper : ℚ) : ℝ)

def cot_pi_11_31_lower : ℚ := 4418242166160997 / 9007199254740992
def cot_pi_11_31_upper : ℚ := 1104560541540253 / 2251799813685248
axiom cot_pi_11_31_bounds :
  ((cot_pi_11_31_lower : ℚ) : ℝ) ≤ cotangentTermV 11 31 ∧
  cotangentTermV 11 31 ≤ ((cot_pi_11_31_upper : ℚ) : ℝ)

def cot_pi_12_31_lower : ℚ := 6671800590693509 / 18014398509481984
def cot_pi_12_31_upper : ℚ := 6671800590693527 / 18014398509481984
axiom cot_pi_12_31_bounds :
  ((cot_pi_12_31_lower : ℚ) : ℝ) ≤ cotangentTermV 12 31 ∧
  cotangentTermV 12 31 ≤ ((cot_pi_12_31_upper : ℚ) : ℝ)

def cot_pi_13_31_lower : ℚ := 4664250931586607 / 18014398509481984
def cot_pi_13_31_upper : ℚ := 4664250931586633 / 18014398509481984
axiom cot_pi_13_31_bounds :
  ((cot_pi_13_31_lower : ℚ) : ℝ) ≤ cotangentTermV 13 31 ∧
  cotangentTermV 13 31 ≤ ((cot_pi_13_31_upper : ℚ) : ℝ)

def cot_pi_14_31_lower : ℚ := 5519408689654929 / 36028797018963968
def cot_pi_14_31_upper : ℚ := 5519408689654959 / 36028797018963968
axiom cot_pi_14_31_bounds :
  ((cot_pi_14_31_lower : ℚ) : ℝ) ≤ cotangentTermV 14 31 ∧
  cotangentTermV 14 31 ≤ ((cot_pi_14_31_upper : ℚ) : ℝ)

def cot_pi_15_31_lower : ℚ := 7308695150891947 / 144115188075855872
def cot_pi_15_31_upper : ℚ := 7308695150892115 / 144115188075855872
axiom cot_pi_15_31_bounds :
  ((cot_pi_15_31_lower : ℚ) : ℝ) ≤ cotangentTermV 15 31 ∧
  cotangentTermV 15 31 ≤ ((cot_pi_15_31_upper : ℚ) : ℝ)

def cot_pi_16_31_lower : ℚ := -7308695150892033 / 144115188075855872
def cot_pi_16_31_upper : ℚ := -7308695150891929 / 144115188075855872
axiom cot_pi_16_31_bounds :
  ((cot_pi_16_31_lower : ℚ) : ℝ) ≤ cotangentTermV 16 31 ∧
  cotangentTermV 16 31 ≤ ((cot_pi_16_31_upper : ℚ) : ℝ)

def cot_pi_17_31_lower : ℚ := -5519408689654947 / 36028797018963968
def cot_pi_17_31_upper : ℚ := -5519408689654899 / 36028797018963968
axiom cot_pi_17_31_bounds :
  ((cot_pi_17_31_lower : ℚ) : ℝ) ≤ cotangentTermV 17 31 ∧
  cotangentTermV 17 31 ≤ ((cot_pi_17_31_upper : ℚ) : ℝ)

def cot_pi_18_31_lower : ℚ := -2332125465793311 / 9007199254740992
def cot_pi_18_31_upper : ℚ := -1166062732896651 / 4503599627370496
axiom cot_pi_18_31_bounds :
  ((cot_pi_18_31_lower : ℚ) : ℝ) ≤ cotangentTermV 18 31 ∧
  cotangentTermV 18 31 ≤ ((cot_pi_18_31_upper : ℚ) : ℝ)

def cot_pi_19_31_lower : ℚ := -3335900295346761 / 9007199254740992
def cot_pi_19_31_upper : ℚ := -1667950147673373 / 4503599627370496
axiom cot_pi_19_31_bounds :
  ((cot_pi_19_31_lower : ℚ) : ℝ) ≤ cotangentTermV 19 31 ∧
  cotangentTermV 19 31 ≤ ((cot_pi_19_31_upper : ℚ) : ℝ)

def cot_pi_20_31_lower : ℚ := -8836484332322013 / 18014398509481984
def cot_pi_20_31_upper : ℚ := -8836484332321979 / 18014398509481984
axiom cot_pi_20_31_bounds :
  ((cot_pi_20_31_lower : ℚ) : ℝ) ≤ cotangentTermV 20 31 ∧
  cotangentTermV 20 31 ≤ ((cot_pi_20_31_upper : ℚ) : ℝ)

def cot_pi_21_31_lower : ℚ := -5614230223706305 / 9007199254740992
def cot_pi_21_31_upper : ℚ := -5614230223706273 / 9007199254740992
axiom cot_pi_21_31_bounds :
  ((cot_pi_21_31_lower : ℚ) : ℝ) ≤ cotangentTermV 21 31 ∧
  cotangentTermV 21 31 ≤ ((cot_pi_21_31_upper : ℚ) : ℝ)

def cot_pi_22_31_lower : ℚ := -871511398917041 / 1125899906842624
def cot_pi_22_31_upper : ℚ := -3486045595668145 / 4503599627370496
axiom cot_pi_22_31_bounds :
  ((cot_pi_22_31_lower : ℚ) : ℝ) ≤ cotangentTermV 22 31 ∧
  cotangentTermV 22 31 ≤ ((cot_pi_22_31_upper : ℚ) : ℝ)

def cot_pi_23_31_lower : ℚ := -8561981340575911 / 9007199254740992
def cot_pi_23_31_upper : ℚ := -8561981340575867 / 9007199254740992
axiom cot_pi_23_31_bounds :
  ((cot_pi_23_31_lower : ℚ) : ℝ) ≤ cotangentTermV 23 31 ∧
  cotangentTermV 23 31 ≤ ((cot_pi_23_31_upper : ℚ) : ℝ)

def cot_pi_24_31_lower : ℚ := -5246065637195229 / 4503599627370496
def cot_pi_24_31_upper : ℚ := -5246065637195211 / 4503599627370496
axiom cot_pi_24_31_bounds :
  ((cot_pi_24_31_lower : ℚ) : ℝ) ≤ cotangentTermV 24 31 ∧
  cotangentTermV 24 31 ≤ ((cot_pi_24_31_upper : ℚ) : ℝ)

def cot_pi_25_31_lower : ℚ := -6470498148347127 / 4503599627370496
def cot_pi_25_31_upper : ℚ := -6470498148347091 / 4503599627370496
axiom cot_pi_25_31_bounds :
  ((cot_pi_25_31_lower : ℚ) : ℝ) ≤ cotangentTermV 25 31 ∧
  cotangentTermV 25 31 ≤ ((cot_pi_25_31_upper : ℚ) : ℝ)

def cot_pi_26_31_lower : ℚ := -4056965970345949 / 2251799813685248
def cot_pi_26_31_upper : ℚ := -4056965970345925 / 2251799813685248
axiom cot_pi_26_31_bounds :
  ((cot_pi_26_31_lower : ℚ) : ℝ) ≤ cotangentTermV 26 31 ∧
  cotangentTermV 26 31 ≤ ((cot_pi_26_31_upper : ℚ) : ℝ)

def cot_pi_27_31_lower : ℚ := -655914259342119 / 281474976710656
def cot_pi_27_31_upper : ℚ := -1311828518684229 / 562949953421312
axiom cot_pi_27_31_bounds :
  ((cot_pi_27_31_lower : ℚ) : ℝ) ≤ cotangentTermV 27 31 ∧
  cotangentTermV 27 31 ≤ ((cot_pi_27_31_upper : ℚ) : ℝ)

def cot_pi_28_31_lower : ℚ := -3588502448884833 / 1125899906842624
def cot_pi_28_31_upper : ℚ := -3588502448884813 / 1125899906842624
axiom cot_pi_28_31_bounds :
  ((cot_pi_28_31_lower : ℚ) : ℝ) ≤ cotangentTermV 28 31 ∧
  cotangentTermV 28 31 ≤ ((cot_pi_28_31_upper : ℚ) : ℝ)

def cot_pi_29_31_lower : ℚ := -2739346193702783 / 562949953421312
def cot_pi_29_31_upper : ℚ := -2739346193702749 / 562949953421312
axiom cot_pi_29_31_bounds :
  ((cot_pi_29_31_lower : ℚ) : ℝ) ≤ cotangentTermV 29 31 ∧
  cotangentTermV 29 31 ≤ ((cot_pi_29_31_upper : ℚ) : ℝ)

def cot_pi_30_31_lower : ℚ := -5535938802398419 / 562949953421312
def cot_pi_30_31_upper : ℚ := -5535938802398291 / 562949953421312
axiom cot_pi_30_31_bounds :
  ((cot_pi_30_31_lower : ℚ) : ℝ) ≤ cotangentTermV 30 31 ∧
  cotangentTermV 30 31 ≤ ((cot_pi_30_31_upper : ℚ) : ℝ)

def cot_pi_1_32_lower : ℚ := 5715726796783049 / 562949953421312
def cot_pi_1_32_upper : ℚ := 5715726796783055 / 562949953421312
axiom cot_pi_1_32_bounds :
  ((cot_pi_1_32_lower : ℚ) : ℝ) ≤ cotangentTermV 1 32 ∧
  cotangentTermV 1 32 ≤ ((cot_pi_1_32_upper : ℚ) : ℝ)

def cot_pi_2_32_lower : ℚ := 2830140532925367 / 562949953421312
def cot_pi_2_32_upper : ℚ := 1415070266462685 / 281474976710656
axiom cot_pi_2_32_bounds :
  ((cot_pi_2_32_lower : ℚ) : ℝ) ≤ cotangentTermV 2 32 ∧
  cotangentTermV 2 32 ≤ ((cot_pi_2_32_upper : ℚ) : ℝ)

def cot_pi_3_32_lower : ℚ := 7423189160689881 / 2251799813685248
def cot_pi_3_32_upper : ℚ := 7423189160689889 / 2251799813685248
axiom cot_pi_3_32_bounds :
  ((cot_pi_3_32_lower : ℚ) : ℝ) ≤ cotangentTermV 3 32 ∧
  cotangentTermV 3 32 ≤ ((cot_pi_3_32_upper : ℚ) : ℝ)

def cot_pi_4_32_lower : ℚ := 5436325649948131 / 2251799813685248
def cot_pi_4_32_upper : ℚ := 5436325649948137 / 2251799813685248
axiom cot_pi_4_32_bounds :
  ((cot_pi_4_32_lower : ℚ) : ℝ) ≤ cotangentTermV 4 32 ∧
  cotangentTermV 4 32 ≤ ((cot_pi_4_32_upper : ℚ) : ℝ)

def cot_pi_5_32_lower : ℚ := 4212821141096961 / 2251799813685248
def cot_pi_5_32_upper : ℚ := 4212821141096965 / 2251799813685248
axiom cot_pi_5_32_bounds :
  ((cot_pi_5_32_lower : ℚ) : ℝ) ≤ cotangentTermV 5 32 ∧
  cotangentTermV 5 32 ≤ ((cot_pi_5_32_upper : ℚ) : ℝ)

def cot_pi_6_32_lower : ℚ := 6740113155060829 / 4503599627370496
def cot_pi_6_32_upper : ℚ := 6740113155060837 / 4503599627370496
axiom cot_pi_6_32_bounds :
  ((cot_pi_6_32_lower : ℚ) : ℝ) ≤ cotangentTermV 6 32 ∧
  cotangentTermV 6 32 ≤ ((cot_pi_6_32_upper : ℚ) : ℝ)

def cot_pi_7_32_lower : ℚ := 5487652023787643 / 4503599627370496
def cot_pi_7_32_upper : ℚ := 5487652023787649 / 4503599627370496
axiom cot_pi_7_32_bounds :
  ((cot_pi_7_32_lower : ℚ) : ℝ) ≤ cotangentTermV 7 32 ∧
  cotangentTermV 7 32 ≤ ((cot_pi_7_32_upper : ℚ) : ℝ)

def cot_pi_8_32_lower : ℚ := 2251799813685247 / 2251799813685248
def cot_pi_8_32_upper : ℚ := 2251799813685249 / 2251799813685248
axiom cot_pi_8_32_bounds :
  ((cot_pi_8_32_lower : ℚ) : ℝ) ≤ cotangentTermV 8 32 ∧
  cotangentTermV 8 32 ≤ ((cot_pi_8_32_upper : ℚ) : ℝ)

def cot_pi_9_32_lower : ℚ := 1848004348283411 / 2251799813685248
def cot_pi_9_32_upper : ℚ := 1848004348283413 / 2251799813685248
axiom cot_pi_9_32_bounds :
  ((cot_pi_9_32_lower : ℚ) : ℝ) ≤ cotangentTermV 9 32 ∧
  cotangentTermV 9 32 ≤ ((cot_pi_9_32_upper : ℚ) : ℝ)

def cot_pi_10_32_lower : ℚ := 1504604532375139 / 2251799813685248
def cot_pi_10_32_upper : ℚ := 1504604532375141 / 2251799813685248
axiom cot_pi_10_32_bounds :
  ((cot_pi_10_32_lower : ℚ) : ℝ) ≤ cotangentTermV 10 32 ∧
  cotangentTermV 10 32 ≤ ((cot_pi_10_32_upper : ℚ) : ℝ)

def cot_pi_11_32_lower : ℚ := 4814448305386727 / 9007199254740992
def cot_pi_11_32_upper : ℚ := 4814448305386739 / 9007199254740992
axiom cot_pi_11_32_bounds :
  ((cot_pi_11_32_lower : ℚ) : ℝ) ≤ cotangentTermV 11 32 ∧
  cotangentTermV 11 32 ≤ ((cot_pi_11_32_upper : ℚ) : ℝ)

def cot_pi_12_32_lower : ℚ := 7461808180621101 / 18014398509481984
def cot_pi_12_32_upper : ℚ := 7461808180621111 / 18014398509481984
axiom cot_pi_12_32_bounds :
  ((cot_pi_12_32_lower : ℚ) : ℝ) ≤ cotangentTermV 12 32 ∧
  cotangentTermV 12 32 ≤ ((cot_pi_12_32_upper : ℚ) : ℝ)

def cot_pi_13_32_lower : ℚ := 2732304022516203 / 9007199254740992
def cot_pi_13_32_upper : ℚ := 683076005629053 / 2251799813685248
axiom cot_pi_13_32_bounds :
  ((cot_pi_13_32_lower : ℚ) : ℝ) ≤ cotangentTermV 13 32 ∧
  cotangentTermV 13 32 ≤ ((cot_pi_13_32_upper : ℚ) : ℝ)

def cot_pi_14_32_lower : ℚ := 3583286654441641 / 18014398509481984
def cot_pi_14_32_upper : ℚ := 223955415902603 / 1125899906842624
axiom cot_pi_14_32_bounds :
  ((cot_pi_14_32_lower : ℚ) : ℝ) ≤ cotangentTermV 14 32 ∧
  cotangentTermV 14 32 ≤ ((cot_pi_14_32_upper : ℚ) : ℝ)

def cot_pi_15_32_lower : ℚ := 7097053559336339 / 72057594037927936
def cot_pi_15_32_upper : ℚ := 7097053559336393 / 72057594037927936
axiom cot_pi_15_32_bounds :
  ((cot_pi_15_32_lower : ℚ) : ℝ) ≤ cotangentTermV 15 32 ∧
  cotangentTermV 15 32 ≤ ((cot_pi_15_32_upper : ℚ) : ℝ)

def cot_pi_16_32_lower : ℚ := -488112139 / 9671406556917033397649408
def cot_pi_16_32_upper : ℚ := 1671954449 / 9671406556917033397649408
axiom cot_pi_16_32_bounds :
  ((cot_pi_16_32_lower : ℚ) : ℝ) ≤ cotangentTermV 16 32 ∧
  cotangentTermV 16 32 ≤ ((cot_pi_16_32_upper : ℚ) : ℝ)

def cot_pi_17_32_lower : ℚ := -7097053559336369 / 72057594037927936
def cot_pi_17_32_upper : ℚ := -7097053559336313 / 72057594037927936
axiom cot_pi_17_32_bounds :
  ((cot_pi_17_32_lower : ℚ) : ℝ) ≤ cotangentTermV 17 32 ∧
  cotangentTermV 17 32 ≤ ((cot_pi_17_32_upper : ℚ) : ℝ)

def cot_pi_18_32_lower : ℚ := -7166573308883293 / 36028797018963968
def cot_pi_18_32_upper : ℚ := -7166573308883277 / 36028797018963968
axiom cot_pi_18_32_bounds :
  ((cot_pi_18_32_lower : ℚ) : ℝ) ≤ cotangentTermV 18 32 ∧
  cotangentTermV 18 32 ≤ ((cot_pi_18_32_upper : ℚ) : ℝ)

def cot_pi_19_32_lower : ℚ := -2732304022516209 / 9007199254740992
def cot_pi_19_32_upper : ℚ := -2732304022516199 / 9007199254740992
axiom cot_pi_19_32_bounds :
  ((cot_pi_19_32_lower : ℚ) : ℝ) ≤ cotangentTermV 19 32 ∧
  cotangentTermV 19 32 ≤ ((cot_pi_19_32_upper : ℚ) : ℝ)

def cot_pi_20_32_lower : ℚ := -3730904090310555 / 9007199254740992
def cot_pi_20_32_upper : ℚ := -3730904090310549 / 9007199254740992
axiom cot_pi_20_32_bounds :
  ((cot_pi_20_32_lower : ℚ) : ℝ) ≤ cotangentTermV 20 32 ∧
  cotangentTermV 20 32 ≤ ((cot_pi_20_32_upper : ℚ) : ℝ)

def cot_pi_21_32_lower : ℚ := -4814448305386735 / 9007199254740992
def cot_pi_21_32_upper : ℚ := -4814448305386717 / 9007199254740992
axiom cot_pi_21_32_bounds :
  ((cot_pi_21_32_lower : ℚ) : ℝ) ≤ cotangentTermV 21 32 ∧
  cotangentTermV 21 32 ≤ ((cot_pi_21_32_upper : ℚ) : ℝ)

def cot_pi_22_32_lower : ℚ := -6018418129500567 / 9007199254740992
def cot_pi_22_32_upper : ℚ := -6018418129500545 / 9007199254740992
axiom cot_pi_22_32_bounds :
  ((cot_pi_22_32_lower : ℚ) : ℝ) ≤ cotangentTermV 22 32 ∧
  cotangentTermV 22 32 ≤ ((cot_pi_22_32_upper : ℚ) : ℝ)

def cot_pi_23_32_lower : ℚ := -7392017393133657 / 9007199254740992
def cot_pi_23_32_upper : ℚ := -7392017393133631 / 9007199254740992
axiom cot_pi_23_32_bounds :
  ((cot_pi_23_32_lower : ℚ) : ℝ) ≤ cotangentTermV 23 32 ∧
  cotangentTermV 23 32 ≤ ((cot_pi_23_32_upper : ℚ) : ℝ)

def cot_pi_24_32_lower : ℚ := -2251799813685249 / 2251799813685248
def cot_pi_24_32_upper : ℚ := -4503599627370491 / 4503599627370496
axiom cot_pi_24_32_bounds :
  ((cot_pi_24_32_lower : ℚ) : ℝ) ≤ cotangentTermV 24 32 ∧
  cotangentTermV 24 32 ≤ ((cot_pi_24_32_upper : ℚ) : ℝ)

def cot_pi_25_32_lower : ℚ := -2743826011893825 / 2251799813685248
def cot_pi_25_32_upper : ℚ := -2743826011893815 / 2251799813685248
axiom cot_pi_25_32_bounds :
  ((cot_pi_25_32_lower : ℚ) : ℝ) ≤ cotangentTermV 25 32 ∧
  cotangentTermV 25 32 ≤ ((cot_pi_25_32_upper : ℚ) : ℝ)

def cot_pi_26_32_lower : ℚ := -3370056577530421 / 2251799813685248
def cot_pi_26_32_upper : ℚ := -421257072191301 / 281474976710656
axiom cot_pi_26_32_bounds :
  ((cot_pi_26_32_lower : ℚ) : ℝ) ≤ cotangentTermV 26 32 ∧
  cotangentTermV 26 32 ≤ ((cot_pi_26_32_upper : ℚ) : ℝ)

def cot_pi_27_32_lower : ℚ := -8425642282193937 / 4503599627370496
def cot_pi_27_32_upper : ℚ := -8425642282193905 / 4503599627370496
axiom cot_pi_27_32_bounds :
  ((cot_pi_27_32_lower : ℚ) : ℝ) ≤ cotangentTermV 27 32 ∧
  cotangentTermV 27 32 ≤ ((cot_pi_27_32_upper : ℚ) : ℝ)

def cot_pi_28_32_lower : ℚ := -5436325649948137 / 2251799813685248
def cot_pi_28_32_upper : ℚ := -5436325649948127 / 2251799813685248
axiom cot_pi_28_32_bounds :
  ((cot_pi_28_32_lower : ℚ) : ℝ) ≤ cotangentTermV 28 32 ∧
  cotangentTermV 28 32 ≤ ((cot_pi_28_32_upper : ℚ) : ℝ)

def cot_pi_29_32_lower : ℚ := -3711594580344947 / 1125899906842624
def cot_pi_29_32_upper : ℚ := -1855797290172463 / 562949953421312
axiom cot_pi_29_32_bounds :
  ((cot_pi_29_32_lower : ℚ) : ℝ) ≤ cotangentTermV 29 32 ∧
  cotangentTermV 29 32 ≤ ((cot_pi_29_32_upper : ℚ) : ℝ)

def cot_pi_30_32_lower : ℚ := -5660281065850749 / 1125899906842624
def cot_pi_30_32_upper : ℚ := -5660281065850705 / 1125899906842624
axiom cot_pi_30_32_bounds :
  ((cot_pi_30_32_lower : ℚ) : ℝ) ≤ cotangentTermV 30 32 ∧
  cotangentTermV 30 32 ≤ ((cot_pi_30_32_upper : ℚ) : ℝ)

def cot_pi_31_32_lower : ℚ := -5715726796783079 / 562949953421312
def cot_pi_31_32_upper : ℚ := -5715726796782997 / 562949953421312
axiom cot_pi_31_32_bounds :
  ((cot_pi_31_32_lower : ℚ) : ℝ) ≤ cotangentTermV 31 32 ∧
  cotangentTermV 31 32 ≤ ((cot_pi_31_32_upper : ℚ) : ℝ)

def cot_pi_1_33_lower : ℚ := 5895478635181975 / 562949953421312
def cot_pi_1_33_upper : ℚ := 5895478635181983 / 562949953421312
axiom cot_pi_1_33_bounds :
  ((cot_pi_1_33_lower : ℚ) : ℝ) ≤ cotangentTermV 1 33 ∧
  cotangentTermV 1 33 ≤ ((cot_pi_1_33_upper : ℚ) : ℝ)

def cot_pi_2_33_lower : ℚ := 2920861716155385 / 562949953421312
def cot_pi_2_33_upper : ℚ := 2920861716155389 / 562949953421312
axiom cot_pi_2_33_bounds :
  ((cot_pi_2_33_lower : ℚ) : ℝ) ≤ cotangentTermV 2 33 ∧
  cotangentTermV 2 33 ≤ ((cot_pi_2_33_upper : ℚ) : ℝ)

def cot_pi_3_33_lower : ℚ := 7668925890001035 / 2251799813685248
def cot_pi_3_33_upper : ℚ := 7668925890001047 / 2251799813685248
axiom cot_pi_3_33_bounds :
  ((cot_pi_3_33_lower : ℚ) : ℝ) ≤ cotangentTermV 3 33 ∧
  cotangentTermV 3 33 ≤ ((cot_pi_3_33_upper : ℚ) : ℝ)

def cot_pi_4_33_lower : ℚ := 2812362005845855 / 1125899906842624
def cot_pi_4_33_upper : ℚ := 2812362005845859 / 1125899906842624
axiom cot_pi_4_33_bounds :
  ((cot_pi_4_33_lower : ℚ) : ℝ) ≤ cotangentTermV 4 33 ∧
  cotangentTermV 4 33 ≤ ((cot_pi_4_33_upper : ℚ) : ℝ)

def cot_pi_5_33_lower : ℚ := 2183941132578789 / 1125899906842624
def cot_pi_5_33_upper : ℚ := 4367882265157583 / 2251799813685248
axiom cot_pi_5_33_bounds :
  ((cot_pi_5_33_lower : ℚ) : ℝ) ≤ cotangentTermV 5 33 ∧
  cotangentTermV 5 33 ≤ ((cot_pi_5_33_upper : ℚ) : ℝ)

def cot_pi_6_33_lower : ℚ := 7007737807909369 / 4503599627370496
def cot_pi_6_33_upper : ℚ := 7007737807909381 / 4503599627370496
axiom cot_pi_6_33_bounds :
  ((cot_pi_6_33_lower : ℚ) : ℝ) ≤ cotangentTermV 6 33 ∧
  cotangentTermV 6 33 ≤ ((cot_pi_6_33_upper : ℚ) : ℝ)

def cot_pi_7_33_lower : ℚ := 1431698197182593 / 1125899906842624
def cot_pi_7_33_upper : ℚ := 2863396394365191 / 2251799813685248
axiom cot_pi_7_33_bounds :
  ((cot_pi_7_33_lower : ℚ) : ℝ) ≤ cotangentTermV 7 33 ∧
  cotangentTermV 7 33 ≤ ((cot_pi_7_33_upper : ℚ) : ℝ)

def cot_pi_8_33_lower : ℚ := 4723239353889297 / 4503599627370496
def cot_pi_8_33_upper : ℚ := 4723239353889305 / 4503599627370496
axiom cot_pi_8_33_bounds :
  ((cot_pi_8_33_lower : ℚ) : ℝ) ≤ cotangentTermV 8 33 ∧
  cotangentTermV 8 33 ≤ ((cot_pi_8_33_upper : ℚ) : ℝ)

def cot_pi_9_33_lower : ℚ := 7804782582631265 / 9007199254740992
def cot_pi_9_33_upper : ℚ := 7804782582631277 / 9007199254740992
axiom cot_pi_9_33_bounds :
  ((cot_pi_9_33_lower : ℚ) : ℝ) ≤ cotangentTermV 9 33 ∧
  cotangentTermV 9 33 ≤ ((cot_pi_9_33_upper : ℚ) : ℝ)

def cot_pi_10_33_lower : ℚ := 3206998776753847 / 4503599627370496
def cot_pi_10_33_upper : ℚ := 3206998776753853 / 4503599627370496
axiom cot_pi_10_33_bounds :
  ((cot_pi_10_33_lower : ℚ) : ℝ) ≤ cotangentTermV 10 33 ∧
  cotangentTermV 10 33 ≤ ((cot_pi_10_33_upper : ℚ) : ℝ)

def cot_pi_11_33_lower : ℚ := 5200308914369303 / 9007199254740992
def cot_pi_11_33_upper : ℚ := 5200308914369321 / 9007199254740992
axiom cot_pi_11_33_bounds :
  ((cot_pi_11_33_lower : ℚ) : ℝ) ≤ cotangentTermV 11 33 ∧
  cotangentTermV 11 33 ≤ ((cot_pi_11_33_upper : ℚ) : ℝ)

def cot_pi_12_33_lower : ℚ := 8226900141217031 / 18014398509481984
def cot_pi_12_33_upper : ℚ := 8226900141217051 / 18014398509481984
axiom cot_pi_12_33_bounds :
  ((cot_pi_12_33_lower : ℚ) : ℝ) ≤ cotangentTermV 12 33 ∧
  cotangentTermV 12 33 ≤ ((cot_pi_12_33_upper : ℚ) : ℝ)

def cot_pi_13_33_lower : ℚ := 6234843943202615 / 18014398509481984
def cot_pi_13_33_upper : ℚ := 6234843943202633 / 18014398509481984
axiom cot_pi_13_33_bounds :
  ((cot_pi_13_33_lower : ℚ) : ℝ) ≤ cotangentTermV 13 33 ∧
  cotangentTermV 13 33 ≤ ((cot_pi_13_33_upper : ℚ) : ℝ)

def cot_pi_14_33_lower : ℚ := 4370245791336497 / 18014398509481984
def cot_pi_14_33_upper : ℚ := 68285090489633 / 281474976710656
axiom cot_pi_14_33_bounds :
  ((cot_pi_14_33_lower : ℚ) : ℝ) ≤ cotangentTermV 14 33 ∧
  cotangentTermV 14 33 ≤ ((cot_pi_14_33_upper : ℚ) : ℝ)

def cot_pi_15_33_lower : ℚ := 5180158970077803 / 36028797018963968
def cot_pi_15_33_upper : ℚ := 5180158970077849 / 36028797018963968
axiom cot_pi_15_33_bounds :
  ((cot_pi_15_33_lower : ℚ) : ℝ) ≤ cotangentTermV 15 33 ∧
  cotangentTermV 15 33 ≤ ((cot_pi_15_33_upper : ℚ) : ℝ)

def cot_pi_16_33_lower : ℚ := 1716263130987149 / 36028797018963968
def cot_pi_16_33_upper : ℚ := 3432526261974349 / 72057594037927936
axiom cot_pi_16_33_bounds :
  ((cot_pi_16_33_lower : ℚ) : ℝ) ≤ cotangentTermV 16 33 ∧
  cotangentTermV 16 33 ≤ ((cot_pi_16_33_upper : ℚ) : ℝ)

def cot_pi_17_33_lower : ℚ := -858131565493585 / 18014398509481984
def cot_pi_17_33_upper : ℚ := -3432526261974257 / 72057594037927936
axiom cot_pi_17_33_bounds :
  ((cot_pi_17_33_lower : ℚ) : ℝ) ≤ cotangentTermV 17 33 ∧
  cotangentTermV 17 33 ≤ ((cot_pi_17_33_upper : ℚ) : ℝ)

def cot_pi_18_33_lower : ℚ := -1295039742519457 / 9007199254740992
def cot_pi_18_33_upper : ℚ := -2590079485038899 / 18014398509481984
axiom cot_pi_18_33_bounds :
  ((cot_pi_18_33_lower : ℚ) : ℝ) ≤ cotangentTermV 18 33 ∧
  cotangentTermV 18 33 ≤ ((cot_pi_18_33_upper : ℚ) : ℝ)

def cot_pi_19_33_lower : ℚ := -4370245791336511 / 18014398509481984
def cot_pi_19_33_upper : ℚ := -2185122895668243 / 9007199254740992
axiom cot_pi_19_33_bounds :
  ((cot_pi_19_33_lower : ℚ) : ℝ) ≤ cotangentTermV 19 33 ∧
  cotangentTermV 19 33 ≤ ((cot_pi_19_33_upper : ℚ) : ℝ)

def cot_pi_20_33_lower : ℚ := -6234843943202627 / 18014398509481984
def cot_pi_20_33_upper : ℚ := -6234843943202607 / 18014398509481984
axiom cot_pi_20_33_bounds :
  ((cot_pi_20_33_lower : ℚ) : ℝ) ≤ cotangentTermV 20 33 ∧
  cotangentTermV 20 33 ≤ ((cot_pi_20_33_upper : ℚ) : ℝ)

def cot_pi_21_33_lower : ℚ := -8226900141217045 / 18014398509481984
def cot_pi_21_33_upper : ℚ := -8226900141217003 / 18014398509481984
axiom cot_pi_21_33_bounds :
  ((cot_pi_21_33_lower : ℚ) : ℝ) ≤ cotangentTermV 21 33 ∧
  cotangentTermV 21 33 ≤ ((cot_pi_21_33_upper : ℚ) : ℝ)

def cot_pi_22_33_lower : ℚ := -5200308914369315 / 9007199254740992
def cot_pi_22_33_upper : ℚ := -5200308914369285 / 9007199254740992
axiom cot_pi_22_33_bounds :
  ((cot_pi_22_33_lower : ℚ) : ℝ) ≤ cotangentTermV 22 33 ∧
  cotangentTermV 22 33 ≤ ((cot_pi_22_33_upper : ℚ) : ℝ)

def cot_pi_23_33_lower : ℚ := -6413997553507709 / 9007199254740992
def cot_pi_23_33_upper : ℚ := -6413997553507675 / 9007199254740992
axiom cot_pi_23_33_bounds :
  ((cot_pi_23_33_lower : ℚ) : ℝ) ≤ cotangentTermV 23 33 ∧
  cotangentTermV 23 33 ≤ ((cot_pi_23_33_upper : ℚ) : ℝ)

def cot_pi_24_33_lower : ℚ := -3902391291315637 / 4503599627370496
def cot_pi_24_33_upper : ℚ := -487798911414453 / 562949953421312
axiom cot_pi_24_33_bounds :
  ((cot_pi_24_33_lower : ℚ) : ℝ) ≤ cotangentTermV 24 33 ∧
  cotangentTermV 24 33 ≤ ((cot_pi_24_33_upper : ℚ) : ℝ)

def cot_pi_25_33_lower : ℚ := -4723239353889305 / 4503599627370496
def cot_pi_25_33_upper : ℚ := -4723239353889281 / 4503599627370496
axiom cot_pi_25_33_bounds :
  ((cot_pi_25_33_lower : ℚ) : ℝ) ≤ cotangentTermV 25 33 ∧
  cotangentTermV 25 33 ≤ ((cot_pi_25_33_upper : ℚ) : ℝ)

def cot_pi_26_33_lower : ℚ := -5726792788730383 / 4503599627370496
def cot_pi_26_33_upper : ℚ := -5726792788730363 / 4503599627370496
axiom cot_pi_26_33_bounds :
  ((cot_pi_26_33_lower : ℚ) : ℝ) ≤ cotangentTermV 26 33 ∧
  cotangentTermV 26 33 ≤ ((cot_pi_26_33_upper : ℚ) : ℝ)

def cot_pi_27_33_lower : ℚ := -3503868903954695 / 2251799813685248
def cot_pi_27_33_upper : ℚ := -3503868903954675 / 2251799813685248
axiom cot_pi_27_33_bounds :
  ((cot_pi_27_33_lower : ℚ) : ℝ) ≤ cotangentTermV 27 33 ∧
  cotangentTermV 27 33 ≤ ((cot_pi_27_33_upper : ℚ) : ℝ)

def cot_pi_28_33_lower : ℚ := -8735764530315175 / 4503599627370496
def cot_pi_28_33_upper : ℚ := -8735764530315141 / 4503599627370496
axiom cot_pi_28_33_bounds :
  ((cot_pi_28_33_lower : ℚ) : ℝ) ≤ cotangentTermV 28 33 ∧
  cotangentTermV 28 33 ≤ ((cot_pi_28_33_upper : ℚ) : ℝ)

def cot_pi_29_33_lower : ℚ := -5624724011691725 / 2251799813685248
def cot_pi_29_33_upper : ℚ := -5624724011691685 / 2251799813685248
axiom cot_pi_29_33_bounds :
  ((cot_pi_29_33_lower : ℚ) : ℝ) ≤ cotangentTermV 29 33 ∧
  cotangentTermV 29 33 ≤ ((cot_pi_29_33_upper : ℚ) : ℝ)

def cot_pi_30_33_lower : ℚ := -3834462945000531 / 1125899906842624
def cot_pi_30_33_upper : ℚ := -3834462945000497 / 1125899906842624
axiom cot_pi_30_33_bounds :
  ((cot_pi_30_33_lower : ℚ) : ℝ) ≤ cotangentTermV 30 33 ∧
  cotangentTermV 30 33 ≤ ((cot_pi_30_33_upper : ℚ) : ℝ)

def cot_pi_31_33_lower : ℚ := -2920861716155401 / 562949953421312
def cot_pi_31_33_upper : ℚ := -730215429038841 / 140737488355328
axiom cot_pi_31_33_bounds :
  ((cot_pi_31_33_lower : ℚ) : ℝ) ≤ cotangentTermV 31 33 ∧
  cotangentTermV 31 33 ≤ ((cot_pi_31_33_upper : ℚ) : ℝ)

def cot_pi_32_33_lower : ℚ := -5895478635182009 / 562949953421312
def cot_pi_32_33_upper : ℚ := -5895478635181921 / 562949953421312
axiom cot_pi_32_33_bounds :
  ((cot_pi_32_33_lower : ℚ) : ℝ) ≤ cotangentTermV 32 33 ∧
  cotangentTermV 32 33 ≤ ((cot_pi_32_33_upper : ℚ) : ℝ)

def cot_pi_1_34_lower : ℚ := 6075197515441309 / 562949953421312
def cot_pi_1_34_upper : ℚ := 6075197515441317 / 562949953421312
axiom cot_pi_1_34_bounds :
  ((cot_pi_1_34_lower : ℚ) : ℝ) ≤ cotangentTermV 1 34 ∧
  cotangentTermV 1 34 ≤ ((cot_pi_1_34_upper : ℚ) : ℝ)

def cot_pi_2_34_lower : ℚ := 6023032520105509 / 1125899906842624
def cot_pi_2_34_upper : ℚ := 6023032520105517 / 1125899906842624
axiom cot_pi_2_34_bounds :
  ((cot_pi_2_34_lower : ℚ) : ℝ) ≤ cotangentTermV 2 34 ∧
  cotangentTermV 2 34 ≤ ((cot_pi_2_34_upper : ℚ) : ℝ)

def cot_pi_3_34_lower : ℚ := 7914255426076299 / 2251799813685248
def cot_pi_3_34_upper : ℚ := 7914255426076311 / 2251799813685248
axiom cot_pi_3_34_bounds :
  ((cot_pi_3_34_lower : ℚ) : ℝ) ≤ cotangentTermV 3 34 ∧
  cotangentTermV 3 34 ≤ ((cot_pi_3_34_upper : ℚ) : ℝ)

def cot_pi_4_34_lower : ℚ := 5812565351615769 / 2251799813685248
def cot_pi_4_34_upper : ℚ := 5812565351615777 / 2251799813685248
axiom cot_pi_4_34_bounds :
  ((cot_pi_4_34_lower : ℚ) : ℝ) ≤ cotangentTermV 4 34 ∧
  cotangentTermV 4 34 ≤ ((cot_pi_4_34_upper : ℚ) : ℝ)

def cot_pi_5_34_lower : ℚ := 565277955825543 / 281474976710656
def cot_pi_5_34_upper : ℚ := 2261111823302175 / 1125899906842624
axiom cot_pi_5_34_bounds :
  ((cot_pi_5_34_lower : ℚ) : ℝ) ≤ cotangentTermV 5 34 ∧
  cotangentTermV 5 34 ≤ ((cot_pi_5_34_upper : ℚ) : ℝ)

def cot_pi_6_34_lower : ℚ := 7273563140077287 / 4503599627370496
def cot_pi_6_34_upper : ℚ := 7273563140077299 / 4503599627370496
axiom cot_pi_6_34_bounds :
  ((cot_pi_6_34_lower : ℚ) : ℝ) ≤ cotangentTermV 6 34 ∧
  cotangentTermV 6 34 ≤ ((cot_pi_6_34_upper : ℚ) : ℝ)

def cot_pi_7_34_lower : ℚ := 1490932428397933 / 1125899906842624
def cot_pi_7_34_upper : ℚ := 2981864856795871 / 2251799813685248
axiom cot_pi_7_34_bounds :
  ((cot_pi_7_34_lower : ℚ) : ℝ) ≤ cotangentTermV 7 34 ∧
  cotangentTermV 7 34 ≤ ((cot_pi_7_34_upper : ℚ) : ℝ)

def cot_pi_8_34_lower : ℚ := 2470106728168569 / 2251799813685248
def cot_pi_8_34_upper : ℚ := 2470106728168573 / 2251799813685248
axiom cot_pi_8_34_bounds :
  ((cot_pi_8_34_lower : ℚ) : ℝ) ≤ cotangentTermV 8 34 ∧
  cotangentTermV 8 34 ≤ ((cot_pi_8_34_upper : ℚ) : ℝ)

def cot_pi_9_34_lower : ℚ := 2052786765482173 / 2251799813685248
def cot_pi_9_34_upper : ℚ := 32074793210659 / 35184372088832
axiom cot_pi_9_34_bounds :
  ((cot_pi_9_34_lower : ℚ) : ℝ) ≤ cotangentTermV 9 34 ∧
  cotangentTermV 9 34 ≤ ((cot_pi_9_34_upper : ℚ) : ℝ)

def cot_pi_10_34_lower : ℚ := 6801921139191367 / 9007199254740992
def cot_pi_10_34_upper : ℚ := 6801921139191379 / 9007199254740992
axiom cot_pi_10_34_bounds :
  ((cot_pi_10_34_lower : ℚ) : ℝ) ≤ cotangentTermV 10 34 ∧
  cotangentTermV 10 34 ≤ ((cot_pi_10_34_upper : ℚ) : ℝ)

def cot_pi_11_34_lower : ℚ := 2788510832042645 / 4503599627370496
def cot_pi_11_34_upper : ℚ := 1394255416021327 / 2251799813685248
axiom cot_pi_11_34_bounds :
  ((cot_pi_11_34_lower : ℚ) : ℝ) ≤ cotangentTermV 11 34 ∧
  cotangentTermV 11 34 ≤ ((cot_pi_11_34_upper : ℚ) : ℝ)

def cot_pi_12_34_lower : ℚ := 8970104616069279 / 18014398509481984
def cot_pi_12_34_upper : ℚ := 8970104616069299 / 18014398509481984
axiom cot_pi_12_34_bounds :
  ((cot_pi_12_34_lower : ℚ) : ℝ) ≤ cotangentTermV 12 34 ∧
  cotangentTermV 12 34 ≤ ((cot_pi_12_34_upper : ℚ) : ℝ)

def cot_pi_13_34_lower : ℚ := 1744703790557259 / 4503599627370496
def cot_pi_13_34_upper : ℚ := 872351895278633 / 2251799813685248
axiom cot_pi_13_34_bounds :
  ((cot_pi_13_34_lower : ℚ) : ℝ) ≤ cotangentTermV 13 34 ∧
  cotangentTermV 13 34 ≤ ((cot_pi_13_34_upper : ℚ) : ℝ)

def cot_pi_14_34_lower : ℚ := 5125538287992095 / 18014398509481984
def cot_pi_14_34_upper : ℚ := 5125538287992113 / 18014398509481984
axiom cot_pi_14_34_bounds :
  ((cot_pi_14_34_lower : ℚ) : ℝ) ≤ cotangentTermV 14 34 ∧
  cotangentTermV 14 34 ≤ ((cot_pi_14_34_upper : ℚ) : ℝ)

def cot_pi_15_34_lower : ℚ := 6734949391671659 / 36028797018963968
def cot_pi_15_34_upper : ℚ := 6734949391671705 / 36028797018963968
axiom cot_pi_15_34_bounds :
  ((cot_pi_15_34_lower : ℚ) : ℝ) ≤ cotangentTermV 15 34 ∧
  cotangentTermV 15 34 ≤ ((cot_pi_15_34_upper : ℚ) : ℝ)

def cot_pi_16_34_lower : ℚ := 3338559701491169 / 36028797018963968
def cot_pi_16_34_upper : ℚ := 834639925372799 / 9007199254740992
axiom cot_pi_16_34_bounds :
  ((cot_pi_16_34_lower : ℚ) : ℝ) ≤ cotangentTermV 16 34 ∧
  cotangentTermV 16 34 ≤ ((cot_pi_16_34_upper : ℚ) : ℝ)

def cot_pi_17_34_lower : ℚ := -313659157 / 1208925819614629174706176
def cot_pi_17_34_upper : ℚ := 998510359 / 1208925819614629174706176
axiom cot_pi_17_34_bounds :
  ((cot_pi_17_34_lower : ℚ) : ℝ) ≤ cotangentTermV 17 34 ∧
  cotangentTermV 17 34 ≤ ((cot_pi_17_34_upper : ℚ) : ℝ)

def cot_pi_18_34_lower : ℚ := -6677119402982369 / 72057594037927936
def cot_pi_18_34_upper : ℚ := -6677119402982313 / 72057594037927936
axiom cot_pi_18_34_bounds :
  ((cot_pi_18_34_lower : ℚ) : ℝ) ≤ cotangentTermV 18 34 ∧
  cotangentTermV 18 34 ≤ ((cot_pi_18_34_upper : ℚ) : ℝ)

def cot_pi_19_34_lower : ℚ := -6734949391671685 / 36028797018963968
def cot_pi_19_34_upper : ℚ := -6734949391671637 / 36028797018963968
axiom cot_pi_19_34_bounds :
  ((cot_pi_19_34_lower : ℚ) : ℝ) ≤ cotangentTermV 19 34 ∧
  cotangentTermV 19 34 ≤ ((cot_pi_19_34_upper : ℚ) : ℝ)

def cot_pi_20_34_lower : ℚ := -5125538287992107 / 18014398509481984
def cot_pi_20_34_upper : ℚ := -5125538287992087 / 18014398509481984
axiom cot_pi_20_34_bounds :
  ((cot_pi_20_34_lower : ℚ) : ℝ) ≤ cotangentTermV 20 34 ∧
  cotangentTermV 20 34 ≤ ((cot_pi_20_34_upper : ℚ) : ℝ)

def cot_pi_21_34_lower : ℚ := -6978815162229051 / 18014398509481984
def cot_pi_21_34_upper : ℚ := -6978815162229013 / 18014398509481984
axiom cot_pi_21_34_bounds :
  ((cot_pi_21_34_lower : ℚ) : ℝ) ≤ cotangentTermV 21 34 ∧
  cotangentTermV 21 34 ≤ ((cot_pi_21_34_upper : ℚ) : ℝ)

def cot_pi_22_34_lower : ℚ := -8970104616069303 / 18014398509481984
def cot_pi_22_34_upper : ℚ := -8970104616069251 / 18014398509481984
axiom cot_pi_22_34_bounds :
  ((cot_pi_22_34_lower : ℚ) : ℝ) ≤ cotangentTermV 22 34 ∧
  cotangentTermV 22 34 ≤ ((cot_pi_22_34_upper : ℚ) : ℝ)

def cot_pi_23_34_lower : ℚ := -5577021664085309 / 9007199254740992
def cot_pi_23_34_upper : ℚ := -5577021664085277 / 9007199254740992
axiom cot_pi_23_34_bounds :
  ((cot_pi_23_34_lower : ℚ) : ℝ) ≤ cotangentTermV 23 34 ∧
  cotangentTermV 23 34 ≤ ((cot_pi_23_34_upper : ℚ) : ℝ)

def cot_pi_24_34_lower : ℚ := -6801921139191381 / 9007199254740992
def cot_pi_24_34_upper : ℚ := -6801921139191357 / 9007199254740992
axiom cot_pi_24_34_bounds :
  ((cot_pi_24_34_lower : ℚ) : ℝ) ≤ cotangentTermV 24 34 ∧
  cotangentTermV 24 34 ≤ ((cot_pi_24_34_upper : ℚ) : ℝ)

def cot_pi_25_34_lower : ℚ := -32074793210659 / 35184372088832
def cot_pi_25_34_upper : ℚ := -4105573530964339 / 4503599627370496
axiom cot_pi_25_34_bounds :
  ((cot_pi_25_34_lower : ℚ) : ℝ) ≤ cotangentTermV 25 34 ∧
  cotangentTermV 25 34 ≤ ((cot_pi_25_34_upper : ℚ) : ℝ)

def cot_pi_26_34_lower : ℚ := -1235053364084287 / 1125899906842624
def cot_pi_26_34_upper : ℚ := -2470106728168561 / 2251799813685248
axiom cot_pi_26_34_bounds :
  ((cot_pi_26_34_lower : ℚ) : ℝ) ≤ cotangentTermV 26 34 ∧
  cotangentTermV 26 34 ≤ ((cot_pi_26_34_upper : ℚ) : ℝ)

def cot_pi_27_34_lower : ℚ := -2981864856795873 / 2251799813685248
def cot_pi_27_34_upper : ℚ := -2981864856795857 / 2251799813685248
axiom cot_pi_27_34_bounds :
  ((cot_pi_27_34_lower : ℚ) : ℝ) ≤ cotangentTermV 27 34 ∧
  cotangentTermV 27 34 ≤ ((cot_pi_27_34_upper : ℚ) : ℝ)

def cot_pi_28_34_lower : ℚ := -1818390785019325 / 1125899906842624
def cot_pi_28_34_upper : ℚ := -909195392509659 / 562949953421312
axiom cot_pi_28_34_bounds :
  ((cot_pi_28_34_lower : ℚ) : ℝ) ≤ cotangentTermV 28 34 ∧
  cotangentTermV 28 34 ≤ ((cot_pi_28_34_upper : ℚ) : ℝ)

def cot_pi_29_34_lower : ℚ := -2261111823302177 / 1125899906842624
def cot_pi_29_34_upper : ℚ := -2261111823302163 / 1125899906842624
axiom cot_pi_29_34_bounds :
  ((cot_pi_29_34_lower : ℚ) : ℝ) ≤ cotangentTermV 29 34 ∧
  cotangentTermV 29 34 ≤ ((cot_pi_29_34_upper : ℚ) : ℝ)

def cot_pi_30_34_lower : ℚ := -2906282675807893 / 1125899906842624
def cot_pi_30_34_upper : ℚ := -22705333404749 / 8796093022208
axiom cot_pi_30_34_bounds :
  ((cot_pi_30_34_lower : ℚ) : ℝ) ≤ cotangentTermV 30 34 ∧
  cotangentTermV 30 34 ≤ ((cot_pi_30_34_upper : ℚ) : ℝ)

def cot_pi_31_34_lower : ℚ := -247320482064885 / 70368744177664
def cot_pi_31_34_upper : ℚ := -1978563856519069 / 562949953421312
axiom cot_pi_31_34_bounds :
  ((cot_pi_31_34_lower : ℚ) : ℝ) ≤ cotangentTermV 31 34 ∧
  cotangentTermV 31 34 ≤ ((cot_pi_31_34_upper : ℚ) : ℝ)

def cot_pi_32_34_lower : ℚ := -6023032520105521 / 1125899906842624
def cot_pi_32_34_upper : ℚ := -6023032520105471 / 1125899906842624
axiom cot_pi_32_34_bounds :
  ((cot_pi_32_34_lower : ℚ) : ℝ) ≤ cotangentTermV 32 34 ∧
  cotangentTermV 32 34 ≤ ((cot_pi_32_34_upper : ℚ) : ℝ)

def cot_pi_33_34_lower : ℚ := -759399689430167 / 70368744177664
def cot_pi_33_34_upper : ℚ := -1518799378860297 / 140737488355328
axiom cot_pi_33_34_bounds :
  ((cot_pi_33_34_lower : ℚ) : ℝ) ≤ cotangentTermV 33 34 ∧
  cotangentTermV 33 34 ≤ ((cot_pi_33_34_upper : ℚ) : ℝ)

def cot_pi_1_35_lower : ℚ := 6254886268896339 / 562949953421312
def cot_pi_1_35_upper : ℚ := 6254886268896345 / 562949953421312
axiom cot_pi_1_35_bounds :
  ((cot_pi_1_35_lower : ℚ) : ℝ) ≤ cotangentTermV 1 35 ∧
  cotangentTermV 1 35 ≤ ((cot_pi_1_35_upper : ℚ) : ℝ)

def cot_pi_2_35_lower : ℚ := 3102109928020983 / 562949953421312
def cot_pi_2_35_upper : ℚ := 1551054964010493 / 281474976710656
axiom cot_pi_2_35_bounds :
  ((cot_pi_2_35_lower : ℚ) : ℝ) ≤ cotangentTermV 2 35 ∧
  cotangentTermV 2 35 ≤ ((cot_pi_2_35_upper : ℚ) : ℝ)

def cot_pi_3_35_lower : ℚ := 127487709073883 / 35184372088832
def cot_pi_3_35_upper : ℚ := 1019901672591065 / 281474976710656
axiom cot_pi_3_35_bounds :
  ((cot_pi_3_35_lower : ℚ) : ℝ) ≤ cotangentTermV 3 35 ∧
  cotangentTermV 3 35 ≤ ((cot_pi_3_35_upper : ℚ) : ℝ)

def cot_pi_4_35_lower : ℚ := 2999949573484729 / 1125899906842624
def cot_pi_4_35_upper : ℚ := 749987393371183 / 281474976710656
axiom cot_pi_4_35_bounds :
  ((cot_pi_4_35_lower : ℚ) : ℝ) ≤ cotangentTermV 4 35 ∧
  cotangentTermV 4 35 ≤ ((cot_pi_4_35_upper : ℚ) : ℝ)

def cot_pi_5_35_lower : ℚ := 4675910493915015 / 2251799813685248
def cot_pi_5_35_upper : ℚ := 4675910493915021 / 2251799813685248
axiom cot_pi_5_35_bounds :
  ((cot_pi_5_35_lower : ℚ) : ℝ) ≤ cotangentTermV 5 35 ∧
  cotangentTermV 5 35 ≤ ((cot_pi_5_35_upper : ℚ) : ℝ)

def cot_pi_6_35_lower : ℚ := 7537756119555601 / 4503599627370496
def cot_pi_6_35_upper : ℚ := 7537756119555609 / 4503599627370496
axiom cot_pi_6_35_bounds :
  ((cot_pi_6_35_lower : ℚ) : ℝ) ≤ cotangentTermV 6 35 ∧
  cotangentTermV 6 35 ≤ ((cot_pi_6_35_upper : ℚ) : ℝ)

def cot_pi_7_35_lower : ℚ := 6198673104153461 / 4503599627370496
def cot_pi_7_35_upper : ℚ := 6198673104153469 / 4503599627370496
axiom cot_pi_7_35_bounds :
  ((cot_pi_7_35_lower : ℚ) : ℝ) ≤ cotangentTermV 7 35 ∧
  cotangentTermV 7 35 ≤ ((cot_pi_7_35_upper : ℚ) : ℝ)

def cot_pi_8_35_lower : ℚ := 5154784541422451 / 4503599627370496
def cot_pi_8_35_upper : ℚ := 5154784541422457 / 4503599627370496
axiom cot_pi_8_35_bounds :
  ((cot_pi_8_35_lower : ℚ) : ℝ) ≤ cotangentTermV 8 35 ∧
  cotangentTermV 8 35 ≤ ((cot_pi_8_35_upper : ℚ) : ℝ)

def cot_pi_9_35_lower : ℚ := 8611764261817283 / 9007199254740992
def cot_pi_9_35_upper : ℚ := 8611764261817293 / 9007199254740992
axiom cot_pi_9_35_bounds :
  ((cot_pi_9_35_lower : ℚ) : ℝ) ≤ cotangentTermV 9 35 ∧
  cotangentTermV 9 35 ≤ ((cot_pi_9_35_upper : ℚ) : ℝ)

def cot_pi_10_35_lower : ℚ := 3591500857008679 / 4503599627370496
def cot_pi_10_35_upper : ℚ := 3591500857008683 / 4503599627370496
axiom cot_pi_10_35_bounds :
  ((cot_pi_10_35_lower : ℚ) : ℝ) ≤ cotangentTermV 10 35 ∧
  cotangentTermV 10 35 ≤ ((cot_pi_10_35_upper : ℚ) : ℝ)

def cot_pi_11_35_lower : ℚ := 5945600171883123 / 9007199254740992
def cot_pi_11_35_upper : ℚ := 5945600171883139 / 9007199254740992
axiom cot_pi_11_35_bounds :
  ((cot_pi_11_35_lower : ℚ) : ℝ) ≤ cotangentTermV 11 35 ∧
  cotangentTermV 11 35 ≤ ((cot_pi_11_35_upper : ℚ) : ℝ)

def cot_pi_12_35_lower : ℚ := 1211745151168417 / 2251799813685248
def cot_pi_12_35_upper : ℚ := 2423490302336837 / 4503599627370496
axiom cot_pi_12_35_bounds :
  ((cot_pi_12_35_lower : ℚ) : ℝ) ≤ cotangentTermV 12 35 ∧
  cotangentTermV 12 35 ≤ ((cot_pi_12_35_upper : ℚ) : ℝ)

def cot_pi_13_35_lower : ℚ := 481232715025159 / 1125899906842624
def cot_pi_13_35_upper : ℚ := 1924930860100643 / 4503599627370496
axiom cot_pi_13_35_bounds :
  ((cot_pi_13_35_lower : ℚ) : ℝ) ≤ cotangentTermV 13 35 ∧
  cotangentTermV 13 35 ≤ ((cot_pi_13_35_upper : ℚ) : ℝ)

def cot_pi_14_35_lower : ℚ := 2926616445759701 / 9007199254740992
def cot_pi_14_35_upper : ℚ := 1463308222879853 / 4503599627370496
axiom cot_pi_14_35_bounds :
  ((cot_pi_14_35_lower : ℚ) : ℝ) ≤ cotangentTermV 14 35 ∧
  cotangentTermV 14 35 ≤ ((cot_pi_14_35_upper : ℚ) : ℝ)

def cot_pi_15_35_lower : ℚ := 1027917226213225 / 4503599627370496
def cot_pi_15_35_upper : ℚ := 4111668904852923 / 18014398509481984
axiom cot_pi_15_35_bounds :
  ((cot_pi_15_35_lower : ℚ) : ℝ) ≤ cotangentTermV 15 35 ∧
  cotangentTermV 15 35 ≤ ((cot_pi_15_35_upper : ℚ) : ℝ)

def cot_pi_16_35_lower : ℚ := 610054020133757 / 4503599627370496
def cot_pi_16_35_upper : ℚ := 1220108040267517 / 9007199254740992
axiom cot_pi_16_35_bounds :
  ((cot_pi_16_35_lower : ℚ) : ℝ) ≤ cotangentTermV 16 35 ∧
  cotangentTermV 16 35 ≤ ((cot_pi_16_35_upper : ℚ) : ℝ)

def cot_pi_17_35_lower : ℚ := 6472220559389025 / 144115188075855872
def cot_pi_17_35_upper : ℚ := 6472220559389185 / 144115188075855872
axiom cot_pi_17_35_bounds :
  ((cot_pi_17_35_lower : ℚ) : ℝ) ≤ cotangentTermV 17 35 ∧
  cotangentTermV 17 35 ≤ ((cot_pi_17_35_upper : ℚ) : ℝ)

def cot_pi_18_35_lower : ℚ := -6472220559389075 / 144115188075855872
def cot_pi_18_35_upper : ℚ := -6472220559389037 / 144115188075855872
axiom cot_pi_18_35_bounds :
  ((cot_pi_18_35_lower : ℚ) : ℝ) ≤ cotangentTermV 18 35 ∧
  cotangentTermV 18 35 ≤ ((cot_pi_18_35_upper : ℚ) : ℝ)

def cot_pi_19_35_lower : ℚ := -4880432161070073 / 36028797018963968
def cot_pi_19_35_upper : ℚ := -4880432161070027 / 36028797018963968
axiom cot_pi_19_35_bounds :
  ((cot_pi_19_35_lower : ℚ) : ℝ) ≤ cotangentTermV 19 35 ∧
  cotangentTermV 19 35 ≤ ((cot_pi_19_35_upper : ℚ) : ℝ)

def cot_pi_20_35_lower : ℚ := -8223337809705817 / 36028797018963968
def cot_pi_20_35_upper : ℚ := -8223337809705801 / 36028797018963968
axiom cot_pi_20_35_bounds :
  ((cot_pi_20_35_lower : ℚ) : ℝ) ≤ cotangentTermV 20 35 ∧
  cotangentTermV 20 35 ≤ ((cot_pi_20_35_upper : ℚ) : ℝ)

def cot_pi_21_35_lower : ℚ := -2926616445759707 / 9007199254740992
def cot_pi_21_35_upper : ℚ := -2926616445759689 / 9007199254740992
axiom cot_pi_21_35_bounds :
  ((cot_pi_21_35_lower : ℚ) : ℝ) ≤ cotangentTermV 21 35 ∧
  cotangentTermV 21 35 ≤ ((cot_pi_21_35_upper : ℚ) : ℝ)

def cot_pi_22_35_lower : ℚ := -3849861720201283 / 9007199254740992
def cot_pi_22_35_upper : ℚ := -3849861720201263 / 9007199254740992
axiom cot_pi_22_35_bounds :
  ((cot_pi_22_35_lower : ℚ) : ℝ) ≤ cotangentTermV 22 35 ∧
  cotangentTermV 22 35 ≤ ((cot_pi_22_35_upper : ℚ) : ℝ)

def cot_pi_23_35_lower : ℚ := -2423490302336839 / 4503599627370496
def cot_pi_23_35_upper : ℚ := -2423490302336825 / 4503599627370496
axiom cot_pi_23_35_bounds :
  ((cot_pi_23_35_lower : ℚ) : ℝ) ≤ cotangentTermV 23 35 ∧
  cotangentTermV 23 35 ≤ ((cot_pi_23_35_upper : ℚ) : ℝ)

def cot_pi_24_35_lower : ℚ := -5945600171883133 / 9007199254740992
def cot_pi_24_35_upper : ℚ := -5945600171883123 / 9007199254740992
axiom cot_pi_24_35_bounds :
  ((cot_pi_24_35_lower : ℚ) : ℝ) ≤ cotangentTermV 24 35 ∧
  cotangentTermV 24 35 ≤ ((cot_pi_24_35_upper : ℚ) : ℝ)

def cot_pi_25_35_lower : ℚ := -7183001714017371 / 9007199254740992
def cot_pi_25_35_upper : ℚ := -7183001714017335 / 9007199254740992
axiom cot_pi_25_35_bounds :
  ((cot_pi_25_35_lower : ℚ) : ℝ) ≤ cotangentTermV 25 35 ∧
  cotangentTermV 25 35 ≤ ((cot_pi_25_35_upper : ℚ) : ℝ)

def cot_pi_26_35_lower : ℚ := -4305882130908649 / 4503599627370496
def cot_pi_26_35_upper : ℚ := -1076470532727157 / 1125899906842624
axiom cot_pi_26_35_bounds :
  ((cot_pi_26_35_lower : ℚ) : ℝ) ≤ cotangentTermV 26 35 ∧
  cotangentTermV 26 35 ≤ ((cot_pi_26_35_upper : ℚ) : ℝ)

def cot_pi_27_35_lower : ℚ := -2577392270711231 / 2251799813685248
def cot_pi_27_35_upper : ℚ := -1288696135355609 / 1125899906842624
axiom cot_pi_27_35_bounds :
  ((cot_pi_27_35_lower : ℚ) : ℝ) ≤ cotangentTermV 27 35 ∧
  cotangentTermV 27 35 ≤ ((cot_pi_27_35_upper : ℚ) : ℝ)

def cot_pi_28_35_lower : ℚ := -6198673104153469 / 4503599627370496
def cot_pi_28_35_upper : ℚ := -6198673104153459 / 4503599627370496
axiom cot_pi_28_35_bounds :
  ((cot_pi_28_35_lower : ℚ) : ℝ) ≤ cotangentTermV 28 35 ∧
  cotangentTermV 28 35 ≤ ((cot_pi_28_35_upper : ℚ) : ℝ)

def cot_pi_29_35_lower : ℚ := -235554878736113 / 140737488355328
def cot_pi_29_35_upper : ℚ := -1884439029888893 / 1125899906842624
axiom cot_pi_29_35_bounds :
  ((cot_pi_29_35_lower : ℚ) : ℝ) ≤ cotangentTermV 29 35 ∧
  cotangentTermV 29 35 ≤ ((cot_pi_29_35_upper : ℚ) : ℝ)

def cot_pi_30_35_lower : ℚ := -4675910493915027 / 2251799813685248
def cot_pi_30_35_upper : ℚ := -4675910493914997 / 2251799813685248
axiom cot_pi_30_35_bounds :
  ((cot_pi_30_35_lower : ℚ) : ℝ) ≤ cotangentTermV 30 35 ∧
  cotangentTermV 30 35 ≤ ((cot_pi_30_35_upper : ℚ) : ℝ)

def cot_pi_31_35_lower : ℚ := -5999899146969473 / 2251799813685248
def cot_pi_31_35_upper : ℚ := -5999899146969429 / 2251799813685248
axiom cot_pi_31_35_bounds :
  ((cot_pi_31_35_lower : ℚ) : ℝ) ≤ cotangentTermV 31 35 ∧
  cotangentTermV 31 35 ≤ ((cot_pi_31_35_upper : ℚ) : ℝ)

def cot_pi_32_35_lower : ℚ := -4079606690364261 / 1125899906842624
def cot_pi_32_35_upper : ℚ := -4079606690364251 / 1125899906842624
axiom cot_pi_32_35_bounds :
  ((cot_pi_32_35_lower : ℚ) : ℝ) ≤ cotangentTermV 32 35 ∧
  cotangentTermV 32 35 ≤ ((cot_pi_32_35_upper : ℚ) : ℝ)

def cot_pi_33_35_lower : ℚ := -3102109928020995 / 562949953421312
def cot_pi_33_35_upper : ℚ := -1551054964010477 / 281474976710656
axiom cot_pi_33_35_bounds :
  ((cot_pi_33_35_lower : ℚ) : ℝ) ≤ cotangentTermV 33 35 ∧
  cotangentTermV 33 35 ≤ ((cot_pi_33_35_upper : ℚ) : ℝ)

def cot_pi_34_35_lower : ℚ := -3127443134448191 / 281474976710656
def cot_pi_34_35_upper : ℚ := -3127443134448113 / 281474976710656
axiom cot_pi_34_35_bounds :
  ((cot_pi_34_35_lower : ℚ) : ℝ) ≤ cotangentTermV 34 35 ∧
  cotangentTermV 34 35 ≤ ((cot_pi_34_35_upper : ℚ) : ℝ)

def cot_pi_1_36_lower : ℚ := 6434547411442653 / 562949953421312
def cot_pi_1_36_upper : ℚ := 6434547411442661 / 562949953421312
axiom cot_pi_1_36_bounds :
  ((cot_pi_1_36_lower : ℚ) : ℝ) ≤ cotangentTermV 1 36 ∧
  cotangentTermV 1 36 ≤ ((cot_pi_1_36_upper : ℚ) : ℝ)

def cot_pi_2_36_lower : ℚ := 3192647836192921 / 562949953421312
def cot_pi_2_36_upper : ℚ := 3192647836192925 / 562949953421312
axiom cot_pi_2_36_bounds :
  ((cot_pi_2_36_lower : ℚ) : ℝ) ≤ cotangentTermV 2 36 ∧
  cotangentTermV 2 36 ≤ ((cot_pi_2_36_upper : ℚ) : ℝ)

def cot_pi_3_36_lower : ℚ := 8403831313147473 / 2251799813685248
def cot_pi_3_36_upper : ℚ := 8403831313147485 / 2251799813685248
axiom cot_pi_3_36_bounds :
  ((cot_pi_3_36_lower : ℚ) : ℝ) ≤ cotangentTermV 3 36 ∧
  cotangentTermV 3 36 ≤ ((cot_pi_3_36_upper : ℚ) : ℝ)

def cot_pi_4_36_lower : ℚ := 1546692285308085 / 562949953421312
def cot_pi_4_36_upper : ℚ := 1546692285308087 / 562949953421312
axiom cot_pi_4_36_bounds :
  ((cot_pi_4_36_lower : ℚ) : ℝ) ≤ cotangentTermV 4 36 ∧
  cotangentTermV 4 36 ≤ ((cot_pi_4_36_upper : ℚ) : ℝ)

def cot_pi_5_36_lower : ℚ := 4829000284050147 / 2251799813685248
def cot_pi_5_36_upper : ℚ := 4829000284050153 / 2251799813685248
axiom cot_pi_5_36_bounds :
  ((cot_pi_5_36_lower : ℚ) : ℝ) ≤ cotangentTermV 5 36 ∧
  cotangentTermV 5 36 ≤ ((cot_pi_5_36_upper : ℚ) : ℝ)

def cot_pi_6_36_lower : ℚ := 1950115842888489 / 1125899906842624
def cot_pi_6_36_upper : ℚ := 487528960722123 / 281474976710656
axiom cot_pi_6_36_bounds :
  ((cot_pi_6_36_lower : ℚ) : ℝ) ≤ cotangentTermV 6 36 ∧
  cotangentTermV 6 36 ≤ ((cot_pi_6_36_upper : ℚ) : ℝ)

def cot_pi_7_36_lower : ℚ := 6431806830993699 / 4503599627370496
def cot_pi_7_36_upper : ℚ := 6431806830993709 / 4503599627370496
axiom cot_pi_7_36_bounds :
  ((cot_pi_7_36_lower : ℚ) : ℝ) ≤ cotangentTermV 7 36 ∧
  cotangentTermV 7 36 ≤ ((cot_pi_7_36_upper : ℚ) : ℝ)

def cot_pi_8_36_lower : ℚ := 2683590517762365 / 2251799813685248
def cot_pi_8_36_upper : ℚ := 2683590517762369 / 2251799813685248
axiom cot_pi_8_36_bounds :
  ((cot_pi_8_36_lower : ℚ) : ℝ) ≤ cotangentTermV 8 36 ∧
  cotangentTermV 8 36 ≤ ((cot_pi_8_36_upper : ℚ) : ℝ)

def cot_pi_9_36_lower : ℚ := 2251799813685247 / 2251799813685248
def cot_pi_9_36_upper : ℚ := 2251799813685249 / 2251799813685248
axiom cot_pi_9_36_bounds :
  ((cot_pi_9_36_lower : ℚ) : ℝ) ≤ cotangentTermV 9 36 ∧
  cotangentTermV 9 36 ≤ ((cot_pi_9_36_upper : ℚ) : ℝ)

def cot_pi_10_36_lower : ℚ := 7557937572593433 / 9007199254740992
def cot_pi_10_36_upper : ℚ := 7557937572593445 / 9007199254740992
axiom cot_pi_10_36_bounds :
  ((cot_pi_10_36_lower : ℚ) : ℝ) ≤ cotangentTermV 10 36 ∧
  cotangentTermV 10 36 ≤ ((cot_pi_10_36_upper : ℚ) : ℝ)

def cot_pi_11_36_lower : ℚ := 3153454408163259 / 4503599627370496
def cot_pi_11_36_upper : ℚ := 3153454408163267 / 4503599627370496
axiom cot_pi_11_36_bounds :
  ((cot_pi_11_36_lower : ℚ) : ℝ) ≤ cotangentTermV 11 36 ∧
  cotangentTermV 11 36 ≤ ((cot_pi_11_36_upper : ℚ) : ℝ)

def cot_pi_12_36_lower : ℚ := 5200308914369303 / 9007199254740992
def cot_pi_12_36_upper : ℚ := 5200308914369315 / 9007199254740992
axiom cot_pi_12_36_bounds :
  ((cot_pi_12_36_lower : ℚ) : ℝ) ≤ cotangentTermV 12 36 ∧
  cotangentTermV 12 36 ≤ ((cot_pi_12_36_upper : ℚ) : ℝ)

def cot_pi_13_36_lower : ℚ := 8400251982027431 / 18014398509481984
def cot_pi_13_36_upper : ℚ := 8400251982027459 / 18014398509481984
axiom cot_pi_13_36_bounds :
  ((cot_pi_13_36_lower : ℚ) : ℝ) ≤ cotangentTermV 13 36 ∧
  cotangentTermV 13 36 ≤ ((cot_pi_13_36_upper : ℚ) : ℝ)

def cot_pi_14_36_lower : ℚ := 6556704845660877 / 18014398509481984
def cot_pi_14_36_upper : ℚ := 6556704845660895 / 18014398509481984
axiom cot_pi_14_36_bounds :
  ((cot_pi_14_36_lower : ℚ) : ℝ) ≤ cotangentTermV 14 36 ∧
  cotangentTermV 14 36 ≤ ((cot_pi_14_36_upper : ℚ) : ℝ)

def cot_pi_15_36_lower : ℚ := 1206735883187027 / 4503599627370496
def cot_pi_15_36_upper : ℚ := 2413471766374067 / 9007199254740992
axiom cot_pi_15_36_bounds :
  ((cot_pi_15_36_lower : ℚ) : ℝ) ≤ cotangentTermV 15 36 ∧
  cotangentTermV 15 36 ≤ ((cot_pi_15_36_upper : ℚ) : ℝ)

def cot_pi_16_36_lower : ℚ := 6352848996912047 / 36028797018963968
def cot_pi_16_36_upper : ℚ := 6352848996912077 / 36028797018963968
axiom cot_pi_16_36_bounds :
  ((cot_pi_16_36_lower : ℚ) : ℝ) ≤ cotangentTermV 16 36 ∧
  cotangentTermV 16 36 ≤ ((cot_pi_16_36_upper : ℚ) : ℝ)

def cot_pi_17_36_lower : ℚ := 1576055649817969 / 18014398509481984
def cot_pi_17_36_upper : ℚ := 3152111299635979 / 36028797018963968
axiom cot_pi_17_36_bounds :
  ((cot_pi_17_36_lower : ℚ) : ℝ) ≤ cotangentTermV 17 36 ∧
  cotangentTermV 17 36 ≤ ((cot_pi_17_36_upper : ℚ) : ℝ)

def cot_pi_18_36_lower : ℚ := -488112139 / 9671406556917033397649408
def cot_pi_18_36_upper : ℚ := 1671954449 / 9671406556917033397649408
axiom cot_pi_18_36_bounds :
  ((cot_pi_18_36_lower : ℚ) : ℝ) ≤ cotangentTermV 18 36 ∧
  cotangentTermV 18 36 ≤ ((cot_pi_18_36_upper : ℚ) : ℝ)

def cot_pi_19_36_lower : ℚ := -3152111299635959 / 36028797018963968
def cot_pi_19_36_upper : ℚ := -3152111299635933 / 36028797018963968
axiom cot_pi_19_36_bounds :
  ((cot_pi_19_36_lower : ℚ) : ℝ) ≤ cotangentTermV 19 36 ∧
  cotangentTermV 19 36 ≤ ((cot_pi_19_36_upper : ℚ) : ℝ)

def cot_pi_20_36_lower : ℚ := -3176424498456033 / 18014398509481984
def cot_pi_20_36_upper : ℚ := -3176424498456017 / 18014398509481984
axiom cot_pi_20_36_bounds :
  ((cot_pi_20_36_lower : ℚ) : ℝ) ≤ cotangentTermV 20 36 ∧
  cotangentTermV 20 36 ≤ ((cot_pi_20_36_upper : ℚ) : ℝ)

def cot_pi_21_36_lower : ℚ := -1206735883187031 / 4503599627370496
def cot_pi_21_36_upper : ℚ := -2413471766374049 / 9007199254740992
axiom cot_pi_21_36_bounds :
  ((cot_pi_21_36_lower : ℚ) : ℝ) ≤ cotangentTermV 21 36 ∧
  cotangentTermV 21 36 ≤ ((cot_pi_21_36_upper : ℚ) : ℝ)

def cot_pi_22_36_lower : ℚ := -1639176211415223 / 4503599627370496
def cot_pi_22_36_upper : ℚ := -819588105707607 / 2251799813685248
axiom cot_pi_22_36_bounds :
  ((cot_pi_22_36_lower : ℚ) : ℝ) ≤ cotangentTermV 22 36 ∧
  cotangentTermV 22 36 ≤ ((cot_pi_22_36_upper : ℚ) : ℝ)

def cot_pi_23_36_lower : ℚ := -8400251982027453 / 18014398509481984
def cot_pi_23_36_upper : ℚ := -8400251982027403 / 18014398509481984
axiom cot_pi_23_36_bounds :
  ((cot_pi_23_36_lower : ℚ) : ℝ) ≤ cotangentTermV 23 36 ∧
  cotangentTermV 23 36 ≤ ((cot_pi_23_36_upper : ℚ) : ℝ)

def cot_pi_24_36_lower : ℚ := -2600154457184657 / 4503599627370496
def cot_pi_24_36_upper : ℚ := -325019307148081 / 562949953421312
axiom cot_pi_24_36_bounds :
  ((cot_pi_24_36_lower : ℚ) : ℝ) ≤ cotangentTermV 24 36 ∧
  cotangentTermV 24 36 ≤ ((cot_pi_24_36_upper : ℚ) : ℝ)

def cot_pi_25_36_lower : ℚ := -6306908816326529 / 9007199254740992
def cot_pi_25_36_upper : ℚ := -6306908816326495 / 9007199254740992
axiom cot_pi_25_36_bounds :
  ((cot_pi_25_36_lower : ℚ) : ℝ) ≤ cotangentTermV 25 36 ∧
  cotangentTermV 25 36 ≤ ((cot_pi_25_36_upper : ℚ) : ℝ)

def cot_pi_26_36_lower : ℚ := -3778968786296725 / 4503599627370496
def cot_pi_26_36_upper : ℚ := -1889484393148353 / 2251799813685248
axiom cot_pi_26_36_bounds :
  ((cot_pi_26_36_lower : ℚ) : ℝ) ≤ cotangentTermV 26 36 ∧
  cotangentTermV 26 36 ≤ ((cot_pi_26_36_upper : ℚ) : ℝ)

def cot_pi_27_36_lower : ℚ := -4503599627370503 / 4503599627370496
def cot_pi_27_36_upper : ℚ := -9007199254740961 / 9007199254740992
axiom cot_pi_27_36_bounds :
  ((cot_pi_27_36_lower : ℚ) : ℝ) ≤ cotangentTermV 27 36 ∧
  cotangentTermV 27 36 ≤ ((cot_pi_27_36_upper : ℚ) : ℝ)

def cot_pi_28_36_lower : ℚ := -5367181035524741 / 4503599627370496
def cot_pi_28_36_upper : ℚ := -5367181035524721 / 4503599627370496
axiom cot_pi_28_36_bounds :
  ((cot_pi_28_36_lower : ℚ) : ℝ) ≤ cotangentTermV 28 36 ∧
  cotangentTermV 28 36 ≤ ((cot_pi_28_36_upper : ℚ) : ℝ)

def cot_pi_29_36_lower : ℚ := -6431806830993711 / 4503599627370496
def cot_pi_29_36_upper : ℚ := -6431806830993677 / 4503599627370496
axiom cot_pi_29_36_bounds :
  ((cot_pi_29_36_lower : ℚ) : ℝ) ≤ cotangentTermV 29 36 ∧
  cotangentTermV 29 36 ≤ ((cot_pi_29_36_upper : ℚ) : ℝ)

def cot_pi_30_36_lower : ℚ := -975057921444247 / 562949953421312
def cot_pi_30_36_upper : ℚ := -1950115842888483 / 1125899906842624
axiom cot_pi_30_36_bounds :
  ((cot_pi_30_36_lower : ℚ) : ℝ) ≤ cotangentTermV 30 36 ∧
  cotangentTermV 30 36 ≤ ((cot_pi_30_36_upper : ℚ) : ℝ)

def cot_pi_31_36_lower : ℚ := -4829000284050157 / 2251799813685248
def cot_pi_31_36_upper : ℚ := -4829000284050127 / 2251799813685248
axiom cot_pi_31_36_bounds :
  ((cot_pi_31_36_lower : ℚ) : ℝ) ≤ cotangentTermV 31 36 ∧
  cotangentTermV 31 36 ≤ ((cot_pi_31_36_upper : ℚ) : ℝ)

def cot_pi_32_36_lower : ℚ := -1546692285308089 / 562949953421312
def cot_pi_32_36_upper : ℚ := -3093384570616163 / 1125899906842624
axiom cot_pi_32_36_bounds :
  ((cot_pi_32_36_lower : ℚ) : ℝ) ≤ cotangentTermV 32 36 ∧
  cotangentTermV 32 36 ≤ ((cot_pi_32_36_upper : ℚ) : ℝ)

def cot_pi_33_36_lower : ℚ := -8403831313147493 / 2251799813685248
def cot_pi_33_36_upper : ℚ := -8403831313147415 / 2251799813685248
axiom cot_pi_33_36_bounds :
  ((cot_pi_33_36_lower : ℚ) : ℝ) ≤ cotangentTermV 33 36 ∧
  cotangentTermV 33 36 ≤ ((cot_pi_33_36_upper : ℚ) : ℝ)

def cot_pi_34_36_lower : ℚ := -3192647836192937 / 562949953421312
def cot_pi_34_36_upper : ℚ := -3192647836192895 / 562949953421312
axiom cot_pi_34_36_bounds :
  ((cot_pi_34_36_lower : ℚ) : ℝ) ≤ cotangentTermV 34 36 ∧
  cotangentTermV 34 36 ≤ ((cot_pi_34_36_upper : ℚ) : ℝ)

def cot_pi_35_36_lower : ℚ := -6434547411442705 / 562949953421312
def cot_pi_35_36_upper : ℚ := -6434547411442543 / 562949953421312
axiom cot_pi_35_36_bounds :
  ((cot_pi_35_36_lower : ℚ) : ℝ) ≤ cotangentTermV 35 36 ∧
  cotangentTermV 35 36 ≤ ((cot_pi_35_36_upper : ℚ) : ℝ)

def cot_pi_1_37_lower : ℚ := 3307091593147563 / 281474976710656
def cot_pi_1_37_upper : ℚ := 3307091593147567 / 281474976710656
axiom cot_pi_1_37_bounds :
  ((cot_pi_1_37_lower : ℚ) : ℝ) ≤ cotangentTermV 1 37 ∧
  cotangentTermV 1 37 ≤ ((cot_pi_1_37_upper : ℚ) : ℝ)

def cot_pi_2_37_lower : ℚ := 1641567270989787 / 281474976710656
def cot_pi_2_37_upper : ℚ := 1641567270989789 / 281474976710656
axiom cot_pi_2_37_bounds :
  ((cot_pi_2_37_lower : ℚ) : ℝ) ≤ cotangentTermV 2 37 ∧
  cotangentTermV 2 37 ≤ ((cot_pi_2_37_upper : ℚ) : ℝ)

def cot_pi_3_37_lower : ℚ := 4324068646340031 / 1125899906842624
def cot_pi_3_37_upper : ℚ := 2162034323170019 / 562949953421312
axiom cot_pi_3_37_bounds :
  ((cot_pi_3_37_lower : ℚ) : ℝ) ≤ cotangentTermV 3 37 ∧
  cotangentTermV 3 37 ≤ ((cot_pi_3_37_upper : ℚ) : ℝ)

def cot_pi_4_37_lower : ℚ := 1593303539180311 / 562949953421312
def cot_pi_4_37_upper : ℚ := 1593303539180313 / 562949953421312
axiom cot_pi_4_37_bounds :
  ((cot_pi_4_37_lower : ℚ) : ℝ) ≤ cotangentTermV 4 37 ∧
  cotangentTermV 4 37 ≤ ((cot_pi_4_37_upper : ℚ) : ℝ)

def cot_pi_5_37_lower : ℚ := 4981543886133679 / 2251799813685248
def cot_pi_5_37_upper : ℚ := 4981543886133685 / 2251799813685248
axiom cot_pi_5_37_bounds :
  ((cot_pi_5_37_lower : ℚ) : ℝ) ≤ cotangentTermV 5 37 ∧
  cotangentTermV 5 37 ≤ ((cot_pi_5_37_upper : ℚ) : ℝ)

def cot_pi_6_37_lower : ℚ := 4030907111705009 / 2251799813685248
def cot_pi_6_37_upper : ℚ := 4030907111705015 / 2251799813685248
axiom cot_pi_6_37_bounds :
  ((cot_pi_6_37_lower : ℚ) : ℝ) ≤ cotangentTermV 6 37 ∧
  cotangentTermV 6 37 ≤ ((cot_pi_6_37_upper : ℚ) : ℝ)

def cot_pi_7_37_lower : ℚ := 6663292419545811 / 4503599627370496
def cot_pi_7_37_upper : ℚ := 6663292419545821 / 4503599627370496
axiom cot_pi_7_37_bounds :
  ((cot_pi_7_37_lower : ℚ) : ℝ) ≤ cotangentTermV 7 37 ∧
  cotangentTermV 7 37 ≤ ((cot_pi_7_37_upper : ℚ) : ℝ)

def cot_pi_8_37_lower : ℚ := 5577602668353883 / 4503599627370496
def cot_pi_8_37_upper : ℚ := 5577602668353893 / 4503599627370496
axiom cot_pi_8_37_bounds :
  ((cot_pi_8_37_lower : ℚ) : ℝ) ≤ cotangentTermV 8 37 ∧
  cotangentTermV 8 37 ≤ ((cot_pi_8_37_upper : ℚ) : ℝ)

def cot_pi_9_37_lower : ℚ := 2349485873308385 / 2251799813685248
def cot_pi_9_37_upper : ℚ := 2349485873308389 / 2251799813685248
axiom cot_pi_9_37_bounds :
  ((cot_pi_9_37_lower : ℚ) : ℝ) ≤ cotangentTermV 9 37 ∧
  cotangentTermV 9 37 ≤ ((cot_pi_9_37_upper : ℚ) : ℝ)

def cot_pi_10_37_lower : ℚ := 3963666192628433 / 4503599627370496
def cot_pi_10_37_upper : ℚ := 3963666192628439 / 4503599627370496
axiom cot_pi_10_37_bounds :
  ((cot_pi_10_37_lower : ℚ) : ℝ) ≤ cotangentTermV 10 37 ∧
  cotangentTermV 10 37 ≤ ((cot_pi_10_37_upper : ℚ) : ℝ)

def cot_pi_11_37_lower : ℚ := 6661689824698491 / 9007199254740992
def cot_pi_11_37_upper : ℚ := 6661689824698507 / 9007199254740992
axiom cot_pi_11_37_bounds :
  ((cot_pi_11_37_lower : ℚ) : ℝ) ≤ cotangentTermV 11 37 ∧
  cotangentTermV 11 37 ≤ ((cot_pi_11_37_upper : ℚ) : ℝ)

def cot_pi_12_37_lower : ℚ := 5545952527570477 / 9007199254740992
def cot_pi_12_37_upper : ℚ := 5545952527570491 / 9007199254740992
axiom cot_pi_12_37_bounds :
  ((cot_pi_12_37_lower : ℚ) : ℝ) ≤ cotangentTermV 12 37 ∧
  cotangentTermV 12 37 ≤ ((cot_pi_12_37_upper : ℚ) : ℝ)

def cot_pi_13_37_lower : ℚ := 4541334308770913 / 9007199254740992
def cot_pi_13_37_upper : ℚ := 4541334308770929 / 9007199254740992
axiom cot_pi_13_37_bounds :
  ((cot_pi_13_37_lower : ℚ) : ℝ) ≤ cotangentTermV 13 37 ∧
  cotangentTermV 13 37 ≤ ((cot_pi_13_37_upper : ℚ) : ℝ)

def cot_pi_14_37_lower : ℚ := 7238780694655121 / 18014398509481984
def cot_pi_14_37_upper : ℚ := 7238780694655139 / 18014398509481984
axiom cot_pi_14_37_bounds :
  ((cot_pi_14_37_lower : ℚ) : ℝ) ≤ cotangentTermV 14 37 ∧
  cotangentTermV 14 37 ≤ ((cot_pi_14_37_upper : ℚ) : ℝ)

def cot_pi_15_37_lower : ℚ := 689605941983693 / 2251799813685248
def cot_pi_15_37_upper : ℚ := 2758423767934785 / 9007199254740992
axiom cot_pi_15_37_bounds :
  ((cot_pi_15_37_lower : ℚ) : ℝ) ≤ cotangentTermV 15 37 ∧
  cotangentTermV 15 37 ≤ ((cot_pi_15_37_upper : ℚ) : ℝ)

def cot_pi_16_37_lower : ℚ := 485299983082703 / 2251799813685248
def cot_pi_16_37_upper : ℚ := 3882399864661639 / 18014398509481984
axiom cot_pi_16_37_bounds :
  ((cot_pi_16_37_lower : ℚ) : ℝ) ≤ cotangentTermV 16 37 ∧
  cotangentTermV 16 37 ≤ ((cot_pi_16_37_upper : ℚ) : ℝ)

def cot_pi_17_37_lower : ℚ := 1153416986921995 / 9007199254740992
def cot_pi_17_37_upper : ℚ := 576708493461003 / 4503599627370496
axiom cot_pi_17_37_bounds :
  ((cot_pi_17_37_lower : ℚ) : ℝ) ≤ cotangentTermV 17 37 ∧
  cotangentTermV 17 37 ≤ ((cot_pi_17_37_upper : ℚ) : ℝ)

def cot_pi_18_37_lower : ℚ := 6121938053857871 / 144115188075855872
def cot_pi_18_37_upper : ℚ := 6121938053857973 / 144115188075855872
axiom cot_pi_18_37_bounds :
  ((cot_pi_18_37_lower : ℚ) : ℝ) ≤ cotangentTermV 18 37 ∧
  cotangentTermV 18 37 ≤ ((cot_pi_18_37_upper : ℚ) : ℝ)

def cot_pi_19_37_lower : ℚ := -191310564183061 / 4503599627370496
def cot_pi_19_37_upper : ℚ := -3060969026928897 / 72057594037927936
axiom cot_pi_19_37_bounds :
  ((cot_pi_19_37_lower : ℚ) : ℝ) ≤ cotangentTermV 19 37 ∧
  cotangentTermV 19 37 ≤ ((cot_pi_19_37_upper : ℚ) : ℝ)

def cot_pi_20_37_lower : ℚ := -4613667947687997 / 36028797018963968
def cot_pi_20_37_upper : ℚ := -4613667947687967 / 36028797018963968
axiom cot_pi_20_37_bounds :
  ((cot_pi_20_37_lower : ℚ) : ℝ) ≤ cotangentTermV 20 37 ∧
  cotangentTermV 20 37 ≤ ((cot_pi_20_37_upper : ℚ) : ℝ)

def cot_pi_21_37_lower : ℚ := -7764799729323273 / 36028797018963968
def cot_pi_21_37_upper : ℚ := -7764799729323211 / 36028797018963968
axiom cot_pi_21_37_bounds :
  ((cot_pi_21_37_lower : ℚ) : ℝ) ≤ cotangentTermV 21 37 ∧
  cotangentTermV 21 37 ≤ ((cot_pi_21_37_upper : ℚ) : ℝ)

def cot_pi_22_37_lower : ℚ := -1379211883967391 / 4503599627370496
def cot_pi_22_37_upper : ℚ := -2758423767934765 / 9007199254740992
axiom cot_pi_22_37_bounds :
  ((cot_pi_22_37_lower : ℚ) : ℝ) ≤ cotangentTermV 22 37 ∧
  cotangentTermV 22 37 ≤ ((cot_pi_22_37_upper : ℚ) : ℝ)

def cot_pi_23_37_lower : ℚ := -7238780694655137 / 18014398509481984
def cot_pi_23_37_upper : ℚ := -7238780694655099 / 18014398509481984
axiom cot_pi_23_37_bounds :
  ((cot_pi_23_37_lower : ℚ) : ℝ) ≤ cotangentTermV 23 37 ∧
  cotangentTermV 23 37 ≤ ((cot_pi_23_37_upper : ℚ) : ℝ)

def cot_pi_24_37_lower : ℚ := -1135333577192731 / 2251799813685248
def cot_pi_24_37_upper : ℚ := -2270667154385453 / 4503599627370496
axiom cot_pi_24_37_bounds :
  ((cot_pi_24_37_lower : ℚ) : ℝ) ≤ cotangentTermV 24 37 ∧
  cotangentTermV 24 37 ≤ ((cot_pi_24_37_upper : ℚ) : ℝ)

def cot_pi_25_37_lower : ℚ := -5545952527570489 / 9007199254740992
def cot_pi_25_37_upper : ℚ := -5545952527570459 / 9007199254740992
axiom cot_pi_25_37_bounds :
  ((cot_pi_25_37_lower : ℚ) : ℝ) ≤ cotangentTermV 25 37 ∧
  cotangentTermV 25 37 ≤ ((cot_pi_25_37_upper : ℚ) : ℝ)

def cot_pi_26_37_lower : ℚ := -1665422456174627 / 2251799813685248
def cot_pi_26_37_upper : ℚ := -3330844912349237 / 4503599627370496
axiom cot_pi_26_37_bounds :
  ((cot_pi_26_37_lower : ℚ) : ℝ) ≤ cotangentTermV 26 37 ∧
  cotangentTermV 26 37 ≤ ((cot_pi_26_37_upper : ℚ) : ℝ)

def cot_pi_27_37_lower : ℚ := -7927332385256887 / 9007199254740992
def cot_pi_27_37_upper : ℚ := -7927332385256847 / 9007199254740992
axiom cot_pi_27_37_bounds :
  ((cot_pi_27_37_lower : ℚ) : ℝ) ≤ cotangentTermV 27 37 ∧
  cotangentTermV 27 37 ≤ ((cot_pi_27_37_upper : ℚ) : ℝ)

def cot_pi_28_37_lower : ℚ := -4698971746616777 / 4503599627370496
def cot_pi_28_37_upper : ℚ := -4698971746616761 / 4503599627370496
axiom cot_pi_28_37_bounds :
  ((cot_pi_28_37_lower : ℚ) : ℝ) ≤ cotangentTermV 28 37 ∧
  cotangentTermV 28 37 ≤ ((cot_pi_28_37_upper : ℚ) : ℝ)

def cot_pi_29_37_lower : ℚ := -5577602668353893 / 4503599627370496
def cot_pi_29_37_upper : ℚ := -5577602668353865 / 4503599627370496
axiom cot_pi_29_37_bounds :
  ((cot_pi_29_37_lower : ℚ) : ℝ) ≤ cotangentTermV 29 37 ∧
  cotangentTermV 29 37 ≤ ((cot_pi_29_37_upper : ℚ) : ℝ)

def cot_pi_30_37_lower : ℚ := -208227888110807 / 140737488355328
def cot_pi_30_37_upper : ℚ := -1665823104886447 / 1125899906842624
axiom cot_pi_30_37_bounds :
  ((cot_pi_30_37_lower : ℚ) : ℝ) ≤ cotangentTermV 30 37 ∧
  cotangentTermV 30 37 ≤ ((cot_pi_30_37_upper : ℚ) : ℝ)

def cot_pi_31_37_lower : ℚ := -4030907111705019 / 2251799813685248
def cot_pi_31_37_upper : ℚ := -4030907111704997 / 2251799813685248
axiom cot_pi_31_37_bounds :
  ((cot_pi_31_37_lower : ℚ) : ℝ) ≤ cotangentTermV 31 37 ∧
  cotangentTermV 31 37 ≤ ((cot_pi_31_37_upper : ℚ) : ℝ)

def cot_pi_32_37_lower : ℚ := -2490771943066845 / 1125899906842624
def cot_pi_32_37_upper : ℚ := -1245385971533417 / 562949953421312
axiom cot_pi_32_37_bounds :
  ((cot_pi_32_37_lower : ℚ) : ℝ) ≤ cotangentTermV 32 37 ∧
  cotangentTermV 32 37 ≤ ((cot_pi_32_37_upper : ℚ) : ℝ)

def cot_pi_33_37_lower : ℚ := -3186607078360631 / 1125899906842624
def cot_pi_33_37_upper : ℚ := -3186607078360607 / 1125899906842624
axiom cot_pi_33_37_bounds :
  ((cot_pi_33_37_lower : ℚ) : ℝ) ≤ cotangentTermV 33 37 ∧
  cotangentTermV 33 37 ≤ ((cot_pi_33_37_upper : ℚ) : ℝ)

def cot_pi_34_37_lower : ℚ := -8648137292680085 / 2251799813685248
def cot_pi_34_37_upper : ℚ := -8648137292680003 / 2251799813685248
axiom cot_pi_34_37_bounds :
  ((cot_pi_34_37_lower : ℚ) : ℝ) ≤ cotangentTermV 34 37 ∧
  cotangentTermV 34 37 ≤ ((cot_pi_34_37_upper : ℚ) : ℝ)

def cot_pi_35_37_lower : ℚ := -820783635494897 / 140737488355328
def cot_pi_35_37_upper : ℚ := -410391817747443 / 70368744177664
axiom cot_pi_35_37_bounds :
  ((cot_pi_35_37_lower : ℚ) : ℝ) ≤ cotangentTermV 35 37 ∧
  cotangentTermV 35 37 ≤ ((cot_pi_35_37_upper : ℚ) : ℝ)

def cot_pi_36_37_lower : ℚ := -826772898286895 / 70368744177664
def cot_pi_36_37_upper : ℚ := -3307091593147525 / 281474976710656
axiom cot_pi_36_37_bounds :
  ((cot_pi_36_37_lower : ℚ) : ℝ) ≤ cotangentTermV 36 37 ∧
  cotangentTermV 36 37 ≤ ((cot_pi_36_37_upper : ℚ) : ℝ)

def cot_pi_1_38_lower : ℚ := 6793795599972087 / 562949953421312
def cot_pi_1_38_upper : ℚ := 6793795599972097 / 562949953421312
axiom cot_pi_1_38_bounds :
  ((cot_pi_1_38_lower : ℚ) : ℝ) ≤ cotangentTermV 1 38 ∧
  cotangentTermV 1 38 ≤ ((cot_pi_1_38_upper : ℚ) : ℝ)

def cot_pi_2_38_lower : ℚ := 105424191201407 / 17592186044416
def cot_pi_2_38_upper : ℚ := 3373574118445029 / 562949953421312
axiom cot_pi_2_38_bounds :
  ((cot_pi_2_38_lower : ℚ) : ℝ) ≤ cotangentTermV 2 38 ∧
  cotangentTermV 2 38 ≤ ((cot_pi_2_38_upper : ℚ) : ℝ)

def cot_pi_3_38_lower : ℚ := 8892156370028527 / 2251799813685248
def cot_pi_3_38_upper : ℚ := 8892156370028537 / 2251799813685248
axiom cot_pi_3_38_bounds :
  ((cot_pi_3_38_lower : ℚ) : ℝ) ≤ cotangentTermV 3 38 ∧
  cotangentTermV 3 38 ≤ ((cot_pi_3_38_upper : ℚ) : ℝ)

def cot_pi_4_38_lower : ℚ := 6559268772007781 / 2251799813685248
def cot_pi_4_38_upper : ℚ := 6559268772007791 / 2251799813685248
axiom cot_pi_4_38_bounds :
  ((cot_pi_4_38_lower : ℚ) : ℝ) ≤ cotangentTermV 4 38 ∧
  cotangentTermV 4 38 ≤ ((cot_pi_4_38_upper : ℚ) : ℝ)

def cot_pi_5_38_lower : ℚ := 5133586493103047 / 2251799813685248
def cot_pi_5_38_upper : ℚ := 5133586493103055 / 2251799813685248
axiom cot_pi_5_38_bounds :
  ((cot_pi_5_38_lower : ℚ) : ℝ) ≤ cotangentTermV 5 38 ∧
  cotangentTermV 5 38 ≤ ((cot_pi_5_38_upper : ℚ) : ℝ)

def cot_pi_6_38_lower : ℚ := 4160961606430263 / 2251799813685248
def cot_pi_6_38_upper : ℚ := 1040240401607567 / 562949953421312
axiom cot_pi_6_38_bounds :
  ((cot_pi_6_38_lower : ℚ) : ℝ) ≤ cotangentTermV 6 38 ∧
  cotangentTermV 6 38 ≤ ((cot_pi_6_38_upper : ℚ) : ℝ)

def cot_pi_7_38_lower : ℚ := 6893272394394405 / 4503599627370496
def cot_pi_7_38_upper : ℚ := 6893272394394417 / 4503599627370496
axiom cot_pi_7_38_bounds :
  ((cot_pi_7_38_lower : ℚ) : ℝ) ≤ cotangentTermV 7 38 ∧
  cotangentTermV 7 38 ≤ ((cot_pi_7_38_upper : ℚ) : ℝ)

def cot_pi_8_38_lower : ℚ := 2893112459767835 / 2251799813685248
def cot_pi_8_38_upper : ℚ := 90409764367745 / 70368744177664
axiom cot_pi_8_38_bounds :
  ((cot_pi_8_38_lower : ℚ) : ℝ) ≤ cotangentTermV 8 38 ∧
  cotangentTermV 8 38 ≤ ((cot_pi_8_38_upper : ℚ) : ℝ)

def cot_pi_9_38_lower : ℚ := 4892213325694961 / 4503599627370496
def cot_pi_9_38_upper : ℚ := 4892213325694969 / 4503599627370496
axiom cot_pi_9_38_bounds :
  ((cot_pi_9_38_lower : ℚ) : ℝ) ≤ cotangentTermV 9 38 ∧
  cotangentTermV 9 38 ≤ ((cot_pi_9_38_upper : ℚ) : ℝ)

def cot_pi_10_38_lower : ℚ := 2072927758191169 / 2251799813685248
def cot_pi_10_38_upper : ℚ := 4145855516382345 / 4503599627370496
axiom cot_pi_10_38_bounds :
  ((cot_pi_10_38_lower : ℚ) : ℝ) ≤ cotangentTermV 10 38 ∧
  cotangentTermV 10 38 ≤ ((cot_pi_10_38_upper : ℚ) : ℝ)

def cot_pi_11_38_lower : ℚ := 7010584581727337 / 9007199254740992
def cot_pi_11_38_upper : ℚ := 7010584581727351 / 9007199254740992
axiom cot_pi_11_38_bounds :
  ((cot_pi_11_38_lower : ℚ) : ℝ) ≤ cotangentTermV 11 38 ∧
  cotangentTermV 11 38 ≤ ((cot_pi_11_38_upper : ℚ) : ℝ)

def cot_pi_12_38_lower : ℚ := 5884696975023141 / 9007199254740992
def cot_pi_12_38_upper : ℚ := 5884696975023151 / 9007199254740992
axiom cot_pi_12_38_bounds :
  ((cot_pi_12_38_lower : ℚ) : ℝ) ≤ cotangentTermV 12 38 ∧
  cotangentTermV 12 38 ≤ ((cot_pi_12_38_upper : ℚ) : ℝ)

def cot_pi_13_38_lower : ℚ := 4874452475674765 / 9007199254740992
def cot_pi_13_38_upper : ℚ := 4874452475674781 / 9007199254740992
axiom cot_pi_13_38_bounds :
  ((cot_pi_13_38_lower : ℚ) : ℝ) ≤ cotangentTermV 13 38 ∧
  cotangentTermV 13 38 ≤ ((cot_pi_13_38_upper : ℚ) : ℝ)

def cot_pi_14_38_lower : ℚ := 7901847813765667 / 18014398509481984
def cot_pi_14_38_upper : ℚ := 7901847813765687 / 18014398509481984
axiom cot_pi_14_38_bounds :
  ((cot_pi_14_38_lower : ℚ) : ℝ) ≤ cotangentTermV 14 38 ∧
  cotangentTermV 14 38 ≤ ((cot_pi_14_38_upper : ℚ) : ℝ)

def cot_pi_15_38_lower : ℚ := 6184350819776887 / 18014398509481984
def cot_pi_15_38_upper : ℚ := 6184350819776913 / 18014398509481984
axiom cot_pi_15_38_bounds :
  ((cot_pi_15_38_lower : ℚ) : ℝ) ≤ cotangentTermV 15 38 ∧
  cotangentTermV 15 38 ≤ ((cot_pi_15_38_upper : ℚ) : ℝ)

def cot_pi_16_38_lower : ℚ := 2280932628671999 / 9007199254740992
def cot_pi_16_38_upper : ℚ := 2280932628672007 / 9007199254740992
axiom cot_pi_16_38_bounds :
  ((cot_pi_16_38_lower : ℚ) : ℝ) ≤ cotangentTermV 16 38 ∧
  cotangentTermV 16 38 ≤ ((cot_pi_16_38_upper : ℚ) : ℝ)

def cot_pi_17_38_lower : ℚ := 1503035719058127 / 9007199254740992
def cot_pi_17_38_upper : ℚ := 751517859529069 / 4503599627370496
axiom cot_pi_17_38_bounds :
  ((cot_pi_17_38_lower : ℚ) : ℝ) ≤ cotangentTermV 17 38 ∧
  cotangentTermV 17 38 ≤ ((cot_pi_17_38_upper : ℚ) : ℝ)

def cot_pi_18_38_lower : ℚ := 2985431237250487 / 36028797018963968
def cot_pi_18_38_upper : ℚ := 1492715618625257 / 18014398509481984
axiom cot_pi_18_38_bounds :
  ((cot_pi_18_38_lower : ℚ) : ℝ) ≤ cotangentTermV 18 38 ∧
  cotangentTermV 18 38 ≤ ((cot_pi_18_38_upper : ℚ) : ℝ)

def cot_pi_19_38_lower : ℚ := -71766233 / 302231454903657293676544
def cot_pi_19_38_upper : ℚ := 485958067 / 604462909807314587353088
axiom cot_pi_19_38_bounds :
  ((cot_pi_19_38_lower : ℚ) : ℝ) ≤ cotangentTermV 19 38 ∧
  cotangentTermV 19 38 ≤ ((cot_pi_19_38_upper : ℚ) : ℝ)

def cot_pi_20_38_lower : ℚ := -2985431237250501 / 36028797018963968
def cot_pi_20_38_upper : ℚ := -1492715618625237 / 18014398509481984
axiom cot_pi_20_38_bounds :
  ((cot_pi_20_38_lower : ℚ) : ℝ) ≤ cotangentTermV 20 38 ∧
  cotangentTermV 20 38 ≤ ((cot_pi_20_38_upper : ℚ) : ℝ)

def cot_pi_21_38_lower : ℚ := -6012142876232531 / 36028797018963968
def cot_pi_21_38_upper : ℚ := -6012142876232471 / 36028797018963968
axiom cot_pi_21_38_bounds :
  ((cot_pi_21_38_lower : ℚ) : ℝ) ≤ cotangentTermV 21 38 ∧
  cotangentTermV 21 38 ≤ ((cot_pi_21_38_upper : ℚ) : ℝ)

def cot_pi_22_38_lower : ℚ := -1140466314336003 / 4503599627370496
def cot_pi_22_38_upper : ℚ := -1140466314335997 / 4503599627370496
axiom cot_pi_22_38_bounds :
  ((cot_pi_22_38_lower : ℚ) : ℝ) ≤ cotangentTermV 22 38 ∧
  cotangentTermV 22 38 ≤ ((cot_pi_22_38_upper : ℚ) : ℝ)

def cot_pi_23_38_lower : ℚ := -6184350819776907 / 18014398509481984
def cot_pi_23_38_upper : ℚ := -6184350819776871 / 18014398509481984
axiom cot_pi_23_38_bounds :
  ((cot_pi_23_38_lower : ℚ) : ℝ) ≤ cotangentTermV 23 38 ∧
  cotangentTermV 23 38 ≤ ((cot_pi_23_38_upper : ℚ) : ℝ)

def cot_pi_24_38_lower : ℚ := -7901847813765681 / 18014398509481984
def cot_pi_24_38_upper : ℚ := -7901847813765659 / 18014398509481984
axiom cot_pi_24_38_bounds :
  ((cot_pi_24_38_lower : ℚ) : ℝ) ≤ cotangentTermV 24 38 ∧
  cotangentTermV 24 38 ≤ ((cot_pi_24_38_upper : ℚ) : ℝ)

def cot_pi_25_38_lower : ℚ := -2437226237837389 / 4503599627370496
def cot_pi_25_38_upper : ℚ := -2437226237837375 / 4503599627370496
axiom cot_pi_25_38_bounds :
  ((cot_pi_25_38_lower : ℚ) : ℝ) ≤ cotangentTermV 25 38 ∧
  cotangentTermV 25 38 ≤ ((cot_pi_25_38_upper : ℚ) : ℝ)

def cot_pi_26_38_lower : ℚ := -367793560938947 / 562949953421312
def cot_pi_26_38_upper : ℚ := -367793560938945 / 562949953421312
axiom cot_pi_26_38_bounds :
  ((cot_pi_26_38_lower : ℚ) : ℝ) ≤ cotangentTermV 26 38 ∧
  cotangentTermV 26 38 ≤ ((cot_pi_26_38_upper : ℚ) : ℝ)

def cot_pi_27_38_lower : ℚ := -3505292290863677 / 4503599627370496
def cot_pi_27_38_upper : ℚ := -3505292290863659 / 4503599627370496
axiom cot_pi_27_38_bounds :
  ((cot_pi_27_38_lower : ℚ) : ℝ) ≤ cotangentTermV 27 38 ∧
  cotangentTermV 27 38 ≤ ((cot_pi_27_38_upper : ℚ) : ℝ)

def cot_pi_28_38_lower : ℚ := -2072927758191173 / 2251799813685248
def cot_pi_28_38_upper : ℚ := -1036463879095583 / 1125899906842624
axiom cot_pi_28_38_bounds :
  ((cot_pi_28_38_lower : ℚ) : ℝ) ≤ cotangentTermV 28 38 ∧
  cotangentTermV 28 38 ≤ ((cot_pi_28_38_upper : ℚ) : ℝ)

def cot_pi_29_38_lower : ℚ := -4892213325694973 / 4503599627370496
def cot_pi_29_38_upper : ℚ := -4892213325694949 / 4503599627370496
axiom cot_pi_29_38_bounds :
  ((cot_pi_29_38_lower : ℚ) : ℝ) ≤ cotangentTermV 29 38 ∧
  cotangentTermV 29 38 ≤ ((cot_pi_29_38_upper : ℚ) : ℝ)

def cot_pi_30_38_lower : ℚ := -2893112459767841 / 2251799813685248
def cot_pi_30_38_upper : ℚ := -1446556229883913 / 1125899906842624
axiom cot_pi_30_38_bounds :
  ((cot_pi_30_38_lower : ℚ) : ℝ) ≤ cotangentTermV 30 38 ∧
  cotangentTermV 30 38 ≤ ((cot_pi_30_38_upper : ℚ) : ℝ)

def cot_pi_31_38_lower : ℚ := -861659049299303 / 562949953421312
def cot_pi_31_38_upper : ℚ := -3446636197197193 / 2251799813685248
axiom cot_pi_31_38_bounds :
  ((cot_pi_31_38_lower : ℚ) : ℝ) ≤ cotangentTermV 31 38 ∧
  cotangentTermV 31 38 ≤ ((cot_pi_31_38_upper : ℚ) : ℝ)

def cot_pi_32_38_lower : ℚ := -4160961606430271 / 2251799813685248
def cot_pi_32_38_upper : ℚ := -4160961606430255 / 2251799813685248
axiom cot_pi_32_38_bounds :
  ((cot_pi_32_38_lower : ℚ) : ℝ) ≤ cotangentTermV 32 38 ∧
  cotangentTermV 32 38 ≤ ((cot_pi_32_38_upper : ℚ) : ℝ)

def cot_pi_33_38_lower : ℚ := -5133586493103055 / 2251799813685248
def cot_pi_33_38_upper : ℚ := -5133586493103035 / 2251799813685248
axiom cot_pi_33_38_bounds :
  ((cot_pi_33_38_lower : ℚ) : ℝ) ≤ cotangentTermV 33 38 ∧
  cotangentTermV 33 38 ≤ ((cot_pi_33_38_upper : ℚ) : ℝ)

def cot_pi_34_38_lower : ℚ := -6559268772007799 / 2251799813685248
def cot_pi_34_38_upper : ℚ := -6559268772007749 / 2251799813685248
axiom cot_pi_34_38_bounds :
  ((cot_pi_34_38_lower : ℚ) : ℝ) ≤ cotangentTermV 34 38 ∧
  cotangentTermV 34 38 ≤ ((cot_pi_34_38_upper : ℚ) : ℝ)

def cot_pi_35_38_lower : ℚ := -8892156370028559 / 2251799813685248
def cot_pi_35_38_upper : ℚ := -8892156370028475 / 2251799813685248
axiom cot_pi_35_38_bounds :
  ((cot_pi_35_38_lower : ℚ) : ℝ) ≤ cotangentTermV 35 38 ∧
  cotangentTermV 35 38 ≤ ((cot_pi_35_38_upper : ℚ) : ℝ)

def cot_pi_36_38_lower : ℚ := -6747148236890077 / 1125899906842624
def cot_pi_36_38_upper : ℚ := -6747148236890017 / 1125899906842624
axiom cot_pi_36_38_bounds :
  ((cot_pi_36_38_lower : ℚ) : ℝ) ≤ cotangentTermV 36 38 ∧
  cotangentTermV 36 38 ≤ ((cot_pi_36_38_upper : ℚ) : ℝ)

def cot_pi_37_38_lower : ℚ := -3396897799986057 / 281474976710656
def cot_pi_37_38_upper : ℚ := -212306112499123 / 17592186044416
axiom cot_pi_37_38_bounds :
  ((cot_pi_37_38_lower : ℚ) : ℝ) ≤ cotangentTermV 37 38 ∧
  cotangentTermV 37 38 ≤ ((cot_pi_37_38_upper : ℚ) : ℝ)

def cot_pi_1_39_lower : ℚ := 3486693226362649 / 281474976710656
def cot_pi_1_39_upper : ℚ := 1743346613181327 / 140737488355328
axiom cot_pi_1_39_bounds :
  ((cot_pi_1_39_lower : ℚ) : ℝ) ≤ cotangentTermV 1 39 ∧
  cotangentTermV 1 39 ≤ ((cot_pi_1_39_upper : ℚ) : ℝ)

def cot_pi_2_39_lower : ℚ := 6927940434179573 / 1125899906842624
def cot_pi_2_39_upper : ℚ := 6927940434179583 / 1125899906842624
axiom cot_pi_2_39_bounds :
  ((cot_pi_2_39_lower : ℚ) : ℝ) ≤ cotangentTermV 2 39 ∧
  cotangentTermV 2 39 ≤ ((cot_pi_2_39_upper : ℚ) : ℝ)

def cot_pi_3_39_lower : ℚ := 4567955486925621 / 1125899906842624
def cot_pi_3_39_upper : ℚ := 4567955486925627 / 1125899906842624
axiom cot_pi_3_39_bounds :
  ((cot_pi_3_39_lower : ℚ) : ℝ) ≤ cotangentTermV 3 39 ∧
  cotangentTermV 3 39 ≤ ((cot_pi_3_39_upper : ℚ) : ℝ)

def cot_pi_4_39_lower : ℚ := 6744963889812337 / 2251799813685248
def cot_pi_4_39_upper : ℚ := 6744963889812347 / 2251799813685248
axiom cot_pi_4_39_bounds :
  ((cot_pi_4_39_lower : ℚ) : ℝ) ≤ cotangentTermV 4 39 ∧
  cotangentTermV 4 39 ≤ ((cot_pi_4_39_upper : ℚ) : ℝ)

def cot_pi_5_39_lower : ℚ := 1321292099705077 / 562949953421312
def cot_pi_5_39_upper : ℚ := 1321292099705079 / 562949953421312
axiom cot_pi_5_39_bounds :
  ((cot_pi_5_39_lower : ℚ) : ℝ) ≤ cotangentTermV 5 39 ∧
  cotangentTermV 5 39 ≤ ((cot_pi_5_39_upper : ℚ) : ℝ)

def cot_pi_6_39_lower : ℚ := 4290446083899149 / 2251799813685248
def cot_pi_6_39_upper : ℚ := 2145223041949577 / 1125899906842624
axiom cot_pi_6_39_bounds :
  ((cot_pi_6_39_lower : ℚ) : ℝ) ≤ cotangentTermV 6 39 ∧
  cotangentTermV 6 39 ≤ ((cot_pi_6_39_upper : ℚ) : ℝ)

def cot_pi_7_39_lower : ℚ := 1780468258321387 / 1125899906842624
def cot_pi_7_39_upper : ℚ := 890234129160695 / 562949953421312
axiom cot_pi_7_39_bounds :
  ((cot_pi_7_39_lower : ℚ) : ℝ) ≤ cotangentTermV 7 39 ∧
  cotangentTermV 7 39 ≤ ((cot_pi_7_39_upper : ℚ) : ℝ)

def cot_pi_8_39_lower : ℚ := 2996601326140247 / 2251799813685248
def cot_pi_8_39_upper : ℚ := 749150331535063 / 562949953421312
axiom cot_pi_8_39_bounds :
  ((cot_pi_8_39_lower : ℚ) : ℝ) ≤ cotangentTermV 8 39 ∧
  cotangentTermV 8 39 ≤ ((cot_pi_8_39_upper : ℚ) : ℝ)

def cot_pi_9_39_lower : ℚ := 5083513109760297 / 4503599627370496
def cot_pi_9_39_upper : ℚ := 5083513109760305 / 4503599627370496
axiom cot_pi_9_39_bounds :
  ((cot_pi_9_39_lower : ℚ) : ℝ) ≤ cotangentTermV 9 39 ∧
  cotangentTermV 9 39 ≤ ((cot_pi_9_39_upper : ℚ) : ℝ)

def cot_pi_10_39_lower : ℚ := 2162883079381063 / 2251799813685248
def cot_pi_10_39_upper : ℚ := 4325766158762133 / 4503599627370496
axiom cot_pi_10_39_bounds :
  ((cot_pi_10_39_lower : ℚ) : ℝ) ≤ cotangentTermV 10 39 ∧
  cotangentTermV 10 39 ≤ ((cot_pi_10_39_upper : ℚ) : ℝ)

def cot_pi_11_39_lower : ℚ := 7354150562483121 / 9007199254740992
def cot_pi_11_39_upper : ℚ := 7354150562483139 / 9007199254740992
axiom cot_pi_11_39_bounds :
  ((cot_pi_11_39_lower : ℚ) : ℝ) ≤ cotangentTermV 11 39 ∧
  cotangentTermV 11 39 ≤ ((cot_pi_11_39_upper : ℚ) : ℝ)

def cot_pi_12_39_lower : ℚ := 3108610372237027 / 4503599627370496
def cot_pi_12_39_upper : ℚ := 388576296529629 / 562949953421312
axiom cot_pi_12_39_bounds :
  ((cot_pi_12_39_lower : ℚ) : ℝ) ≤ cotangentTermV 12 39 ∧
  cotangentTermV 12 39 ≤ ((cot_pi_12_39_upper : ℚ) : ℝ)

def cot_pi_13_39_lower : ℚ := 5200308914369303 / 9007199254740992
def cot_pi_13_39_upper : ℚ := 5200308914369321 / 9007199254740992
axiom cot_pi_13_39_bounds :
  ((cot_pi_13_39_lower : ℚ) : ℝ) ≤ cotangentTermV 13 39 ∧
  cotangentTermV 13 39 ≤ ((cot_pi_13_39_upper : ℚ) : ℝ)

def cot_pi_14_39_lower : ℚ := 4273969187084191 / 9007199254740992
def cot_pi_14_39_upper : ℚ := 4273969187084201 / 9007199254740992
axiom cot_pi_14_39_bounds :
  ((cot_pi_14_39_lower : ℚ) : ℝ) ≤ cotangentTermV 14 39 ∧
  cotangentTermV 14 39 ≤ ((cot_pi_14_39_upper : ℚ) : ℝ)

def cot_pi_15_39_lower : ℚ := 6831960191672633 / 18014398509481984
def cot_pi_15_39_upper : ℚ := 6831960191672659 / 18014398509481984
axiom cot_pi_15_39_bounds :
  ((cot_pi_15_39_lower : ℚ) : ℝ) ≤ cotangentTermV 15 39 ∧
  cotangentTermV 15 39 ≤ ((cot_pi_15_39_upper : ℚ) : ℝ)

def cot_pi_16_39_lower : ℚ := 5217934161362143 / 18014398509481984
def cot_pi_16_39_upper : ℚ := 5217934161362161 / 18014398509481984
axiom cot_pi_16_39_bounds :
  ((cot_pi_16_39_lower : ℚ) : ℝ) ≤ cotangentTermV 16 39 ∧
  cotangentTermV 16 39 ≤ ((cot_pi_16_39_upper : ℚ) : ℝ)

def cot_pi_17_39_lower : ℚ := 7355331574773631 / 36028797018963968
def cot_pi_17_39_upper : ℚ := 7355331574773675 / 36028797018963968
axiom cot_pi_17_39_bounds :
  ((cot_pi_17_39_lower : ℚ) : ℝ) ≤ cotangentTermV 17 39 ∧
  cotangentTermV 17 39 ≤ ((cot_pi_17_39_upper : ℚ) : ℝ)

def cot_pi_18_39_lower : ℚ := 2187343993577433 / 18014398509481984
def cot_pi_18_39_upper : ℚ := 4374687987154893 / 36028797018963968
axiom cot_pi_18_39_bounds :
  ((cot_pi_18_39_lower : ℚ) : ℝ) ≤ cotangentTermV 18 39 ∧
  cotangentTermV 18 39 ≤ ((cot_pi_18_39_upper : ℚ) : ℝ)

def cot_pi_19_39_lower : ℚ := 5807643541450469 / 144115188075855872
def cot_pi_19_39_upper : ℚ := 5807643541450623 / 144115188075855872
axiom cot_pi_19_39_bounds :
  ((cot_pi_19_39_lower : ℚ) : ℝ) ≤ cotangentTermV 19 39 ∧
  cotangentTermV 19 39 ≤ ((cot_pi_19_39_upper : ℚ) : ℝ)

def cot_pi_20_39_lower : ℚ := -5807643541450515 / 144115188075855872
def cot_pi_20_39_upper : ℚ := -5807643541450413 / 144115188075855872
axiom cot_pi_20_39_bounds :
  ((cot_pi_20_39_lower : ℚ) : ℝ) ≤ cotangentTermV 20 39 ∧
  cotangentTermV 20 39 ≤ ((cot_pi_20_39_upper : ℚ) : ℝ)

def cot_pi_21_39_lower : ℚ := -2187343993577443 / 18014398509481984
def cot_pi_21_39_upper : ℚ := -4374687987154831 / 36028797018963968
axiom cot_pi_21_39_bounds :
  ((cot_pi_21_39_lower : ℚ) : ℝ) ≤ cotangentTermV 21 39 ∧
  cotangentTermV 21 39 ≤ ((cot_pi_21_39_upper : ℚ) : ℝ)

def cot_pi_22_39_lower : ℚ := -3677665787386831 / 18014398509481984
def cot_pi_22_39_upper : ℚ := -3677665787386801 / 18014398509481984
axiom cot_pi_22_39_bounds :
  ((cot_pi_22_39_lower : ℚ) : ℝ) ≤ cotangentTermV 22 39 ∧
  cotangentTermV 22 39 ≤ ((cot_pi_22_39_upper : ℚ) : ℝ)

def cot_pi_23_39_lower : ℚ := -2608967080681081 / 9007199254740992
def cot_pi_23_39_upper : ℚ := -326120885085133 / 1125899906842624
axiom cot_pi_23_39_bounds :
  ((cot_pi_23_39_lower : ℚ) : ℝ) ≤ cotangentTermV 23 39 ∧
  cotangentTermV 23 39 ≤ ((cot_pi_23_39_upper : ℚ) : ℝ)

def cot_pi_24_39_lower : ℚ := -6831960191672649 / 18014398509481984
def cot_pi_24_39_upper : ℚ := -6831960191672629 / 18014398509481984
axiom cot_pi_24_39_bounds :
  ((cot_pi_24_39_lower : ℚ) : ℝ) ≤ cotangentTermV 24 39 ∧
  cotangentTermV 24 39 ≤ ((cot_pi_24_39_upper : ℚ) : ℝ)

def cot_pi_25_39_lower : ℚ := -4273969187084197 / 9007199254740992
def cot_pi_25_39_upper : ℚ := -1068492296771043 / 2251799813685248
axiom cot_pi_25_39_bounds :
  ((cot_pi_25_39_lower : ℚ) : ℝ) ≤ cotangentTermV 25 39 ∧
  cotangentTermV 25 39 ≤ ((cot_pi_25_39_upper : ℚ) : ℝ)

def cot_pi_26_39_lower : ℚ := -2600154457184657 / 4503599627370496
def cot_pi_26_39_upper : ℚ := -2600154457184643 / 4503599627370496
axiom cot_pi_26_39_bounds :
  ((cot_pi_26_39_lower : ℚ) : ℝ) ≤ cotangentTermV 26 39 ∧
  cotangentTermV 26 39 ≤ ((cot_pi_26_39_upper : ℚ) : ℝ)

def cot_pi_27_39_lower : ℚ := -3108610372237033 / 4503599627370496
def cot_pi_27_39_upper : ℚ := -3108610372237017 / 4503599627370496
axiom cot_pi_27_39_bounds :
  ((cot_pi_27_39_lower : ℚ) : ℝ) ≤ cotangentTermV 27 39 ∧
  cotangentTermV 27 39 ≤ ((cot_pi_27_39_upper : ℚ) : ℝ)

def cot_pi_28_39_lower : ℚ := -7354150562483133 / 9007199254740992
def cot_pi_28_39_upper : ℚ := -7354150562483107 / 9007199254740992
axiom cot_pi_28_39_bounds :
  ((cot_pi_28_39_lower : ℚ) : ℝ) ≤ cotangentTermV 28 39 ∧
  cotangentTermV 28 39 ≤ ((cot_pi_28_39_upper : ℚ) : ℝ)

def cot_pi_29_39_lower : ℚ := -540720769845267 / 562949953421312
def cot_pi_29_39_upper : ℚ := -4325766158762115 / 4503599627370496
axiom cot_pi_29_39_bounds :
  ((cot_pi_29_39_lower : ℚ) : ℝ) ≤ cotangentTermV 29 39 ∧
  cotangentTermV 29 39 ≤ ((cot_pi_29_39_upper : ℚ) : ℝ)

def cot_pi_30_39_lower : ℚ := -5083513109760309 / 4503599627370496
def cot_pi_30_39_upper : ℚ := -5083513109760283 / 4503599627370496
axiom cot_pi_30_39_bounds :
  ((cot_pi_30_39_lower : ℚ) : ℝ) ≤ cotangentTermV 30 39 ∧
  cotangentTermV 30 39 ≤ ((cot_pi_30_39_upper : ℚ) : ℝ)

def cot_pi_31_39_lower : ℚ := -2996601326140255 / 2251799813685248
def cot_pi_31_39_upper : ℚ := -187287582883765 / 140737488355328
axiom cot_pi_31_39_bounds :
  ((cot_pi_31_39_lower : ℚ) : ℝ) ≤ cotangentTermV 31 39 ∧
  cotangentTermV 31 39 ≤ ((cot_pi_31_39_upper : ℚ) : ℝ)

def cot_pi_32_39_lower : ℚ := -3560936516642781 / 2251799813685248
def cot_pi_32_39_upper : ℚ := -222558532290173 / 140737488355328
axiom cot_pi_32_39_bounds :
  ((cot_pi_32_39_lower : ℚ) : ℝ) ≤ cotangentTermV 32 39 ∧
  cotangentTermV 32 39 ≤ ((cot_pi_32_39_upper : ℚ) : ℝ)

def cot_pi_33_39_lower : ℚ := -4290446083899157 / 2251799813685248
def cot_pi_33_39_upper : ℚ := -4290446083899133 / 2251799813685248
axiom cot_pi_33_39_bounds :
  ((cot_pi_33_39_lower : ℚ) : ℝ) ≤ cotangentTermV 33 39 ∧
  cotangentTermV 33 39 ≤ ((cot_pi_33_39_upper : ℚ) : ℝ)

def cot_pi_34_39_lower : ℚ := -165161512463135 / 70368744177664
def cot_pi_34_39_upper : ℚ := -2642584199410143 / 1125899906842624
axiom cot_pi_34_39_bounds :
  ((cot_pi_34_39_lower : ℚ) : ℝ) ≤ cotangentTermV 34 39 ∧
  cotangentTermV 34 39 ≤ ((cot_pi_34_39_upper : ℚ) : ℝ)

def cot_pi_35_39_lower : ℚ := -3372481944906179 / 1125899906842624
def cot_pi_35_39_upper : ℚ := -3372481944906153 / 1125899906842624
axiom cot_pi_35_39_bounds :
  ((cot_pi_35_39_lower : ℚ) : ℝ) ≤ cotangentTermV 35 39 ∧
  cotangentTermV 35 39 ≤ ((cot_pi_35_39_upper : ℚ) : ℝ)

def cot_pi_36_39_lower : ℚ := -4567955486925631 / 1125899906842624
def cot_pi_36_39_upper : ℚ := -4567955486925601 / 1125899906842624
axiom cot_pi_36_39_bounds :
  ((cot_pi_36_39_lower : ℚ) : ℝ) ≤ cotangentTermV 36 39 ∧
  cotangentTermV 36 39 ≤ ((cot_pi_36_39_upper : ℚ) : ℝ)

def cot_pi_37_39_lower : ℚ := -3463970217089797 / 562949953421312
def cot_pi_37_39_upper : ℚ := -3463970217089749 / 562949953421312
axiom cot_pi_37_39_bounds :
  ((cot_pi_37_39_lower : ℚ) : ℝ) ≤ cotangentTermV 37 39 ∧
  cotangentTermV 37 39 ≤ ((cot_pi_37_39_upper : ℚ) : ℝ)

def cot_pi_38_39_lower : ℚ := -6973386452725339 / 562949953421312
def cot_pi_38_39_upper : ℚ := -6973386452725153 / 562949953421312
axiom cot_pi_38_39_bounds :
  ((cot_pi_38_39_lower : ℚ) : ℝ) ≤ cotangentTermV 38 39 ∧
  cotangentTermV 38 39 ≤ ((cot_pi_38_39_upper : ℚ) : ℝ)

def cot_pi_1_40_lower : ℚ := 7152957364391201 / 562949953421312
def cot_pi_1_40_upper : ℚ := 7152957364391209 / 562949953421312
axiom cot_pi_1_40_bounds :
  ((cot_pi_1_40_lower : ℚ) : ℝ) ≤ cotangentTermV 1 40 ∧
  cotangentTermV 1 40 ≤ ((cot_pi_1_40_upper : ℚ) : ℝ)

def cot_pi_2_40_lower : ℚ := 7108652242200103 / 1125899906842624
def cot_pi_2_40_upper : ℚ := 7108652242200111 / 1125899906842624
axiom cot_pi_2_40_bounds :
  ((cot_pi_2_40_lower : ℚ) : ℝ) ≤ cotangentTermV 2 40 ∧
  cotangentTermV 2 40 ≤ ((cot_pi_2_40_upper : ℚ) : ℝ)

def cot_pi_3_40_lower : ℚ := 2344855311558201 / 562949953421312
def cot_pi_3_40_upper : ℚ := 2344855311558203 / 562949953421312
axiom cot_pi_3_40_bounds :
  ((cot_pi_3_40_lower : ℚ) : ℝ) ≤ cotangentTermV 3 40 ∧
  cotangentTermV 3 40 ≤ ((cot_pi_3_40_upper : ℚ) : ℝ)

def cot_pi_4_40_lower : ℚ := 3465163607796693 / 1125899906842624
def cot_pi_4_40_upper : ℚ := 3465163607796697 / 1125899906842624
axiom cot_pi_4_40_bounds :
  ((cot_pi_4_40_lower : ℚ) : ℝ) ≤ cotangentTermV 4 40 ∧
  cotangentTermV 4 40 ≤ ((cot_pi_4_40_upper : ℚ) : ℝ)

def cot_pi_5_40_lower : ℚ := 5436325649948131 / 2251799813685248
def cot_pi_5_40_upper : ℚ := 5436325649948137 / 2251799813685248
axiom cot_pi_5_40_bounds :
  ((cot_pi_5_40_lower : ℚ) : ℝ) ≤ cotangentTermV 5 40 ∧
  cotangentTermV 5 40 ≤ ((cot_pi_5_40_upper : ℚ) : ℝ)

def cot_pi_6_40_lower : ℚ := 8838811941266413 / 4503599627370496
def cot_pi_6_40_upper : ℚ := 8838811941266421 / 4503599627370496
axiom cot_pi_6_40_bounds :
  ((cot_pi_6_40_lower : ℚ) : ℝ) ≤ cotangentTermV 6 40 ∧
  cotangentTermV 6 40 ≤ ((cot_pi_6_40_upper : ℚ) : ℝ)

def cot_pi_7_40_lower : ℚ := 918650831259641 / 562949953421312
def cot_pi_7_40_upper : ℚ := 459325415629821 / 281474976710656
axiom cot_pi_7_40_bounds :
  ((cot_pi_7_40_lower : ℚ) : ℝ) ≤ cotangentTermV 7 40 ∧
  cotangentTermV 7 40 ≤ ((cot_pi_7_40_upper : ℚ) : ℝ)

def cot_pi_8_40_lower : ℚ := 6198673104153461 / 4503599627370496
def cot_pi_8_40_upper : ℚ := 6198673104153469 / 4503599627370496
axiom cot_pi_8_40_bounds :
  ((cot_pi_8_40_lower : ℚ) : ℝ) ≤ cotangentTermV 8 40 ∧
  cotangentTermV 8 40 ≤ ((cot_pi_8_40_upper : ℚ) : ℝ)

def cot_pi_9_40_lower : ℚ := 659129708706417 / 562949953421312
def cot_pi_9_40_upper : ℚ := 2636518834825671 / 2251799813685248
axiom cot_pi_9_40_bounds :
  ((cot_pi_9_40_lower : ℚ) : ℝ) ≤ cotangentTermV 9 40 ∧
  cotangentTermV 9 40 ≤ ((cot_pi_9_40_upper : ℚ) : ℝ)

def cot_pi_10_40_lower : ℚ := 2251799813685247 / 2251799813685248
def cot_pi_10_40_upper : ℚ := 2251799813685249 / 2251799813685248
axiom cot_pi_10_40_bounds :
  ((cot_pi_10_40_lower : ℚ) : ℝ) ≤ cotangentTermV 10 40 ∧
  cotangentTermV 10 40 ≤ ((cot_pi_10_40_upper : ℚ) : ℝ)

def cot_pi_11_40_lower : ℚ := 1923218728398801 / 2251799813685248
def cot_pi_11_40_upper : ℚ := 3846437456797611 / 4503599627370496
axiom cot_pi_11_40_bounds :
  ((cot_pi_11_40_lower : ℚ) : ℝ) ≤ cotangentTermV 11 40 ∧
  cotangentTermV 11 40 ≤ ((cot_pi_11_40_upper : ℚ) : ℝ)

def cot_pi_12_40_lower : ℚ := 6544113316787519 / 9007199254740992
def cot_pi_12_40_upper : ℚ := 6544113316787527 / 9007199254740992
axiom cot_pi_12_40_bounds :
  ((cot_pi_12_40_lower : ℚ) : ℝ) ≤ cotangentTermV 12 40 ∧
  cotangentTermV 12 40 ≤ ((cot_pi_12_40_upper : ℚ) : ℝ)

def cot_pi_13_40_lower : ℚ := 5519618802238681 / 9007199254740992
def cot_pi_13_40_upper : ℚ := 5519618802238699 / 9007199254740992
axiom cot_pi_13_40_bounds :
  ((cot_pi_13_40_lower : ℚ) : ℝ) ≤ cotangentTermV 13 40 ∧
  cotangentTermV 13 40 ≤ ((cot_pi_13_40_upper : ℚ) : ℝ)

def cot_pi_14_40_lower : ℚ := 4589397248957785 / 9007199254740992
def cot_pi_14_40_upper : ℚ := 4589397248957791 / 9007199254740992
axiom cot_pi_14_40_bounds :
  ((cot_pi_14_40_lower : ℚ) : ℝ) ≤ cotangentTermV 14 40 ∧
  cotangentTermV 14 40 ≤ ((cot_pi_14_40_upper : ℚ) : ℝ)

def cot_pi_15_40_lower : ℚ := 3730904090310549 / 9007199254740992
def cot_pi_15_40_upper : ℚ := 1865452045155281 / 4503599627370496
axiom cot_pi_15_40_bounds :
  ((cot_pi_15_40_lower : ℚ) : ℝ) ≤ cotangentTermV 15 40 ∧
  cotangentTermV 15 40 ≤ ((cot_pi_15_40_upper : ℚ) : ℝ)

def cot_pi_16_40_lower : ℚ := 2926616445759701 / 9007199254740992
def cot_pi_16_40_upper : ℚ := 1463308222879853 / 4503599627370496
axiom cot_pi_16_40_bounds :
  ((cot_pi_16_40_lower : ℚ) : ℝ) ≤ cotangentTermV 16 40 ∧
  cotangentTermV 16 40 ≤ ((cot_pi_16_40_upper : ℚ) : ℝ)

def cot_pi_17_40_lower : ℚ := 4324874439731121 / 18014398509481984
def cot_pi_17_40_upper : ℚ := 4324874439731143 / 18014398509481984
axiom cot_pi_17_40_bounds :
  ((cot_pi_17_40_lower : ℚ) : ℝ) ≤ cotangentTermV 17 40 ∧
  cotangentTermV 17 40 ≤ ((cot_pi_17_40_upper : ℚ) : ℝ)

def cot_pi_18_40_lower : ℚ := 5706400851414925 / 36028797018963968
def cot_pi_18_40_upper : ℚ := 5706400851414937 / 36028797018963968
axiom cot_pi_18_40_bounds :
  ((cot_pi_18_40_lower : ℚ) : ℝ) ≤ cotangentTermV 18 40 ∧
  cotangentTermV 18 40 ≤ ((cot_pi_18_40_upper : ℚ) : ℝ)

def cot_pi_19_40_lower : ℚ := 5671055640460359 / 72057594037927936
def cot_pi_19_40_upper : ℚ := 5671055640460439 / 72057594037927936
axiom cot_pi_19_40_bounds :
  ((cot_pi_19_40_lower : ℚ) : ℝ) ≤ cotangentTermV 19 40 ∧
  cotangentTermV 19 40 ≤ ((cot_pi_19_40_upper : ℚ) : ℝ)

def cot_pi_20_40_lower : ℚ := -488112139 / 9671406556917033397649408
def cot_pi_20_40_upper : ℚ := 1671954449 / 9671406556917033397649408
axiom cot_pi_20_40_bounds :
  ((cot_pi_20_40_lower : ℚ) : ℝ) ≤ cotangentTermV 20 40 ∧
  cotangentTermV 20 40 ≤ ((cot_pi_20_40_upper : ℚ) : ℝ)

def cot_pi_21_40_lower : ℚ := -2835527820230197 / 36028797018963968
def cot_pi_21_40_upper : ℚ := -5538140273887 / 70368744177664
axiom cot_pi_21_40_bounds :
  ((cot_pi_21_40_lower : ℚ) : ℝ) ≤ cotangentTermV 21 40 ∧
  cotangentTermV 21 40 ≤ ((cot_pi_21_40_upper : ℚ) : ℝ)

def cot_pi_22_40_lower : ℚ := -5706400851414947 / 36028797018963968
def cot_pi_22_40_upper : ℚ := -5706400851414889 / 36028797018963968
axiom cot_pi_22_40_bounds :
  ((cot_pi_22_40_lower : ℚ) : ℝ) ≤ cotangentTermV 22 40 ∧
  cotangentTermV 22 40 ≤ ((cot_pi_22_40_upper : ℚ) : ℝ)

def cot_pi_23_40_lower : ℚ := -8649748879462271 / 36028797018963968
def cot_pi_23_40_upper : ℚ := -8649748879462211 / 36028797018963968
axiom cot_pi_23_40_bounds :
  ((cot_pi_23_40_lower : ℚ) : ℝ) ≤ cotangentTermV 23 40 ∧
  cotangentTermV 23 40 ≤ ((cot_pi_23_40_upper : ℚ) : ℝ)

def cot_pi_24_40_lower : ℚ := -2926616445759705 / 9007199254740992
def cot_pi_24_40_upper : ℚ := -731654111439925 / 2251799813685248
axiom cot_pi_24_40_bounds :
  ((cot_pi_24_40_lower : ℚ) : ℝ) ≤ cotangentTermV 24 40 ∧
  cotangentTermV 24 40 ≤ ((cot_pi_24_40_upper : ℚ) : ℝ)

def cot_pi_25_40_lower : ℚ := -7461808180621113 / 18014398509481984
def cot_pi_25_40_upper : ℚ := -7461808180621077 / 18014398509481984
axiom cot_pi_25_40_bounds :
  ((cot_pi_25_40_lower : ℚ) : ℝ) ≤ cotangentTermV 25 40 ∧
  cotangentTermV 25 40 ≤ ((cot_pi_25_40_upper : ℚ) : ℝ)

def cot_pi_26_40_lower : ℚ := -4589397248957795 / 9007199254740992
def cot_pi_26_40_upper : ℚ := -4589397248957769 / 9007199254740992
axiom cot_pi_26_40_bounds :
  ((cot_pi_26_40_lower : ℚ) : ℝ) ≤ cotangentTermV 26 40 ∧
  cotangentTermV 26 40 ≤ ((cot_pi_26_40_upper : ℚ) : ℝ)

def cot_pi_27_40_lower : ℚ := -689952350279837 / 1125899906842624
def cot_pi_27_40_upper : ℚ := -2759809401119333 / 4503599627370496
axiom cot_pi_27_40_bounds :
  ((cot_pi_27_40_lower : ℚ) : ℝ) ≤ cotangentTermV 27 40 ∧
  cotangentTermV 27 40 ≤ ((cot_pi_27_40_upper : ℚ) : ℝ)

def cot_pi_28_40_lower : ℚ := -3272056658393763 / 4503599627370496
def cot_pi_28_40_upper : ℚ := -1636028329196879 / 2251799813685248
axiom cot_pi_28_40_bounds :
  ((cot_pi_28_40_lower : ℚ) : ℝ) ≤ cotangentTermV 28 40 ∧
  cotangentTermV 28 40 ≤ ((cot_pi_28_40_upper : ℚ) : ℝ)

def cot_pi_29_40_lower : ℚ := -3846437456797611 / 4503599627370496
def cot_pi_29_40_upper : ℚ := -480804682099699 / 562949953421312
axiom cot_pi_29_40_bounds :
  ((cot_pi_29_40_lower : ℚ) : ℝ) ≤ cotangentTermV 29 40 ∧
  cotangentTermV 29 40 ≤ ((cot_pi_29_40_upper : ℚ) : ℝ)

def cot_pi_30_40_lower : ℚ := -2251799813685251 / 2251799813685248
def cot_pi_30_40_upper : ℚ := -9007199254740961 / 9007199254740992
axiom cot_pi_30_40_bounds :
  ((cot_pi_30_40_lower : ℚ) : ℝ) ≤ cotangentTermV 30 40 ∧
  cotangentTermV 30 40 ≤ ((cot_pi_30_40_upper : ℚ) : ℝ)

def cot_pi_31_40_lower : ℚ := -5273037669651345 / 4503599627370496
def cot_pi_31_40_upper : ℚ := -5273037669651319 / 4503599627370496
axiom cot_pi_31_40_bounds :
  ((cot_pi_31_40_lower : ℚ) : ℝ) ≤ cotangentTermV 31 40 ∧
  cotangentTermV 31 40 ≤ ((cot_pi_31_40_upper : ℚ) : ℝ)

def cot_pi_32_40_lower : ℚ := -6198673104153469 / 4503599627370496
def cot_pi_32_40_upper : ℚ := -6198673104153459 / 4503599627370496
axiom cot_pi_32_40_bounds :
  ((cot_pi_32_40_lower : ℚ) : ℝ) ≤ cotangentTermV 32 40 ∧
  cotangentTermV 32 40 ≤ ((cot_pi_32_40_upper : ℚ) : ℝ)

def cot_pi_33_40_lower : ℚ := -7349206650077143 / 4503599627370496
def cot_pi_33_40_upper : ℚ := -7349206650077103 / 4503599627370496
axiom cot_pi_33_40_bounds :
  ((cot_pi_33_40_lower : ℚ) : ℝ) ≤ cotangentTermV 33 40 ∧
  cotangentTermV 33 40 ≤ ((cot_pi_33_40_upper : ℚ) : ℝ)

def cot_pi_34_40_lower : ℚ := -4419405970633215 / 2251799813685248
def cot_pi_34_40_upper : ℚ := -2209702985316595 / 1125899906842624
axiom cot_pi_34_40_bounds :
  ((cot_pi_34_40_lower : ℚ) : ℝ) ≤ cotangentTermV 34 40 ∧
  cotangentTermV 34 40 ≤ ((cot_pi_34_40_upper : ℚ) : ℝ)

def cot_pi_35_40_lower : ℚ := -339770353121759 / 140737488355328
def cot_pi_35_40_upper : ℚ := -1359081412487027 / 562949953421312
axiom cot_pi_35_40_bounds :
  ((cot_pi_35_40_lower : ℚ) : ℝ) ≤ cotangentTermV 35 40 ∧
  cotangentTermV 35 40 ≤ ((cot_pi_35_40_upper : ℚ) : ℝ)

def cot_pi_36_40_lower : ℚ := -1732581803898349 / 562949953421312
def cot_pi_36_40_upper : ℚ := -1732581803898345 / 562949953421312
axiom cot_pi_36_40_bounds :
  ((cot_pi_36_40_lower : ℚ) : ℝ) ≤ cotangentTermV 36 40 ∧
  cotangentTermV 36 40 ≤ ((cot_pi_36_40_upper : ℚ) : ℝ)

def cot_pi_37_40_lower : ℚ := -4689710623116415 / 1125899906842624
def cot_pi_37_40_upper : ℚ := -4689710623116369 / 1125899906842624
axiom cot_pi_37_40_bounds :
  ((cot_pi_37_40_lower : ℚ) : ℝ) ≤ cotangentTermV 37 40 ∧
  cotangentTermV 37 40 ≤ ((cot_pi_37_40_upper : ℚ) : ℝ)

def cot_pi_38_40_lower : ℚ := -7108652242200131 / 1125899906842624
def cot_pi_38_40_upper : ℚ := -7108652242200031 / 1125899906842624
axiom cot_pi_38_40_bounds :
  ((cot_pi_38_40_lower : ℚ) : ℝ) ≤ cotangentTermV 38 40 ∧
  cotangentTermV 38 40 ≤ ((cot_pi_38_40_upper : ℚ) : ℝ)

def cot_pi_39_40_lower : ℚ := -447059835274453 / 35184372088832
def cot_pi_39_40_upper : ℚ := -447059835274441 / 35184372088832
axiom cot_pi_39_40_bounds :
  ((cot_pi_39_40_lower : ℚ) : ℝ) ≤ cotangentTermV 39 40 ∧
  cotangentTermV 39 40 ≤ ((cot_pi_39_40_upper : ℚ) : ℝ)

def cot_pi_1_41_lower : ℚ := 7332509796447873 / 562949953421312
def cot_pi_1_41_upper : ℚ := 7332509796447883 / 562949953421312
axiom cot_pi_1_41_bounds :
  ((cot_pi_1_41_lower : ℚ) : ℝ) ≤ cotangentTermV 1 41 ∧
  cotangentTermV 1 41 ≤ ((cot_pi_1_41_upper : ℚ) : ℝ)

def cot_pi_2_41_lower : ℚ := 7289289581425375 / 1125899906842624
def cot_pi_2_41_upper : ℚ := 7289289581425385 / 1125899906842624
axiom cot_pi_2_41_bounds :
  ((cot_pi_2_41_lower : ℚ) : ℝ) ≤ cotangentTermV 2 41 ∧
  cotangentTermV 2 41 ≤ ((cot_pi_2_41_upper : ℚ) : ℝ)

def cot_pi_3_41_lower : ℚ := 4811352663886863 / 1125899906842624
def cot_pi_3_41_upper : ℚ := 4811352663886869 / 1125899906842624
axiom cot_pi_3_41_bounds :
  ((cot_pi_3_41_lower : ℚ) : ℝ) ≤ cotangentTermV 3 41 ∧
  cotangentTermV 3 41 ≤ ((cot_pi_3_41_upper : ℚ) : ℝ)

def cot_pi_4_41_lower : ℚ := 3557691831438133 / 1125899906842624
def cot_pi_4_41_upper : ℚ := 1778845915719069 / 562949953421312
axiom cot_pi_4_41_bounds :
  ((cot_pi_4_41_lower : ℚ) : ℝ) ≤ cotangentTermV 4 41 ∧
  cotangentTermV 4 41 ≤ ((cot_pi_4_41_upper : ℚ) : ℝ)

def cot_pi_5_41_lower : ℚ := 5587090595674949 / 2251799813685248
def cot_pi_5_41_upper : ℚ := 5587090595674957 / 2251799813685248
axiom cot_pi_5_41_bounds :
  ((cot_pi_5_41_lower : ℚ) : ℝ) ≤ cotangentTermV 5 41 ∧
  cotangentTermV 5 41 ≤ ((cot_pi_5_41_upper : ℚ) : ℝ)

def cot_pi_6_41_lower : ℚ := 35530327605915 / 17592186044416
def cot_pi_6_41_upper : ℚ := 2273940966778563 / 1125899906842624
axiom cot_pi_6_41_bounds :
  ((cot_pi_6_41_lower : ℚ) : ℝ) ≤ cotangentTermV 6 41 ∧
  cotangentTermV 6 41 ≤ ((cot_pi_6_41_upper : ℚ) : ℝ)

def cot_pi_7_41_lower : ℚ := 7575373498900089 / 4503599627370496
def cot_pi_7_41_upper : ℚ := 7575373498900101 / 4503599627370496
axiom cot_pi_7_41_bounds :
  ((cot_pi_7_41_lower : ℚ) : ℝ) ≤ cotangentTermV 7 41 ∧
  cotangentTermV 7 41 ≤ ((cot_pi_7_41_upper : ℚ) : ℝ)

def cot_pi_8_41_lower : ℚ := 6402758365189477 / 4503599627370496
def cot_pi_8_41_upper : ℚ := 6402758365189487 / 4503599627370496
axiom cot_pi_8_41_bounds :
  ((cot_pi_8_41_lower : ℚ) : ℝ) ≤ cotangentTermV 8 41 ∧
  cotangentTermV 8 41 ≤ ((cot_pi_8_41_upper : ℚ) : ℝ)

def cot_pi_9_41_lower : ℚ := 1365233656081351 / 1125899906842624
def cot_pi_9_41_upper : ℚ := 2730467312162707 / 2251799813685248
axiom cot_pi_9_41_bounds :
  ((cot_pi_9_41_lower : ℚ) : ℝ) ≤ cotangentTermV 9 41 ∧
  cotangentTermV 9 41 ≤ ((cot_pi_9_41_upper : ℚ) : ℝ)

def cot_pi_10_41_lower : ℚ := 4679533735072377 / 4503599627370496
def cot_pi_10_41_upper : ℚ := 4679533735072385 / 4503599627370496
axiom cot_pi_10_41_bounds :
  ((cot_pi_10_41_lower : ℚ) : ℝ) ≤ cotangentTermV 10 41 ∧
  cotangentTermV 10 41 ≤ ((cot_pi_10_41_upper : ℚ) : ℝ)

def cot_pi_11_41_lower : ℚ := 4013592719988389 / 4503599627370496
def cot_pi_11_41_upper : ℚ := 2006796359994199 / 2251799813685248
axiom cot_pi_11_41_bounds :
  ((cot_pi_11_41_lower : ℚ) : ℝ) ≤ cotangentTermV 11 41 ∧
  cotangentTermV 11 41 ≤ ((cot_pi_11_41_upper : ℚ) : ℝ)

def cot_pi_12_41_lower : ℚ := 3432944810080181 / 4503599627370496
def cot_pi_12_41_upper : ℚ := 3432944810080187 / 4503599627370496
axiom cot_pi_12_41_bounds :
  ((cot_pi_12_41_lower : ℚ) : ℝ) ≤ cotangentTermV 12 41 ∧
  cotangentTermV 12 41 ≤ ((cot_pi_12_41_upper : ℚ) : ℝ)

def cot_pi_13_41_lower : ℚ := 5833003217483867 / 9007199254740992
def cot_pi_13_41_upper : ℚ := 5833003217483883 / 9007199254740992
axiom cot_pi_13_41_bounds :
  ((cot_pi_13_41_lower : ℚ) : ℝ) ≤ cotangentTermV 13 41 ∧
  cotangentTermV 13 41 ≤ ((cot_pi_13_41_upper : ℚ) : ℝ)

def cot_pi_14_41_lower : ℚ := 4897959691304125 / 9007199254740992
def cot_pi_14_41_upper : ℚ := 4897959691304137 / 9007199254740992
axiom cot_pi_14_41_bounds :
  ((cot_pi_14_41_lower : ℚ) : ℝ) ≤ cotangentTermV 14 41 ∧
  cotangentTermV 14 41 ≤ ((cot_pi_14_41_upper : ℚ) : ℝ)

def cot_pi_15_41_lower : ℚ := 2018930477281177 / 4503599627370496
def cot_pi_15_41_upper : ℚ := 63091577415037 / 140737488355328
axiom cot_pi_15_41_bounds :
  ((cot_pi_15_41_lower : ℚ) : ℝ) ≤ cotangentTermV 15 41 ∧
  cotangentTermV 15 41 ≤ ((cot_pi_15_41_upper : ℚ) : ℝ)

def cot_pi_16_41_lower : ℚ := 6469994304943355 / 18014398509481984
def cot_pi_16_41_upper : ℚ := 6469994304943373 / 18014398509481984
axiom cot_pi_16_41_bounds :
  ((cot_pi_16_41_lower : ℚ) : ℝ) ≤ cotangentTermV 16 41 ∧
  cotangentTermV 16 41 ≤ ((cot_pi_16_41_upper : ℚ) : ℝ)

def cot_pi_17_41_lower : ℚ := 2475221713336171 / 9007199254740992
def cot_pi_17_41_upper : ℚ := 2475221713336183 / 9007199254740992
axiom cot_pi_17_41_bounds :
  ((cot_pi_17_41_lower : ℚ) : ℝ) ≤ cotangentTermV 17 41 ∧
  cotangentTermV 17 41 ≤ ((cot_pi_17_41_upper : ℚ) : ℝ)

def cot_pi_18_41_lower : ℚ := 6987373425062973 / 36028797018963968
def cot_pi_18_41_upper : ℚ := 6987373425063003 / 36028797018963968
axiom cot_pi_18_41_bounds :
  ((cot_pi_18_41_lower : ℚ) : ℝ) ≤ cotangentTermV 18 41 ∧
  cotangentTermV 18 41 ≤ ((cot_pi_18_41_upper : ℚ) : ℝ)

def cot_pi_19_41_lower : ℚ := 2079674432795915 / 18014398509481984
def cot_pi_19_41_upper : ℚ := 2079674432795935 / 18014398509481984
axiom cot_pi_19_41_bounds :
  ((cot_pi_19_41_lower : ℚ) : ℝ) ≤ cotangentTermV 19 41 ∧
  cotangentTermV 19 41 ≤ ((cot_pi_19_41_upper : ℚ) : ℝ)

def cot_pi_20_41_lower : ℚ := 5524059328970883 / 144115188075855872
def cot_pi_20_41_upper : ℚ := 5524059328970985 / 144115188075855872
axiom cot_pi_20_41_bounds :
  ((cot_pi_20_41_lower : ℚ) : ℝ) ≤ cotangentTermV 20 41 ∧
  cotangentTermV 20 41 ≤ ((cot_pi_20_41_upper : ℚ) : ℝ)

def cot_pi_21_41_lower : ℚ := -5524059328970953 / 144115188075855872
def cot_pi_21_41_upper : ℚ := -5524059328970751 / 144115188075855872
axiom cot_pi_21_41_bounds :
  ((cot_pi_21_41_lower : ℚ) : ℝ) ≤ cotangentTermV 21 41 ∧
  cotangentTermV 21 41 ≤ ((cot_pi_21_41_upper : ℚ) : ℝ)

def cot_pi_22_41_lower : ℚ := -259959304099491 / 2251799813685248
def cot_pi_22_41_upper : ℚ := -2079674432795901 / 18014398509481984
axiom cot_pi_22_41_bounds :
  ((cot_pi_22_41_lower : ℚ) : ℝ) ≤ cotangentTermV 22 41 ∧
  cotangentTermV 22 41 ≤ ((cot_pi_22_41_upper : ℚ) : ℝ)

def cot_pi_23_41_lower : ℚ := -1746843356265749 / 9007199254740992
def cot_pi_23_41_upper : ℚ := -3493686712531469 / 18014398509481984
axiom cot_pi_23_41_bounds :
  ((cot_pi_23_41_lower : ℚ) : ℝ) ≤ cotangentTermV 23 41 ∧
  cotangentTermV 23 41 ≤ ((cot_pi_23_41_upper : ℚ) : ℝ)

def cot_pi_24_41_lower : ℚ := -4950443426672357 / 18014398509481984
def cot_pi_24_41_upper : ℚ := -4950443426672337 / 18014398509481984
axiom cot_pi_24_41_bounds :
  ((cot_pi_24_41_lower : ℚ) : ℝ) ≤ cotangentTermV 24 41 ∧
  cotangentTermV 24 41 ≤ ((cot_pi_24_41_upper : ℚ) : ℝ)

def cot_pi_25_41_lower : ℚ := -3234997152471685 / 9007199254740992
def cot_pi_25_41_upper : ℚ := -808749288117917 / 2251799813685248
axiom cot_pi_25_41_bounds :
  ((cot_pi_25_41_lower : ℚ) : ℝ) ≤ cotangentTermV 25 41 ∧
  cotangentTermV 25 41 ≤ ((cot_pi_25_41_upper : ℚ) : ℝ)

def cot_pi_26_41_lower : ℚ := -8075721909124725 / 18014398509481984
def cot_pi_26_41_upper : ℚ := -8075721909124687 / 18014398509481984
axiom cot_pi_26_41_bounds :
  ((cot_pi_26_41_lower : ℚ) : ℝ) ≤ cotangentTermV 26 41 ∧
  cotangentTermV 26 41 ≤ ((cot_pi_26_41_upper : ℚ) : ℝ)

def cot_pi_27_41_lower : ℚ := -1224489922826035 / 2251799813685248
def cot_pi_27_41_upper : ℚ := -2448979845652057 / 4503599627370496
axiom cot_pi_27_41_bounds :
  ((cot_pi_27_41_lower : ℚ) : ℝ) ≤ cotangentTermV 27 41 ∧
  cotangentTermV 27 41 ≤ ((cot_pi_27_41_upper : ℚ) : ℝ)

def cot_pi_28_41_lower : ℚ := -2916501608741941 / 4503599627370496
def cot_pi_28_41_upper : ℚ := -1458250804370965 / 2251799813685248
axiom cot_pi_28_41_bounds :
  ((cot_pi_28_41_lower : ℚ) : ℝ) ≤ cotangentTermV 28 41 ∧
  cotangentTermV 28 41 ≤ ((cot_pi_28_41_upper : ℚ) : ℝ)

def cot_pi_29_41_lower : ℚ := -6865889620160377 / 9007199254740992
def cot_pi_29_41_upper : ℚ := -6865889620160343 / 9007199254740992
axiom cot_pi_29_41_bounds :
  ((cot_pi_29_41_lower : ℚ) : ℝ) ≤ cotangentTermV 29 41 ∧
  cotangentTermV 29 41 ≤ ((cot_pi_29_41_upper : ℚ) : ℝ)

def cot_pi_30_41_lower : ℚ := -8027185439976793 / 9007199254740992
def cot_pi_30_41_upper : ℚ := -8027185439976755 / 9007199254740992
axiom cot_pi_30_41_bounds :
  ((cot_pi_30_41_lower : ℚ) : ℝ) ≤ cotangentTermV 30 41 ∧
  cotangentTermV 30 41 ≤ ((cot_pi_30_41_upper : ℚ) : ℝ)

def cot_pi_31_41_lower : ℚ := -4679533735072387 / 4503599627370496
def cot_pi_31_41_upper : ℚ := -4679533735072363 / 4503599627370496
axiom cot_pi_31_41_bounds :
  ((cot_pi_31_41_lower : ℚ) : ℝ) ≤ cotangentTermV 31 41 ∧
  cotangentTermV 31 41 ≤ ((cot_pi_31_41_upper : ℚ) : ℝ)

def cot_pi_32_41_lower : ℚ := -5460934624325413 / 4503599627370496
def cot_pi_32_41_upper : ℚ := -5460934624325393 / 4503599627370496
axiom cot_pi_32_41_bounds :
  ((cot_pi_32_41_lower : ℚ) : ℝ) ≤ cotangentTermV 32 41 ∧
  cotangentTermV 32 41 ≤ ((cot_pi_32_41_upper : ℚ) : ℝ)

def cot_pi_33_41_lower : ℚ := -6402758365189489 / 4503599627370496
def cot_pi_33_41_upper : ℚ := -6402758365189457 / 4503599627370496
axiom cot_pi_33_41_bounds :
  ((cot_pi_33_41_lower : ℚ) : ℝ) ≤ cotangentTermV 33 41 ∧
  cotangentTermV 33 41 ≤ ((cot_pi_33_41_upper : ℚ) : ℝ)

def cot_pi_34_41_lower : ℚ := -7575373498900109 / 4503599627370496
def cot_pi_34_41_upper : ℚ := -7575373498900067 / 4503599627370496
axiom cot_pi_34_41_bounds :
  ((cot_pi_34_41_lower : ℚ) : ℝ) ≤ cotangentTermV 34 41 ∧
  cotangentTermV 34 41 ≤ ((cot_pi_34_41_upper : ℚ) : ℝ)

def cot_pi_35_41_lower : ℚ := -1136970483389283 / 562949953421312
def cot_pi_35_41_upper : ℚ := -2273940966778553 / 1125899906842624
axiom cot_pi_35_41_bounds :
  ((cot_pi_35_41_lower : ℚ) : ℝ) ≤ cotangentTermV 35 41 ∧
  cotangentTermV 35 41 ≤ ((cot_pi_35_41_upper : ℚ) : ℝ)

def cot_pi_36_41_lower : ℚ := -5587090595674957 / 2251799813685248
def cot_pi_36_41_upper : ℚ := -5587090595674931 / 2251799813685248
axiom cot_pi_36_41_bounds :
  ((cot_pi_36_41_lower : ℚ) : ℝ) ≤ cotangentTermV 36 41 ∧
  cotangentTermV 36 41 ≤ ((cot_pi_36_41_upper : ℚ) : ℝ)

def cot_pi_37_41_lower : ℚ := -7115383662876277 / 2251799813685248
def cot_pi_37_41_upper : ℚ := -7115383662876221 / 2251799813685248
axiom cot_pi_37_41_bounds :
  ((cot_pi_37_41_lower : ℚ) : ℝ) ≤ cotangentTermV 37 41 ∧
  cotangentTermV 37 41 ≤ ((cot_pi_37_41_upper : ℚ) : ℝ)

def cot_pi_38_41_lower : ℚ := -1202838165971719 / 281474976710656
def cot_pi_38_41_upper : ℚ := -1202838165971707 / 281474976710656
axiom cot_pi_38_41_bounds :
  ((cot_pi_38_41_lower : ℚ) : ℝ) ≤ cotangentTermV 38 41 ∧
  cotangentTermV 38 41 ≤ ((cot_pi_38_41_upper : ℚ) : ℝ)

def cot_pi_39_41_lower : ℚ := -28473787427443 / 4398046511104
def cot_pi_39_41_upper : ℚ := -911161197678163 / 140737488355328
axiom cot_pi_39_41_bounds :
  ((cot_pi_39_41_lower : ℚ) : ℝ) ≤ cotangentTermV 39 41 ∧
  cotangentTermV 39 41 ≤ ((cot_pi_39_41_upper : ℚ) : ℝ)

def cot_pi_40_41_lower : ℚ := -7332509796447917 / 562949953421312
def cot_pi_40_41_upper : ℚ := -7332509796447783 / 562949953421312
axiom cot_pi_40_41_bounds :
  ((cot_pi_40_41_lower : ℚ) : ℝ) ≤ cotangentTermV 40 41 ∧
  cotangentTermV 40 41 ≤ ((cot_pi_40_41_upper : ℚ) : ℝ)

def cot_pi_1_42_lower : ℚ := 3756022535456065 / 281474976710656
def cot_pi_1_42_upper : ℚ := 1878011267728035 / 140737488355328
axiom cot_pi_1_42_bounds :
  ((cot_pi_1_42_lower : ℚ) : ℝ) ≤ cotangentTermV 1 42 ∧
  cotangentTermV 1 42 ≤ ((cot_pi_1_42_upper : ℚ) : ℝ)

def cot_pi_2_42_lower : ℚ := 7469857804053975 / 1125899906842624
def cot_pi_2_42_upper : ℚ := 7469857804053985 / 1125899906842624
axiom cot_pi_2_42_bounds :
  ((cot_pi_2_42_lower : ℚ) : ℝ) ≤ cotangentTermV 2 42 ∧
  cotangentTermV 2 42 ≤ ((cot_pi_2_42_upper : ℚ) : ℝ)

def cot_pi_3_42_lower : ℚ := 4932889800468321 / 1125899906842624
def cot_pi_3_42_upper : ℚ := 4932889800468327 / 1125899906842624
axiom cot_pi_3_42_bounds :
  ((cot_pi_3_42_lower : ℚ) : ℝ) ≤ cotangentTermV 3 42 ∧
  cotangentTermV 3 42 ≤ ((cot_pi_3_42_upper : ℚ) : ℝ)

def cot_pi_4_42_lower : ℚ := 912519462267461 / 281474976710656
def cot_pi_4_42_upper : ℚ := 3650077849069849 / 1125899906842624
axiom cot_pi_4_42_bounds :
  ((cot_pi_4_42_lower : ℚ) : ℝ) ≤ cotangentTermV 4 42 ∧
  cotangentTermV 4 42 ≤ ((cot_pi_4_42_upper : ℚ) : ℝ)

def cot_pi_5_42_lower : ℚ := 5737492353608003 / 2251799813685248
def cot_pi_5_42_upper : ℚ := 5737492353608011 / 2251799813685248
axiom cot_pi_5_42_bounds :
  ((cot_pi_5_42_lower : ℚ) : ℝ) ≤ cotangentTermV 5 42 ∧
  cotangentTermV 5 42 ≤ ((cot_pi_5_42_upper : ℚ) : ℝ)

def cot_pi_6_42_lower : ℚ := 4675910493915015 / 2251799813685248
def cot_pi_6_42_upper : ℚ := 4675910493915021 / 2251799813685248
axiom cot_pi_6_42_bounds :
  ((cot_pi_6_42_lower : ℚ) : ℝ) ≤ cotangentTermV 6 42 ∧
  cotangentTermV 6 42 ≤ ((cot_pi_6_42_upper : ℚ) : ℝ)

def cot_pi_7_42_lower : ℚ := 1950115842888489 / 1125899906842624
def cot_pi_7_42_upper : ℚ := 487528960722123 / 281474976710656
axiom cot_pi_7_42_bounds :
  ((cot_pi_7_42_lower : ℚ) : ℝ) ≤ cotangentTermV 7 42 ∧
  cotangentTermV 7 42 ≤ ((cot_pi_7_42_upper : ℚ) : ℝ)

def cot_pi_8_42_lower : ℚ := 6605567444055593 / 4503599627370496
def cot_pi_8_42_upper : ℚ := 6605567444055603 / 4503599627370496
axiom cot_pi_8_42_bounds :
  ((cot_pi_8_42_lower : ℚ) : ℝ) ≤ cotangentTermV 8 42 ∧
  cotangentTermV 8 42 ≤ ((cot_pi_8_42_upper : ℚ) : ℝ)

def cot_pi_9_42_lower : ℚ := 5647335309435131 / 4503599627370496
def cot_pi_9_42_upper : ℚ := 5647335309435137 / 4503599627370496
axiom cot_pi_9_42_bounds :
  ((cot_pi_9_42_lower : ℚ) : ℝ) ≤ cotangentTermV 9 42 ∧
  cotangentTermV 9 42 ≤ ((cot_pi_9_42_upper : ℚ) : ℝ)

def cot_pi_10_42_lower : ℚ := 4853726051466565 / 4503599627370496
def cot_pi_10_42_upper : ℚ := 4853726051466573 / 4503599627370496
axiom cot_pi_10_42_bounds :
  ((cot_pi_10_42_lower : ℚ) : ℝ) ≤ cotangentTermV 10 42 ∧
  cotangentTermV 10 42 ≤ ((cot_pi_10_42_upper : ℚ) : ℝ)

def cot_pi_11_42_lower : ℚ := 8357459563472175 / 9007199254740992
def cot_pi_11_42_upper : ℚ := 8357459563472193 / 9007199254740992
axiom cot_pi_11_42_bounds :
  ((cot_pi_11_42_lower : ℚ) : ℝ) ≤ cotangentTermV 11 42 ∧
  cotangentTermV 11 42 ≤ ((cot_pi_11_42_upper : ℚ) : ℝ)

def cot_pi_12_42_lower : ℚ := 3591500857008679 / 4503599627370496
def cot_pi_12_42_upper : ℚ := 3591500857008683 / 4503599627370496
axiom cot_pi_12_42_bounds :
  ((cot_pi_12_42_lower : ℚ) : ℝ) ≤ cotangentTermV 12 42 ∧
  cotangentTermV 12 42 ≤ ((cot_pi_12_42_upper : ℚ) : ℝ)

def cot_pi_13_42_lower : ℚ := 6141004470979691 / 9007199254740992
def cot_pi_13_42_upper : ℚ := 6141004470979707 / 9007199254740992
axiom cot_pi_13_42_bounds :
  ((cot_pi_13_42_lower : ℚ) : ℝ) ≤ cotangentTermV 13 42 ∧
  cotangentTermV 13 42 ≤ ((cot_pi_13_42_upper : ℚ) : ℝ)

def cot_pi_14_42_lower : ℚ := 5200308914369303 / 9007199254740992
def cot_pi_14_42_upper : ℚ := 5200308914369315 / 9007199254740992
axiom cot_pi_14_42_bounds :
  ((cot_pi_14_42_lower : ℚ) : ℝ) ≤ cotangentTermV 14 42 ∧
  cotangentTermV 14 42 ≤ ((cot_pi_14_42_upper : ℚ) : ℝ)

def cot_pi_15_42_lower : ℚ := 8675277095250691 / 18014398509481984
def cot_pi_15_42_upper : ℚ := 8675277095250719 / 18014398509481984
axiom cot_pi_15_42_bounds :
  ((cot_pi_15_42_lower : ℚ) : ℝ) ≤ cotangentTermV 15 42 ∧
  cotangentTermV 15 42 ≤ ((cot_pi_15_42_upper : ℚ) : ℝ)

def cot_pi_16_42_lower : ℚ := 3535065208565745 / 9007199254740992
def cot_pi_16_42_upper : ℚ := 1767532604282877 / 4503599627370496
axiom cot_pi_16_42_bounds :
  ((cot_pi_16_42_lower : ℚ) : ℝ) ≤ cotangentTermV 16 42 ∧
  cotangentTermV 16 42 ≤ ((cot_pi_16_42_upper : ℚ) : ℝ)

def cot_pi_17_42_lower : ℚ := 2778353016336383 / 9007199254740992
def cot_pi_17_42_upper : ℚ := 2778353016336395 / 9007199254740992
axiom cot_pi_17_42_bounds :
  ((cot_pi_17_42_lower : ℚ) : ℝ) ≤ cotangentTermV 17 42 ∧
  cotangentTermV 17 42 ≤ ((cot_pi_17_42_upper : ℚ) : ℝ)

def cot_pi_18_42_lower : ℚ := 513958613106613 / 2251799813685248
def cot_pi_18_42_upper : ℚ := 4111668904852911 / 18014398509481984
axiom cot_pi_18_42_bounds :
  ((cot_pi_18_42_lower : ℚ) : ℝ) ≤ cotangentTermV 18 42 ∧
  cotangentTermV 18 42 ≤ ((cot_pi_18_42_upper : ℚ) : ℝ)

def cot_pi_19_42_lower : ℚ := 678808423657145 / 4503599627370496
def cot_pi_19_42_upper : ℚ := 2715233694628601 / 18014398509481984
axiom cot_pi_19_42_bounds :
  ((cot_pi_19_42_lower : ℚ) : ℝ) ≤ cotangentTermV 19 42 ∧
  cotangentTermV 19 42 ≤ ((cot_pi_19_42_upper : ℚ) : ℝ)

def cot_pi_20_42_lower : ℚ := 5399970157843809 / 72057594037927936
def cot_pi_20_42_upper : ℚ := 5399970157843863 / 72057594037927936
axiom cot_pi_20_42_bounds :
  ((cot_pi_20_42_lower : ℚ) : ℝ) ≤ cotangentTermV 20 42 ∧
  cotangentTermV 20 42 ≤ ((cot_pi_20_42_upper : ℚ) : ℝ)

def cot_pi_21_42_lower : ℚ := -50405767 / 302231454903657293676544
def cot_pi_21_42_upper : ℚ := 711672593 / 604462909807314587353088
axiom cot_pi_21_42_bounds :
  ((cot_pi_21_42_lower : ℚ) : ℝ) ≤ cotangentTermV 21 42 ∧
  cotangentTermV 21 42 ≤ ((cot_pi_21_42_upper : ℚ) : ℝ)

def cot_pi_22_42_lower : ℚ := -5399970157843847 / 72057594037927936
def cot_pi_22_42_upper : ℚ := -5399970157843743 / 72057594037927936
axiom cot_pi_22_42_bounds :
  ((cot_pi_22_42_lower : ℚ) : ℝ) ≤ cotangentTermV 22 42 ∧
  cotangentTermV 22 42 ≤ ((cot_pi_22_42_upper : ℚ) : ℝ)

def cot_pi_23_42_lower : ℚ := -1357616847314297 / 9007199254740992
def cot_pi_23_42_upper : ℚ := -1357616847314283 / 9007199254740992
axiom cot_pi_23_42_bounds :
  ((cot_pi_23_42_lower : ℚ) : ℝ) ≤ cotangentTermV 23 42 ∧
  cotangentTermV 23 42 ≤ ((cot_pi_23_42_upper : ℚ) : ℝ)

def cot_pi_24_42_lower : ℚ := -8223337809705817 / 36028797018963968
def cot_pi_24_42_upper : ℚ := -8223337809705801 / 36028797018963968
axiom cot_pi_24_42_bounds :
  ((cot_pi_24_42_lower : ℚ) : ℝ) ≤ cotangentTermV 24 42 ∧
  cotangentTermV 24 42 ≤ ((cot_pi_24_42_upper : ℚ) : ℝ)

def cot_pi_25_42_lower : ℚ := -2778353016336389 / 9007199254740992
def cot_pi_25_42_upper : ℚ := -2778353016336373 / 9007199254740992
axiom cot_pi_25_42_bounds :
  ((cot_pi_25_42_lower : ℚ) : ℝ) ≤ cotangentTermV 25 42 ∧
  cotangentTermV 25 42 ≤ ((cot_pi_25_42_upper : ℚ) : ℝ)

def cot_pi_26_42_lower : ℚ := -3535065208565753 / 9007199254740992
def cot_pi_26_42_upper : ℚ := -3535065208565735 / 9007199254740992
axiom cot_pi_26_42_bounds :
  ((cot_pi_26_42_lower : ℚ) : ℝ) ≤ cotangentTermV 26 42 ∧
  cotangentTermV 26 42 ≤ ((cot_pi_26_42_upper : ℚ) : ℝ)

def cot_pi_27_42_lower : ℚ := -8675277095250711 / 18014398509481984
def cot_pi_27_42_upper : ℚ := -8675277095250663 / 18014398509481984
axiom cot_pi_27_42_bounds :
  ((cot_pi_27_42_lower : ℚ) : ℝ) ≤ cotangentTermV 27 42 ∧
  cotangentTermV 27 42 ≤ ((cot_pi_27_42_upper : ℚ) : ℝ)

def cot_pi_28_42_lower : ℚ := -2600154457184657 / 4503599627370496
def cot_pi_28_42_upper : ℚ := -325019307148081 / 562949953421312
axiom cot_pi_28_42_bounds :
  ((cot_pi_28_42_lower : ℚ) : ℝ) ≤ cotangentTermV 28 42 ∧
  cotangentTermV 28 42 ≤ ((cot_pi_28_42_upper : ℚ) : ℝ)

def cot_pi_29_42_lower : ℚ := -3070502235489853 / 4503599627370496
def cot_pi_29_42_upper : ℚ := -3070502235489837 / 4503599627370496
axiom cot_pi_29_42_bounds :
  ((cot_pi_29_42_lower : ℚ) : ℝ) ≤ cotangentTermV 29 42 ∧
  cotangentTermV 29 42 ≤ ((cot_pi_29_42_upper : ℚ) : ℝ)

def cot_pi_30_42_lower : ℚ := -3591500857008685 / 4503599627370496
def cot_pi_30_42_upper : ℚ := -897875214252167 / 1125899906842624
axiom cot_pi_30_42_bounds :
  ((cot_pi_30_42_lower : ℚ) : ℝ) ≤ cotangentTermV 30 42 ∧
  cotangentTermV 30 42 ≤ ((cot_pi_30_42_upper : ℚ) : ℝ)

def cot_pi_31_42_lower : ℚ := -2089364890868049 / 2251799813685248
def cot_pi_31_42_upper : ℚ := -2089364890868039 / 2251799813685248
axiom cot_pi_31_42_bounds :
  ((cot_pi_31_42_lower : ℚ) : ℝ) ≤ cotangentTermV 31 42 ∧
  cotangentTermV 31 42 ≤ ((cot_pi_31_42_upper : ℚ) : ℝ)

def cot_pi_32_42_lower : ℚ := -2426863025733287 / 2251799813685248
def cot_pi_32_42_upper : ℚ := -1213431512866639 / 1125899906842624
axiom cot_pi_32_42_bounds :
  ((cot_pi_32_42_lower : ℚ) : ℝ) ≤ cotangentTermV 32 42 ∧
  cotangentTermV 32 42 ≤ ((cot_pi_32_42_upper : ℚ) : ℝ)

def cot_pi_33_42_lower : ℚ := -2823667654717571 / 2251799813685248
def cot_pi_33_42_upper : ℚ := -2823667654717557 / 2251799813685248
axiom cot_pi_33_42_bounds :
  ((cot_pi_33_42_lower : ℚ) : ℝ) ≤ cotangentTermV 33 42 ∧
  cotangentTermV 33 42 ≤ ((cot_pi_33_42_upper : ℚ) : ℝ)

def cot_pi_34_42_lower : ℚ := -1651391861013901 / 1125899906842624
def cot_pi_34_42_upper : ℚ := -3302783722027785 / 2251799813685248
axiom cot_pi_34_42_bounds :
  ((cot_pi_34_42_lower : ℚ) : ℝ) ≤ cotangentTermV 34 42 ∧
  cotangentTermV 34 42 ≤ ((cot_pi_34_42_upper : ℚ) : ℝ)

def cot_pi_35_42_lower : ℚ := -7800463371553975 / 4503599627370496
def cot_pi_35_42_upper : ℚ := -7800463371553933 / 4503599627370496
axiom cot_pi_35_42_bounds :
  ((cot_pi_35_42_lower : ℚ) : ℝ) ≤ cotangentTermV 35 42 ∧
  cotangentTermV 35 42 ≤ ((cot_pi_35_42_upper : ℚ) : ℝ)

def cot_pi_36_42_lower : ℚ := -2337955246957511 / 1125899906842624
def cot_pi_36_42_upper : ℚ := -1168977623478753 / 562949953421312
axiom cot_pi_36_42_bounds :
  ((cot_pi_36_42_lower : ℚ) : ℝ) ≤ cotangentTermV 36 42 ∧
  cotangentTermV 36 42 ≤ ((cot_pi_36_42_upper : ℚ) : ℝ)

def cot_pi_37_42_lower : ℚ := -1434373088402003 / 562949953421312
def cot_pi_37_42_upper : ℚ := -2868746176803987 / 1125899906842624
axiom cot_pi_37_42_bounds :
  ((cot_pi_37_42_lower : ℚ) : ℝ) ≤ cotangentTermV 37 42 ∧
  cotangentTermV 37 42 ≤ ((cot_pi_37_42_upper : ℚ) : ℝ)

def cot_pi_38_42_lower : ℚ := -7300155698139711 / 2251799813685248
def cot_pi_38_42_upper : ℚ := -7300155698139653 / 2251799813685248
axiom cot_pi_38_42_bounds :
  ((cot_pi_38_42_lower : ℚ) : ℝ) ≤ cotangentTermV 38 42 ∧
  cotangentTermV 38 42 ≤ ((cot_pi_38_42_upper : ℚ) : ℝ)

def cot_pi_39_42_lower : ℚ := -4932889800468335 / 1125899906842624
def cot_pi_39_42_upper : ℚ := -4932889800468287 / 1125899906842624
axiom cot_pi_39_42_bounds :
  ((cot_pi_39_42_lower : ℚ) : ℝ) ≤ cotangentTermV 39 42 ∧
  cotangentTermV 39 42 ≤ ((cot_pi_39_42_upper : ℚ) : ℝ)

def cot_pi_40_42_lower : ℚ := -7469857804054003 / 1125899906842624
def cot_pi_40_42_upper : ℚ := -7469857804053929 / 1125899906842624
axiom cot_pi_40_42_bounds :
  ((cot_pi_40_42_lower : ℚ) : ℝ) ≤ cotangentTermV 40 42 ∧
  cotangentTermV 40 42 ≤ ((cot_pi_40_42_upper : ℚ) : ℝ)

def cot_pi_41_42_lower : ℚ := -7512045070912231 / 562949953421312
def cot_pi_41_42_upper : ℚ := -7512045070911953 / 562949953421312
axiom cot_pi_41_42_bounds :
  ((cot_pi_41_42_lower : ℚ) : ℝ) ≤ cotangentTermV 41 42 ∧
  cotangentTermV 41 42 ≤ ((cot_pi_41_42_upper : ℚ) : ℝ)

def cot_pi_1_43_lower : ℚ := 240361387081023 / 17592186044416
def cot_pi_1_43_upper : ℚ := 3845782193296373 / 281474976710656
axiom cot_pi_1_43_bounds :
  ((cot_pi_1_43_lower : ℚ) : ℝ) ≤ cotangentTermV 1 43 ∧
  cotangentTermV 1 43 ≤ ((cot_pi_1_43_upper : ℚ) : ℝ)

def cot_pi_2_43_lower : ℚ := 7650361760686167 / 1125899906842624
def cot_pi_2_43_upper : ℚ := 7650361760686177 / 1125899906842624
axiom cot_pi_2_43_bounds :
  ((cot_pi_2_43_lower : ℚ) : ℝ) ≤ cotangentTermV 2 43 ∧
  cotangentTermV 2 43 ≤ ((cot_pi_2_43_upper : ℚ) : ℝ)

def cot_pi_3_43_lower : ℚ := 5054329449314795 / 1125899906842624
def cot_pi_3_43_upper : ℚ := 5054329449314801 / 1125899906842624
axiom cot_pi_3_43_bounds :
  ((cot_pi_3_43_lower : ℚ) : ℝ) ≤ cotangentTermV 3 43 ∧
  cotangentTermV 3 43 ≤ ((cot_pi_3_43_upper : ℚ) : ℝ)

def cot_pi_4_43_lower : ℚ := 7484663635567111 / 2251799813685248
def cot_pi_4_43_upper : ℚ := 7484663635567121 / 2251799813685248
axiom cot_pi_4_43_bounds :
  ((cot_pi_4_43_lower : ℚ) : ℝ) ≤ cotangentTermV 4 43 ∧
  cotangentTermV 4 43 ≤ ((cot_pi_4_43_upper : ℚ) : ℝ)

def cot_pi_5_43_lower : ℚ := 2943778603235869 / 1125899906842624
def cot_pi_5_43_upper : ℚ := 2943778603235873 / 1125899906842624
axiom cot_pi_5_43_bounds :
  ((cot_pi_5_43_lower : ℚ) : ℝ) ≤ cotangentTermV 5 43 ∧
  cotangentTermV 5 43 ≤ ((cot_pi_5_43_upper : ℚ) : ℝ)

def cot_pi_6_43_lower : ℚ := 4803524547707109 / 2251799813685248
def cot_pi_6_43_upper : ℚ := 4803524547707115 / 2251799813685248
axiom cot_pi_6_43_bounds :
  ((cot_pi_6_43_lower : ℚ) : ℝ) ≤ cotangentTermV 6 43 ∧
  cotangentTermV 6 43 ≤ ((cot_pi_6_43_upper : ℚ) : ℝ)

def cot_pi_7_43_lower : ℚ := 8024556944807347 / 4503599627370496
def cot_pi_7_43_upper : ℚ := 8024556944807359 / 4503599627370496
axiom cot_pi_7_43_bounds :
  ((cot_pi_7_43_lower : ℚ) : ℝ) ≤ cotangentTermV 7 43 ∧
  cotangentTermV 7 43 ≤ ((cot_pi_7_43_upper : ℚ) : ℝ)

def cot_pi_8_43_lower : ℚ := 212724937524895 / 140737488355328
def cot_pi_8_43_upper : ℚ := 1701799500199163 / 1125899906842624
axiom cot_pi_8_43_bounds :
  ((cot_pi_8_43_lower : ℚ) : ℝ) ≤ cotangentTermV 8 43 ∧
  cotangentTermV 8 43 ≤ ((cot_pi_8_43_upper : ℚ) : ℝ)

def cot_pi_9_43_lower : ℚ := 5832357001178801 / 4503599627370496
def cot_pi_9_43_upper : ℚ := 5832357001178811 / 4503599627370496
axiom cot_pi_9_43_bounds :
  ((cot_pi_9_43_lower : ℚ) : ℝ) ≤ cotangentTermV 9 43 ∧
  cotangentTermV 9 43 ≤ ((cot_pi_9_43_upper : ℚ) : ℝ)

def cot_pi_10_43_lower : ℚ := 157072398729919 / 140737488355328
def cot_pi_10_43_upper : ℚ := 628289594919677 / 562949953421312
axiom cot_pi_10_43_bounds :
  ((cot_pi_10_43_lower : ℚ) : ℝ) ≤ cotangentTermV 10 43 ∧
  cotangentTermV 10 43 ≤ ((cot_pi_10_43_upper : ℚ) : ℝ)

def cot_pi_11_43_lower : ℚ := 2171007920440947 / 2251799813685248
def cot_pi_11_43_upper : ℚ := 271375990055119 / 281474976710656
axiom cot_pi_11_43_bounds :
  ((cot_pi_11_43_lower : ℚ) : ℝ) ≤ cotangentTermV 11 43 ∧
  cotangentTermV 11 43 ≤ ((cot_pi_11_43_upper : ℚ) : ℝ)

def cot_pi_12_43_lower : ℚ := 1873962077294417 / 2251799813685248
def cot_pi_12_43_upper : ℚ := 468490519323605 / 562949953421312
axiom cot_pi_12_43_bounds :
  ((cot_pi_12_43_lower : ℚ) : ℝ) ≤ cotangentTermV 12 43 ∧
  cotangentTermV 12 43 ≤ ((cot_pi_12_43_upper : ℚ) : ℝ)

def cot_pi_13_43_lower : ℚ := 3222049245228357 / 4503599627370496
def cot_pi_13_43_upper : ℚ := 3222049245228365 / 4503599627370496
axiom cot_pi_13_43_bounds :
  ((cot_pi_13_43_lower : ℚ) : ℝ) ≤ cotangentTermV 13 43 ∧
  cotangentTermV 13 43 ≤ ((cot_pi_13_43_upper : ℚ) : ℝ)

def cot_pi_14_43_lower : ℚ := 687126791862139 / 1125899906842624
def cot_pi_14_43_upper : ℚ := 2748507167448563 / 4503599627370496
axiom cot_pi_14_43_bounds :
  ((cot_pi_14_43_lower : ℚ) : ℝ) ≤ cotangentTermV 14 43 ∧
  cotangentTermV 14 43 ≤ ((cot_pi_14_43_upper : ℚ) : ℝ)

def cot_pi_15_43_lower : ℚ := 2315460207795471 / 4503599627370496
def cot_pi_15_43_upper : ℚ := 1157730103897739 / 2251799813685248
axiom cot_pi_15_43_bounds :
  ((cot_pi_15_43_lower : ℚ) : ℝ) ≤ cotangentTermV 15 43 ∧
  cotangentTermV 15 43 ≤ ((cot_pi_15_43_upper : ℚ) : ℝ)

def cot_pi_16_43_lower : ℚ := 7655289302690733 / 18014398509481984
def cot_pi_16_43_upper : ℚ := 7655289302690753 / 18014398509481984
axiom cot_pi_16_43_bounds :
  ((cot_pi_16_43_lower : ℚ) : ℝ) ≤ cotangentTermV 16 43 ∧
  cotangentTermV 16 43 ≤ ((cot_pi_16_43_upper : ℚ) : ℝ)

def cot_pi_17_43_lower : ℚ := 3072829591179417 / 9007199254740992
def cot_pi_17_43_upper : ℚ := 3072829591179429 / 9007199254740992
axiom cot_pi_17_43_bounds :
  ((cot_pi_17_43_lower : ℚ) : ℝ) ≤ cotangentTermV 17 43 ∧
  cotangentTermV 17 43 ≤ ((cot_pi_17_43_upper : ℚ) : ℝ)

def cot_pi_18_43_lower : ℚ := 2354790453117307 / 9007199254740992
def cot_pi_18_43_upper : ℚ := 588697613279329 / 2251799813685248
axiom cot_pi_18_43_bounds :
  ((cot_pi_18_43_lower : ℚ) : ℝ) ≤ cotangentTermV 18 43 ∧
  cotangentTermV 18 43 ≤ ((cot_pi_18_43_upper : ℚ) : ℝ)

def cot_pi_19_43_lower : ℚ := 6654856264865129 / 36028797018963968
def cot_pi_19_43_upper : ℚ := 6654856264865171 / 36028797018963968
axiom cot_pi_19_43_bounds :
  ((cot_pi_19_43_lower : ℚ) : ℝ) ≤ cotangentTermV 19 43 ∧
  cotangentTermV 19 43 ≤ ((cot_pi_19_43_upper : ℚ) : ℝ)

def cot_pi_20_43_lower : ℚ := 7928589940093415 / 72057594037927936
def cot_pi_20_43_upper : ℚ := 7928589940093469 / 72057594037927936
axiom cot_pi_20_43_bounds :
  ((cot_pi_20_43_lower : ℚ) : ℝ) ≤ cotangentTermV 20 43 ∧
  cotangentTermV 20 43 ≤ ((cot_pi_20_43_upper : ℚ) : ℝ)

def cot_pi_21_43_lower : ℚ := 1316723009367947 / 36028797018963968
def cot_pi_21_43_upper : ℚ := 329180752341999 / 9007199254740992
axiom cot_pi_21_43_bounds :
  ((cot_pi_21_43_lower : ℚ) : ℝ) ≤ cotangentTermV 21 43 ∧
  cotangentTermV 21 43 ≤ ((cot_pi_21_43_upper : ℚ) : ℝ)

def cot_pi_22_43_lower : ℚ := -41147594042749 / 1125899906842624
def cot_pi_22_43_upper : ℚ := -2633446018735837 / 72057594037927936
axiom cot_pi_22_43_bounds :
  ((cot_pi_22_43_lower : ℚ) : ℝ) ≤ cotangentTermV 22 43 ∧
  cotangentTermV 22 43 ≤ ((cot_pi_22_43_upper : ℚ) : ℝ)

def cot_pi_23_43_lower : ℚ := -1982147485023367 / 18014398509481984
def cot_pi_23_43_upper : ℚ := -1982147485023341 / 18014398509481984
axiom cot_pi_23_43_bounds :
  ((cot_pi_23_43_lower : ℚ) : ℝ) ≤ cotangentTermV 23 43 ∧
  cotangentTermV 23 43 ≤ ((cot_pi_23_43_upper : ℚ) : ℝ)

def cot_pi_24_43_lower : ℚ := -3327428132432577 / 18014398509481984
def cot_pi_24_43_upper : ℚ := -3327428132432561 / 18014398509481984
axiom cot_pi_24_43_bounds :
  ((cot_pi_24_43_lower : ℚ) : ℝ) ≤ cotangentTermV 24 43 ∧
  cotangentTermV 24 43 ≤ ((cot_pi_24_43_upper : ℚ) : ℝ)

def cot_pi_25_43_lower : ℚ := -4709580906234629 / 18014398509481984
def cot_pi_25_43_upper : ℚ := -4709580906234597 / 18014398509481984
axiom cot_pi_25_43_bounds :
  ((cot_pi_25_43_lower : ℚ) : ℝ) ≤ cotangentTermV 25 43 ∧
  cotangentTermV 25 43 ≤ ((cot_pi_25_43_upper : ℚ) : ℝ)

def cot_pi_26_43_lower : ℚ := -6145659182358851 / 18014398509481984
def cot_pi_26_43_upper : ℚ := -6145659182358817 / 18014398509481984
axiom cot_pi_26_43_bounds :
  ((cot_pi_26_43_lower : ℚ) : ℝ) ≤ cotangentTermV 26 43 ∧
  cotangentTermV 26 43 ≤ ((cot_pi_26_43_upper : ℚ) : ℝ)

def cot_pi_27_43_lower : ℚ := -3827644651345375 / 9007199254740992
def cot_pi_27_43_upper : ℚ := -3827644651345357 / 9007199254740992
axiom cot_pi_27_43_bounds :
  ((cot_pi_27_43_lower : ℚ) : ℝ) ≤ cotangentTermV 27 43 ∧
  cotangentTermV 27 43 ≤ ((cot_pi_27_43_upper : ℚ) : ℝ)

def cot_pi_28_43_lower : ℚ := -2315460207795475 / 4503599627370496
def cot_pi_28_43_upper : ℚ := -1157730103897733 / 2251799813685248
axiom cot_pi_28_43_bounds :
  ((cot_pi_28_43_lower : ℚ) : ℝ) ≤ cotangentTermV 28 43 ∧
  cotangentTermV 28 43 ≤ ((cot_pi_28_43_upper : ℚ) : ℝ)

def cot_pi_29_43_lower : ℚ := -5497014334897125 / 9007199254740992
def cot_pi_29_43_upper : ℚ := -5497014334897095 / 9007199254740992
axiom cot_pi_29_43_bounds :
  ((cot_pi_29_43_lower : ℚ) : ℝ) ≤ cotangentTermV 29 43 ∧
  cotangentTermV 29 43 ≤ ((cot_pi_29_43_upper : ℚ) : ℝ)

def cot_pi_30_43_lower : ℚ := -6444098490456727 / 9007199254740992
def cot_pi_30_43_upper : ℚ := -6444098490456695 / 9007199254740992
axiom cot_pi_30_43_bounds :
  ((cot_pi_30_43_lower : ℚ) : ℝ) ≤ cotangentTermV 30 43 ∧
  cotangentTermV 30 43 ≤ ((cot_pi_30_43_upper : ℚ) : ℝ)

def cot_pi_31_43_lower : ℚ := -3747924154588843 / 4503599627370496
def cot_pi_31_43_upper : ℚ := -3747924154588825 / 4503599627370496
axiom cot_pi_31_43_bounds :
  ((cot_pi_31_43_lower : ℚ) : ℝ) ≤ cotangentTermV 31 43 ∧
  cotangentTermV 31 43 ≤ ((cot_pi_31_43_upper : ℚ) : ℝ)

def cot_pi_32_43_lower : ℚ := -8684031681763801 / 9007199254740992
def cot_pi_32_43_upper : ℚ := -8684031681763773 / 9007199254740992
axiom cot_pi_32_43_bounds :
  ((cot_pi_32_43_lower : ℚ) : ℝ) ≤ cotangentTermV 32 43 ∧
  cotangentTermV 32 43 ≤ ((cot_pi_32_43_upper : ℚ) : ℝ)

def cot_pi_33_43_lower : ℚ := -2513158379678709 / 2251799813685248
def cot_pi_33_43_upper : ℚ := -2513158379678697 / 2251799813685248
axiom cot_pi_33_43_bounds :
  ((cot_pi_33_43_lower : ℚ) : ℝ) ≤ cotangentTermV 33 43 ∧
  cotangentTermV 33 43 ≤ ((cot_pi_33_43_upper : ℚ) : ℝ)

def cot_pi_34_43_lower : ℚ := -1458089250294703 / 1125899906842624
def cot_pi_34_43_upper : ℚ := -182261156286837 / 140737488355328
axiom cot_pi_34_43_bounds :
  ((cot_pi_34_43_lower : ℚ) : ℝ) ≤ cotangentTermV 34 43 ∧
  cotangentTermV 34 43 ≤ ((cot_pi_34_43_upper : ℚ) : ℝ)

def cot_pi_35_43_lower : ℚ := -6807198000796659 / 4503599627370496
def cot_pi_35_43_upper : ℚ := -6807198000796623 / 4503599627370496
axiom cot_pi_35_43_bounds :
  ((cot_pi_35_43_lower : ℚ) : ℝ) ≤ cotangentTermV 35 43 ∧
  cotangentTermV 35 43 ≤ ((cot_pi_35_43_upper : ℚ) : ℝ)

def cot_pi_36_43_lower : ℚ := -8024556944807359 / 4503599627370496
def cot_pi_36_43_upper : ℚ := -8024556944807329 / 4503599627370496
axiom cot_pi_36_43_bounds :
  ((cot_pi_36_43_lower : ℚ) : ℝ) ≤ cotangentTermV 36 43 ∧
  cotangentTermV 36 43 ≤ ((cot_pi_36_43_upper : ℚ) : ℝ)

def cot_pi_37_43_lower : ℚ := -4803524547707121 / 2251799813685248
def cot_pi_37_43_upper : ℚ := -4803524547707093 / 2251799813685248
axiom cot_pi_37_43_bounds :
  ((cot_pi_37_43_lower : ℚ) : ℝ) ≤ cotangentTermV 37 43 ∧
  cotangentTermV 37 43 ≤ ((cot_pi_37_43_upper : ℚ) : ℝ)

def cot_pi_38_43_lower : ℚ := -5887557206471751 / 2251799813685248
def cot_pi_38_43_upper : ℚ := -5887557206471711 / 2251799813685248
axiom cot_pi_38_43_bounds :
  ((cot_pi_38_43_lower : ℚ) : ℝ) ≤ cotangentTermV 38 43 ∧
  cotangentTermV 38 43 ≤ ((cot_pi_38_43_upper : ℚ) : ℝ)

def cot_pi_39_43_lower : ℚ := -7484663635567127 / 2251799813685248
def cot_pi_39_43_upper : ℚ := -7484663635567067 / 2251799813685248
axiom cot_pi_39_43_bounds :
  ((cot_pi_39_43_lower : ℚ) : ℝ) ≤ cotangentTermV 39 43 ∧
  cotangentTermV 39 43 ≤ ((cot_pi_39_43_upper : ℚ) : ℝ)

def cot_pi_40_43_lower : ℚ := -2527164724657405 / 562949953421312
def cot_pi_40_43_upper : ℚ := -2527164724657387 / 562949953421312
axiom cot_pi_40_43_bounds :
  ((cot_pi_40_43_lower : ℚ) : ℝ) ≤ cotangentTermV 40 43 ∧
  cotangentTermV 40 43 ≤ ((cot_pi_40_43_upper : ℚ) : ℝ)

def cot_pi_41_43_lower : ℚ := -3825180880343113 / 562949953421312
def cot_pi_41_43_upper : ℚ := -3825180880343039 / 562949953421312
axiom cot_pi_41_43_bounds :
  ((cot_pi_41_43_lower : ℚ) : ℝ) ≤ cotangentTermV 41 43 ∧
  cotangentTermV 41 43 ≤ ((cot_pi_41_43_upper : ℚ) : ℝ)

def cot_pi_42_43_lower : ℚ := -3845782193296393 / 281474976710656
def cot_pi_42_43_upper : ℚ := -3845782193296249 / 281474976710656
axiom cot_pi_42_43_bounds :
  ((cot_pi_42_43_lower : ℚ) : ℝ) ≤ cotangentTermV 42 43 ∧
  cotangentTermV 42 43 ≤ ((cot_pi_42_43_upper : ℚ) : ℝ)

def cot_pi_1_44_lower : ℚ := 7871068833121619 / 562949953421312
def cot_pi_1_44_upper : ℚ := 7871068833121631 / 562949953421312
axiom cot_pi_1_44_bounds :
  ((cot_pi_1_44_lower : ℚ) : ℝ) ≤ cotangentTermV 1 44 ∧
  cotangentTermV 1 44 ≤ ((cot_pi_1_44_upper : ℚ) : ℝ)

def cot_pi_2_44_lower : ℚ := 244712683056749 / 35184372088832
def cot_pi_2_44_upper : ℚ := 1957701464453995 / 281474976710656
axiom cot_pi_2_44_bounds :
  ((cot_pi_2_44_lower : ℚ) : ℝ) ≤ cotangentTermV 2 44 ∧
  cotangentTermV 2 44 ≤ ((cot_pi_2_44_upper : ℚ) : ℝ)

def cot_pi_3_44_lower : ℚ := 2587839170925175 / 562949953421312
def cot_pi_3_44_upper : ℚ := 1293919585462589 / 281474976710656
axiom cot_pi_3_44_bounds :
  ((cot_pi_3_44_lower : ℚ) : ℝ) ≤ cotangentTermV 3 44 ∧
  cotangentTermV 3 44 ≤ ((cot_pi_3_44_upper : ℚ) : ℝ)

def cot_pi_4_44_lower : ℚ := 7668925890001035 / 2251799813685248
def cot_pi_4_44_upper : ℚ := 7668925890001047 / 2251799813685248
axiom cot_pi_4_44_bounds :
  ((cot_pi_4_44_lower : ℚ) : ℝ) ≤ cotangentTermV 4 44 ∧
  cotangentTermV 4 44 ≤ ((cot_pi_4_44_upper : ℚ) : ℝ)

def cot_pi_5_44_lower : ℚ := 754663617672945 / 281474976710656
def cot_pi_5_44_upper : ℚ := 377331808836473 / 140737488355328
axiom cot_pi_5_44_bounds :
  ((cot_pi_5_44_lower : ℚ) : ℝ) ≤ cotangentTermV 5 44 ∧
  cotangentTermV 5 44 ≤ ((cot_pi_5_44_upper : ℚ) : ℝ)

def cot_pi_6_44_lower : ℚ := 4930753808967761 / 2251799813685248
def cot_pi_6_44_upper : ℚ := 4930753808967767 / 2251799813685248
axiom cot_pi_6_44_bounds :
  ((cot_pi_6_44_lower : ℚ) : ℝ) ≤ cotangentTermV 6 44 ∧
  cotangentTermV 6 44 ≤ ((cot_pi_6_44_upper : ℚ) : ℝ)

def cot_pi_7_44_lower : ℚ := 2061931730632379 / 1125899906842624
def cot_pi_7_44_upper : ℚ := 4123863461264763 / 2251799813685248
axiom cot_pi_7_44_bounds :
  ((cot_pi_7_44_lower : ℚ) : ℝ) ≤ cotangentTermV 7 44 ∧
  cotangentTermV 7 44 ≤ ((cot_pi_7_44_upper : ℚ) : ℝ)

def cot_pi_8_44_lower : ℚ := 7007737807909369 / 4503599627370496
def cot_pi_8_44_upper : ℚ := 7007737807909381 / 4503599627370496
axiom cot_pi_8_44_bounds :
  ((cot_pi_8_44_lower : ℚ) : ℝ) ≤ cotangentTermV 8 44 ∧
  cotangentTermV 8 44 ≤ ((cot_pi_8_44_upper : ℚ) : ℝ)

def cot_pi_9_44_lower : ℚ := 3008052390229861 / 2251799813685248
def cot_pi_9_44_upper : ℚ := 1504026195114933 / 1125899906842624
axiom cot_pi_9_44_bounds :
  ((cot_pi_9_44_lower : ℚ) : ℝ) ≤ cotangentTermV 9 44 ∧
  cotangentTermV 9 44 ≤ ((cot_pi_9_44_upper : ℚ) : ℝ)

def cot_pi_10_44_lower : ℚ := 5197431033835087 / 4503599627370496
def cot_pi_10_44_upper : ℚ := 5197431033835095 / 4503599627370496
axiom cot_pi_10_44_bounds :
  ((cot_pi_10_44_lower : ℚ) : ℝ) ≤ cotangentTermV 10 44 ∧
  cotangentTermV 10 44 ≤ ((cot_pi_10_44_upper : ℚ) : ℝ)

def cot_pi_11_44_lower : ℚ := 9007199254740983 / 9007199254740992
def cot_pi_11_44_upper : ℚ := 2251799813685251 / 2251799813685248
axiom cot_pi_11_44_bounds :
  ((cot_pi_11_44_lower : ℚ) : ℝ) ≤ cotangentTermV 11 44 ∧
  cotangentTermV 11 44 ≤ ((cot_pi_11_44_upper : ℚ) : ℝ)

def cot_pi_12_44_lower : ℚ := 7804782582631265 / 9007199254740992
def cot_pi_12_44_upper : ℚ := 7804782582631277 / 9007199254740992
axiom cot_pi_12_44_bounds :
  ((cot_pi_12_44_lower : ℚ) : ℝ) ≤ cotangentTermV 12 44 ∧
  cotangentTermV 12 44 ≤ ((cot_pi_12_44_upper : ℚ) : ℝ)

def cot_pi_13_44_lower : ℚ := 26338691031977 / 35184372088832
def cot_pi_13_44_upper : ℚ := 1685676226046531 / 2251799813685248
axiom cot_pi_13_44_bounds :
  ((cot_pi_13_44_lower : ℚ) : ℝ) ≤ cotangentTermV 13 44 ∧
  cotangentTermV 13 44 ≤ ((cot_pi_13_44_upper : ℚ) : ℝ)

def cot_pi_14_44_lower : ℚ := 723571934325213 / 1125899906842624
def cot_pi_14_44_upper : ℚ := 2894287737300857 / 4503599627370496
axiom cot_pi_14_44_bounds :
  ((cot_pi_14_44_lower : ℚ) : ℝ) ≤ cotangentTermV 14 44 ∧
  cotangentTermV 14 44 ≤ ((cot_pi_14_44_upper : ℚ) : ℝ)

def cot_pi_15_44_lower : ℚ := 2459151447927809 / 4503599627370496
def cot_pi_15_44_upper : ℚ := 2459151447927817 / 4503599627370496
axiom cot_pi_15_44_bounds :
  ((cot_pi_15_44_lower : ℚ) : ℝ) ≤ cotangentTermV 15 44 ∧
  cotangentTermV 15 44 ≤ ((cot_pi_15_44_upper : ℚ) : ℝ)

def cot_pi_16_44_lower : ℚ := 8226900141217031 / 18014398509481984
def cot_pi_16_44_upper : ℚ := 8226900141217051 / 18014398509481984
axiom cot_pi_16_44_bounds :
  ((cot_pi_16_44_lower : ℚ) : ℝ) ≤ cotangentTermV 16 44 ∧
  cotangentTermV 16 44 ≤ ((cot_pi_16_44_upper : ℚ) : ℝ)

def cot_pi_17_44_lower : ℚ := 6719023260387781 / 18014398509481984
def cot_pi_17_44_upper : ℚ := 6719023260387807 / 18014398509481984
axiom cot_pi_17_44_bounds :
  ((cot_pi_17_44_lower : ℚ) : ℝ) ≤ cotangentTermV 17 44 ∧
  cotangentTermV 17 44 ≤ ((cot_pi_17_44_upper : ℚ) : ℝ)

def cot_pi_18_44_lower : ℚ := 330594041045833 / 1125899906842624
def cot_pi_18_44_upper : ℚ := 2644752328366673 / 9007199254740992
axiom cot_pi_18_44_bounds :
  ((cot_pi_18_44_lower : ℚ) : ℝ) ≤ cotangentTermV 18 44 ∧
  cotangentTermV 18 44 ≤ ((cot_pi_18_44_upper : ℚ) : ℝ)

def cot_pi_19_44_lower : ℚ := 3918792526121413 / 18014398509481984
def cot_pi_19_44_upper : ℚ := 1959396263060717 / 9007199254740992
axiom cot_pi_19_44_bounds :
  ((cot_pi_19_44_lower : ℚ) : ℝ) ≤ cotangentTermV 19 44 ∧
  cotangentTermV 19 44 ≤ ((cot_pi_19_44_upper : ℚ) : ℝ)

def cot_pi_20_44_lower : ℚ := 5180158970077811 / 36028797018963968
def cot_pi_20_44_upper : ℚ := 5180158970077841 / 36028797018963968
axiom cot_pi_20_44_bounds :
  ((cot_pi_20_44_lower : ℚ) : ℝ) ≤ cotangentTermV 20 44 ∧
  cotangentTermV 20 44 ≤ ((cot_pi_20_44_upper : ℚ) : ℝ)

def cot_pi_21_44_lower : ℚ := 5153660839123347 / 72057594037927936
def cot_pi_21_44_upper : ℚ := 5153660839123447 / 72057594037927936
axiom cot_pi_21_44_bounds :
  ((cot_pi_21_44_lower : ℚ) : ℝ) ≤ cotangentTermV 21 44 ∧
  cotangentTermV 21 44 ≤ ((cot_pi_21_44_upper : ℚ) : ℝ)

def cot_pi_22_44_lower : ℚ := -225732797 / 604462909807314587353088
def cot_pi_22_44_upper : ℚ := 568158399 / 604462909807314587353088
axiom cot_pi_22_44_bounds :
  ((cot_pi_22_44_lower : ℚ) : ℝ) ≤ cotangentTermV 22 44 ∧
  cotangentTermV 22 44 ≤ ((cot_pi_22_44_upper : ℚ) : ℝ)

def cot_pi_23_44_lower : ℚ := -2576830419561695 / 36028797018963968
def cot_pi_23_44_upper : ℚ := -644207604890411 / 9007199254740992
axiom cot_pi_23_44_bounds :
  ((cot_pi_23_44_lower : ℚ) : ℝ) ≤ cotangentTermV 23 44 ∧
  cotangentTermV 23 44 ≤ ((cot_pi_23_44_upper : ℚ) : ℝ)

def cot_pi_24_44_lower : ℚ := -1295039742519457 / 9007199254740992
def cot_pi_24_44_upper : ℚ := -2590079485038899 / 18014398509481984
axiom cot_pi_24_44_bounds :
  ((cot_pi_24_44_lower : ℚ) : ℝ) ≤ cotangentTermV 24 44 ∧
  cotangentTermV 24 44 ≤ ((cot_pi_24_44_upper : ℚ) : ℝ)

def cot_pi_25_44_lower : ℚ := -7837585052242855 / 36028797018963968
def cot_pi_25_44_upper : ℚ := -7837585052242797 / 36028797018963968
axiom cot_pi_25_44_bounds :
  ((cot_pi_25_44_lower : ℚ) : ℝ) ≤ cotangentTermV 25 44 ∧
  cotangentTermV 25 44 ≤ ((cot_pi_25_44_upper : ℚ) : ℝ)

def cot_pi_26_44_lower : ℚ := -5289504656733343 / 18014398509481984
def cot_pi_26_44_upper : ℚ := -5289504656733319 / 18014398509481984
axiom cot_pi_26_44_bounds :
  ((cot_pi_26_44_lower : ℚ) : ℝ) ≤ cotangentTermV 26 44 ∧
  cotangentTermV 26 44 ≤ ((cot_pi_26_44_upper : ℚ) : ℝ)

def cot_pi_27_44_lower : ℚ := -6719023260387799 / 18014398509481984
def cot_pi_27_44_upper : ℚ := -6719023260387765 / 18014398509481984
axiom cot_pi_27_44_bounds :
  ((cot_pi_27_44_lower : ℚ) : ℝ) ≤ cotangentTermV 27 44 ∧
  cotangentTermV 27 44 ≤ ((cot_pi_27_44_upper : ℚ) : ℝ)

def cot_pi_28_44_lower : ℚ := -8226900141217045 / 18014398509481984
def cot_pi_28_44_upper : ℚ := -8226900141217023 / 18014398509481984
axiom cot_pi_28_44_bounds :
  ((cot_pi_28_44_lower : ℚ) : ℝ) ≤ cotangentTermV 28 44 ∧
  cotangentTermV 28 44 ≤ ((cot_pi_28_44_upper : ℚ) : ℝ)

def cot_pi_29_44_lower : ℚ := -307393930990977 / 562949953421312
def cot_pi_29_44_upper : ℚ := -2459151447927803 / 4503599627370496
axiom cot_pi_29_44_bounds :
  ((cot_pi_29_44_lower : ℚ) : ℝ) ≤ cotangentTermV 29 44 ∧
  cotangentTermV 29 44 ≤ ((cot_pi_29_44_upper : ℚ) : ℝ)

def cot_pi_30_44_lower : ℚ := -5788575474601719 / 9007199254740992
def cot_pi_30_44_upper : ℚ := -5788575474601689 / 9007199254740992
axiom cot_pi_30_44_bounds :
  ((cot_pi_30_44_lower : ℚ) : ℝ) ≤ cotangentTermV 30 44 ∧
  cotangentTermV 30 44 ≤ ((cot_pi_30_44_upper : ℚ) : ℝ)

def cot_pi_31_44_lower : ℚ := -3371352452093063 / 4503599627370496
def cot_pi_31_44_upper : ℚ := -3371352452093047 / 4503599627370496
axiom cot_pi_31_44_bounds :
  ((cot_pi_31_44_lower : ℚ) : ℝ) ≤ cotangentTermV 31 44 ∧
  cotangentTermV 31 44 ≤ ((cot_pi_31_44_upper : ℚ) : ℝ)

def cot_pi_32_44_lower : ℚ := -3902391291315637 / 4503599627370496
def cot_pi_32_44_upper : ℚ := -487798911414453 / 562949953421312
axiom cot_pi_32_44_bounds :
  ((cot_pi_32_44_lower : ℚ) : ℝ) ≤ cotangentTermV 32 44 ∧
  cotangentTermV 32 44 ≤ ((cot_pi_32_44_upper : ℚ) : ℝ)

def cot_pi_33_44_lower : ℚ := -2251799813685251 / 2251799813685248
def cot_pi_33_44_upper : ℚ := -4503599627370481 / 4503599627370496
axiom cot_pi_33_44_bounds :
  ((cot_pi_33_44_lower : ℚ) : ℝ) ≤ cotangentTermV 33 44 ∧
  cotangentTermV 33 44 ≤ ((cot_pi_33_44_upper : ℚ) : ℝ)

def cot_pi_34_44_lower : ℚ := -649678879229387 / 562949953421312
def cot_pi_34_44_upper : ℚ := -2598715516917535 / 2251799813685248
axiom cot_pi_34_44_bounds :
  ((cot_pi_34_44_lower : ℚ) : ℝ) ≤ cotangentTermV 34 44 ∧
  cotangentTermV 34 44 ≤ ((cot_pi_34_44_upper : ℚ) : ℝ)

def cot_pi_35_44_lower : ℚ := -1504026195114933 / 1125899906842624
def cot_pi_35_44_upper : ℚ := -3008052390229857 / 2251799813685248
axiom cot_pi_35_44_bounds :
  ((cot_pi_35_44_lower : ℚ) : ℝ) ≤ cotangentTermV 35 44 ∧
  cotangentTermV 35 44 ≤ ((cot_pi_35_44_upper : ℚ) : ℝ)

def cot_pi_36_44_lower : ℚ := -7007737807909383 / 4503599627370496
def cot_pi_36_44_upper : ℚ := -7007737807909357 / 4503599627370496
axiom cot_pi_36_44_bounds :
  ((cot_pi_36_44_lower : ℚ) : ℝ) ≤ cotangentTermV 36 44 ∧
  cotangentTermV 36 44 ≤ ((cot_pi_36_44_upper : ℚ) : ℝ)

def cot_pi_37_44_lower : ℚ := -8247726922529529 / 4503599627370496
def cot_pi_37_44_upper : ℚ := -8247726922529485 / 4503599627370496
axiom cot_pi_37_44_bounds :
  ((cot_pi_37_44_lower : ℚ) : ℝ) ≤ cotangentTermV 37 44 ∧
  cotangentTermV 37 44 ≤ ((cot_pi_37_44_upper : ℚ) : ℝ)

def cot_pi_38_44_lower : ℚ := -4930753808967775 / 2251799813685248
def cot_pi_38_44_upper : ℚ := -4930753808967745 / 2251799813685248
axiom cot_pi_38_44_bounds :
  ((cot_pi_38_44_lower : ℚ) : ℝ) ≤ cotangentTermV 38 44 ∧
  cotangentTermV 38 44 ≤ ((cot_pi_38_44_upper : ℚ) : ℝ)

def cot_pi_39_44_lower : ℚ := -3018654470691789 / 1125899906842624
def cot_pi_39_44_upper : ℚ := -377331808836471 / 140737488355328
axiom cot_pi_39_44_bounds :
  ((cot_pi_39_44_lower : ℚ) : ℝ) ≤ cotangentTermV 39 44 ∧
  cotangentTermV 39 44 ≤ ((cot_pi_39_44_upper : ℚ) : ℝ)

def cot_pi_40_44_lower : ℚ := -3834462945000525 / 1125899906842624
def cot_pi_40_44_upper : ℚ := -3834462945000503 / 1125899906842624
axiom cot_pi_40_44_bounds :
  ((cot_pi_40_44_lower : ℚ) : ℝ) ≤ cotangentTermV 40 44 ∧
  cotangentTermV 40 44 ≤ ((cot_pi_40_44_upper : ℚ) : ℝ)

def cot_pi_41_44_lower : ℚ := -5175678341850377 / 1125899906842624
def cot_pi_41_44_upper : ℚ := -5175678341850307 / 1125899906842624
axiom cot_pi_41_44_bounds :
  ((cot_pi_41_44_lower : ℚ) : ℝ) ≤ cotangentTermV 41 44 ∧
  cotangentTermV 41 44 ≤ ((cot_pi_41_44_upper : ℚ) : ℝ)

def cot_pi_42_44_lower : ℚ := -3915402928907999 / 562949953421312
def cot_pi_42_44_upper : ℚ := -1957701464453961 / 281474976710656
axiom cot_pi_42_44_bounds :
  ((cot_pi_42_44_lower : ℚ) : ℝ) ≤ cotangentTermV 42 44 ∧
  cotangentTermV 42 44 ≤ ((cot_pi_42_44_upper : ℚ) : ℝ)

def cot_pi_43_44_lower : ℚ := -3935534416560857 / 281474976710656
def cot_pi_43_44_upper : ℚ := -983883604140177 / 70368744177664
axiom cot_pi_43_44_bounds :
  ((cot_pi_43_44_lower : ℚ) : ℝ) ≤ cotangentTermV 43 44 ∧
  cotangentTermV 43 44 ≤ ((cot_pi_43_44_upper : ℚ) : ℝ)

def cot_pi_1_45_lower : ℚ := 1006319925388713 / 70368744177664
def cot_pi_1_45_upper : ℚ := 2012639850777429 / 140737488355328
axiom cot_pi_1_45_bounds :
  ((cot_pi_1_45_lower : ℚ) : ℝ) ≤ cotangentTermV 1 45 ∧
  cotangentTermV 1 45 ≤ ((cot_pi_1_45_upper : ℚ) : ℝ)

def cot_pi_2_45_lower : ℚ := 8011194107583203 / 1125899906842624
def cot_pi_2_45_upper : ℚ := 8011194107583215 / 1125899906842624
axiom cot_pi_2_45_bounds :
  ((cot_pi_2_45_lower : ℚ) : ℝ) ≤ cotangentTermV 2 45 ∧
  cotangentTermV 2 45 ≤ ((cot_pi_2_45_upper : ℚ) : ℝ)

def cot_pi_3_45_lower : ℚ := 662117825248849 / 140737488355328
def cot_pi_3_45_upper : ℚ := 2648471300995399 / 562949953421312
axiom cot_pi_3_45_bounds :
  ((cot_pi_3_45_lower : ℚ) : ℝ) ≤ cotangentTermV 3 45 ∧
  cotangentTermV 3 45 ≤ ((cot_pi_3_45_upper : ℚ) : ℝ)

def cot_pi_4_45_lower : ℚ := 1963239798721049 / 562949953421312
def cot_pi_4_45_upper : ℚ := 490809949680263 / 140737488355328
axiom cot_pi_4_45_bounds :
  ((cot_pi_4_45_lower : ℚ) : ℝ) ≤ cotangentTermV 4 45 ∧
  cotangentTermV 4 45 ≤ ((cot_pi_4_45_upper : ℚ) : ℝ)

def cot_pi_5_45_lower : ℚ := 1546692285308085 / 562949953421312
def cot_pi_5_45_upper : ℚ := 1546692285308087 / 562949953421312
axiom cot_pi_5_45_bounds :
  ((cot_pi_5_45_lower : ℚ) : ℝ) ≤ cotangentTermV 5 45 ∧
  cotangentTermV 5 45 ≤ ((cot_pi_5_45_upper : ℚ) : ℝ)

def cot_pi_6_45_lower : ℚ := 2528812594503863 / 1125899906842624
def cot_pi_6_45_upper : ℚ := 1264406297251933 / 562949953421312
axiom cot_pi_6_45_bounds :
  ((cot_pi_6_45_lower : ℚ) : ℝ) ≤ cotangentTermV 6 45 ∧
  cotangentTermV 6 45 ≤ ((cot_pi_6_45_upper : ℚ) : ℝ)

def cot_pi_7_45_lower : ℚ := 4235019504259783 / 2251799813685248
def cot_pi_7_45_upper : ℚ := 1058754876064947 / 562949953421312
axiom cot_pi_7_45_bounds :
  ((cot_pi_7_45_lower : ℚ) : ℝ) ≤ cotangentTermV 7 45 ∧
  cotangentTermV 7 45 ≤ ((cot_pi_7_45_upper : ℚ) : ℝ)

def cot_pi_8_45_lower : ℚ := 28153382768193 / 17592186044416
def cot_pi_8_45_upper : ℚ := 1801816497164355 / 1125899906842624
axiom cot_pi_8_45_bounds :
  ((cot_pi_8_45_lower : ℚ) : ℝ) ≤ cotangentTermV 8 45 ∧
  cotangentTermV 8 45 ≤ ((cot_pi_8_45_upper : ℚ) : ℝ)

def cot_pi_9_45_lower : ℚ := 6198673104153461 / 4503599627370496
def cot_pi_9_45_upper : ℚ := 6198673104153469 / 4503599627370496
axiom cot_pi_9_45_bounds :
  ((cot_pi_9_45_lower : ℚ) : ℝ) ≤ cotangentTermV 9 45 ∧
  cotangentTermV 9 45 ≤ ((cot_pi_9_45_upper : ℚ) : ℝ)

def cot_pi_10_45_lower : ℚ := 2683590517762365 / 2251799813685248
def cot_pi_10_45_upper : ℚ := 2683590517762369 / 2251799813685248
axiom cot_pi_10_45_bounds :
  ((cot_pi_10_45_lower : ℚ) : ℝ) ≤ cotangentTermV 10 45 ∧
  cotangentTermV 10 45 ≤ ((cot_pi_10_45_upper : ℚ) : ℝ)

def cot_pi_11_45_lower : ℚ := 582951741914757 / 562949953421312
def cot_pi_11_45_upper : ℚ := 1165903483829517 / 1125899906842624
axiom cot_pi_11_45_bounds :
  ((cot_pi_11_45_lower : ℚ) : ℝ) ≤ cotangentTermV 11 45 ∧
  cotangentTermV 11 45 ≤ ((cot_pi_11_45_upper : ℚ) : ℝ)

def cot_pi_12_45_lower : ℚ := 4055059318382637 / 4503599627370496
def cot_pi_12_45_upper : ℚ := 4055059318382643 / 4503599627370496
axiom cot_pi_12_45_bounds :
  ((cot_pi_12_45_lower : ℚ) : ℝ) ≤ cotangentTermV 12 45 ∧
  cotangentTermV 12 45 ≤ ((cot_pi_12_45_upper : ℚ) : ℝ)

def cot_pi_13_45_lower : ℚ := 1759298828202787 / 2251799813685248
def cot_pi_13_45_upper : ℚ := 1759298828202791 / 2251799813685248
axiom cot_pi_13_45_bounds :
  ((cot_pi_13_45_lower : ℚ) : ℝ) ≤ cotangentTermV 13 45 ∧
  cotangentTermV 13 45 ≤ ((cot_pi_13_45_upper : ℚ) : ℝ)

def cot_pi_14_45_lower : ℚ := 6075432610219553 / 9007199254740992
def cot_pi_14_45_upper : ℚ := 6075432610219563 / 9007199254740992
axiom cot_pi_14_45_bounds :
  ((cot_pi_14_45_lower : ℚ) : ℝ) ≤ cotangentTermV 14 45 ∧
  cotangentTermV 14 45 ≤ ((cot_pi_14_45_upper : ℚ) : ℝ)

def cot_pi_15_45_lower : ℚ := 650038614296163 / 1125899906842624
def cot_pi_15_45_upper : ℚ := 650038614296165 / 1125899906842624
axiom cot_pi_15_45_bounds :
  ((cot_pi_15_45_lower : ℚ) : ℝ) ≤ cotangentTermV 15 45 ∧
  cotangentTermV 15 45 ≤ ((cot_pi_15_45_upper : ℚ) : ℝ)

def cot_pi_16_45_lower : ℚ := 8786209216486639 / 18014398509481984
def cot_pi_16_45_upper : ℚ := 8786209216486659 / 18014398509481984
axiom cot_pi_16_45_bounds :
  ((cot_pi_16_45_lower : ℚ) : ℝ) ≤ cotangentTermV 16 45 ∧
  cotangentTermV 16 45 ≤ ((cot_pi_16_45_upper : ℚ) : ℝ)

def cot_pi_17_45_lower : ℚ := 7278289440476469 / 18014398509481984
def cot_pi_17_45_upper : ℚ := 7278289440476495 / 18014398509481984
axiom cot_pi_17_45_bounds :
  ((cot_pi_17_45_lower : ℚ) : ℝ) ≤ cotangentTermV 17 45 ∧
  cotangentTermV 17 45 ≤ ((cot_pi_17_45_upper : ℚ) : ℝ)

def cot_pi_18_45_lower : ℚ := 2926616445759701 / 9007199254740992
def cot_pi_18_45_upper : ℚ := 1463308222879853 / 4503599627370496
axiom cot_pi_18_45_bounds :
  ((cot_pi_18_45_lower : ℚ) : ℝ) ≤ cotangentTermV 18 45 ∧
  cotangentTermV 18 45 ≤ ((cot_pi_18_45_upper : ℚ) : ℝ)

def cot_pi_19_45_lower : ℚ := 8982988005580613 / 36028797018963968
def cot_pi_19_45_upper : ℚ := 8982988005580655 / 36028797018963968
axiom cot_pi_19_45_bounds :
  ((cot_pi_19_45_lower : ℚ) : ℝ) ≤ cotangentTermV 19 45 ∧
  cotangentTermV 19 45 ≤ ((cot_pi_19_45_upper : ℚ) : ℝ)

def cot_pi_20_45_lower : ℚ := 6352848996912047 / 36028797018963968
def cot_pi_20_45_upper : ℚ := 6352848996912077 / 36028797018963968
axiom cot_pi_20_45_bounds :
  ((cot_pi_20_45_lower : ℚ) : ℝ) ≤ cotangentTermV 20 45 ∧
  cotangentTermV 20 45 ≤ ((cot_pi_20_45_upper : ℚ) : ℝ)

def cot_pi_21_45_lower : ℚ := 7573558316440963 / 72057594037927936
def cot_pi_21_45_upper : ℚ := 7573558316441063 / 72057594037927936
axiom cot_pi_21_45_bounds :
  ((cot_pi_21_45_lower : ℚ) : ℝ) ≤ cotangentTermV 21 45 ∧
  cotangentTermV 21 45 ≤ ((cot_pi_21_45_upper : ℚ) : ℝ)

def cot_pi_22_45_lower : ℚ := 2516306631528393 / 72057594037927936
def cot_pi_22_45_upper : ℚ := 2516306631528489 / 72057594037927936
axiom cot_pi_22_45_bounds :
  ((cot_pi_22_45_lower : ℚ) : ℝ) ≤ cotangentTermV 22 45 ∧
  cotangentTermV 22 45 ≤ ((cot_pi_22_45_upper : ℚ) : ℝ)

def cot_pi_23_45_lower : ℚ := -5032613263056897 / 144115188075855872
def cot_pi_23_45_upper : ℚ := -5032613263056703 / 144115188075855872
axiom cot_pi_23_45_bounds :
  ((cot_pi_23_45_lower : ℚ) : ℝ) ≤ cotangentTermV 23 45 ∧
  cotangentTermV 23 45 ≤ ((cot_pi_23_45_upper : ℚ) : ℝ)

def cot_pi_24_45_lower : ℚ := -7573558316441001 / 72057594037927936
def cot_pi_24_45_upper : ℚ := -7573558316440945 / 72057594037927936
axiom cot_pi_24_45_bounds :
  ((cot_pi_24_45_lower : ℚ) : ℝ) ≤ cotangentTermV 24 45 ∧
  cotangentTermV 24 45 ≤ ((cot_pi_24_45_upper : ℚ) : ℝ)

def cot_pi_25_45_lower : ℚ := -6352848996912069 / 36028797018963968
def cot_pi_25_45_upper : ℚ := -6352848996912013 / 36028797018963968
axiom cot_pi_25_45_bounds :
  ((cot_pi_25_45_lower : ℚ) : ℝ) ≤ cotangentTermV 25 45 ∧
  cotangentTermV 25 45 ≤ ((cot_pi_25_45_upper : ℚ) : ℝ)

def cot_pi_26_45_lower : ℚ := -8982988005580643 / 36028797018963968
def cot_pi_26_45_upper : ℚ := -8982988005580585 / 36028797018963968
axiom cot_pi_26_45_bounds :
  ((cot_pi_26_45_lower : ℚ) : ℝ) ≤ cotangentTermV 26 45 ∧
  cotangentTermV 26 45 ≤ ((cot_pi_26_45_upper : ℚ) : ℝ)

def cot_pi_27_45_lower : ℚ := -731654111439927 / 2251799813685248
def cot_pi_27_45_upper : ℚ := -731654111439923 / 2251799813685248
axiom cot_pi_27_45_bounds :
  ((cot_pi_27_45_lower : ℚ) : ℝ) ≤ cotangentTermV 27 45 ∧
  cotangentTermV 27 45 ≤ ((cot_pi_27_45_upper : ℚ) : ℝ)

def cot_pi_28_45_lower : ℚ := -7278289440476487 / 18014398509481984
def cot_pi_28_45_upper : ℚ := -7278289440476465 / 18014398509481984
axiom cot_pi_28_45_bounds :
  ((cot_pi_28_45_lower : ℚ) : ℝ) ≤ cotangentTermV 28 45 ∧
  cotangentTermV 28 45 ≤ ((cot_pi_28_45_upper : ℚ) : ℝ)

def cot_pi_29_45_lower : ℚ := -2196552304121665 / 4503599627370496
def cot_pi_29_45_upper : ℚ := -2196552304121653 / 4503599627370496
axiom cot_pi_29_45_bounds :
  ((cot_pi_29_45_lower : ℚ) : ℝ) ≤ cotangentTermV 29 45 ∧
  cotangentTermV 29 45 ≤ ((cot_pi_29_45_upper : ℚ) : ℝ)

def cot_pi_30_45_lower : ℚ := -5200308914369313 / 9007199254740992
def cot_pi_30_45_upper : ℚ := -5200308914369287 / 9007199254740992
axiom cot_pi_30_45_bounds :
  ((cot_pi_30_45_lower : ℚ) : ℝ) ≤ cotangentTermV 30 45 ∧
  cotangentTermV 30 45 ≤ ((cot_pi_30_45_upper : ℚ) : ℝ)

def cot_pi_31_45_lower : ℚ := -1518858152554891 / 2251799813685248
def cot_pi_31_45_upper : ℚ := -3037716305109767 / 4503599627370496
axiom cot_pi_31_45_bounds :
  ((cot_pi_31_45_lower : ℚ) : ℝ) ≤ cotangentTermV 31 45 ∧
  cotangentTermV 31 45 ≤ ((cot_pi_31_45_upper : ℚ) : ℝ)

def cot_pi_32_45_lower : ℚ := -3518597656405579 / 4503599627370496
def cot_pi_32_45_upper : ℚ := -3518597656405567 / 4503599627370496
axiom cot_pi_32_45_bounds :
  ((cot_pi_32_45_lower : ℚ) : ℝ) ≤ cotangentTermV 32 45 ∧
  cotangentTermV 32 45 ≤ ((cot_pi_32_45_upper : ℚ) : ℝ)

def cot_pi_33_45_lower : ℚ := -8110118636765291 / 9007199254740992
def cot_pi_33_45_upper : ℚ := -8110118636765253 / 9007199254740992
axiom cot_pi_33_45_bounds :
  ((cot_pi_33_45_lower : ℚ) : ℝ) ≤ cotangentTermV 33 45 ∧
  cotangentTermV 33 45 ≤ ((cot_pi_33_45_upper : ℚ) : ℝ)

def cot_pi_34_45_lower : ℚ := -4663613935318069 / 4503599627370496
def cot_pi_34_45_upper : ℚ := -4663613935318047 / 4503599627370496
axiom cot_pi_34_45_bounds :
  ((cot_pi_34_45_lower : ℚ) : ℝ) ≤ cotangentTermV 34 45 ∧
  cotangentTermV 34 45 ≤ ((cot_pi_34_45_upper : ℚ) : ℝ)

def cot_pi_35_45_lower : ℚ := -670897629440593 / 562949953421312
def cot_pi_35_45_upper : ℚ := -2683590517762359 / 2251799813685248
axiom cot_pi_35_45_bounds :
  ((cot_pi_35_45_lower : ℚ) : ℝ) ≤ cotangentTermV 35 45 ∧
  cotangentTermV 35 45 ≤ ((cot_pi_35_45_upper : ℚ) : ℝ)

def cot_pi_36_45_lower : ℚ := -6198673104153469 / 4503599627370496
def cot_pi_36_45_upper : ℚ := -6198673104153459 / 4503599627370496
axiom cot_pi_36_45_bounds :
  ((cot_pi_36_45_lower : ℚ) : ℝ) ≤ cotangentTermV 36 45 ∧
  cotangentTermV 36 45 ≤ ((cot_pi_36_45_upper : ℚ) : ℝ)

def cot_pi_37_45_lower : ℚ := -450454124291089 / 281474976710656
def cot_pi_37_45_upper : ℚ := -3603632994328693 / 2251799813685248
axiom cot_pi_37_45_bounds :
  ((cot_pi_37_45_lower : ℚ) : ℝ) ≤ cotangentTermV 37 45 ∧
  cotangentTermV 37 45 ≤ ((cot_pi_37_45_upper : ℚ) : ℝ)

def cot_pi_38_45_lower : ℚ := -4235019504259793 / 2251799813685248
def cot_pi_38_45_upper : ℚ := -2117509752129885 / 1125899906842624
axiom cot_pi_38_45_bounds :
  ((cot_pi_38_45_lower : ℚ) : ℝ) ≤ cotangentTermV 38 45 ∧
  cotangentTermV 38 45 ≤ ((cot_pi_38_45_upper : ℚ) : ℝ)

def cot_pi_39_45_lower : ℚ := -1264406297251935 / 562949953421312
def cot_pi_39_45_upper : ℚ := -2528812594503855 / 1125899906842624
axiom cot_pi_39_45_bounds :
  ((cot_pi_39_45_lower : ℚ) : ℝ) ≤ cotangentTermV 39 45 ∧
  cotangentTermV 39 45 ≤ ((cot_pi_39_45_upper : ℚ) : ℝ)

def cot_pi_40_45_lower : ℚ := -1546692285308089 / 562949953421312
def cot_pi_40_45_upper : ℚ := -3093384570616163 / 1125899906842624
axiom cot_pi_40_45_bounds :
  ((cot_pi_40_45_lower : ℚ) : ℝ) ≤ cotangentTermV 40 45 ∧
  cotangentTermV 40 45 ≤ ((cot_pi_40_45_upper : ℚ) : ℝ)

def cot_pi_41_45_lower : ℚ := -7852959194884227 / 2251799813685248
def cot_pi_41_45_upper : ℚ := -7852959194884143 / 2251799813685248
axiom cot_pi_41_45_bounds :
  ((cot_pi_41_45_lower : ℚ) : ℝ) ≤ cotangentTermV 41 45 ∧
  cotangentTermV 41 45 ≤ ((cot_pi_41_45_upper : ℚ) : ℝ)

def cot_pi_42_45_lower : ℚ := -5296942601990809 / 1125899906842624
def cot_pi_42_45_upper : ℚ := -5296942601990737 / 1125899906842624
axiom cot_pi_42_45_bounds :
  ((cot_pi_42_45_lower : ℚ) : ℝ) ≤ cotangentTermV 42 45 ∧
  cotangentTermV 42 45 ≤ ((cot_pi_42_45_upper : ℚ) : ℝ)

def cot_pi_43_45_lower : ℚ := -8011194107583269 / 1125899906842624
def cot_pi_43_45_upper : ℚ := -8011194107583111 / 1125899906842624
axiom cot_pi_43_45_bounds :
  ((cot_pi_43_45_lower : ℚ) : ℝ) ≤ cotangentTermV 43 45 ∧
  cotangentTermV 43 45 ≤ ((cot_pi_43_45_upper : ℚ) : ℝ)

def cot_pi_44_45_lower : ℚ := -4025279701554893 / 281474976710656
def cot_pi_44_45_upper : ℚ := -4025279701554739 / 281474976710656
axiom cot_pi_44_45_bounds :
  ((cot_pi_44_45_lower : ℚ) : ℝ) ≤ cotangentTermV 44 45 ∧
  cotangentTermV 44 45 ≤ ((cot_pi_44_45_upper : ℚ) : ℝ)

def cot_pi_1_46_lower : ℚ := 8230037002713485 / 562949953421312
def cot_pi_1_46_upper : ℚ := 8230037002713497 / 562949953421312
axiom cot_pi_1_46_bounds :
  ((cot_pi_1_46_lower : ℚ) : ℝ) ≤ cotangentTermV 1 46 ∧
  cotangentTermV 1 46 ≤ ((cot_pi_1_46_upper : ℚ) : ℝ)

def cot_pi_2_46_lower : ℚ := 8191530170975963 / 1125899906842624
def cot_pi_2_46_upper : ℚ := 8191530170975975 / 1125899906842624
axiom cot_pi_2_46_bounds :
  ((cot_pi_2_46_lower : ℚ) : ℝ) ≤ cotangentTermV 2 46 ∧
  cotangentTermV 2 46 ≤ ((cot_pi_2_46_upper : ℚ) : ℝ)

def cot_pi_3_46_lower : ℚ := 5418127813344329 / 1125899906842624
def cot_pi_3_46_upper : ℚ := 5418127813344337 / 1125899906842624
axiom cot_pi_3_46_bounds :
  ((cot_pi_3_46_lower : ℚ) : ℝ) ≤ cotangentTermV 3 46 ∧
  cotangentTermV 3 46 ≤ ((cot_pi_3_46_upper : ℚ) : ℝ)

def cot_pi_4_46_lower : ℚ := 8036778790736929 / 2251799813685248
def cot_pi_4_46_upper : ℚ := 8036778790736941 / 2251799813685248
axiom cot_pi_4_46_bounds :
  ((cot_pi_4_46_lower : ℚ) : ℝ) ≤ cotangentTermV 4 46 ∧
  cotangentTermV 4 46 ≤ ((cot_pi_4_46_upper : ℚ) : ℝ)

def cot_pi_5_46_lower : ℚ := 395997339744493 / 140737488355328
def cot_pi_5_46_upper : ℚ := 791994679488987 / 281474976710656
axiom cot_pi_5_46_bounds :
  ((cot_pi_5_46_lower : ℚ) : ℝ) ≤ cotangentTermV 5 46 ∧
  cotangentTermV 5 46 ≤ ((cot_pi_5_46_upper : ℚ) : ℝ)

def cot_pi_6_46_lower : ℚ := 5184163122237167 / 2251799813685248
def cot_pi_6_46_upper : ℚ := 5184163122237175 / 2251799813685248
axiom cot_pi_6_46_bounds :
  ((cot_pi_6_46_lower : ℚ) : ℝ) ≤ cotangentTermV 6 46 ∧
  cotangentTermV 6 46 ≤ ((cot_pi_6_46_upper : ℚ) : ℝ)

def cot_pi_7_46_lower : ℚ := 8691552738857353 / 4503599627370496
def cot_pi_7_46_upper : ℚ := 8691552738857363 / 4503599627370496
axiom cot_pi_7_46_bounds :
  ((cot_pi_7_46_lower : ℚ) : ℝ) ≤ cotangentTermV 7 46 ∧
  cotangentTermV 7 46 ≤ ((cot_pi_7_46_upper : ℚ) : ℝ)

def cot_pi_8_46_lower : ℚ := 7405854071649573 / 4503599627370496
def cot_pi_8_46_upper : ℚ := 7405854071649585 / 4503599627370496
axiom cot_pi_8_46_bounds :
  ((cot_pi_8_46_lower : ℚ) : ℝ) ≤ cotangentTermV 8 46 ∧
  cotangentTermV 8 46 ≤ ((cot_pi_8_46_upper : ℚ) : ℝ)

def cot_pi_9_46_lower : ℚ := 6380147136357235 / 4503599627370496
def cot_pi_9_46_upper : ℚ := 6380147136357245 / 4503599627370496
axiom cot_pi_9_46_bounds :
  ((cot_pi_9_46_lower : ℚ) : ℝ) ≤ cotangentTermV 9 46 ∧
  cotangentTermV 9 46 ≤ ((cot_pi_9_46_upper : ℚ) : ℝ)

def cot_pi_10_46_lower : ℚ := 5535667589870151 / 4503599627370496
def cot_pi_10_46_upper : ℚ := 5535667589870161 / 4503599627370496
axiom cot_pi_10_46_bounds :
  ((cot_pi_10_46_lower : ℚ) : ℝ) ≤ cotangentTermV 10 46 ∧
  cotangentTermV 10 46 ≤ ((cot_pi_10_46_upper : ℚ) : ℝ)

def cot_pi_11_46_lower : ℚ := 1205544436024055 / 1125899906842624
def cot_pi_11_46_upper : ℚ := 602772218012029 / 562949953421312
axiom cot_pi_11_46_bounds :
  ((cot_pi_11_46_lower : ℚ) : ℝ) ≤ cotangentTermV 11 46 ∧
  cotangentTermV 11 46 ≤ ((cot_pi_11_46_upper : ℚ) : ℝ)

def cot_pi_12_46_lower : ℚ := 8412136872591781 / 9007199254740992
def cot_pi_12_46_upper : ℚ := 8412136872591795 / 9007199254740992
axiom cot_pi_12_46_bounds :
  ((cot_pi_12_46_lower : ℚ) : ℝ) ≤ cotangentTermV 12 46 ∧
  cotangentTermV 12 46 ≤ ((cot_pi_12_46_upper : ℚ) : ℝ)

def cot_pi_13_46_lower : ℚ := 3663950061012857 / 4503599627370496
def cot_pi_13_46_upper : ℚ := 3663950061012865 / 4503599627370496
axiom cot_pi_13_46_bounds :
  ((cot_pi_13_46_lower : ℚ) : ℝ) ≤ cotangentTermV 13 46 ∧
  cotangentTermV 13 46 ≤ ((cot_pi_13_46_upper : ℚ) : ℝ)

def cot_pi_14_46_lower : ℚ := 6357975504380591 / 9007199254740992
def cot_pi_14_46_upper : ℚ := 6357975504380603 / 9007199254740992
axiom cot_pi_14_46_bounds :
  ((cot_pi_14_46_lower : ℚ) : ℝ) ≤ cotangentTermV 14 46 ∧
  cotangentTermV 14 46 ≤ ((cot_pi_14_46_upper : ℚ) : ℝ)

def cot_pi_15_46_lower : ℚ := 2738699602696053 / 4503599627370496
def cot_pi_15_46_upper : ℚ := 1369349801348031 / 2251799813685248
axiom cot_pi_15_46_bounds :
  ((cot_pi_15_46_lower : ℚ) : ℝ) ≤ cotangentTermV 15 46 ∧
  cotangentTermV 15 46 ≤ ((cot_pi_15_46_upper : ℚ) : ℝ)

def cot_pi_16_46_lower : ℚ := 4667154468953517 / 9007199254740992
def cot_pi_16_46_upper : ℚ := 4667154468953529 / 9007199254740992
axiom cot_pi_16_46_bounds :
  ((cot_pi_16_46_lower : ℚ) : ℝ) ≤ cotangentTermV 16 46 ∧
  cotangentTermV 16 46 ≤ ((cot_pi_16_46_upper : ℚ) : ℝ)

def cot_pi_17_46_lower : ℚ := 1956189371882553 / 4503599627370496
def cot_pi_17_46_upper : ℚ := 3912378743765119 / 9007199254740992
axiom cot_pi_17_46_bounds :
  ((cot_pi_17_46_lower : ℚ) : ℝ) ≤ cotangentTermV 17 46 ∧
  cotangentTermV 17 46 ≤ ((cot_pi_17_46_upper : ℚ) : ℝ)

def cot_pi_18_46_lower : ℚ := 3201159384166939 / 9007199254740992
def cot_pi_18_46_upper : ℚ := 800289846041737 / 2251799813685248
axiom cot_pi_18_46_bounds :
  ((cot_pi_18_46_lower : ℚ) : ℝ) ≤ cotangentTermV 18 46 ∧
  cotangentTermV 18 46 ≤ ((cot_pi_18_46_upper : ℚ) : ℝ)

def cot_pi_19_46_lower : ℚ := 5047397752698835 / 18014398509481984
def cot_pi_19_46_upper : ℚ := 5047397752698859 / 18014398509481984
axiom cot_pi_19_46_bounds :
  ((cot_pi_19_46_lower : ℚ) : ℝ) ≤ cotangentTermV 19 46 ∧
  cotangentTermV 19 46 ≤ ((cot_pi_19_46_upper : ℚ) : ℝ)

def cot_pi_20_46_lower : ℚ := 1871717528857293 / 9007199254740992
def cot_pi_20_46_upper : ℚ := 3743435057714601 / 18014398509481984
axiom cot_pi_20_46_bounds :
  ((cot_pi_20_46_lower : ℚ) : ℝ) ≤ cotangentTermV 20 46 ∧
  cotangentTermV 20 46 ≤ ((cot_pi_20_46_upper : ℚ) : ℝ)

def cot_pi_21_46_lower : ℚ := 4952044167649109 / 36028797018963968
def cot_pi_21_46_upper : ℚ := 4952044167649161 / 36028797018963968
axiom cot_pi_21_46_bounds :
  ((cot_pi_21_46_lower : ℚ) : ℝ) ≤ cotangentTermV 21 46 ∧
  cotangentTermV 21 46 ≤ ((cot_pi_21_46_upper : ℚ) : ℝ)

def cot_pi_22_46_lower : ℚ := 4928874462402615 / 72057594037927936
def cot_pi_22_46_upper : ℚ := 4928874462402713 / 72057594037927936
axiom cot_pi_22_46_bounds :
  ((cot_pi_22_46_lower : ℚ) : ℝ) ≤ cotangentTermV 22 46 ∧
  cotangentTermV 22 46 ≤ ((cot_pi_22_46_upper : ℚ) : ℝ)

def cot_pi_23_46_lower : ℚ := -217244719 / 604462909807314587353088
def cot_pi_23_46_upper : ℚ := 559670321 / 604462909807314587353088
axiom cot_pi_23_46_bounds :
  ((cot_pi_23_46_lower : ℚ) : ℝ) ≤ cotangentTermV 23 46 ∧
  cotangentTermV 23 46 ≤ ((cot_pi_23_46_upper : ℚ) : ℝ)

def cot_pi_24_46_lower : ℚ := -2464437231201333 / 36028797018963968
def cot_pi_24_46_upper : ℚ := -1232218615600653 / 18014398509481984
axiom cot_pi_24_46_bounds :
  ((cot_pi_24_46_lower : ℚ) : ℝ) ≤ cotangentTermV 24 46 ∧
  cotangentTermV 24 46 ≤ ((cot_pi_24_46_upper : ℚ) : ℝ)

def cot_pi_25_46_lower : ℚ := -4952044167649133 / 36028797018963968
def cot_pi_25_46_upper : ℚ := -4952044167649079 / 36028797018963968
axiom cot_pi_25_46_bounds :
  ((cot_pi_25_46_lower : ℚ) : ℝ) ≤ cotangentTermV 25 46 ∧
  cotangentTermV 25 46 ≤ ((cot_pi_25_46_upper : ℚ) : ℝ)

def cot_pi_26_46_lower : ℚ := -3743435057714597 / 18014398509481984
def cot_pi_26_46_upper : ℚ := -3743435057714569 / 18014398509481984
axiom cot_pi_26_46_bounds :
  ((cot_pi_26_46_lower : ℚ) : ℝ) ≤ cotangentTermV 26 46 ∧
  cotangentTermV 26 46 ≤ ((cot_pi_26_46_upper : ℚ) : ℝ)

def cot_pi_27_46_lower : ℚ := -630924719087357 / 2251799813685248
def cot_pi_27_46_upper : ℚ := -630924719087353 / 2251799813685248
axiom cot_pi_27_46_bounds :
  ((cot_pi_27_46_lower : ℚ) : ℝ) ≤ cotangentTermV 27 46 ∧
  cotangentTermV 27 46 ≤ ((cot_pi_27_46_upper : ℚ) : ℝ)

def cot_pi_28_46_lower : ℚ := -6402318768333891 / 18014398509481984
def cot_pi_28_46_upper : ℚ := -6402318768333871 / 18014398509481984
axiom cot_pi_28_46_bounds :
  ((cot_pi_28_46_lower : ℚ) : ℝ) ≤ cotangentTermV 28 46 ∧
  cotangentTermV 28 46 ≤ ((cot_pi_28_46_upper : ℚ) : ℝ)

def cot_pi_29_46_lower : ℚ := -3912378743765113 / 9007199254740992
def cot_pi_29_46_upper : ℚ := -3912378743765095 / 9007199254740992
axiom cot_pi_29_46_bounds :
  ((cot_pi_29_46_lower : ℚ) : ℝ) ≤ cotangentTermV 29 46 ∧
  cotangentTermV 29 46 ≤ ((cot_pi_29_46_upper : ℚ) : ℝ)

def cot_pi_30_46_lower : ℚ := -4667154468953529 / 9007199254740992
def cot_pi_30_46_upper : ℚ := -4667154468953503 / 9007199254740992
axiom cot_pi_30_46_bounds :
  ((cot_pi_30_46_lower : ℚ) : ℝ) ≤ cotangentTermV 30 46 ∧
  cotangentTermV 30 46 ≤ ((cot_pi_30_46_upper : ℚ) : ℝ)

def cot_pi_31_46_lower : ℚ := -5477399205392121 / 9007199254740992
def cot_pi_31_46_upper : ℚ := -5477399205392093 / 9007199254740992
axiom cot_pi_31_46_bounds :
  ((cot_pi_31_46_lower : ℚ) : ℝ) ≤ cotangentTermV 31 46 ∧
  cotangentTermV 31 46 ≤ ((cot_pi_31_46_upper : ℚ) : ℝ)

def cot_pi_32_46_lower : ℚ := -6357975504380605 / 9007199254740992
def cot_pi_32_46_upper : ℚ := -6357975504380583 / 9007199254740992
axiom cot_pi_32_46_bounds :
  ((cot_pi_32_46_lower : ℚ) : ℝ) ≤ cotangentTermV 32 46 ∧
  cotangentTermV 32 46 ≤ ((cot_pi_32_46_upper : ℚ) : ℝ)

def cot_pi_33_46_lower : ℚ := -7327900122025731 / 9007199254740992
def cot_pi_33_46_upper : ℚ := -7327900122025697 / 9007199254740992
axiom cot_pi_33_46_bounds :
  ((cot_pi_33_46_lower : ℚ) : ℝ) ≤ cotangentTermV 33 46 ∧
  cotangentTermV 33 46 ≤ ((cot_pi_33_46_upper : ℚ) : ℝ)

def cot_pi_34_46_lower : ℚ := -2103034218147949 / 2251799813685248
def cot_pi_34_46_upper : ℚ := -4206068436295879 / 4503599627370496
axiom cot_pi_34_46_bounds :
  ((cot_pi_34_46_lower : ℚ) : ℝ) ≤ cotangentTermV 34 46 ∧
  cotangentTermV 34 46 ≤ ((cot_pi_34_46_upper : ℚ) : ℝ)

def cot_pi_35_46_lower : ℚ := -602772218012029 / 562949953421312
def cot_pi_35_46_upper : ℚ := -301386109006013 / 281474976710656
axiom cot_pi_35_46_bounds :
  ((cot_pi_35_46_lower : ℚ) : ℝ) ≤ cotangentTermV 35 46 ∧
  cotangentTermV 35 46 ≤ ((cot_pi_35_46_upper : ℚ) : ℝ)

def cot_pi_36_46_lower : ℚ := -2767833794935081 / 2251799813685248
def cot_pi_36_46_upper : ℚ := -2767833794935071 / 2251799813685248
axiom cot_pi_36_46_bounds :
  ((cot_pi_36_46_lower : ℚ) : ℝ) ≤ cotangentTermV 36 46 ∧
  cotangentTermV 36 46 ≤ ((cot_pi_36_46_upper : ℚ) : ℝ)

def cot_pi_37_46_lower : ℚ := -6380147136357249 / 4503599627370496
def cot_pi_37_46_upper : ℚ := -6380147136357217 / 4503599627370496
axiom cot_pi_37_46_bounds :
  ((cot_pi_37_46_lower : ℚ) : ℝ) ≤ cotangentTermV 37 46 ∧
  cotangentTermV 37 46 ≤ ((cot_pi_37_46_upper : ℚ) : ℝ)

def cot_pi_38_46_lower : ℚ := -925731758956199 / 562949953421312
def cot_pi_38_46_upper : ℚ := -3702927035824777 / 2251799813685248
axiom cot_pi_38_46_bounds :
  ((cot_pi_38_46_lower : ℚ) : ℝ) ≤ cotangentTermV 38 46 ∧
  cotangentTermV 38 46 ≤ ((cot_pi_38_46_upper : ℚ) : ℝ)

def cot_pi_39_46_lower : ℚ := -8691552738857367 / 4503599627370496
def cot_pi_39_46_upper : ℚ := -8691552738857321 / 4503599627370496
axiom cot_pi_39_46_bounds :
  ((cot_pi_39_46_lower : ℚ) : ℝ) ≤ cotangentTermV 39 46 ∧
  cotangentTermV 39 46 ≤ ((cot_pi_39_46_upper : ℚ) : ℝ)

def cot_pi_40_46_lower : ℚ := -5184163122237177 / 2251799813685248
def cot_pi_40_46_upper : ℚ := -5184163122237153 / 2251799813685248
axiom cot_pi_40_46_bounds :
  ((cot_pi_40_46_lower : ℚ) : ℝ) ≤ cotangentTermV 40 46 ∧
  cotangentTermV 40 46 ≤ ((cot_pi_40_46_upper : ℚ) : ℝ)

def cot_pi_41_46_lower : ℚ := -3167978717955953 / 1125899906842624
def cot_pi_41_46_upper : ℚ := -3167978717955925 / 1125899906842624
axiom cot_pi_41_46_bounds :
  ((cot_pi_41_46_lower : ℚ) : ℝ) ≤ cotangentTermV 41 46 ∧
  cotangentTermV 41 46 ≤ ((cot_pi_41_46_upper : ℚ) : ℝ)

def cot_pi_42_46_lower : ℚ := -8036778790736949 / 2251799813685248
def cot_pi_42_46_upper : ℚ := -8036778790736863 / 2251799813685248
axiom cot_pi_42_46_bounds :
  ((cot_pi_42_46_lower : ℚ) : ℝ) ≤ cotangentTermV 42 46 ∧
  cotangentTermV 42 46 ≤ ((cot_pi_42_46_upper : ℚ) : ℝ)

def cot_pi_43_46_lower : ℚ := -5418127813344363 / 1125899906842624
def cot_pi_43_46_upper : ℚ := -5418127813344289 / 1125899906842624
axiom cot_pi_43_46_bounds :
  ((cot_pi_43_46_lower : ℚ) : ℝ) ≤ cotangentTermV 43 46 ∧
  cotangentTermV 43 46 ≤ ((cot_pi_43_46_upper : ℚ) : ℝ)

def cot_pi_44_46_lower : ℚ := -8191530170976021 / 1125899906842624
def cot_pi_44_46_upper : ℚ := -8191530170975857 / 1125899906842624
axiom cot_pi_44_46_bounds :
  ((cot_pi_44_46_lower : ℚ) : ℝ) ≤ cotangentTermV 44 46 ∧
  cotangentTermV 44 46 ≤ ((cot_pi_44_46_upper : ℚ) : ℝ)

def cot_pi_45_46_lower : ℚ := -8230037002713557 / 562949953421312
def cot_pi_45_46_upper : ℚ := -8230037002713239 / 562949953421312
axiom cot_pi_45_46_bounds :
  ((cot_pi_45_46_lower : ℚ) : ℝ) ≤ cotangentTermV 45 46 ∧
  cotangentTermV 45 46 ≤ ((cot_pi_45_46_upper : ℚ) : ℝ)

def cot_pi_1_47_lower : ℚ := 8409502460849687 / 562949953421312
def cot_pi_1_47_upper : ℚ := 8409502460849699 / 562949953421312
axiom cot_pi_1_47_bounds :
  ((cot_pi_1_47_lower : ℚ) : ℝ) ≤ cotangentTermV 1 47 ∧
  cotangentTermV 1 47 ≤ ((cot_pi_1_47_upper : ℚ) : ℝ)

def cot_pi_2_47_lower : ℚ := 261619293608403 / 35184372088832
def cot_pi_2_47_upper : ℚ := 2092954348867227 / 281474976710656
axiom cot_pi_2_47_bounds :
  ((cot_pi_2_47_lower : ℚ) : ℝ) ≤ cotangentTermV 2 47 ∧
  cotangentTermV 2 47 ≤ ((cot_pi_2_47_upper : ℚ) : ℝ)

def cot_pi_3_47_lower : ℚ := 346202442353957 / 70368744177664
def cot_pi_3_47_upper : ℚ := 692404884707915 / 140737488355328
axiom cot_pi_3_47_bounds :
  ((cot_pi_3_47_lower : ℚ) : ℝ) ≤ cotangentTermV 3 47 ∧
  cotangentTermV 3 47 ≤ ((cot_pi_3_47_upper : ℚ) : ℝ)

def cot_pi_4_47_lower : ℚ := 256887455897923 / 70368744177664
def cot_pi_4_47_upper : ℚ := 2055099647183387 / 562949953421312
axiom cot_pi_4_47_bounds :
  ((cot_pi_4_47_lower : ℚ) : ℝ) ≤ cotangentTermV 4 47 ∧
  cotangentTermV 4 47 ≤ ((cot_pi_4_47_upper : ℚ) : ℝ)

def cot_pi_5_47_lower : ℚ := 1621222929938209 / 562949953421312
def cot_pi_5_47_upper : ℚ := 3242445859876423 / 1125899906842624
axiom cot_pi_5_47_bounds :
  ((cot_pi_5_47_lower : ℚ) : ℝ) ≤ cotangentTermV 5 47 ∧
  cotangentTermV 5 47 ≤ ((cot_pi_5_47_upper : ℚ) : ℝ)

def cot_pi_6_47_lower : ℚ := 5310389847208545 / 2251799813685248
def cot_pi_6_47_upper : ℚ := 5310389847208553 / 2251799813685248
axiom cot_pi_6_47_bounds :
  ((cot_pi_6_47_lower : ℚ) : ℝ) ≤ cotangentTermV 6 47 ∧
  cotangentTermV 6 47 ≤ ((cot_pi_6_47_upper : ℚ) : ℝ)

def cot_pi_7_47_lower : ℚ := 8912322197085203 / 4503599627370496
def cot_pi_7_47_upper : ℚ := 8912322197085213 / 4503599627370496
axiom cot_pi_7_47_bounds :
  ((cot_pi_7_47_lower : ℚ) : ℝ) ≤ cotangentTermV 7 47 ∧
  cotangentTermV 7 47 ≤ ((cot_pi_7_47_upper : ℚ) : ℝ)

def cot_pi_8_47_lower : ℚ := 7603566893022037 / 4503599627370496
def cot_pi_8_47_upper : ℚ := 7603566893022049 / 4503599627370496
axiom cot_pi_8_47_bounds :
  ((cot_pi_8_47_lower : ℚ) : ℝ) ≤ cotangentTermV 8 47 ∧
  cotangentTermV 8 47 ≤ ((cot_pi_8_47_upper : ℚ) : ℝ)

def cot_pi_9_47_lower : ℚ := 3280301940886895 / 2251799813685248
def cot_pi_9_47_upper : ℚ := 820075485221725 / 562949953421312
axiom cot_pi_9_47_bounds :
  ((cot_pi_9_47_lower : ℚ) : ℝ) ≤ cotangentTermV 9 47 ∧
  cotangentTermV 9 47 ≤ ((cot_pi_9_47_upper : ℚ) : ℝ)

def cot_pi_10_47_lower : ℚ := 5702981609292861 / 4503599627370496
def cot_pi_10_47_upper : ℚ := 5702981609292871 / 4503599627370496
axiom cot_pi_10_47_bounds :
  ((cot_pi_10_47_lower : ℚ) : ℝ) ≤ cotangentTermV 10 47 ∧
  cotangentTermV 10 47 ≤ ((cot_pi_10_47_upper : ℚ) : ℝ)

def cot_pi_11_47_lower : ℚ := 622424750549523 / 562949953421312
def cot_pi_11_47_upper : ℚ := 1244849501099049 / 1125899906842624
axiom cot_pi_11_47_bounds :
  ((cot_pi_11_47_lower : ℚ) : ℝ) ≤ cotangentTermV 11 47 ∧
  cotangentTermV 11 47 ≤ ((cot_pi_11_47_upper : ℚ) : ℝ)

def cot_pi_12_47_lower : ℚ := 34027689400391 / 35184372088832
def cot_pi_12_47_upper : ℚ := 4355544243250055 / 4503599627370496
axiom cot_pi_12_47_bounds :
  ((cot_pi_12_47_lower : ℚ) : ℝ) ≤ cotangentTermV 12 47 ∧
  cotangentTermV 12 47 ≤ ((cot_pi_12_47_upper : ℚ) : ℝ)

def cot_pi_13_47_lower : ℚ := 7615114223062449 / 9007199254740992
def cot_pi_13_47_upper : ℚ := 7615114223062463 / 9007199254740992
axiom cot_pi_13_47_bounds :
  ((cot_pi_13_47_lower : ℚ) : ℝ) ≤ cotangentTermV 13 47 ∧
  cotangentTermV 13 47 ≤ ((cot_pi_13_47_upper : ℚ) : ℝ)

def cot_pi_14_47_lower : ℚ := 6636550613077043 / 9007199254740992
def cot_pi_14_47_upper : ℚ := 6636550613077055 / 9007199254740992
axiom cot_pi_14_47_bounds :
  ((cot_pi_14_47_lower : ℚ) : ℝ) ≤ cotangentTermV 14 47 ∧
  cotangentTermV 14 47 ≤ ((cot_pi_14_47_upper : ℚ) : ℝ)

def cot_pi_15_47_lower : ℚ := 5749981503871007 / 9007199254740992
def cot_pi_15_47_upper : ℚ := 5749981503871025 / 9007199254740992
axiom cot_pi_15_47_bounds :
  ((cot_pi_15_47_lower : ℚ) : ℝ) ≤ cotangentTermV 15 47 ∧
  cotangentTermV 15 47 ≤ ((cot_pi_15_47_upper : ℚ) : ℝ)

def cot_pi_16_47_lower : ℚ := 4936080713310083 / 9007199254740992
def cot_pi_16_47_upper : ℚ := 4936080713310095 / 9007199254740992
axiom cot_pi_16_47_bounds :
  ((cot_pi_16_47_lower : ℚ) : ℝ) ≤ cotangentTermV 16 47 ∧
  cotangentTermV 16 47 ≤ ((cot_pi_16_47_upper : ℚ) : ℝ)

def cot_pi_17_47_lower : ℚ := 8359566215541367 / 18014398509481984
def cot_pi_17_47_upper : ℚ := 8359566215541393 / 18014398509481984
axiom cot_pi_17_47_bounds :
  ((cot_pi_17_47_lower : ℚ) : ℝ) ≤ cotangentTermV 17 47 ∧
  cotangentTermV 17 47 ≤ ((cot_pi_17_47_upper : ℚ) : ℝ)

def cot_pi_18_47_lower : ℚ := 3469057742248613 / 9007199254740992
def cot_pi_18_47_upper : ℚ := 1734528871124311 / 4503599627370496
axiom cot_pi_18_47_bounds :
  ((cot_pi_18_47_lower : ℚ) : ℝ) ≤ cotangentTermV 18 47 ∧
  cotangentTermV 18 47 ≤ ((cot_pi_18_47_upper : ℚ) : ℝ)

def cot_pi_19_47_lower : ℚ := 5588118969754733 / 18014398509481984
def cot_pi_19_47_upper : ℚ := 5588118969754757 / 18014398509481984
axiom cot_pi_19_47_bounds :
  ((cot_pi_19_47_lower : ℚ) : ℝ) ≤ cotangentTermV 19 47 ∧
  cotangentTermV 19 47 ≤ ((cot_pi_19_47_upper : ℚ) : ℝ)

def cot_pi_20_47_lower : ℚ := 8586097919259351 / 36028797018963968
def cot_pi_20_47_upper : ℚ := 8586097919259381 / 36028797018963968
axiom cot_pi_20_47_bounds :
  ((cot_pi_20_47_lower : ℚ) : ℝ) ≤ cotangentTermV 20 47 ∧
  cotangentTermV 20 47 ≤ ((cot_pi_20_47_upper : ℚ) : ℝ)

def cot_pi_21_47_lower : ℚ := 759662728178121 / 4503599627370496
def cot_pi_21_47_upper : ℚ := 1519325456356255 / 9007199254740992
axiom cot_pi_21_47_bounds :
  ((cot_pi_21_47_lower : ℚ) : ℝ) ≤ cotangentTermV 21 47 ∧
  cotangentTermV 21 47 ≤ ((cot_pi_21_47_upper : ℚ) : ℝ)

def cot_pi_22_47_lower : ℚ := 7249060835947689 / 72057594037927936
def cot_pi_22_47_upper : ℚ := 7249060835947787 / 72057594037927936
axiom cot_pi_22_47_bounds :
  ((cot_pi_22_47_lower : ℚ) : ℝ) ≤ cotangentTermV 22 47 ∧
  cotangentTermV 22 47 ≤ ((cot_pi_22_47_upper : ℚ) : ℝ)

def cot_pi_23_47_lower : ℚ := 1204574101870923 / 36028797018963968
def cot_pi_23_47_upper : ℚ := 602287050935485 / 18014398509481984
axiom cot_pi_23_47_bounds :
  ((cot_pi_23_47_lower : ℚ) : ℝ) ≤ cotangentTermV 23 47 ∧
  cotangentTermV 23 47 ≤ ((cot_pi_23_47_upper : ℚ) : ℝ)

def cot_pi_24_47_lower : ℚ := -2409148203741877 / 72057594037927936
def cot_pi_24_47_upper : ℚ := -1204574101870913 / 36028797018963968
axiom cot_pi_24_47_bounds :
  ((cot_pi_24_47_lower : ℚ) : ℝ) ≤ cotangentTermV 24 47 ∧
  cotangentTermV 24 47 ≤ ((cot_pi_24_47_upper : ℚ) : ℝ)

def cot_pi_25_47_lower : ℚ := -3624530417973865 / 36028797018963968
def cot_pi_25_47_upper : ℚ := -3624530417973815 / 36028797018963968
axiom cot_pi_25_47_bounds :
  ((cot_pi_25_47_lower : ℚ) : ℝ) ≤ cotangentTermV 25 47 ∧
  cotangentTermV 25 47 ≤ ((cot_pi_25_47_upper : ℚ) : ℝ)

def cot_pi_26_47_lower : ℚ := -189915682044531 / 1125899906842624
def cot_pi_26_47_upper : ℚ := -3038650912712477 / 18014398509481984
axiom cot_pi_26_47_bounds :
  ((cot_pi_26_47_lower : ℚ) : ℝ) ≤ cotangentTermV 26 47 ∧
  cotangentTermV 26 47 ≤ ((cot_pi_26_47_upper : ℚ) : ℝ)

def cot_pi_27_47_lower : ℚ := -2146524479814845 / 9007199254740992
def cot_pi_27_47_upper : ℚ := -2146524479814831 / 9007199254740992
axiom cot_pi_27_47_bounds :
  ((cot_pi_27_47_lower : ℚ) : ℝ) ≤ cotangentTermV 27 47 ∧
  cotangentTermV 27 47 ≤ ((cot_pi_27_47_upper : ℚ) : ℝ)

def cot_pi_28_47_lower : ℚ := -5588118969754749 / 18014398509481984
def cot_pi_28_47_upper : ℚ := -5588118969754729 / 18014398509481984
axiom cot_pi_28_47_bounds :
  ((cot_pi_28_47_lower : ℚ) : ℝ) ≤ cotangentTermV 28 47 ∧
  cotangentTermV 28 47 ≤ ((cot_pi_28_47_upper : ℚ) : ℝ)

def cot_pi_29_47_lower : ℚ := -867264435562155 / 2251799813685248
def cot_pi_29_47_upper : ℚ := -3469057742248603 / 9007199254740992
axiom cot_pi_29_47_bounds :
  ((cot_pi_29_47_lower : ℚ) : ℝ) ≤ cotangentTermV 29 47 ∧
  cotangentTermV 29 47 ≤ ((cot_pi_29_47_upper : ℚ) : ℝ)

def cot_pi_30_47_lower : ℚ := -8359566215541385 / 18014398509481984
def cot_pi_30_47_upper : ℚ := -8359566215541339 / 18014398509481984
axiom cot_pi_30_47_bounds :
  ((cot_pi_30_47_lower : ℚ) : ℝ) ≤ cotangentTermV 30 47 ∧
  cotangentTermV 30 47 ≤ ((cot_pi_30_47_upper : ℚ) : ℝ)

def cot_pi_31_47_lower : ℚ := -1234020178327523 / 2251799813685248
def cot_pi_31_47_upper : ℚ := -2468040356655033 / 4503599627370496
axiom cot_pi_31_47_bounds :
  ((cot_pi_31_47_lower : ℚ) : ℝ) ≤ cotangentTermV 31 47 ∧
  cotangentTermV 31 47 ≤ ((cot_pi_31_47_upper : ℚ) : ℝ)

def cot_pi_32_47_lower : ℚ := -2874990751935509 / 4503599627370496
def cot_pi_32_47_upper : ℚ := -1437495375967749 / 2251799813685248
axiom cot_pi_32_47_bounds :
  ((cot_pi_32_47_lower : ℚ) : ℝ) ≤ cotangentTermV 32 47 ∧
  cotangentTermV 32 47 ≤ ((cot_pi_32_47_upper : ℚ) : ℝ)

def cot_pi_33_47_lower : ℚ := -6636550613077057 / 9007199254740992
def cot_pi_33_47_upper : ℚ := -6636550613077025 / 9007199254740992
axiom cot_pi_33_47_bounds :
  ((cot_pi_33_47_lower : ℚ) : ℝ) ≤ cotangentTermV 33 47 ∧
  cotangentTermV 33 47 ≤ ((cot_pi_33_47_upper : ℚ) : ℝ)

def cot_pi_34_47_lower : ℚ := -118986159735351 / 140737488355328
def cot_pi_34_47_upper : ℚ := -1903778555765607 / 2251799813685248
axiom cot_pi_34_47_bounds :
  ((cot_pi_34_47_lower : ℚ) : ℝ) ≤ cotangentTermV 34 47 ∧
  cotangentTermV 34 47 ≤ ((cot_pi_34_47_upper : ℚ) : ℝ)

def cot_pi_35_47_lower : ℚ := -544443030406257 / 562949953421312
def cot_pi_35_47_upper : ℚ := -1088886060812509 / 1125899906842624
axiom cot_pi_35_47_bounds :
  ((cot_pi_35_47_lower : ℚ) : ℝ) ≤ cotangentTermV 35 47 ∧
  cotangentTermV 35 47 ≤ ((cot_pi_35_47_upper : ℚ) : ℝ)

def cot_pi_36_47_lower : ℚ := -2489699002198097 / 2251799813685248
def cot_pi_36_47_upper : ℚ := -311212375274761 / 281474976710656
axiom cot_pi_36_47_bounds :
  ((cot_pi_36_47_lower : ℚ) : ℝ) ≤ cotangentTermV 36 47 ∧
  cotangentTermV 36 47 ≤ ((cot_pi_36_47_upper : ℚ) : ℝ)

def cot_pi_37_47_lower : ℚ := -5702981609292875 / 4503599627370496
def cot_pi_37_47_upper : ℚ := -5702981609292847 / 4503599627370496
axiom cot_pi_37_47_bounds :
  ((cot_pi_37_47_lower : ℚ) : ℝ) ≤ cotangentTermV 37 47 ∧
  cotangentTermV 37 47 ≤ ((cot_pi_37_47_upper : ℚ) : ℝ)

def cot_pi_38_47_lower : ℚ := -1640150970443451 / 1125899906842624
def cot_pi_38_47_upper : ℚ := -1640150970443443 / 1125899906842624
axiom cot_pi_38_47_bounds :
  ((cot_pi_38_47_lower : ℚ) : ℝ) ≤ cotangentTermV 38 47 ∧
  cotangentTermV 38 47 ≤ ((cot_pi_38_47_upper : ℚ) : ℝ)

def cot_pi_39_47_lower : ℚ := -950445861627757 / 562949953421312
def cot_pi_39_47_upper : ℚ := -118805732703469 / 70368744177664
axiom cot_pi_39_47_bounds :
  ((cot_pi_39_47_lower : ℚ) : ℝ) ≤ cotangentTermV 39 47 ∧
  cotangentTermV 39 47 ≤ ((cot_pi_39_47_upper : ℚ) : ℝ)

def cot_pi_40_47_lower : ℚ := -8912322197085217 / 4503599627370496
def cot_pi_40_47_upper : ℚ := -8912322197085183 / 4503599627370496
axiom cot_pi_40_47_bounds :
  ((cot_pi_40_47_lower : ℚ) : ℝ) ≤ cotangentTermV 40 47 ∧
  cotangentTermV 40 47 ≤ ((cot_pi_40_47_upper : ℚ) : ℝ)

def cot_pi_41_47_lower : ℚ := -2655194923604279 / 1125899906842624
def cot_pi_41_47_upper : ℚ := -1327597461802129 / 562949953421312
axiom cot_pi_41_47_bounds :
  ((cot_pi_41_47_lower : ℚ) : ℝ) ≤ cotangentTermV 41 47 ∧
  cotangentTermV 41 47 ≤ ((cot_pi_41_47_upper : ℚ) : ℝ)

def cot_pi_42_47_lower : ℚ := -3242445859876427 / 1125899906842624
def cot_pi_42_47_upper : ℚ := -1621222929938199 / 562949953421312
axiom cot_pi_42_47_bounds :
  ((cot_pi_42_47_lower : ℚ) : ℝ) ≤ cotangentTermV 42 47 ∧
  cotangentTermV 42 47 ≤ ((cot_pi_42_47_upper : ℚ) : ℝ)

def cot_pi_43_47_lower : ℚ := -4110199294366789 / 1125899906842624
def cot_pi_43_47_upper : ℚ := -513774911795843 / 140737488355328
axiom cot_pi_43_47_bounds :
  ((cot_pi_43_47_lower : ℚ) : ℝ) ≤ cotangentTermV 43 47 ∧
  cotangentTermV 43 47 ≤ ((cot_pi_43_47_upper : ℚ) : ℝ)

def cot_pi_44_47_lower : ℚ := -5539239077663335 / 1125899906842624
def cot_pi_44_47_upper : ℚ := -5539239077663259 / 1125899906842624
axiom cot_pi_44_47_bounds :
  ((cot_pi_44_47_lower : ℚ) : ℝ) ≤ cotangentTermV 44 47 ∧
  cotangentTermV 44 47 ≤ ((cot_pi_44_47_upper : ℚ) : ℝ)

def cot_pi_45_47_lower : ℚ := -8371817395468917 / 1125899906842624
def cot_pi_45_47_upper : ℚ := -8371817395468749 / 1125899906842624
axiom cot_pi_45_47_bounds :
  ((cot_pi_45_47_lower : ℚ) : ℝ) ≤ cotangentTermV 45 47 ∧
  cotangentTermV 45 47 ≤ ((cot_pi_45_47_upper : ℚ) : ℝ)

def cot_pi_46_47_lower : ℚ := -4204751230424891 / 281474976710656
def cot_pi_46_47_upper : ℚ := -4204751230424727 / 281474976710656
axiom cot_pi_46_47_bounds :
  ((cot_pi_46_47_lower : ℚ) : ℝ) ≤ cotangentTermV 46 47 ∧
  cotangentTermV 46 47 ≤ ((cot_pi_46_47_upper : ℚ) : ℝ)

def cot_pi_1_48_lower : ℚ := 8588956537255631 / 562949953421312
def cot_pi_1_48_upper : ℚ := 8588956537255643 / 562949953421312
axiom cot_pi_1_48_bounds :
  ((cot_pi_1_48_lower : ℚ) : ℝ) ≤ cotangentTermV 1 48 ∧
  cotangentTermV 1 48 ≤ ((cot_pi_1_48_upper : ℚ) : ℝ)

def cot_pi_2_48_lower : ℚ := 8552058847916719 / 1125899906842624
def cot_pi_2_48_upper : ℚ := 8552058847916731 / 1125899906842624
axiom cot_pi_2_48_bounds :
  ((cot_pi_2_48_lower : ℚ) : ℝ) ≤ cotangentTermV 2 48 ∧
  cotangentTermV 2 48 ≤ ((cot_pi_2_48_upper : ℚ) : ℝ)

def cot_pi_3_48_lower : ℚ := 2830140532925367 / 562949953421312
def cot_pi_3_48_upper : ℚ := 1415070266462685 / 281474976710656
axiom cot_pi_3_48_bounds :
  ((cot_pi_3_48_lower : ℚ) : ℝ) ≤ cotangentTermV 3 48 ∧
  cotangentTermV 3 48 ≤ ((cot_pi_3_48_upper : ℚ) : ℝ)

def cot_pi_4_48_lower : ℚ := 8403831313147473 / 2251799813685248
def cot_pi_4_48_upper : ℚ := 8403831313147485 / 2251799813685248
axiom cot_pi_4_48_bounds :
  ((cot_pi_4_48_lower : ℚ) : ℝ) ≤ cotangentTermV 4 48 ∧
  cotangentTermV 4 48 ≤ ((cot_pi_4_48_upper : ℚ) : ℝ)

def cot_pi_5_48_lower : ℚ := 3316794170185319 / 1125899906842624
def cot_pi_5_48_upper : ℚ := 829198542546331 / 281474976710656
axiom cot_pi_5_48_bounds :
  ((cot_pi_5_48_lower : ℚ) : ℝ) ≤ cotangentTermV 5 48 ∧
  cotangentTermV 5 48 ≤ ((cot_pi_5_48_upper : ℚ) : ℝ)

def cot_pi_6_48_lower : ℚ := 5436325649948131 / 2251799813685248
def cot_pi_6_48_upper : ℚ := 5436325649948137 / 2251799813685248
axiom cot_pi_6_48_bounds :
  ((cot_pi_6_48_lower : ℚ) : ℝ) ≤ cotangentTermV 6 48 ∧
  cotangentTermV 6 48 ≤ ((cot_pi_6_48_upper : ℚ) : ℝ)

def cot_pi_7_48_lower : ℚ := 2283099157795195 / 1125899906842624
def cot_pi_7_48_upper : ℚ := 1141549578897599 / 562949953421312
axiom cot_pi_7_48_bounds :
  ((cot_pi_7_48_lower : ℚ) : ℝ) ≤ cotangentTermV 7 48 ∧
  cotangentTermV 7 48 ≤ ((cot_pi_7_48_upper : ℚ) : ℝ)

def cot_pi_8_48_lower : ℚ := 1950115842888489 / 1125899906842624
def cot_pi_8_48_upper : ℚ := 487528960722123 / 281474976710656
axiom cot_pi_8_48_bounds :
  ((cot_pi_8_48_lower : ℚ) : ℝ) ≤ cotangentTermV 8 48 ∧
  cotangentTermV 8 48 ≤ ((cot_pi_8_48_upper : ℚ) : ℝ)

def cot_pi_9_48_lower : ℚ := 6740113155060829 / 4503599627370496
def cot_pi_9_48_upper : ℚ := 6740113155060837 / 4503599627370496
axiom cot_pi_9_48_bounds :
  ((cot_pi_9_48_lower : ℚ) : ℝ) ≤ cotangentTermV 9 48 ∧
  cotangentTermV 9 48 ≤ ((cot_pi_9_48_upper : ℚ) : ℝ)

def cot_pi_10_48_lower : ℚ := 5869205303507425 / 4503599627370496
def cot_pi_10_48_upper : ℚ := 5869205303507435 / 4503599627370496
axiom cot_pi_10_48_bounds :
  ((cot_pi_10_48_lower : ℚ) : ℝ) ≤ cotangentTermV 10 48 ∧
  cotangentTermV 10 48 ≤ ((cot_pi_10_48_upper : ℚ) : ℝ)

def cot_pi_11_48_lower : ℚ := 5135371150100853 / 4503599627370496
def cot_pi_11_48_upper : ℚ := 5135371150100865 / 4503599627370496
axiom cot_pi_11_48_bounds :
  ((cot_pi_11_48_lower : ℚ) : ℝ) ≤ cotangentTermV 11 48 ∧
  cotangentTermV 11 48 ≤ ((cot_pi_11_48_upper : ℚ) : ℝ)

def cot_pi_12_48_lower : ℚ := 2251799813685247 / 2251799813685248
def cot_pi_12_48_upper : ℚ := 2251799813685249 / 2251799813685248
axiom cot_pi_12_48_bounds :
  ((cot_pi_12_48_lower : ℚ) : ℝ) ≤ cotangentTermV 12 48 ∧
  cotangentTermV 12 48 ≤ ((cot_pi_12_48_upper : ℚ) : ℝ)

def cot_pi_13_48_lower : ℚ := 493693858993359 / 562949953421312
def cot_pi_13_48_upper : ℚ := 3949550871946879 / 4503599627370496
axiom cot_pi_13_48_bounds :
  ((cot_pi_13_48_lower : ℚ) : ℝ) ≤ cotangentTermV 13 48 ∧
  cotangentTermV 13 48 ≤ ((cot_pi_13_48_upper : ℚ) : ℝ)

def cot_pi_14_48_lower : ℚ := 431966692141671 / 562949953421312
def cot_pi_14_48_upper : ℚ := 1727866768566687 / 2251799813685248
axiom cot_pi_14_48_bounds :
  ((cot_pi_14_48_lower : ℚ) : ℝ) ≤ cotangentTermV 14 48 ∧
  cotangentTermV 14 48 ≤ ((cot_pi_14_48_upper : ℚ) : ℝ)

def cot_pi_15_48_lower : ℚ := 3009209064750277 / 4503599627370496
def cot_pi_15_48_upper : ℚ := 752302266187571 / 1125899906842624
axiom cot_pi_15_48_bounds :
  ((cot_pi_15_48_lower : ℚ) : ℝ) ≤ cotangentTermV 15 48 ∧
  cotangentTermV 15 48 ≤ ((cot_pi_15_48_upper : ℚ) : ℝ)

def cot_pi_16_48_lower : ℚ := 5200308914369303 / 9007199254740992
def cot_pi_16_48_upper : ℚ := 5200308914369315 / 9007199254740992
axiom cot_pi_16_48_bounds :
  ((cot_pi_16_48_lower : ℚ) : ℝ) ≤ cotangentTermV 16 48 ∧
  cotangentTermV 16 48 ≤ ((cot_pi_16_48_upper : ℚ) : ℝ)

def cot_pi_17_48_lower : ℚ := 4441859113828087 / 9007199254740992
def cot_pi_17_48_upper : ℚ := 1110464778457025 / 2251799813685248
axiom cot_pi_17_48_bounds :
  ((cot_pi_17_48_lower : ℚ) : ℝ) ≤ cotangentTermV 17 48 ∧
  cotangentTermV 17 48 ≤ ((cot_pi_17_48_upper : ℚ) : ℝ)

def cot_pi_18_48_lower : ℚ := 7461808180621101 / 18014398509481984
def cot_pi_18_48_upper : ℚ := 7461808180621111 / 18014398509481984
axiom cot_pi_18_48_bounds :
  ((cot_pi_18_48_lower : ℚ) : ℝ) ≤ cotangentTermV 18 48 ∧
  cotangentTermV 18 48 ≤ ((cot_pi_18_48_upper : ℚ) : ℝ)

def cot_pi_19_48_lower : ℚ := 3057532147452851 / 9007199254740992
def cot_pi_19_48_upper : ℚ := 3057532147452859 / 9007199254740992
axiom cot_pi_19_48_bounds :
  ((cot_pi_19_48_lower : ℚ) : ℝ) ≤ cotangentTermV 19 48 ∧
  cotangentTermV 19 48 ≤ ((cot_pi_19_48_upper : ℚ) : ℝ)

def cot_pi_20_48_lower : ℚ := 301683970796757 / 1125899906842624
def cot_pi_20_48_upper : ℚ := 2413471766374065 / 9007199254740992
axiom cot_pi_20_48_bounds :
  ((cot_pi_20_48_lower : ℚ) : ℝ) ≤ cotangentTermV 20 48 ∧
  cotangentTermV 20 48 ≤ ((cot_pi_20_48_upper : ℚ) : ℝ)

def cot_pi_21_48_lower : ℚ := 447910831805205 / 2251799813685248
def cot_pi_21_48_upper : ℚ := 1791643327220829 / 9007199254740992
axiom cot_pi_21_48_bounds :
  ((cot_pi_21_48_lower : ℚ) : ℝ) ≤ cotangentTermV 21 48 ∧
  cotangentTermV 21 48 ≤ ((cot_pi_21_48_upper : ℚ) : ℝ)

def cot_pi_22_48_lower : ℚ := 1185820278153979 / 9007199254740992
def cot_pi_22_48_upper : ℚ := 2371640556307983 / 18014398509481984
axiom cot_pi_22_48_bounds :
  ((cot_pi_22_48_lower : ℚ) : ℝ) ≤ cotangentTermV 22 48 ∧
  cotangentTermV 22 48 ≤ ((cot_pi_22_48_upper : ℚ) : ℝ)

def cot_pi_23_48_lower : ℚ := 1180726058845107 / 18014398509481984
def cot_pi_23_48_upper : ℚ := 1180726058845131 / 18014398509481984
axiom cot_pi_23_48_bounds :
  ((cot_pi_23_48_lower : ℚ) : ℝ) ≤ cotangentTermV 23 48 ∧
  cotangentTermV 23 48 ≤ ((cot_pi_23_48_upper : ℚ) : ℝ)

def cot_pi_24_48_lower : ℚ := -488112137 / 9671406556917033397649408
def cot_pi_24_48_upper : ℚ := 1671954447 / 9671406556917033397649408
axiom cot_pi_24_48_bounds :
  ((cot_pi_24_48_lower : ℚ) : ℝ) ≤ cotangentTermV 24 48 ∧
  cotangentTermV 24 48 ≤ ((cot_pi_24_48_upper : ℚ) : ℝ)

def cot_pi_25_48_lower : ℚ := -1180726058845121 / 18014398509481984
def cot_pi_25_48_upper : ℚ := -2361452117690193 / 36028797018963968
axiom cot_pi_25_48_bounds :
  ((cot_pi_25_48_lower : ℚ) : ℝ) ≤ cotangentTermV 25 48 ∧
  cotangentTermV 25 48 ≤ ((cot_pi_25_48_upper : ℚ) : ℝ)

def cot_pi_26_48_lower : ℚ := -2371640556307969 / 18014398509481984
def cot_pi_26_48_upper : ℚ := -2371640556307951 / 18014398509481984
axiom cot_pi_26_48_bounds :
  ((cot_pi_26_48_lower : ℚ) : ℝ) ≤ cotangentTermV 26 48 ∧
  cotangentTermV 26 48 ≤ ((cot_pi_26_48_upper : ℚ) : ℝ)

def cot_pi_27_48_lower : ℚ := -895821663610413 / 4503599627370496
def cot_pi_27_48_upper : ℚ := -3583286654441625 / 18014398509481984
axiom cot_pi_27_48_bounds :
  ((cot_pi_27_48_lower : ℚ) : ℝ) ≤ cotangentTermV 27 48 ∧
  cotangentTermV 27 48 ≤ ((cot_pi_27_48_upper : ℚ) : ℝ)

def cot_pi_28_48_lower : ℚ := -4826943532748123 / 18014398509481984
def cot_pi_28_48_upper : ℚ := -4826943532748105 / 18014398509481984
axiom cot_pi_28_48_bounds :
  ((cot_pi_28_48_lower : ℚ) : ℝ) ≤ cotangentTermV 28 48 ∧
  cotangentTermV 28 48 ≤ ((cot_pi_28_48_upper : ℚ) : ℝ)

def cot_pi_29_48_lower : ℚ := -6115064294905715 / 18014398509481984
def cot_pi_29_48_upper : ℚ := -6115064294905683 / 18014398509481984
axiom cot_pi_29_48_bounds :
  ((cot_pi_29_48_lower : ℚ) : ℝ) ≤ cotangentTermV 29 48 ∧
  cotangentTermV 29 48 ≤ ((cot_pi_29_48_upper : ℚ) : ℝ)

def cot_pi_30_48_lower : ℚ := -1865452045155279 / 4503599627370496
def cot_pi_30_48_upper : ℚ := -3730904090310541 / 9007199254740992
axiom cot_pi_30_48_bounds :
  ((cot_pi_30_48_lower : ℚ) : ℝ) ≤ cotangentTermV 30 48 ∧
  cotangentTermV 30 48 ≤ ((cot_pi_30_48_upper : ℚ) : ℝ)

def cot_pi_31_48_lower : ℚ := -17351012163391 / 35184372088832
def cot_pi_31_48_upper : ℚ := -4441859113828083 / 9007199254740992
axiom cot_pi_31_48_bounds :
  ((cot_pi_31_48_lower : ℚ) : ℝ) ≤ cotangentTermV 31 48 ∧
  cotangentTermV 31 48 ≤ ((cot_pi_31_48_upper : ℚ) : ℝ)

def cot_pi_32_48_lower : ℚ := -2600154457184657 / 4503599627370496
def cot_pi_32_48_upper : ℚ := -325019307148081 / 562949953421312
axiom cot_pi_32_48_bounds :
  ((cot_pi_32_48_lower : ℚ) : ℝ) ≤ cotangentTermV 32 48 ∧
  cotangentTermV 32 48 ≤ ((cot_pi_32_48_upper : ℚ) : ℝ)

def cot_pi_33_48_lower : ℚ := -6018418129500565 / 9007199254740992
def cot_pi_33_48_upper : ℚ := -6018418129500547 / 9007199254740992
axiom cot_pi_33_48_bounds :
  ((cot_pi_33_48_lower : ℚ) : ℝ) ≤ cotangentTermV 33 48 ∧
  cotangentTermV 33 48 ≤ ((cot_pi_33_48_upper : ℚ) : ℝ)

def cot_pi_34_48_lower : ℚ := -53995836517709 / 70368744177664
def cot_pi_34_48_upper : ℚ := -215983346070835 / 281474976710656
axiom cot_pi_34_48_bounds :
  ((cot_pi_34_48_lower : ℚ) : ℝ) ≤ cotangentTermV 34 48 ∧
  cotangentTermV 34 48 ≤ ((cot_pi_34_48_upper : ℚ) : ℝ)

def cot_pi_35_48_lower : ℚ := -3949550871946881 / 4503599627370496
def cot_pi_35_48_upper : ℚ := -3949550871946863 / 4503599627370496
axiom cot_pi_35_48_bounds :
  ((cot_pi_35_48_lower : ℚ) : ℝ) ≤ cotangentTermV 35 48 ∧
  cotangentTermV 35 48 ≤ ((cot_pi_35_48_upper : ℚ) : ℝ)

def cot_pi_36_48_lower : ℚ := -2251799813685249 / 2251799813685248
def cot_pi_36_48_upper : ℚ := -4503599627370491 / 4503599627370496
axiom cot_pi_36_48_bounds :
  ((cot_pi_36_48_lower : ℚ) : ℝ) ≤ cotangentTermV 36 48 ∧
  cotangentTermV 36 48 ≤ ((cot_pi_36_48_upper : ℚ) : ℝ)

def cot_pi_37_48_lower : ℚ := -5135371150100863 / 4503599627370496
def cot_pi_37_48_upper : ℚ := -5135371150100839 / 4503599627370496
axiom cot_pi_37_48_bounds :
  ((cot_pi_37_48_lower : ℚ) : ℝ) ≤ cotangentTermV 37 48 ∧
  cotangentTermV 37 48 ≤ ((cot_pi_37_48_upper : ℚ) : ℝ)

def cot_pi_38_48_lower : ℚ := -1467301325876859 / 1125899906842624
def cot_pi_38_48_upper : ℚ := -2934602651753709 / 2251799813685248
axiom cot_pi_38_48_bounds :
  ((cot_pi_38_48_lower : ℚ) : ℝ) ≤ cotangentTermV 38 48 ∧
  cotangentTermV 38 48 ≤ ((cot_pi_38_48_upper : ℚ) : ℝ)

def cot_pi_39_48_lower : ℚ := -3370056577530423 / 2251799813685248
def cot_pi_39_48_upper : ℚ := -1685028288765203 / 1125899906842624
axiom cot_pi_39_48_bounds :
  ((cot_pi_39_48_lower : ℚ) : ℝ) ≤ cotangentTermV 39 48 ∧
  cotangentTermV 39 48 ≤ ((cot_pi_39_48_upper : ℚ) : ℝ)

def cot_pi_40_48_lower : ℚ := -7800463371553969 / 4503599627370496
def cot_pi_40_48_upper : ℚ := -7800463371553939 / 4503599627370496
axiom cot_pi_40_48_bounds :
  ((cot_pi_40_48_lower : ℚ) : ℝ) ≤ cotangentTermV 40 48 ∧
  cotangentTermV 40 48 ≤ ((cot_pi_40_48_upper : ℚ) : ℝ)

def cot_pi_41_48_lower : ℚ := -1141549578897601 / 562949953421312
def cot_pi_41_48_upper : ℚ := -1141549578897593 / 562949953421312
axiom cot_pi_41_48_bounds :
  ((cot_pi_41_48_lower : ℚ) : ℝ) ≤ cotangentTermV 41 48 ∧
  cotangentTermV 41 48 ≤ ((cot_pi_41_48_upper : ℚ) : ℝ)

def cot_pi_42_48_lower : ℚ := -5436325649948141 / 2251799813685248
def cot_pi_42_48_upper : ℚ := -5436325649948111 / 2251799813685248
axiom cot_pi_42_48_bounds :
  ((cot_pi_42_48_lower : ℚ) : ℝ) ≤ cotangentTermV 42 48 ∧
  cotangentTermV 42 48 ≤ ((cot_pi_42_48_upper : ℚ) : ℝ)

def cot_pi_43_48_lower : ℚ := -6633588340370659 / 2251799813685248
def cot_pi_43_48_upper : ℚ := -6633588340370619 / 2251799813685248
axiom cot_pi_43_48_bounds :
  ((cot_pi_43_48_lower : ℚ) : ℝ) ≤ cotangentTermV 43 48 ∧
  cotangentTermV 43 48 ≤ ((cot_pi_43_48_upper : ℚ) : ℝ)

def cot_pi_44_48_lower : ℚ := -2100957828286875 / 562949953421312
def cot_pi_44_48_upper : ℚ := -525239457071713 / 140737488355328
axiom cot_pi_44_48_bounds :
  ((cot_pi_44_48_lower : ℚ) : ℝ) ≤ cotangentTermV 44 48 ∧
  cotangentTermV 44 48 ≤ ((cot_pi_44_48_upper : ℚ) : ℝ)

def cot_pi_45_48_lower : ℚ := -5660281065850753 / 1125899906842624
def cot_pi_45_48_upper : ℚ := -5660281065850673 / 1125899906842624
axiom cot_pi_45_48_bounds :
  ((cot_pi_45_48_lower : ℚ) : ℝ) ≤ cotangentTermV 45 48 ∧
  cotangentTermV 45 48 ≤ ((cot_pi_45_48_upper : ℚ) : ℝ)

def cot_pi_46_48_lower : ℚ := -534503677994799 / 70368744177664
def cot_pi_46_48_upper : ℚ := -4276029423958305 / 562949953421312
axiom cot_pi_46_48_bounds :
  ((cot_pi_46_48_lower : ℚ) : ℝ) ≤ cotangentTermV 46 48 ∧
  cotangentTermV 46 48 ≤ ((cot_pi_46_48_upper : ℚ) : ℝ)

def cot_pi_47_48_lower : ℚ := -8588956537255681 / 562949953421312
def cot_pi_47_48_upper : ℚ := -8588956537255459 / 562949953421312
axiom cot_pi_47_48_bounds :
  ((cot_pi_47_48_lower : ℚ) : ℝ) ≤ cotangentTermV 47 48 ∧
  cotangentTermV 47 48 ≤ ((cot_pi_47_48_upper : ℚ) : ℝ)

def cot_pi_1_49_lower : ℚ := 4384199964780293 / 281474976710656
def cot_pi_1_49_upper : ℚ := 4384199964780299 / 281474976710656
axiom cot_pi_1_49_bounds :
  ((cot_pi_1_49_lower : ℚ) : ℝ) ≤ cotangentTermV 1 49 ∧
  cotangentTermV 1 49 ≤ ((cot_pi_1_49_upper : ℚ) : ℝ)

def cot_pi_2_49_lower : ℚ := 1091532167923397 / 140737488355328
def cot_pi_2_49_upper : ℚ := 2183064335846797 / 281474976710656
axiom cot_pi_2_49_bounds :
  ((cot_pi_2_49_lower : ℚ) : ℝ) ≤ cotangentTermV 2 49 ∧
  cotangentTermV 2 49 ≤ ((cot_pi_2_49_upper : ℚ) : ℝ)

def cot_pi_3_49_lower : ℚ := 5781258062607303 / 1125899906842624
def cot_pi_3_49_upper : ℚ := 5781258062607311 / 1125899906842624
axiom cot_pi_3_49_bounds :
  ((cot_pi_3_49_lower : ℚ) : ℝ) ≤ cotangentTermV 3 49 ∧
  cotangentTermV 3 49 ≤ ((cot_pi_3_49_upper : ℚ) : ℝ)

def cot_pi_4_49_lower : ℚ := 4293544312897279 / 1125899906842624
def cot_pi_4_49_upper : ℚ := 2146772156448643 / 562949953421312
axiom cot_pi_4_49_bounds :
  ((cot_pi_4_49_lower : ℚ) : ℝ) ≤ cotangentTermV 4 49 ∧
  cotangentTermV 4 49 ≤ ((cot_pi_4_49_upper : ℚ) : ℝ)

def cot_pi_5_49_lower : ℚ := 211939445726323 / 70368744177664
def cot_pi_5_49_upper : ℚ := 3391031131621173 / 1125899906842624
axiom cot_pi_5_49_bounds :
  ((cot_pi_5_49_lower : ℚ) : ℝ) ≤ cotangentTermV 5 49 ∧
  cotangentTermV 5 49 ≤ ((cot_pi_5_49_upper : ℚ) : ℝ)

def cot_pi_6_49_lower : ℚ := 2780994537695133 / 1125899906842624
def cot_pi_6_49_upper : ℚ := 2780994537695137 / 1125899906842624
axiom cot_pi_6_49_bounds :
  ((cot_pi_6_49_lower : ℚ) : ℝ) ≤ cotangentTermV 6 49 ∧
  cotangentTermV 6 49 ≤ ((cot_pi_6_49_upper : ℚ) : ℝ)

def cot_pi_7_49_lower : ℚ := 4675910493915015 / 2251799813685248
def cot_pi_7_49_upper : ℚ := 4675910493915021 / 2251799813685248
axiom cot_pi_7_49_bounds :
  ((cot_pi_7_49_lower : ℚ) : ℝ) ≤ cotangentTermV 7 49 ∧
  cotangentTermV 7 49 ≤ ((cot_pi_7_49_upper : ℚ) : ℝ)

def cot_pi_8_49_lower : ℚ := 499787323581859 / 281474976710656
def cot_pi_8_49_upper : ℚ := 1999149294327439 / 1125899906842624
axiom cot_pi_8_49_bounds :
  ((cot_pi_8_49_lower : ℚ) : ℝ) ≤ cotangentTermV 8 49 ∧
  cotangentTermV 8 49 ≤ ((cot_pi_8_49_upper : ℚ) : ℝ)

def cot_pi_9_49_lower : ℚ := 6918738413471011 / 4503599627370496
def cot_pi_9_49_upper : ℚ := 6918738413471023 / 4503599627370496
axiom cot_pi_9_49_bounds :
  ((cot_pi_9_49_lower : ℚ) : ℝ) ≤ cotangentTermV 9 49 ∧
  cotangentTermV 9 49 ≤ ((cot_pi_9_49_upper : ℚ) : ℝ)

def cot_pi_10_49_lower : ℚ := 47143853236797 / 35184372088832
def cot_pi_10_49_upper : ℚ := 3017206607155013 / 2251799813685248
axiom cot_pi_10_49_bounds :
  ((cot_pi_10_49_lower : ℚ) : ℝ) ≤ cotangentTermV 10 49 ∧
  cotangentTermV 10 49 ≤ ((cot_pi_10_49_upper : ℚ) : ℝ)

def cot_pi_11_49_lower : ℚ := 5290184384387765 / 4503599627370496
def cot_pi_11_49_upper : ℚ := 5290184384387777 / 4503599627370496
axiom cot_pi_11_49_bounds :
  ((cot_pi_11_49_lower : ℚ) : ℝ) ≤ cotangentTermV 11 49 ∧
  cotangentTermV 11 49 ≤ ((cot_pi_11_49_upper : ℚ) : ℝ)

def cot_pi_12_49_lower : ℚ := 2325168183832947 / 2251799813685248
def cot_pi_12_49_upper : ℚ := 2325168183832951 / 2251799813685248
axiom cot_pi_12_49_bounds :
  ((cot_pi_12_49_lower : ℚ) : ℝ) ≤ cotangentTermV 12 49 ∧
  cotangentTermV 12 49 ≤ ((cot_pi_12_49_upper : ℚ) : ℝ)

def cot_pi_13_49_lower : ℚ := 4090050022861441 / 4503599627370496
def cot_pi_13_49_upper : ℚ := 2045025011430725 / 2251799813685248
axiom cot_pi_13_49_bounds :
  ((cot_pi_13_49_lower : ℚ) : ℝ) ≤ cotangentTermV 13 49 ∧
  cotangentTermV 13 49 ≤ ((cot_pi_13_49_upper : ℚ) : ℝ)

def cot_pi_14_49_lower : ℚ := 3591500857008679 / 4503599627370496
def cot_pi_14_49_upper : ℚ := 3591500857008683 / 4503599627370496
axiom cot_pi_14_49_bounds :
  ((cot_pi_14_49_lower : ℚ) : ℝ) ≤ cotangentTermV 14 49 ∧
  cotangentTermV 14 49 ≤ ((cot_pi_14_49_upper : ℚ) : ℝ)

def cot_pi_15_49_lower : ℚ := 3141516142367951 / 4503599627370496
def cot_pi_15_49_upper : ℚ := 1570758071183979 / 2251799813685248
axiom cot_pi_15_49_bounds :
  ((cot_pi_15_49_lower : ℚ) : ℝ) ≤ cotangentTermV 15 49 ∧
  cotangentTermV 15 49 ≤ ((cot_pi_15_49_upper : ℚ) : ℝ)

def cot_pi_16_49_lower : ℚ := 2730108560201095 / 4503599627370496
def cot_pi_16_49_upper : ℚ := 1365054280100551 / 2251799813685248
axiom cot_pi_16_49_bounds :
  ((cot_pi_16_49_lower : ℚ) : ℝ) ≤ cotangentTermV 16 49 ∧
  cotangentTermV 16 49 ≤ ((cot_pi_16_49_upper : ℚ) : ℝ)

def cot_pi_17_49_lower : ℚ := 4699050081811899 / 9007199254740992
def cot_pi_17_49_upper : ℚ := 4699050081811913 / 9007199254740992
axiom cot_pi_17_49_bounds :
  ((cot_pi_17_49_lower : ℚ) : ℝ) ≤ cotangentTermV 17 49 ∧
  cotangentTermV 17 49 ≤ ((cot_pi_17_49_upper : ℚ) : ℝ)

def cot_pi_18_49_lower : ℚ := 996804980250295 / 2251799813685248
def cot_pi_18_49_upper : ℚ := 1993609960500595 / 4503599627370496
axiom cot_pi_18_49_bounds :
  ((cot_pi_18_49_lower : ℚ) : ℝ) ≤ cotangentTermV 18 49 ∧
  cotangentTermV 18 49 ≤ ((cot_pi_18_49_upper : ℚ) : ℝ)

def cot_pi_19_49_lower : ℚ := 6629465174763733 / 18014398509481984
def cot_pi_19_49_upper : ℚ := 6629465174763757 / 18014398509481984
axiom cot_pi_19_49_bounds :
  ((cot_pi_19_49_lower : ℚ) : ℝ) ≤ cotangentTermV 19 49 ∧
  cotangentTermV 19 49 ≤ ((cot_pi_19_49_upper : ℚ) : ℝ)

def cot_pi_20_49_lower : ℚ := 5346578918106857 / 18014398509481984
def cot_pi_20_49_upper : ℚ := 5346578918106875 / 18014398509481984
axiom cot_pi_20_49_bounds :
  ((cot_pi_20_49_lower : ℚ) : ℝ) ≤ cotangentTermV 20 49 ∧
  cotangentTermV 20 49 ≤ ((cot_pi_20_49_upper : ℚ) : ℝ)

def cot_pi_21_49_lower : ℚ := 8223337809705797 / 36028797018963968
def cot_pi_21_49_upper : ℚ := 8223337809705849 / 36028797018963968
axiom cot_pi_21_49_bounds :
  ((cot_pi_21_49_lower : ℚ) : ℝ) ≤ cotangentTermV 21 49 ∧
  cotangentTermV 21 49 ≤ ((cot_pi_21_49_upper : ℚ) : ℝ)

def cot_pi_22_49_lower : ℚ := 5824856494532221 / 36028797018963968
def cot_pi_22_49_upper : ℚ := 5824856494532273 / 36028797018963968
axiom cot_pi_22_49_bounds :
  ((cot_pi_22_49_lower : ℚ) : ℝ) ≤ cotangentTermV 22 49 ∧
  cotangentTermV 22 49 ≤ ((cot_pi_22_49_upper : ℚ) : ℝ)

def cot_pi_23_49_lower : ℚ := 6951309434903005 / 72057594037927936
def cot_pi_23_49_upper : ℚ := 6951309434903101 / 72057594037927936
axiom cot_pi_23_49_bounds :
  ((cot_pi_23_49_lower : ℚ) : ℝ) ≤ cotangentTermV 23 49 ∧
  cotangentTermV 23 49 ≤ ((cot_pi_23_49_upper : ℚ) : ℝ)

def cot_pi_24_49_lower : ℚ := 4621493578396145 / 144115188075855872
def cot_pi_24_49_upper : ℚ := 4621493578396247 / 144115188075855872
axiom cot_pi_24_49_bounds :
  ((cot_pi_24_49_lower : ℚ) : ℝ) ≤ cotangentTermV 24 49 ∧
  cotangentTermV 24 49 ≤ ((cot_pi_24_49_upper : ℚ) : ℝ)

def cot_pi_25_49_lower : ℚ := -4621493578396207 / 144115188075855872
def cot_pi_25_49_upper : ℚ := -4621493578396021 / 144115188075855872
axiom cot_pi_25_49_bounds :
  ((cot_pi_25_49_lower : ℚ) : ℝ) ≤ cotangentTermV 25 49 ∧
  cotangentTermV 25 49 ≤ ((cot_pi_25_49_upper : ℚ) : ℝ)

def cot_pi_26_49_lower : ℚ := -3475654717451531 / 36028797018963968
def cot_pi_26_49_upper : ℚ := -1737827358725741 / 18014398509481984
axiom cot_pi_26_49_bounds :
  ((cot_pi_26_49_lower : ℚ) : ℝ) ≤ cotangentTermV 26 49 ∧
  cotangentTermV 26 49 ≤ ((cot_pi_26_49_upper : ℚ) : ℝ)

def cot_pi_27_49_lower : ℚ := -5824856494532253 / 36028797018963968
def cot_pi_27_49_upper : ℚ := -5824856494532201 / 36028797018963968
axiom cot_pi_27_49_bounds :
  ((cot_pi_27_49_lower : ℚ) : ℝ) ≤ cotangentTermV 27 49 ∧
  cotangentTermV 27 49 ≤ ((cot_pi_27_49_upper : ℚ) : ℝ)

def cot_pi_28_49_lower : ℚ := -8223337809705817 / 36028797018963968
def cot_pi_28_49_upper : ℚ := -8223337809705801 / 36028797018963968
axiom cot_pi_28_49_bounds :
  ((cot_pi_28_49_lower : ℚ) : ℝ) ≤ cotangentTermV 28 49 ∧
  cotangentTermV 28 49 ≤ ((cot_pi_28_49_upper : ℚ) : ℝ)

def cot_pi_29_49_lower : ℚ := -2673289459053435 / 9007199254740992
def cot_pi_29_49_upper : ℚ := -668322364763355 / 2251799813685248
axiom cot_pi_29_49_bounds :
  ((cot_pi_29_49_lower : ℚ) : ℝ) ≤ cotangentTermV 29 49 ∧
  cotangentTermV 29 49 ≤ ((cot_pi_29_49_upper : ℚ) : ℝ)

def cot_pi_30_49_lower : ℚ := -6629465174763751 / 18014398509481984
def cot_pi_30_49_upper : ℚ := -6629465174763719 / 18014398509481984
axiom cot_pi_30_49_bounds :
  ((cot_pi_30_49_lower : ℚ) : ℝ) ≤ cotangentTermV 30 49 ∧
  cotangentTermV 30 49 ≤ ((cot_pi_30_49_upper : ℚ) : ℝ)

def cot_pi_31_49_lower : ℚ := -7974439842002379 / 18014398509481984
def cot_pi_31_49_upper : ℚ := -7974439842002345 / 18014398509481984
axiom cot_pi_31_49_bounds :
  ((cot_pi_31_49_lower : ℚ) : ℝ) ≤ cotangentTermV 31 49 ∧
  cotangentTermV 31 49 ≤ ((cot_pi_31_49_upper : ℚ) : ℝ)

def cot_pi_32_49_lower : ℚ := -4699050081811911 / 9007199254740992
def cot_pi_32_49_upper : ℚ := -4699050081811893 / 9007199254740992
axiom cot_pi_32_49_bounds :
  ((cot_pi_32_49_lower : ℚ) : ℝ) ≤ cotangentTermV 32 49 ∧
  cotangentTermV 32 49 ≤ ((cot_pi_32_49_upper : ℚ) : ℝ)

def cot_pi_33_49_lower : ℚ := -5460217120402205 / 9007199254740992
def cot_pi_33_49_upper : ℚ := -5460217120402177 / 9007199254740992
axiom cot_pi_33_49_bounds :
  ((cot_pi_33_49_lower : ℚ) : ℝ) ≤ cotangentTermV 33 49 ∧
  cotangentTermV 33 49 ≤ ((cot_pi_33_49_upper : ℚ) : ℝ)

def cot_pi_34_49_lower : ℚ := -6283032284735917 / 9007199254740992
def cot_pi_34_49_upper : ℚ := -6283032284735887 / 9007199254740992
axiom cot_pi_34_49_bounds :
  ((cot_pi_34_49_lower : ℚ) : ℝ) ≤ cotangentTermV 34 49 ∧
  cotangentTermV 34 49 ≤ ((cot_pi_34_49_upper : ℚ) : ℝ)

def cot_pi_35_49_lower : ℚ := -3591500857008685 / 4503599627370496
def cot_pi_35_49_upper : ℚ := -897875214252167 / 1125899906842624
axiom cot_pi_35_49_bounds :
  ((cot_pi_35_49_lower : ℚ) : ℝ) ≤ cotangentTermV 35 49 ∧
  cotangentTermV 35 49 ≤ ((cot_pi_35_49_upper : ℚ) : ℝ)

def cot_pi_36_49_lower : ℚ := -8180100045722897 / 9007199254740992
def cot_pi_36_49_upper : ℚ := -8180100045722869 / 9007199254740992
axiom cot_pi_36_49_bounds :
  ((cot_pi_36_49_lower : ℚ) : ℝ) ≤ cotangentTermV 36 49 ∧
  cotangentTermV 36 49 ≤ ((cot_pi_36_49_upper : ℚ) : ℝ)

def cot_pi_37_49_lower : ℚ := -2325168183832951 / 2251799813685248
def cot_pi_37_49_upper : ℚ := -581292045958235 / 562949953421312
axiom cot_pi_37_49_bounds :
  ((cot_pi_37_49_lower : ℚ) : ℝ) ≤ cotangentTermV 37 49 ∧
  cotangentTermV 37 49 ≤ ((cot_pi_37_49_upper : ℚ) : ℝ)

def cot_pi_38_49_lower : ℚ := -5290184384387777 / 4503599627370496
def cot_pi_38_49_upper : ℚ := -5290184384387751 / 4503599627370496
axiom cot_pi_38_49_bounds :
  ((cot_pi_38_49_lower : ℚ) : ℝ) ≤ cotangentTermV 38 49 ∧
  cotangentTermV 38 49 ≤ ((cot_pi_38_49_upper : ℚ) : ℝ)

def cot_pi_39_49_lower : ℚ := -6034413214310031 / 4503599627370496
def cot_pi_39_49_upper : ℚ := -6034413214310001 / 4503599627370496
axiom cot_pi_39_49_bounds :
  ((cot_pi_39_49_lower : ℚ) : ℝ) ≤ cotangentTermV 39 49 ∧
  cotangentTermV 39 49 ≤ ((cot_pi_39_49_upper : ℚ) : ℝ)

def cot_pi_40_49_lower : ℚ := -6918738413471021 / 4503599627370496
def cot_pi_40_49_upper : ℚ := -6918738413470995 / 4503599627370496
axiom cot_pi_40_49_bounds :
  ((cot_pi_40_49_lower : ℚ) : ℝ) ≤ cotangentTermV 40 49 ∧
  cotangentTermV 40 49 ≤ ((cot_pi_40_49_upper : ℚ) : ℝ)

def cot_pi_41_49_lower : ℚ := -7996597177309761 / 4503599627370496
def cot_pi_41_49_upper : ℚ := -7996597177309709 / 4503599627370496
axiom cot_pi_41_49_bounds :
  ((cot_pi_41_49_lower : ℚ) : ℝ) ≤ cotangentTermV 41 49 ∧
  cotangentTermV 41 49 ≤ ((cot_pi_41_49_upper : ℚ) : ℝ)

def cot_pi_42_49_lower : ℚ := -4675910493915029 / 2251799813685248
def cot_pi_42_49_upper : ℚ := -4675910493914995 / 2251799813685248
axiom cot_pi_42_49_bounds :
  ((cot_pi_42_49_lower : ℚ) : ℝ) ≤ cotangentTermV 42 49 ∧
  cotangentTermV 42 49 ≤ ((cot_pi_42_49_upper : ℚ) : ℝ)

def cot_pi_43_49_lower : ℚ := -2780994537695143 / 1125899906842624
def cot_pi_43_49_upper : ℚ := -2780994537695121 / 1125899906842624
axiom cot_pi_43_49_bounds :
  ((cot_pi_43_49_lower : ℚ) : ℝ) ≤ cotangentTermV 43 49 ∧
  cotangentTermV 43 49 ≤ ((cot_pi_43_49_upper : ℚ) : ℝ)

def cot_pi_44_49_lower : ℚ := -1695515565810589 / 562949953421312
def cot_pi_44_49_upper : ℚ := -3391031131621147 / 1125899906842624
axiom cot_pi_44_49_bounds :
  ((cot_pi_44_49_lower : ℚ) : ℝ) ≤ cotangentTermV 44 49 ∧
  cotangentTermV 44 49 ≤ ((cot_pi_44_49_upper : ℚ) : ℝ)

def cot_pi_45_49_lower : ℚ := -4293544312897291 / 1125899906842624
def cot_pi_45_49_upper : ℚ := -1073386078224311 / 281474976710656
axiom cot_pi_45_49_bounds :
  ((cot_pi_45_49_lower : ℚ) : ℝ) ≤ cotangentTermV 45 49 ∧
  cotangentTermV 45 49 ≤ ((cot_pi_45_49_upper : ℚ) : ℝ)

def cot_pi_46_49_lower : ℚ := -2890629031303663 / 562949953421312
def cot_pi_46_49_upper : ℚ := -1445314515651811 / 281474976710656
axiom cot_pi_46_49_bounds :
  ((cot_pi_46_49_lower : ℚ) : ℝ) ≤ cotangentTermV 46 49 ∧
  cotangentTermV 46 49 ≤ ((cot_pi_46_49_upper : ℚ) : ℝ)

def cot_pi_47_49_lower : ℚ := -8732257343387237 / 1125899906842624
def cot_pi_47_49_upper : ℚ := -8732257343387057 / 1125899906842624
axiom cot_pi_47_49_bounds :
  ((cot_pi_47_49_lower : ℚ) : ℝ) ≤ cotangentTermV 47 49 ∧
  cotangentTermV 47 49 ≤ ((cot_pi_47_49_upper : ℚ) : ℝ)

def cot_pi_48_49_lower : ℚ := -4384199964780321 / 281474976710656
def cot_pi_48_49_upper : ℚ := -2192099982390113 / 140737488355328
axiom cot_pi_48_49_bounds :
  ((cot_pi_48_49_lower : ℚ) : ℝ) ≤ cotangentTermV 48 49 ∧
  cotangentTermV 48 49 ≤ ((cot_pi_48_49_upper : ℚ) : ℝ)

def cot_pi_1_50_lower : ℚ := 4473916639753461 / 281474976710656
def cot_pi_1_50_upper : ℚ := 1118479159938367 / 70368744177664
axiom cot_pi_1_50_bounds :
  ((cot_pi_1_50_lower : ℚ) : ℝ) ≤ cotangentTermV 1 50 ∧
  cotangentTermV 1 50 ≤ ((cot_pi_1_50_upper : ℚ) : ℝ)

def cot_pi_2_50_lower : ℚ := 8912415470506963 / 1125899906842624
def cot_pi_2_50_upper : ℚ := 8912415470506977 / 1125899906842624
axiom cot_pi_2_50_bounds :
  ((cot_pi_2_50_lower : ℚ) : ℝ) ≤ cotangentTermV 2 50 ∧
  cotangentTermV 2 50 ≤ ((cot_pi_2_50_upper : ℚ) : ℝ)

def cot_pi_3_50_lower : ℚ := 5902174005627255 / 1125899906842624
def cot_pi_3_50_upper : ℚ := 5902174005627263 / 1125899906842624
axiom cot_pi_3_50_bounds :
  ((cot_pi_3_50_lower : ℚ) : ℝ) ≤ cotangentTermV 3 50 ∧
  cotangentTermV 3 50 ≤ ((cot_pi_3_50_upper : ℚ) : ℝ)

def cot_pi_4_50_lower : ℚ := 8770181235083003 / 2251799813685248
def cot_pi_4_50_upper : ℚ := 8770181235083015 / 2251799813685248
axiom cot_pi_4_50_bounds :
  ((cot_pi_4_50_lower : ℚ) : ℝ) ≤ cotangentTermV 4 50 ∧
  cotangentTermV 4 50 ≤ ((cot_pi_4_50_upper : ℚ) : ℝ)

def cot_pi_5_50_lower : ℚ := 3465163607796693 / 1125899906842624
def cot_pi_5_50_upper : ℚ := 3465163607796697 / 1125899906842624
axiom cot_pi_5_50_bounds :
  ((cot_pi_5_50_lower : ℚ) : ℝ) ≤ cotangentTermV 5 50 ∧
  cotangentTermV 5 50 ≤ ((cot_pi_5_50_upper : ℚ) : ℝ)

def cot_pi_6_50_lower : ℚ := 2843698555860045 / 1125899906842624
def cot_pi_6_50_upper : ℚ := 2843698555860049 / 1125899906842624
axiom cot_pi_6_50_bounds :
  ((cot_pi_6_50_lower : ℚ) : ℝ) ≤ cotangentTermV 6 50 ∧
  cotangentTermV 6 50 ≤ ((cot_pi_6_50_upper : ℚ) : ℝ)

def cot_pi_7_50_lower : ℚ := 74770596693381 / 35184372088832
def cot_pi_7_50_upper : ℚ := 2392659094188195 / 1125899906842624
axiom cot_pi_7_50_bounds :
  ((cot_pi_7_50_lower : ℚ) : ℝ) ≤ cotangentTermV 7 50 ∧
  cotangentTermV 7 50 ≤ ((cot_pi_7_50_upper : ℚ) : ℝ)

def cot_pi_8_50_lower : ℚ := 4096008655322227 / 2251799813685248
def cot_pi_8_50_upper : ℚ := 4096008655322233 / 2251799813685248
axiom cot_pi_8_50_bounds :
  ((cot_pi_8_50_lower : ℚ) : ℝ) ≤ cotangentTermV 8 50 ∧
  cotangentTermV 8 50 ≤ ((cot_pi_8_50_upper : ℚ) : ℝ)

def cot_pi_9_50_lower : ℚ := 7096537474984669 / 4503599627370496
def cot_pi_9_50_upper : ℚ := 7096537474984681 / 4503599627370496
axiom cot_pi_9_50_bounds :
  ((cot_pi_9_50_lower : ℚ) : ℝ) ≤ cotangentTermV 9 50 ∧
  cotangentTermV 9 50 ≤ ((cot_pi_9_50_upper : ℚ) : ℝ)

def cot_pi_10_50_lower : ℚ := 6198673104153461 / 4503599627370496
def cot_pi_10_50_upper : ℚ := 6198673104153469 / 4503599627370496
axiom cot_pi_10_50_bounds :
  ((cot_pi_10_50_lower : ℚ) : ℝ) ≤ cotangentTermV 10 50 ∧
  cotangentTermV 10 50 ≤ ((cot_pi_10_50_upper : ℚ) : ℝ)

def cot_pi_11_50_lower : ℚ := 5443916778873017 / 4503599627370496
def cot_pi_11_50_upper : ℚ := 5443916778873029 / 4503599627370496
axiom cot_pi_11_50_bounds :
  ((cot_pi_11_50_lower : ℚ) : ℝ) ≤ cotangentTermV 11 50 ∧
  cotangentTermV 11 50 ≤ ((cot_pi_11_50_upper : ℚ) : ℝ)

def cot_pi_12_50_lower : ℚ := 2397923247638305 / 2251799813685248
def cot_pi_12_50_upper : ℚ := 2397923247638309 / 2251799813685248
axiom cot_pi_12_50_bounds :
  ((cot_pi_12_50_lower : ℚ) : ℝ) ≤ cotangentTermV 12 50 ∧
  cotangentTermV 12 50 ≤ ((cot_pi_12_50_upper : ℚ) : ℝ)

def cot_pi_13_50_lower : ℚ := 8458323102554519 / 9007199254740992
def cot_pi_13_50_upper : ℚ := 8458323102554537 / 9007199254740992
axiom cot_pi_13_50_bounds :
  ((cot_pi_13_50_lower : ℚ) : ℝ) ≤ cotangentTermV 13 50 ∧
  cotangentTermV 13 50 ≤ ((cot_pi_13_50_upper : ℚ) : ℝ)

def cot_pi_14_50_lower : ℚ := 7451403255231407 / 9007199254740992
def cot_pi_14_50_upper : ℚ := 7451403255231419 / 9007199254740992
axiom cot_pi_14_50_bounds :
  ((cot_pi_14_50_lower : ℚ) : ℝ) ≤ cotangentTermV 14 50 ∧
  cotangentTermV 14 50 ≤ ((cot_pi_14_50_upper : ℚ) : ℝ)

def cot_pi_15_50_lower : ℚ := 6544113316787517 / 9007199254740992
def cot_pi_15_50_upper : ℚ := 6544113316787533 / 9007199254740992
axiom cot_pi_15_50_bounds :
  ((cot_pi_15_50_lower : ℚ) : ℝ) ≤ cotangentTermV 15 50 ∧
  cotangentTermV 15 50 ≤ ((cot_pi_15_50_upper : ℚ) : ℝ)

def cot_pi_16_50_lower : ℚ := 714517807985487 / 1125899906842624
def cot_pi_16_50_upper : ℚ := 2858071231941955 / 4503599627370496
axiom cot_pi_16_50_bounds :
  ((cot_pi_16_50_lower : ℚ) : ℝ) ≤ cotangentTermV 16 50 ∧
  cotangentTermV 16 50 ≤ ((cot_pi_16_50_upper : ℚ) : ℝ)

def cot_pi_17_50_lower : ℚ := 1237937423380277 / 2251799813685248
def cot_pi_17_50_upper : ℚ := 2475874846760561 / 4503599627370496
axiom cot_pi_17_50_bounds :
  ((cot_pi_17_50_lower : ℚ) : ℝ) ≤ cotangentTermV 17 50 ∧
  cotangentTermV 17 50 ≤ ((cot_pi_17_50_upper : ℚ) : ℝ)

def cot_pi_18_50_lower : ℚ := 8476932486085439 / 18014398509481984
def cot_pi_18_50_upper : ℚ := 8476932486085459 / 18014398509481984
axiom cot_pi_18_50_bounds :
  ((cot_pi_18_50_lower : ℚ) : ℝ) ≤ cotangentTermV 18 50 ∧
  cotangentTermV 18 50 ≤ ((cot_pi_18_50_upper : ℚ) : ℝ)

def cot_pi_19_50_lower : ℚ := 7132404931547829 / 18014398509481984
def cot_pi_19_50_upper : ℚ := 7132404931547853 / 18014398509481984
axiom cot_pi_19_50_bounds :
  ((cot_pi_19_50_lower : ℚ) : ℝ) ≤ cotangentTermV 19 50 ∧
  cotangentTermV 19 50 ≤ ((cot_pi_19_50_upper : ℚ) : ℝ)

def cot_pi_20_50_lower : ℚ := 2926616445759701 / 9007199254740992
def cot_pi_20_50_upper : ℚ := 1463308222879853 / 4503599627370496
axiom cot_pi_20_50_bounds :
  ((cot_pi_20_50_lower : ℚ) : ℝ) ≤ cotangentTermV 20 50 ∧
  cotangentTermV 20 50 ≤ ((cot_pi_20_50_upper : ℚ) : ℝ)

def cot_pi_21_50_lower : ℚ := 2312655697754195 / 9007199254740992
def cot_pi_21_50_upper : ℚ := 2312655697754209 / 9007199254740992
axiom cot_pi_21_50_bounds :
  ((cot_pi_21_50_lower : ℚ) : ℝ) ≤ cotangentTermV 21 50 ∧
  cotangentTermV 21 50 ≤ ((cot_pi_21_50_upper : ℚ) : ℝ)

def cot_pi_22_50_lower : ℚ := 6872860605029247 / 36028797018963968
def cot_pi_22_50_upper : ℚ := 6872860605029299 / 36028797018963968
axiom cot_pi_22_50_bounds :
  ((cot_pi_22_50_lower : ℚ) : ℝ) ≤ cotangentTermV 22 50 ∧
  cotangentTermV 22 50 ≤ ((cot_pi_22_50_upper : ℚ) : ℝ)

def cot_pi_23_50_lower : ℚ := 4551495533566695 / 36028797018963968
def cot_pi_23_50_upper : ℚ := 4551495533566745 / 36028797018963968
axiom cot_pi_23_50_bounds :
  ((cot_pi_23_50_lower : ℚ) : ℝ) ≤ cotangentTermV 23 50 ∧
  cotangentTermV 23 50 ≤ ((cot_pi_23_50_upper : ℚ) : ℝ)

def cot_pi_24_50_lower : ℚ := 4533479551994797 / 72057594037927936
def cot_pi_24_50_upper : ℚ := 4533479551994849 / 72057594037927936
axiom cot_pi_24_50_bounds :
  ((cot_pi_24_50_lower : ℚ) : ℝ) ≤ cotangentTermV 24 50 ∧
  cotangentTermV 24 50 ≤ ((cot_pi_24_50_upper : ℚ) : ℝ)

def cot_pi_25_50_lower : ℚ := -101152851 / 302231454903657293676544
def cot_pi_25_50_upper : ℚ := 544731305 / 604462909807314587353088
axiom cot_pi_25_50_bounds :
  ((cot_pi_25_50_lower : ℚ) : ℝ) ≤ cotangentTermV 25 50 ∧
  cotangentTermV 25 50 ≤ ((cot_pi_25_50_upper : ℚ) : ℝ)

def cot_pi_26_50_lower : ℚ := -2266739775997415 / 36028797018963968
def cot_pi_26_50_upper : ℚ := -2266739775997367 / 36028797018963968
axiom cot_pi_26_50_bounds :
  ((cot_pi_26_50_lower : ℚ) : ℝ) ≤ cotangentTermV 26 50 ∧
  cotangentTermV 26 50 ≤ ((cot_pi_26_50_upper : ℚ) : ℝ)

def cot_pi_27_50_lower : ℚ := -2275747766783363 / 18014398509481984
def cot_pi_27_50_upper : ℚ := -2275747766783337 / 18014398509481984
axiom cot_pi_27_50_bounds :
  ((cot_pi_27_50_lower : ℚ) : ℝ) ≤ cotangentTermV 27 50 ∧
  cotangentTermV 27 50 ≤ ((cot_pi_27_50_upper : ℚ) : ℝ)

def cot_pi_28_50_lower : ℚ := -6872860605029267 / 36028797018963968
def cot_pi_28_50_upper : ℚ := -6872860605029235 / 36028797018963968
axiom cot_pi_28_50_bounds :
  ((cot_pi_28_50_lower : ℚ) : ℝ) ≤ cotangentTermV 28 50 ∧
  cotangentTermV 28 50 ≤ ((cot_pi_28_50_upper : ℚ) : ℝ)

def cot_pi_29_50_lower : ℚ := -4625311395508403 / 18014398509481984
def cot_pi_29_50_upper : ℚ := -4625311395508375 / 18014398509481984
axiom cot_pi_29_50_bounds :
  ((cot_pi_29_50_lower : ℚ) : ℝ) ≤ cotangentTermV 29 50 ∧
  cotangentTermV 29 50 ≤ ((cot_pi_29_50_upper : ℚ) : ℝ)

def cot_pi_30_50_lower : ℚ := -731654111439927 / 2251799813685248
def cot_pi_30_50_upper : ℚ := -731654111439923 / 2251799813685248
axiom cot_pi_30_50_bounds :
  ((cot_pi_30_50_lower : ℚ) : ℝ) ≤ cotangentTermV 30 50 ∧
  cotangentTermV 30 50 ≤ ((cot_pi_30_50_upper : ℚ) : ℝ)

def cot_pi_31_50_lower : ℚ := -1783101232886963 / 4503599627370496
def cot_pi_31_50_upper : ℚ := -3566202465773909 / 9007199254740992
axiom cot_pi_31_50_bounds :
  ((cot_pi_31_50_lower : ℚ) : ℝ) ≤ cotangentTermV 31 50 ∧
  cotangentTermV 31 50 ≤ ((cot_pi_31_50_upper : ℚ) : ℝ)

def cot_pi_32_50_lower : ℚ := -8476932486085453 / 18014398509481984
def cot_pi_32_50_upper : ℚ := -8476932486085421 / 18014398509481984
axiom cot_pi_32_50_bounds :
  ((cot_pi_32_50_lower : ℚ) : ℝ) ≤ cotangentTermV 32 50 ∧
  cotangentTermV 32 50 ≤ ((cot_pi_32_50_upper : ℚ) : ℝ)

def cot_pi_33_50_lower : ℚ := -1237937423380279 / 2251799813685248
def cot_pi_33_50_upper : ℚ := -2475874846760545 / 4503599627370496
axiom cot_pi_33_50_bounds :
  ((cot_pi_33_50_lower : ℚ) : ℝ) ≤ cotangentTermV 33 50 ∧
  cotangentTermV 33 50 ≤ ((cot_pi_33_50_upper : ℚ) : ℝ)

def cot_pi_34_50_lower : ℚ := -5716142463883907 / 9007199254740992
def cot_pi_34_50_upper : ℚ := -5716142463883879 / 9007199254740992
axiom cot_pi_34_50_bounds :
  ((cot_pi_34_50_lower : ℚ) : ℝ) ≤ cotangentTermV 34 50 ∧
  cotangentTermV 34 50 ≤ ((cot_pi_34_50_upper : ℚ) : ℝ)

def cot_pi_35_50_lower : ℚ := -6544113316787531 / 9007199254740992
def cot_pi_35_50_upper : ℚ := -6544113316787501 / 9007199254740992
axiom cot_pi_35_50_bounds :
  ((cot_pi_35_50_lower : ℚ) : ℝ) ≤ cotangentTermV 35 50 ∧
  cotangentTermV 35 50 ≤ ((cot_pi_35_50_upper : ℚ) : ℝ)

def cot_pi_36_50_lower : ℚ := -3725701627615709 / 4503599627370496
def cot_pi_36_50_upper : ℚ := -232856351725981 / 281474976710656
axiom cot_pi_36_50_bounds :
  ((cot_pi_36_50_lower : ℚ) : ℝ) ≤ cotangentTermV 36 50 ∧
  cotangentTermV 36 50 ≤ ((cot_pi_36_50_upper : ℚ) : ℝ)

def cot_pi_37_50_lower : ℚ := -8458323102554539 / 9007199254740992
def cot_pi_37_50_upper : ℚ := -8458323102554501 / 9007199254740992
axiom cot_pi_37_50_bounds :
  ((cot_pi_37_50_lower : ℚ) : ℝ) ≤ cotangentTermV 37 50 ∧
  cotangentTermV 37 50 ≤ ((cot_pi_37_50_upper : ℚ) : ℝ)

def cot_pi_38_50_lower : ℚ := -2397923247638311 / 2251799813685248
def cot_pi_38_50_upper : ℚ := -599480811909575 / 562949953421312
axiom cot_pi_38_50_bounds :
  ((cot_pi_38_50_lower : ℚ) : ℝ) ≤ cotangentTermV 38 50 ∧
  cotangentTermV 38 50 ≤ ((cot_pi_38_50_upper : ℚ) : ℝ)

def cot_pi_39_50_lower : ℚ := -680489597359129 / 562949953421312
def cot_pi_39_50_upper : ℚ := -2721958389436503 / 2251799813685248
axiom cot_pi_39_50_bounds :
  ((cot_pi_39_50_lower : ℚ) : ℝ) ≤ cotangentTermV 39 50 ∧
  cotangentTermV 39 50 ≤ ((cot_pi_39_50_upper : ℚ) : ℝ)

def cot_pi_40_50_lower : ℚ := -6198673104153469 / 4503599627370496
def cot_pi_40_50_upper : ℚ := -6198673104153459 / 4503599627370496
axiom cot_pi_40_50_bounds :
  ((cot_pi_40_50_lower : ℚ) : ℝ) ≤ cotangentTermV 40 50 ∧
  cotangentTermV 40 50 ≤ ((cot_pi_40_50_upper : ℚ) : ℝ)

def cot_pi_41_50_lower : ℚ := -7096537474984687 / 4503599627370496
def cot_pi_41_50_upper : ℚ := -7096537474984643 / 4503599627370496
axiom cot_pi_41_50_bounds :
  ((cot_pi_41_50_lower : ℚ) : ℝ) ≤ cotangentTermV 41 50 ∧
  cotangentTermV 41 50 ≤ ((cot_pi_41_50_upper : ℚ) : ℝ)

def cot_pi_42_50_lower : ℚ := -8192017310644469 / 4503599627370496
def cot_pi_42_50_upper : ℚ := -8192017310644417 / 4503599627370496
axiom cot_pi_42_50_bounds :
  ((cot_pi_42_50_lower : ℚ) : ℝ) ≤ cotangentTermV 42 50 ∧
  cotangentTermV 42 50 ≤ ((cot_pi_42_50_upper : ℚ) : ℝ)

def cot_pi_43_50_lower : ℚ := -299082386773525 / 140737488355328
def cot_pi_43_50_upper : ℚ := -2392659094188183 / 1125899906842624
axiom cot_pi_43_50_bounds :
  ((cot_pi_43_50_lower : ℚ) : ℝ) ≤ cotangentTermV 43 50 ∧
  cotangentTermV 43 50 ≤ ((cot_pi_43_50_upper : ℚ) : ℝ)

def cot_pi_44_50_lower : ℚ := -2843698555860053 / 1125899906842624
def cot_pi_44_50_upper : ℚ := -1421849277930015 / 562949953421312
axiom cot_pi_44_50_bounds :
  ((cot_pi_44_50_lower : ℚ) : ℝ) ≤ cotangentTermV 44 50 ∧
  cotangentTermV 44 50 ≤ ((cot_pi_44_50_upper : ℚ) : ℝ)

def cot_pi_45_50_lower : ℚ := -6930327215593399 / 2251799813685248
def cot_pi_45_50_upper : ℚ := -6930327215593335 / 2251799813685248
axiom cot_pi_45_50_bounds :
  ((cot_pi_45_50_lower : ℚ) : ℝ) ≤ cotangentTermV 45 50 ∧
  cotangentTermV 45 50 ≤ ((cot_pi_45_50_upper : ℚ) : ℝ)

def cot_pi_46_50_lower : ℚ := -4385090617541519 / 1125899906842624
def cot_pi_46_50_upper : ℚ := -4385090617541471 / 1125899906842624
axiom cot_pi_46_50_bounds :
  ((cot_pi_46_50_lower : ℚ) : ℝ) ≤ cotangentTermV 46 50 ∧
  cotangentTermV 46 50 ≤ ((cot_pi_46_50_upper : ℚ) : ℝ)

def cot_pi_47_50_lower : ℚ := -2951087002813637 / 562949953421312
def cot_pi_47_50_upper : ℚ := -2951087002813595 / 562949953421312
axiom cot_pi_47_50_bounds :
  ((cot_pi_47_50_lower : ℚ) : ℝ) ≤ cotangentTermV 47 50 ∧
  cotangentTermV 47 50 ≤ ((cot_pi_47_50_upper : ℚ) : ℝ)

def cot_pi_48_50_lower : ℚ := -4456207735253499 / 562949953421312
def cot_pi_48_50_upper : ℚ := -4456207735253447 / 562949953421312
axiom cot_pi_48_50_bounds :
  ((cot_pi_48_50_lower : ℚ) : ℝ) ≤ cotangentTermV 48 50 ∧
  cotangentTermV 48 50 ≤ ((cot_pi_48_50_upper : ℚ) : ℝ)

def cot_pi_49_50_lower : ℚ := -8947833279507013 / 562949953421312
def cot_pi_49_50_upper : ℚ := -8947833279506653 / 562949953421312
axiom cot_pi_49_50_bounds :
  ((cot_pi_49_50_lower : ℚ) : ℝ) ≤ cotangentTermV 49 50 ∧
  cotangentTermV 49 50 ≤ ((cot_pi_49_50_upper : ℚ) : ℝ)

end RH.Certificates.Generated
