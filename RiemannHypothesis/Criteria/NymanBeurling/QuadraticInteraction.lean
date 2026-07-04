import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open RH.Criteria.NymanBeurling.VasyuninGram

-- ---------------------------------------------------------------------------
-- 1. Unified Interaction Kernel
-- ---------------------------------------------------------------------------

/--
  The central arithmetic interaction kernel independent of the Möbius cutoff weights.
  It combines the log-ratio and the fractional cotangent sum, which are individually large
  but cancel heavily to approximate 1 when summed against the Möbius cutoff.
-/
noncomputable def quadraticInteractionKernel (h k : ℕ) : ℝ :=
  (((k : ℝ) - (h : ℝ)) / (2 * (h : ℝ) * (k : ℝ)) * Real.log ((h : ℝ) / (k : ℝ)))
    - (Real.pi / (2 * (h : ℝ) * (k : ℝ)) * (cotangentSumVFormula h k + cotangentSumVFormula k h))

theorem quadraticInteractionKernel_symm (h k : ℕ) :
    quadraticInteractionKernel h k = quadraticInteractionKernel k h := by
  by_cases hh : h = 0
  · subst h
    simp [quadraticInteractionKernel]
  by_cases hk : k = 0
  · subst k
    simp [quadraticInteractionKernel]
  unfold quadraticInteractionKernel
  rw [Real.log_div (Nat.cast_ne_zero.mpr hh) (Nat.cast_ne_zero.mpr hk),
    Real.log_div (Nat.cast_ne_zero.mpr hk) (Nat.cast_ne_zero.mpr hh)]
  ring

-- ---------------------------------------------------------------------------
-- 2. Diagonal / Off-Diagonal Split
-- ---------------------------------------------------------------------------

/-- The terms in the weighted interaction sum with equal indices. -/
noncomputable def quadraticInteractionDiagonal (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N h * quadraticInteractionKernel h h

/-- The terms in the weighted interaction sum with distinct indices. -/
noncomputable def quadraticInteractionOffDiagonal (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ (Finset.Icc 1 N).erase h,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k

theorem quadraticInteractionKernelSum_eq_diagonal_add_offDiagonal (N : ℕ) :
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k) =
      quadraticInteractionDiagonal N + quadraticInteractionOffDiagonal N := by
  unfold quadraticInteractionDiagonal quadraticInteractionOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  exact (Finset.add_sum_erase (Finset.Icc 1 N)
    (fun k => cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
      quadraticInteractionKernel h k) hh).symm

-- ---------------------------------------------------------------------------
-- 3. GCD Stratification
-- ---------------------------------------------------------------------------

/-- The weighted interaction terms whose two indices have gcd exactly `g`. -/
noncomputable def quadraticInteractionGcdSlice (N g : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    if Nat.gcd h k = g then
      cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k
    else 0

theorem quadraticInteractionKernelSum_eq_sum_gcdSlices (N : ℕ) :
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k) =
      ∑ g ∈ Finset.Icc 1 N, quadraticInteractionGcdSlice N g := by
  symm
  unfold quadraticInteractionGcdSlice
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rcases Finset.mem_Icc.mp hh with ⟨h1, hN⟩
  have hhpos : 0 < h := lt_of_lt_of_le Nat.zero_lt_one h1
  have hgcd_mem : Nat.gcd h k ∈ Finset.Icc 1 N :=
    Finset.mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left k hhpos,
      (Nat.gcd_le_left k hhpos).trans hN⟩
  simp only [Finset.sum_ite_eq, if_pos hgcd_mem]

/-- The `g`-scaled interaction terms indexed by coprime positive pairs. -/
noncomputable def quadraticInteractionCoprimeScaledSlice (N g : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g), ∑ b ∈ Finset.Icc 1 (N / g),
    if Nat.Coprime a b then
      cutoffMobiusCoeff N (g * a) * cutoffMobiusCoeff N (g * b) *
        quadraticInteractionKernel (g * a) (g * b)
    else 0

/-- A positive gcd slice is exactly its reindexing by coprime pairs `h = g * a`, `k = g * b`. -/
theorem quadraticInteractionGcdSlice_eq_coprimeScaled (N g : ℕ) (hg : 0 < g) :
    quadraticInteractionGcdSlice N g = quadraticInteractionCoprimeScaledSlice N g := by
  classical
  let S := Finset.Icc 1 N
  let T := Finset.Icc 1 (N / g)
  let F : ℕ × ℕ → ℝ := fun p =>
    cutoffMobiusCoeff N p.1 * cutoffMobiusCoeff N p.2 *
      quadraticInteractionKernel p.1 p.2
  let scaledF : ℕ × ℕ → ℝ := fun p =>
    cutoffMobiusCoeff N (g * p.1) * cutoffMobiusCoeff N (g * p.2) *
      quadraticInteractionKernel (g * p.1) (g * p.2)
  calc
    quadraticInteractionGcdSlice N g =
        ∑ p ∈ (S ×ˢ S).filter (fun p => Nat.gcd p.1 p.2 = g), F p := by
      unfold quadraticInteractionGcdSlice
      dsimp [S, F]
      rw [Finset.sum_filter, Finset.sum_product]
    _ = ∑ p ∈ (T ×ˢ T).filter (fun p => Nat.Coprime p.1 p.2), scaledF p := by
      symm
      apply Finset.sum_bij (fun p _ => (g * p.1, g * p.2))
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpbox, hcop⟩
        rcases Finset.mem_product.mp hpbox with ⟨hpa, hpb⟩
        rcases Finset.mem_Icc.mp hpa with ⟨ha1, haN⟩
        rcases Finset.mem_Icc.mp hpb with ⟨hb1, hbN⟩
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_product.mpr
          constructor
          · apply Finset.mem_Icc.mpr
            constructor
            · exact Nat.one_le_iff_ne_zero.mpr
                (Nat.mul_ne_zero (Nat.ne_of_gt hg)
                  (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one ha1)))
            · have ha_mul := (Nat.le_div_iff_mul_le hg).mp haN
              simpa [Nat.mul_comm] using ha_mul
          · apply Finset.mem_Icc.mpr
            constructor
            · exact Nat.one_le_iff_ne_zero.mpr
                (Nat.mul_ne_zero (Nat.ne_of_gt hg)
                  (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hb1)))
            · have hb_mul := (Nat.le_div_iff_mul_le hg).mp hbN
              simpa [Nat.mul_comm] using hb_mul
        · rw [Nat.gcd_mul_left, hcop.gcd_eq_one, Nat.mul_one]
      · intro p _ q _ hpq
        apply Prod.ext
        · exact Nat.mul_left_cancel hg (congrArg Prod.fst hpq)
        · exact Nat.mul_left_cancel hg (congrArg Prod.snd hpq)
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpbox, hpgcd⟩
        rcases Finset.mem_product.mp hpbox with ⟨hph, hpk⟩
        rcases Finset.mem_Icc.mp hph with ⟨hh1, hhN⟩
        rcases Finset.mem_Icc.mp hpk with ⟨hk1, hkN⟩
        have hhpos : 0 < p.1 := lt_of_lt_of_le Nat.zero_lt_one hh1
        have hkpos : 0 < p.2 := lt_of_lt_of_le Nat.zero_lt_one hk1
        have hdvdh : g ∣ p.1 := by
          rw [← hpgcd]
          exact Nat.gcd_dvd_left _ _
        have hdvdk : g ∣ p.2 := by
          rw [← hpgcd]
          exact Nat.gcd_dvd_right _ _
        have hg_le_h : g ≤ p.1 := by
          rw [← hpgcd]
          exact Nat.gcd_le_left _ hhpos
        have hg_le_k : g ≤ p.2 := by
          rw [← hpgcd]
          exact Nat.gcd_le_right _ hkpos
        have hreconh : g * (p.1 / g) = p.1 := by
          rw [Nat.mul_comm]
          exact Nat.div_mul_cancel hdvdh
        have hreconk : g * (p.2 / g) = p.2 := by
          rw [Nat.mul_comm]
          exact Nat.div_mul_cancel hdvdk
        refine ⟨(p.1 / g, p.2 / g), ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          constructor
          · apply Finset.mem_product.mpr
            constructor
            · exact Finset.mem_Icc.mpr
                ⟨Nat.div_pos hg_le_h hg, Nat.div_le_div_right hhN⟩
            · exact Finset.mem_Icc.mpr
                ⟨Nat.div_pos hg_le_k hg, Nat.div_le_div_right hkN⟩
          · apply Nat.coprime_iff_gcd_eq_one.mpr
            apply Nat.mul_left_cancel hg
            rw [← Nat.gcd_mul_left, hreconh, hreconk, hpgcd, Nat.mul_one]
        · apply Prod.ext
          · exact hreconh
          · exact hreconk
      · intro p _
        rfl
    _ = quadraticInteractionCoprimeScaledSlice N g := by
      unfold quadraticInteractionCoprimeScaledSlice
      dsimp [T, scaledF]
      rw [Finset.sum_filter, Finset.sum_product]

-- ---------------------------------------------------------------------------
-- 4. Off-Diagonal GCD Stratification
-- ---------------------------------------------------------------------------

/-- The off-diagonal weighted interaction terms whose indices have gcd exactly `g`. -/
noncomputable def quadraticInteractionOffDiagonalGcdSlice (N g : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ (Finset.Icc 1 N).erase h,
    if Nat.gcd h k = g then
      cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k
    else 0

theorem quadraticInteractionOffDiagonal_eq_sum_gcdSlices (N : ℕ) :
    quadraticInteractionOffDiagonal N =
      ∑ g ∈ Finset.Icc 1 N, quadraticInteractionOffDiagonalGcdSlice N g := by
  symm
  unfold quadraticInteractionOffDiagonal quadraticInteractionOffDiagonalGcdSlice
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rcases Finset.mem_Icc.mp hh with ⟨h1, hN⟩
  have hhpos : 0 < h := lt_of_lt_of_le Nat.zero_lt_one h1
  have hgcd_mem : Nat.gcd h k ∈ Finset.Icc 1 N :=
    Finset.mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left k hhpos,
      (Nat.gcd_le_left k hhpos).trans hN⟩
  simp only [Finset.sum_ite_eq, if_pos hgcd_mem]

-- ---------------------------------------------------------------------------
-- 5. Formal Reductions
-- ---------------------------------------------------------------------------

theorem explicitQuadraticLogCotangentInteraction_eq_unified_sum (N : ℕ) :
    explicitQuadraticLogCotangentInteraction N =
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k := by
  unfold explicitQuadraticLogCotangentInteraction
  unfold explicitQuadraticLogRatioComponent explicitQuadraticCotangentComponent
  unfold quadraticInteractionKernel
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

-- ---------------------------------------------------------------------------
-- 6. The Isolated Hard Remainder Target
-- ---------------------------------------------------------------------------

/--
  The core remaining analytic estimate target:
  The double sum over the interaction kernel must converge to 1
  with an error rate of O(1/log N).
-/
theorem explicitQuadraticInteractionRemainder_eq_kernel_sum (N : ℕ) :
    explicitQuadraticInteractionRemainder N =
      (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        cutoffMobiusCoeff N h * cutoffMobiusCoeff N k * quadraticInteractionKernel h k) - 1 := by
  unfold explicitQuadraticInteractionRemainder
  rw [explicitQuadraticLogCotangentInteraction_eq_unified_sum N]

theorem explicitQuadraticInteractionRemainder_eq_diagonal_add_offDiagonal (N : ℕ) :
    explicitQuadraticInteractionRemainder N =
      quadraticInteractionDiagonal N + quadraticInteractionOffDiagonal N - 1 := by
  rw [explicitQuadraticInteractionRemainder_eq_kernel_sum,
    quadraticInteractionKernelSum_eq_diagonal_add_offDiagonal]

theorem explicitQuadraticInteractionRemainder_eq_sum_gcdSlices (N : ℕ) :
    explicitQuadraticInteractionRemainder N =
      (∑ g ∈ Finset.Icc 1 N, quadraticInteractionGcdSlice N g) - 1 := by
  rw [explicitQuadraticInteractionRemainder_eq_kernel_sum,
    quadraticInteractionKernelSum_eq_sum_gcdSlices]

end RH.Criteria.NymanBeurling.QuadraticInteraction
