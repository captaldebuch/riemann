import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula

namespace RH.Criteria.NymanBeurling.QuadraticInteraction

open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open RH.Criteria.NymanBeurling.VasyuninGram

-- ---------------------------------------------------------------------------
-- 1. Unified Interaction Kernel
-- ---------------------------------------------------------------------------

/-- The central arithmetic interaction kernel independent of the Möbius cutoff weights.
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

theorem quadraticInteractionKernel_diag_eq_zero (h : ℕ) :
    quadraticInteractionKernel h h = 0 := by
  simp [quadraticInteractionKernel, cotangentSumVFormula_diag_eq_zero]

-- ---------------------------------------------------------------------------
-- 2. Diagonal / Off-Diagonal Split
-- ---------------------------------------------------------------------------

/-- The terms in the weighted interaction sum with equal indices. -/
noncomputable def quadraticInteractionDiagonal (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N h * quadraticInteractionKernel h h

theorem quadraticInteractionDiagonal_eq_zero (N : ℕ) :
    quadraticInteractionDiagonal N = 0 := by
  simp [quadraticInteractionDiagonal, quadraticInteractionKernel_diag_eq_zero]

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

/-- A gcd stratum indexed by a non-squarefree integer vanishes identically. -/
theorem quadraticInteractionGcdSlice_eq_zero_of_not_squarefree
    (N g : ℕ) (hg : ¬ Squarefree g) :
    quadraticInteractionGcdSlice N g = 0 := by
  classical
  unfold quadraticInteractionGcdSlice
  apply Finset.sum_eq_zero
  intro h _
  apply Finset.sum_eq_zero
  intro k _
  split_ifs with hgcd
  · have hgdvdh : g ∣ h := by
      rw [← hgcd]
      exact Nat.gcd_dvd_left h k
    have h_not_squarefree : ¬ Squarefree h := by
      intro hh
      exact hg (hh.squarefree_of_dvd hgdvdh)
    have hmu : ArithmeticFunction.moebius h = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree h_not_squarefree
    simp [cutoffMobiusCoeff, hmu]
  · rfl

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
-- 5. Analytic Sub-Estimate Interfaces
-- ---------------------------------------------------------------------------

/-- The diagonal contribution is negligible at the target logarithmic rate. -/
structure QuadraticInteractionDiagonalEstimate where
  C_diagonal : ℝ
  C_diagonal_nonneg : 0 ≤ C_diagonal
  diagonal_bound :
    ∀ N : ℕ,
      |quadraticInteractionDiagonal N| ≤ C_diagonal / Real.log (N + 2 : ℝ)

/-- The exact-zero diagonal supplies its logarithmic estimate with constant zero. -/
noncomputable def quadraticInteractionDiagonalEstimate_zero :
    QuadraticInteractionDiagonalEstimate := by
  refine ⟨0, le_rfl, ?_⟩
  intro N
  rw [quadraticInteractionDiagonal_eq_zero]
  simp

/--
The limiting main term assigned to each off-diagonal gcd stratum. Its partial
sums account for the target value `1` at the required logarithmic rate.
-/
structure QuadraticInteractionGcdMainTermEstimate where
  mainTerm : ℕ → ℝ
  C_main : ℝ
  C_main_nonneg : 0 ≤ C_main
  main_term_bound :
    ∀ N : ℕ,
      |(∑ g ∈ Finset.Icc 1 N, mainTerm g) - 1| ≤ C_main / Real.log (N + 2 : ℝ)

/--
Each finite-cutoff gcd slice is controlled against its limiting main term by a
nonnegative majorant whose total mass has the target logarithmic decay.
-/
structure QuadraticInteractionGcdSliceErrorEstimate (mainTerm : ℕ → ℝ) where
  errorMajorant : ℕ → ℕ → ℝ
  C_error : ℝ
  C_error_nonneg : 0 ≤ C_error
  errorMajorant_nonneg : ∀ N g : ℕ, 0 ≤ errorMajorant N g
  slice_error_bound :
    ∀ N g : ℕ,
      g ∈ Finset.Icc 1 N →
        |quadraticInteractionOffDiagonalGcdSlice N g - mainTerm g| ≤ errorMajorant N g
  error_mass_bound :
    ∀ N : ℕ,
      (∑ g ∈ Finset.Icc 1 N, errorMajorant N g) ≤ C_error / Real.log (N + 2 : ℝ)

/--
The Phase 15D analytic debts, bundled without yet deriving the global
`QuadraticInteractionEstimates` interface. That synthesis is reserved for Phase 15E.
-/
structure QuadraticInteractionAnalyticSubEstimates where
  diagonal : QuadraticInteractionDiagonalEstimate
  gcdMain : QuadraticInteractionGcdMainTermEstimate
  gcdError : QuadraticInteractionGcdSliceErrorEstimate gcdMain.mainTerm

-- ---------------------------------------------------------------------------
-- 5a. BBLS / Estermann Contour Package Interface
-- ---------------------------------------------------------------------------

/--
Structural interface for the Báez-Duarte--Balazard--Landreau--Saias
autocorrelation/Estermann contour input relevant to the quadratic interaction.

This is intentionally only a dependency package, not an attempted proof of the
contour argument.  The current Lean kernel is

`((k-h)/(2hk))*log(h/k) - (π/(2hk))*(V(h,k)+V(k,h))`.

For coprime positive `h,k`, BBLS Proposition 89 gives

`A(h/k)/h =
  quadraticInteractionKernel h k
    + ((log(2π)-γ)/2) * (1/h + 1/k)`.

Thus the BBLS autocorrelation main term lines up with this file only after
respecting the existing split between the log-gamma component and the
log/cotangent interaction kernel.  The package below records the three analytic
inputs expected from the Mellin/Estermann contour method, plus the extracted
gcd-main-term estimate that H15 can consume.  It deliberately does **not**
include the gcd-slice error estimate, which is the separate Möbius-correlation
problem.
-/
structure BBLS_EstermannContourPackage where
  /--
  BBLS Proposition 86: the Mellin transform formula for the multiplicative
  fractional-part autocorrelation `A`, namely
  `M_A(s) = -ζ(-s)ζ(s+1)/(s(s+1))` on `-1 < Re s < 0`, expressed in whatever
  eventual Mellin-transform API this project adopts.
  -/
  mellin_transform_formula : Prop
  /--
  The residue/double-pole computation at `s = 0` for the contour-shifted
  integrand, producing the explicit main term that matches the BBLS
  Proposition 89 normalization after subtracting this file's log-gamma split.
  -/
  double_pole_residue_formula : Prop
  /--
  The vertical-strip growth bound for the Estermann side, of the kind used in
  BBLS Proposition 66, sufficient to justify the contour shift.
  -/
  vertical_strip_growth_bound : Prop
  mellin_transform_formula_holds : mellin_transform_formula
  double_pole_residue_formula_holds : double_pole_residue_formula
  vertical_strip_growth_bound_holds : vertical_strip_growth_bound
  mainTerm : ℕ → ℝ
  C_main : ℝ
  C_main_nonneg : 0 ≤ C_main
  /--
  The H15-level consequence of the BBLS residue extraction: the proposed gcd
  main terms sum to the target value `1` at the logarithmic rate required by
  `QuadraticInteractionGcdMainTermEstimate`.

  Proving this field from the preceding analytic fields is future Mellin/
  contour infrastructure.  Once supplied, the bridge below is purely structural.
  -/
  main_term_bound :
    ∀ N : ℕ,
      |(∑ g ∈ Finset.Icc 1 N, mainTerm g) - 1| ≤ C_main / Real.log (N + 2 : ℝ)

/-- The BBLS/Estermann contour package discharges the gcd-main-term subestimate. -/
noncomputable def quadraticInteractionGcdMainTermEstimate_of_BBLS
    (H : BBLS_EstermannContourPackage) :
    QuadraticInteractionGcdMainTermEstimate :=
  { mainTerm := H.mainTerm
    C_main := H.C_main
    C_main_nonneg := H.C_main_nonneg
    main_term_bound := H.main_term_bound }

/--
BBLS contour input plus a separately supplied gcd-slice error estimate gives
the full analytic-subestimate package.  The diagonal component is already
unconditional (`quadraticInteractionDiagonalEstimate_zero`); the remaining
separate input is exactly the uniform Möbius-weighted slice-error estimate.
-/
noncomputable def quadraticInteractionAnalyticSubEstimates_of_BBLS_and_gcdError
    (H : BBLS_EstermannContourPackage)
    (E : QuadraticInteractionGcdSliceErrorEstimate H.mainTerm) :
    QuadraticInteractionAnalyticSubEstimates :=
  { diagonal := quadraticInteractionDiagonalEstimate_zero
    gcdMain := quadraticInteractionGcdMainTermEstimate_of_BBLS H
    gcdError := E }

-- ---------------------------------------------------------------------------
-- 5b. Farey-Cell Möbius Correlation Interface
-- ---------------------------------------------------------------------------

/--
The two-linear-forms Möbius correlation sum expected after decomposing a gcd
slice into Farey cells.  The parameters `a/q` describe the Farey approximant,
`r,s` are residue offsets, and `w` is the real kernel/cutoff weight left over
from the quadratic interaction on that cell.

The point of this definition is that the arithmetic obstruction is genuinely a
binary correlation

`μ(a*m+r) * μ(q*m+s)`,

not a one-dimensional arithmetic-progression or Bombieri--Vinogradov-type
estimate.
-/
noncomputable def fareyCellMobiusCorrelationSum
    (a q r s M : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M,
    ((ArithmeticFunction.moebius (a * m + r) : ℤ) : ℝ) *
      ((ArithmeticFunction.moebius (q * m + s) : ℤ) : ℝ) * w m

/-- The `ℓ¹` size of the cell weight over the active parameter interval. -/
noncomputable def fareyCellWeightL1 (M : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, |w m|

/--
The pointwise logarithmic saving predicted for one Farey-cell correlation sum.
The global H15 error still needs a separate summation/decomposition hypothesis:
there are many cells, and their weights must have summable total mass.
-/
noncomputable def fareyCellLogSavingMajorant
    (C : ℝ) (N M : ℕ) (w : ℕ → ℝ) : ℝ :=
  C * fareyCellWeightL1 M w / Real.log (N + 2 : ℝ)

/--
Finite summation over the Farey-cell parameters relevant to the `g`-scaled
off-diagonal slice.  For a slice with `h = g*x`, `k = g*y`, the scaled variables
`x,y` are at most `N/g`; hence the Farey order and all cell lengths are bounded
by `N/g`.
-/
noncomputable def fareyCellParameterSum
    (N g : ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / g),
    ∑ q ∈ (Finset.Icc 1 (N / g)).filter (fun q => Nat.Coprime a q),
      ∑ r ∈ Finset.range a,
        ∑ s ∈ Finset.range q,
          ∑ M ∈ Finset.Icc 1 (N / g), F a q r s M

/--
The genuine arithmetic input needed by the Farey-cell approach: a uniform
log-saving estimate for Möbius evaluated on two independent affine-linear
forms.

This is deliberately stronger and more specific than
`QuadraticInteractionGcdSliceErrorEstimate`.  It does not mention the H15 kernel
or gcd slices; it only states the binary Möbius-correlation estimate that a
future analytic proof would have to supply.  The surrounding parameter ranges
are those arising from `quadraticInteractionOffDiagonalGcdSlice` after the
scaling `h = g*x`, `k = g*y` and a Farey decomposition of the coprime pair
`x/y`.
-/
structure FareyCellMobiusCorrelationEstimate where
  C_correlation : ℝ
  C_correlation_nonneg : 0 ≤ C_correlation
  correlation_bound :
    ∀ N g a q r s M : ℕ,
      ∀ w : ℕ → ℝ,
        g ∈ Finset.Icc 1 N →
          a ∈ Finset.Icc 1 (N / g) →
            q ∈ Finset.Icc 1 (N / g) →
              Nat.Coprime a q →
                r < a →
                  s < q →
                    M ∈ Finset.Icc 1 (N / g) →
                      |fareyCellMobiusCorrelationSum a q r s M w| ≤
                        fareyCellLogSavingMajorant C_correlation N M w

/--
The combinatorial and weight bookkeeping that connects Farey-cell correlations
back to the concrete H15 gcd-slice error.

This is a separate package because it is not merely a tactic-level rewrite:
formalizing the Farey partition of the off-diagonal coprime pairs, extracting
the exact cell weights from `quadraticInteractionKernel`, and proving their
summed log-saving majorants are all substantial infrastructure.  The fields
below isolate that infrastructure without pretending to prove the hard binary
Möbius-correlation estimate itself.
-/
structure FareyCellGcdSliceErrorDecomposition
    (Hcorr : FareyCellMobiusCorrelationEstimate) (mainTerm : ℕ → ℝ) where
  /--
  The real weight attached to a Farey cell.  It absorbs the cutoff factors, the
  log/cotangent interaction kernel, the fixed gcd `g`, and any squarefree or
  coprimality indicators needed to convert `μ(g*x) μ(g*y)` into the primitive
  two-linear-forms correlation.
  -/
  cellWeight : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ
  errorMajorant : ℕ → ℕ → ℝ
  C_error : ℝ
  C_error_nonneg : 0 ≤ C_error
  errorMajorant_nonneg : ∀ N g : ℕ, 0 ≤ errorMajorant N g
  /--
  Exact Farey-cell decomposition of one finite gcd slice after subtracting its
  BBLS-supplied limiting main term.
  -/
  farey_cell_decomposition :
    ∀ N g : ℕ,
      g ∈ Finset.Icc 1 N →
        quadraticInteractionOffDiagonalGcdSlice N g - mainTerm g =
          fareyCellParameterSum N g (fun a q r s M =>
            fareyCellMobiusCorrelationSum a q r s M
              (cellWeight N g a q r s M))
  /--
  The finite triangle-inequality and cellwise correlation step: applying
  `Hcorr.correlation_bound` over all relevant Farey cells is enough to dominate
  the decomposed slice by the sum of the cell log-saving majorants.
  -/
  farey_cell_correlation_bound :
    ∀ N g : ℕ,
      g ∈ Finset.Icc 1 N →
        |fareyCellParameterSum N g (fun a q r s M =>
          fareyCellMobiusCorrelationSum a q r s M
            (cellWeight N g a q r s M))| ≤
          fareyCellParameterSum N g (fun a q r s M =>
            fareyCellLogSavingMajorant Hcorr.C_correlation N M
              (cellWeight N g a q r s M))
  /--
  The remaining Farey-cell mass bookkeeping: once every cell has its
  log-saving majorant, their total contribution to this gcd slice is controlled
  by `errorMajorant`.
  -/
  farey_cell_majorant_bound :
    ∀ N g : ℕ,
      g ∈ Finset.Icc 1 N →
        fareyCellParameterSum N g (fun a q r s M =>
          fareyCellLogSavingMajorant Hcorr.C_correlation N M
            (cellWeight N g a q r s M)) ≤ errorMajorant N g
  error_mass_bound :
    ∀ N : ℕ,
      (∑ g ∈ Finset.Icc 1 N, errorMajorant N g) ≤
        C_error / Real.log (N + 2 : ℝ)

/--
Farey-cell binary Möbius-correlation input, together with the explicit
decomposition/weight bookkeeping, supplies the abstract H15 gcd-slice error
estimate.
-/
noncomputable def quadraticInteractionGcdSliceErrorEstimate_of_fareyCellCorrelation
    (Hcorr : FareyCellMobiusCorrelationEstimate) (mainTerm : ℕ → ℝ)
    (D : FareyCellGcdSliceErrorDecomposition Hcorr mainTerm) :
    QuadraticInteractionGcdSliceErrorEstimate mainTerm :=
  { errorMajorant := D.errorMajorant
    C_error := D.C_error
    C_error_nonneg := D.C_error_nonneg
    errorMajorant_nonneg := D.errorMajorant_nonneg
    slice_error_bound := by
      intro N g hg
      rw [D.farey_cell_decomposition N g hg]
      exact (D.farey_cell_correlation_bound N g hg).trans
        (D.farey_cell_majorant_bound N g hg)
    error_mass_bound := D.error_mass_bound }

-- ---------------------------------------------------------------------------
-- 6. Formal Reductions
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
-- 7. The Isolated Hard Remainder Target
-- ---------------------------------------------------------------------------

/-- The core remaining analytic estimate target:
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

theorem explicitQuadraticInteractionRemainder_eq_diagonal_add_sum_offDiagonalGcdSlices
    (N : ℕ) :
    explicitQuadraticInteractionRemainder N =
      quadraticInteractionDiagonal N +
        (∑ g ∈ Finset.Icc 1 N, quadraticInteractionOffDiagonalGcdSlice N g) - 1 := by
  rw [explicitQuadraticInteractionRemainder_eq_diagonal_add_offDiagonal,
    quadraticInteractionOffDiagonal_eq_sum_gcdSlices]

theorem explicitQuadraticInteractionRemainder_eq_sum_gcdSlices (N : ℕ) :
    explicitQuadraticInteractionRemainder N =
      (∑ g ∈ Finset.Icc 1 N, quadraticInteractionGcdSlice N g) - 1 := by
  rw [explicitQuadraticInteractionRemainder_eq_kernel_sum,
    quadraticInteractionKernelSum_eq_sum_gcdSlices]

-- ---------------------------------------------------------------------------
-- 8. Analytic Synthesis (Phase 15E)
-- ---------------------------------------------------------------------------

/--
The three Phase 15D hypotheses imply the interaction-remainder field required
by `QuadraticInteractionEstimates`. This is finite-sum and triangle-inequality wiring.
-/
theorem explicitQuadraticInteractionRemainder_bound_of_analytic_subEstimates
    (H : QuadraticInteractionAnalyticSubEstimates) (N : ℕ) :
    |explicitQuadraticInteractionRemainder N| ≤
      (H.diagonal.C_diagonal + H.gcdError.C_error + H.gcdMain.C_main) /
        Real.log (N + 2 : ℝ) := by
  rw [explicitQuadraticInteractionRemainder_eq_diagonal_add_sum_offDiagonalGcdSlices]
  have hdecomp :
      quadraticInteractionDiagonal N +
          (∑ g ∈ Finset.Icc 1 N, quadraticInteractionOffDiagonalGcdSlice N g) - 1 =
        quadraticInteractionDiagonal N +
          (∑ g ∈ Finset.Icc 1 N,
            (quadraticInteractionOffDiagonalGcdSlice N g - H.gcdMain.mainTerm g)) +
          ((∑ g ∈ Finset.Icc 1 N, H.gcdMain.mainTerm g) - 1) := by
    rw [Finset.sum_sub_distrib]
    abel
  rw [hdecomp]
  have hslice :
      |∑ g ∈ Finset.Icc 1 N,
          (quadraticInteractionOffDiagonalGcdSlice N g - H.gcdMain.mainTerm g)| ≤
        ∑ g ∈ Finset.Icc 1 N, H.gcdError.errorMajorant N g := by
    calc
      |∑ g ∈ Finset.Icc 1 N,
          (quadraticInteractionOffDiagonalGcdSlice N g - H.gcdMain.mainTerm g)|
          ≤ ∑ g ∈ Finset.Icc 1 N,
              |quadraticInteractionOffDiagonalGcdSlice N g - H.gcdMain.mainTerm g| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ g ∈ Finset.Icc 1 N, H.gcdError.errorMajorant N g := by
        exact Finset.sum_le_sum fun g hg => H.gcdError.slice_error_bound N g hg
  calc
    |quadraticInteractionDiagonal N +
        (∑ g ∈ Finset.Icc 1 N,
          (quadraticInteractionOffDiagonalGcdSlice N g - H.gcdMain.mainTerm g)) +
        ((∑ g ∈ Finset.Icc 1 N, H.gcdMain.mainTerm g) - 1)|
        ≤ |quadraticInteractionDiagonal N| +
            |∑ g ∈ Finset.Icc 1 N,
              (quadraticInteractionOffDiagonalGcdSlice N g - H.gcdMain.mainTerm g)| +
            |(∑ g ∈ Finset.Icc 1 N, H.gcdMain.mainTerm g) - 1| := by
          exact (abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ H.diagonal.C_diagonal / Real.log (N + 2 : ℝ) +
          (∑ g ∈ Finset.Icc 1 N, H.gcdError.errorMajorant N g) +
          H.gcdMain.C_main / Real.log (N + 2 : ℝ) :=
      add_le_add (add_le_add (H.diagonal.diagonal_bound N) hslice)
        (H.gcdMain.main_term_bound N)
    _ ≤ H.diagonal.C_diagonal / Real.log (N + 2 : ℝ) +
          H.gcdError.C_error / Real.log (N + 2 : ℝ) +
          H.gcdMain.C_main / Real.log (N + 2 : ℝ) :=
      add_le_add (add_le_add le_rfl (H.gcdError.error_mass_bound N)) le_rfl
    _ = (H.diagonal.C_diagonal + H.gcdError.C_error + H.gcdMain.C_main) /
          Real.log (N + 2 : ℝ) := by rw [add_div, add_div]

/-- Package the interaction bridge with independently supplied log-gamma and residue bounds. -/
noncomputable def quadraticInteractionEstimates_of_analytic_subEstimates
    (H : QuadraticInteractionAnalyticSubEstimates)
    (C_loggamma C_residue : ℝ)
    (C_pos :
      0 < C_loggamma +
        (H.diagonal.C_diagonal + H.gcdError.C_error + H.gcdMain.C_main) + C_residue)
    (loggamma_bound :
      ∀ N : ℕ,
        |explicitQuadraticLogGammaComponent N| ≤ C_loggamma / Real.log (N + 2 : ℝ))
    (residue_bound :
      ∀ N : ℕ,
        |explicitCutoffResidueComponent N| ≤ C_residue / Real.log (N + 2 : ℝ)) :
    QuadraticInteractionEstimates := by
  refine ⟨C_loggamma,
    H.diagonal.C_diagonal + H.gcdError.C_error + H.gcdMain.C_main,
    C_residue, C_pos, loggamma_bound, ?_, residue_bound⟩
  exact explicitQuadraticInteractionRemainder_bound_of_analytic_subEstimates H

end RH.Criteria.NymanBeurling.QuadraticInteraction
