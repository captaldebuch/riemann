import RiemannHypothesis.Criteria.NymanBeurling.H14ZetaFETransport

/-!
# A2: boundary identities for the functional-equation factor

The reflection-formula algebra and the two boundary moduli are unconditional.
The interior interpolation estimate is isolated in `FEFactorInteriorInterpolation`:
Mathlib does not currently expose the required vertical-strip Gamma estimate.
-/

namespace RH.Criteria.NymanBeurling.H14ZetaFETransport

open Complex MeasureTheory Set Filter Topology

/-- Reflection-formula inversion of the functional-equation factor off the real axis. -/
theorem zetaFEFactor_mul_complement {w : ℂ} (hw : w.im ≠ 0) :
    zetaFEFactor w * zetaFEFactor (1 - w) = 1 := by
  unfold zetaFEFactor
  have hsin : Complex.sin (Real.pi * w) ≠ 0 := by
    intro h
    rw [Complex.sin_eq_zero_iff] at h
    rcases h with ⟨n, hn⟩
    have him : w.im = 0 := by
      have h' := congrArg Complex.im hn
      simp at h'
      linarith
    exact hw him
  have hpow :
      (2 * (Real.pi : ℂ)) ^ (w - 1) *
          (2 * (Real.pi : ℂ)) ^ ((1 - w) - 1) = 1 := by
    rw [← Complex.cpow_add]
    · simp
    · norm_num
  have htrig :
      Complex.cos (Real.pi * (1 - w) / 2) *
          Complex.cos (Real.pi * (1 - (1 - w)) / 2) =
        Complex.sin (Real.pi * w) / 2 := by
    rw [show (1 - (1 - w) : ℂ) = w by ring]
    rw [show (Real.pi : ℂ) * (1 - w) / 2 =
        (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * w / 2 by ring]
    rw [Complex.cos_sub]
    rw [show Complex.cos (Real.pi / 2) = 0 by
      rw [Complex.cos_ofReal]
      norm_num,
      show Complex.sin (Real.pi / 2) = 1 by
        rw [Complex.sin_ofReal]
        norm_num]
    rw [Complex.sin_two_mul]
    ring
  rw [show (1 - w) - 1 = -w by ring]
  rw [hpow]
  rw [show 1 - (1 - w) = w by ring]
  rw [← Complex.Gamma_mul_Gamma_one_sub (1 - w)]
  rw [htrig]
  field_simp [hsin]
  ring

/-- Conjugation symmetry of the factor (the base `2π` is positive real). -/
theorem zetaFEFactor_conj (w : ℂ) :
    zetaFEFactor (conj w) = conj (zetaFEFactor w) := by
  unfold zetaFEFactor
  rw [map_mul, map_mul, map_mul]
  rw [Complex.cpow_conj]
  · rw [Complex.Gamma_conj, Complex.cos_conj]
    congr 2 <;> push_cast <;> ring
  · norm_num [Complex.arg_ofReal_of_pos]

/-- The factor is unimodular on the critical boundary line. -/
theorem zetaFEFactor_half_norm {t : ℝ} (ht : t ≠ 0) :
    ‖zetaFEFactor ((1 / 2 : ℝ) + Complex.I * t : ℂ)‖ = 1 := by
  let w : ℂ := (1 / 2 : ℝ) + Complex.I * t
  have him : w.im ≠ 0 := by
    dsimp [w]
    rw [im_sigma_add_I_mul]
    simpa using ht
  have hcomp : (1 : ℂ) - w = conj w := by
    dsimp [w]
    apply Complex.ext <;> simp <;> ring
  have hinv := zetaFEFactor_mul_complement him
  have hconj := zetaFEFactor_conj w
  rw [hcomp, hconj] at hinv
  have hsq : ‖zetaFEFactor w‖ ^ 2 = 1 := by
    rw [← norm_mul, hinv]
    norm_num
  have hnorm : ‖zetaFEFactor w‖ = 1 := by
    nlinarith [norm_nonneg (zetaFEFactor w)]
  exact hnorm

lemma sin_pi_half_add_I_mul (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) * ((1 / 2 : ℝ) + Complex.I * t)) =
      (Real.cosh (Real.pi * t) : ℂ) := by
  rw [show (Real.pi : ℂ) * ((1 / 2 : ℝ) + Complex.I * t) =
      (Real.pi / 2 : ℂ) + (Real.pi * t) * Complex.I by push_cast; ring]
  rw [Complex.sin_add_mul_I]
  rw [show Complex.sin (Real.pi / 2) = 1 by
    rw [Complex.sin_ofReal]
    norm_num,
    show Complex.cos (Real.pi / 2) = 0 by
      rw [Complex.cos_ofReal]
      norm_num]
  simp [Complex.ofReal_cosh]

lemma normSq_cos_three_half_sub_I_mul (t : ℝ) :
    Complex.normSq (Complex.cos ((Real.pi : ℂ) *
      ((3 / 2 : ℝ) - Complex.I * t) / 2)) = Real.cosh (Real.pi * t) / 2 := by
  rw [show (Real.pi : ℂ) * ((3 / 2 : ℝ) - Complex.I * t) / 2 =
      (3 * Real.pi / 4 : ℂ) + (-Real.pi * t / 2) * Complex.I by
        push_cast
        ring]
  rw [Complex.cos_add_mul_I, Complex.normSq_sub_mul_I]
  rw [Complex.cos_ofReal, Complex.sin_ofReal]
  rw [show (3 * Real.pi / 4 : ℝ) = Real.pi - Real.pi / 4 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.cosh_sq]
  ring

lemma normSq_gamma_half_add_I_mul (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℝ) + Complex.I * t)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := by
  let a : ℂ := (1 / 2 : ℝ) + Complex.I * t
  have ha : (1 - a) = conj a := by
    dsimp [a]
    apply Complex.ext <;> simp <;> ring
  have hgamma := Complex.Gamma_mul_Gamma_one_sub a
  rw [ha, Complex.Gamma_conj] at hgamma
  have hsin : Complex.sin (Real.pi * a) = (Real.cosh (Real.pi * t) : ℂ) := by
    exact sin_pi_half_add_I_mul t
  rw [hsin] at hgamma
  have hnorm : (‖Complex.Gamma a‖ ^ 2 : ℂ) =
      Complex.Gamma a * conj (Complex.Gamma a) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    ring
  have hnorm' := congrArg Complex.re hnorm
  have hgamma' := congrArg Complex.re hgamma
  simp at hnorm' hgamma'
  dsimp [a] at hnorm' ⊢
  rw [← hnorm']
  exact hgamma'

/-- Exact modulus on the left boundary `Re w = -1/2`. -/
theorem zetaFEFactor_minus_half_norm {t : ℝ} (ht : t ≠ 0) :
    ‖zetaFEFactor (-(1 / 2 : ℝ) + Complex.I * t : ℂ)‖ =
      ‖(1 / 2 : ℝ) - Complex.I * t‖ / (2 * Real.pi) := by
  let w : ℂ := -(1 / 2 : ℝ) + Complex.I * t
  have hbase : 0 < (2 * Real.pi : ℝ) := by positivity
  have hgamma_add :
      ‖Complex.Gamma ((3 / 2 : ℝ) - Complex.I * t)‖ ^ 2 =
        ((1 / 2 : ℝ) ^ 2 + t ^ 2) *
          (Real.pi / Real.cosh (Real.pi * (-t))) := by
    have hz : ((1 / 2 : ℝ) - Complex.I * t : ℂ) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact ht (by linarith)
    have hg := Complex.Gamma_add_one ((1 / 2 : ℝ) - Complex.I * t) hz
    have hn := normSq_gamma_half_add_I_mul (-t)
    rw [show ((1 / 2 : ℝ) - Complex.I * t : ℂ) + 1 =
        (3 / 2 : ℝ) - Complex.I * t by push_cast; ring] at hg
    rw [hg, norm_mul]
    rw [show ‖((1 / 2 : ℝ) - Complex.I * t : ℂ)‖ ^ 2 =
        (1 / 2 : ℝ) ^ 2 + t ^ 2 by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
      ring]
    rw [← Real.cosh_neg]
    exact congrArg (fun x : ℝ => x) hn
  have hcos :
      ‖Complex.cos ((Real.pi : ℂ) *
          ((3 / 2 : ℝ) - Complex.I * t) / 2)‖ ^ 2 =
        Real.cosh (Real.pi * t) / 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact normSq_cos_three_half_sub_I_mul t
  have hnorm :
      ‖zetaFEFactor w‖ ^ 2 =
        (2 * (2 * Real.pi) ^ (-(3 / 2 : ℝ))) ^ 2 *
          (((1 / 2 : ℝ) ^ 2 + t ^ 2) *
            (Real.pi / Real.cosh (Real.pi * (-t)))) *
          (Real.cosh (Real.pi * t) / 2) := by
    unfold zetaFEFactor w
    rw [norm_mul, norm_mul, norm_mul]
    rw [norm_real, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [norm_cpow_eq_rpow_re_of_pos hbase]
    rw [show (-(1 / 2 : ℝ) + Complex.I * t : ℂ) - 1 =
        -(3 / 2 : ℝ) + Complex.I * t by push_cast; ring]
    rw [Complex.Gamma_add_one ((1 / 2 : ℝ) - Complex.I * t)
      (by
        intro h
        have him := congrArg Complex.im h
        simp at him
        exact ht (by linarith))]
    rw [norm_mul]
    rw [show ((1 / 2 : ℝ) - Complex.I * t : ℂ) + 1 =
        (3 / 2 : ℝ) - Complex.I * t by push_cast; ring]
    rw [hgamma_add, hcos]
    congr 1
    norm_num
  have hnorm' :
      ‖zetaFEFactor w‖ ^ 2 =
        ‖(1 / 2 : ℝ) - Complex.I * t‖ ^ 2 / (2 * Real.pi) ^ 2 := by
    rw [hnorm]
    rw [show Real.cosh (Real.pi * (-t)) = Real.cosh (Real.pi * t) by rw [Real.cosh_neg]]
    rw [show ‖(1 / 2 : ℝ) - Complex.I * t‖ ^ 2 =
        (1 / 2 : ℝ) ^ 2 + t ^ 2 by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
      ring]
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp [hpi]
    ring
  have hrnonneg : 0 ≤ ‖(1 / 2 : ℝ) - Complex.I * t‖ / (2 * Real.pi) := by positivity
  have hsquare := hnorm'
  rw [div_pow] at hsquare
  nlinarith [norm_nonneg (zetaFEFactor w)]

/-!
The remaining interpolation is isolated without changing the target exponent
or quantifier range.  Supplying this structure is exactly the missing
Phragmén--Lindelöf/Gamma vertical estimate.
-/
structure FEFactorInteriorInterpolation where
  C : ℝ
  C_nonneg : 0 ≤ C
  interpolation_bound :
    ∀ {σ t : ℝ}, -(1 / 2 : ℝ) ≤ σ → σ ≤ (1 / 2 : ℝ) → 1 ≤ |t| →
      ‖zetaFEFactor (σ + Complex.I * t : ℂ)‖ ≤
        C * (|t| + 2) ^ ((1 / 2 : ℝ) - σ)

/-- Mechanical packaging of the isolated interior interpolation residual. -/
noncomputable def zetaFEFactorVerticalBound_of_interior
    (H : FEFactorInteriorInterpolation) : ZetaFEFactorVerticalBound :=
  { C := H.C
    C_nonneg := H.C_nonneg
    factor_bound := H.interpolation_bound }

end RH.Criteria.NymanBeurling.H14ZetaFETransport
