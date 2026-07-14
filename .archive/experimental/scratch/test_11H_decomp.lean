import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula

open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open RH.Criteria.NymanBeurling.CoefficientFamilies

noncomputable def explicitLinearLogComponent (N : ℕ) : ℝ :=
  - 2 * (∑ k ∈ Finset.Icc 1 N, cutoffMobiusCoeff N k * explicitChiRhoKernel k)

noncomputable def explicitQuadraticLogGammaComponent (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
      ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 * (1 / (h : ℝ) + 1 / (k : ℝ)))

noncomputable def explicitQuadraticLogRatioComponent (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
      (((k : ℝ) - (h : ℝ)) / (2 * (h : ℝ) * (k : ℝ)) * Real.log ((h : ℝ) / (k : ℝ)))

noncomputable def explicitQuadraticCotangentComponent (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
      (- (Real.pi / (2 * (h : ℝ) * (k : ℝ)) *
        (RH.Criteria.NymanBeurling.VasyuninGram.cotangentSumVFormula h k +
         RH.Criteria.NymanBeurling.VasyuninGram.cotangentSumVFormula k h)))

noncomputable def explicitCutoffResidueComponent (_N : ℕ) : ℝ := 0

noncomputable def explicitCutoffMobiusComponentSum (N : ℕ) : ℝ :=
  1
    + explicitLinearLogComponent N
    + explicitQuadraticLogGammaComponent N
    + explicitQuadraticLogRatioComponent N
    + explicitQuadraticCotangentComponent N
    + explicitCutoffResidueComponent N

theorem explicitCutoffMobiusEnergyKernel_eq_components (N : ℕ) :
    explicitCutoffMobiusEnergyKernel N = explicitCutoffMobiusComponentSum N := by
  unfold explicitCutoffMobiusEnergyKernel explicitCutoffMobiusComponentSum
  unfold explicitLinearLogComponent explicitQuadraticLogGammaComponent
  unfold explicitQuadraticLogRatioComponent explicitQuadraticCotangentComponent
  unfold explicitCutoffResidueComponent
  unfold explicitBaezDuarteKernel RH.Criteria.NymanBeurling.VasyuninGram.vasyuninBEntryFormula
  have h_quad : (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
        ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 * (1 / (h : ℝ) + 1 / (k : ℝ)) +
          ((k : ℝ) - (h : ℝ)) / (2 * (h : ℝ) * (k : ℝ)) * Real.log ((h : ℝ) / (k : ℝ)) -
          Real.pi / (2 * (h : ℝ) * (k : ℝ)) *
            (RH.Criteria.NymanBeurling.VasyuninGram.cotangentSumVFormula h k +
              RH.Criteria.NymanBeurling.VasyuninGram.cotangentSumVFormula k h))) =
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
        ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / 2 * (1 / (h : ℝ) + 1 / (k : ℝ)))) +
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
        (((k : ℝ) - (h : ℝ)) / (2 * (h : ℝ) * (k : ℝ)) * Real.log ((h : ℝ) / (k : ℝ)))) +
    (∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      cutoffMobiusCoeff N h * cutoffMobiusCoeff N k *
        (- (Real.pi / (2 * (h : ℝ) * (k : ℝ)) *
          (RH.Criteria.NymanBeurling.VasyuninGram.cotangentSumVFormula h k +
           RH.Criteria.NymanBeurling.VasyuninGram.cotangentSumVFormula k h)))) := by
    -- we distribute the multiplication then the sums
    sorry
  rw [h_quad]
  ring
