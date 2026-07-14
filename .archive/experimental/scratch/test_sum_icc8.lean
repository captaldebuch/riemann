import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels

open Finset
open scoped BigOperators

theorem cutoffMobiusLinearTerm_eq_sum_test (N : ℕ) :
    RH.Criteria.NymanBeurling.CoefficientFamilies.cutoffMobiusLinearTerm N =
      ∑ k ∈ Finset.Icc 1 N, RH.Criteria.NymanBeurling.CutoffMobiusKernels.cutoffMobiusCoeff N k * RH.Criteria.NymanBeurling.CutoffMobiusKernels.chiRhoKernel k := by
  unfold RH.Criteria.NymanBeurling.CoefficientFamilies.cutoffMobiusLinearTerm
  unfold RH.Criteria.NymanBeurling.CutoffMobiusKernels.cutoffMobiusCoeff
  unfold RH.Criteria.NymanBeurling.CutoffMobiusKernels.cutoffWeight
  unfold RH.Criteria.NymanBeurling.CutoffMobiusKernels.chiRhoKernel
  rw [← RH.Criteria.NymanBeurling.CutoffMobiusKernels.sum_fin_eq_sum_Icc_one]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  have h_sub : (k : ℝ) + 1 - 1 = ↑k := by ring
  rw [h_sub]

theorem cutoffMobiusQuadraticTerm_eq_double_sum_test (N : ℕ) :
    RH.Criteria.NymanBeurling.CoefficientFamilies.cutoffMobiusQuadraticTerm N =
      ∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 N,
          RH.Criteria.NymanBeurling.CutoffMobiusKernels.cutoffMobiusCoeff N h * RH.Criteria.NymanBeurling.CutoffMobiusKernels.cutoffMobiusCoeff N k * RH.Criteria.NymanBeurling.CutoffMobiusKernels.baezDuarteKernel h k := by
  unfold RH.Criteria.NymanBeurling.CoefficientFamilies.cutoffMobiusQuadraticTerm
  unfold RH.Criteria.NymanBeurling.CutoffMobiusKernels.cutoffMobiusCoeff
  unfold RH.Criteria.NymanBeurling.CutoffMobiusKernels.cutoffWeight
  unfold RH.Criteria.NymanBeurling.CutoffMobiusKernels.baezDuarteKernel
  rw [← RH.Criteria.NymanBeurling.CutoffMobiusKernels.sum_fin_fin_eq_sum_Icc_Icc]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  rfl

