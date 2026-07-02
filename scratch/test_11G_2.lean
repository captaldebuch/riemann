import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula
import RiemannHypothesis.Certificates.NymanBeurlingCertificate

open RH.Criteria.NymanBeurling.CutoffMobiusKernels
open RH.Criteria.NymanBeurling.CoefficientFamilies
open RH.Certificates

noncomputable def explicitChiRhoKernel (k : ℕ) : ℝ :=
  (Real.log (k : ℝ) + 1 - Real.eulerMascheroniConstant) / (k : ℝ)

noncomputable def explicitBaezDuarteKernel (h k : ℕ) : ℝ :=
  RH.Criteria.NymanBeurling.VasyuninGram.vasyuninBEntryFormula h k

theorem chiRhoKernel_eq_explicit
    {k : ℕ} (hk : 1 ≤ k) :
    chiRhoKernel k = explicitChiRhoKernel k := by
  unfold chiRhoKernel explicitChiRhoKernel
  rw [innerProductChiRho_formula (k - 1)]
  have h_cancel : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by exact_mod_cast Nat.sub_add_cancel hk
  rw [h_cancel]

theorem baezDuarteKernel_eq_explicit
    {h k : ℕ} (_hh : 1 ≤ h) (_hk : 1 ≤ k) :
    baezDuarteKernel h k = explicitBaezDuarteKernel h k := by
  unfold baezDuarteKernel explicitBaezDuarteKernel
  rw [RH.Criteria.NymanBeurling.VasyuninGram.vasyuninBEntry_correct_axiom h k]
  rfl

noncomputable def explicitCutoffMobiusEnergyKernel (N : ℕ) : ℝ :=
  1
    - 2 * (∑ k ∈ Finset.Icc 1 N,
        cutoffMobiusCoeff N k * explicitChiRhoKernel k)
    + (∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 N,
          cutoffMobiusCoeff N h
            * cutoffMobiusCoeff N k
            * explicitBaezDuarteKernel h k)

theorem cutoffMobiusEnergyKernel_eq_explicit
    (N : ℕ) :
    cutoffMobiusEnergyKernel N =
      explicitCutoffMobiusEnergyKernel N := by
  unfold cutoffMobiusEnergyKernel explicitCutoffMobiusEnergyKernel
  congr 1
  · congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [chiRhoKernel_eq_explicit hk.1]
  · apply Finset.sum_congr rfl
    intro h hh
    rw [Finset.mem_Icc] at hh
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [baezDuarteKernel_eq_explicit hh.1 hk.1]

structure ExplicitCutoffMobiusKernelEstimate where
  C : ℝ
  C_pos : 0 < C
  bound :
    ∀ N : ℕ,
      explicitCutoffMobiusEnergyKernel N
        ≤ C / Real.log (N + 2 : ℝ)

def cutoffMobius_kernel_estimate_of_explicit
    (H : ExplicitCutoffMobiusKernelEstimate) :
    CutoffMobiusKernelEstimate := by
  refine ⟨H.C, H.C_pos, ?_⟩
  intro N
  rw [cutoffMobiusEnergyKernel_eq_explicit]
  exact H.bound N
