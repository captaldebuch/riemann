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
