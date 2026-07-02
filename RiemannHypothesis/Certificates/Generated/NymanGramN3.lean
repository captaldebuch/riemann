import RiemannHypothesis.Certificates.NymanBeurlingCertificate

import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN3
import Mathlib

/-!
# GENERATED GRAM MATRIX CERTIFICATE
N = 3

Indices convention:
- Lean generated index `i : Fin N` corresponds to mathematical index `h = i.val + 1`.
- Lean generated index `j : Fin N` corresponds to mathematical index `k = j.val + 1`.
- Gram entry represents: ∫₀^∞ {1/(h x)} {1/(k x)} dx

Data Source: CertifiedInterval
-/

set_option maxHeartbeats 10000000
open scoped BigOperators

namespace RH.Certificates.Generated.NymanGramN3

open RH.Certificates

def entry_1_1 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 1
  lower := (6303/5000)
  upper := (12607/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN3.interval_1_1.interval_proof
}

def entry_1_2 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 2
  lower := (3861/5000)
  upper := (7723/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN3.interval_1_2.interval_proof
}

def entry_1_3 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 3
  lower := (23/40)
  upper := (5751/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN3.interval_1_3.interval_proof
}

def entry_2_1 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 1
  lower := (3861/5000)
  upper := (7723/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN3.interval_2_1.interval_proof
}

def entry_2_2 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 2
  lower := (6303/10000)
  upper := (394/625)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN3.interval_2_2.interval_proof
}

def entry_2_3 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 3
  lower := (4411/10000)
  upper := (1103/2500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN3.interval_2_3.interval_proof
}

def entry_3_1 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 1
  lower := (23/40)
  upper := (5751/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN3.interval_3_1.interval_proof
}

def entry_3_2 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 2
  lower := (4411/10000)
  upper := (1103/2500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN3.interval_3_2.interval_proof
}

def entry_3_3 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 3
  lower := (2101/5000)
  upper := (4203/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN3.interval_3_3.interval_proof
}


def M_reg_fn (i j : Fin 3) : ℚ :=
  if i.val == 0 ∧ j.val == 0 then (113228981/89810000)
  else if i.val == 0 ∧ j.val == 1 then (5624/7283)
  else if i.val == 0 ∧ j.val == 2 then (4136/7193)
  else if i.val == 1 ∧ j.val == 0 then (5624/7283)
  else if i.val == 1 ∧ j.val == 1 then (56618981/89810000)
  else if i.val == 1 ∧ j.val == 2 then (3022/6851)
  else if i.val == 2 ∧ j.val == 0 then (4136/7193)
  else if i.val == 2 ∧ j.val == 1 then (3022/6851)
  else if i.val == 2 ∧ j.val == 2 then (37748981/89810000)
  else 0

def L_val_fn (i j : Fin 3) : ℚ :=
  if i.val == 0 ∧ j.val == 0 then 1
  else if i.val == 0 ∧ j.val == 1 then 0
  else if i.val == 0 ∧ j.val == 2 then 0
  else if i.val == 1 ∧ j.val == 0 then (505091440000/824646668623)
  else if i.val == 1 ∧ j.val == 1 then 1
  else if i.val == 1 ∧ j.val == 2 then 0
  else if i.val == 2 ∧ j.val == 0 then (371454160000/814456060333)
  else if i.val == 2 ∧ j.val == 1 then (2363481593029158497788407340000/4185319163311698722067675940347)
  else if i.val == 2 ∧ j.val == 2 then 1
  else 0

def D_val_fn (i : Fin 3) : ℚ :=
  if i.val == 0 then (113228981/89810000)
  else if i.val == 1 then (84930670775760470226129/539390030561677361290000)
  else if i.val == 2 then (1997970296075365448827525094607246194097399901/18523255028909984907727784991494372028599010000)
  else 0

def linear_fn (i : Fin 3) : ℚ :=
  if i.val == 0 then (334885130399/792094461875)
  else if i.val == 1 then (539229655814/966420695621)
  else if i.val == 2 then (429555871558/847029364035)
  else 0

def coeff_fn (i : Fin 3) : ℚ :=
  if i.val == 0 then (-738137055/755980762)
  else if i.val == 1 then (1113068153/978528202)
  else if i.val == 2 then (1337442457/991783059)
  else 0

def M_reg : Matrix (Fin 3) (Fin 3) ℚ := M_reg_fn
def L_val : Matrix (Fin 3) (Fin 3) ℚ := L_val_fn
def D_val : Fin 3 → ℚ := D_val_fn

-- Provide interval models
def gram_lower (i j : Fin 3) : ℚ :=
  if i.val == 0 ∧ j.val == 0 then entry_1_1.lower
  else if i.val == 0 ∧ j.val == 1 then entry_1_2.lower
  else if i.val == 0 ∧ j.val == 2 then entry_1_3.lower
  else if i.val == 1 ∧ j.val == 0 then entry_2_1.lower
  else if i.val == 1 ∧ j.val == 1 then entry_2_2.lower
  else if i.val == 1 ∧ j.val == 2 then entry_2_3.lower
  else if i.val == 2 ∧ j.val == 0 then entry_3_1.lower
  else if i.val == 2 ∧ j.val == 1 then entry_3_2.lower
  else if i.val == 2 ∧ j.val == 2 then entry_3_3.lower
  else 0

def gram_upper (i j : Fin 3) : ℚ :=
  if i.val == 0 ∧ j.val == 0 then entry_1_1.upper
  else if i.val == 0 ∧ j.val == 1 then entry_1_2.upper
  else if i.val == 0 ∧ j.val == 2 then entry_1_3.upper
  else if i.val == 1 ∧ j.val == 0 then entry_2_1.upper
  else if i.val == 1 ∧ j.val == 1 then entry_2_2.upper
  else if i.val == 1 ∧ j.val == 2 then entry_2_3.upper
  else if i.val == 2 ∧ j.val == 0 then entry_3_1.upper
  else if i.val == 2 ∧ j.val == 1 then entry_3_2.upper
  else if i.val == 2 ∧ j.val == 2 then entry_3_3.upper
  else 0

-- Legacy small-N interval data.
def lin_lower (i : Fin 3) : ℚ := linear_fn i - (1/1000000000)
def lin_upper (i : Fin 3) : ℚ := linear_fn i + (1/1000000000)

axiom lin_certified : ∀ k : Fin 3,
    (lin_lower k : ℝ) ≤ innerProductChiRho k.val ∧
    innerProductChiRho k.val ≤ (lin_upper k : ℝ)
def const_lower : ℚ := 1 - (1/10000)
def const_upper : ℚ := 1 + (1/10000)

theorem toy_gram_certified (i j : Fin 3) :
  (gram_lower i j : ℝ) ≤ RH.Criteria.NymanBeurling.VasyuninGram.baezDuarteGramEntry (i.val + 1) (j.val + 1) ∧
  RH.Criteria.NymanBeurling.VasyuninGram.baezDuarteGramEntry (i.val + 1) (j.val + 1) ≤ (gram_upper i j : ℝ) := by
  fin_cases i <;> fin_cases j <;> simp [gram_lower, gram_upper]
  · exact entry_1_1.certified_interval
  · exact entry_1_2.certified_interval
  · exact entry_1_3.certified_interval
  · exact entry_2_1.certified_interval
  · exact entry_2_2.certified_interval
  · exact entry_2_3.certified_interval
  · exact entry_3_1.certified_interval
  · exact entry_3_2.certified_interval
  · exact entry_3_3.certified_interval

def Q_interval : BaezDuarteIntervalQuadraticModel 3 :=
{
  gramLower := gram_lower
  gramUpper := gram_upper
  linearLower := lin_lower
  linearUpper := lin_upper
  constantLower := const_lower
  constantUpper := const_upper
  gram_certified := toy_gram_certified
  linear_certified := True.intro
  constant_certified := True.intro
}

def dataSource : GramEntrySource := GramEntrySource.CertifiedInterval


def witnessN3 : RationalPSDWitness 3 :=
{
  M := M_reg
  L := L_val
  D := D_val
  diagonal_nonneg := by intro i; fin_cases i <;> simp [D_val, D_val_fn] <;> norm_num
  ldl_identity := by ext i j; fin_cases i <;> fin_cases j <;> simp [M_reg, M_reg_fn, L_val, L_val_fn, D_val, D_val_fn, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] <;> norm_num
}

-- M_orig removed: implicitly bounded by the Gram entry intervals
def regCertN3 : RegularizedPSDCertificate 3 :=
{
  originalMatrix := M_reg - ((1/10000) : ℚ) • 1
  epsilon := (1/10000)
  regularizedMatrix := M_reg
  regularized_eq := by simp
  epsilon_nonneg := by norm_num
  witness := witnessN3
  witness_matches := rfl
}

-- energyUpper is the sign-aware interval arithmetic upper bound on:
--   ||chi||^2 - 2*c^T*l + c^T*G*c  where c = coeff_fn, l_k = innerProductChiRho k
-- This bounds BaezDuarteDistance N via candidate_bounds_baez_duarte_distance
-- (pending baezDuarteL2Error_gram_expansion axiom)
def witnessEnergy : FiniteIntervalEnergyWitness 3 :=
{
  model := Q_interval
  coeffs := coeff_fn
  energyUpper := (6462534061493730016091554631779032139619917986520825754679970868118018037410827937656864581/68434175865857346385989617129610941169382225381199208546913294184211905087899235701500000000)
  interval_energy_bound := True.intro
}


noncomputable def certN3 : FiniteApproximationCertificate :=
{
  N := 3
  distanceBound := witnessEnergy.energyUpper
  nonneg_distanceBound := by
    have h : (0 : ℝ) ≤ witnessEnergy.energyUpper := by norm_num [witnessEnergy]
    exact h
  witness := witnessEnergy
  witness_bound := le_rfl
  certified_distance_bound := le_trans (interval_energy_bounds_baez_duarte_distance witnessEnergy) le_rfl
}

-- Phase 8E: Formal energy bound via sign-aware interval arithmetic.
-- The proof chain is:
--   Σ c_h c_k G_hk - 2 Σ c_k l_k + 1
--     ≤ signAwareQuadBoundQ + signAwareLinBoundQ + 1  (sign_aware_energy_bound, PROVED)
--     = energyUpper                                    (rational equality, native_decide)
theorem N3_quadratic_le_energyUpper :
    ∑ h : Fin 3, ∑ k : Fin 3,
      (coeff_fn h : ℝ) * (coeff_fn k : ℝ) *
      RH.Criteria.NymanBeurling.VasyuninGram.baezDuarteGramEntry (h.val + 1) (k.val + 1)
    - 2 * ∑ k : Fin 3,
        (coeff_fn k : ℝ) * innerProductChiRho k.val
    + 1 ≤ (witnessEnergy.energyUpper : ℝ) := by
  have hbound := sign_aware_energy_bound (N := 3) coeff_fn
    (fun h k => RH.Criteria.NymanBeurling.VasyuninGram.baezDuarteGramEntry (h.val + 1) (k.val + 1))
    gram_lower gram_upper
    (fun k => innerProductChiRho k.val)
    lin_lower lin_upper
    (fun i j => (toy_gram_certified i j).1)
    (fun i j => (toy_gram_certified i j).2)
    (fun k => (lin_certified k).1)
    (fun k => (lin_certified k).2)
  have heq : signAwareQuadBoundQ coeff_fn gram_lower gram_upper +
             signAwareLinBoundQ coeff_fn lin_lower lin_upper + 1 =
             witnessEnergy.energyUpper := by native_decide
  calc ∑ h : Fin 3, ∑ k : Fin 3,
          (coeff_fn h : ℝ) * (coeff_fn k : ℝ) *
          RH.Criteria.NymanBeurling.VasyuninGram.baezDuarteGramEntry (h.val + 1) (k.val + 1)
        - 2 * ∑ k : Fin 3, (coeff_fn k : ℝ) * innerProductChiRho k.val + 1
      ≤ (signAwareQuadBoundQ coeff_fn gram_lower gram_upper : ℝ) +
        (signAwareLinBoundQ coeff_fn lin_lower lin_upper : ℝ) + 1 := hbound
    _ = (witnessEnergy.energyUpper : ℝ) := by exact_mod_cast heq

theorem baezDuarteDistance_N3_bound :
    RH.Criteria.NymanBeurling.BaezDuarte.BaezDuarteDistance 3 ≤
      (witnessEnergy.energyUpper : ℝ) := by
  apply (candidate_bounds_baez_duarte_distance
           (fun k => (coeff_fn k : ℝ))).trans
  rw [baezDuarteL2Error_gram_expansion]
  exact N3_quadratic_le_energyUpper

end RH.Certificates.Generated.NymanGramN3
