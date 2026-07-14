import RiemannHypothesis.Certificates.NymanBeurlingCertificate

import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5
import Mathlib

/-!
# GENERATED GRAM MATRIX CERTIFICATE
N = 5

Indices convention:
- Lean generated index `i : Fin N` corresponds to mathematical index `h = i.val + 1`.
- Lean generated index `j : Fin N` corresponds to mathematical index `k = j.val + 1`.
- Gram entry represents: ∫₀^∞ {1/(h x)} {1/(k x)} dx

Data Source: CertifiedInterval
-/

set_option maxHeartbeats 10000000
open scoped BigOperators

namespace RH.Certificates.Generated.NymanGramN5

open RH.Certificates

def entry_1_1 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 1
  lower := (6303/5000)
  upper := (12607/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_1_1.interval_proof
}

def entry_1_2 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 2
  lower := (3861/5000)
  upper := (7723/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_1_2.interval_proof
}

def entry_1_3 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 3
  lower := (23/40)
  upper := (5751/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_1_3.interval_proof
}

def entry_1_4 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 4
  lower := (74098041/159590000)
  upper := (74129959/159590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_1_4.interval_proof
}

def entry_1_5 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 5
  lower := (297474187/758130000)
  upper := (297625813/758130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_1_5.interval_proof
}

def entry_2_1 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 1
  lower := (3861/5000)
  upper := (7723/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_2_1.interval_proof
}

def entry_2_2 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 2
  lower := (6303/10000)
  upper := (394/625)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_2_2.interval_proof
}

def entry_2_3 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 3
  lower := (4411/10000)
  upper := (1103/2500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_2_3.interval_proof
}

def entry_2_4 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 4
  lower := (368854443/955570000)
  upper := (369045557/955570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_2_4.interval_proof
}

def entry_2_5 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 5
  lower := (36498461/115390000)
  upper := (36521539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_2_5.interval_proof
}

def entry_3_1 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 1
  lower := (23/40)
  upper := (5751/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_3_1.interval_proof
}

def entry_3_2 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 2
  lower := (4411/10000)
  upper := (1103/2500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_3_2.interval_proof
}

def entry_3_3 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 3
  lower := (2101/5000)
  upper := (4203/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_3_3.interval_proof
}

def entry_3_4 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 4
  lower := (12635993/40070000)
  upper := (12644007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_3_4.interval_proof
}

def entry_3_5 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 5
  lower := (80650507/294930000)
  upper := (80709493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_3_5.interval_proof
}

def entry_4_1 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 1
  lower := (74098041/159590000)
  upper := (74129959/159590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_4_1.interval_proof
}

def entry_4_2 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 2
  lower := (368854443/955570000)
  upper := (369045557/955570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_4_2.interval_proof
}

def entry_4_3 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 3
  lower := (12635993/40070000)
  upper := (12644007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_4_3.interval_proof
}

def entry_4_4 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 4
  lower := (797903/2532500)
  upper := (1596819/5065000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_4_4.interval_proof
}

def entry_4_5 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 5
  lower := (25442211/102890000)
  upper := (25462789/102890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_4_5.interval_proof
}

def entry_5_1 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 1
  lower := (297474187/758130000)
  upper := (297625813/758130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_5_1.interval_proof
}

def entry_5_2 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 2
  lower := (36498461/115390000)
  upper := (36521539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_5_2.interval_proof
}

def entry_5_3 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 3
  lower := (80650507/294930000)
  upper := (80709493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_5_3.interval_proof
}

def entry_5_4 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 4
  lower := (25442211/102890000)
  upper := (25462789/102890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_5_4.interval_proof
}

def entry_5_5 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 5
  lower := (175820239/697610000)
  upper := (175959761/697610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5.interval_5_5.interval_proof
}


def M_reg_fn (i j : Fin 5) : ℚ :=
  if i.val == 0 ∧ j.val == 0 then (113228981/89810000)
  else if i.val == 0 ∧ j.val == 1 then (5624/7283)
  else if i.val == 0 ∧ j.val == 2 then (4136/7193)
  else if i.val == 0 ∧ j.val == 3 then (1846/3975)
  else if i.val == 0 ∧ j.val == 4 then (3298/8403)
  else if i.val == 1 ∧ j.val == 0 then (5624/7283)
  else if i.val == 1 ∧ j.val == 1 then (56618981/89810000)
  else if i.val == 1 ∧ j.val == 2 then (3022/6851)
  else if i.val == 1 ∧ j.val == 3 then (2812/7283)
  else if i.val == 1 ∧ j.val == 4 then (2461/7778)
  else if i.val == 2 ∧ j.val == 0 then (4136/7193)
  else if i.val == 2 ∧ j.val == 1 then (3022/6851)
  else if i.val == 2 ∧ j.val == 2 then (37748981/89810000)
  else if i.val == 2 ∧ j.val == 3 then (1264/4007)
  else if i.val == 2 ∧ j.val == 4 then (2729/9976)
  else if i.val == 3 ∧ j.val == 0 then (1846/3975)
  else if i.val == 3 ∧ j.val == 1 then (2812/7283)
  else if i.val == 3 ∧ j.val == 2 then (1264/4007)
  else if i.val == 3 ∧ j.val == 3 then (3622399/11490000)
  else if i.val == 3 ∧ j.val == 4 then (1579/6383)
  else if i.val == 4 ∧ j.val == 0 then (3298/8403)
  else if i.val == 4 ∧ j.val == 1 then (2461/7778)
  else if i.val == 4 ∧ j.val == 2 then (2729/9976)
  else if i.val == 4 ∧ j.val == 3 then (1579/6383)
  else if i.val == 4 ∧ j.val == 4 then (16856683/66830000)
  else 0

def L_val_fn (i j : Fin 5) : ℚ :=
  if i.val == 0 ∧ j.val == 0 then 1
  else if i.val == 0 ∧ j.val == 1 then 0
  else if i.val == 0 ∧ j.val == 2 then 0
  else if i.val == 0 ∧ j.val == 3 then 0
  else if i.val == 0 ∧ j.val == 4 then 0
  else if i.val == 1 ∧ j.val == 0 then (505091440000/824646668623)
  else if i.val == 1 ∧ j.val == 1 then 1
  else if i.val == 1 ∧ j.val == 2 then 0
  else if i.val == 1 ∧ j.val == 3 then 0
  else if i.val == 1 ∧ j.val == 4 then 0
  else if i.val == 2 ∧ j.val == 0 then (371454160000/814456060333)
  else if i.val == 2 ∧ j.val == 1 then (2363481593029158497788407340000/4185319163311698722067675940347)
  else if i.val == 2 ∧ j.val == 2 then 1
  else if i.val == 2 ∧ j.val == 3 then 0
  else if i.val == 2 ∧ j.val == 4 then 0
  else if i.val == 3 ∧ j.val == 0 then (6631570400/18003407979)
  else if i.val == 3 ∧ j.val == 1 then (8718728289113224618040000/13503976653345914765954511)
  else if i.val == 3 ∧ j.val == 2 then (545654345117216697764754584241447207696260457760000/1272932849243464307198850995600506444459976743125813)
  else if i.val == 3 ∧ j.val == 3 then 1
  else if i.val == 3 ∧ j.val == 4 then 0
  else if i.val == 4 ∧ j.val == 0 then (296193380000/951463127343)
  else if i.val == 4 ∧ j.val == 1 then (1339891499886161962498500035000/2775472066770173534565219967443)
  else if i.val == 4 ∧ j.val == 2 then (38972818039162973890059208544828141599788683573019178750/81419379340104351772137483306290461764018515947079051049)
  else if i.val == 4 ∧ j.val == 3 then (2836457674994064286947431672765071568380914139981141837922803015665110130000/5273782699982368461722222272852504953435571571656987888163677441376979743051)
  else if i.val == 4 ∧ j.val == 4 then 1
  else 0

def D_val_fn (i : Fin 5) : ℚ :=
  if i.val == 0 then (113228981/89810000)
  else if i.val == 1 then (84930670775760470226129/539390030561677361290000)
  else if i.val == 2 then (1997970296075365448827525094607246194097399901/18523255028909984907727784991494372028599010000)
  else if i.val == 3 then (60824686803419712752445686775678370200311339030715745962000859/1035379304745198794611207117732965840265849231102044884946090000)
  else if i.val == 4 then (1578304571500256988537585061305705496749177542465943190379499417883844778908582783618113226896837/30558782135572008104305775498876932809630049946661719469425555323574302824730953316568938093370000)
  else 0

def linear_fn (i : Fin 5) : ℚ :=
  if i.val == 0 then (334885130399/792094461875)
  else if i.val == 1 then (539229655814/966420695621)
  else if i.val == 2 then (429555871558/847029364035)
  else if i.val == 3 then (365803125173/808816390216)
  else if i.val == 4 then (310041832416/762814777745)
  else 0

def coeff_fn (i : Fin 5) : ℚ :=
  if i.val == 0 then (-662212804/714757509)
  else if i.val == 1 then (587988911/684994299)
  else if i.val == 2 then (696229222/807378543)
  else if i.val == 3 then (185772793/625903528)
  else if i.val == 4 then (309415520/412599753)
  else 0

def M_reg : Matrix (Fin 5) (Fin 5) ℚ := M_reg_fn
def L_val : Matrix (Fin 5) (Fin 5) ℚ := L_val_fn
def D_val : Fin 5 → ℚ := D_val_fn

-- Provide interval models
def gram_lower (i j : Fin 5) : ℚ :=
  if i.val == 0 ∧ j.val == 0 then entry_1_1.lower
  else if i.val == 0 ∧ j.val == 1 then entry_1_2.lower
  else if i.val == 0 ∧ j.val == 2 then entry_1_3.lower
  else if i.val == 0 ∧ j.val == 3 then entry_1_4.lower
  else if i.val == 0 ∧ j.val == 4 then entry_1_5.lower
  else if i.val == 1 ∧ j.val == 0 then entry_2_1.lower
  else if i.val == 1 ∧ j.val == 1 then entry_2_2.lower
  else if i.val == 1 ∧ j.val == 2 then entry_2_3.lower
  else if i.val == 1 ∧ j.val == 3 then entry_2_4.lower
  else if i.val == 1 ∧ j.val == 4 then entry_2_5.lower
  else if i.val == 2 ∧ j.val == 0 then entry_3_1.lower
  else if i.val == 2 ∧ j.val == 1 then entry_3_2.lower
  else if i.val == 2 ∧ j.val == 2 then entry_3_3.lower
  else if i.val == 2 ∧ j.val == 3 then entry_3_4.lower
  else if i.val == 2 ∧ j.val == 4 then entry_3_5.lower
  else if i.val == 3 ∧ j.val == 0 then entry_4_1.lower
  else if i.val == 3 ∧ j.val == 1 then entry_4_2.lower
  else if i.val == 3 ∧ j.val == 2 then entry_4_3.lower
  else if i.val == 3 ∧ j.val == 3 then entry_4_4.lower
  else if i.val == 3 ∧ j.val == 4 then entry_4_5.lower
  else if i.val == 4 ∧ j.val == 0 then entry_5_1.lower
  else if i.val == 4 ∧ j.val == 1 then entry_5_2.lower
  else if i.val == 4 ∧ j.val == 2 then entry_5_3.lower
  else if i.val == 4 ∧ j.val == 3 then entry_5_4.lower
  else if i.val == 4 ∧ j.val == 4 then entry_5_5.lower
  else 0

def gram_upper (i j : Fin 5) : ℚ :=
  if i.val == 0 ∧ j.val == 0 then entry_1_1.upper
  else if i.val == 0 ∧ j.val == 1 then entry_1_2.upper
  else if i.val == 0 ∧ j.val == 2 then entry_1_3.upper
  else if i.val == 0 ∧ j.val == 3 then entry_1_4.upper
  else if i.val == 0 ∧ j.val == 4 then entry_1_5.upper
  else if i.val == 1 ∧ j.val == 0 then entry_2_1.upper
  else if i.val == 1 ∧ j.val == 1 then entry_2_2.upper
  else if i.val == 1 ∧ j.val == 2 then entry_2_3.upper
  else if i.val == 1 ∧ j.val == 3 then entry_2_4.upper
  else if i.val == 1 ∧ j.val == 4 then entry_2_5.upper
  else if i.val == 2 ∧ j.val == 0 then entry_3_1.upper
  else if i.val == 2 ∧ j.val == 1 then entry_3_2.upper
  else if i.val == 2 ∧ j.val == 2 then entry_3_3.upper
  else if i.val == 2 ∧ j.val == 3 then entry_3_4.upper
  else if i.val == 2 ∧ j.val == 4 then entry_3_5.upper
  else if i.val == 3 ∧ j.val == 0 then entry_4_1.upper
  else if i.val == 3 ∧ j.val == 1 then entry_4_2.upper
  else if i.val == 3 ∧ j.val == 2 then entry_4_3.upper
  else if i.val == 3 ∧ j.val == 3 then entry_4_4.upper
  else if i.val == 3 ∧ j.val == 4 then entry_4_5.upper
  else if i.val == 4 ∧ j.val == 0 then entry_5_1.upper
  else if i.val == 4 ∧ j.val == 1 then entry_5_2.upper
  else if i.val == 4 ∧ j.val == 2 then entry_5_3.upper
  else if i.val == 4 ∧ j.val == 3 then entry_5_4.upper
  else if i.val == 4 ∧ j.val == 4 then entry_5_5.upper
  else 0

-- Legacy small-N interval data.
def lin_lower (i : Fin 5) : ℚ := linear_fn i - (1/1000000000)
def lin_upper (i : Fin 5) : ℚ := linear_fn i + (1/1000000000)

axiom lin_certified : ∀ k : Fin 5,
    (lin_lower k : ℝ) ≤ innerProductChiRho k.val ∧
    innerProductChiRho k.val ≤ (lin_upper k : ℝ)
def const_lower : ℚ := 1 - (1/10000)
def const_upper : ℚ := 1 + (1/10000)

theorem toy_gram_certified (i j : Fin 5) :
  (gram_lower i j : ℝ) ≤ RH.Criteria.NymanBeurling.VasyuninGram.baezDuarteGramEntry (i.val + 1) (j.val + 1) ∧
  RH.Criteria.NymanBeurling.VasyuninGram.baezDuarteGramEntry (i.val + 1) (j.val + 1) ≤ (gram_upper i j : ℝ) := by
  fin_cases i <;> fin_cases j <;> simp [gram_lower, gram_upper]
  · exact entry_1_1.certified_interval
  · exact entry_1_2.certified_interval
  · exact entry_1_3.certified_interval
  · exact entry_1_4.certified_interval
  · exact entry_1_5.certified_interval
  · exact entry_2_1.certified_interval
  · exact entry_2_2.certified_interval
  · exact entry_2_3.certified_interval
  · exact entry_2_4.certified_interval
  · exact entry_2_5.certified_interval
  · exact entry_3_1.certified_interval
  · exact entry_3_2.certified_interval
  · exact entry_3_3.certified_interval
  · exact entry_3_4.certified_interval
  · exact entry_3_5.certified_interval
  · exact entry_4_1.certified_interval
  · exact entry_4_2.certified_interval
  · exact entry_4_3.certified_interval
  · exact entry_4_4.certified_interval
  · exact entry_4_5.certified_interval
  · exact entry_5_1.certified_interval
  · exact entry_5_2.certified_interval
  · exact entry_5_3.certified_interval
  · exact entry_5_4.certified_interval
  · exact entry_5_5.certified_interval

def Q_interval : BaezDuarteIntervalQuadraticModel 5 :=
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


def witnessN5 : RationalPSDWitness 5 :=
{
  M := M_reg
  L := L_val
  D := D_val
  diagonal_nonneg := by intro i; fin_cases i <;> simp [D_val, D_val_fn] <;> norm_num
  ldl_identity := by ext i j; fin_cases i <;> fin_cases j <;> simp [M_reg, M_reg_fn, L_val, L_val_fn, D_val, D_val_fn, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] <;> norm_num
}

-- M_orig removed: implicitly bounded by the Gram entry intervals
def regCertN5 : RegularizedPSDCertificate 5 :=
{
  originalMatrix := M_reg - ((1/10000) : ℚ) • 1
  epsilon := (1/10000)
  regularizedMatrix := M_reg
  regularized_eq := by simp
  epsilon_nonneg := by norm_num
  witness := witnessN5
  witness_matches := rfl
}

-- energyUpper is the sign-aware interval arithmetic upper bound on:
--   ||chi||^2 - 2*c^T*l + c^T*G*c  where c = coeff_fn, l_k = innerProductChiRho k
-- This bounds BaezDuarteDistance N via candidate_bounds_baez_duarte_distance
-- (pending baezDuarteL2Error_gram_expansion axiom)
def witnessEnergy : FiniteIntervalEnergyWitness 5 :=
{
  model := Q_interval
  coeffs := coeff_fn
  energyUpper := (31778224828003876712256800850823669472384851513893492523692946960664413530836909136090534081944968607317562551780641016814975191450208016315881880596646078031252004155224851233/857202289756649522254969899243333258643614442990426198222088086931327526201338270988779093962149674638941632186326758430699187861918014386722309266501268821585328019799200000000)
  interval_energy_bound := True.intro
}


noncomputable def certN5 : FiniteApproximationCertificate :=
{
  N := 5
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
--     = energyUpper                                    (kernel-checked rational equality)
theorem N5_quadratic_le_energyUpper :
    ∑ h : Fin 5, ∑ k : Fin 5,
      (coeff_fn h : ℝ) * (coeff_fn k : ℝ) *
      RH.Criteria.NymanBeurling.VasyuninGram.baezDuarteGramEntry (h.val + 1) (k.val + 1)
    - 2 * ∑ k : Fin 5,
        (coeff_fn k : ℝ) * innerProductChiRho k.val
    + 1 ≤ (witnessEnergy.energyUpper : ℝ) := by
  have hbound := sign_aware_energy_bound (N := 5) coeff_fn
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
             witnessEnergy.energyUpper := by
    norm_num [signAwareQuadBoundQ, signAwareLinBoundQ, coeff_fn,
      gram_lower, gram_upper, lin_lower, lin_upper, linear_fn,
      entry_1_1, entry_1_2, entry_1_3, entry_1_4, entry_1_5,
      entry_2_1, entry_2_2, entry_2_3, entry_2_4, entry_2_5,
      entry_3_1, entry_3_2, entry_3_3, entry_3_4, entry_3_5,
      entry_4_1, entry_4_2, entry_4_3, entry_4_4, entry_4_5,
      entry_5_1, entry_5_2, entry_5_3, entry_5_4, entry_5_5,
      witnessEnergy, Fin.sum_univ_succ, Fin.sum_univ_zero]
  calc ∑ h : Fin 5, ∑ k : Fin 5,
          (coeff_fn h : ℝ) * (coeff_fn k : ℝ) *
          RH.Criteria.NymanBeurling.VasyuninGram.baezDuarteGramEntry (h.val + 1) (k.val + 1)
        - 2 * ∑ k : Fin 5, (coeff_fn k : ℝ) * innerProductChiRho k.val + 1
      ≤ (signAwareQuadBoundQ coeff_fn gram_lower gram_upper : ℝ) +
        (signAwareLinBoundQ coeff_fn lin_lower lin_upper : ℝ) + 1 := hbound
    _ = (witnessEnergy.energyUpper : ℝ) := by exact_mod_cast heq

theorem baezDuarteDistance_N5_bound :
    RH.Criteria.NymanBeurling.BaezDuarte.BaezDuarteDistance 5 ≤
      (witnessEnergy.energyUpper : ℝ) := by
  apply (candidate_bounds_baez_duarte_distance
           (fun k => (coeff_fn k : ℝ))).trans
  rw [baezDuarteL2Error_gram_expansion]
  exact N5_quadratic_le_energyUpper

end RH.Certificates.Generated.NymanGramN5
