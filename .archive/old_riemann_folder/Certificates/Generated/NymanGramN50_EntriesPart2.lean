import RiemannHypothesis.Certificates.NymanBeurlingCertificate
import RiemannHypothesis.Certificates.Generated.ChiRhoBoundsN50
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
import Mathlib

/-!
# GENERATED GRAM MATRIX CERTIFICATE
N = 50

Indices convention:
- Lean generated index `i : Fin N` corresponds to mathematical index `h = i.val + 1`.
- Lean generated index `j : Fin N` corresponds to mathematical index `k = j.val + 1`.
- Gram entry represents: ∫₀^∞ {1/(h x)} {1/(k x)} dx

Data Source: CertifiedInterval
-/

set_option maxHeartbeats 10000000
open scoped BigOperators

namespace RH.Certificates.Generated.NymanGramN50

open RH.Certificates

def entry_11_1 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 1
  lower := (12924551/60740000)
  upper := (12936699/60740000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_1.interval_proof
}

def entry_11_2 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 2
  lower := (146398607/813930000)
  upper := (146561393/813930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_2.interval_proof
}

def entry_11_3 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 3
  lower := (142731359/886410000)
  upper := (142908641/886410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_3.interval_proof
}

def entry_11_4 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 4
  lower := (4931041/33340000)
  upper := (4937709/33340000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_4.interval_proof
}

def entry_11_5 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 5
  lower := (47031043/339570000)
  upper := (47098957/339570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_5.interval_proof
}

def entry_11_6 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 6
  lower := (38255551/294490000)
  upper := (38314449/294490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_6.interval_proof
}

def entry_11_7 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 7
  lower := (96270517/794830000)
  upper := (96429483/794830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_7.interval_proof
}

def entry_11_8 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 8
  lower := (27808387/241130000)
  upper := (27856613/241130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_8.interval_proof
}

def entry_11_9 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 9
  lower := (5335219/47810000)
  upper := (5344781/47810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_9.interval_proof
}

def entry_11_10 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 10
  lower := (79467961/720390000)
  upper := (79612039/720390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_10.interval_proof
}

def entry_11_11 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 11
  lower := (79880239/697610000)
  upper := (80019761/697610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_11.interval_proof
}

def entry_11_12 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 12
  lower := (36858559/364410000)
  upper := (36931441/364410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_12.interval_proof
}

def entry_11_13 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 13
  lower := (27340857/291430000)
  upper := (27399143/291430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_13.interval_proof
}

def entry_11_14 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 14
  lower := (52111121/588790000)
  upper := (52228879/588790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_14.interval_proof
}

def entry_11_15 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 15
  lower := (130283/1545000)
  upper := (16324/193125)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_15.interval_proof
}

def entry_11_16 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 16
  lower := (21553381/266190000)
  upper := (21606619/266190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_16.interval_proof
}

def entry_11_17 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 17
  lower := (3587397/46030000)
  upper := (3596603/46030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_17.interval_proof
}

def entry_11_18 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 18
  lower := (32107257/427430000)
  upper := (32192743/427430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_18.interval_proof
}

def entry_11_19 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 19
  lower := (1617779/22210000)
  upper := (1622221/22210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_19.interval_proof
}

def entry_11_20 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 20
  lower := (38505797/542030000)
  upper := (38614203/542030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_20.interval_proof
}

def entry_11_21 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 21
  lower := (17212859/246410000)
  upper := (17262141/246410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_21.interval_proof
}

def entry_11_22 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 22
  lower := (41151297/587030000)
  upper := (41268703/587030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_22.interval_proof
}

def entry_11_23 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 23
  lower := (1953439/29610000)
  upper := (1959361/29610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_23.interval_proof
}

def entry_11_24 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 24
  lower := (27746189/438110000)
  upper := (27833811/438110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_24.interval_proof
}

def entry_11_25 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 25
  lower := (360611/5890000)
  upper := (361789/5890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_25.interval_proof
}

def entry_11_26 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 26
  lower := (1793857/30180000)
  upper := (1799893/30180000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_26.interval_proof
}

def entry_11_27 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 27
  lower := (5244943/90570000)
  upper := (5263057/90570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_27.interval_proof
}

def entry_11_28 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 28
  lower := (48823551/864490000)
  upper := (48996449/864490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_28.interval_proof
}

def entry_11_29 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 29
  lower := (54900389/996110000)
  upper := (55099611/996110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_29.interval_proof
}

def entry_11_30 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 30
  lower := (19384071/359290000)
  upper := (19455929/359290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_30.interval_proof
}

def entry_11_31 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 31
  lower := (51792233/977670000)
  upper := (51987767/977670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_31.interval_proof
}

def entry_11_32 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 32
  lower := (23729591/454090000)
  upper := (23820409/454090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_32.interval_proof
}

def entry_11_33 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 33
  lower := (3752807/71930000)
  upper := (3767193/71930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_33.interval_proof
}

def entry_11_34 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 34
  lower := (35030131/698690000)
  upper := (35169869/698690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_34.interval_proof
}

def entry_11_35 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 35
  lower := (46314997/950030000)
  upper := (46505003/950030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_35.interval_proof
}

def entry_11_36 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 36
  lower := (27252747/572530000)
  upper := (27367253/572530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_36.interval_proof
}

def entry_11_37 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 37
  lower := (41800289/897110000)
  upper := (41979711/897110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_37.interval_proof
}

def entry_11_38 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 38
  lower := (528843/11570000)
  upper := (531157/11570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_38.interval_proof
}

def entry_11_39 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 39
  lower := (41886633/933670000)
  upper := (42073367/933670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_39.interval_proof
}

def entry_11_40 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 40
  lower := (295569/6710000)
  upper := (296911/6710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_40.interval_proof
}

def entry_11_41 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 41
  lower := (6439141/148590000)
  upper := (6468859/148590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_41.interval_proof
}

def entry_11_42 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 42
  lower := (7747863/181370000)
  upper := (7784137/181370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_42.interval_proof
}

def entry_11_43 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 43
  lower := (13847219/327810000)
  upper := (13912781/327810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_43.interval_proof
}

def entry_11_44 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 44
  lower := (1596709/37910000)
  upper := (1604291/37910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_44.interval_proof
}

def entry_11_45 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 45
  lower := (35273743/862570000)
  upper := (35446257/862570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_45.interval_proof
}

def entry_11_46 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 46
  lower := (2041151/50990000)
  upper := (2051349/50990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_46.interval_proof
}

def entry_11_47 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 47
  lower := (23689717/602830000)
  upper := (23810283/602830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_47.interval_proof
}

def entry_11_48 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 48
  lower := (13265673/343270000)
  upper := (13334327/343270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_48.interval_proof
}

def entry_11_49 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 49
  lower := (15274867/401330000)
  upper := (15355133/401330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_49.interval_proof
}

def entry_11_50 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 50
  lower := (36133637/963630000)
  upper := (36326363/963630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_11_50.interval_proof
}

def entry_12_1 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 1
  lower := (47665997/240030000)
  upper := (47714003/240030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_1.interval_proof
}

def entry_12_2 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 2
  lower := (69074523/404770000)
  upper := (69155477/404770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_2.interval_proof
}

def entry_12_3 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 3
  lower := (50607287/327130000)
  upper := (50672713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_3.interval_proof
}

def entry_12_4 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 4
  lower := (134556331/936690000)
  upper := (134743669/936690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_4.interval_proof
}

def entry_12_5 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 5
  lower := (40823471/315290000)
  upper := (40886529/315290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_5.interval_proof
}

def entry_12_6 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 6
  lower := (56760863/441370000)
  upper := (56849137/441370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_6.interval_proof
}

def entry_12_7 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 7
  lower := (94797571/824290000)
  upper := (94962429/824290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_7.interval_proof
}

def entry_12_8 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 8
  lower := (14656697/133030000)
  upper := (14683303/133030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_8.interval_proof
}

def entry_12_9 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 9
  lower := (12627979/120210000)
  upper := (12652021/120210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_9.interval_proof
}

def entry_12_10 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 10
  lower := (17482859/171410000)
  upper := (17517141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_10.interval_proof
}

def entry_12_11 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 11
  lower := (36858559/364410000)
  upper := (36931441/364410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_11.interval_proof
}

def entry_12_12 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 12
  lower := (99305383/946170000)
  upper := (99494617/946170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_12.interval_proof
}

def entry_12_13 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 13
  lower := (1308599/14010000)
  upper := (1311401/14010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_13.interval_proof
}

def entry_12_14 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 14
  lower := (40833059/469410000)
  upper := (40926941/469410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_14.interval_proof
}

def entry_12_15 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 15
  lower := (62534071/759290000)
  upper := (62685929/759290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_15.interval_proof
}

def entry_12_16 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 16
  lower := (3155993/40070000)
  upper := (3164007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_16.interval_proof
}

def entry_12_17 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 17
  lower := (12688163/168370000)
  upper := (12721837/168370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_17.interval_proof
}

def entry_12_18 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 18
  lower := (9766697/133030000)
  upper := (9793303/133030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_18.interval_proof
}

def entry_12_19 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 19
  lower := (2970771/42290000)
  upper := (2979229/42290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_19.interval_proof
}

def entry_12_20 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 20
  lower := (20140507/294930000)
  upper := (20199493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_20.interval_proof
}

def entry_12_21 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 21
  lower := (49345657/743430000)
  upper := (49494343/743430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_21.interval_proof
}

def entry_12_22 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 22
  lower := (27931963/430370000)
  upper := (28018037/430370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_22.interval_proof
}

def entry_12_23 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 23
  lower := (42833041/669590000)
  upper := (42966959/669590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_23.interval_proof
}

def entry_12_24 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 24
  lower := (14038151/218490000)
  upper := (14081849/218490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_24.interval_proof
}

def entry_12_25 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 25
  lower := (32336729/532710000)
  upper := (32443271/532710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_25.interval_proof
}

def entry_12_26 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 26
  lower := (44563717/762830000)
  upper := (44716283/762830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_26.interval_proof
}

def entry_12_27 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 27
  lower := (54284103/958970000)
  upper := (54475897/958970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_27.interval_proof
}

def entry_12_28 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 28
  lower := (22289539/404610000)
  upper := (22370461/404610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_28.interval_proof
}

def entry_12_29 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 29
  lower := (47351681/883190000)
  upper := (47528319/883190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_29.interval_proof
}

def entry_12_30 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 30
  lower := (6073461/115390000)
  upper := (6096539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_30.interval_proof
}

def entry_12_31 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 31
  lower := (21053881/411190000)
  upper := (21136119/411190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_31.interval_proof
}

def entry_12_32 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 32
  lower := (48912587/974130000)
  upper := (49107413/974130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_32.interval_proof
}

def entry_12_33 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 33
  lower := (19106193/388070000)
  upper := (19183807/388070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_33.interval_proof
}

def entry_12_34 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 34
  lower := (8864197/183030000)
  upper := (8900803/183030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_34.interval_proof
}

def entry_12_35 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 35
  lower := (4024091/84090000)
  upper := (4040909/84090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_35.interval_proof
}

def entry_12_36 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 36
  lower := (37910717/792830000)
  upper := (38069283/792830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_36.interval_proof
}

def entry_12_37 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 37
  lower := (16623917/360830000)
  upper := (16696083/360830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_37.interval_proof
}

def entry_12_38 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 38
  lower := (8236647/183530000)
  upper := (8273353/183530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_38.interval_proof
}

def entry_12_39 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 39
  lower := (35309559/804410000)
  upper := (35470441/804410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_39.interval_proof
}

def entry_12_40 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 40
  lower := (37014009/859910000)
  upper := (37185991/859910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_40.interval_proof
}

def entry_12_41 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 41
  lower := (892261/21140000)
  upper := (896489/21140000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_41.interval_proof
}

def entry_12_42 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 42
  lower := (38088471/915290000)
  upper := (38271529/915290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_42.interval_proof
}

def entry_12_43 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 43
  lower := (7595377/186230000)
  upper := (7632623/186230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_43.interval_proof
}

def entry_12_44 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 44
  lower := (18538861/461390000)
  upper := (18631139/461390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_44.interval_proof
}

def entry_12_45 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 45
  lower := (24099113/608870000)
  upper := (24220887/608870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_45.interval_proof
}

def entry_12_46 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 46
  lower := (3750401/95990000)
  upper := (3769599/95990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_46.interval_proof
}

def entry_12_47 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 47
  lower := (35647851/921490000)
  upper := (35832149/921490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_47.interval_proof
}

def entry_12_48 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 48
  lower := (12627287/327130000)
  upper := (12692713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_48.interval_proof
}

def entry_12_49 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 49
  lower := (4419481/117690000)
  upper := (4443019/117690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_49.interval_proof
}

def entry_12_50 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 50
  lower := (3649087/99130000)
  upper := (3668913/99130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_12_50.interval_proof
}

def entry_13_1 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 1
  lower := (53581241/287590000)
  upper := (53638759/287590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_1.interval_proof
}

def entry_13_2 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 2
  lower := (104703999/660010000)
  upper := (104836001/660010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_2.interval_proof
}

def entry_13_3 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 3
  lower := (50979311/356890000)
  upper := (51050689/356890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_3.interval_proof
}

def entry_13_4 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 4
  lower := (4026447/30530000)
  upper := (4032553/30530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_4.interval_proof
}

def entry_13_5 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 5
  lower := (114946181/938190000)
  upper := (115133819/938190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_5.interval_proof
}

def entry_13_6 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 6
  lower := (12443359/106410000)
  upper := (12464641/106410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_6.interval_proof
}

def entry_13_7 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 7
  lower := (13636439/123110000)
  upper := (13661061/123110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_7.interval_proof
}

def entry_13_8 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 8
  lower := (9109969/87810000)
  upper := (9127531/87810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_8.interval_proof
}

def entry_13_9 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 9
  lower := (16962929/170710000)
  upper := (16997071/170710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_9.interval_proof
}

def entry_13_10 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 10
  lower := (22993523/239770000)
  upper := (23041477/239770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_10.interval_proof
}

def entry_13_11 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 11
  lower := (27340857/291430000)
  upper := (27399143/291430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_11.interval_proof
}

def entry_13_12 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 12
  lower := (1308599/14010000)
  upper := (1311401/14010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_12.interval_proof
}

def entry_13_13 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 13
  lower := (67580239/697610000)
  upper := (67719761/697610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_13.interval_proof
}

def entry_13_14 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 14
  lower := (80816869/931310000)
  upper := (81003131/931310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_14.interval_proof
}

def entry_13_15 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 15
  lower := (26002911/320890000)
  upper := (26067089/320890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_15.interval_proof
}

def entry_13_16 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 16
  lower := (4146601/53990000)
  upper := (4157399/53990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_16.interval_proof
}

def entry_13_17 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 17
  lower := (22654157/308430000)
  upper := (22715843/308430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_17.interval_proof
}

def entry_13_18 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 18
  lower := (27021719/382810000)
  upper := (27098281/382810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_18.interval_proof
}

def entry_13_19 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 19
  lower := (18522891/271090000)
  upper := (18577109/271090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_19.interval_proof
}

def entry_13_20 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 20
  lower := (2653489/40110000)
  upper := (2661511/40110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_20.interval_proof
}

def entry_13_21 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 21
  lower := (47346051/739490000)
  upper := (47493949/739490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_21.interval_proof
}

def entry_13_22 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 22
  lower := (58376347/936530000)
  upper := (58563653/936530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_22.interval_proof
}

def entry_13_23 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 23
  lower := (23401551/384490000)
  upper := (23478449/384490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_23.interval_proof
}

def entry_13_24 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 24
  lower := (3969603/66470000)
  upper := (3982897/66470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_24.interval_proof
}

def entry_13_25 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 25
  lower := (13729231/232690000)
  upper := (13775769/232690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_25.interval_proof
}

def entry_13_26 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 26
  lower := (34811297/587030000)
  upper := (34928703/587030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_26.interval_proof
}

def entry_13_27 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 27
  lower := (29647261/527390000)
  upper := (29752739/527390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_27.interval_proof
}

def entry_13_28 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 28
  lower := (79129/1460000)
  upper := (79421/1460000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_28.interval_proof
}

def entry_13_29 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 29
  lower := (9853757/187430000)
  upper := (9891243/187430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_29.interval_proof
}

def entry_13_30 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 30
  lower := (297419/5810000)
  upper := (298581/5810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_30.interval_proof
}

def entry_13_31 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 31
  lower := (11080317/221830000)
  upper := (11124683/221830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_31.interval_proof
}

def entry_13_32 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 32
  lower := (18312553/374470000)
  upper := (18387447/374470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_32.interval_proof
}

def entry_13_33 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 33
  lower := (6895597/144030000)
  upper := (6924403/144030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_33.interval_proof
}

def entry_13_34 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 34
  lower := (2316307/49430000)
  upper := (2326193/49430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_34.interval_proof
}

def entry_13_35 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 35
  lower := (79587/1730000)
  upper := (79933/1730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_35.interval_proof
}

def entry_13_36 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 36
  lower := (22570103/498970000)
  upper := (22669897/498970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_36.interval_proof
}

def entry_13_37 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 37
  lower := (21571627/483730000)
  upper := (21668373/483730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_37.interval_proof
}

def entry_13_38 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 38
  lower := (20498557/464430000)
  upper := (20591443/464430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_38.interval_proof
}

def entry_13_39 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 39
  lower := (34970757/792430000)
  upper := (35129243/792430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_39.interval_proof
}

def entry_13_40 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 40
  lower := (6708259/157410000)
  upper := (6739741/157410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_40.interval_proof
}

def entry_13_41 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 41
  lower := (1534309/36910000)
  upper := (1541691/36910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_41.interval_proof
}

def entry_13_42 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 42
  lower := (4696459/115410000)
  upper := (4719541/115410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_42.interval_proof
}

def entry_13_43 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 43
  lower := (3418937/85630000)
  upper := (3436063/85630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_43.interval_proof
}

def entry_13_44 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 44
  lower := (33265189/848110000)
  upper := (33434811/848110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_44.interval_proof
}

def entry_13_45 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 45
  lower := (4076941/105590000)
  upper := (4098059/105590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_45.interval_proof
}

def entry_13_46 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 46
  lower := (8293179/218210000)
  upper := (8336821/218210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_46.interval_proof
}

def entry_13_47 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 47
  lower := (16052083/429170000)
  upper := (16137917/429170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_47.interval_proof
}

def entry_13_48 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 48
  lower := (239351/6490000)
  upper := (240649/6490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_48.interval_proof
}

def entry_13_49 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 49
  lower := (23784659/653410000)
  upper := (23915341/653410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_49.interval_proof
}

def entry_13_50 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 50
  lower := (1159279/32210000)
  upper := (1165721/32210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_13_50.interval_proof
}

def entry_14_1 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 1
  lower := (150274417/855830000)
  upper := (150445583/855830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_1.interval_proof
}

def entry_14_2 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 2
  lower := (77688731/512690000)
  upper := (77791269/512690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_2.interval_proof
}

def entry_14_3 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 3
  lower := (110508283/817170000)
  upper := (110671717/817170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_3.interval_proof
}

def entry_14_4 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 4
  lower := (103337357/826430000)
  upper := (103502643/826430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_4.interval_proof
}

def entry_14_5 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 5
  lower := (3848713/32870000)
  upper := (3855287/32870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_5.interval_proof
}

def entry_14_6 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 6
  lower := (2713939/24610000)
  upper := (2718861/24610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_6.interval_proof
}

def entry_14_7 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 7
  lower := (52417441/475590000)
  upper := (52512559/475590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_7.interval_proof
}

def entry_14_8 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 8
  lower := (24685219/247810000)
  upper := (24734781/247810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_8.interval_proof
}

def entry_14_9 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 9
  lower := (23572643/248570000)
  upper := (23622357/248570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_9.interval_proof
}

def entry_14_10 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 10
  lower := (18160087/199130000)
  upper := (18199913/199130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_10.interval_proof
}

def entry_14_11 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 11
  lower := (52111121/588790000)
  upper := (52228879/588790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_11.interval_proof
}

def entry_14_12 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 12
  lower := (40833059/469410000)
  upper := (40926941/469410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_12.interval_proof
}

def entry_14_13 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 13
  lower := (80816869/931310000)
  upper := (81003131/931310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_13.interval_proof
}

def entry_14_14 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 14
  lower := (28368461/315390000)
  upper := (28431539/315390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_14.interval_proof
}

def entry_14_15 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 15
  lower := (49139363/606370000)
  upper := (49260637/606370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_15.interval_proof
}

def entry_14_16 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 16
  lower := (55417003/729970000)
  upper := (55562997/729970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_16.interval_proof
}

def entry_14_17 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 17
  lower := (552753/7670000)
  upper := (554287/7670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_17.interval_proof
}

def entry_14_18 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 18
  lower := (11691061/169390000)
  upper := (11724939/169390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_18.interval_proof
}

def entry_14_19 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 19
  lower := (19860119/298810000)
  upper := (19919881/298810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_19.interval_proof
}

def entry_14_20 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 20
  lower := (43302617/673830000)
  upper := (43437383/673830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_20.interval_proof
}

def entry_14_21 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 21
  lower := (58586879/931210000)
  upper := (58773121/931210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_21.interval_proof
}

def entry_14_22 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 22
  lower := (58543251/967490000)
  upper := (58736749/967490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_22.interval_proof
}

def entry_14_23 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 23
  lower := (38664323/656770000)
  upper := (38795677/656770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_23.interval_proof
}

def entry_14_24 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 24
  lower := (47357571/824290000)
  upper := (47522429/824290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_24.interval_proof
}

def entry_14_25 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 25
  lower := (8859251/157490000)
  upper := (8890749/157490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_25.interval_proof
}

def entry_14_26 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 26
  lower := (1105003/19970000)
  upper := (1108997/19970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_26.interval_proof
}

def entry_14_27 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 27
  lower := (13547757/247430000)
  upper := (13597243/247430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_27.interval_proof
}

def entry_14_28 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 28
  lower := (24300863/441370000)
  upper := (24389137/441370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_28.interval_proof
}

def entry_14_29 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 29
  lower := (43447003/829970000)
  upper := (43612997/829970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_29.interval_proof
}

def entry_14_30 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 30
  lower := (14451421/285790000)
  upper := (14508579/285790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_30.interval_proof
}

def entry_14_31 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 31
  lower := (48012237/977630000)
  upper := (48207763/977630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_31.interval_proof
}

def entry_14_32 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 32
  lower := (522309/10910000)
  upper := (524491/10910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_32.interval_proof
}

def entry_14_33 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 33
  lower := (4819697/103030000)
  upper := (4840303/103030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_33.interval_proof
}

def entry_14_34 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 34
  lower := (5927057/129430000)
  upper := (5952943/129430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_34.interval_proof
}

def entry_14_35 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 35
  lower := (36429227/807730000)
  upper := (36590773/807730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_35.interval_proof
}

def entry_14_36 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 36
  lower := (41336101/938990000)
  upper := (41523899/938990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_36.interval_proof
}

def entry_14_37 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 37
  lower := (27127231/627690000)
  upper := (27252769/627690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_37.interval_proof
}

def entry_14_38 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 38
  lower := (29869709/702910000)
  upper := (30010291/702910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_38.interval_proof
}

def entry_14_39 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 39
  lower := (783129/18710000)
  upper := (786871/18710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_39.interval_proof
}

def entry_14_40 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 40
  lower := (38975703/942970000)
  upper := (39164297/942970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_40.interval_proof
}

def entry_14_41 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 41
  lower := (38875081/949190000)
  upper := (39064919/949190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_41.interval_proof
}

def entry_14_42 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 42
  lower := (32450797/792030000)
  upper := (32609203/792030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_42.interval_proof
}

def entry_14_43 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 43
  lower := (17535767/442330000)
  upper := (17624233/442330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_43.interval_proof
}

def entry_14_44 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 44
  lower := (33852577/874230000)
  upper := (34027423/874230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_44.interval_proof
}

def entry_14_45 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 45
  lower := (8871619/233810000)
  upper := (8918381/233810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_45.interval_proof
}

def entry_14_46 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 46
  lower := (2808463/75370000)
  upper := (2823537/75370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_46.interval_proof
}

def entry_14_47 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 47
  lower := (2553033/69670000)
  upper := (2566967/69670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_47.interval_proof
}

def entry_14_48 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 48
  lower := (3970993/110070000)
  upper := (3993007/110070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_48.interval_proof
}

def entry_14_49 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 49
  lower := (139409/3910000)
  upper := (140191/3910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_49.interval_proof
}

def entry_14_50 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 50
  lower := (2557699/73010000)
  upper := (2572301/73010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_14_50.interval_proof
}

def entry_15_1 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 1
  lower := (161452817/971830000)
  upper := (161647183/971830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_1.interval_proof
}

def entry_15_2 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 2
  lower := (8406591/59090000)
  upper := (8418409/59090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_2.interval_proof
}

def entry_15_3 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 3
  lower := (42827239/327610000)
  upper := (42892761/327610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_3.interval_proof
}

def entry_15_4 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 4
  lower := (22107413/185870000)
  upper := (22144587/185870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_4.interval_proof
}

def entry_15_5 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 5
  lower := (107626331/936690000)
  upper := (107813669/936690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_5.interval_proof
}

def entry_15_6 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 6
  lower := (12158461/115390000)
  upper := (12181539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_6.interval_proof
}

def entry_15_7 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 7
  lower := (28931421/285790000)
  upper := (28988579/285790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_7.interval_proof
}

def entry_15_8 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 8
  lower := (52665471/545290000)
  upper := (52774529/545290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_8.interval_proof
}

def entry_15_9 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 9
  lower := (80591521/884790000)
  upper := (80768479/884790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_9.interval_proof
}

def entry_15_10 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 10
  lower := (2109169/23935000)
  upper := (528489/5983750)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_10.interval_proof
}

def entry_15_11 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 11
  lower := (130283/1545000)
  upper := (16324/193125)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_11.interval_proof
}

def entry_15_12 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 12
  lower := (62534071/759290000)
  upper := (62685929/759290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_12.interval_proof
}

def entry_15_13 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 13
  lower := (26002911/320890000)
  upper := (26067089/320890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_13.interval_proof
}

def entry_15_14 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 14
  lower := (49139363/606370000)
  upper := (49260637/606370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_14.interval_proof
}

def entry_15_15 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 15
  lower := (58560239/697610000)
  upper := (58699761/697610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_15.interval_proof
}

def entry_15_16 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 16
  lower := (43632603/573970000)
  upper := (43747397/573970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_16.interval_proof
}

def entry_15_17 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 17
  lower := (29174127/408730000)
  upper := (29255873/408730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_17.interval_proof
}

def entry_15_18 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 18
  lower := (34948577/514230000)
  upper := (35051423/514230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_18.interval_proof
}

def entry_15_19 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 19
  lower := (3683343/56570000)
  upper := (3694657/56570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_19.interval_proof
}

def entry_15_20 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 20
  lower := (2523993/40070000)
  upper := (2532007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_20.interval_proof
}

def entry_15_21 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 21
  lower := (12100087/199130000)
  upper := (12139913/199130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_21.interval_proof
}

def entry_15_22 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 22
  lower := (39662891/671090000)
  upper := (39797109/671090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_22.interval_proof
}

def entry_15_23 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 23
  lower := (2429273/42270000)
  upper := (2437727/42270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_23.interval_proof
}

def entry_15_24 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 24
  lower := (837001/14990000)
  upper := (839999/14990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_24.interval_proof
}

def entry_15_25 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 25
  lower := (40356103/738970000)
  upper := (40503897/738970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_25.interval_proof
}

def entry_15_26 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 26
  lower := (25631903/480970000)
  upper := (25728097/480970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_26.interval_proof
}

def entry_15_27 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 27
  lower := (17207117/328830000)
  upper := (17272883/328830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_27.interval_proof
}

def entry_15_28 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 28
  lower := (32506923/630770000)
  upper := (32633077/630770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_28.interval_proof
}

def entry_15_29 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 29
  lower := (14501609/283910000)
  upper := (14558391/283910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_29.interval_proof
}

def entry_15_30 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 30
  lower := (16952007/329930000)
  upper := (17017993/329930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_30.interval_proof
}

def entry_15_31 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 31
  lower := (8036093/164070000)
  upper := (8068907/164070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_31.interval_proof
}

def entry_15_32 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 32
  lower := (9438081/199190000)
  upper := (9477919/199190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_32.interval_proof
}

def entry_15_33 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 33
  lower := (40362447/875530000)
  upper := (40537553/875530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_33.interval_proof
}

def entry_15_34 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 34
  lower := (67001/1490000)
  upper := (67299/1490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_34.interval_proof
}

def entry_15_35 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 35
  lower := (1159867/26330000)
  upper := (1165133/26330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_35.interval_proof
}

def entry_15_36 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 36
  lower := (12481037/289630000)
  upper := (12538963/289630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_36.interval_proof
}

def entry_15_37 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 37
  lower := (26716867/631330000)
  upper := (26843133/631330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_37.interval_proof
}

def entry_15_38 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 38
  lower := (31334581/754190000)
  upper := (31485419/754190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_38.interval_proof
}

def entry_15_39 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 39
  lower := (38595341/946590000)
  upper := (38784659/946590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_39.interval_proof
}

def entry_15_40 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 40
  lower := (30863129/768710000)
  upper := (31016871/768710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_40.interval_proof
}

def entry_15_41 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 41
  lower := (34372949/870510000)
  upper := (34547051/870510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_41.interval_proof
}

def entry_15_42 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 42
  lower := (1280713/32870000)
  upper := (1287287/32870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_42.interval_proof
}

def entry_15_43 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 43
  lower := (18362319/476810000)
  upper := (18457681/476810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_43.interval_proof
}

def entry_15_44 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 44
  lower := (37751183/988170000)
  upper := (37948817/988170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_44.interval_proof
}

def entry_15_45 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 45
  lower := (2757787/72130000)
  upper := (2772213/72130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_45.interval_proof
}

def entry_15_46 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 46
  lower := (6163369/166310000)
  upper := (6196631/166310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_46.interval_proof
}

def entry_15_47 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 47
  lower := (12495517/344830000)
  upper := (12564483/344830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_47.interval_proof
}

def entry_15_48 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 48
  lower := (10540353/296470000)
  upper := (10599647/296470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_48.interval_proof
}

def entry_15_49 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 49
  lower := (6194767/177330000)
  upper := (6230233/177330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_49.interval_proof
}

def entry_15_50 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 50
  lower := (29594009/859910000)
  upper := (29765991/859910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_15_50.interval_proof
}

def entry_16_1 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 1
  lower := (149864983/950170000)
  upper := (150055017/950170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_1.interval_proof
}

def entry_16_2 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 2
  lower := (7473279/54710000)
  upper := (7484221/54710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_2.interval_proof
}

def entry_16_3 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 3
  lower := (19793853/161470000)
  upper := (19826147/161470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_3.interval_proof
}

def entry_16_4 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 4
  lower := (37947287/327130000)
  upper := (38012713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_4.interval_proof
}

def entry_16_5 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 5
  lower := (19049673/178270000)
  upper := (19085327/178270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_5.interval_proof
}

def entry_16_6 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 6
  lower := (4012883/39920000)
  upper := (4020867/39920000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_6.interval_proof
}

def entry_16_7 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 7
  lower := (1045709/10910000)
  upper := (1047891/10910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_7.interval_proof
}

def entry_16_8 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 8
  lower := (7022717/72830000)
  upper := (7037283/72830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_8.interval_proof
}

def entry_16_9 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 9
  lower := (12042277/137230000)
  upper := (12069723/137230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_9.interval_proof
}

def entry_16_10 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 10
  lower := (1256251/14990000)
  upper := (1259249/14990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_10.interval_proof
}

def entry_16_11 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 11
  lower := (21553381/266190000)
  upper := (21606619/266190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_11.interval_proof
}

def entry_16_12 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 12
  lower := (3155993/40070000)
  upper := (3164007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_12.interval_proof
}

def entry_16_13 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 13
  lower := (4146601/53990000)
  upper := (4157399/53990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_13.interval_proof
}

def entry_16_14 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 14
  lower := (55417003/729970000)
  upper := (55562997/729970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_14.interval_proof
}

def entry_16_15 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 15
  lower := (43632603/573970000)
  upper := (43747397/573970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_15.interval_proof
}

def entry_16_16 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 16
  lower := (24818461/315390000)
  upper := (24881539/315390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_16.interval_proof
}

def entry_16_17 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 17
  lower := (36109561/504390000)
  upper := (36210439/504390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_17.interval_proof
}

def entry_16_18 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 18
  lower := (36795403/545970000)
  upper := (36904597/545970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_18.interval_proof
}

def entry_16_19 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 19
  lower := (33687533/524670000)
  upper := (33792467/524670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_19.interval_proof
}

def entry_16_20 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 20
  lower := (21470227/347730000)
  upper := (21539773/347730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_20.interval_proof
}

def entry_16_21 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 21
  lower := (3135981/52690000)
  upper := (3146519/52690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_21.interval_proof
}

def entry_16_22 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 22
  lower := (3813381/66190000)
  upper := (3826619/66190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_22.interval_proof
}

def entry_16_23 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 23
  lower := (36085559/644410000)
  upper := (36214441/644410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_23.interval_proof
}

def entry_16_24 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 24
  lower := (7321697/133030000)
  upper := (7348303/133030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_24.interval_proof
}

def entry_16_25 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 25
  lower := (4537709/85410000)
  upper := (4554791/85410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_25.interval_proof
}

def entry_16_26 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 26
  lower := (9094451/175490000)
  upper := (9129549/175490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_26.interval_proof
}

def entry_16_27 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 27
  lower := (42057073/829270000)
  upper := (42222927/829270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_27.interval_proof
}

def entry_16_28 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 28
  lower := (12330219/247810000)
  upper := (12379781/247810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_28.interval_proof
}

def entry_16_29 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 29
  lower := (2229189/45610000)
  upper := (2238311/45610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_29.interval_proof
}

def entry_16_30 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 30
  lower := (26305471/545290000)
  upper := (26414529/545290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_30.interval_proof
}

def entry_16_31 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 31
  lower := (4036567/84330000)
  upper := (4053433/84330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_31.interval_proof
}

def entry_16_32 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 32
  lower := (3507717/72830000)
  upper := (3522283/72830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_32.interval_proof
}

def entry_16_33 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 33
  lower := (1251281/27190000)
  upper := (1256719/27190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_33.interval_proof
}

def entry_16_34 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 34
  lower := (5283151/118490000)
  upper := (5306849/118490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_34.interval_proof
}

def entry_16_35 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 35
  lower := (15514261/357390000)
  upper := (15585739/357390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_35.interval_proof
}

def entry_16_36 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 36
  lower := (671667/15830000)
  upper := (674833/15830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_36.interval_proof
}

def entry_16_37 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 37
  lower := (11133181/268190000)
  upper := (11186819/268190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_37.interval_proof
}

def entry_16_38 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 38
  lower := (18270097/449030000)
  upper := (18359903/449030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_38.interval_proof
}

def entry_16_39 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 39
  lower := (37994907/950930000)
  upper := (38185093/950930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_39.interval_proof
}

def entry_16_40 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 40
  lower := (4552211/115390000)
  upper := (4575289/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_40.interval_proof
}

def entry_16_41 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 41
  lower := (4620031/119690000)
  upper := (4643969/119690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_41.interval_proof
}

def entry_16_42 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 42
  lower := (16426733/432670000)
  upper := (16513267/432670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_42.interval_proof
}

def entry_16_43 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 43
  lower := (1055179/28210000)
  upper := (1060821/28210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_43.interval_proof
}

def entry_16_44 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 44
  lower := (895573/24270000)
  upper := (900427/24270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_44.interval_proof
}

def entry_16_45 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 45
  lower := (6534561/179390000)
  upper := (6570439/179390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_45.interval_proof
}

def entry_16_46 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 46
  lower := (453941/12590000)
  upper := (456459/12590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_46.interval_proof
}

def entry_16_47 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 47
  lower := (9159413/255870000)
  upper := (9210587/255870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_47.interval_proof
}

def entry_16_48 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 48
  lower := (33626171/938290000)
  upper := (33813829/938290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_48.interval_proof
}

def entry_16_49 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 49
  lower := (4469653/128470000)
  upper := (4495347/128470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_49.interval_proof
}

def entry_16_50 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 50
  lower := (762511/22390000)
  upper := (766989/22390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_16_50.interval_proof
}

def entry_17_1 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 1
  lower := (149910189/998110000)
  upper := (150109811/998110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_1.interval_proof
}

def entry_17_2 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 2
  lower := (856697/6630000)
  upper := (858023/6630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_2.interval_proof
}

def entry_17_3 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 3
  lower := (6694909/57160000)
  upper := (6706341/57160000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_3.interval_proof
}

def entry_17_4 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 4
  lower := (3296469/30310000)
  upper := (3302531/30310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_4.interval_proof
}

def entry_17_5 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 5
  lower := (43667113/428870000)
  upper := (43752887/428870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_5.interval_proof
}

def entry_17_6 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 6
  lower := (79068453/815470000)
  upper := (79231547/815470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_6.interval_proof
}

def entry_17_7 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 7
  lower := (41439803/451970000)
  upper := (41530197/451970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_7.interval_proof
}

def entry_17_8 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 8
  lower := (10578151/118490000)
  upper := (10601849/118490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_8.interval_proof
}

def entry_17_9 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 9
  lower := (25929723/302770000)
  upper := (25990277/302770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_9.interval_proof
}

def entry_17_10 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 10
  lower := (35975501/444990000)
  upper := (36064499/444990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_10.interval_proof
}

def entry_17_11 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 11
  lower := (3587397/46030000)
  upper := (3596603/46030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_11.interval_proof
}

def entry_17_12 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 12
  lower := (12688163/168370000)
  upper := (12721837/168370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_12.interval_proof
}

def entry_17_13 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 13
  lower := (22654157/308430000)
  upper := (22715843/308430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_13.interval_proof
}

def entry_17_14 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 14
  lower := (552753/7670000)
  upper := (554287/7670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_14.interval_proof
}

def entry_17_15 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 15
  lower := (29174127/408730000)
  upper := (29255873/408730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_15.interval_proof
}

def entry_17_16 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 16
  lower := (36109561/504390000)
  upper := (36210439/504390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_16.interval_proof
}

def entry_17_17 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 17
  lower := (6651019/89810000)
  upper := (6668981/89810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_17.interval_proof
}

def entry_17_18 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 18
  lower := (40150653/593470000)
  upper := (40269347/593470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_18.interval_proof
}

def entry_17_19 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 19
  lower := (9257493/145070000)
  upper := (9286507/145070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_19.interval_proof
}

def entry_17_20 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 20
  lower := (43069279/707210000)
  upper := (43210721/707210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_20.interval_proof
}

def entry_17_21 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 21
  lower := (34800559/594410000)
  upper := (34919441/594410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_21.interval_proof
}

def entry_17_22 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 22
  lower := (693773/12270000)
  upper := (696227/12270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_22.interval_proof
}

def entry_17_23 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 23
  lower := (930179/16960000)
  upper := (933571/16960000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_23.interval_proof
}

def entry_17_24 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 24
  lower := (48798413/915870000)
  upper := (48981587/915870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_24.interval_proof
}

def entry_17_25 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 25
  lower := (47688419/915810000)
  upper := (47871581/915810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_25.interval_proof
}

def entry_17_26 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 26
  lower := (7071081/139190000)
  upper := (7098919/139190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_26.interval_proof
}

def entry_17_27 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 27
  lower := (35897419/725810000)
  upper := (36042581/725810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_27.interval_proof
}

def entry_17_28 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 28
  lower := (706141/14590000)
  upper := (709059/14590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_28.interval_proof
}

def entry_17_29 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 29
  lower := (202947/4280000)
  upper := (203803/4280000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_29.interval_proof
}

def entry_17_30 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 30
  lower := (25285717/542830000)
  upper := (25394283/542830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_30.interval_proof
}

def entry_17_31 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 31
  lower := (5416193/118070000)
  upper := (5439807/118070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_31.interval_proof
}

def entry_17_32 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 32
  lower := (12412621/273790000)
  upper := (12467379/273790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_32.interval_proof
}

def entry_17_33 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 33
  lower := (5036317/111830000)
  upper := (5058683/111830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_33.interval_proof
}

def entry_17_34 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 34
  lower := (4563681/100690000)
  upper := (4583819/100690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_34.interval_proof
}

def entry_17_35 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 35
  lower := (4729103/108970000)
  upper := (4750897/108970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_35.interval_proof
}

def entry_17_36 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 36
  lower := (20296787/482130000)
  upper := (20393213/482130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_36.interval_proof
}

def entry_17_37 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 37
  lower := (6554027/159730000)
  upper := (6585973/159730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_37.interval_proof
}

def entry_17_38 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 38
  lower := (201373/5020000)
  upper := (202377/5020000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_38.interval_proof
}

def entry_17_39 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 39
  lower := (4118269/104810000)
  upper := (4139231/104810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_39.interval_proof
}

def entry_17_40 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 40
  lower := (28127059/729410000)
  upper := (28272941/729410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_40.interval_proof
}

def entry_17_41 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 41
  lower := (22031821/581790000)
  upper := (22148179/581790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_41.interval_proof
}

def entry_17_42 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 42
  lower := (30119241/807590000)
  upper := (30280759/807590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_42.interval_proof
}

def entry_17_43 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 43
  lower := (27664609/753910000)
  upper := (27815391/753910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_43.interval_proof
}

def entry_17_44 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 44
  lower := (22796791/632090000)
  upper := (22923209/632090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_44.interval_proof
}

def entry_17_45 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 45
  lower := (25388563/714370000)
  upper := (25531437/714370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_45.interval_proof
}

def entry_17_46 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 46
  lower := (15490793/442070000)
  upper := (15579207/442070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_46.interval_proof
}

def entry_17_47 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 47
  lower := (125597/3630000)
  upper := (126323/3630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_47.interval_proof
}

def entry_17_48 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 48
  lower := (23491331/686690000)
  upper := (23628669/686690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_48.interval_proof
}

def entry_17_49 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 49
  lower := (20748779/612210000)
  upper := (20871221/612210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_49.interval_proof
}

def entry_17_50 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 50
  lower := (6069477/180230000)
  upper := (6105523/180230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_17_50.interval_proof
}

def entry_18_1 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 1
  lower := (65389403/455970000)
  upper := (65480597/455970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_1.interval_proof
}

def entry_18_2 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 2
  lower := (40807243/327570000)
  upper := (40872757/327570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_2.interval_proof
}

def entry_18_3 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 3
  lower := (9472921/83290000)
  upper := (9489579/83290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_3.interval_proof
}

def entry_18_4 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 4
  lower := (52819343/506570000)
  upper := (52920657/506570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_4.interval_proof
}

def entry_18_5 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 5
  lower := (24899519/254810000)
  upper := (24950481/254810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_5.interval_proof
}

def entry_18_6 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 6
  lower := (48279569/504310000)
  upper := (48380431/504310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_6.interval_proof
}

def entry_18_7 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 7
  lower := (42916311/486890000)
  upper := (43013689/486890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_7.interval_proof
}

def entry_18_8 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 8
  lower := (81474103/958970000)
  upper := (81665897/958970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_8.interval_proof
}

def entry_18_9 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 9
  lower := (37825863/441370000)
  upper := (37914137/441370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_9.interval_proof
}

def entry_18_10 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 10
  lower := (8609039/109610000)
  upper := (8630961/109610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_10.interval_proof
}

def entry_18_11 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 11
  lower := (32107257/427430000)
  upper := (32192743/427430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_11.interval_proof
}

def entry_18_12 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 12
  lower := (9766697/133030000)
  upper := (9793303/133030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_12.interval_proof
}

def entry_18_13 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 13
  lower := (27021719/382810000)
  upper := (27098281/382810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_13.interval_proof
}

def entry_18_14 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 14
  lower := (11691061/169390000)
  upper := (11724939/169390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_14.interval_proof
}

def entry_18_15 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 15
  lower := (34948577/514230000)
  upper := (35051423/514230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_15.interval_proof
}

def entry_18_16 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 16
  lower := (36795403/545970000)
  upper := (36904597/545970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_16.interval_proof
}

def entry_18_17 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 17
  lower := (40150653/593470000)
  upper := (40269347/593470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_17.interval_proof
}

def entry_18_18 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 18
  lower := (6281019/89810000)
  upper := (6298981/89810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_18.interval_proof
}

def entry_18_19 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 19
  lower := (30397601/473990000)
  upper := (30492399/473990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_19.interval_proof
}

def entry_18_20 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 20
  lower := (44356831/731690000)
  upper := (44503169/731690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_20.interval_proof
}

def entry_18_21 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 21
  lower := (50772399/876010000)
  upper := (50947601/876010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_21.interval_proof
}

def entry_18_22 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 22
  lower := (2665219/47810000)
  upper := (2674781/47810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_22.interval_proof
}

def entry_18_23 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 23
  lower := (53750251/997490000)
  upper := (53949749/997490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_23.interval_proof
}

def entry_18_24 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 24
  lower := (6307979/120210000)
  upper := (6332021/120210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_24.interval_proof
}

def entry_18_25 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 25
  lower := (50820057/999430000)
  upper := (51019943/999430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_25.interval_proof
}

def entry_18_26 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 26
  lower := (8472929/170710000)
  upper := (8507071/170710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_26.interval_proof
}

def entry_18_27 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 27
  lower := (6506697/133030000)
  upper := (6533303/133030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_27.interval_proof
}

def entry_18_28 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 28
  lower := (46282289/977110000)
  upper := (46477711/977110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_28.interval_proof
}

def entry_18_29 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 29
  lower := (29725781/642190000)
  upper := (29854219/642190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_29.interval_proof
}

def entry_18_30 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 30
  lower := (40251521/884790000)
  upper := (40428479/884790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_30.interval_proof
}

def entry_18_31 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 31
  lower := (12506921/280790000)
  upper := (12563079/280790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_31.interval_proof
}

def entry_18_32 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 32
  lower := (6014277/137230000)
  upper := (6041723/137230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_32.interval_proof
}

def entry_18_33 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 33
  lower := (18606963/430370000)
  upper := (18693037/430370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_33.interval_proof
}

def entry_18_34 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 34
  lower := (12949723/302770000)
  upper := (13010277/302770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_34.interval_proof
}

def entry_18_35 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 35
  lower := (11263511/264890000)
  upper := (11316489/264890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_35.interval_proof
}

def entry_18_36 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 36
  lower := (18890863/441370000)
  upper := (18979137/441370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_36.interval_proof
}

def entry_18_37 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 37
  lower := (3880549/94510000)
  upper := (3899451/94510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_37.interval_proof
}

def entry_18_38 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 38
  lower := (12518609/313910000)
  upper := (12581391/313910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_38.interval_proof
}

def entry_18_39 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 39
  lower := (8106667/208330000)
  upper := (8148333/208330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_39.interval_proof
}

def entry_18_40 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 40
  lower := (3453427/90730000)
  upper := (3471573/90730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_40.interval_proof
}

def entry_18_41 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 41
  lower := (25242343/676570000)
  upper := (25377657/676570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_41.interval_proof
}

def entry_18_42 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 42
  lower := (5816149/158510000)
  upper := (5847851/158510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_42.interval_proof
}

def entry_18_43 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 43
  lower := (19595569/544310000)
  upper := (19704431/544310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_43.interval_proof
}

def entry_18_44 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 44
  lower := (10071583/284170000)
  upper := (10128417/284170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_44.interval_proof
}

def entry_18_45 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 45
  lower := (12135383/346170000)
  upper := (12204617/346170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_45.interval_proof
}

def entry_18_46 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 46
  lower := (9133427/265730000)
  upper := (9186573/265730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_46.interval_proof
}

def entry_18_47 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 47
  lower := (25624307/756930000)
  upper := (25775693/756930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_47.interval_proof
}

def entry_18_48 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 48
  lower := (12128731/362690000)
  upper := (12201269/362690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_48.interval_proof
}

def entry_18_49 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 49
  lower := (23957329/726710000)
  upper := (24102671/726710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_49.interval_proof
}

def entry_18_50 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 50
  lower := (11404999/350010000)
  upper := (11475001/350010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_18_50.interval_proof
}

def entry_19_1 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 1
  lower := (2263351/16490000)
  upper := (2266649/16490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_1.interval_proof
}

def entry_19_2 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 2
  lower := (37213607/313930000)
  upper := (37276393/313930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_2.interval_proof
}

def entry_19_3 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 3
  lower := (9353321/86790000)
  upper := (9370679/86790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_3.interval_proof
}

def entry_19_4 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 4
  lower := (13139383/131170000)
  upper := (13165617/131170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_4.interval_proof
}

def entry_19_5 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 5
  lower := (37759987/400130000)
  upper := (37840013/400130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_5.interval_proof
}

def entry_19_6 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 6
  lower := (16491647/183530000)
  upper := (16528353/183530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_6.interval_proof
}

def entry_19_7 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 7
  lower := (2231877/26230000)
  upper := (2237123/26230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_7.interval_proof
}

def entry_19_8 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 8
  lower := (36585097/449030000)
  upper := (36674903/449030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_8.interval_proof
}

def entry_19_9 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 9
  lower := (25068609/313910000)
  upper := (25131391/313910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_9.interval_proof
}

def entry_19_10 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 10
  lower := (12617601/163990000)
  upper := (12650399/163990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_10.interval_proof
}

def entry_19_11 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 11
  lower := (1617779/22210000)
  upper := (1622221/22210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_11.interval_proof
}

def entry_19_12 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 12
  lower := (2970771/42290000)
  upper := (2979229/42290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_12.interval_proof
}

def entry_19_13 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 13
  lower := (18522891/271090000)
  upper := (18577109/271090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_13.interval_proof
}

def entry_19_14 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 14
  lower := (19860119/298810000)
  upper := (19919881/298810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_14.interval_proof
}

def entry_19_15 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 15
  lower := (3683343/56570000)
  upper := (3694657/56570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_15.interval_proof
}

def entry_19_16 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 16
  lower := (33687533/524670000)
  upper := (33792467/524670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_16.interval_proof
}

def entry_19_17 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 17
  lower := (9257493/145070000)
  upper := (9286507/145070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_17.interval_proof
}

def entry_19_18 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 18
  lower := (30397601/473990000)
  upper := (30492399/473990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_18.interval_proof
}

def entry_19_19 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 19
  lower := (14183591/214090000)
  upper := (14226409/214090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_19.interval_proof
}

def entry_19_20 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 20
  lower := (54370809/891910000)
  upper := (54549191/891910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_20.interval_proof
}

def entry_19_21 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 21
  lower := (4814659/83410000)
  upper := (4831341/83410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_21.interval_proof
}

def entry_19_22 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 22
  lower := (110893/2007500)
  upper := (222589/4015000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_22.interval_proof
}

def entry_19_23 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 23
  lower := (11945051/224490000)
  upper := (11989949/224490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_23.interval_proof
}

def entry_19_24 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 24
  lower := (48465881/941190000)
  upper := (48654119/941190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_24.interval_proof
}

def entry_19_25 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 25
  lower := (23597829/471710000)
  upper := (23692171/471710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_25.interval_proof
}

def entry_19_26 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 26
  lower := (2966403/60970000)
  upper := (2978597/60970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_26.interval_proof
}

def entry_19_27 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 27
  lower := (19972921/420790000)
  upper := (20057079/420790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_27.interval_proof
}

def entry_19_28 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 28
  lower := (1937337/41630000)
  upper := (1945663/41630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_28.interval_proof
}

def entry_19_29 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 29
  lower := (7351849/161510000)
  upper := (7384151/161510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_29.interval_proof
}

def entry_19_30 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 30
  lower := (9328993/210070000)
  upper := (9371007/210070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_30.interval_proof
}

def entry_19_31 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 31
  lower := (39698773/912270000)
  upper := (39881227/912270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_31.interval_proof
}

def entry_19_32 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 32
  lower := (327593/7663750)
  upper := (1316503/30655000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_32.interval_proof
}

def entry_19_33 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 33
  lower := (7943591/189090000)
  upper := (7981409/189090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_33.interval_proof
}

def entry_19_34 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 34
  lower := (468867/11330000)
  upper := (471133/11330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_34.interval_proof
}

def entry_19_35 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 35
  lower := (2254483/55170000)
  upper := (2265517/55170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_35.interval_proof
}

def entry_19_36 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 36
  lower := (6100927/150730000)
  upper := (6131073/150730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_36.interval_proof
}

def entry_19_37 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 37
  lower := (7229549/179510000)
  upper := (7265451/179510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_37.interval_proof
}

def entry_19_38 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 38
  lower := (2952717/72830000)
  upper := (2967283/72830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_38.interval_proof
}

def entry_19_39 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 39
  lower := (6868371/176290000)
  upper := (6903629/176290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_39.interval_proof
}

def entry_19_40 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 40
  lower := (25602411/675890000)
  upper := (25737589/675890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_40.interval_proof
}

def entry_19_41 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 41
  lower := (31435011/849890000)
  upper := (31604989/849890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_41.interval_proof
}

def entry_19_42 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 42
  lower := (24213137/668630000)
  upper := (24346863/668630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_42.interval_proof
}

def entry_19_43 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 43
  lower := (17121803/481970000)
  upper := (17218197/481970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_43.interval_proof
}

def entry_19_44 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 44
  lower := (2071067/59330000)
  upper := (2082933/59330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_44.interval_proof
}

def entry_19_45 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 45
  lower := (1547989/45110000)
  upper := (1557011/45110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_45.interval_proof
}

def entry_19_46 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 46
  lower := (22294007/659930000)
  upper := (22425993/659930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_46.interval_proof
}

def entry_19_47 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 47
  lower := (107677/3230000)
  upper := (108323/3230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_47.interval_proof
}

def entry_19_48 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 48
  lower := (29041609/883910000)
  upper := (29218391/883910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_48.interval_proof
}

def entry_19_49 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 49
  lower := (29658291/917090000)
  upper := (29841709/917090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_49.interval_proof
}

def entry_19_50 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 50
  lower := (21941223/687770000)
  upper := (22078777/687770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_19_50.interval_proof
}

def entry_20_1 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 1
  lower := (44721031/339690000)
  upper := (44788969/339690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_1.interval_proof
}

def entry_20_2 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 2
  lower := (40714493/355070000)
  upper := (40785507/355070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_2.interval_proof
}

def entry_20_3 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 3
  lower := (37633689/363110000)
  upper := (37706311/363110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_3.interval_proof
}

def entry_20_4 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 4
  lower := (32112239/327610000)
  upper := (32177761/327610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_4.interval_proof
}

def entry_20_5 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 5
  lower := (21841459/235410000)
  upper := (21888541/235410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_5.interval_proof
}

def entry_20_6 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 6
  lower := (32207631/373690000)
  upper := (32282369/373690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_6.interval_proof
}

def entry_20_7 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 7
  lower := (78045703/942970000)
  upper := (78234297/942970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_7.interval_proof
}

def entry_20_8 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 8
  lower := (9115961/115390000)
  upper := (9139039/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_8.interval_proof
}

def entry_20_9 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 9
  lower := (6915927/90730000)
  upper := (6934073/90730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_9.interval_proof
}

def entry_20_10 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 10
  lower := (73694443/955570000)
  upper := (73885557/955570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_10.interval_proof
}

def entry_20_11 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 11
  lower := (38505797/542030000)
  upper := (38614203/542030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_11.interval_proof
}

def entry_20_12 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 12
  lower := (20140507/294930000)
  upper := (20199493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_12.interval_proof
}

def entry_20_13 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 13
  lower := (2653489/40110000)
  upper := (2661511/40110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_13.interval_proof
}

def entry_20_14 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 14
  lower := (43302617/673830000)
  upper := (43437383/673830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_14.interval_proof
}

def entry_20_15 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 15
  lower := (2523993/40070000)
  upper := (2532007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_15.interval_proof
}

def entry_20_16 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 16
  lower := (21470227/347730000)
  upper := (21539773/347730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_16.interval_proof
}

def entry_20_17 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 17
  lower := (43069279/707210000)
  upper := (43210721/707210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_17.interval_proof
}

def entry_20_18 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 18
  lower := (44356831/731690000)
  upper := (44503169/731690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_18.interval_proof
}

def entry_20_19 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 19
  lower := (54370809/891910000)
  upper := (54549191/891910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_19.interval_proof
}

def entry_20_20 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 20
  lower := (19848461/315390000)
  upper := (19911539/315390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_20.interval_proof
}

def entry_20_21 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 21
  lower := (8423/145000)
  upper := (2113/36250)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_21.interval_proof
}

def entry_20_22 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 22
  lower := (39697961/720390000)
  upper := (39842039/720390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_22.interval_proof
}

def entry_20_23 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 23
  lower := (634049/12010000)
  upper := (636451/12010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_23.interval_proof
}

def entry_20_24 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 24
  lower := (8732859/171410000)
  upper := (8767141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_24.interval_proof
}

def entry_20_25 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 25
  lower := (23472461/475390000)
  upper := (23567539/475390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_25.interval_proof
}

def entry_20_26 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 26
  lower := (8749733/182670000)
  upper := (8786267/182670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_26.interval_proof
}

def entry_20_27 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 27
  lower := (7711481/165190000)
  upper := (7744519/165190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_27.interval_proof
}

def entry_20_28 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 28
  lower := (9070087/199130000)
  upper := (9109913/199130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_28.interval_proof
}

def entry_20_29 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 29
  lower := (5203323/116770000)
  upper := (5226677/116770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_29.interval_proof
}

def entry_20_30 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 30
  lower := (38143331/866690000)
  upper := (38316669/866690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_30.interval_proof
}

def entry_20_31 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 31
  lower := (42580339/996610000)
  upper := (42779661/996610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_31.interval_proof
}

def entry_20_32 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 32
  lower := (40383511/964890000)
  upper := (40576489/964890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_32.interval_proof
}

def entry_20_33 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 33
  lower := (37528661/913390000)
  upper := (37711339/913390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_33.interval_proof
}

def entry_20_34 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 34
  lower := (17965501/444990000)
  upper := (18054499/444990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_34.interval_proof
}

def entry_20_35 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 35
  lower := (38742621/973790000)
  upper := (38937379/973790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_35.interval_proof
}

def entry_20_36 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 36
  lower := (4299039/109610000)
  upper := (4320961/109610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_36.interval_proof
}

def entry_20_37 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 37
  lower := (7464737/192630000)
  upper := (7503263/192630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_37.interval_proof
}

def entry_20_38 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 38
  lower := (4625461/120390000)
  upper := (4649539/120390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_38.interval_proof
}

def entry_20_39 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 39
  lower := (36454699/953010000)
  upper := (36645301/953010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_39.interval_proof
}

def entry_20_40 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 40
  lower := (2804717/72830000)
  upper := (2819283/72830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_40.interval_proof
}

def entry_20_41 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 41
  lower := (10003013/269870000)
  upper := (10056987/269870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_41.interval_proof
}

def entry_20_42 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 42
  lower := (3482347/96530000)
  upper := (3501653/96530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_42.interval_proof
}

def entry_20_43 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 43
  lower := (867539/24610000)
  upper := (872461/24610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_43.interval_proof
}

def entry_20_44 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 44
  lower := (26573089/769110000)
  upper := (26726911/769110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_44.interval_proof
}

def entry_20_45 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 45
  lower := (537017/15830000)
  upper := (540183/15830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_45.interval_proof
}

def entry_20_46 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 46
  lower := (19112641/573590000)
  upper := (19227359/573590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_46.interval_proof
}

def entry_20_47 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 47
  lower := (12686317/386830000)
  upper := (12763683/386830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_47.interval_proof
}

def entry_20_48 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 48
  lower := (29717979/920210000)
  upper := (29902021/920210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_48.interval_proof
}

def entry_20_49 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 49
  lower := (1109017/34830000)
  upper := (1115983/34830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_49.interval_proof
}

def entry_20_50 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 50
  lower := (6092683/193170000)
  upper := (6131317/193170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_20_50.interval_proof
}

end RH.Certificates.Generated.NymanGramN50
