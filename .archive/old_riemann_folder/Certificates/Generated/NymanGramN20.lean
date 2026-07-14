import RiemannHypothesis.Certificates.NymanBeurlingCertificate
import RiemannHypothesis.Certificates.Generated.ChiRhoBoundsN20
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20
import Mathlib

/-!
# GENERATED GRAM MATRIX CERTIFICATE
N = 20

Indices convention:
- Lean generated index `i : Fin N` corresponds to mathematical index `h = i.val + 1`.
- Lean generated index `j : Fin N` corresponds to mathematical index `k = j.val + 1`.
- Gram entry represents: ∫₀^∞ {1/(h x)} {1/(k x)} dx

Data Source: CertifiedInterval
-/

set_option maxHeartbeats 10000000
open scoped BigOperators

namespace RH.Certificates.Generated.NymanGramN20

open RH.Certificates

def entry_1_1 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 1
  lower := (6303/5000)
  upper := (12607/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_1.interval_proof
}

def entry_1_2 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 2
  lower := (3861/5000)
  upper := (7723/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_2.interval_proof
}

def entry_1_3 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 3
  lower := (23/40)
  upper := (5751/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_3.interval_proof
}

def entry_1_4 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 4
  lower := (74098041/159590000)
  upper := (74129959/159590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_4.interval_proof
}

def entry_1_5 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 5
  lower := (297474187/758130000)
  upper := (297625813/758130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_5.interval_proof
}

def entry_1_6 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 6
  lower := (138189523/404770000)
  upper := (138270477/404770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_6.interval_proof
}

def entry_1_7 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 7
  lower := (155428731/512690000)
  upper := (155531269/512690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_7.interval_proof
}

def entry_1_8 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 8
  lower := (14952029/54710000)
  upper := (14962971/54710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_8.interval_proof
}

def entry_1_9 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 9
  lower := (214204061/859390000)
  upper := (214375939/859390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_9.interval_proof
}

def entry_1_10 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 10
  lower := (16135967/70330000)
  upper := (16150033/70330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_10.interval_proof
}

def entry_1_11 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 11
  lower := (12924551/60740000)
  upper := (12936699/60740000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_11.interval_proof
}

def entry_1_12 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 12
  lower := (47665997/240030000)
  upper := (47714003/240030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_12.interval_proof
}

def entry_1_13 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 13
  lower := (53581241/287590000)
  upper := (53638759/287590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_13.interval_proof
}

def entry_1_14 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 14
  lower := (150274417/855830000)
  upper := (150445583/855830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_14.interval_proof
}

def entry_1_15 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 15
  lower := (161452817/971830000)
  upper := (161647183/971830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_15.interval_proof
}

def entry_1_16 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 16
  lower := (149864983/950170000)
  upper := (150055017/950170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_16.interval_proof
}

def entry_1_17 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 17
  lower := (149910189/998110000)
  upper := (150109811/998110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_17.interval_proof
}

def entry_1_18 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 18
  lower := (65389403/455970000)
  upper := (65480597/455970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_18.interval_proof
}

def entry_1_19 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 19
  lower := (2263351/16490000)
  upper := (2266649/16490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_19.interval_proof
}

def entry_1_20 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 20
  lower := (44721031/339690000)
  upper := (44788969/339690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_1_20.interval_proof
}

def entry_2_1 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 1
  lower := (3861/5000)
  upper := (7723/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_1.interval_proof
}

def entry_2_2 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 2
  lower := (6303/10000)
  upper := (394/625)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_2.interval_proof
}

def entry_2_3 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 3
  lower := (4411/10000)
  upper := (1103/2500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_3.interval_proof
}

def entry_2_4 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 4
  lower := (368854443/955570000)
  upper := (369045557/955570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_4.interval_proof
}

def entry_2_5 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 5
  lower := (36498461/115390000)
  upper := (36521539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_5.interval_proof
}

def entry_2_6 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 6
  lower := (269206331/936690000)
  upper := (269393669/936690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_6.interval_proof
}

def entry_2_7 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 7
  lower := (157846907/630930000)
  upper := (157973093/630930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_7.interval_proof
}

def entry_2_8 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 8
  lower := (75927287/327130000)
  upper := (75992713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_8.interval_proof
}

def entry_2_9 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 9
  lower := (135824899/651010000)
  upper := (135955101/651010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_9.interval_proof
}

def entry_2_10 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 10
  lower := (64257239/327610000)
  upper := (64322761/327610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_10.interval_proof
}

def entry_2_11 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 11
  lower := (146398607/813930000)
  upper := (146561393/813930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_11.interval_proof
}

def entry_2_12 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 12
  lower := (69074523/404770000)
  upper := (69155477/404770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_12.interval_proof
}

def entry_2_13 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 13
  lower := (104703999/660010000)
  upper := (104836001/660010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_13.interval_proof
}

def entry_2_14 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 14
  lower := (77688731/512690000)
  upper := (77791269/512690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_14.interval_proof
}

def entry_2_15 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 15
  lower := (8406591/59090000)
  upper := (8418409/59090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_15.interval_proof
}

def entry_2_16 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 16
  lower := (7473279/54710000)
  upper := (7484221/54710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_16.interval_proof
}

def entry_2_17 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 17
  lower := (856697/6630000)
  upper := (858023/6630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_17.interval_proof
}

def entry_2_18 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 18
  lower := (40807243/327570000)
  upper := (40872757/327570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_18.interval_proof
}

def entry_2_19 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 19
  lower := (37213607/313930000)
  upper := (37276393/313930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_19.interval_proof
}

def entry_2_20 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 20
  lower := (40714493/355070000)
  upper := (40785507/355070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_2_20.interval_proof
}

def entry_3_1 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 1
  lower := (23/40)
  upper := (5751/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_1.interval_proof
}

def entry_3_2 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 2
  lower := (4411/10000)
  upper := (1103/2500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_2.interval_proof
}

def entry_3_3 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 3
  lower := (2101/5000)
  upper := (4203/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_3.interval_proof
}

def entry_3_4 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 4
  lower := (12635993/40070000)
  upper := (12644007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_4.interval_proof
}

def entry_3_5 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 5
  lower := (80650507/294930000)
  upper := (80709493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_5.interval_proof
}

def entry_3_6 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 6
  lower := (45200433/175670000)
  upper := (45235567/175670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_6.interval_proof
}

def entry_3_7 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 7
  lower := (112519007/509930000)
  upper := (112620993/509930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_7.interval_proof
}

def entry_3_8 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 8
  lower := (4014879/19960000)
  upper := (4018871/19960000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_8.interval_proof
}

def entry_3_9 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 9
  lower := (124245143/648570000)
  upper := (124374857/648570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_9.interval_proof
}

def entry_3_10 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 10
  lower := (64452631/373690000)
  upper := (64527369/373690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_10.interval_proof
}

def entry_3_11 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 11
  lower := (142731359/886410000)
  upper := (142908641/886410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_11.interval_proof
}

def entry_3_12 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 12
  lower := (50607287/327130000)
  upper := (50672713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_12.interval_proof
}

def entry_3_13 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 13
  lower := (50979311/356890000)
  upper := (51050689/356890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_13.interval_proof
}

def entry_3_14 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 14
  lower := (110508283/817170000)
  upper := (110671717/817170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_14.interval_proof
}

def entry_3_15 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 15
  lower := (42827239/327610000)
  upper := (42892761/327610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_15.interval_proof
}

def entry_3_16 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 16
  lower := (19793853/161470000)
  upper := (19826147/161470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_16.interval_proof
}

def entry_3_17 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 17
  lower := (6694909/57160000)
  upper := (6706341/57160000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_17.interval_proof
}

def entry_3_18 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 18
  lower := (9472921/83290000)
  upper := (9489579/83290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_18.interval_proof
}

def entry_3_19 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 19
  lower := (9353321/86790000)
  upper := (9370679/86790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_19.interval_proof
}

def entry_3_20 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 20
  lower := (37633689/363110000)
  upper := (37706311/363110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_3_20.interval_proof
}

def entry_4_1 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 1
  lower := (74098041/159590000)
  upper := (74129959/159590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_1.interval_proof
}

def entry_4_2 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 2
  lower := (368854443/955570000)
  upper := (369045557/955570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_2.interval_proof
}

def entry_4_3 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 3
  lower := (12635993/40070000)
  upper := (12644007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_3.interval_proof
}

def entry_4_4 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 4
  lower := (797903/2532500)
  upper := (1596819/5065000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_4.interval_proof
}

def entry_4_5 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 5
  lower := (25442211/102890000)
  upper := (25462789/102890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_5.interval_proof
}

def entry_4_6 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 6
  lower := (55097507/249930000)
  upper := (55147493/249930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_6.interval_proof
}

def entry_4_7 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 7
  lower := (49395219/247810000)
  upper := (49444781/247810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_7.interval_proof
}

def entry_4_8 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 8
  lower := (14052717/72830000)
  upper := (14067283/72830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_8.interval_proof
}

def entry_4_9 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 9
  lower := (163044103/958970000)
  upper := (163235897/958970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_9.interval_proof
}

def entry_4_10 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 10
  lower := (18243461/115390000)
  upper := (18266539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_10.interval_proof
}

def entry_4_11 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 11
  lower := (4931041/33340000)
  upper := (4937709/33340000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_11.interval_proof
}

def entry_4_12 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 12
  lower := (134556331/936690000)
  upper := (134743669/936690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_12.interval_proof
}

def entry_4_13 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 13
  lower := (4026447/30530000)
  upper := (4032553/30530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_13.interval_proof
}

def entry_4_14 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 14
  lower := (103337357/826430000)
  upper := (103502643/826430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_14.interval_proof
}

def entry_4_15 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 15
  lower := (22107413/185870000)
  upper := (22144587/185870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_15.interval_proof
}

def entry_4_16 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 16
  lower := (37947287/327130000)
  upper := (38012713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_16.interval_proof
}

def entry_4_17 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 17
  lower := (3296469/30310000)
  upper := (3302531/30310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_17.interval_proof
}

def entry_4_18 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 18
  lower := (52819343/506570000)
  upper := (52920657/506570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_18.interval_proof
}

def entry_4_19 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 19
  lower := (13139383/131170000)
  upper := (13165617/131170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_19.interval_proof
}

def entry_4_20 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 20
  lower := (32112239/327610000)
  upper := (32177761/327610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_4_20.interval_proof
}

def entry_5_1 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 1
  lower := (297474187/758130000)
  upper := (297625813/758130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_1.interval_proof
}

def entry_5_2 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 2
  lower := (36498461/115390000)
  upper := (36521539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_2.interval_proof
}

def entry_5_3 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 3
  lower := (80650507/294930000)
  upper := (80709493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_3.interval_proof
}

def entry_5_4 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 4
  lower := (25442211/102890000)
  upper := (25462789/102890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_4.interval_proof
}

def entry_5_5 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 5
  lower := (175820239/697610000)
  upper := (175959761/697610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_5.interval_proof
}

def entry_5_6 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 6
  lower := (34982859/171410000)
  upper := (35017141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_6.interval_proof
}

def entry_5_7 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 7
  lower := (167378283/917170000)
  upper := (167561717/917170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_7.interval_proof
}

def entry_5_8 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 8
  lower := (2514001/14990000)
  upper := (2516999/14990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_8.interval_proof
}

def entry_5_9 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 9
  lower := (17229039/109610000)
  upper := (17250961/109610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_9.interval_proof
}

def entry_5_10 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 10
  lower := (50922007/329930000)
  upper := (50987993/329930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_10.interval_proof
}

def entry_5_11 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 11
  lower := (47031043/339570000)
  upper := (47098957/339570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_11.interval_proof
}

def entry_5_12 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 12
  lower := (40823471/315290000)
  upper := (40886529/315290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_12.interval_proof
}

def entry_5_13 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 13
  lower := (114946181/938190000)
  upper := (115133819/938190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_13.interval_proof
}

def entry_5_14 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 14
  lower := (3848713/32870000)
  upper := (3855287/32870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_14.interval_proof
}

def entry_5_15 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 15
  lower := (107626331/936690000)
  upper := (107813669/936690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_15.interval_proof
}

def entry_5_16 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 16
  lower := (19049673/178270000)
  upper := (19085327/178270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_16.interval_proof
}

def entry_5_17 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 17
  lower := (43667113/428870000)
  upper := (43752887/428870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_17.interval_proof
}

def entry_5_18 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 18
  lower := (24899519/254810000)
  upper := (24950481/254810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_18.interval_proof
}

def entry_5_19 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 19
  lower := (37759987/400130000)
  upper := (37840013/400130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_19.interval_proof
}

def entry_5_20 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 20
  lower := (21841459/235410000)
  upper := (21888541/235410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_5_20.interval_proof
}

def entry_6_1 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 1
  lower := (138189523/404770000)
  upper := (138270477/404770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_1.interval_proof
}

def entry_6_2 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 2
  lower := (269206331/936690000)
  upper := (269393669/936690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_2.interval_proof
}

def entry_6_3 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 3
  lower := (45200433/175670000)
  upper := (45235567/175670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_3.interval_proof
}

def entry_6_4 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 4
  lower := (55097507/249930000)
  upper := (55147493/249930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_4.interval_proof
}

def entry_6_5 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 5
  lower := (34982859/171410000)
  upper := (35017141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_5.interval_proof
}

def entry_6_6 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 6
  lower := (198705383/946170000)
  upper := (198894617/946170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_6.interval_proof
}

def entry_6_7 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 7
  lower := (81713059/469410000)
  upper := (81806941/469410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_7.interval_proof
}

def entry_6_8 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 8
  lower := (6315993/40070000)
  upper := (6324007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_8.interval_proof
}

def entry_6_9 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 9
  lower := (71076627/483730000)
  upper := (71173373/483730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_9.interval_proof
}

def entry_6_10 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 10
  lower := (40310507/294930000)
  upper := (40369493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_10.interval_proof
}

def entry_6_11 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 11
  lower := (38255551/294490000)
  upper := (38314449/294490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_11.interval_proof
}

def entry_6_12 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 12
  lower := (56760863/441370000)
  upper := (56849137/441370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_12.interval_proof
}

def entry_6_13 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 13
  lower := (12443359/106410000)
  upper := (12464641/106410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_13.interval_proof
}

def entry_6_14 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 14
  lower := (2713939/24610000)
  upper := (2718861/24610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_14.interval_proof
}

def entry_6_15 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 15
  lower := (12158461/115390000)
  upper := (12181539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_15.interval_proof
}

def entry_6_16 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 16
  lower := (4012883/39920000)
  upper := (4020867/39920000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_16.interval_proof
}

def entry_6_17 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 17
  lower := (79068453/815470000)
  upper := (79231547/815470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_17.interval_proof
}

def entry_6_18 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 18
  lower := (48279569/504310000)
  upper := (48380431/504310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_18.interval_proof
}

def entry_6_19 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 19
  lower := (16491647/183530000)
  upper := (16528353/183530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_19.interval_proof
}

def entry_6_20 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 20
  lower := (32207631/373690000)
  upper := (32282369/373690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_6_20.interval_proof
}

def entry_7_1 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 1
  lower := (155428731/512690000)
  upper := (155531269/512690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_1.interval_proof
}

def entry_7_2 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 2
  lower := (157846907/630930000)
  upper := (157973093/630930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_2.interval_proof
}

def entry_7_3 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 3
  lower := (112519007/509930000)
  upper := (112620993/509930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_3.interval_proof
}

def entry_7_4 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 4
  lower := (49395219/247810000)
  upper := (49444781/247810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_4.interval_proof
}

def entry_7_5 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 5
  lower := (167378283/917170000)
  upper := (167561717/917170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_5.interval_proof
}

def entry_7_6 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 6
  lower := (81713059/469410000)
  upper := (81806941/469410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_6.interval_proof
}

def entry_7_7 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 7
  lower := (70865629/393710000)
  upper := (70944371/393710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_7.interval_proof
}

def entry_7_8 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 8
  lower := (27455929/180710000)
  upper := (27492071/180710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_8.interval_proof
}

def entry_7_9 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 9
  lower := (34032863/246370000)
  upper := (34082137/246370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_9.interval_proof
}

def entry_7_10 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 10
  lower := (86672617/673830000)
  upper := (86807383/673830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_10.interval_proof
}

def entry_7_11 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 11
  lower := (96270517/794830000)
  upper := (96429483/794830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_11.interval_proof
}

def entry_7_12 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 12
  lower := (94797571/824290000)
  upper := (94962429/824290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_12.interval_proof
}

def entry_7_13 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 13
  lower := (13636439/123110000)
  upper := (13661061/123110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_13.interval_proof
}

def entry_7_14 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 14
  lower := (52417441/475590000)
  upper := (52512559/475590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_14.interval_proof
}

def entry_7_15 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 15
  lower := (28931421/285790000)
  upper := (28988579/285790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_15.interval_proof
}

def entry_7_16 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 16
  lower := (1045709/10910000)
  upper := (1047891/10910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_16.interval_proof
}

def entry_7_17 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 17
  lower := (41439803/451970000)
  upper := (41530197/451970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_17.interval_proof
}

def entry_7_18 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 18
  lower := (42916311/486890000)
  upper := (43013689/486890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_18.interval_proof
}

def entry_7_19 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 19
  lower := (2231877/26230000)
  upper := (2237123/26230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_19.interval_proof
}

def entry_7_20 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 20
  lower := (78045703/942970000)
  upper := (78234297/942970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_7_20.interval_proof
}

def entry_8_1 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 1
  lower := (14952029/54710000)
  upper := (14962971/54710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_1.interval_proof
}

def entry_8_2 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 2
  lower := (75927287/327130000)
  upper := (75992713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_2.interval_proof
}

def entry_8_3 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 3
  lower := (4014879/19960000)
  upper := (4018871/19960000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_3.interval_proof
}

def entry_8_4 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 4
  lower := (14052717/72830000)
  upper := (14067283/72830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_4.interval_proof
}

def entry_8_5 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 5
  lower := (2514001/14990000)
  upper := (2516999/14990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_5.interval_proof
}

def entry_8_6 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 6
  lower := (6315993/40070000)
  upper := (6324007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_6.interval_proof
}

def entry_8_7 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 7
  lower := (27455929/180710000)
  upper := (27492071/180710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_7.interval_proof
}

def entry_8_8 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 8
  lower := (77955499/495010000)
  upper := (78054501/495010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_8.interval_proof
}

def entry_8_9 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 9
  lower := (11758283/87170000)
  upper := (11775717/87170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_9.interval_proof
}

def entry_8_10 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 10
  lower := (12715961/102890000)
  upper := (12736539/102890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_10.interval_proof
}

def entry_8_11 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 11
  lower := (27808387/241130000)
  upper := (27856613/241130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_11.interval_proof
}

def entry_8_12 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 12
  lower := (14656697/133030000)
  upper := (14683303/133030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_12.interval_proof
}

def entry_8_13 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 13
  lower := (9109969/87810000)
  upper := (9127531/87810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_13.interval_proof
}

def entry_8_14 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 14
  lower := (24685219/247810000)
  upper := (24734781/247810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_14.interval_proof
}

def entry_8_15 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 15
  lower := (52665471/545290000)
  upper := (52774529/545290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_15.interval_proof
}

def entry_8_16 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 16
  lower := (7022717/72830000)
  upper := (7037283/72830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_16.interval_proof
}

def entry_8_17 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 17
  lower := (10578151/118490000)
  upper := (10601849/118490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_17.interval_proof
}

def entry_8_18 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 18
  lower := (81474103/958970000)
  upper := (81665897/958970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_18.interval_proof
}

def entry_8_19 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 19
  lower := (36585097/449030000)
  upper := (36674903/449030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_19.interval_proof
}

def entry_8_20 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 20
  lower := (9115961/115390000)
  upper := (9139039/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_8_20.interval_proof
}

def entry_9_1 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 1
  lower := (214204061/859390000)
  upper := (214375939/859390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_1.interval_proof
}

def entry_9_2 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 2
  lower := (135824899/651010000)
  upper := (135955101/651010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_2.interval_proof
}

def entry_9_3 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 3
  lower := (124245143/648570000)
  upper := (124374857/648570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_3.interval_proof
}

def entry_9_4 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 4
  lower := (163044103/958970000)
  upper := (163235897/958970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_4.interval_proof
}

def entry_9_5 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 5
  lower := (17229039/109610000)
  upper := (17250961/109610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_5.interval_proof
}

def entry_9_6 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 6
  lower := (71076627/483730000)
  upper := (71173373/483730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_6.interval_proof
}

def entry_9_7 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 7
  lower := (34032863/246370000)
  upper := (34082137/246370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_7.interval_proof
}

def entry_9_8 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 8
  lower := (11758283/87170000)
  upper := (11775717/87170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_8.interval_proof
}

def entry_9_9 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 9
  lower := (12571019/89810000)
  upper := (12588981/89810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_9.interval_proof
}

def entry_9_10 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 10
  lower := (116434047/959530000)
  upper := (116625953/959530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_10.interval_proof
}

def entry_9_11 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 11
  lower := (5335219/47810000)
  upper := (5344781/47810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_11.interval_proof
}

def entry_9_12 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 12
  lower := (12627979/120210000)
  upper := (12652021/120210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_12.interval_proof
}

def entry_9_13 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 13
  lower := (16962929/170710000)
  upper := (16997071/170710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_13.interval_proof
}

def entry_9_14 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 14
  lower := (23572643/248570000)
  upper := (23622357/248570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_14.interval_proof
}

def entry_9_15 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 15
  lower := (80591521/884790000)
  upper := (80768479/884790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_15.interval_proof
}

def entry_9_16 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 16
  lower := (12042277/137230000)
  upper := (12069723/137230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_16.interval_proof
}

def entry_9_17 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 17
  lower := (25929723/302770000)
  upper := (25990277/302770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_17.interval_proof
}

def entry_9_18 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 18
  lower := (37825863/441370000)
  upper := (37914137/441370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_18.interval_proof
}

def entry_9_19 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 19
  lower := (25068609/313910000)
  upper := (25131391/313910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_19.interval_proof
}

def entry_9_20 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 20
  lower := (6915927/90730000)
  upper := (6934073/90730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_9_20.interval_proof
}

def entry_10_1 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 1
  lower := (16135967/70330000)
  upper := (16150033/70330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_1.interval_proof
}

def entry_10_2 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 2
  lower := (64257239/327610000)
  upper := (64322761/327610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_2.interval_proof
}

def entry_10_3 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 3
  lower := (64452631/373690000)
  upper := (64527369/373690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_3.interval_proof
}

def entry_10_4 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 4
  lower := (18243461/115390000)
  upper := (18266539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_4.interval_proof
}

def entry_10_5 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 5
  lower := (50922007/329930000)
  upper := (50987993/329930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_5.interval_proof
}

def entry_10_6 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 6
  lower := (40310507/294930000)
  upper := (40369493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_6.interval_proof
}

def entry_10_7 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 7
  lower := (86672617/673830000)
  upper := (86807383/673830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_7.interval_proof
}

def entry_10_8 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 8
  lower := (12715961/102890000)
  upper := (12736539/102890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_8.interval_proof
}

def entry_10_9 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 9
  lower := (116434047/959530000)
  upper := (116625953/959530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_9.interval_proof
}

def entry_10_10 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 10
  lower := (39728461/315390000)
  upper := (39791539/315390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_10.interval_proof
}

def entry_10_11 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 11
  lower := (79467961/720390000)
  upper := (79612039/720390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_11.interval_proof
}

def entry_10_12 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 12
  lower := (17482859/171410000)
  upper := (17517141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_12.interval_proof
}

def entry_10_13 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 13
  lower := (22993523/239770000)
  upper := (23041477/239770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_13.interval_proof
}

def entry_10_14 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 14
  lower := (18160087/199130000)
  upper := (18199913/199130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_14.interval_proof
}

def entry_10_15 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 15
  lower := (2109169/23935000)
  upper := (528489/5983750)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_15.interval_proof
}

def entry_10_16 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 16
  lower := (1256251/14990000)
  upper := (1259249/14990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_16.interval_proof
}

def entry_10_17 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 17
  lower := (35975501/444990000)
  upper := (36064499/444990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_17.interval_proof
}

def entry_10_18 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 18
  lower := (8609039/109610000)
  upper := (8630961/109610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_18.interval_proof
}

def entry_10_19 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 19
  lower := (12617601/163990000)
  upper := (12650399/163990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_19.interval_proof
}

def entry_10_20 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 20
  lower := (73694443/955570000)
  upper := (73885557/955570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_10_20.interval_proof
}

def entry_11_1 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 1
  lower := (12924551/60740000)
  upper := (12936699/60740000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_1.interval_proof
}

def entry_11_2 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 2
  lower := (146398607/813930000)
  upper := (146561393/813930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_2.interval_proof
}

def entry_11_3 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 3
  lower := (142731359/886410000)
  upper := (142908641/886410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_3.interval_proof
}

def entry_11_4 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 4
  lower := (4931041/33340000)
  upper := (4937709/33340000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_4.interval_proof
}

def entry_11_5 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 5
  lower := (47031043/339570000)
  upper := (47098957/339570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_5.interval_proof
}

def entry_11_6 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 6
  lower := (38255551/294490000)
  upper := (38314449/294490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_6.interval_proof
}

def entry_11_7 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 7
  lower := (96270517/794830000)
  upper := (96429483/794830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_7.interval_proof
}

def entry_11_8 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 8
  lower := (27808387/241130000)
  upper := (27856613/241130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_8.interval_proof
}

def entry_11_9 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 9
  lower := (5335219/47810000)
  upper := (5344781/47810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_9.interval_proof
}

def entry_11_10 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 10
  lower := (79467961/720390000)
  upper := (79612039/720390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_10.interval_proof
}

def entry_11_11 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 11
  lower := (79880239/697610000)
  upper := (80019761/697610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_11.interval_proof
}

def entry_11_12 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 12
  lower := (36858559/364410000)
  upper := (36931441/364410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_12.interval_proof
}

def entry_11_13 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 13
  lower := (27340857/291430000)
  upper := (27399143/291430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_13.interval_proof
}

def entry_11_14 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 14
  lower := (52111121/588790000)
  upper := (52228879/588790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_14.interval_proof
}

def entry_11_15 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 15
  lower := (130283/1545000)
  upper := (16324/193125)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_15.interval_proof
}

def entry_11_16 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 16
  lower := (21553381/266190000)
  upper := (21606619/266190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_16.interval_proof
}

def entry_11_17 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 17
  lower := (3587397/46030000)
  upper := (3596603/46030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_17.interval_proof
}

def entry_11_18 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 18
  lower := (32107257/427430000)
  upper := (32192743/427430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_18.interval_proof
}

def entry_11_19 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 19
  lower := (1617779/22210000)
  upper := (1622221/22210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_19.interval_proof
}

def entry_11_20 : GramEntryIntervalCertificate :=
{
  h := 11
  k := 20
  lower := (38505797/542030000)
  upper := (38614203/542030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_11_20.interval_proof
}

def entry_12_1 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 1
  lower := (47665997/240030000)
  upper := (47714003/240030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_1.interval_proof
}

def entry_12_2 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 2
  lower := (69074523/404770000)
  upper := (69155477/404770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_2.interval_proof
}

def entry_12_3 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 3
  lower := (50607287/327130000)
  upper := (50672713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_3.interval_proof
}

def entry_12_4 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 4
  lower := (134556331/936690000)
  upper := (134743669/936690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_4.interval_proof
}

def entry_12_5 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 5
  lower := (40823471/315290000)
  upper := (40886529/315290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_5.interval_proof
}

def entry_12_6 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 6
  lower := (56760863/441370000)
  upper := (56849137/441370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_6.interval_proof
}

def entry_12_7 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 7
  lower := (94797571/824290000)
  upper := (94962429/824290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_7.interval_proof
}

def entry_12_8 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 8
  lower := (14656697/133030000)
  upper := (14683303/133030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_8.interval_proof
}

def entry_12_9 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 9
  lower := (12627979/120210000)
  upper := (12652021/120210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_9.interval_proof
}

def entry_12_10 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 10
  lower := (17482859/171410000)
  upper := (17517141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_10.interval_proof
}

def entry_12_11 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 11
  lower := (36858559/364410000)
  upper := (36931441/364410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_11.interval_proof
}

def entry_12_12 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 12
  lower := (99305383/946170000)
  upper := (99494617/946170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_12.interval_proof
}

def entry_12_13 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 13
  lower := (1308599/14010000)
  upper := (1311401/14010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_13.interval_proof
}

def entry_12_14 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 14
  lower := (40833059/469410000)
  upper := (40926941/469410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_14.interval_proof
}

def entry_12_15 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 15
  lower := (62534071/759290000)
  upper := (62685929/759290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_15.interval_proof
}

def entry_12_16 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 16
  lower := (3155993/40070000)
  upper := (3164007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_16.interval_proof
}

def entry_12_17 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 17
  lower := (12688163/168370000)
  upper := (12721837/168370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_17.interval_proof
}

def entry_12_18 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 18
  lower := (9766697/133030000)
  upper := (9793303/133030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_18.interval_proof
}

def entry_12_19 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 19
  lower := (2970771/42290000)
  upper := (2979229/42290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_19.interval_proof
}

def entry_12_20 : GramEntryIntervalCertificate :=
{
  h := 12
  k := 20
  lower := (20140507/294930000)
  upper := (20199493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_12_20.interval_proof
}

def entry_13_1 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 1
  lower := (53581241/287590000)
  upper := (53638759/287590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_1.interval_proof
}

def entry_13_2 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 2
  lower := (104703999/660010000)
  upper := (104836001/660010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_2.interval_proof
}

def entry_13_3 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 3
  lower := (50979311/356890000)
  upper := (51050689/356890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_3.interval_proof
}

def entry_13_4 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 4
  lower := (4026447/30530000)
  upper := (4032553/30530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_4.interval_proof
}

def entry_13_5 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 5
  lower := (114946181/938190000)
  upper := (115133819/938190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_5.interval_proof
}

def entry_13_6 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 6
  lower := (12443359/106410000)
  upper := (12464641/106410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_6.interval_proof
}

def entry_13_7 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 7
  lower := (13636439/123110000)
  upper := (13661061/123110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_7.interval_proof
}

def entry_13_8 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 8
  lower := (9109969/87810000)
  upper := (9127531/87810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_8.interval_proof
}

def entry_13_9 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 9
  lower := (16962929/170710000)
  upper := (16997071/170710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_9.interval_proof
}

def entry_13_10 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 10
  lower := (22993523/239770000)
  upper := (23041477/239770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_10.interval_proof
}

def entry_13_11 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 11
  lower := (27340857/291430000)
  upper := (27399143/291430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_11.interval_proof
}

def entry_13_12 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 12
  lower := (1308599/14010000)
  upper := (1311401/14010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_12.interval_proof
}

def entry_13_13 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 13
  lower := (67580239/697610000)
  upper := (67719761/697610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_13.interval_proof
}

def entry_13_14 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 14
  lower := (80816869/931310000)
  upper := (81003131/931310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_14.interval_proof
}

def entry_13_15 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 15
  lower := (26002911/320890000)
  upper := (26067089/320890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_15.interval_proof
}

def entry_13_16 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 16
  lower := (4146601/53990000)
  upper := (4157399/53990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_16.interval_proof
}

def entry_13_17 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 17
  lower := (22654157/308430000)
  upper := (22715843/308430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_17.interval_proof
}

def entry_13_18 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 18
  lower := (27021719/382810000)
  upper := (27098281/382810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_18.interval_proof
}

def entry_13_19 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 19
  lower := (18522891/271090000)
  upper := (18577109/271090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_19.interval_proof
}

def entry_13_20 : GramEntryIntervalCertificate :=
{
  h := 13
  k := 20
  lower := (2653489/40110000)
  upper := (2661511/40110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_13_20.interval_proof
}

def entry_14_1 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 1
  lower := (150274417/855830000)
  upper := (150445583/855830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_1.interval_proof
}

def entry_14_2 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 2
  lower := (77688731/512690000)
  upper := (77791269/512690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_2.interval_proof
}

def entry_14_3 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 3
  lower := (110508283/817170000)
  upper := (110671717/817170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_3.interval_proof
}

def entry_14_4 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 4
  lower := (103337357/826430000)
  upper := (103502643/826430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_4.interval_proof
}

def entry_14_5 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 5
  lower := (3848713/32870000)
  upper := (3855287/32870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_5.interval_proof
}

def entry_14_6 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 6
  lower := (2713939/24610000)
  upper := (2718861/24610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_6.interval_proof
}

def entry_14_7 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 7
  lower := (52417441/475590000)
  upper := (52512559/475590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_7.interval_proof
}

def entry_14_8 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 8
  lower := (24685219/247810000)
  upper := (24734781/247810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_8.interval_proof
}

def entry_14_9 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 9
  lower := (23572643/248570000)
  upper := (23622357/248570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_9.interval_proof
}

def entry_14_10 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 10
  lower := (18160087/199130000)
  upper := (18199913/199130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_10.interval_proof
}

def entry_14_11 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 11
  lower := (52111121/588790000)
  upper := (52228879/588790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_11.interval_proof
}

def entry_14_12 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 12
  lower := (40833059/469410000)
  upper := (40926941/469410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_12.interval_proof
}

def entry_14_13 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 13
  lower := (80816869/931310000)
  upper := (81003131/931310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_13.interval_proof
}

def entry_14_14 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 14
  lower := (28368461/315390000)
  upper := (28431539/315390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_14.interval_proof
}

def entry_14_15 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 15
  lower := (49139363/606370000)
  upper := (49260637/606370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_15.interval_proof
}

def entry_14_16 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 16
  lower := (55417003/729970000)
  upper := (55562997/729970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_16.interval_proof
}

def entry_14_17 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 17
  lower := (552753/7670000)
  upper := (554287/7670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_17.interval_proof
}

def entry_14_18 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 18
  lower := (11691061/169390000)
  upper := (11724939/169390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_18.interval_proof
}

def entry_14_19 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 19
  lower := (19860119/298810000)
  upper := (19919881/298810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_19.interval_proof
}

def entry_14_20 : GramEntryIntervalCertificate :=
{
  h := 14
  k := 20
  lower := (43302617/673830000)
  upper := (43437383/673830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_14_20.interval_proof
}

def entry_15_1 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 1
  lower := (161452817/971830000)
  upper := (161647183/971830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_1.interval_proof
}

def entry_15_2 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 2
  lower := (8406591/59090000)
  upper := (8418409/59090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_2.interval_proof
}

def entry_15_3 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 3
  lower := (42827239/327610000)
  upper := (42892761/327610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_3.interval_proof
}

def entry_15_4 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 4
  lower := (22107413/185870000)
  upper := (22144587/185870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_4.interval_proof
}

def entry_15_5 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 5
  lower := (107626331/936690000)
  upper := (107813669/936690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_5.interval_proof
}

def entry_15_6 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 6
  lower := (12158461/115390000)
  upper := (12181539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_6.interval_proof
}

def entry_15_7 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 7
  lower := (28931421/285790000)
  upper := (28988579/285790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_7.interval_proof
}

def entry_15_8 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 8
  lower := (52665471/545290000)
  upper := (52774529/545290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_8.interval_proof
}

def entry_15_9 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 9
  lower := (80591521/884790000)
  upper := (80768479/884790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_9.interval_proof
}

def entry_15_10 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 10
  lower := (2109169/23935000)
  upper := (528489/5983750)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_10.interval_proof
}

def entry_15_11 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 11
  lower := (130283/1545000)
  upper := (16324/193125)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_11.interval_proof
}

def entry_15_12 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 12
  lower := (62534071/759290000)
  upper := (62685929/759290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_12.interval_proof
}

def entry_15_13 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 13
  lower := (26002911/320890000)
  upper := (26067089/320890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_13.interval_proof
}

def entry_15_14 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 14
  lower := (49139363/606370000)
  upper := (49260637/606370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_14.interval_proof
}

def entry_15_15 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 15
  lower := (58560239/697610000)
  upper := (58699761/697610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_15.interval_proof
}

def entry_15_16 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 16
  lower := (43632603/573970000)
  upper := (43747397/573970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_16.interval_proof
}

def entry_15_17 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 17
  lower := (29174127/408730000)
  upper := (29255873/408730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_17.interval_proof
}

def entry_15_18 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 18
  lower := (34948577/514230000)
  upper := (35051423/514230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_18.interval_proof
}

def entry_15_19 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 19
  lower := (3683343/56570000)
  upper := (3694657/56570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_19.interval_proof
}

def entry_15_20 : GramEntryIntervalCertificate :=
{
  h := 15
  k := 20
  lower := (2523993/40070000)
  upper := (2532007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_15_20.interval_proof
}

def entry_16_1 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 1
  lower := (149864983/950170000)
  upper := (150055017/950170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_1.interval_proof
}

def entry_16_2 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 2
  lower := (7473279/54710000)
  upper := (7484221/54710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_2.interval_proof
}

def entry_16_3 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 3
  lower := (19793853/161470000)
  upper := (19826147/161470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_3.interval_proof
}

def entry_16_4 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 4
  lower := (37947287/327130000)
  upper := (38012713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_4.interval_proof
}

def entry_16_5 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 5
  lower := (19049673/178270000)
  upper := (19085327/178270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_5.interval_proof
}

def entry_16_6 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 6
  lower := (4012883/39920000)
  upper := (4020867/39920000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_6.interval_proof
}

def entry_16_7 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 7
  lower := (1045709/10910000)
  upper := (1047891/10910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_7.interval_proof
}

def entry_16_8 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 8
  lower := (7022717/72830000)
  upper := (7037283/72830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_8.interval_proof
}

def entry_16_9 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 9
  lower := (12042277/137230000)
  upper := (12069723/137230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_9.interval_proof
}

def entry_16_10 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 10
  lower := (1256251/14990000)
  upper := (1259249/14990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_10.interval_proof
}

def entry_16_11 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 11
  lower := (21553381/266190000)
  upper := (21606619/266190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_11.interval_proof
}

def entry_16_12 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 12
  lower := (3155993/40070000)
  upper := (3164007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_12.interval_proof
}

def entry_16_13 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 13
  lower := (4146601/53990000)
  upper := (4157399/53990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_13.interval_proof
}

def entry_16_14 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 14
  lower := (55417003/729970000)
  upper := (55562997/729970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_14.interval_proof
}

def entry_16_15 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 15
  lower := (43632603/573970000)
  upper := (43747397/573970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_15.interval_proof
}

def entry_16_16 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 16
  lower := (24818461/315390000)
  upper := (24881539/315390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_16.interval_proof
}

def entry_16_17 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 17
  lower := (36109561/504390000)
  upper := (36210439/504390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_17.interval_proof
}

def entry_16_18 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 18
  lower := (36795403/545970000)
  upper := (36904597/545970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_18.interval_proof
}

def entry_16_19 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 19
  lower := (33687533/524670000)
  upper := (33792467/524670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_19.interval_proof
}

def entry_16_20 : GramEntryIntervalCertificate :=
{
  h := 16
  k := 20
  lower := (21470227/347730000)
  upper := (21539773/347730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_16_20.interval_proof
}

def entry_17_1 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 1
  lower := (149910189/998110000)
  upper := (150109811/998110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_1.interval_proof
}

def entry_17_2 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 2
  lower := (856697/6630000)
  upper := (858023/6630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_2.interval_proof
}

def entry_17_3 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 3
  lower := (6694909/57160000)
  upper := (6706341/57160000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_3.interval_proof
}

def entry_17_4 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 4
  lower := (3296469/30310000)
  upper := (3302531/30310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_4.interval_proof
}

def entry_17_5 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 5
  lower := (43667113/428870000)
  upper := (43752887/428870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_5.interval_proof
}

def entry_17_6 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 6
  lower := (79068453/815470000)
  upper := (79231547/815470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_6.interval_proof
}

def entry_17_7 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 7
  lower := (41439803/451970000)
  upper := (41530197/451970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_7.interval_proof
}

def entry_17_8 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 8
  lower := (10578151/118490000)
  upper := (10601849/118490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_8.interval_proof
}

def entry_17_9 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 9
  lower := (25929723/302770000)
  upper := (25990277/302770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_9.interval_proof
}

def entry_17_10 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 10
  lower := (35975501/444990000)
  upper := (36064499/444990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_10.interval_proof
}

def entry_17_11 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 11
  lower := (3587397/46030000)
  upper := (3596603/46030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_11.interval_proof
}

def entry_17_12 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 12
  lower := (12688163/168370000)
  upper := (12721837/168370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_12.interval_proof
}

def entry_17_13 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 13
  lower := (22654157/308430000)
  upper := (22715843/308430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_13.interval_proof
}

def entry_17_14 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 14
  lower := (552753/7670000)
  upper := (554287/7670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_14.interval_proof
}

def entry_17_15 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 15
  lower := (29174127/408730000)
  upper := (29255873/408730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_15.interval_proof
}

def entry_17_16 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 16
  lower := (36109561/504390000)
  upper := (36210439/504390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_16.interval_proof
}

def entry_17_17 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 17
  lower := (6651019/89810000)
  upper := (6668981/89810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_17.interval_proof
}

def entry_17_18 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 18
  lower := (40150653/593470000)
  upper := (40269347/593470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_18.interval_proof
}

def entry_17_19 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 19
  lower := (9257493/145070000)
  upper := (9286507/145070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_19.interval_proof
}

def entry_17_20 : GramEntryIntervalCertificate :=
{
  h := 17
  k := 20
  lower := (43069279/707210000)
  upper := (43210721/707210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_17_20.interval_proof
}

def entry_18_1 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 1
  lower := (65389403/455970000)
  upper := (65480597/455970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_1.interval_proof
}

def entry_18_2 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 2
  lower := (40807243/327570000)
  upper := (40872757/327570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_2.interval_proof
}

def entry_18_3 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 3
  lower := (9472921/83290000)
  upper := (9489579/83290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_3.interval_proof
}

def entry_18_4 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 4
  lower := (52819343/506570000)
  upper := (52920657/506570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_4.interval_proof
}

def entry_18_5 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 5
  lower := (24899519/254810000)
  upper := (24950481/254810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_5.interval_proof
}

def entry_18_6 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 6
  lower := (48279569/504310000)
  upper := (48380431/504310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_6.interval_proof
}

def entry_18_7 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 7
  lower := (42916311/486890000)
  upper := (43013689/486890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_7.interval_proof
}

def entry_18_8 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 8
  lower := (81474103/958970000)
  upper := (81665897/958970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_8.interval_proof
}

def entry_18_9 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 9
  lower := (37825863/441370000)
  upper := (37914137/441370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_9.interval_proof
}

def entry_18_10 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 10
  lower := (8609039/109610000)
  upper := (8630961/109610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_10.interval_proof
}

def entry_18_11 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 11
  lower := (32107257/427430000)
  upper := (32192743/427430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_11.interval_proof
}

def entry_18_12 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 12
  lower := (9766697/133030000)
  upper := (9793303/133030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_12.interval_proof
}

def entry_18_13 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 13
  lower := (27021719/382810000)
  upper := (27098281/382810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_13.interval_proof
}

def entry_18_14 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 14
  lower := (11691061/169390000)
  upper := (11724939/169390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_14.interval_proof
}

def entry_18_15 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 15
  lower := (34948577/514230000)
  upper := (35051423/514230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_15.interval_proof
}

def entry_18_16 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 16
  lower := (36795403/545970000)
  upper := (36904597/545970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_16.interval_proof
}

def entry_18_17 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 17
  lower := (40150653/593470000)
  upper := (40269347/593470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_17.interval_proof
}

def entry_18_18 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 18
  lower := (6281019/89810000)
  upper := (6298981/89810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_18.interval_proof
}

def entry_18_19 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 19
  lower := (30397601/473990000)
  upper := (30492399/473990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_19.interval_proof
}

def entry_18_20 : GramEntryIntervalCertificate :=
{
  h := 18
  k := 20
  lower := (44356831/731690000)
  upper := (44503169/731690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_18_20.interval_proof
}

def entry_19_1 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 1
  lower := (2263351/16490000)
  upper := (2266649/16490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_1.interval_proof
}

def entry_19_2 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 2
  lower := (37213607/313930000)
  upper := (37276393/313930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_2.interval_proof
}

def entry_19_3 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 3
  lower := (9353321/86790000)
  upper := (9370679/86790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_3.interval_proof
}

def entry_19_4 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 4
  lower := (13139383/131170000)
  upper := (13165617/131170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_4.interval_proof
}

def entry_19_5 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 5
  lower := (37759987/400130000)
  upper := (37840013/400130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_5.interval_proof
}

def entry_19_6 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 6
  lower := (16491647/183530000)
  upper := (16528353/183530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_6.interval_proof
}

def entry_19_7 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 7
  lower := (2231877/26230000)
  upper := (2237123/26230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_7.interval_proof
}

def entry_19_8 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 8
  lower := (36585097/449030000)
  upper := (36674903/449030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_8.interval_proof
}

def entry_19_9 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 9
  lower := (25068609/313910000)
  upper := (25131391/313910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_9.interval_proof
}

def entry_19_10 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 10
  lower := (12617601/163990000)
  upper := (12650399/163990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_10.interval_proof
}

def entry_19_11 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 11
  lower := (1617779/22210000)
  upper := (1622221/22210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_11.interval_proof
}

def entry_19_12 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 12
  lower := (2970771/42290000)
  upper := (2979229/42290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_12.interval_proof
}

def entry_19_13 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 13
  lower := (18522891/271090000)
  upper := (18577109/271090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_13.interval_proof
}

def entry_19_14 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 14
  lower := (19860119/298810000)
  upper := (19919881/298810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_14.interval_proof
}

def entry_19_15 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 15
  lower := (3683343/56570000)
  upper := (3694657/56570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_15.interval_proof
}

def entry_19_16 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 16
  lower := (33687533/524670000)
  upper := (33792467/524670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_16.interval_proof
}

def entry_19_17 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 17
  lower := (9257493/145070000)
  upper := (9286507/145070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_17.interval_proof
}

def entry_19_18 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 18
  lower := (30397601/473990000)
  upper := (30492399/473990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_18.interval_proof
}

def entry_19_19 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 19
  lower := (14183591/214090000)
  upper := (14226409/214090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_19.interval_proof
}

def entry_19_20 : GramEntryIntervalCertificate :=
{
  h := 19
  k := 20
  lower := (54370809/891910000)
  upper := (54549191/891910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_19_20.interval_proof
}

def entry_20_1 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 1
  lower := (44721031/339690000)
  upper := (44788969/339690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_1.interval_proof
}

def entry_20_2 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 2
  lower := (40714493/355070000)
  upper := (40785507/355070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_2.interval_proof
}

def entry_20_3 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 3
  lower := (37633689/363110000)
  upper := (37706311/363110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_3.interval_proof
}

def entry_20_4 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 4
  lower := (32112239/327610000)
  upper := (32177761/327610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_4.interval_proof
}

def entry_20_5 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 5
  lower := (21841459/235410000)
  upper := (21888541/235410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_5.interval_proof
}

def entry_20_6 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 6
  lower := (32207631/373690000)
  upper := (32282369/373690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_6.interval_proof
}

def entry_20_7 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 7
  lower := (78045703/942970000)
  upper := (78234297/942970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_7.interval_proof
}

def entry_20_8 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 8
  lower := (9115961/115390000)
  upper := (9139039/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_8.interval_proof
}

def entry_20_9 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 9
  lower := (6915927/90730000)
  upper := (6934073/90730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_9.interval_proof
}

def entry_20_10 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 10
  lower := (73694443/955570000)
  upper := (73885557/955570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_10.interval_proof
}

def entry_20_11 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 11
  lower := (38505797/542030000)
  upper := (38614203/542030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_11.interval_proof
}

def entry_20_12 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 12
  lower := (20140507/294930000)
  upper := (20199493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_12.interval_proof
}

def entry_20_13 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 13
  lower := (2653489/40110000)
  upper := (2661511/40110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_13.interval_proof
}

def entry_20_14 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 14
  lower := (43302617/673830000)
  upper := (43437383/673830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_14.interval_proof
}

def entry_20_15 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 15
  lower := (2523993/40070000)
  upper := (2532007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_15.interval_proof
}

def entry_20_16 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 16
  lower := (21470227/347730000)
  upper := (21539773/347730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_16.interval_proof
}

def entry_20_17 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 17
  lower := (43069279/707210000)
  upper := (43210721/707210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_17.interval_proof
}

def entry_20_18 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 18
  lower := (44356831/731690000)
  upper := (44503169/731690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_18.interval_proof
}

def entry_20_19 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 19
  lower := (54370809/891910000)
  upper := (54549191/891910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_19.interval_proof
}

def entry_20_20 : GramEntryIntervalCertificate :=
{
  h := 20
  k := 20
  lower := (19848461/315390000)
  upper := (19911539/315390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20.interval_20_20.interval_proof
}


def mreg_r_0 (j : Fin 20) : ℚ :=
  if j.val == 0 then (113228981/89810000)
  else if j.val == 1 then (5624/7283)
  else if j.val == 2 then (4136/7193)
  else if j.val == 3 then (1846/3975)
  else if j.val == 4 then (3298/8403)
  else if j.val == 5 then (3191/9344)
  else if j.val == 6 then (2565/8458)
  else if j.val == 7 then (2527/9243)
  else if j.val == 8 then (2018/8093)
  else if j.val == 9 then (157/684)
  else if j.val == 10 then (1867/8770)
  else if j.val == 11 then (1479/7444)
  else if j.val == 12 then (107/574)
  else if j.val == 13 then (1415/8054)
  else if j.val == 14 then (447/2689)
  else if j.val == 15 then (1535/9726)
  else if j.val == 16 then (690/4591)
  else if j.val == 17 then (1356/9449)
  else if j.val == 18 then (453/3298)
  else if j.val == 19 then (1039/7886)
  else 0
def mreg_r_1 (j : Fin 20) : ℚ :=
  if j.val == 0 then (5624/7283)
  else if j.val == 1 then (56618981/89810000)
  else if j.val == 2 then (3022/6851)
  else if j.val == 3 then (2812/7283)
  else if j.val == 4 then (2461/7778)
  else if j.val == 5 then (2068/7193)
  else if j.val == 6 then (1112/4443)
  else if j.val == 7 then (923/3975)
  else if j.val == 8 then (1529/7325)
  else if j.val == 9 then (1649/8403)
  else if j.val == 10 then (1069/5940)
  else if j.val == 11 then (425/2489)
  else if j.val == 12 then (1532/9651)
  else if j.val == 13 then (1459/9622)
  else if j.val == 14 then (997/7003)
  else if j.val == 15 then (799/5845)
  else if j.val == 16 then (457/3534)
  else if j.val == 17 then (1009/8093)
  else if j.val == 18 then (674/5681)
  else if j.val == 19 then (157/1368)
  else 0
def mreg_r_2 (j : Fin 20) : ℚ :=
  if j.val == 0 then (4136/7193)
  else if j.val == 1 then (3022/6851)
  else if j.val == 2 then (37748981/89810000)
  else if j.val == 3 then (1264/4007)
  else if j.val == 4 then (2729/9976)
  else if j.val == 5 then (113/439)
  else if j.val == 6 then (1957/8865)
  else if j.val == 7 then (872/4333)
  else if j.val == 8 then (1371/7153)
  else if j.val == 9 then (1319/7643)
  else if j.val == 10 then (1419/8807)
  else if j.val == 11 then (1372/8863)
  else if j.val == 12 then (949/6639)
  else if j.val == 13 then (1313/9702)
  else if j.val == 14 then (247/1888)
  else if j.val == 15 then (1186/9667)
  else if j.val == 16 then (311/2653)
  else if j.val == 17 then (850/7467)
  else if j.val == 18 then (440/4079)
  else if j.val == 19 then (887/8550)
  else 0
def mreg_r_3 (j : Fin 20) : ℚ :=
  if j.val == 0 then (1846/3975)
  else if j.val == 1 then (2812/7283)
  else if j.val == 2 then (1264/4007)
  else if j.val == 3 then (3622399/11490000)
  else if j.val == 4 then (1579/6383)
  else if j.val == 5 then (1511/6851)
  else if j.val == 6 then (1949/9773)
  else if j.val == 7 then (1406/7283)
  else if j.val == 8 then (1601/9411)
  else if j.val == 9 then (595/3761)
  else if j.val == 10 then (1085/7331)
  else if j.val == 11 then (1034/7193)
  else if j.val == 12 then (385/2917)
  else if j.val == 13 then (556/4443)
  else if j.val == 14 then (382/3209)
  else if j.val == 15 then (923/7950)
  else if j.val == 16 then (843/7744)
  else if j.val == 17 then (743/7119)
  else if j.val == 18 then (741/7390)
  else if j.val == 19 then (741/7552)
  else 0
def mreg_r_4 (j : Fin 20) : ℚ :=
  if j.val == 0 then (3298/8403)
  else if j.val == 1 then (2461/7778)
  else if j.val == 2 then (2729/9976)
  else if j.val == 3 then (1579/6383)
  else if j.val == 4 then (16856683/66830000)
  else if j.val == 5 then (2018/9883)
  else if j.val == 6 then (1433/7848)
  else if j.val == 7 then (1099/6549)
  else if j.val == 8 then (1534/9753)
  else if j.val == 9 then (1057/6844)
  else if j.val == 10 then (1247/8997)
  else if j.val == 11 then (665/5132)
  else if j.val == 12 then (103/840)
  else if j.val == 13 then (647/5521)
  else if j.val == 14 then (818/7113)
  else if j.val == 15 then (601/5619)
  else if j.val == 16 then (239/2345)
  else if j.val == 17 then (919/9395)
  else if j.val == 18 then (866/9167)
  else if j.val == 19 then (227/2444)
  else 0
def mreg_r_5 (j : Fin 20) : ℚ :=
  if j.val == 0 then (3191/9344)
  else if j.val == 1 then (2068/7193)
  else if j.val == 2 then (113/439)
  else if j.val == 3 then (1511/6851)
  else if j.val == 4 then (2018/9883)
  else if j.val == 5 then (18878981/89810000)
  else if j.val == 6 then (1094/6281)
  else if j.val == 7 then (632/4007)
  else if j.val == 8 then (1423/9678)
  else if j.val == 9 then (45/329)
  else if j.val == 10 then (591/4546)
  else if j.val == 11 then (113/878)
  else if j.val == 12 then (825/7049)
  else if j.val == 13 then (184/1667)
  else if j.val == 14 then (1028/9747)
  else if j.val == 15 then (436/4333)
  else if j.val == 16 then (809/8335)
  else if j.val == 17 then (697/7273)
  else if j.val == 18 then (877/9749)
  else if j.val == 19 then (623/7220)
  else 0
def mreg_r_6 (j : Fin 20) : ℚ :=
  if j.val == 0 then (2565/8458)
  else if j.val == 1 then (1112/4443)
  else if j.val == 2 then (1957/8865)
  else if j.val == 3 then (1949/9773)
  else if j.val == 4 then (1433/7848)
  else if j.val == 5 then (1094/6281)
  else if j.val == 6 then (17959967/99670000)
  else if j.val == 7 then (542/3565)
  else if j.val == 8 then (1261/9122)
  else if j.val == 9 then (639/4964)
  else if j.val == 10 then (838/6913)
  else if j.val == 11 then (887/7706)
  else if j.val == 12 then (1107/9985)
  else if j.val == 13 then (755/6844)
  else if j.val == 14 then (1011/9977)
  else if j.val == 15 then (926/9651)
  else if j.val == 16 then (903/9838)
  else if j.val == 17 then (307/3479)
  else if j.val == 18 then (815/9567)
  else if j.val == 19 then (517/6239)
  else 0
def mreg_r_7 (j : Fin 20) : ℚ :=
  if j.val == 0 then (2527/9243)
  else if j.val == 1 then (923/3975)
  else if j.val == 2 then (872/4333)
  else if j.val == 3 then (1406/7283)
  else if j.val == 4 then (1099/6549)
  else if j.val == 5 then (632/4007)
  else if j.val == 6 then (542/3565)
  else if j.val == 7 then (1382877/8770000)
  else if j.val == 8 then (1299/9623)
  else if j.val == 9 then (1143/9241)
  else if j.val == 10 then (764/6619)
  else if j.val == 11 then (1071/9712)
  else if j.val == 12 then (1034/9957)
  else if j.val == 13 then (174/1745)
  else if j.val == 14 then (102/1055)
  else if j.val == 15 then (703/7283)
  else if j.val == 16 then (736/8235)
  else if j.val == 17 then (78/917)
  else if j.val == 18 then (762/9341)
  else if j.val == 19 then (595/7522)
  else 0
def mreg_r_8 (j : Fin 20) : ℚ :=
  if j.val == 0 then (2018/8093)
  else if j.val == 1 then (1529/7325)
  else if j.val == 2 then (1371/7153)
  else if j.val == 3 then (1601/9411)
  else if j.val == 4 then (1534/9753)
  else if j.val == 5 then (1423/9678)
  else if j.val == 6 then (1261/9122)
  else if j.val == 7 then (1299/9623)
  else if j.val == 8 then (12588981/89810000)
  else if j.val == 9 then (585/4817)
  else if j.val == 10 then (534/4781)
  else if j.val == 11 then (1021/9710)
  else if j.val == 12 then (877/8817)
  else if j.val == 13 then (163/1717)
  else if j.val == 14 then (30/329)
  else if j.val == 15 then (81/922)
  else if j.val == 16 then (537/6263)
  else if j.val == 17 then (113/1317)
  else if j.val == 18 then (549/6866)
  else if j.val == 19 then (609/7979)
  else 0
def mreg_r_9 (j : Fin 20) : ℚ :=
  if j.val == 0 then (157/684)
  else if j.val == 1 then (1649/8403)
  else if j.val == 2 then (1319/7643)
  else if j.val == 3 then (595/3761)
  else if j.val == 4 then (1057/6844)
  else if j.val == 5 then (45/329)
  else if j.val == 6 then (639/4964)
  else if j.val == 7 then (1143/9241)
  else if j.val == 8 then (585/4817)
  else if j.val == 9 then (10798559/85590000)
  else if j.val == 10 then (597/5407)
  else if j.val == 11 then (1009/9883)
  else if j.val == 12 then (439/4573)
  else if j.val == 13 then (385/4217)
  else if j.val == 14 then (534/6053)
  else if j.val == 15 then (635/7568)
  else if j.val == 16 then (743/9179)
  else if j.val == 17 then (767/9753)
  else if j.val == 18 then (752/9761)
  else if j.val == 19 then (698/9039)
  else 0
def mreg_r_10 (j : Fin 20) : ℚ :=
  if j.val == 0 then (1867/8770)
  else if j.val == 1 then (1069/5940)
  else if j.val == 2 then (1419/8807)
  else if j.val == 3 then (1085/7331)
  else if j.val == 4 then (1247/8997)
  else if j.val == 5 then (591/4546)
  else if j.val == 6 then (838/6913)
  else if j.val == 7 then (764/6619)
  else if j.val == 8 then (534/4781)
  else if j.val == 9 then (597/5407)
  else if j.val == 10 then (450793/3930000)
  else if j.val == 11 then (642/6341)
  else if j.val == 12 then (724/7709)
  else if j.val == 13 then (521/5880)
  else if j.val == 14 then (715/8469)
  else if j.val == 15 then (785/9683)
  else if j.val == 16 then (329/4216)
  else if j.val == 17 then (78/1037)
  else if j.val == 18 then (162/2221)
  else if j.val == 19 then (493/6930)
  else 0
def mreg_r_11 (j : Fin 20) : ℚ :=
  if j.val == 0 then (1479/7444)
  else if j.val == 1 then (425/2489)
  else if j.val == 2 then (1372/8863)
  else if j.val == 3 then (1034/7193)
  else if j.val == 4 then (665/5132)
  else if j.val == 5 then (113/878)
  else if j.val == 6 then (887/7706)
  else if j.val == 7 then (1071/9712)
  else if j.val == 8 then (1021/9710)
  else if j.val == 9 then (1009/9883)
  else if j.val == 10 then (642/6341)
  else if j.val == 11 then (5054807/48070000)
  else if j.val == 12 then (131/1401)
  else if j.val == 13 then (547/6281)
  else if j.val == 14 then (762/9241)
  else if j.val == 15 then (316/4007)
  else if j.val == 16 then (662/8773)
  else if j.val == 17 then (533/7250)
  else if j.val == 18 then (595/8458)
  else if j.val == 19 then (45/658)
  else 0
def mreg_r_12 (j : Fin 20) : ℚ :=
  if j.val == 0 then (107/574)
  else if j.val == 1 then (1532/9651)
  else if j.val == 2 then (949/6639)
  else if j.val == 3 then (385/2917)
  else if j.val == 4 then (103/840)
  else if j.val == 5 then (825/7049)
  else if j.val == 6 then (1107/9985)
  else if j.val == 7 then (1034/9957)
  else if j.val == 8 then (877/8817)
  else if j.val == 9 then (439/4573)
  else if j.val == 10 then (724/7709)
  else if j.val == 11 then (131/1401)
  else if j.val == 12 then (1379421/14210000)
  else if j.val == 13 then (766/8817)
  else if j.val == 14 then (375/4622)
  else if j.val == 15 then (593/7711)
  else if j.val == 16 then (686/9327)
  else if j.val == 17 then (593/8389)
  else if j.val == 18 then (671/9806)
  else if j.val == 19 then (655/9886)
  else 0
def mreg_r_13 (j : Fin 20) : ℚ :=
  if j.val == 0 then (1415/8054)
  else if j.val == 1 then (1459/9622)
  else if j.val == 2 then (1313/9702)
  else if j.val == 3 then (556/4443)
  else if j.val == 4 then (647/5521)
  else if j.val == 5 then (184/1667)
  else if j.val == 6 then (755/6844)
  else if j.val == 7 then (174/1745)
  else if j.val == 8 then (163/1717)
  else if j.val == 9 then (385/4217)
  else if j.val == 10 then (521/5880)
  else if j.val == 11 then (547/6281)
  else if j.val == 12 then (766/8817)
  else if j.val == 13 then (190211/2110000)
  else if j.val == 14 then (801/9872)
  else if j.val == 15 then (271/3565)
  else if j.val == 16 then (384/5321)
  else if j.val == 17 then (109/1577)
  else if j.val == 18 then (562/8443)
  else if j.val == 19 then (639/9928)
  else 0
def mreg_r_14 (j : Fin 20) : ℚ :=
  if j.val == 0 then (447/2689)
  else if j.val == 1 then (997/7003)
  else if j.val == 2 then (247/1888)
  else if j.val == 3 then (382/3209)
  else if j.val == 4 then (818/7113)
  else if j.val == 5 then (1028/9747)
  else if j.val == 6 then (1011/9977)
  else if j.val == 7 then (102/1055)
  else if j.val == 8 then (30/329)
  else if j.val == 9 then (534/6053)
  else if j.val == 10 then (715/8469)
  else if j.val == 11 then (762/9241)
  else if j.val == 12 then (375/4622)
  else if j.val == 13 then (801/9872)
  else if j.val == 14 then (4044807/48070000)
  else if j.val == 15 then (517/6792)
  else if j.val == 16 then (313/4379)
  else if j.val == 17 then (13/191)
  else if j.val == 18 then (230/3527)
  else if j.val == 19 then (107/1696)
  else 0
def mreg_r_15 (j : Fin 20) : ℚ :=
  if j.val == 0 then (1535/9726)
  else if j.val == 1 then (799/5845)
  else if j.val == 2 then (1186/9667)
  else if j.val == 3 then (923/7950)
  else if j.val == 4 then (601/5619)
  else if j.val == 5 then (436/4333)
  else if j.val == 6 then (926/9651)
  else if j.val == 7 then (703/7283)
  else if j.val == 8 then (81/922)
  else if j.val == 9 then (635/7568)
  else if j.val == 10 then (785/9683)
  else if j.val == 11 then (316/4007)
  else if j.val == 12 then (593/7711)
  else if j.val == 13 then (271/3565)
  else if j.val == 14 then (517/6792)
  else if j.val == 15 then (691877/8770000)
  else if j.val == 16 then (215/2999)
  else if j.val == 17 then (587/8697)
  else if j.val == 18 then (129/2006)
  else if j.val == 19 then (218/3525)
  else 0
def mreg_r_16 (j : Fin 20) : ℚ :=
  if j.val == 0 then (690/4591)
  else if j.val == 1 then (457/3534)
  else if j.val == 2 then (311/2653)
  else if j.val == 3 then (843/7744)
  else if j.val == 4 then (239/2345)
  else if j.val == 5 then (809/8335)
  else if j.val == 6 then (903/9838)
  else if j.val == 7 then (736/8235)
  else if j.val == 8 then (537/6263)
  else if j.val == 9 then (743/9179)
  else if j.val == 10 then (329/4216)
  else if j.val == 11 then (662/8773)
  else if j.val == 12 then (686/9327)
  else if j.val == 13 then (384/5321)
  else if j.val == 14 then (313/4379)
  else if j.val == 15 then (215/2999)
  else if j.val == 16 then (6668981/89810000)
  else if j.val == 17 then (54/797)
  else if j.val == 18 then (630/9857)
  else if j.val == 19 then (483/7918)
  else 0
def mreg_r_17 (j : Fin 20) : ℚ :=
  if j.val == 0 then (1356/9449)
  else if j.val == 1 then (1009/8093)
  else if j.val == 2 then (850/7467)
  else if j.val == 3 then (743/7119)
  else if j.val == 4 then (919/9395)
  else if j.val == 5 then (697/7273)
  else if j.val == 6 then (307/3479)
  else if j.val == 7 then (78/917)
  else if j.val == 8 then (113/1317)
  else if j.val == 9 then (767/9753)
  else if j.val == 10 then (78/1037)
  else if j.val == 11 then (533/7250)
  else if j.val == 12 then (593/8389)
  else if j.val == 13 then (109/1577)
  else if j.val == 14 then (13/191)
  else if j.val == 15 then (587/8697)
  else if j.val == 16 then (54/797)
  else if j.val == 17 then (6298981/89810000)
  else if j.val == 18 then (582/9061)
  else if j.val == 19 then (585/9634)
  else 0
def mreg_r_18 (j : Fin 20) : ℚ :=
  if j.val == 0 then (453/3298)
  else if j.val == 1 then (674/5681)
  else if j.val == 2 then (440/4079)
  else if j.val == 3 then (741/7390)
  else if j.val == 4 then (866/9167)
  else if j.val == 5 then (877/9749)
  else if j.val == 6 then (815/9567)
  else if j.val == 7 then (762/9341)
  else if j.val == 8 then (549/6866)
  else if j.val == 9 then (752/9761)
  else if j.val == 10 then (162/2221)
  else if j.val == 11 then (595/8458)
  else if j.val == 12 then (671/9806)
  else if j.val == 13 then (562/8443)
  else if j.val == 14 then (230/3527)
  else if j.val == 15 then (129/2006)
  else if j.val == 16 then (630/9857)
  else if j.val == 17 then (582/9061)
  else if j.val == 18 then (140211/2110000)
  else if j.val == 19 then (591/9679)
  else 0
def mreg_r_19 (j : Fin 20) : ℚ :=
  if j.val == 0 then (1039/7886)
  else if j.val == 1 then (157/1368)
  else if j.val == 2 then (887/8550)
  else if j.val == 3 then (741/7552)
  else if j.val == 4 then (227/2444)
  else if j.val == 5 then (623/7220)
  else if j.val == 6 then (517/6239)
  else if j.val == 7 then (595/7522)
  else if j.val == 8 then (609/7979)
  else if j.val == 9 then (698/9039)
  else if j.val == 10 then (493/6930)
  else if j.val == 11 then (45/658)
  else if j.val == 12 then (655/9886)
  else if j.val == 13 then (639/9928)
  else if j.val == 14 then (107/1696)
  else if j.val == 15 then (218/3525)
  else if j.val == 16 then (483/7918)
  else if j.val == 17 then (585/9634)
  else if j.val == 18 then (591/9679)
  else if j.val == 19 then (3034807/48070000)
  else 0

def M_reg_fn (i j : Fin 20) : ℚ :=
  if i.val == 0 then mreg_r_0 j
  else if i.val == 1 then mreg_r_1 j
  else if i.val == 2 then mreg_r_2 j
  else if i.val == 3 then mreg_r_3 j
  else if i.val == 4 then mreg_r_4 j
  else if i.val == 5 then mreg_r_5 j
  else if i.val == 6 then mreg_r_6 j
  else if i.val == 7 then mreg_r_7 j
  else if i.val == 8 then mreg_r_8 j
  else if i.val == 9 then mreg_r_9 j
  else if i.val == 10 then mreg_r_10 j
  else if i.val == 11 then mreg_r_11 j
  else if i.val == 12 then mreg_r_12 j
  else if i.val == 13 then mreg_r_13 j
  else if i.val == 14 then mreg_r_14 j
  else if i.val == 15 then mreg_r_15 j
  else if i.val == 16 then mreg_r_16 j
  else if i.val == 17 then mreg_r_17 j
  else if i.val == 18 then mreg_r_18 j
  else if i.val == 19 then mreg_r_19 j
  else 0

def lval_r_0 (j : Fin 20) : ℚ :=
  if j.val == 0 then 1
  else if j.val == 1 then 0
  else if j.val == 2 then 0
  else if j.val == 3 then 0
  else if j.val == 4 then 0
  else if j.val == 5 then 0
  else if j.val == 6 then 0
  else if j.val == 7 then 0
  else if j.val == 8 then 0
  else if j.val == 9 then 0
  else if j.val == 10 then 0
  else if j.val == 11 then 0
  else if j.val == 12 then 0
  else if j.val == 13 then 0
  else if j.val == 14 then 0
  else if j.val == 15 then 0
  else if j.val == 16 then 0
  else if j.val == 17 then 0
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_1 (j : Fin 20) : ℚ :=
  if j.val == 0 then (505091440000/824646668623)
  else if j.val == 1 then 1
  else if j.val == 2 then 0
  else if j.val == 3 then 0
  else if j.val == 4 then 0
  else if j.val == 5 then 0
  else if j.val == 6 then 0
  else if j.val == 7 then 0
  else if j.val == 8 then 0
  else if j.val == 9 then 0
  else if j.val == 10 then 0
  else if j.val == 11 then 0
  else if j.val == 12 then 0
  else if j.val == 13 then 0
  else if j.val == 14 then 0
  else if j.val == 15 then 0
  else if j.val == 16 then 0
  else if j.val == 17 then 0
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_2 (j : Fin 20) : ℚ :=
  if j.val == 0 then (371454160000/814456060333)
  else if j.val == 1 then (2363481593029158497788407340000/4185319163311698722067675940347)
  else if j.val == 2 then 1
  else if j.val == 3 then 0
  else if j.val == 4 then 0
  else if j.val == 5 then 0
  else if j.val == 6 then 0
  else if j.val == 7 then 0
  else if j.val == 8 then 0
  else if j.val == 9 then 0
  else if j.val == 10 then 0
  else if j.val == 11 then 0
  else if j.val == 12 then 0
  else if j.val == 13 then 0
  else if j.val == 14 then 0
  else if j.val == 15 then 0
  else if j.val == 16 then 0
  else if j.val == 17 then 0
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_3 (j : Fin 20) : ℚ :=
  if j.val == 0 then (6631570400/18003407979)
  else if j.val == 1 then (8718728289113224618040000/13503976653345914765954511)
  else if j.val == 2 then (545654345117216697764754584241447207696260457760000/1272932849243464307198850995600506444459976743125813)
  else if j.val == 3 then 1
  else if j.val == 4 then 0
  else if j.val == 5 then 0
  else if j.val == 6 then 0
  else if j.val == 7 then 0
  else if j.val == 8 then 0
  else if j.val == 9 then 0
  else if j.val == 10 then 0
  else if j.val == 11 then 0
  else if j.val == 12 then 0
  else if j.val == 13 then 0
  else if j.val == 14 then 0
  else if j.val == 15 then 0
  else if j.val == 16 then 0
  else if j.val == 17 then 0
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_4 (j : Fin 20) : ℚ :=
  if j.val == 0 then (296193380000/951463127343)
  else if j.val == 1 then (1339891499886161962498500035000/2775472066770173534565219967443)
  else if j.val == 2 then (38972818039162973890059208544828141599788683573019178750/81419379340104351772137483306290461764018515947079051049)
  else if j.val == 3 then (2836457674994064286947431672765071568380914139981141837922803015665110130000/5273782699982368461722222272852504953435571571656987888163677441376979743051)
  else if j.val == 4 then 1
  else if j.val == 5 then 0
  else if j.val == 6 then 0
  else if j.val == 7 then 0
  else if j.val == 8 then 0
  else if j.val == 9 then 0
  else if j.val == 10 then 0
  else if j.val == 11 then 0
  else if j.val == 12 then 0
  else if j.val == 13 then 0
  else if j.val == 14 then 0
  else if j.val == 15 then 0
  else if j.val == 16 then 0
  else if j.val == 17 then 0
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_5 (j : Fin 20) : ℚ :=
  if j.val == 0 then (17911481875/66125724904)
  else if j.val == 1 then (22186176773635445886614810000/44596160986973289550567850481)
  else if j.val == 2 then (34083285357383122532516196271713945261720577240000/64028954078327236538575696706878418782239374627347)
  else if j.val == 3 then (32002036652777746111649183857113355610564027528930119103314116600521852500/96057502226812701005993779556074574060305656610133073902338513427384461639)
  else if j.val == 4 then (2427185474921403909418210375333641110039243475105521920865922826043109764449750228037948348029097555195737847500/5684717931243021251594502854953004740573399484287917078628492604425365963784728257001701680796337511126456423821)
  else if j.val == 5 then 1
  else if j.val == 6 then 0
  else if j.val == 7 then 0
  else if j.val == 8 then 0
  else if j.val == 9 then 0
  else if j.val == 10 then 0
  else if j.val == 11 then 0
  else if j.val == 12 then 0
  else if j.val == 13 then 0
  else if j.val == 14 then 0
  else if j.val == 15 then 0
  else if j.val == 16 then 0
  else if j.val == 17 then 0
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_6 (j : Fin 20) : ℚ :=
  if j.val == 0 then (115181325000/478845360649)
  else if j.val == 1 then (654045337051655078613695920000/1595800337215600240008928860663)
  else if j.val == 2 then (1051353950018449659755628696715627597025322846422954000/2465176375393143419985356998846563040483042410232005053)
  else if j.val == 3 then (8780660918411047911277591076257342336953096244662269323680237299910610000/19587515742564559017295045011788542778730790870745419392347914222719302247)
  else if j.val == 4 then (779669294248955652557051658737413343254213106200503244482004946900470558038380566196144177510363039120000303750/1931389861127504645067440921003172572247857390359770748769993843956260229176730348075420636592632271240292648651)
  else if j.val == 5 then (155323875285373168092167409213852102987777208140716880208176251149468841945818296870841520803711986170487195907750649790094651051305555812558076850658920000/281893164530868791518011454980863364768294204775206252764531657562291412997427694981950469730887433762079329060111230480024447864205916142314321542743591983)
  else if j.val == 6 then 1
  else if j.val == 7 then 0
  else if j.val == 8 then 0
  else if j.val == 9 then 0
  else if j.val == 10 then 0
  else if j.val == 11 then 0
  else if j.val == 12 then 0
  else if j.val == 13 then 0
  else if j.val == 14 then 0
  else if j.val == 15 then 0
  else if j.val == 16 then 0
  else if j.val == 17 then 0
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_7 (j : Fin 20) : ℚ :=
  if j.val == 0 then (226949870000/1046575471383)
  else if j.val == 1 then (17108662544243797231765370800/41605752068958763393905848391)
  else if j.val == 2 then (17279852039709439515916091348879015052925751273680000/46604209578877949652855761818712527307614666370548077)
  else if j.val == 3 then (36947665253690645508506054371993367533330083586361384869477122689620000/64987403616813124079392214312502220940483366235421579617645229726198191)
  else if j.val == 4 then (162490604843545978183788606064642124762808770746936648256354664215974323092508198990267558069445434536012110000/585316786335486567810378003980688520504382582645311132160051264844906614803045002926338838128666927658367740361)
  else if j.val == 5 then (9791116672586473589109808108296699748919031971817265429972720769498383657895983078528873811343695016854199417189370009057983408313461490275816739619920000/24431013331149871295961675885783543241418315104459871765282385887890584215925845317631639164447389297030170249959580284989592367044061472854990445099847467)
  else if j.val == 6 then (20546632973071600923154013130386287228670499073049751538935617797599815633105514075173641036016123817220636457716987930241370841869906193216184119926436834716639409303752345805486333395564166427152000/43276975131380447682648104107653702718728781921916488207275546690295113573446919530172089175885368104690491881374273647525531597358198182876015533468243680024438954396288964825154458272628461488345439)
  else if j.val == 7 then 1
  else if j.val == 8 then 0
  else if j.val == 9 then 0
  else if j.val == 10 then 0
  else if j.val == 11 then 0
  else if j.val == 12 then 0
  else if j.val == 13 then 0
  else if j.val == 14 then 0
  else if j.val == 15 then 0
  else if j.val == 16 then 0
  else if j.val == 17 then 0
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_8 (j : Fin 20) : ℚ :=
  if j.val == 0 then (181236580000/916362143233)
  else if j.val == 1 then (23879854781997326284301788400/67130589382117079754412721707)
  else if j.val == 2 then (14551322145391456539863969473179737476938098855636790000/33888661281378457095678263839554903216918469533854934397)
  else if j.val == 3 then (1226050102421798051632358221630525217104209896197162330027837765606088910000/3236382065421383472419248546764862493709123495809315611497303402951549936251)
  else if j.val == 4 then (293093061661848923069680125817407617987572897082566846666596063211875043468332272939495136791933967542135420120000/819047224827504605986373840889776178124494907587252024656304655151739530956290411364925709314039727267028274166429)
  else if j.val == 5 then (13212116423014693226338924134062851278306138424717924253100992037031418521375787561615426062256958537563426967585187117780233155437424823076520766115360000/36503383334661633237694379961634457839019958396101157165270842156645868984927622248834766003611144851660701391070185196630451990572163643416504487786036021)
  else if j.val == 6 then (10345613907308917258919003546809615224245957001813601101664985564992859740609780410565684986345281529534249350399698895223195627302867771617082132308928776851299748227293961965719604384050362448870955205000/27601564248518561689688681898288082074577212661654563509494512546895743276824328097947909252414401559410897554620047489503618858707723981716558469557432624960408500562937062468765853533195082090295034363441)
  else if j.val == 7 then (569643125827146578497476504527753180752495134770806963865866597531418228814124531989768071665759092525896011975467549252563012972723994483892556169173133970156242461092725836207803322404362570953134168129440963522225686411450428304613469276772157667895810000/976032088140174216854353179239841850970636152412055105303172486930845924467280679292083974319598891807736618013090855505911921382736038190583434430578956220554690493586574008021029917870418345721303400258628470530420888256212972392216718834368582003046680233)
  else if j.val == 8 then 1
  else if j.val == 9 then 0
  else if j.val == 10 then 0
  else if j.val == 11 then 0
  else if j.val == 12 then 0
  else if j.val == 13 then 0
  else if j.val == 14 then 0
  else if j.val == 15 then 0
  else if j.val == 16 then 0
  else if j.val == 17 then 0
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_9 (j : Fin 20) : ℚ :=
  if j.val == 0 then (3525042500/19362155751)
  else if j.val == 1 then (756730957184865612901630000/2141017279586145693930485961)
  else if j.val == 2 then (2472655697572482404431422625964812997673785524678490000/7314120415898810465535586614327200082554815638965440053)
  else if j.val == 3 then (104975280438080660734338851805022568848147024529037861763312122532019050000/279148333098993362580164008296723497053079979779705818371855431393739387249)
  else if j.val == 4 then (237375704754598269691515578332554221633460399213543488271534850857978530498758379673774594968001910630232500/457726576849828299058150098312294512725282404126682683133224752551570041939899577036691151406055918618168239)
  else if j.val == 5 then (13047582819258698648389018738028285107657584239846512756136858278266322809744688432341826560879927744214822009603405203499047121193918417750477225300000/48284184720711628567866944545162863702975582554074696700535800626042676594284457014781983128850781318106196726109031201044553861301821840642807185668761)
  else if j.val == 6 then (598446251428255248801677045392094676412668290290010317551287269118563125352394272038435098731633039957979999229969772087522978614275343266194069990265016198722933854685968838468201786416455773232500/1935289426768837531411152377006301886436577469027421220209799315028305651256655442705024019601023281125354603355011676491851543411896825394548761858349313905659333122059896213919081658602671092050017)
  else if j.val == 7 then (655814517276308679496429389553258900217326937827001550635752300833204629996732422063570857566200434364232438875822992568351118869680463622619689627298014049854078982513107784093442344750080748545465636016988108601889438353173466390336952527583746030000/1511515638623374951102632121053232734169127582650232575217081386387703074119816193876120522050751912764031097296690417550791173861432053230069152200771245137884428102860192875699960034991293212530715182562780711924161083954852757892577051432369387488561)
  else if j.val == 8 then (9145141457111136628128126986296141215799328589761065999600771576379448882149012219274330680822795637000383575837000173499997807279824090456554443393854593886492921474828598672383810984180002963949838158635840002184271911849447947058064314642512540804627369355896342145366782472300248198690748391067399693633604679150000/17637188615435118502677367973680080212937531597769511049411994178574235293066981312794452616865264965037825303612227036637282748696341380516695417067709216294359801731971147878171296341013708699961634985040724200049384120522345920875608065940139206465537864292885947947814198345804682537758171789487037421939964978001693)
  else if j.val == 9 then 1
  else if j.val == 10 then 0
  else if j.val == 11 then 0
  else if j.val == 12 then 0
  else if j.val == 13 then 0
  else if j.val == 14 then 0
  else if j.val == 15 then 0
  else if j.val == 16 then 0
  else if j.val == 17 then 0
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_10 (j : Fin 20) : ℚ :=
  if j.val == 0 then (16767527000/99301816337)
  else if j.val == 1 then (6965088744608462847873588500/22121806886291553919329594501)
  else if j.val == 2 then (1531152868560766695123609721014537595804072150274110000/4583244925701737575739412974468913102249642251943102183)
  else if j.val == 3 then (385339975078318098363062972631395869518654851614248760580912596985747750000/1022885777008309025337142526376359360216879488405692603438073694365727159907)
  else if j.val == 4 then (88983720236734111003452838130182204141555729448619522889389083348418205687199104250563220441811570536946416470000/238800808836432920058732873047047776023005462366224620014667519399537589012916112833493647714491953747509819602897)
  else if j.val == 5 then (174108429910987553175717511103329715430343955060795740564202780914824478941646500021508242212076490908801478742371212266001507812554455915389243568158920000/434933676193697297084459199124002133398261732158925544816977087126394663591206983400438769041801210481691444553728485723011652577754778608385440618800977977)
  else if j.val == 6 then (159187055216491879327692304065860531052532164789009754734731037534853191989870089075045071600652125256325925706877447338550164143617548113905717614444422666615673047590022783243265630439336550155392480000/520856584456147443608469510043468203408954732583717734781979291673015974322229277865315354996673862531743354685244676772357888562391043749622092228428006200454215748334512120065638914763273546724461118073)
  else if j.val == 7 then (42753044235553366549331580040305512609023723931663932290220089245358501329638814324810894267440583394168165779402200308708482350289677302775075999770702698872256698668632091521824335674814302798775990370977615762999994146851008208114822208099892467680000/117893453132124628593788409364652996396936483132229513673929954836992133103802321600698011433789976145979018641386107174260483364948556689872020219090707599002611817573217991619257475508236305449544216137487377001844477759103693750904189410761287968999043)
  else if j.val == 8 then (71564764299774793560533871994507106767252774920648721343825993181219911935297584827613091724046759946474022281185598643173019510261420722509983463964793778559667226949654333016114169039514585763622696872271042369140702531963257645084025115703964090360497874247333366932197210588083278486478302145773293421201924667148580000/171060624697638614301228752419200279939056575962819186702693274228277788371617673027068073250022338204811030242563196027684028490492851458538846008148448830439901257029302269109958378839261906931773802087843013789596410146835775127680693348496222560422857759080514842999621734679771289690842031741020212872251555923313584857)
  else if j.val == 9 then (483345521837831799156981607112367352635724813015013171410679564827960440157909296947560201380967467224178020133356093742850689390436903691280600492440476743599066847724290074133435428616030668341551033221488692363789065004154506603522419888181543047530962540980064788741356257824373913456665229541893866346782303322793878027873533011919159246906954063102103793384073604167515830000/786125499067871761704815180654367296346298733337867881835762435514901583931602730500313879687882936944934514801838274909491400524795922236371798407098954031514130996558040714455594620766877615930607863573826251869999797105698004103078052546753847362382383840398053761430703961309793774174345985247310646590292413689447918578233569668330603581785880207729087755801924004317124876173)
  else if j.val == 10 then 1
  else if j.val == 11 then 0
  else if j.val == 12 then 0
  else if j.val == 13 then 0
  else if j.val == 14 then 0
  else if j.val == 15 then 0
  else if j.val == 16 then 0
  else if j.val == 17 then 0
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_11 (j : Fin 20) : ℚ :=
  if j.val == 0 then (33207247500/210719133641)
  else if j.val == 1 then (122571900190467291366493250000/393401330022774995141066085741)
  else if j.val == 2 then (27742758895463606710170430622628852554837901918049880000/82024019252736434485698315751643126237364832926516170327)
  else if j.val == 3 then (7109476692484441220847341572894514466072101567311327422736120794917286620000/17961473451152397009063709248212879381558624988963168049019996939145183478249)
  else if j.val == 4 then (488887700204621768391466022511731199027696732235613053098022257183544445463057650297505634227139898168200721162500/1793910636375338669729565782339352247458462235621891147277147954604059331338434375116160087147114839523110506183343)
  else if j.val == 5 then (83592518098865875345631742250501998436474482733442661692100909058591236698677897224024909298879824563435087724677094138983922320673781051055540000/155758549689437733643144084941774264539282299175788655762627977431955410210738893315796179787918060224599708509134961181996553994878797073062390549)
  else if j.val == 6 then (6103791235386642272425784451878444675306989517436410926956994007794455899724525574181484251662586372511399660087557780175804252841688582917197418047501733686669403303166930160081961275745710541845240000/31661400866382272472581362746770914540995984181211854128418779816108409391656598148484016048428111911972398309548316090248869053798837168978898866646935841295862526138824703698218463168763092216135413787)
  else if j.val == 7 then (490705828443217078965695061534668583139048782199520091861855341336496873562896372154459496019022894006112927681317983438657472222163698921500237912097586976863186003134690202168117291376960851744331030354324238867289215689406939767107690114548864397938125/1624301211499599246037736275182875781495207474428638814605582457789113225648924333582009297393420004183592405488305151391438792150320197018196230845177265344383977308905559585567744929316857238213494119130409909082141544074486441124706305894039851662804317)
  else if j.val == 8 then (974421182323585125653028322186465208127545561667524204459676273506527777634918119488298720379786449997163766657568944776315088085835603492399647548659991043713935193509893488590946320610958395773182550239715466078255651277946066386424544802186490778038596033464409803537250505748761400908050459883782495873244808581000/2977825262319181351777612433629969502894135453131688212907894089669489168555736504954218859675380231976199483688692218571745362158475273084451195346172273992512497587893721485899705283767882734631254624859405429928452907235349621231924920654020108385241709669587205508067520902313637025850977993151752029342841502349281)
  else if j.val == 9 then (139526867308340492660866538669498882148646500385611572286792816331154564312067478609826565624421284021392662427974284045469392132170267373045360823000867568991660437784696261655933189555827359878054600235563175870914519315232203246664625509714189103898165556458137580826595558691565537119686905891551371238706981656272774230027513111092017478382036164041759218019664011362405010000/288830220152161335649302668712901597820178835575859985226573204960371703003956430809418937735387422243578986830586879752410410601789304342645766588257159315814949903943276779243995517831100878698542167764025034268231189109920819714957309624195451932217789143834970977439295465009160125643356895406948366189518109535181229696005131924712113917635352499367780751470432417873390687987)
  else if j.val == 10 then (7236556439085174626413663780286506701254051834108742603786294727897596633479876527998682904938394941870047457566609025270307796401817020407422587127328781433117948249450927814334469041779948309163446455365043381100706867527189354007145486440623081529684710187559926662904876813302780130975728624478746684337106051365581975892647637849342891897571182974235068498430771646579405588619573428405438953003817456774393877925987692496966766739383543336863580000/14602366873779973173967308737972894176150976737819653110307645129273907606504508511312870402386583445778000696408398485008384961276613797841077718255690328777958982801192288642479291179802596614819506913901900945176649005424003351415654547299080402373504912617122717675750801533209469154756113568701458614994112580919707337642045870419746043519849454457684914128213283403210430679788516520188881901064941016516321776076920066828047552530303497939823664859)
  else if j.val == 11 then 1
  else if j.val == 12 then 0
  else if j.val == 13 then 0
  else if j.val == 14 then 0
  else if j.val == 15 then 0
  else if j.val == 16 then 0
  else if j.val == 17 then 0
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_12 (j : Fin 20) : ℚ :=
  if j.val == 0 then (686405000/4642388221)
  else if j.val == 1 then (9511426708564056361747480000/33606302049931436224247210139)
  else if j.val == 2 then (531367681566777451325556422928094147981263915249530000/1749551026971102992173983069881251944434159106733445883)
  else if j.val == 3 then (54229015544636224164960640926171618328377386767774014707777638057238950000/155365253054738578557397502901224153678766669585751826384929858131552335649)
  else if j.val == 4 then (654291312039514450116648759888277694536313961629146837105447959957957960700587276273539466081604709848345250/2064905912684587190195284094340610287265850146304647063408260070231114973659165580764502781580163636493657267)
  else if j.val == 5 then (3970796577213712659047754942415948689897253998614234566829750905048573415795253946995245551130854599403970531590479918747902863791163540207150297000000/9758956037853905132490664762305269748371004888643128942864443773738904997855448414235697788392412077835689984736070987703225042731173356855755424617099)
  else if j.val == 6 then (89779107784114906288626414198156482099820228538209102127679331994211486635529199946595676391794824763661981833492791173486214851202672430952702319004458973350414125769177253170603407428140463094443500/259956521973021419535085745512991071885616919403776577792258704846836349892655566901117513297022964874037577245283905476095870781368382092553891379275947713416875157048196504071213291471256428588210563)
  else if j.val == 7 then (57626345717096717502108600144813168086186617307873568616602230572409101461379729857583601844680199629724590773177488840398388808759003950325122067448045740668183826015629268808679254217443351731653009290352321766629551784357395414225325568601543920000/196553966015357018666187442545456321304963548815389895455522104723326540166448685154199183773140737613291734107929283117004176930083273565741317865922479763458525077425816354724822212892951865114503976711640772686154227311905923918548755373923606053391)
  else if j.val == 8 then (24301149274142820380960804024968920876174774363427265281808818865016219667999840001175682417002317715034412128441635415487835373904025633387069407005181788945980990128841341478602323067629999693626123933761502890935351553678756887069703827930719041505088874818610471761870985552159178534876313489827551078695873420230000/74164715512645574036834861593277450965659875634840333749370668229665435028194573410320831781422564677849543203279448192758616319109941138473261497402785066926281470111454483009557013504536602003853935312140893762331584586583337788892408335395375109438960160003988669503974576709705602534421479169497590787362663539860533)
  else if j.val == 9 then (59535216563819271490335367784527791977310098982271271928917513736780260757920864154488477391759324774108815713364801252599205377639535219145325262004906535532186747408722388479093069368103400811498772592280311430843234822182405661001539140576925501319343682085817876849799266086996304849158001912295845707885446024357789485303276729390554586601408618656830548509064450384105000/152608099802529277307612244010690490856509741793131846471036283287615424794356395874824331936505343570719124538700553449346278455936680123235143748821494466510967988866285506031389262123488426810387000652126359153354791857196461194837529946499881793034561505754929596769592731516144961956205468343750140086502875910211121581175738781107858613083148075444019696354462907708493811)
  else if j.val == 10 then (508920965732739586203141105356828538600252873659508208294964375711367038441627577500049821319876434062269321978462069876735728719241938157466414880577585649571539961523597593123461241432705793122550143042584445621623256270902210281040921792172999037713546988711744472514628589507505677932650280791652269645801304670643695738776946113434671041940839915779654494418556225611426249021602082273440333812411137644241205562862133817047494702011275779410180000/1228767729579256242232137934577092392832737199214833872325465185303622577769410344185953146324254280460672834232842685919713657589372751954206497866513250824441230574595386773729987336894539521248104449726785687938209654071885516942148627535273081712102219350528671757227554883593670728411176514007327125894553351987112756481413699254460424851635965292441024015687918108810557686342469460050916560106496317963833812741614507173293508198942175122250146313)
  else if j.val == 11 then (4287148900370994216595518028872779388374527846901538154757926163990455680330743295221380511164896320885852801349211591001096688911568711618911513925409283879025581087124639376574736602844714969819633311196565438354807774238165725250262720622716085967528591490280805585782825065882674836406208329303772313092287751083882597880203148867775885371929473559748271622989954713764331183080905776107960067247921408445547859785156751181821023631854382027517287522808434084643175174589438255934674087821052109324613167810726560917427268125/6560839283245617590639250043795712577046155381151000181231609258001490461167241521444646580172828198624494935677442855328350379151705213561731798966990870714929489393831692321808220434260014513072947274389300897699960811825634106394223144954050414748997111764682544482293067839193175985890475231725696460318751745525820454786462968116807129591555523645631301516855591720066182110563633787154311967304733624739955123744839980403346838743790156666793498842695818806791209755507248128906425694797717649012136498045628679323525926074)
  else if j.val == 12 then 1
  else if j.val == 13 then 0
  else if j.val == 14 then 0
  else if j.val == 15 then 0
  else if j.val == 16 then 0
  else if j.val == 17 then 0
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_13 (j : Fin 20) : ℚ :=
  if j.val == 0 then (63540575000/455973106487)
  else if j.val == 1 then (153348385998358812692289495000/548479355916831148944196651571)
  else if j.val == 2 then (147974169752166852085848889807832739207051462639365000/525979808089803503312934640585301528433978986652949971)
  else if j.val == 3 then (23003080973846678749549563456145013332594388583332138641260583959908840000/71143665868758262930232296765700882255156112961039018659928329343137983127)
  else if j.val == 4 then (9769641957045663733423902971711697720618163609573015911208320140635843863591939660631972665438404544328296260000/30576387565044358602122580229508817501514990116538921502657742206527775952168926312290715796031020168796862333643)
  else if j.val == 5 then (2056134372825785393755290547349901265910760153423034553370170563276784199015423377794948698522991964470231007473720345257739678995933478147937756939720000/5834606088548167399885234928090104531322605100671019715511264595169431487155450264496344734682290088460644361414898574673306364095632332470518213704077711)
  else if j.val == 6 then (47126121253374568984779523996497944713149866050567089563709765828936988994230099830787514308535421006811690231975289196801057446714011726980628432114744672393441542728926068491584164777268873662500/93953690843089260163432256247508393008528595550366545925534978633464619979467389673057710479411215433193640113422323857358364678648742409491848494709455106790411659395265249149879751114574499875273)
  else if j.val == 7 then (15674018799529780385613090812871602065633346272236406150817729006207905434357582711749212475760224045874314149833806639061592521819505772324914566170889799259887164984583590605645895374159353894432199651096758920428563625968282763698012433565574468000/69564884759485675242395205269404934423027902613632588063333218529509347744718603166851747299808680789289154851838898779896958213214771985868964840527321942791273962293147317384178961983897509667734112000018265614747061412121487289815657546364502804159)
  else if j.val == 8 then (22390323368914588945419227656476109406804706881010065973879913321340872761057734292405210833226903272128281910206713389941562352695274596315216840443427565676403068040959355744026960415335727981089441665468846512929551547834408360233308560906068182463375636457159825551730488016656156906881541982902424051374935232230000/80476363728563919998334674828198137357414786788064798252051721339718364933817554868122775154558619129032614589853655115479661624476810080594114104439309236885082199501774169904247244078399841869896883552804943228641012503127456079394611239338866299316666213838549985747327714902859287405461777748044334463050315653870707)
  else if j.val == 9 then (16142099145809339302392409241222610107702654589892342378801307407695656485812448827034357040699865772077401934732289412612166563915140268671484414083057896388119268066334534986628872377984577528547702888110126471874223139440069417055479995509619579847878257190855858756383809346923009970135880962294808404621109309013265205945341189289427490140367005979078149745989714647600000/50901401402837780264520588305358775326441532689755766788160905989755856879112013727171765471800085233783410071110355685540450487335661587004577198135206148716398896259363327576093853545491944107350110341244619036645976681427319447281613664665433255750568148627251207061588340295669145045536943020052823313898184037477099464356954089061372131325320572099765887459334702835241867)
  else if j.val == 10 then (11475404710425313785434988926030835804259869530873251560466178830586271822700368038687793482984333132906043124494973007839529463499137971028782112908009762732185981996712613550204088757839667710835314994451443783939482662988270132698405568321772879482329573634314428646777992026385250611662205850475252475041912795586822248724646097378298652468635110560445280651314491379350070231097291415037232455410046164609101703442826470640464111117265065634750/33832123773820715582855529582970777812183915654515068347154630410689247504402526746929381853305613968869318270791274098584600537167126463678782122315492992880274611127496704614674949206063754491579145399392433971002433147456638552916838505536562407164039780062881128322868837955446113518560727439446755612567308693749735250674468910012747252588359216957687168258620923174238341831094963087104713743917950569745453440970239121490678613287790037905673)
  else if j.val == 11 then (484121960536779540037378514137301735551451059091179302392890167649336132942439095650042630401947025824838998975383929694843110213532734260599935425523452968401142523152129082963823257955329408960156173593539933193674862074321193623748866147897232623227906866002405605100599487414626535531560467579752409619136252909355011371036550841502556726482554744345663377059400627458321683674881741267362817042137051986015978727775806374417599855015908019846710904647873510569602444678411583480242343347823242520737098763459135219229375/899259243652875628554522682768506707476450776636300828157572661256303078626808003676374597579787438060208392576230940715209767153182034931708576383943664283648329599209545648658634405998355819922748687754851448760445354185260223943770586478713110568095090144011225325223911329164134434694554253531034282949012680054508600146847383991892328876369590822632865319393988584007531022089157925477599614584513229314145542589270448830183454091888224729685895830572511432545980086356136453288924400312860849214221021114744299847045451)
  else if j.val == 12 then (28518070997809282418273377339690569592052727596100702220456717332982611533388682549751733565061425729776440982761512555408256174614177355324840759123904801159637929506504136767054123909700599264606525965543857296262330606577166393023613545722441522463126199247684336731198118511959935295341678285970194421816262395488138386038484631230690677610250867425524421486234643940844003239553388649613493168066167578152765488170478348732923606727813669714866786381638921537628685708330759831473265556628587872693022028150677446518954082935558044349287036514887777742414961681627055538657502345921698261245000/55264014387120020973836592504755822442663888989651066066707692968889374720704795954106740460095220369758164736673590457644433161235183856647931999441748707999458404302276813365559394331396430199341063771720004859402909153076261076637259391156024433309449844119673753619845977356761906084030501985437028044874016681241816024796214308010907412970953947632447097980571382904946382252744610843054576138708466814741245219242541592095129694285348723284761079661020462870066917186442460892045826805033544722824007205370902770009418979251792074931183631610826772837372400446527857047250390046378320971320369)
  else if j.val == 13 then 1
  else if j.val == 14 then 0
  else if j.val == 15 then 0
  else if j.val == 16 then 0
  else if j.val == 17 then 0
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_14 (j : Fin 20) : ℚ :=
  if j.val == 0 then (40145070000/304472729909)
  else if j.val == 1 then (411887271851536466156083570000/1599335151733287390779740349643)
  else if j.val == 2 then (1321727167602842786747998951664948279637427636886655625/4439621676109795170330031187086186228452090763259875306)
  else if j.val == 3 then (65935629486454354086533237062037202115380619220715094965696649546326140000/216858544544961840470456619325738417204010059249280995863688685284050966043)
  else if j.val == 4 then (4830068352973539267274862500356026772670996671554413286907661328423976745413338350748148607135984814508667549375/13341941304627735025232196564958135294405788364056539341576675024867335379991145007333889591619066097518116035279)
  else if j.val == 5 then (9954950915445945352650682337201008713613258731025247347071120132545575897705430758571041287098521709558941767525618727541523659638367297913169658777680000/34734139451034091252986473467872311861745403607812794271522682560258620162398275836754816116220961314921249494097674542734094275543103269793754534876650007)
  else if j.val == 6 then (180035732542046202863766052453613599536137347176035290431334990376522767689798876622539774198632114296370661136833718732138061134849892578004385413581422060897550230617994707367636638636470823676279796250/540290823491507641932132371610559264046725476519181104263895789589705100588129130413952221690147747428057134101041068675023169222730203250673026222907641354816174765635159851443266922048537354875734387223)
  else if j.val == 7 then (406471008401075159225697461833786585575927977493609803117644221089569986867392611434025154799102893548086120057357988997304782168022629618138466221647696040549754645604740417047514251986228631089939022398974613558775978970223270458101749349368738706000/1096022620091188613450500100825605096718839812096878700230261376104147209037955116509133605788172569214490484306307743915178724445086479318744393426377858522348690545706179137465665850799695502349629816124469070164372374427450858474418418756700428185979)
  else if j.val == 8 then (1825138884345077754522601945037909223376263732408648892117773735225245536880501841350260387016367190840388623065765181114585897684798445215784404589466384989697686705676320452475987531583917846575972760842966981861688994816409546345710783127551614612916698463162881341855602356599218588858967184762725136033690167025000/7779946506221437040837853399643221623124199172601071148080900113814483800829152379299017535449509443909867491804845216412384128909513600039313989223623004609763629301518078517980673550971396776617991995867531139874250359695503985329516659200462530233580547766197448121133400716632414855298566909533035031862720648991507)
  else if j.val == 9 then (2348774500802261024350737748686348029245641895060323673467224883022375094048122950556413597347393353867900257242439814320517416033409342141120742961340808475809251939824470324515426890138314611552608205238210436791100036840999183595704634300752274689096524142282588302216380744616192064167053112571297782482876661655041151638174673764459569299778625601152031844172036962907500/7664386485864648867756860133906303189675413253268269704238942999432895517551968087563452615844140096683753609531257488077362334319643095230372990804148542444940726472238739727143376293384594361726109897562845050558675895623764888806043325697372576869503466808300547838958705545440069925068837605577589469437183217479932015087469929135462984986011825733731658208944725690878899)
  else if j.val == 10 then (34633960805057432554564631404784232917597030567174042358295474103617807854771926559641601584792364703331273765821525894908364236039677598056290609002586863255641793919806305903534242367020067762048205034352134303091626126589155662126344670738950189924937965765111148186028222303318720981958586936149162346861210664536537437390081865062188597275041345116853129581681411536745264372350057004434501431948686696944201535784342558193246734280882793960575000/118015157372178379443730620686016530110296229577044546171696219296280905668609220408868501351031020720601775596624401158585256037100672941392278662171611380625157186752127301267562923742539812762241821512116132930515071634302884220371694771765477233330872616690907862243351793184707492172466092235529256421455379203299209153095412350967122387978564333027296081718720818635172313562945501909579049141665788999532771163428764496146098020180970640022266717)
  else if j.val == 11 then (14697628051289093478128035434766430264847513433462237140966191387366426263446192556159010975481032331625849601373215169934532815285288226809271504184975996704863281515479391348205922334138312644797867808754651129013603507534917968276222410696673356689868483918380884918834204772644816518070609394981812488495639858029508045264364189963945681737167947572593885385788434656780491462322003836487339546354813287095982613320390261032757701006568486314472463034508098838485936724671115031941453656943642573119546585987238917968964005625/32062984616506955474594433742940947417609802997924188609150830341053239882584518837016475265313267836474608018741302364683369865993646311979437961059633262039341538008677166202421837584511238733600150246437052680532081506579106048215621225407289011528058781889814784346848222723021912125105618438362412561855153798978830828187283516449520734489518265293540706311152578010711718400468247512747216547180369498297534605246462121065614482609894296213497650201270365687373605617592936889338637262168673895624757802650987479013558346932)
  else if j.val == 12 then (17550161285061945204612951054135356416701183108681515140862125496243115318442437765392443210249737181002296421185685436978434446856100537564220056274886167862308717743981526252951772336177431224296507841142956221850352345855716405008736725574725028110294696440963772934854637125800410214746467440929423273890999472383107685554030995641942521413486516833439230333346368342576443640535857218727766055104201721108354855901877532003446890791542870895007365332467286243924529242019971110695105962019283107199805408535027787843960878753729853085364085394724459933850341824250768178611107167177495843227711875000/42614544679345879125294839547125491989272362659153835209629828080798221188713090956572390009296014114605588630712373950277998959949272734025191169991973480749575187879728412624128417572960774353640675843876986656175312042542767488731297372158421204266432119601911345239182826352196868625327928240328151094091696702299603962519720913359390268258424489751022381266991313404483354005460190228275051859906063311909694779379655334421955192300225831851647857264929871005945574844533330665445257653961569077488802621526955501052093025218800775244081162604655517688088579964906573371957589722326005715810965806117)
  else if j.val == 13 then (24542144005272192753227612683066152370708825104884545454401496220009096887590311670151357891083638621942366201654560456467627644462643036422962710895394658404501884876991691596371115880558718160361759992739672219381804919250464205085140909446312051483149643178847189163242084822992423798085362798906202954259634657015455780149709558323521938860993854968025567108011963945717228121089132970390503584469257324888595772009280925528428614066635149307543046513835956552392990055464558608685405930068964046556981677405300184561328441240916251894725429254093769920409571308737851165626994082301145073424319832350597515902394742115950849858338406778369372993545237299739097513386875/37860637387796318870111035786880208933996983851611982029565536454021430601113866404965680133565135438259008791932207428262727773644140638079989190380539485838440221218069660339289114505093464188347725045919560598557387717819289637489730354369657069896147342286949606053227061974106921916761209591303969144152356434988803656564234364738895826059273489597438522981423871814718735482822362882399556643083523107645640076920218071044410804392236325925092651875610303076179551360825888874575825964456222281474077386614945812054441013151578005981572842652447783403270484999412610754851800429406220844210320281109953803082806119611762105612786415714497199112911050688604577565881423)
  else if j.val == 14 then 1
  else if j.val == 15 then 0
  else if j.val == 16 then 0
  else if j.val == 17 then 0
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_15 (j : Fin 20) : ℚ :=
  if j.val == 0 then (68929175000/550632534603)
  else if j.val == 1 then (17535790230911247385276078000/68973981281081368840514109609)
  else if j.val == 2 then (583751853954349782947709284482132917637325279595580000/2240801809685069193724483998660750844613669391405029001)
  else if j.val == 3 then (7770425475884385827134286030133331896740363095777665285032187319458200/22739088185371302788685390365907302659867456365538383037588941188029253)
  else if j.val == 4 then (915028705189090778221808460717114628536634300199868690882491038523681499300240680125097757325416593223790000/3315454033590654155974257781030947142707318469493022805105968707429580425859745579213234169672294053679184801)
  else if j.val == 5 then (521635068046273940342435593870911127892726355972645708718929171019298581912332331553563210866587589415798357482152475437535110634823970737420465160000/1644453004420268050108848683615239323802642244368135856090801644749110278988499571446110460011950179545824175927613926420211627928190359303547940725923)
  else if j.val == 6 then (8932757230104894008659041185661087531312867026821566592100713609522058018024717333686124526192038269015975753657709983346212959615292817858998670804223257876005194889206846202440481352767327804440000/30242315063965925500314733637264593139983517899475124964580016083492156522479739093697887260301709471598197055867800304578796214838222592134667503028560265441400003273051817731664699446373423661756019)
  else if j.val == 7 then (2196833768934611008149316155673102740693229320680085369631389198599491334367802895458611631596303455477245326917195609555335340893735769539240701424685280082786799188493482245296978968381437313796680874082479390953504403475519035892573193024530000/4129259106896417954031725248209085485941293406565847110087163868691205646188866342151285589864056918480092798524053231744134154797235233049001926190923913977657952329399188926152301941424517345522927340347920446279274799472323117556359409963413713)
  else if j.val == 8 then (530622568797224417047074916047058448653383202965911182322919625164768311855336681359276272012115502549672414774847847547614363993551697923147643159567091255174987307196114711519477755896145291147543197120556571646744786278516552384302816896252231756349107053279092666230433628041656041429498543251052870715623915000/2854327342934169063246724021818774092275976994915072023043012590838327467741645215367167789276389609672315916480810005134664845961838822759732302763890687392332005361164528929718217594163802112616023784066182223955013777986851493410896514312625865173656599040823469923586522687330689945140289032611448047050526141763)
  else if j.val == 9 then (2700606730830044680722025600243624449883425344421213581190180086309334837440834137742167520114626585834970525489316451238651695190220880478739786843964622079318986578996680693056457354898839383914681803642352475072726370663664556111419170800814249318506963845794321290204511769761247738923781794718297225351258589996428952673502226907080626539688255948394674173414749821875/10327444938764768614435520862374025997282834603967810441482498868813371705360661744175662808786543546157661278141465252575019147710568698428453969367169748345025777063609468150506183426854781233016824728450396090981646260577450282330668956786906020930638810019387179783799780902502612861323893561306480792102209591214373669749181449316700470327674989722644986531522745145857)
  else if j.val == 10 then (2734388349893480398074977134397439625189762829250851630431187194420448947574822494048012169549939764148006079831304325802348897836536531353455485635512978580544419225258656922170502083847154829103786168784665029579572861553291717842355726148682918954383556629991534391767251349089886799288681601105399956907273834010135809080934046503214236144038741531983903563548592488055299201990926392603367422922213696242937945287439709191835527370196468900000/9495204040869420613673342917707196777692598159684900973653493938420519031969456394132231675768320885198543036902151257712139837774071128211403561486053508173205264781245684725066924455408283103481404329418996503945207554827060996554099252888208020901877450994843560753630886707798517219188090844371415372123611360605039433015850426494423878471924743067800549818478155451051196904961340735271951436282368669658500057000972076576705998000942112143127)
  else if j.val == 11 then (9290021790225127229533965016509975420920970662112417213369781811797967199062013728840989599353157692179120068624790097963931797460375000618143896785491097614896920648531901283602654812447053110665791150495604416537762540387465558796204418209239262591714543059513703467055611169821226627174188815645615106281973196669173937440928512526255522116972943120121532516233023068792333415487455177908332799391409543639082418620158685393600177709090112875985023890538693472265975060758724510261173935671074003096304581060703007441250/25668122000077535017525234283976549286747569004063888177197734615937344583731793959791256678089196749693073779555548971752580446532041554804669034755420417234000170470649031721099768916353316145659649103171697735500501337202050271653868025902981412949041048670893620665479641419757950100208466390886409170508840988449825095921767657763311138633691576437815604360907017593402940922898343989330746295755500427515860774273427823011863247373980314614471963837156141374779064963730630514885115761033025837505821852511284547548757)
  else if j.val == 12 then (3460390804182799186516045613991693676129137387792705973001528317342820722365304638730805263980733438746107542418704263172305759161635727881035518213651812223742925976896028348522265051588417948400582704282280987781436506029534104747431970106501887964658209659344966759887865317425628441414346845491634655821877608872194408461040368915163881910383566246121955350012273433736535421998374798073684798018856244840559104548228983347869220085854518818558829369782403897555203840749121381234716763955993505193967989523012151611728154293218130380334944533239701182466737714542124111286185459589377622255000/9766001339080067257099697851286097452516496999862292514685208780473073801205489434815359029745425736565303843474419192005991739986452868340731390404416978992867253807886774728468382973760192236503667642940876838144044771653566410405583395881600373534215542129208769691953897153604626006136196000493968501575052760575068734642237903287287402222131755142272740319013259047460369680480943688453817464075324753223789534801324722024937522323704503819691535478107022189314939002835802912269912801158255120750563922721679416099734650672545317567265041785292953804140642673833276043506316823853189824872601)
  else if j.val == 13 then (102233803458493998034094107951153159645395051022878497284319516917834426187559366501074993016174340744565941419311091519742305015292604827927223274078490350497425920796130901451177908503001908746911140118741846602860430378453995186528007099568412270626440688607051565739100040071616238169096231954351166042567307697789489210340153935439236084727419634271881439142640994956279587319177127221997904849392441025642663271847994285362198299354341552827318355979892279488109332358831284041445538586209941503050961754700297355699186454185001430243229905958756292420499986766315281716353181354221942508054890324525615153750685135139116559452469166107300924931558208308157456781214000/192044374865923436614927448353295353354550740828928656823591221694228818323861784305798345869343988511313502226687071417256873700879059967681222771614035509845657613778748034232636272629058369576357226177609138808549551593289516249564274662816490435979922705931801376060070647069542564582670495495050602332450262774116300348305069968978130052980817425949295790744748903540552593035326346853925762641076733409709427840603935215554903749718913236281024827446953609690686661980564286850818577768041483214238682497926887381411895948713224918892351373152034435871042440786566080397654614591747401569872040594021706167331700720544736644693174614647180579819046912675200820689455871)
  else if j.val == 14 then (5093017639949234945890942978735084015633389002872289985722891199744718995364926025048365249653996080377862091466200883979012263987827409511056934992631697751811468009806761253625026873235334848439434958757942947339677065439817639275577823595359805495132344102933231396105658984670875082547515604185161722753487846212240195178696260372600905533067593310657522716746449563342559261178071360209529861845515687648074188191078410730213661491854977095059376327899929277974482990685014294715363168855473805862286751268360475590022504212497002015596512868826994670927290148289630786294216370424652733342682956636325912439311814714183158204366719562995694354055414960645236669723706542011149944068406273081989658402720543790326149949769599885685631615327126608496605000/9144029806104066005950852918231029988014754649559592172200694741233094578779904168399729648890812066079081336974830157068183546652547865849931590429202787054712277304082651940022424655750587645490495175956157724201436171566831315112112424790963741224815955744135964961420371781843249236636182541823940976813249471614991023017741899718324506734691175323886340202940305932977815377500103998744893256019456277618684980602444965090949839668633348873357143065084172654408646792750136122132546223746049919000828239644495283852898858291135522921897458327246750032281572070213130178612336590549576465798836097162220916800939976782193718173324713628779913951906463935562001263616940794149034580566387912675676119895019732160172798168925518336554421950050983025770638173)
  else if j.val == 15 then 1
  else if j.val == 16 then 0
  else if j.val == 17 then 0
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_16 (j : Fin 20) : ℚ :=
  if j.val == 0 then (61968900000/519834251771)
  else if j.val == 1 then (163042498939748171782426115000/688982825742189335334015608313)
  else if j.val == 2 then (50775681829535781434704124535154915954094113898510000/198157441237379105960577524024912358787216423111442073)
  else if j.val == 3 then (874378793441223274249945755899729683685250811128512005572123745550219375/2919756281240918021447791036587627444566321296770698666057447078203400988)
  else if j.val == 4 then (7457001799991080660913644696393343116788857649877079760847934659523352439700549587514639223391384457979876500/26649658035430650770437518854167966732165372908498111231338363555256338464115431801237720286625753840591940647)
  else if j.val == 5 then (1746125077837239451756823215176011194141107403250944038604260173525290261393566162256619217055898840687628861054070663105729481318651948730247900376000/5085305015201022862174335202355675594593940990683391470356674269483347889732180213708778658446470452877375471375173838519341087713920784157753262658619)
  else if j.val == 6 then (8521630530974828027861387745779578140908014018783948897880378881505981147749762248384170574981785743339173001822564565433841499289074866519108214307538388071882781912495257420549927085870019911072500/30333354149281745127393220391430005494064847556565623232183157917001075388013421939340569570575273432933470156373452333576550691948717630828083887750414528700829553885581960829618512931298375199726971)
  else if j.val == 7 then (97143606668251691454076400197904016520969747158402330357962746941234146036160800284559776921487505384274459417345827258031847537291027543933837072010314531738448102205164851948237326360679148328443977702069705355887102998876095212729030636524687069000/245749513373161974938007146112241572626071311206488204423004232801575568728761409829525875412917201339825120328647497578323276378651406339598088116352754468956858393038911218914808139507919864433545670666294790772087249940605549102011810486907785947419)
  else if j.val == 8 then (61908288547994875828231785094466798963545374611630769923710864925694134748672067926704110017120643145130194558043896457657607831337488169600219728207088106276843501535824747281177356235957490929040996973977532013902720812058043820222146573400455854054218028863483282845935168102327319438268989080208485448461213097500/183360829970522864284452246239935229392699861696953056551964519871758212630829995733601937138394064754358305408635641918425152146736654421711935977597058998000602712587392831292193790225587322645213981320686687035771799771691831804822735249092129329595172083280829054412780544991863796598755005454618399629473760985159)
  else if j.val == 9 then (1023527841899308834413751606453175912012729798326974518605070235685700413449151966968639823968901521822671349640024845162859837766382803137210772502873210181539110200657659511400549961049248347077539886968235686781993493817573608427755286322208538542867598757791511483727472573610516552197328836438540653078529019874587209156152740413275966574747652555632896083702965985947500/3907182374592511206943384600048496399596200936359914119658949986185332537952066595024345832269694925767261936724253246335042415625475742644233939151304146115879981073552172907271662538441986522027071141842194126540614535509100863276948237035181926713856400517957179229940184727813882118977861428722826932312665304229356604697056507342260243737207045949741485855284951638538403)
  else if j.val == 10 then (52887329265896042782277832806213361481491858355548790622975383092835007520091472185319304180742737942591021235182804130206361278094337067032002352469846505648924670597336306626611389477751698159638463332550144361322795452563312469977741728907231230315020592766231436928151929845791033232296568901455207329374396261441084197830993898865867983271435548484604792740910972107739470936284383908108232050780324744088037394689717081203676716093954298161250/195513063155016590474764270288459020720024175572754664964601904725667562801570885030839445044258369295619634737439131341368215211831800907668085680059942477176311713770538445669109971243348071763538521783146541042112229728304782282561941773356023160535621227343914018605057488334820193490271552185867563598157752126421473949199473154679309886032659098059617136689546953165748320574111689940974582294638384722796952320865721849000570307864842134603977)
  else if j.val == 11 then (17234697285986027769373794960871370601337813731876775952253077728017767363011548429195536472858695715480591475835684493606589088965809856166037706316079055289585455866958288890789456933996726301086160155911428294178246828741212223935398018776601322742340979237230358022603031454652007054669708880778829598013051157444189134836501174597760970182229307717503655430308565766028613103489250536520797162650139656849240062959534828252446442576086416972928074161985440243799518484363937934407900882101552774767289558151620883935625/55818386003622847439038083933459958021164915009301646120657444809722313199470712958995031585439321125213244947322043948133982787689366578607427737408097978639197833058780829127140788041825571301265989898324012825637358133162527598443030426779696206375271266300053884140963427186702634871172475229372879917577028177862371793996158554886632201836614618184731706117626162974531772987175829705453432219087159307850702173176213767173704986198754462550541815818619883580039425729565976151444617762806022017742099333731532447926543)
  else if j.val == 12 then (205138781134255690918253091230812729075244906378843372142066107108626469564349973024240367897475825301282661890224365290306241926707327458110032443712866785411359496384057763716578945932629243633410038781125892608165345661879995897697139356724201698881226322939046386088246402314965250073636198481786175076229179019699538316105791303111215906032381354413242077142964998200317612873648417877151161392227031798899335215205990605239558464898989571773470821485168690203945250821114963508254850046078462197533054039416089303526655383501794742186013790376220609110944161411245796376105968255554870690057500/627345220407003769054859278921952326800319785204534787630936148109585067684114904369793282073195013703810641076516725917728644301983589723745791020089805015217380285816414958515282905818127445265161514486961434343206546756244753507686186883667008945738107408088014565549322325424063631489752095813361476019001977496224565837914021202726886681431612735808486420573600429818302346902002990676947607041001409569762143127627947386688710234889137411486823011785622011138883405475821702705475859589979099798413940001700639963177285251797793244358597573282357693812878506619082487620209492381201740204419009)
  else if j.val == 13 then (3303283276862444558663184247946956167510962319368420199354143193865063165162728113103258108919349467372476718847176246448433947800081330247368263511671984210224147516090074419934279357349548292234794136585253752621212980089380470929546844013266116217708631346632212176606634589894916501663658373534013057312959793018610173481099514017377629365337474640892602641657806308860333388276388910095744802885189973702000871040388269612672301915672571542913534011380145326216621404597075880724455445804204957649943765962059196336091315714908016431115169872809212223390432649469248494689713210375961049389591188238613203576570783492701453366449482839059667474626703681216527500/7461192881533860229557520450570042651289007971094942141612273401908785761221636616394644631110352564979030961260883745692802613918244267839439079378940838160285402275614871803522411574904873469824962798922208630407051817275599363935494610042099550390073784891837341167095189069702252188382390409864890503376026155087928375427351982506793281923995627298296127551537621868548947458966218071317915343812133651931507391772653629517918847979850869008364796410858138557767834154632819763026930455330144073354662709101623183772228863316220912153404585981105126936446702021640427816386029411242975062536287520967726720114999354482328652554169991759506006773489113348375341571)
  else if j.val == 14 then (575923345270370477578871362216351175309561891929201516742890277978673091185326758064165989541708222853490190888691416982118978620004933556187050766252988545135959088672897326737080254954914365012283355031784749551007926068287118915664342972451951926779999181809434635198826629411051962853386093093129937232367857829333147779741017365611095314814996667749776461499546728636462973623236692407966173101424004386019505008922221697476453565525043715166682858454295647854396084273785892013345024054550659908017046369029511398142747940772401454016849001164050513073040652765310367171958230351611625912976055516706172730857156215357424849328672082252681627188668818267216300389330393202041413127835770392314456045734874075621974410787659136105004237408196697130000/1233812292160150826784467314086673814865371017228759296262109675513490516848777315932981382403373023637688578521525895677547769718223251309458500096517350762288309921001610535919128040680799879570052820670925974059658073323767937048910221071883167238602719101740831485949992475491184616566502659072306226632538737271912260822974191005903215638442325829512743599736615814185273436803196832945869407224085301642267372656211968543844448084620158541140539049890441037364212838061667115803139329747221287610748914081261606643396690133639985611995319730846205706426875097408149065681494340871544132974403484376791216090444267934717977408354617093250037006413860397575030827285534234815012656589884391068742980583561323650879902061517775879772783313686655941179129)
  else if j.val == 15 then (18359313256407582820986735305550373322384749075953010421150089702083502712587252560460445657637579071270095919328281053537007021891649553030874915525018451155207713151630873642182780206903925231692196748529571468764245904314276442013857780622892633295450430172755037392299576854762609405757073720515100547375138876723492091566201277802072763369425264013957083686281892762710283362333790040004526435249935934821946867729232649484044890024816337217205085115777485372715338102327856054580679438632713967334279162634181153333085996069052671365119239272505709163280417835594651639557695129077172116590719674136660753272937207718455162152915026432588796968639187069036453468933019863921516943119168183210696964887298828205623593297324742921961976756907706713963597340951896763720502091521104975953007832685040424075720528708859698543287206149415625/27527228212492460284068217600676542169272165648759599464641083028093831712272960999849502797395338338341141265006032449490736785127678394293928778342666078199047438595673032915122897957519863579878875477957449346092263993105934909768572078015501654859432280143433551873411187160898801368458004872072738119047121513965011768195049624863669542886353158320612417947071733131869220024345374702247725819557575191710159597717134764594587711555723480806216723436971424529851161673645843402034526768257695273974072270237524776363514976266527987109200285224381217145804476419242649286196762748393671579555612540385377229274828298264556960933665175870335782169506427935705237799682766362707413919663017948650272694683341078086511670739387248103705313063256703646428710027418074881313606200071224634284899898258739840756921512334688555430360040201378344)
  else if j.val == 16 then 1
  else if j.val == 17 then 0
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_17 (j : Fin 20) : ℚ :=
  if j.val == 0 then (121782360000/1069900641469)
  else if j.val == 1 then (1517013779550942596421072890000/6494712686740180408868045809653)
  else if j.val == 2 then (97360372070058344654030861539568447805413441522461500000/380285103199944941734555674382149595294364787279214496873)
  else if j.val == 3 then (7447075178716357927791482033775880623129186367659560041753847216455430170000/27472482509530950398861948663310550658256982101170153919023383993450018242411)
  else if j.val == 4 then (1058548294430282459377959583324572121245572171142992045562343346638739528526060846663546868513231120127323552322000/4018434312083993804511439783443302476462235089832799350434269822467992954358920568108864384645412206976031086427401)
  else if j.val == 5 then (190517606596237079822091089259140729020479005165060626080384424550074491751635308488746016358495701863741532307425001824573988463554154169694340304269760000/477927683681837043364569094032813605189165026481660580365357214448849435293740257936567410573067925366432731017370867595270001921786624628290651881940278409)
  else if j.val == 6 then (66180235307481899694920190660055264180156902245542479288659931025719124767334914431797556971429590562282434042484914086596578213525055647232483593546167558819899760601659769260696735543656539267008490000/288034946285007610894076409262335455023425830995709410034296334205915658816556808999516241002211428957842796679460219278762085001428729587497808186606221814968580244354785181304564310265075826668412431503)
  else if j.val == 7 then (111911982695460526475737891764463513982430794879254268824205562930517897663193467421631174055341326718417811623838178539935772257505891972723744360502751132163187632788609167276703742770950645300476901356648605423791257031190878520894064981156937460000/338539333464185907142044133837056344628225145563016024202996728533149673126193137637508514657491296821682461922681317413830237201507776503943996029909632155826874665876202200832258533329395013781793849844107573274631671646841802726436380326937725556619)
  else if j.val == 8 then (2525698727437036211795033722472003694317986183976530354824784643460438572005283027471458615217754420575896939656076858179405079464239103213630033550164373971352885979984716629652836772197263886199460784307948128547520578335564735897482941222933718915189830538047236614299266664613580707091497825007773253262288010000/5026696059580617565734331335332481418979280810845977660985873717414112783341387164632969861708299325407746134175815410292254995021243238662733576571887031378206067248863361917611772430340233816006963931156230767743643972830965334500423650272032375124096035563819900567099582170155800408282444228319509654813106336909)
  else if j.val == 9 then (205319644831829295822278586318500541698060453994986338861645945487777483665820329797158511262873941596953654962814069047954032255068125120993609127267439010994931663838317220617262498495168826621891132566992762021220170306295638060050590441062124031107935156850958664056174147534057709565535939167675353511872179936698676432276578398638055522727430626450712216216897626279990000/1011665886549782816352903512362993849233741546047697041670719846750434030304403715147774965466352495153410557229921799214416128911088529767501853043271880953084429498614622205394028008144285267061934809256652702680584527537776256757513316995068233582845810165226479208066983474915814975476665426553082033482242737374495039092605515959981103927035240313280840422911150799641187441)
  else if j.val == 10 then (151002744733693841710475385794906957508385538731201374136430744611692304615984716261070524767485910402716323608706334428365416266646346937967221546575960485142244410892509304873655427876233710821270138729736570000687327058611717150547402843050459220538229798989973973475300099854241076802385054402687391285628928456758390197306495588290108345954117904656322475050865949795545129096938239423106271117397761674039451618687910857900058786200003732860000/760406898426461900292572543624282660367787343849654024680364218461225040038727600860746087647743393467448092359336959525052768098341120071768710872685863906563421525097516568292219553079672783428877878125427885258746401991478083562637972468577074663283309774838640588514178289826335600440077826644833533258646299590858455950885954781346287042157350823524711769809718928695003789086050255842730684283434890379891436195922407724767450739268493949238419)
  else if j.val == 11 then (1465819946655323209905907592140013376365483591140378539920785208897751351278952538655151005299073577579914285897007098548354919843165072124618255959823361144791363409996283398029249210645243790153731507472901644950539490089622686709612823324163072467492317161561654174201624753564197974216554470774144031969927461485468554754482689329746043608980638411200721653683194199867673845627250877851255723824418645265317697082685310051243736401226913561116145778915945672565042546758449549258005128321593440035883821404456580247895/4943637198237652007264673570155906082284469939635779825658377176787269336904559799384406932105666724506634798958605760337372631906854420709305118685807313371994121130888846209890268040090837850767466820012716196044880865583133827954403903515870155691542903551976141493442862777202363545272642432367575278033144235741604219650803371969896266982774475864299582032027230098826024687104888399991622431711423467179001465983758037373360462614278069543006432345115252640144321563340008732372337281153894736478865766222142455973494)
  else if j.val == 12 then (1361701984827526943011453600839697944196470938769422623970942987469379629565221442331806580839078022627040042505079309537157918777535559678140805634840629719486291434187004530309777258891633042435803868722996750439902718667164780895594737590273294265800873665412240943118300419085379144638848048682651331467368457514155824001233784971277460504645660981946922613668336470716150954409991362059526461165335793699046697268637280814906792248076909103211155377504923292967541473667946050095906473277738996269295269237427213644061175691308139871231198641560953837770275069666386370704314013582810461603742500/5263954297400163834959621725113840341501114485133046417265951487384627819515919256821582228413451368021039419903075104052163876029279189426223162719441049473834312384085851586672893508379844923874843592789932934696632587401856907985062788119934202921571272791053294885291657612670305350418953228941874782153440901381386255939068512260857194403771379809964994194915619950024011343067053656398843056725287651513599718527168844463811330616798680174561651158942235744841672021726616031569627417915608112100824665147900587299718794933088630154482039306266648603919031474889413349645453703789310633896445899)
  else if j.val == 13 then (1556061257450661889231806083390724907345588996513920621830090747291037738556172721797487409185937111690197269749309128961744818497654340791844695032198955091440488243561155461545510439607829177068300682192679464850511127020840089109169580511813475920904480271942284802141757258141268679708070053273075202393554688441463022009084425385331124539163653482830402358126414499506347212506066857988307657289793216331399140418567229859220596873777470638363687059723883462374989760955256321697799939302335284277229826528017011421366668516865678643445896990756242035706400562538101784308555771963700620502794024392241981939839267998564964048801046497336185161721271755285255577679665000/3926041645224331894399067504970342735426728682294344920546758634242369952430053742854488870002630634572738407229865936146622350908631462588597559889094349339753697121938120796872140376467552148626717614191572871398332761465309565586684497249984114103958149306603299865095972017297165811448120954910217677466069027901744124758965127832088646906069418731397037211482935405471862160980340975082191857593936098172316051320370686235662215192955920224234146594183147301221746209955839546587059081242178851231979243898807481930581591804124316993560761618085583757881104086987890004243542487759168060529782496541847874751867473925524274883800657032831096777184166145635485377439375697)
  else if j.val == 14 then (8259128513715695489696347970825964275404274746614052835454850681841163561315451494929447369969342050910661426874386339834305207030307927579602193683750009867828140920689399210016413348114565053237712036662964188302960922063136546349828914571005889703935045947733519890402994193738044171171408633627234204060520917941695884012104918514149021116941310806682220164587476819341765983603103930284839537074045937598174546042618879950436276452151961618590293373019110344851150976594518092430258086308140971705443647173133905777737374191123026273298228083964256116206211453531333195997165140032339860287757692840225827656678336376791294270697522979609549103455218200066166900249589142028347091743321944597125764756689596236742664100992272873252498637101802523783903235000/20312517475800509530644373627497942049914946530738717429492582306468185662049545921498561508745894562826177594598705360192981660533823944316099319739213184323830849418189542891164256286841325521877792246425087935039446113324445267265942088481855623286880249340985944607541427321174776832557781224921090023676600549036900908336790539481186046054231255115659784459190011318896090001707954922530679313463690852627024578518906372567306017967549481949475137518699220961040104922981483695341680065497953242361183958212374661743258634120308356340925476602228163872054979809885447032474291997857665043340308068781604685156735971749302660615152175409908356953051260324796545891546246548953653244717156454472144859049108653272105094131893980127197696599834258229688913946167)
  else if j.val == 15 then (989585642344460911331698192336965080889719632738437758745351198239660024418784729242078186217151479292181181363818403209339543452821972123680876275205666259702141315756283037121046493856904158800812256983958157033096199763736355435346318499749476444392514574028756673775094089419886998641680837291615647943605141711741820345358139429541290370507988663588027299049996505635489008415694343391949988354715336619082349956400071895354632892198801343089482306722547695154822664157048921929991927382851596852290149408742746907659696673815556236019309180507694950374532478032040582316455972826747100960462930867874364664876188445013841106584644760242285353478593544611522760516116086140384895622439980415333988913128636840838773561156682899789231847579162154844419442877599411705025825354152868368361392784190340912733866980219809091210384723876074845307500/1840630131583027152129469760797908463412087650496043441246695308055903785630578298641203082471697742070766498859598243613660186726349576921778503112451574149318546568648494763538101500678749486250679360072228140084935608893103839962463368269856209407469126094447081896641129562539565326696755773498117035543218649500328856746278194916567534484861829298298994909998755117866935376848306693271676676943926383651609625644892497155153616758011561611453847783222073503540618660773443713054105071701726264254967175434994552993818643158558608390405748302910416478997269162884074772846218414885739716231662135806896214624839735836391843337879226457309740235644769715609352088600792842173662365065675410524438244189264380379616332972162693963587640263332960174904206845550224165272364137243584189199103286431761924924682343245682836768915203641619790959255127)
  else if j.val == 16 then (450227885442116405931023075219657996090272031041788005395254011079144123287007884689300337759534795693190067995335891028331190278235998950199627697920588709005159903795966226013918428955651595038446344032613806414659788358688812156598381864121089902821190506395825711684211002415440376956551908255182641869494053090994024861239729956666818932577264172344754097169165504136841933632340772126171578807389360091112351103467897387646840185864009545025721524437631728772291811990280876297731555038741413305216464744806191492979238314955353666987082421310298236442806285528935542016071121409569947628344912939933619326291004436467573887299765962377531654187936887974181037828771570818355733077596987728513387959383492800348471643608616245672655684115713316743602054716219980628398420422450391646784074645654997418300998553120908483541758901746403099043099758230994845590302949348206939398313631499037592356585770780098752253888597749003960000/857765682028411252243368586029041221953833403187007387554091289308949841230538042576753419758348104222405468882659172950033417182839136447682477300701710824527132433666258506903847523049971534033995648913918514860280865069935677703891466352858741403996135661395674835267565870098017052767377768848322651637250547018357165444136623220785939362202104530649150851743104606597212164385004361695061871225046522113975576539091518599571305006819600081132822247286606479849444631232865320913309279516123007695517067976786751042290015361511800640268009268439429732968989954915942378767915829081037809065308898391189593840335452628613316338436877502394585915290980672082057582698004654064719418290375197660838056069438669077257407684915017677884957390457874077351272547387855253737360346277259950799284004973641510326870628579247610063628148950227899799949412169073779522077088400432996866485353450089806289947346968558163299182954795211776501033)
  else if j.val == 17 then 1
  else if j.val == 18 then 0
  else if j.val == 19 then 0
  else 0
def lval_r_18 (j : Fin 20) : ℚ :=
  if j.val == 0 then (20341965000/186714589669)
  else if j.val == 1 then (174385344844737588398299540000/795627890976530036503799462001)
  else if j.val == 2 then (82426047496130558123446280443794566530231315351600000/345458516588901418656217491878815453841184717681831631)
  else if j.val == 3 then (36797996113758901865371028555732368982809998774253796411502998696597863000/132123514568730677144240348437772286609386807028001744440761702308620440027)
  else if j.val == 4 then (25429988451811204324570160896667664265539571111367541600280493594579638491356406962182974305298234082021148780000/94284333817623588239527099750687781076007611170030869827798898427736258101187641608893894480496775557446632123361)
  else if j.val == 5 then (14090920207570624503512884423895564517832724723730393439905513426273689557376436265063279596612882207412487538489255391562020801239592490035424993509720000/43324992114528860639133599388315304741441648161117508728135492191632420045323421565319248417614397479185371697667852485823604416223278962838819481908941389)
  else if j.val == 6 then (51776686136688531901746904007678114287438809365394208539343864784987306958018430558757921125356321720718712221210213766160483584241033001550788678506531048012606733243841892925640377410843030824947650000/194596644928462653556807350311721725552669517618964259554084991095322150499035885680136676911487372951294183816627591784009545280813376031360954726860822555042398595317982127819555916472004364281087144877)
  else if j.val == 7 then (47617278196848396839534504841693212644429405518621348886148879771635513312478279586348419195723258654257881685604595296602619385670868405099248534978261153493667887543044146417040715926909139785419161874030620185906994420812956756476682113889183815029620000/153630155833229817180250974165818370030852519008987112651882232848196395918583385895116660639932915076349945630062638201104286654935519263624567334945383240221875711133067385993456196009316291787442213290257672038053726909125945483375253201519794295755829041)
  else if j.val == 8 then (475734660929897101088944170941166856707860842619792388258768789724433629246681176786412889856361742693111520188316566800026994956358704336924902467620967530472679602947564115473826797018017023419520177183970327199069120519546321679619313337158638947556753914871616518624198115599145919024338038309994929555271123972280005000/1277586584164658775550443216020620765708314676910692846532251669790177798769215304810219550982865043115591042048152589475957409922911150104656404263038750167950523925236575346504616480768448281806812215140567599475244482510367478960254749538287204664379432319754202007150232324529026725952518886118028209540936694315472879317)
  else if j.val == 9 then (46794052220929739217201510023865384983518106842148227562016198756563657241676334374245627902427943427083337334465901542524164875744299537303266743000219203061996453634767243672651617591221179972715709327223994137951328652493610671808156693566873969911568219569616984081838594037585412770588111763678020145123138117092677561327746243832755317842321205115881484269989124755794302280000/129059964016698810840177442234046967439649634245480467269355991609539158009605960730926691159657915651598028965036346998821289914885431477764793865851473103660369445324391405084957469168632407429967285516989917513113779687613945166873817994090404607352196604408026144583792912707846209909177955860487819744517516590430779244891457409141765040139169491596386710512056876187451304223129)
  else if j.val == 10 then (1063792793103191182582217795313951727465321005202801177023202414085393163555381319329835221849249743818144814290705058005053927654061986988564468642105054260761992634282722541200787599317489803819357625611520472649717489326828756469606015240694734720965499843953735002008043045662493331642088625113251230344735431614968631902619924940748529327693655241742021717317653692635738727894170746499770525230254014810557354042030187277821475398365532482966728901420000/5089594546044458206248174989354690109050330272553043936124061804661527416837589477125000937710108909681101838127830678675688947492855564206959728779423782845756515379512773448732767525550030991418193240524983922638252519424128061836230693968897542952561220044059904140332255673773015641136898052772609456057974975282584293423885691847687066715983562814221800854758280172647778638576269489277303175528666560397165681151695747428012682687376465551947337266383611)
  else if j.val == 11 then (7962062202843847659756714872436166852992017404192888647849433686331932878253097388729389842281825280053037565240985245744198966723705029767819953157734636920327988966779712668677722165842448228775513687784074452611428770293809234986751787823586664205902901901129178839587788005670247542767490687050407361073835179006449784887015417096236727523190747264486642722318042272156389380096197000792141205919792489839678044189201842289842923639672634725221210047813013916893850438554030632527555692163657148669329821472208422880266106603125/29970745157361832629145124007573289130556909452429775352045318624953799478951909557780718592477790274431618450785800771815771539757866046057364916725416574466947921265003239246575320646823008098972670581213557253554204620159806561088779476376813965703067027249288849431301142874706111066613903450331839482603252257596797487991338518444928138115521622512185165889235043599392255104803321541609884722651316821488250179730604812990032379449560330565992715259819317863148593987975561551160569616491234888820868021740943481720712337935926)
  else if j.val == 12 then (172288019605119417769596824972285769485171315683105487725226611938018706660891932882966172576624974649224829967903505404333139587184363955472250223479616627896293881173060253848577018167182615533189588130914012436824303243707012464512619113966081615827753325125786705538048054046503171126468072518800507741832928477652239789650019811502705682411776333551856403921033286028561833942913866722093946282652891322523400810041596979441914173863176916463895519769404780150104776679249076700450616963972010378744487811157230082573744619361136444375913408800035922403501030095196527065042119384017476083267877043119727500/594788628717152486364943420395407689266895799045984117329861486596460866218517744958674659228787299595061535049041557131997625090179725325799485198640551842519771226639166203901974495221134795565137671309913104249194287923597589575888557625058381843842711653964329197453693541726665467676354133998555925081408231442001366277264920128155777087722361460716760482300854600275281091200585449993107939875351047633568370693704951446968309533620823038561723871122739444492519003944707261057983578601561173693240364556506576168246276266527911940010604533724115204576564049348747740130159120401755292968648890954478183869)
  else if j.val == 13 then (19774478410776491731193173465055363595073513578819701780977310875256138416945505293275393525453754828481666416714574486834746414811923228379583441139028466859714758111084756263141390587039205976561776586961386526526979666339925715803910997961890446685534827868212439033946254537536699191368215350378988951624081477298912220134043065036436404052192250248060714818635886278274937049215343152100935703752299482791059451929042344215824121106479019669263359596942781833462553311577041986153923323707460081261311303040969095468124258882332087699547724819683512983147092870025415168542200981476265956984071556618584397353016090466083501609642452711976204061772615861655666874678433722617695000/58248209695232822915709183136520162274197107296452845229736607789932520251805924583469137386611833350887260232790510199370389727107144057050955612843369549837533430353773898391248309150298505090929054298809299340066188729945422797838492561282430433275623155816424154019057532830271073399821729241988893750387943695334390593490697353075446634371505089292635956859329922219058827720069340865760003387106579640127527226978868069672064268253328714184926433272692535722828444129277425003306391160578574362168618170920915969654598390372699416453117934181940126632944273202089056393995938605972346355011198672350558568658810367045729225541926188341351389306362255265743090682876281475128781223)
  else if j.val == 14 then (12013058123148250067849967008683501087401522755970620454278507457684969123943248075149179996338736160487439156463129513318855616991469985365325942178322827580589988116752478046339014558166795058522526597167362254818361779937498152196161013575576709511888052636972473928636164174539658173118388317526326831862172353713845047044385404221829237181656952522378114303879767569509027459741941473145313882198149554265101935103456497969314145415278554783683831780663369377730134144398355100891505810153020360042351941137994358927284638840832061472215556007050745665319756827496241717627740526557876388930246382359737465108944338831722908170141146305754390035209162377308968625086862557047611879071588305944141865995559667517229979017750769005595080237127297593216048433563588775000/34565086482720793782623610911076573195163973786457970506753425391150333651489189431636054161858741902851944435959153819009976077957832966982545964279805611848837868453704311936404234537999822299547006621985214671130005963708629571226953886515296063444746038631212201193200117740617821636125409461168465080602732583093718548643605325623800869229928256558388675930354118580238064609816778187217992886591513883778554232788602441852746789421071407263492444873439900682876937685292166708447583582260268976331976916076862905822302879150888592233115916982634283700406785318337883715356532768576191390377892420790379972849956457112511056986211936297728524087360376526799988023058852679089192056884569427574135038222011184538295482055857804227736318372098136330666722907957549573481)
  else if j.val == 15 then (255059804233908557171765769573852746289744840494581583141401297153536811904055990853949512118184599631549249745560587530471386964487609841197750839737984808691192078624947872618605851606422853929551065623506827565144501647521424876412520083995160264946845837585971332926901054164963225675219825586941520492862124197675700223004972616743827282635604191511279029212847658689349638110186247911018976074973199891081195367948533072925224232427960274755208279309515423858157103803583577061891163490460773852816341101941021081307536503377382508075388700107221144239936025804179625739452387577722685178290712632980053935618487004286189359446723828809706778817525349969813362548452890889875395831795927635764935539964735120847431009717182255136895302453989944650651999964627565878711968545975185738735477689231746060750581846802711871441691984253467107674010716679375/554430822509221788762369014921273525077049056273100731682643055955027467881501603294198886447158401907476826980553548981831795011951962893657414293214435957141082187029579847810037027564653215175854372556606670641351245876302367626260532099902429548263459286986077697722683057031398488961415393506426179586796245436295719191181441500177698105954977135366266896322988344247403804979782248164786216353428432582785915887085486144198252898230525288312177583166892934936791363933005430514181955353595475394856889963603911316443568547624131048158729944021977955075680281839251817117517328603638604111014257115195196631238663584394071304769092237451543992741836491309248844426589110109988942215260783846470639218386733910008516116665413032561705881152068232106567152501611991554307567673276814238813570520731383569221029600667265699373606555663971847957363821637218)
  else if j.val == 16 then (551373024449032284083195683633189277869277618492103949668696817379667468974649735821355980493568100043778751572078106705043550000121030597109392265950337260555645235499169590939577501963747314540287583796386241429239103501236196318927517904040198598094633044111267176411478210226777489916647163797153338370430891961326205401104764600533784160348610846616967455298648730999022233928558089287172482483315220951351042952021399342164294352288111822966963415782385689632347608636805504606743040725240921357165633206072602223864792925652052127510549942640456867956239211298864884683984969496493049843926875153940662433327200415236105541855404738365697771399164958699255701450003849417114159794817105429202854308853980202022698746818700456957606270400460629292415025029135457995944690937373964544475521020214997453753813269308492401763556992372105009404007436277608706723125239083140746104189647140174578261002325286630214749655044702702648642684476769450000/1235137236575182263279451220185866724737092121846551074850161097590975941588615817249468150050581732579415112366826667314686743181895205131452902165253506644044707750969170128262067733871481233249800739062475209168408068025275445477646210143568153721097724660830811855410943319617425434498659577429526472432965234153183530457253255915336603574306693107689316246450398373414373741136599495855516296363600361426114743223839710770339643294541155547363359891237801661332042223125628279655762975422221783242696217637495880676441996425996296212409938902347763834950598531736636512398032342393361868861173453156469725099706002798440926709381847173471932230547314836628923426634928733710943018343513644948889612512759963926582733624597295458970933342905806663108351064953058152034695431975756493747169081074157749371812806699929749304120060897885643001832649212416542539941208279236646720601563349702552329366734048079655848279380976725427097363421690371042223)
  else if j.val == 17 then (310877436902274875677722830553446300768798905486168346280938075296467610303806448028522171950207292620564004723449535577509999279000656943420699234280799017985806267092118166509060147645224155082347272226325908193671209994672679395202070293039121628686180732502184751206121719653913582263939577183779070024407223818515445714119118748698863710978390729774831040026202246993051149405458629213234787157477223803862184387758615850167990819412713724501592385657225307737943931297393145220178686356943350376424693586473293503635954970120193564479632154724544088620051302448190153066688921771709422013103705346268020966126192306254752439534562381287528842870061957945268294278806191610145827135065926169662075896957239407289771926282217306641896884696581877201946977510493848762851391334438641230877023995769857857183392386756816081784698459052570467842428311279490023551465339686621127549869458729257932137660853174538896354383644174044414748337027544540090988295443390715165580733756977169764981663901976081293011806040781173413026289828877337614643403432500/441434034595749639931166168138437494089433717816314958384949711479070699153994500995269474095142392480969166604951154245327168038266113668464043907405891611502415571932845378161624423553935584183269843868843360715883041154524359945172038862482671911358747870920500257821796582421736532960703133034318923833846033149714264550780288067821825931233216135726920583138798429443474235878673858152190073447565074094808382440950434819418239440803838485716391342632783531349665420871229399198094586164603034825265550918796364718953777802087980161106257379153378369912703360616314625285095101424283804938717119629165143104151884433859349381081306229704184142477438915814242070137216408161636988182929948418724002992576724798055832993521298885489863910723996742633775426639481561798117991098910778219982976261875596225548116916600468706741114187894024118880022897021496116981244063684650120167925686938671660877447530299715958653564676236730139338808668327574857136910684496070441975948125252824025356035946664574097985972486150302768011130539190142139315469313801)
  else if j.val == 18 then 1
  else if j.val == 19 then 0
  else 0
def lval_r_19 (j : Fin 20) : ℚ :=
  if j.val == 0 then (46656295000/446461872083)
  else if j.val == 1 then (12390190350795130906591973750/57264759562568824331378156637)
  else if j.val == 2 then (304925194266802219692401728256811388611727327668200/1347137466039703379968305277614219568108754175448953)
  else if j.val == 3 then (1881148391994283332319341374929364778591600874337954150183466494636875/6452433134732541182309362498901670987780162014008410260973069188843448)
  else if j.val == 4 then (829640892827971020366123193314328774949995959318500186730726820231729328013110362222637177886967910271250/2950961690303046175885914879764361367334855148963223044003796526050847010567393155262741033375122933711253)
  else if j.val == 5 then (158514342459314639537632801511921109046550054776710295182392068516333357923832239524020239075930208114054055925641287370218640771443375206817748000/584047717793514774273686357524042622951258406212277503890031267946725522958891625664159254751164467506427169388425227852551659910958197868316336347)
  else if j.val == 6 then (5639309190881314083155244892515148649160211340748389742744886404640649284059154872419780457393488904052812220256395561007004748717957514136338627493534152665083703341857768306064446631996041541250/20830793941741385948911236898298627514249061983666452040825555519490056699511010713934619231805452947183208284777920986130837266880016956870150468734050572539257230119541270231570449296614681026597)
  else if j.val == 7 then (52208853369378031907286018680562602914281828430701399120160448217424226165157324348706194767224563324028039443504871081548941014388556965643613074284940051218358348907622301487743771267341332600288330371996298666226442451909400219852618809962500/183680767406107402072023977070386405244859791413132816119049435585672543694289781851943385689844414189132338268046807861721533546600619951236419405207726499811053686955832484886691964382656104540476054277115124812177219894975681727256610342904029)
  else if j.val == 8 then (12893649807573566955762537639118199701948125372041535245739896076160231650300521992317506561963867820465447812127441537616149129849182453881469694354413871545489282445881414205277189050724576695593692534013224085316390262181570765079713826748840546065882868895390338526506985860643061708551438619847198370316267601250/42660327539543536001009941094664454937733172098174573976874848876017169524332782243192723654597913454901364025939106993130439640368776999318543962477647997953059860310506212074837048205423755226019648635149197511355503832661234920312971158666774563512360647242865115429414448831226908230497479843248426926052033288017)
  else if j.val == 9 then (174014291225116228499203114858731778212263638632691132811685569208351388260764665161177172917703446796496571093429255582534248875618427489279453966523208428507324784443347764767779143080123017416635838850285985773482115693672060393096097589530317886494645367713635055403703011295463324199513346760876538960284215439887426850895211809989113178682940291715529536460171250/327190868187062027607416456439215397282983290853069969262885723729019890445954374443054167984956371519239294214629589564044746396913727645103768465220838811737833017574208350081857112973761092327734322016373041269096787834842276172163429374036365628028701383510021485738651914762766505285464167241993218328240687557837273260898553559754220143736356512101073589822453777)
  else if j.val == 10 then (68088374312352203552532120859514107914833460451742819621086976088557603232794684563253019727120350678655406552837377697618422902742342766536348371473728273184621966089693882492557871176489606881406169316866255558276078280512038509396063615837682701534824676270253065974935567526376697298584388918338663602810230128222833413919937602063669518587242223305249929853986110141717488843745683406076297584014174579346581739157743329469414199846236750/461131974197705987209193887251342683145274927866557824264128217743004981993051495493599222559477870934147564060297957048503009253136053181279144336973556311906320040073685665290613538479249093402101386953918551097040439712564432231417173260776484269232721570284695774601711596445157953822655131764030857650507769392862904752968404152581323758889245845766432190788689468455132651326651287119027277249534718493376231740879081891086590838810207243)
  else if j.val == 11 then (169622367529911326352267174154297056086281618873281561343327258322864586740521858547235509119355581199003327974936114491471256325376362556544263661358237879332470649109315155834974548562130702922696276633169589065246812732846729707037023810934021078178502321905306846676676810286478386993197835065703105236913382221673994098821853439175066607315053801843428963593218964537182217933089616289677967870318223086436199406931555474153933529486807734433407295078167195117438732247181551810746673186963812942917025079690625/687687890259937215880164241809194893465352372764014512344846118975189712261887052926976716647085439643451862463909811196801138017781966081177735524076642831660654739703777431434427514308049497324331282516282889431021584538426528713527792908171336470289624409393418550163112355920639697873220683422482539197817463258714367762573255530807477497664742189054232491411531410526042167992795712962235653971013087044573412790797341843493790028140844231495606291839019763647108836088011088542966422745874303985396598320589762)
  else if j.val == 12 then (548125921038732003821504204373208465987245069353538770447671557356303162850654707312747405262734593340296235576005546919753740852831130022130349428880746693804098050806144327205963791080942423208236720587565537420830444677529788552729915894089839180266987670434959950088283969881763425315935533731532718529187910433630417054791609271707134047457033013882869056447060425260402847163358099759479321507743128334208551464718212564770850192271742671326344983115696252155374465667562724359016561350293668821367636212161244023497454737002335665425647455680333187305269222107923691647220343253732631250/2200759595080758451107368374125018425520992632315443268748436617642587505788795113653664680531631307294455855669769665212759206397190410807251503233051173361207822123079383911540206390427860455038969254746541758567048958618585764563684611909898158874455282001774730034378435450208419505382868313223577045636544612713607983106042089885912871358830931122277466710263914352531232166385954062184785232388454163251820045617103788605665109517235854690891371498240161239730726575464174370335095296844384654518891832145334847595267565914978834780799088579181331026895550447369625366014599930489960938207)
  else if j.val == 13 then (107401101717762726609000725843254321959317924448808813307766389983577819262305912937572043531825411261199983998591420365127324002768284647547094935202556718128821022211827041306693277876112285165086752007342875450047588047283297721423833675805158735203678117032937997235995139988234041235648024478729074820294599850927722742423038079245172759583858028642704200575350268738385935841814894690340281133877773948285113350357762941595744770628427124533450863638536510682377387103129108202754231087746822126712513483957379887358348903538698759069679204341455217575704099582530057903739607663964447667980359970348705367330505317330906126582885647099450713788614388008750/369569294681217387543394325921574512732621293638255661043964978486328866395448059646605675218250483879489438634153325390590572672553717165496898728089019884243700182825792601213308977643168492639207350579867273131435713326543505280848624864153850123506739451262668246536776478984129398108527483415701624654398652252664905155142684299723377858481254640992087706562188941028929295261055278163700540559249274565622252901667336299521680920942956585733103625325162010143615355606516404636188282514664568039445848783753204938196268213520369870500171217736040104656400522910334708690632811630739794506109758746224220931733098386660588725241562113095115667999129935617583)
  else if j.val == 14 then (4154062379143437221257254790788229206726426295120904017960697543233355295923775077487070583570346021834234321204635090242849909173928725224966462275655982124389125560790114756646093921114619173714046981063449004561279135528896962082138512184260216708344247130713933941409506461073830644218958407170046225123466475740696386748090544574889021600398993380483294567128859061470548783705590587672479385380674339343161124163336227326973831020371124879333460358999793434762978159342036705764426594008844493763351566375428380914559846068575240546302660302453289570678137341861901000874817263562660429729458885629627512364339550845449896174546559549407395967587448741734075278461553938959844238982617270841203824550659732246858847822187867077233172628573750/13111884227743264411248531133719169825547797663127898348692880578905378189456006561116647199221521672331016897689411871477378365854019063201733197526528088187621904499684531972161923914152214748066306475113759390350942916402533733368148183006409960134289291136190972446702970488028246323149776880353192641696799969964027569851620376458425255184683973357182952330798577886283996618678161709798257836327393187840252076097855188306699092258926237298916785450198178999865747039389107964766397585153000391785385882603692065661107538629794738004031793795371987621443372369155764988136223360810545051409072207504694384532665592643490844738291148610966806281225459926963686341105613682681422362743020947339583675429424603248366452194953923104566121150564319)
  else if j.val == 15 then (240764852987192461913100208022034428679821778083228922861446803565306949911055330133353918752645761617742968303488150203937703264543043958966303757079181176428378863874495791104841597176084863810499675135933013610943412381941871715035823636996314825626010405193543770054718008994169043643521916443693779694508568071087735033338366664898823719075700695954900016979883612877428309102660332558380956333445883960949259415161410570349872586629744064184509700269170715918484468137048000532401323072077447131231980819166357052138125508502188230542091271964854748805556683471846619451389860563777799542240086937410257751952328821215646939835282311570630741175886841909598272480516888010725232356306883180625874273295658888075723581579137361824765549056928907740836288451222661086839851163420141451901431339121450798929431019542243167477845065925/600072131818733370208200096281541927301899755974141004691866493273840104769288133407865563925445002989181258314129398872930104517799005079705085028198860842120094727445939696481013447925902957056071360818784897714780119565355466984720849284139287325151044747764609504797622239183860303924990877816721993886844401118118531948332778279952162631588214690237177621178341128243101944824619625670660851942112905898602747981806883968013877070597233865246888946363954182637584767377099933327695180456076499785941545207625751340099315434208897301593925585316610773835067169740756704804756029840644157060217767936147884659361509925469914692321013626753383544788690851905645824277288019475260062140142438452598001729964172321834001256676701826855144689046985838341154475870324300290828855262751696146650040193977692575425257159193283303981678435984)
  else if j.val == 16 then (68191602546782212362729717086182857699903867642413156472936792220315173172775956176481459781214934872139001545906781828050675614097606006532230927140144618370967643700940147379906981619742046599425555570976910304391854885757779415928406072662335957883552404754293507640649175458300806501804971509421547427247944793798235532504092964952747355084580518913144313593616609455796013908649096855021368935703790211761988354171178920473099741943132436635252668389130280160667154081390668305055932648200995492564304163089193277628437383444437339294176188035631256820791548285568598090878472952964107561670283911950998251190657986724387693553241559249273376771515057329170081329376143810504220249186729354473480730603989628605870334182737942246830657648601451866761902257694269831316106905646106072048029630187681221911951216673706767618195146231252653846980668029766610213892223682202082454438065625548184031205103792243342793466910625/181148128999794559482527384163801378208737732336902004312582977531973989019547313165876928226707132041464990507718747898300558997310213089839828990658283522267609475734512263103222407505992198902281722719027694934200033916000960569726275844707069548034234011469016389093029099919148129817648415816256212745222504960956411779118671723809411981459895875118460041322024306383651333053517081598175384858448392567580903935860376199836524522739831807965025412208221519355828980037411202795671248551665842197954224090317918097512866545398450332452724374476637466748025610529233704542208627927914808041904495402825538467624841253645383320062063156140093039609551226205411870187581357562162979640246208009437116117566372824785859202607736471729272264692430537748211233800322974849873001024994251147320500794363312912155473108293922415134579876474001430182988845147808343188422693083454769718963742601691564772959389344026930955319566842)
  else if j.val == 17 then (17507162024470428070567652013652581787830073797306255425769660369230949596716489774968049279744994808932323530831221039109017297628874807643369078618944531902313076996209846025231540013420676740042295004842000559280133482630439930428225313411455940277579702250412674981650187791554633313921378835243999284919647793366547674117197289168431542406616924024783654064165817534731201533836714742268087275823385116343026910264761192918398393158529689392419110588452482237073362387187096060149264256344771541525126540054595847520107048783876507633599264122439334711725736754817186559349949690763552625645311257898260393571297734775912660984212861015937371301821295423437179689748971666083338169497160932805919024424144576515431640224167279341930594305870491688964194747371806034072736420509471417965576914188102188643149289024212822115873357182825360109463378240451243880622342531281051912614156427684825310662870639754360443561717079762167273875030507986500445094488519962042604088658018864212950468535159243368313324089402743873162500/29031932829581405662464540490430172867882611042316597648497672290758671926146481814626129400497258598868422766054691692326928597528394891983274170476593324378568038778942082858058342416388044182386439311352224813851027900110233827206475083261582397427279853682944914902338895556931622906827046243336012721098093971227751707823560895495769307160078774239379384757008011223031778615714676721270713931810544589110794541062161299350231788917903628035875005986872457940699047477168107062639875911728818980973564807507646101924192898320595121882069182105028246142768959826052309649733722422562563299156361577406020295627028183198477868518009989310035610219628915652891062193406347987400569273583233833686160849507619312272453332046346563091295330894746132693875363456475729282794544131037098472219385488331002831445596381680175160213962035823617093305066763914329287862966959524488084593328353032628292146877811602452101281083149847906058361245588482349845342978267480007850666777540662792429007977735177492701208446052181662411420129)
  else if j.val == 18 then (1195679704471995461179801615323407977810227669614089121471022101461921125362238035463066137056138994457051901340869433443312054087018850093787759793224050058148098719626651480799368988825468006578820243573598736159763464425089706019241340495634129295858222326537117711057374523039660107261966138441035281809825557990271524578907968314423429979221209056124634054880462643375126625328956252243432287735904283308376982072367255621891718755853828048035009448872898503304827710056628189381249887265749442580382022682140518300228451380108835890192010064500835239272832873849885386843987331723933695361490389745393469467075237853743095888582337194634250399394697334873522520455540341749377457440009599546197327075584827619130523816583711071019682611599068780309433221800131213016070863457343549553984422210994898128550729875677331283919945308701356977943265473216812635105926545972642263647886064167216805327975665649293840971211317248552889037455602244960801435239646251901194825762388506427078433155153834028253403028250781386136440571944721953802436744365673937054708001139847634777076310727422763702120069111635838412035857942748366791816625303512873921250/2233960679560925604813023532040696571041971349833114846142447465963793147107278469704481791268658149290961882827007179660558135617439593625529148529929080310500978847840322568304733582994586336533132468724774004547298263910628944395472676197199834040164574158729012798826358793670940041588476750114335659668232352826582972986054757140646273671975119240060749658890019375656687035235657831095424942015694072690559399139161465968546809558380913866784014092586791969319338426796700808890952949902035363670325660761436114265558870153209371880704911406757413321258963515880254890167281389324956915646735419546070951328487869759616019799428402744903039374150967610123677723714102133435171601982787595253563571499368627980497397275235717115985616539590041504664807158503573543282125668103876007685455391566991598672411075269566892903685579626034753621650341515562279379291379601341799578639123203022059034908405518114374458169546905136031895136265359915887494327500538511586387022510750185240670707315151284574169913778897693505527778870676008384776426370396955018829626092249996089548914852332240716698949350964002549528571576109009741042519395759999724159091)
  else if j.val == 19 then 1
  else 0

def L_val_fn (i j : Fin 20) : ℚ :=
  if i.val == 0 then lval_r_0 j
  else if i.val == 1 then lval_r_1 j
  else if i.val == 2 then lval_r_2 j
  else if i.val == 3 then lval_r_3 j
  else if i.val == 4 then lval_r_4 j
  else if i.val == 5 then lval_r_5 j
  else if i.val == 6 then lval_r_6 j
  else if i.val == 7 then lval_r_7 j
  else if i.val == 8 then lval_r_8 j
  else if i.val == 9 then lval_r_9 j
  else if i.val == 10 then lval_r_10 j
  else if i.val == 11 then lval_r_11 j
  else if i.val == 12 then lval_r_12 j
  else if i.val == 13 then lval_r_13 j
  else if i.val == 14 then lval_r_14 j
  else if i.val == 15 then lval_r_15 j
  else if i.val == 16 then lval_r_16 j
  else if i.val == 17 then lval_r_17 j
  else if i.val == 18 then lval_r_18 j
  else if i.val == 19 then lval_r_19 j
  else 0

def D_val_fn (i : Fin 20) : ℚ :=
  if i.val == 0 then (113228981/89810000)
  else if i.val == 1 then (84930670775760470226129/539390030561677361290000)
  else if i.val == 2 then (1997970296075365448827525094607246194097399901/18523255028909984907727784991494372028599010000)
  else if i.val == 3 then (60824686803419712752445686775678370200311339030715745962000859/1035379304745198794611207117732965840265849231102044884946090000)
  else if i.val == 4 then (1578304571500256988537585061305705496749177542465943190379499417883844778908582783618113226896837/30558782135572008104305775498876932809630049946661719469425555323574302824730953316568938093370000)
  else if i.val == 5 then (3794022269018392882401715362153538606914337647428076393604779645529557362174167571732099472589246142840618978293081078715742800152223687/117687868370029329467752607616017991878227696120227412992311232547762187326698406872741713881508132268567053020104080995510891097493120000)
  else if i.val == 6 then (21689142477939055669087026540877095310219992567759916115652331876534342825234893479781413805087679640699691120684372569531723232987961493344829239107993701086979610658767119182874983/695844850995285978543790234089550068300044276758976091103463916326731066923379631995694513843898191400730057232109754591073270039571428266835410630826514387776111891720820712624830000)
  else if i.val == 7 then (1833116778073488506377236995350768386751326253471960273112549109730064243438219136527089917864100007959867466088279908705744360838469617390893064004712544309108190148476510514022561691005378852487238637011491421083173228965090210479/84202219551615416734415605282787865230386545192104704416041676674266002797037921903673651988414784441335360455282521765098803984764992652712156568137148860300104885742193217157439457389056188103746429226559513590727981897498564790000)
  else if i.val == 8 then (4440482885914209028627736409662578036530362304066799785436082621561571696630005371966162113075319293641449409686257988107364914170557787461884160901004530647398967136466063486184458559101136057305814195980976239578046638017324428263982669326392889673443134146107879510228424700120755920164952531/222208637818190640233222461988633851804726676289337763080296066381768317586023271082419503013908450339576494508497013496770906381565555949861787330573292803587296275701732178794511088719032132208964522086208444878631311177807727251237486958954368392696457058941752785325683885603950860410125310000)
  else if i.val == 9 then (33967076566533808122461354807491440212722540124481245357782276884369236545111073806387643779004985147643759354621114233149504310915863624105669115288162682666983533587076718405452347885300159738433385480714072928391222489808296321571749853250572087581885523396008473453061172603362550581104406116900103234643010161990823934924659490287017910478404633/2209001361655988159873730739505492683324729148072851732149061211842206059249804175767482732370827112654739568649100468871786307600947574943864008449226314704431075515213699621997933842049272664485723917301871829290327637998979098533868084445998689349123393471194991461305535604609917894704973544987623740409861460936326813946082234803184646021746330000)
  else if i.val == 10 then (35477445123845272165945820581606646951992373729874648968973594786259402451125150370476473252221077955899774105754733138634171945423175368675773455366260775036039684734114964802172631695568123379356740221970104046974014615662777775992633748078798435425753498357736885749208096368993731563126294817689263822537854810556774058329164534079663130697667827702928340892017208630650771318258790069697417957848094239194401608150871/2310872911032597809412621945467950460131754321141335312256508586060309392024302078842942671066972382709852535383373585151780902635850843673645077396655978769199472512932153521479568365286270991943889290353771153445730715162914455533448629279610842573026352912089065602065658244621627162504305055859878219395397362380291261989311756794861283068392028508364015776226260987518764982653613774456954118521363599320872686520710000)
  else if i.val == 11 then (183497169277489569774468849072480892266657106789492201144747359357056244540386238641216130088550187234015334745939843327532859366279691890557423341966726308780933792216686598884266478346945662238719878954445425080086142523114582084995237159307669798667538794434045561574369117169922928962377365687353209283669016292512806555674256985247648664290221914254563609354479355557602109208127715116460668711815362680877623691544706344146281118307691770449246424334356380009176858758846435714976804269943/16309374454737469046827553113501426036443713634737314598538613743846653898807666533247457046777013646269878012564210475721428537893470629586770980591012452523295640143479106544973785647523813789079991154243025023032961214527576591221726868059003283460079410345543255189819820872855079290235079250097780097060662968517888988453739530389409962718158735929106112606524491023109927095451102198593324414171525164750144127896057634745360122843347812282795934691500057164456763744969931143456967291226875)
  else if i.val == 12 then (3799144656937470811838757568918693894940700408140133869033855678368562724936246234000213484515370229148475763792591762727428884941278286857725481515303938341648469515775248824279526788407204624845528640940232376886410958917709818719532524910199474268091443737096114825032170055468831695078128183817384964664914892993388707624913004949313428921689942558010403566554577804994283623542279026966731356637217544561446673504156911841135210871347251741565806223547590015777306407661735685081097853035434605027073084400668060751079627307626742968552440733385174778994752736433/323132794920020875256438468729347935496474562175926117218998101631272066691397560225728255771134063456155764853802748364655816463218634538298954230919525507753130352718750491667316488252046385316254602585906113409116620600931444604300732865317198285208480367094261653243739076119584983254841930265139431329514415962616691862334027891747070676037701490970258605831899230670610160832676789840156088081454632637666597334953757070731861380787664766575359657525616454134205372791233976700522049741019009177771106486445615938606242322349420247618265536653547876323064174330000)
  else if i.val == 13 then (68102836632708596852887697240391942332773870354788132538611090334155402784455168556013437178027729153400089526194657663347948024317907514169563335548183850107124392980247729365364659686645597717863635234061912766356502315793224971054510814415100684426646492678047334016025948003796442945391122897048719189728832639896437279972000406438000770023439021275878759798226477663722374724721355987642992809024093857012492139305853753539780946644838373100498010704480194052573554520720422339927770795433810374250584550626180505933763376929122146776296898190609814792099642390013154285396761958628620145410333283075555371254394997033872102889232219/7399951146862023311756924411352893459870102807561656996608153219149389947849272118746159111921239171898915261399047623537051691202489925857921452432877360077808026717042456119346360358708897428614678405538641032627518892995267697853569362758776857802518904254835704168789829524497779910673409610049282252314065825556013590472508547598709033367968711147194702169890706674527854517556936463418559482972758460592277939919934782649010572028246651166151587204323069529642980278848291155029065754891127007886965842278861996818227173378861805577833861082555773381268855177620315985486037027504209619544566407320515119069913760700794075051597190000)
  else if i.val == 14 then (2898913985247063380026083391940129770660898645459284384008545402981952935106833562676048887690651547270537557810210889614391830779568889496528323624223502042485405424738854997154847574474731873061645856803392223253341779696577049389602911506018131393204397595342503087139715592518087935245513502445201550538752688999347395970621604537724108095969111642934794860519926994051331830038326049625704204383181438283203557847620518060086504263966465658214957521613804854926775131848750259456737568881723366700093162720640959984462575445710381670322064151596252832234862497807612008426283476797662006165681618286254036705999111202041006176606049457844955723865338428010162547403221248721120939920629622397536001668583603712688528727/328373642303590713157383901769954277611942591792034486827266907848010643062638392541170471205750171257592882340143470772514563495042318846898579573889095634094537821126318586704664781504775344811297111253572096546581503967106057053898923078998683223955113620232908260142205316684344030019897501400293069365458154668388868058294323020690564071514441772927022286244273511811814707452054214965240627838002674811023942068848811308746270667514751383433587546417185888973305432667862699901337556810010999622290239704479671790553425182627680915086372248228209234151652411125993548143110754010036069610627872304717187962614083325086540923229125815718262138152582255367931065138288447314970032513438426036725152642646243157916668520000)
  else if i.val == 15 then (996741577460299937604318737770158261471505017333809271515922387800452466382530786991012691148316383431783336431880954839794886332178192333743213317435723242026217639811651160950900518732557883631104219116329291885932067067228974167497491856252370009540830164649841498643303444106399832205295339280730028479309033401377418029992759074706159636966907647401571646259143353132870963833210353713401116212596167180086358182347255023583022454806752806525676858575210370191321001155077279524506422931290363913316675762881985568417984056434831896531396697986327126733157386376751357416913951027617282559834052173874629407581616048891206739299070166591101904284617457716712606697540277115416557073797038554773194147229522196911548968027141730155277775706764506570979396980891098570021786463620016342337788581957339343/134589825685531464758239049631689186881349882333409570152527627226589674314127497976076517782547928503581290670767576967631702503020481382268272755355334643561168359831201510119956807866066289929430939523073187805245194842206007431412045163229714419457370105327990294242845694599028110394985324416411150167079086153467508668017375217032227042590676907804205364828925234212053612300404799500031336013603886233335061910375668484895709569127933930712489902086583045907720559878995733809527525375496713179713226938494460722036720203152117088516682611577619520545106511167690536894505597878617826588438019570945354541042122350659470150287033000396002442178737789252652739084822400139307251221099211438544663844823698568987803175065109543719488598941938689886236912966467245229036728852367506445913322862283274914375)
  else if i.val == 16 then (19588799744718588837791856474078366005637092456645322066267777320340970364009658293595375974077639481771316885331845631022109746925238323473843893822486636408574920902256878647700615922732620637296258933691740033341153669840220021235061875399273120577093947995150390890861038222508949847502884627319243894111961971914165194445679321025438742674758086319987016279624658733051807682168644296351565861938504330387385076173611575083210348427209664861526973546437731343401332125093722986483205648764374674705259171245340103584264534145687111114470928754368435378030891019411107504849089636484893506470909915518590524519823820974901390158567005493565524176166937706173159134685209185374329158312224793157646336661225442733273380908624482282795692555196233989716032257396798914972349759064870610853120594838438046160823163469094117703301101334055674988123079364720854196948827494006549956667736189735511/2558148417522048177583864622329950247411785148401299413375307386576927313003506783377978791546967377787280283643701050436792580713191111451844524186878012307157811115682034780328984881505734825813085930429394571121189542557843023999894420813980744745315235350135892445344665162477834212486509091672430204394509661761125709627960783680671949238492515269037172007015438320358586645480121809828382547552576763489631422861584671504174211061402834320418247775837244659464518905550582894124360520657673180481186429202589516115178439223288246560640150722316839274089564940948786582426997657719718954614531399612587058235799228455163097006775686800095006716146934214912126521250800996578499026608599228486801124193623628135363750155525176117136303208213463995012481333054554060856973610301073810727956982748363540854654923376348082301311910051503310918516253424230083268796066936153092791982615830411360000)
  else if i.val == 17 then (170755448100933796404427004867760604426927237468507386968372723390853333223616890907474391341682221580174498870066353422944446232126863325217936873224587071623073981349477406150714189792785826480249193946988600940581825060378346363630340295709145007571344030637126272717557610249547723125079229641602976166859336099088741346465663990739090831536221343767766322758718201982084026389259069815492313607340667489246131841368384536223026428260356775981741670119346709659111094286316659462115069768238849367242556042379387620492486211273571951220909399738068412904258673551837167521566471929015669361426782736947325507338289030747093716466092992608655696915814512500890887654658852765010459085952812413950462866800329274823610883856386995467991060324390967060289999322635533727167832536212164087036243661636090803839288820653358025025206458073166029593739526676530412664613026885099002178724572009301498166103532192624375617891561044304628058287365616999632910990269901380790946998771181900074840725177/29049789576194216642054780862644284292789080065770000470473898211305830550208150350712674110397047977693276361495985169374947308332827992068864149935389508144206940622083524728136892850197193606800259743432687791414538184300117892723439051629150099492353933937944946170739539978072216257721583696779486893502707706685996565333943442748033155052990798009118598199013778428052373681636769978078293123038039696400535682504493876406954328268701378379584514281451744228118891076386884360327860589569878546042473401849547504443923636213728099879815529226636465240366795503101827115745476280344867576363079698221744862014270629223661128913373568889928638117024400336743349042467540890998586643348499357831860389314516928710884544656095968276392014619929763274739073953676847024517410790158983855505302819586832343671268199932422464737905311254485857445929439772867831725942419242449744004620541851815100379947725424120475090877940560929061110230772027925138034108667221725119942559959278089358564304770000)
  else if i.val == 18 then (138263050252911642109105349843582892629721770966342048390590516205764387918821092169217680936239799679317140179168863832610003963686311822022994297343917198447581279228825710034471194513875521760720902758223672297935856974080099035236930583423147617477844925410265798304918188719466630172254269165052590262341642629033193788189397574741683783363646738444237186049001593536154717766777560608713044447186132225615490269007078489773394974279405281723111526794326098193477421120724722077126843181711434243228834122484221151756425485520928783552885477573958383708102777735907055370324774698133330362120862532842774244182454265007945950638212922269043138921274038716587172756210751794639800016093507445443332089955958092165197984957723295858629995842255806093459725246667334518307475257462447918719465376821498053256061525196723455050227165156327224220593453023134258927218888820923667300523205740821145004443672324091244910312669756360952770449090236847358009547380455749846480334073338763288894701879466068568141168560967510154548893374767600764615267136020717306062846010807455820875700615736770967416804360427703835787/21671153290721369665966217426600983011965307184312544156469482628537732810976194446526080988247068082490327354348916369450932647690605600986170913324625912327296817815733075697299196680230212112167037503359016970074034368721070587932604808879546143589687105742114096134728161889735391223239546389372083977399702758461635782721110071263861060076301046189083355966628275629878661745482320136095761691934792282374359643965062819397144609973328354257791899557431493154201186830840059262754933298961849326110817293750737266944952616909650187397819044043859381945665210290818749640461127476814357266996243978702474326112528668696775445338724946581578205801532793138350951017176999196568053862098291315593599255513887478670032348848133138860128213111829200137583762627045107230580072888937796307507925390856695308256321740858414377724598339692995993524501653814748423213413005487247067094648886296002661238368161697920749514735850938496778657736296051866491918229023703555042923509807817997699489346001677499263531177374542434418014535502468292647612865827196002631215485599913481673185429014843230142533305683677585807870000)
  else if i.val == 19 then (6211317995475365051756382441745135441532555513025860934079093971418157814611386106903078271143686230161080518690907425395859316644074372189896271428341803239343396103380493501194181596970622305163944734132105085246340032184155157001099551372402693578802548280952507158279389118462624663888319636608134897790210761879212314591783920014554146876331960704345649367916295200491864001660369952879376762776210522514642117036495920815732786704464513034300383110833700016997800869065738702132429102539439626886152449765490862771221469989527361590580258814278723044300930579635315168177373300178151496033219092683273759774295517241903742981465381381724273093749587639475516258760867801695284193414112766657702180993514804537854201988027448544336073436149708007222963968229533879896222367425214640887072269027320960070597480300278787902801544353550108191677063910828234212524267419136109839289938579913074041360738061652603991023633963496438078639429407517086092413423769101416927704951496004321904878922571216561089238332794897438916906073797486027125256224983680661541463481207720664814322949626374201212221832833060266588236285228637002694029838780548492884400134755466191614552989719178716511910733657960431/1207416455140228250348367982368128353579841883381913618947910722096905083194953923193275285318884847289082804122517257125561011070633766938854233458497883499303180229328801644030792855874229342941412113806132157092645324804182338796714593647999043967629521607642641805497075179466089468606885275277933136865357726069293013540034361814639576230263581823887237518763278794366196066426283924833360950296579458162543306720038189691563824225474885650227159850870157094818297197478215074317514775024359662736583024325079178238875742846576668008179742179714775616502485173602259273681183990369805715871962550047479759027573872082495625678597581270038363290360814635875941652743615703056333956957307491536895471380755772860645133386374985145397780311836800060535400090958401586169108943957261890789919912281578931144937181792045504418165951732234948886418628515541886362329046650566210156957114558508396024693596712065522299607021491652614065877292955546365642699683470722641832934574422742117467875667828206226175095361911357900122155793704545731998917844835624341855382928558354291722572601253649438928118400266917285328051496382005022871080265917152538371543909335241309389484645007518376265746703717985560000)
  else 0

def linear_fn (i : Fin 20) : ℚ :=
  if i.val == 0 then (334885130399/792094461875)
  else if i.val == 1 then (539229655814/966420695621)
  else if i.val == 2 then (429555871558/847029364035)
  else if i.val == 3 then (365803125173/808816390216)
  else if i.val == 4 then (310041832416/762814777745)
  else if i.val == 5 then (185905148602/503684275485)
  else if i.val == 6 then (217680372953/643292168266)
  else if i.val == 7 then (265373981399/848441330135)
  else if i.val == 8 then (94134966137/323363287511)
  else if i.val == 9 then (204131695733/749005597659)
  else if i.val == 10 then (238998603362/932039438163)
  else if i.val == 11 then (209301576511/863784676978)
  else if i.val == 12 then (228196111150/992909593093)
  else if i.val == 13 then (57329321650/262133248871)
  else if i.val == 14 then (158608442467/759901748079)
  else if i.val == 15 then (9491117430/47524303471)
  else if i.val == 16 then (158172395365/825839262239)
  else if i.val == 17 then (102860339921/558828520785)
  else if i.val == 18 then (32547503008/183653562427)
  else if i.val == 19 then (44895414341/262660208977)
  else 0

def coeff_fn (i : Fin 20) : ℚ :=
  if i.val == 0 then (-41950145/44092894)
  else if i.val == 1 then (743009227/804799370)
  else if i.val == 2 then (742168863/818031683)
  else if i.val == 3 then (110548121/833630158)
  else if i.val == 4 then (77107813/101027156)
  else if i.val == 5 then (-103454861/189469924)
  else if i.val == 6 then (264424658/423956421)
  else if i.val == 7 then (5187867/265733695)
  else if i.val == 8 then (5090269/194740019)
  else if i.val == 9 then (-370931710/990925679)
  else if i.val == 10 then (115759694/280705269)
  else if i.val == 11 then (-18268564/412345565)
  else if i.val == 12 then (396679187/979045839)
  else if i.val == 13 then (-252128311/734676925)
  else if i.val == 14 then (-181116504/612491653)
  else if i.val == 15 then (9558079/748461582)
  else if i.val == 16 then (139241791/472451640)
  else if i.val == 17 then (-14936567/371956101)
  else if i.val == 18 then (321205085/992545651)
  else if i.val == 19 then (-219380821/899251277)
  else 0

def M_reg : Matrix (Fin 20) (Fin 20) ℚ := M_reg_fn
def L_val : Matrix (Fin 20) (Fin 20) ℚ := L_val_fn
def D_val : Fin 20 → ℚ := D_val_fn

-- Provide interval models
def glwr_r_0 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_1_1.lower
  else if j.val == 1 then entry_1_2.lower
  else if j.val == 2 then entry_1_3.lower
  else if j.val == 3 then entry_1_4.lower
  else if j.val == 4 then entry_1_5.lower
  else if j.val == 5 then entry_1_6.lower
  else if j.val == 6 then entry_1_7.lower
  else if j.val == 7 then entry_1_8.lower
  else if j.val == 8 then entry_1_9.lower
  else if j.val == 9 then entry_1_10.lower
  else if j.val == 10 then entry_1_11.lower
  else if j.val == 11 then entry_1_12.lower
  else if j.val == 12 then entry_1_13.lower
  else if j.val == 13 then entry_1_14.lower
  else if j.val == 14 then entry_1_15.lower
  else if j.val == 15 then entry_1_16.lower
  else if j.val == 16 then entry_1_17.lower
  else if j.val == 17 then entry_1_18.lower
  else if j.val == 18 then entry_1_19.lower
  else if j.val == 19 then entry_1_20.lower
  else 0
def glwr_r_1 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_2_1.lower
  else if j.val == 1 then entry_2_2.lower
  else if j.val == 2 then entry_2_3.lower
  else if j.val == 3 then entry_2_4.lower
  else if j.val == 4 then entry_2_5.lower
  else if j.val == 5 then entry_2_6.lower
  else if j.val == 6 then entry_2_7.lower
  else if j.val == 7 then entry_2_8.lower
  else if j.val == 8 then entry_2_9.lower
  else if j.val == 9 then entry_2_10.lower
  else if j.val == 10 then entry_2_11.lower
  else if j.val == 11 then entry_2_12.lower
  else if j.val == 12 then entry_2_13.lower
  else if j.val == 13 then entry_2_14.lower
  else if j.val == 14 then entry_2_15.lower
  else if j.val == 15 then entry_2_16.lower
  else if j.val == 16 then entry_2_17.lower
  else if j.val == 17 then entry_2_18.lower
  else if j.val == 18 then entry_2_19.lower
  else if j.val == 19 then entry_2_20.lower
  else 0
def glwr_r_2 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_3_1.lower
  else if j.val == 1 then entry_3_2.lower
  else if j.val == 2 then entry_3_3.lower
  else if j.val == 3 then entry_3_4.lower
  else if j.val == 4 then entry_3_5.lower
  else if j.val == 5 then entry_3_6.lower
  else if j.val == 6 then entry_3_7.lower
  else if j.val == 7 then entry_3_8.lower
  else if j.val == 8 then entry_3_9.lower
  else if j.val == 9 then entry_3_10.lower
  else if j.val == 10 then entry_3_11.lower
  else if j.val == 11 then entry_3_12.lower
  else if j.val == 12 then entry_3_13.lower
  else if j.val == 13 then entry_3_14.lower
  else if j.val == 14 then entry_3_15.lower
  else if j.val == 15 then entry_3_16.lower
  else if j.val == 16 then entry_3_17.lower
  else if j.val == 17 then entry_3_18.lower
  else if j.val == 18 then entry_3_19.lower
  else if j.val == 19 then entry_3_20.lower
  else 0
def glwr_r_3 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_4_1.lower
  else if j.val == 1 then entry_4_2.lower
  else if j.val == 2 then entry_4_3.lower
  else if j.val == 3 then entry_4_4.lower
  else if j.val == 4 then entry_4_5.lower
  else if j.val == 5 then entry_4_6.lower
  else if j.val == 6 then entry_4_7.lower
  else if j.val == 7 then entry_4_8.lower
  else if j.val == 8 then entry_4_9.lower
  else if j.val == 9 then entry_4_10.lower
  else if j.val == 10 then entry_4_11.lower
  else if j.val == 11 then entry_4_12.lower
  else if j.val == 12 then entry_4_13.lower
  else if j.val == 13 then entry_4_14.lower
  else if j.val == 14 then entry_4_15.lower
  else if j.val == 15 then entry_4_16.lower
  else if j.val == 16 then entry_4_17.lower
  else if j.val == 17 then entry_4_18.lower
  else if j.val == 18 then entry_4_19.lower
  else if j.val == 19 then entry_4_20.lower
  else 0
def glwr_r_4 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_5_1.lower
  else if j.val == 1 then entry_5_2.lower
  else if j.val == 2 then entry_5_3.lower
  else if j.val == 3 then entry_5_4.lower
  else if j.val == 4 then entry_5_5.lower
  else if j.val == 5 then entry_5_6.lower
  else if j.val == 6 then entry_5_7.lower
  else if j.val == 7 then entry_5_8.lower
  else if j.val == 8 then entry_5_9.lower
  else if j.val == 9 then entry_5_10.lower
  else if j.val == 10 then entry_5_11.lower
  else if j.val == 11 then entry_5_12.lower
  else if j.val == 12 then entry_5_13.lower
  else if j.val == 13 then entry_5_14.lower
  else if j.val == 14 then entry_5_15.lower
  else if j.val == 15 then entry_5_16.lower
  else if j.val == 16 then entry_5_17.lower
  else if j.val == 17 then entry_5_18.lower
  else if j.val == 18 then entry_5_19.lower
  else if j.val == 19 then entry_5_20.lower
  else 0
def glwr_r_5 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_6_1.lower
  else if j.val == 1 then entry_6_2.lower
  else if j.val == 2 then entry_6_3.lower
  else if j.val == 3 then entry_6_4.lower
  else if j.val == 4 then entry_6_5.lower
  else if j.val == 5 then entry_6_6.lower
  else if j.val == 6 then entry_6_7.lower
  else if j.val == 7 then entry_6_8.lower
  else if j.val == 8 then entry_6_9.lower
  else if j.val == 9 then entry_6_10.lower
  else if j.val == 10 then entry_6_11.lower
  else if j.val == 11 then entry_6_12.lower
  else if j.val == 12 then entry_6_13.lower
  else if j.val == 13 then entry_6_14.lower
  else if j.val == 14 then entry_6_15.lower
  else if j.val == 15 then entry_6_16.lower
  else if j.val == 16 then entry_6_17.lower
  else if j.val == 17 then entry_6_18.lower
  else if j.val == 18 then entry_6_19.lower
  else if j.val == 19 then entry_6_20.lower
  else 0
def glwr_r_6 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_7_1.lower
  else if j.val == 1 then entry_7_2.lower
  else if j.val == 2 then entry_7_3.lower
  else if j.val == 3 then entry_7_4.lower
  else if j.val == 4 then entry_7_5.lower
  else if j.val == 5 then entry_7_6.lower
  else if j.val == 6 then entry_7_7.lower
  else if j.val == 7 then entry_7_8.lower
  else if j.val == 8 then entry_7_9.lower
  else if j.val == 9 then entry_7_10.lower
  else if j.val == 10 then entry_7_11.lower
  else if j.val == 11 then entry_7_12.lower
  else if j.val == 12 then entry_7_13.lower
  else if j.val == 13 then entry_7_14.lower
  else if j.val == 14 then entry_7_15.lower
  else if j.val == 15 then entry_7_16.lower
  else if j.val == 16 then entry_7_17.lower
  else if j.val == 17 then entry_7_18.lower
  else if j.val == 18 then entry_7_19.lower
  else if j.val == 19 then entry_7_20.lower
  else 0
def glwr_r_7 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_8_1.lower
  else if j.val == 1 then entry_8_2.lower
  else if j.val == 2 then entry_8_3.lower
  else if j.val == 3 then entry_8_4.lower
  else if j.val == 4 then entry_8_5.lower
  else if j.val == 5 then entry_8_6.lower
  else if j.val == 6 then entry_8_7.lower
  else if j.val == 7 then entry_8_8.lower
  else if j.val == 8 then entry_8_9.lower
  else if j.val == 9 then entry_8_10.lower
  else if j.val == 10 then entry_8_11.lower
  else if j.val == 11 then entry_8_12.lower
  else if j.val == 12 then entry_8_13.lower
  else if j.val == 13 then entry_8_14.lower
  else if j.val == 14 then entry_8_15.lower
  else if j.val == 15 then entry_8_16.lower
  else if j.val == 16 then entry_8_17.lower
  else if j.val == 17 then entry_8_18.lower
  else if j.val == 18 then entry_8_19.lower
  else if j.val == 19 then entry_8_20.lower
  else 0
def glwr_r_8 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_9_1.lower
  else if j.val == 1 then entry_9_2.lower
  else if j.val == 2 then entry_9_3.lower
  else if j.val == 3 then entry_9_4.lower
  else if j.val == 4 then entry_9_5.lower
  else if j.val == 5 then entry_9_6.lower
  else if j.val == 6 then entry_9_7.lower
  else if j.val == 7 then entry_9_8.lower
  else if j.val == 8 then entry_9_9.lower
  else if j.val == 9 then entry_9_10.lower
  else if j.val == 10 then entry_9_11.lower
  else if j.val == 11 then entry_9_12.lower
  else if j.val == 12 then entry_9_13.lower
  else if j.val == 13 then entry_9_14.lower
  else if j.val == 14 then entry_9_15.lower
  else if j.val == 15 then entry_9_16.lower
  else if j.val == 16 then entry_9_17.lower
  else if j.val == 17 then entry_9_18.lower
  else if j.val == 18 then entry_9_19.lower
  else if j.val == 19 then entry_9_20.lower
  else 0
def glwr_r_9 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_10_1.lower
  else if j.val == 1 then entry_10_2.lower
  else if j.val == 2 then entry_10_3.lower
  else if j.val == 3 then entry_10_4.lower
  else if j.val == 4 then entry_10_5.lower
  else if j.val == 5 then entry_10_6.lower
  else if j.val == 6 then entry_10_7.lower
  else if j.val == 7 then entry_10_8.lower
  else if j.val == 8 then entry_10_9.lower
  else if j.val == 9 then entry_10_10.lower
  else if j.val == 10 then entry_10_11.lower
  else if j.val == 11 then entry_10_12.lower
  else if j.val == 12 then entry_10_13.lower
  else if j.val == 13 then entry_10_14.lower
  else if j.val == 14 then entry_10_15.lower
  else if j.val == 15 then entry_10_16.lower
  else if j.val == 16 then entry_10_17.lower
  else if j.val == 17 then entry_10_18.lower
  else if j.val == 18 then entry_10_19.lower
  else if j.val == 19 then entry_10_20.lower
  else 0
def glwr_r_10 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_11_1.lower
  else if j.val == 1 then entry_11_2.lower
  else if j.val == 2 then entry_11_3.lower
  else if j.val == 3 then entry_11_4.lower
  else if j.val == 4 then entry_11_5.lower
  else if j.val == 5 then entry_11_6.lower
  else if j.val == 6 then entry_11_7.lower
  else if j.val == 7 then entry_11_8.lower
  else if j.val == 8 then entry_11_9.lower
  else if j.val == 9 then entry_11_10.lower
  else if j.val == 10 then entry_11_11.lower
  else if j.val == 11 then entry_11_12.lower
  else if j.val == 12 then entry_11_13.lower
  else if j.val == 13 then entry_11_14.lower
  else if j.val == 14 then entry_11_15.lower
  else if j.val == 15 then entry_11_16.lower
  else if j.val == 16 then entry_11_17.lower
  else if j.val == 17 then entry_11_18.lower
  else if j.val == 18 then entry_11_19.lower
  else if j.val == 19 then entry_11_20.lower
  else 0
def glwr_r_11 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_12_1.lower
  else if j.val == 1 then entry_12_2.lower
  else if j.val == 2 then entry_12_3.lower
  else if j.val == 3 then entry_12_4.lower
  else if j.val == 4 then entry_12_5.lower
  else if j.val == 5 then entry_12_6.lower
  else if j.val == 6 then entry_12_7.lower
  else if j.val == 7 then entry_12_8.lower
  else if j.val == 8 then entry_12_9.lower
  else if j.val == 9 then entry_12_10.lower
  else if j.val == 10 then entry_12_11.lower
  else if j.val == 11 then entry_12_12.lower
  else if j.val == 12 then entry_12_13.lower
  else if j.val == 13 then entry_12_14.lower
  else if j.val == 14 then entry_12_15.lower
  else if j.val == 15 then entry_12_16.lower
  else if j.val == 16 then entry_12_17.lower
  else if j.val == 17 then entry_12_18.lower
  else if j.val == 18 then entry_12_19.lower
  else if j.val == 19 then entry_12_20.lower
  else 0
def glwr_r_12 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_13_1.lower
  else if j.val == 1 then entry_13_2.lower
  else if j.val == 2 then entry_13_3.lower
  else if j.val == 3 then entry_13_4.lower
  else if j.val == 4 then entry_13_5.lower
  else if j.val == 5 then entry_13_6.lower
  else if j.val == 6 then entry_13_7.lower
  else if j.val == 7 then entry_13_8.lower
  else if j.val == 8 then entry_13_9.lower
  else if j.val == 9 then entry_13_10.lower
  else if j.val == 10 then entry_13_11.lower
  else if j.val == 11 then entry_13_12.lower
  else if j.val == 12 then entry_13_13.lower
  else if j.val == 13 then entry_13_14.lower
  else if j.val == 14 then entry_13_15.lower
  else if j.val == 15 then entry_13_16.lower
  else if j.val == 16 then entry_13_17.lower
  else if j.val == 17 then entry_13_18.lower
  else if j.val == 18 then entry_13_19.lower
  else if j.val == 19 then entry_13_20.lower
  else 0
def glwr_r_13 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_14_1.lower
  else if j.val == 1 then entry_14_2.lower
  else if j.val == 2 then entry_14_3.lower
  else if j.val == 3 then entry_14_4.lower
  else if j.val == 4 then entry_14_5.lower
  else if j.val == 5 then entry_14_6.lower
  else if j.val == 6 then entry_14_7.lower
  else if j.val == 7 then entry_14_8.lower
  else if j.val == 8 then entry_14_9.lower
  else if j.val == 9 then entry_14_10.lower
  else if j.val == 10 then entry_14_11.lower
  else if j.val == 11 then entry_14_12.lower
  else if j.val == 12 then entry_14_13.lower
  else if j.val == 13 then entry_14_14.lower
  else if j.val == 14 then entry_14_15.lower
  else if j.val == 15 then entry_14_16.lower
  else if j.val == 16 then entry_14_17.lower
  else if j.val == 17 then entry_14_18.lower
  else if j.val == 18 then entry_14_19.lower
  else if j.val == 19 then entry_14_20.lower
  else 0
def glwr_r_14 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_15_1.lower
  else if j.val == 1 then entry_15_2.lower
  else if j.val == 2 then entry_15_3.lower
  else if j.val == 3 then entry_15_4.lower
  else if j.val == 4 then entry_15_5.lower
  else if j.val == 5 then entry_15_6.lower
  else if j.val == 6 then entry_15_7.lower
  else if j.val == 7 then entry_15_8.lower
  else if j.val == 8 then entry_15_9.lower
  else if j.val == 9 then entry_15_10.lower
  else if j.val == 10 then entry_15_11.lower
  else if j.val == 11 then entry_15_12.lower
  else if j.val == 12 then entry_15_13.lower
  else if j.val == 13 then entry_15_14.lower
  else if j.val == 14 then entry_15_15.lower
  else if j.val == 15 then entry_15_16.lower
  else if j.val == 16 then entry_15_17.lower
  else if j.val == 17 then entry_15_18.lower
  else if j.val == 18 then entry_15_19.lower
  else if j.val == 19 then entry_15_20.lower
  else 0
def glwr_r_15 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_16_1.lower
  else if j.val == 1 then entry_16_2.lower
  else if j.val == 2 then entry_16_3.lower
  else if j.val == 3 then entry_16_4.lower
  else if j.val == 4 then entry_16_5.lower
  else if j.val == 5 then entry_16_6.lower
  else if j.val == 6 then entry_16_7.lower
  else if j.val == 7 then entry_16_8.lower
  else if j.val == 8 then entry_16_9.lower
  else if j.val == 9 then entry_16_10.lower
  else if j.val == 10 then entry_16_11.lower
  else if j.val == 11 then entry_16_12.lower
  else if j.val == 12 then entry_16_13.lower
  else if j.val == 13 then entry_16_14.lower
  else if j.val == 14 then entry_16_15.lower
  else if j.val == 15 then entry_16_16.lower
  else if j.val == 16 then entry_16_17.lower
  else if j.val == 17 then entry_16_18.lower
  else if j.val == 18 then entry_16_19.lower
  else if j.val == 19 then entry_16_20.lower
  else 0
def glwr_r_16 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_17_1.lower
  else if j.val == 1 then entry_17_2.lower
  else if j.val == 2 then entry_17_3.lower
  else if j.val == 3 then entry_17_4.lower
  else if j.val == 4 then entry_17_5.lower
  else if j.val == 5 then entry_17_6.lower
  else if j.val == 6 then entry_17_7.lower
  else if j.val == 7 then entry_17_8.lower
  else if j.val == 8 then entry_17_9.lower
  else if j.val == 9 then entry_17_10.lower
  else if j.val == 10 then entry_17_11.lower
  else if j.val == 11 then entry_17_12.lower
  else if j.val == 12 then entry_17_13.lower
  else if j.val == 13 then entry_17_14.lower
  else if j.val == 14 then entry_17_15.lower
  else if j.val == 15 then entry_17_16.lower
  else if j.val == 16 then entry_17_17.lower
  else if j.val == 17 then entry_17_18.lower
  else if j.val == 18 then entry_17_19.lower
  else if j.val == 19 then entry_17_20.lower
  else 0
def glwr_r_17 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_18_1.lower
  else if j.val == 1 then entry_18_2.lower
  else if j.val == 2 then entry_18_3.lower
  else if j.val == 3 then entry_18_4.lower
  else if j.val == 4 then entry_18_5.lower
  else if j.val == 5 then entry_18_6.lower
  else if j.val == 6 then entry_18_7.lower
  else if j.val == 7 then entry_18_8.lower
  else if j.val == 8 then entry_18_9.lower
  else if j.val == 9 then entry_18_10.lower
  else if j.val == 10 then entry_18_11.lower
  else if j.val == 11 then entry_18_12.lower
  else if j.val == 12 then entry_18_13.lower
  else if j.val == 13 then entry_18_14.lower
  else if j.val == 14 then entry_18_15.lower
  else if j.val == 15 then entry_18_16.lower
  else if j.val == 16 then entry_18_17.lower
  else if j.val == 17 then entry_18_18.lower
  else if j.val == 18 then entry_18_19.lower
  else if j.val == 19 then entry_18_20.lower
  else 0
def glwr_r_18 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_19_1.lower
  else if j.val == 1 then entry_19_2.lower
  else if j.val == 2 then entry_19_3.lower
  else if j.val == 3 then entry_19_4.lower
  else if j.val == 4 then entry_19_5.lower
  else if j.val == 5 then entry_19_6.lower
  else if j.val == 6 then entry_19_7.lower
  else if j.val == 7 then entry_19_8.lower
  else if j.val == 8 then entry_19_9.lower
  else if j.val == 9 then entry_19_10.lower
  else if j.val == 10 then entry_19_11.lower
  else if j.val == 11 then entry_19_12.lower
  else if j.val == 12 then entry_19_13.lower
  else if j.val == 13 then entry_19_14.lower
  else if j.val == 14 then entry_19_15.lower
  else if j.val == 15 then entry_19_16.lower
  else if j.val == 16 then entry_19_17.lower
  else if j.val == 17 then entry_19_18.lower
  else if j.val == 18 then entry_19_19.lower
  else if j.val == 19 then entry_19_20.lower
  else 0
def glwr_r_19 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_20_1.lower
  else if j.val == 1 then entry_20_2.lower
  else if j.val == 2 then entry_20_3.lower
  else if j.val == 3 then entry_20_4.lower
  else if j.val == 4 then entry_20_5.lower
  else if j.val == 5 then entry_20_6.lower
  else if j.val == 6 then entry_20_7.lower
  else if j.val == 7 then entry_20_8.lower
  else if j.val == 8 then entry_20_9.lower
  else if j.val == 9 then entry_20_10.lower
  else if j.val == 10 then entry_20_11.lower
  else if j.val == 11 then entry_20_12.lower
  else if j.val == 12 then entry_20_13.lower
  else if j.val == 13 then entry_20_14.lower
  else if j.val == 14 then entry_20_15.lower
  else if j.val == 15 then entry_20_16.lower
  else if j.val == 16 then entry_20_17.lower
  else if j.val == 17 then entry_20_18.lower
  else if j.val == 18 then entry_20_19.lower
  else if j.val == 19 then entry_20_20.lower
  else 0

def gram_lower (i j : Fin 20) : ℚ :=
  if i.val == 0 then glwr_r_0 j
  else if i.val == 1 then glwr_r_1 j
  else if i.val == 2 then glwr_r_2 j
  else if i.val == 3 then glwr_r_3 j
  else if i.val == 4 then glwr_r_4 j
  else if i.val == 5 then glwr_r_5 j
  else if i.val == 6 then glwr_r_6 j
  else if i.val == 7 then glwr_r_7 j
  else if i.val == 8 then glwr_r_8 j
  else if i.val == 9 then glwr_r_9 j
  else if i.val == 10 then glwr_r_10 j
  else if i.val == 11 then glwr_r_11 j
  else if i.val == 12 then glwr_r_12 j
  else if i.val == 13 then glwr_r_13 j
  else if i.val == 14 then glwr_r_14 j
  else if i.val == 15 then glwr_r_15 j
  else if i.val == 16 then glwr_r_16 j
  else if i.val == 17 then glwr_r_17 j
  else if i.val == 18 then glwr_r_18 j
  else if i.val == 19 then glwr_r_19 j
  else 0

def gupr_r_0 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_1_1.upper
  else if j.val == 1 then entry_1_2.upper
  else if j.val == 2 then entry_1_3.upper
  else if j.val == 3 then entry_1_4.upper
  else if j.val == 4 then entry_1_5.upper
  else if j.val == 5 then entry_1_6.upper
  else if j.val == 6 then entry_1_7.upper
  else if j.val == 7 then entry_1_8.upper
  else if j.val == 8 then entry_1_9.upper
  else if j.val == 9 then entry_1_10.upper
  else if j.val == 10 then entry_1_11.upper
  else if j.val == 11 then entry_1_12.upper
  else if j.val == 12 then entry_1_13.upper
  else if j.val == 13 then entry_1_14.upper
  else if j.val == 14 then entry_1_15.upper
  else if j.val == 15 then entry_1_16.upper
  else if j.val == 16 then entry_1_17.upper
  else if j.val == 17 then entry_1_18.upper
  else if j.val == 18 then entry_1_19.upper
  else if j.val == 19 then entry_1_20.upper
  else 0
def gupr_r_1 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_2_1.upper
  else if j.val == 1 then entry_2_2.upper
  else if j.val == 2 then entry_2_3.upper
  else if j.val == 3 then entry_2_4.upper
  else if j.val == 4 then entry_2_5.upper
  else if j.val == 5 then entry_2_6.upper
  else if j.val == 6 then entry_2_7.upper
  else if j.val == 7 then entry_2_8.upper
  else if j.val == 8 then entry_2_9.upper
  else if j.val == 9 then entry_2_10.upper
  else if j.val == 10 then entry_2_11.upper
  else if j.val == 11 then entry_2_12.upper
  else if j.val == 12 then entry_2_13.upper
  else if j.val == 13 then entry_2_14.upper
  else if j.val == 14 then entry_2_15.upper
  else if j.val == 15 then entry_2_16.upper
  else if j.val == 16 then entry_2_17.upper
  else if j.val == 17 then entry_2_18.upper
  else if j.val == 18 then entry_2_19.upper
  else if j.val == 19 then entry_2_20.upper
  else 0
def gupr_r_2 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_3_1.upper
  else if j.val == 1 then entry_3_2.upper
  else if j.val == 2 then entry_3_3.upper
  else if j.val == 3 then entry_3_4.upper
  else if j.val == 4 then entry_3_5.upper
  else if j.val == 5 then entry_3_6.upper
  else if j.val == 6 then entry_3_7.upper
  else if j.val == 7 then entry_3_8.upper
  else if j.val == 8 then entry_3_9.upper
  else if j.val == 9 then entry_3_10.upper
  else if j.val == 10 then entry_3_11.upper
  else if j.val == 11 then entry_3_12.upper
  else if j.val == 12 then entry_3_13.upper
  else if j.val == 13 then entry_3_14.upper
  else if j.val == 14 then entry_3_15.upper
  else if j.val == 15 then entry_3_16.upper
  else if j.val == 16 then entry_3_17.upper
  else if j.val == 17 then entry_3_18.upper
  else if j.val == 18 then entry_3_19.upper
  else if j.val == 19 then entry_3_20.upper
  else 0
def gupr_r_3 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_4_1.upper
  else if j.val == 1 then entry_4_2.upper
  else if j.val == 2 then entry_4_3.upper
  else if j.val == 3 then entry_4_4.upper
  else if j.val == 4 then entry_4_5.upper
  else if j.val == 5 then entry_4_6.upper
  else if j.val == 6 then entry_4_7.upper
  else if j.val == 7 then entry_4_8.upper
  else if j.val == 8 then entry_4_9.upper
  else if j.val == 9 then entry_4_10.upper
  else if j.val == 10 then entry_4_11.upper
  else if j.val == 11 then entry_4_12.upper
  else if j.val == 12 then entry_4_13.upper
  else if j.val == 13 then entry_4_14.upper
  else if j.val == 14 then entry_4_15.upper
  else if j.val == 15 then entry_4_16.upper
  else if j.val == 16 then entry_4_17.upper
  else if j.val == 17 then entry_4_18.upper
  else if j.val == 18 then entry_4_19.upper
  else if j.val == 19 then entry_4_20.upper
  else 0
def gupr_r_4 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_5_1.upper
  else if j.val == 1 then entry_5_2.upper
  else if j.val == 2 then entry_5_3.upper
  else if j.val == 3 then entry_5_4.upper
  else if j.val == 4 then entry_5_5.upper
  else if j.val == 5 then entry_5_6.upper
  else if j.val == 6 then entry_5_7.upper
  else if j.val == 7 then entry_5_8.upper
  else if j.val == 8 then entry_5_9.upper
  else if j.val == 9 then entry_5_10.upper
  else if j.val == 10 then entry_5_11.upper
  else if j.val == 11 then entry_5_12.upper
  else if j.val == 12 then entry_5_13.upper
  else if j.val == 13 then entry_5_14.upper
  else if j.val == 14 then entry_5_15.upper
  else if j.val == 15 then entry_5_16.upper
  else if j.val == 16 then entry_5_17.upper
  else if j.val == 17 then entry_5_18.upper
  else if j.val == 18 then entry_5_19.upper
  else if j.val == 19 then entry_5_20.upper
  else 0
def gupr_r_5 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_6_1.upper
  else if j.val == 1 then entry_6_2.upper
  else if j.val == 2 then entry_6_3.upper
  else if j.val == 3 then entry_6_4.upper
  else if j.val == 4 then entry_6_5.upper
  else if j.val == 5 then entry_6_6.upper
  else if j.val == 6 then entry_6_7.upper
  else if j.val == 7 then entry_6_8.upper
  else if j.val == 8 then entry_6_9.upper
  else if j.val == 9 then entry_6_10.upper
  else if j.val == 10 then entry_6_11.upper
  else if j.val == 11 then entry_6_12.upper
  else if j.val == 12 then entry_6_13.upper
  else if j.val == 13 then entry_6_14.upper
  else if j.val == 14 then entry_6_15.upper
  else if j.val == 15 then entry_6_16.upper
  else if j.val == 16 then entry_6_17.upper
  else if j.val == 17 then entry_6_18.upper
  else if j.val == 18 then entry_6_19.upper
  else if j.val == 19 then entry_6_20.upper
  else 0
def gupr_r_6 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_7_1.upper
  else if j.val == 1 then entry_7_2.upper
  else if j.val == 2 then entry_7_3.upper
  else if j.val == 3 then entry_7_4.upper
  else if j.val == 4 then entry_7_5.upper
  else if j.val == 5 then entry_7_6.upper
  else if j.val == 6 then entry_7_7.upper
  else if j.val == 7 then entry_7_8.upper
  else if j.val == 8 then entry_7_9.upper
  else if j.val == 9 then entry_7_10.upper
  else if j.val == 10 then entry_7_11.upper
  else if j.val == 11 then entry_7_12.upper
  else if j.val == 12 then entry_7_13.upper
  else if j.val == 13 then entry_7_14.upper
  else if j.val == 14 then entry_7_15.upper
  else if j.val == 15 then entry_7_16.upper
  else if j.val == 16 then entry_7_17.upper
  else if j.val == 17 then entry_7_18.upper
  else if j.val == 18 then entry_7_19.upper
  else if j.val == 19 then entry_7_20.upper
  else 0
def gupr_r_7 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_8_1.upper
  else if j.val == 1 then entry_8_2.upper
  else if j.val == 2 then entry_8_3.upper
  else if j.val == 3 then entry_8_4.upper
  else if j.val == 4 then entry_8_5.upper
  else if j.val == 5 then entry_8_6.upper
  else if j.val == 6 then entry_8_7.upper
  else if j.val == 7 then entry_8_8.upper
  else if j.val == 8 then entry_8_9.upper
  else if j.val == 9 then entry_8_10.upper
  else if j.val == 10 then entry_8_11.upper
  else if j.val == 11 then entry_8_12.upper
  else if j.val == 12 then entry_8_13.upper
  else if j.val == 13 then entry_8_14.upper
  else if j.val == 14 then entry_8_15.upper
  else if j.val == 15 then entry_8_16.upper
  else if j.val == 16 then entry_8_17.upper
  else if j.val == 17 then entry_8_18.upper
  else if j.val == 18 then entry_8_19.upper
  else if j.val == 19 then entry_8_20.upper
  else 0
def gupr_r_8 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_9_1.upper
  else if j.val == 1 then entry_9_2.upper
  else if j.val == 2 then entry_9_3.upper
  else if j.val == 3 then entry_9_4.upper
  else if j.val == 4 then entry_9_5.upper
  else if j.val == 5 then entry_9_6.upper
  else if j.val == 6 then entry_9_7.upper
  else if j.val == 7 then entry_9_8.upper
  else if j.val == 8 then entry_9_9.upper
  else if j.val == 9 then entry_9_10.upper
  else if j.val == 10 then entry_9_11.upper
  else if j.val == 11 then entry_9_12.upper
  else if j.val == 12 then entry_9_13.upper
  else if j.val == 13 then entry_9_14.upper
  else if j.val == 14 then entry_9_15.upper
  else if j.val == 15 then entry_9_16.upper
  else if j.val == 16 then entry_9_17.upper
  else if j.val == 17 then entry_9_18.upper
  else if j.val == 18 then entry_9_19.upper
  else if j.val == 19 then entry_9_20.upper
  else 0
def gupr_r_9 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_10_1.upper
  else if j.val == 1 then entry_10_2.upper
  else if j.val == 2 then entry_10_3.upper
  else if j.val == 3 then entry_10_4.upper
  else if j.val == 4 then entry_10_5.upper
  else if j.val == 5 then entry_10_6.upper
  else if j.val == 6 then entry_10_7.upper
  else if j.val == 7 then entry_10_8.upper
  else if j.val == 8 then entry_10_9.upper
  else if j.val == 9 then entry_10_10.upper
  else if j.val == 10 then entry_10_11.upper
  else if j.val == 11 then entry_10_12.upper
  else if j.val == 12 then entry_10_13.upper
  else if j.val == 13 then entry_10_14.upper
  else if j.val == 14 then entry_10_15.upper
  else if j.val == 15 then entry_10_16.upper
  else if j.val == 16 then entry_10_17.upper
  else if j.val == 17 then entry_10_18.upper
  else if j.val == 18 then entry_10_19.upper
  else if j.val == 19 then entry_10_20.upper
  else 0
def gupr_r_10 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_11_1.upper
  else if j.val == 1 then entry_11_2.upper
  else if j.val == 2 then entry_11_3.upper
  else if j.val == 3 then entry_11_4.upper
  else if j.val == 4 then entry_11_5.upper
  else if j.val == 5 then entry_11_6.upper
  else if j.val == 6 then entry_11_7.upper
  else if j.val == 7 then entry_11_8.upper
  else if j.val == 8 then entry_11_9.upper
  else if j.val == 9 then entry_11_10.upper
  else if j.val == 10 then entry_11_11.upper
  else if j.val == 11 then entry_11_12.upper
  else if j.val == 12 then entry_11_13.upper
  else if j.val == 13 then entry_11_14.upper
  else if j.val == 14 then entry_11_15.upper
  else if j.val == 15 then entry_11_16.upper
  else if j.val == 16 then entry_11_17.upper
  else if j.val == 17 then entry_11_18.upper
  else if j.val == 18 then entry_11_19.upper
  else if j.val == 19 then entry_11_20.upper
  else 0
def gupr_r_11 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_12_1.upper
  else if j.val == 1 then entry_12_2.upper
  else if j.val == 2 then entry_12_3.upper
  else if j.val == 3 then entry_12_4.upper
  else if j.val == 4 then entry_12_5.upper
  else if j.val == 5 then entry_12_6.upper
  else if j.val == 6 then entry_12_7.upper
  else if j.val == 7 then entry_12_8.upper
  else if j.val == 8 then entry_12_9.upper
  else if j.val == 9 then entry_12_10.upper
  else if j.val == 10 then entry_12_11.upper
  else if j.val == 11 then entry_12_12.upper
  else if j.val == 12 then entry_12_13.upper
  else if j.val == 13 then entry_12_14.upper
  else if j.val == 14 then entry_12_15.upper
  else if j.val == 15 then entry_12_16.upper
  else if j.val == 16 then entry_12_17.upper
  else if j.val == 17 then entry_12_18.upper
  else if j.val == 18 then entry_12_19.upper
  else if j.val == 19 then entry_12_20.upper
  else 0
def gupr_r_12 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_13_1.upper
  else if j.val == 1 then entry_13_2.upper
  else if j.val == 2 then entry_13_3.upper
  else if j.val == 3 then entry_13_4.upper
  else if j.val == 4 then entry_13_5.upper
  else if j.val == 5 then entry_13_6.upper
  else if j.val == 6 then entry_13_7.upper
  else if j.val == 7 then entry_13_8.upper
  else if j.val == 8 then entry_13_9.upper
  else if j.val == 9 then entry_13_10.upper
  else if j.val == 10 then entry_13_11.upper
  else if j.val == 11 then entry_13_12.upper
  else if j.val == 12 then entry_13_13.upper
  else if j.val == 13 then entry_13_14.upper
  else if j.val == 14 then entry_13_15.upper
  else if j.val == 15 then entry_13_16.upper
  else if j.val == 16 then entry_13_17.upper
  else if j.val == 17 then entry_13_18.upper
  else if j.val == 18 then entry_13_19.upper
  else if j.val == 19 then entry_13_20.upper
  else 0
def gupr_r_13 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_14_1.upper
  else if j.val == 1 then entry_14_2.upper
  else if j.val == 2 then entry_14_3.upper
  else if j.val == 3 then entry_14_4.upper
  else if j.val == 4 then entry_14_5.upper
  else if j.val == 5 then entry_14_6.upper
  else if j.val == 6 then entry_14_7.upper
  else if j.val == 7 then entry_14_8.upper
  else if j.val == 8 then entry_14_9.upper
  else if j.val == 9 then entry_14_10.upper
  else if j.val == 10 then entry_14_11.upper
  else if j.val == 11 then entry_14_12.upper
  else if j.val == 12 then entry_14_13.upper
  else if j.val == 13 then entry_14_14.upper
  else if j.val == 14 then entry_14_15.upper
  else if j.val == 15 then entry_14_16.upper
  else if j.val == 16 then entry_14_17.upper
  else if j.val == 17 then entry_14_18.upper
  else if j.val == 18 then entry_14_19.upper
  else if j.val == 19 then entry_14_20.upper
  else 0
def gupr_r_14 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_15_1.upper
  else if j.val == 1 then entry_15_2.upper
  else if j.val == 2 then entry_15_3.upper
  else if j.val == 3 then entry_15_4.upper
  else if j.val == 4 then entry_15_5.upper
  else if j.val == 5 then entry_15_6.upper
  else if j.val == 6 then entry_15_7.upper
  else if j.val == 7 then entry_15_8.upper
  else if j.val == 8 then entry_15_9.upper
  else if j.val == 9 then entry_15_10.upper
  else if j.val == 10 then entry_15_11.upper
  else if j.val == 11 then entry_15_12.upper
  else if j.val == 12 then entry_15_13.upper
  else if j.val == 13 then entry_15_14.upper
  else if j.val == 14 then entry_15_15.upper
  else if j.val == 15 then entry_15_16.upper
  else if j.val == 16 then entry_15_17.upper
  else if j.val == 17 then entry_15_18.upper
  else if j.val == 18 then entry_15_19.upper
  else if j.val == 19 then entry_15_20.upper
  else 0
def gupr_r_15 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_16_1.upper
  else if j.val == 1 then entry_16_2.upper
  else if j.val == 2 then entry_16_3.upper
  else if j.val == 3 then entry_16_4.upper
  else if j.val == 4 then entry_16_5.upper
  else if j.val == 5 then entry_16_6.upper
  else if j.val == 6 then entry_16_7.upper
  else if j.val == 7 then entry_16_8.upper
  else if j.val == 8 then entry_16_9.upper
  else if j.val == 9 then entry_16_10.upper
  else if j.val == 10 then entry_16_11.upper
  else if j.val == 11 then entry_16_12.upper
  else if j.val == 12 then entry_16_13.upper
  else if j.val == 13 then entry_16_14.upper
  else if j.val == 14 then entry_16_15.upper
  else if j.val == 15 then entry_16_16.upper
  else if j.val == 16 then entry_16_17.upper
  else if j.val == 17 then entry_16_18.upper
  else if j.val == 18 then entry_16_19.upper
  else if j.val == 19 then entry_16_20.upper
  else 0
def gupr_r_16 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_17_1.upper
  else if j.val == 1 then entry_17_2.upper
  else if j.val == 2 then entry_17_3.upper
  else if j.val == 3 then entry_17_4.upper
  else if j.val == 4 then entry_17_5.upper
  else if j.val == 5 then entry_17_6.upper
  else if j.val == 6 then entry_17_7.upper
  else if j.val == 7 then entry_17_8.upper
  else if j.val == 8 then entry_17_9.upper
  else if j.val == 9 then entry_17_10.upper
  else if j.val == 10 then entry_17_11.upper
  else if j.val == 11 then entry_17_12.upper
  else if j.val == 12 then entry_17_13.upper
  else if j.val == 13 then entry_17_14.upper
  else if j.val == 14 then entry_17_15.upper
  else if j.val == 15 then entry_17_16.upper
  else if j.val == 16 then entry_17_17.upper
  else if j.val == 17 then entry_17_18.upper
  else if j.val == 18 then entry_17_19.upper
  else if j.val == 19 then entry_17_20.upper
  else 0
def gupr_r_17 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_18_1.upper
  else if j.val == 1 then entry_18_2.upper
  else if j.val == 2 then entry_18_3.upper
  else if j.val == 3 then entry_18_4.upper
  else if j.val == 4 then entry_18_5.upper
  else if j.val == 5 then entry_18_6.upper
  else if j.val == 6 then entry_18_7.upper
  else if j.val == 7 then entry_18_8.upper
  else if j.val == 8 then entry_18_9.upper
  else if j.val == 9 then entry_18_10.upper
  else if j.val == 10 then entry_18_11.upper
  else if j.val == 11 then entry_18_12.upper
  else if j.val == 12 then entry_18_13.upper
  else if j.val == 13 then entry_18_14.upper
  else if j.val == 14 then entry_18_15.upper
  else if j.val == 15 then entry_18_16.upper
  else if j.val == 16 then entry_18_17.upper
  else if j.val == 17 then entry_18_18.upper
  else if j.val == 18 then entry_18_19.upper
  else if j.val == 19 then entry_18_20.upper
  else 0
def gupr_r_18 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_19_1.upper
  else if j.val == 1 then entry_19_2.upper
  else if j.val == 2 then entry_19_3.upper
  else if j.val == 3 then entry_19_4.upper
  else if j.val == 4 then entry_19_5.upper
  else if j.val == 5 then entry_19_6.upper
  else if j.val == 6 then entry_19_7.upper
  else if j.val == 7 then entry_19_8.upper
  else if j.val == 8 then entry_19_9.upper
  else if j.val == 9 then entry_19_10.upper
  else if j.val == 10 then entry_19_11.upper
  else if j.val == 11 then entry_19_12.upper
  else if j.val == 12 then entry_19_13.upper
  else if j.val == 13 then entry_19_14.upper
  else if j.val == 14 then entry_19_15.upper
  else if j.val == 15 then entry_19_16.upper
  else if j.val == 16 then entry_19_17.upper
  else if j.val == 17 then entry_19_18.upper
  else if j.val == 18 then entry_19_19.upper
  else if j.val == 19 then entry_19_20.upper
  else 0
def gupr_r_19 (j : Fin 20) : ℚ :=
  if j.val == 0 then entry_20_1.upper
  else if j.val == 1 then entry_20_2.upper
  else if j.val == 2 then entry_20_3.upper
  else if j.val == 3 then entry_20_4.upper
  else if j.val == 4 then entry_20_5.upper
  else if j.val == 5 then entry_20_6.upper
  else if j.val == 6 then entry_20_7.upper
  else if j.val == 7 then entry_20_8.upper
  else if j.val == 8 then entry_20_9.upper
  else if j.val == 9 then entry_20_10.upper
  else if j.val == 10 then entry_20_11.upper
  else if j.val == 11 then entry_20_12.upper
  else if j.val == 12 then entry_20_13.upper
  else if j.val == 13 then entry_20_14.upper
  else if j.val == 14 then entry_20_15.upper
  else if j.val == 15 then entry_20_16.upper
  else if j.val == 16 then entry_20_17.upper
  else if j.val == 17 then entry_20_18.upper
  else if j.val == 18 then entry_20_19.upper
  else if j.val == 19 then entry_20_20.upper
  else 0

def gram_upper (i j : Fin 20) : ℚ :=
  if i.val == 0 then gupr_r_0 j
  else if i.val == 1 then gupr_r_1 j
  else if i.val == 2 then gupr_r_2 j
  else if i.val == 3 then gupr_r_3 j
  else if i.val == 4 then gupr_r_4 j
  else if i.val == 5 then gupr_r_5 j
  else if i.val == 6 then gupr_r_6 j
  else if i.val == 7 then gupr_r_7 j
  else if i.val == 8 then gupr_r_8 j
  else if i.val == 9 then gupr_r_9 j
  else if i.val == 10 then gupr_r_10 j
  else if i.val == 11 then gupr_r_11 j
  else if i.val == 12 then gupr_r_12 j
  else if i.val == 13 then gupr_r_13 j
  else if i.val == 14 then gupr_r_14 j
  else if i.val == 15 then gupr_r_15 j
  else if i.val == 16 then gupr_r_16 j
  else if i.val == 17 then gupr_r_17 j
  else if i.val == 18 then gupr_r_18 j
  else if i.val == 19 then gupr_r_19 j
  else 0

-- Rational intervals proved from the χ–ρ formula and Arb log/γ certificates.
def lin_lower : Fin 20 → ℚ :=
  RH.Certificates.Generated.ChiRhoBoundsN20.linearLower
def lin_upper : Fin 20 → ℚ :=
  RH.Certificates.Generated.ChiRhoBoundsN20.linearUpper
def const_lower : ℚ := 1 - (1/10000)
def const_upper : ℚ := 1 + (1/10000)

theorem toy_gram_certified (i j : Fin 20) :
  (gram_lower i j : ℝ) ≤ RH.Criteria.NymanBeurling.VasyuninGram.baezDuarteGramEntry (i.val + 1) (j.val + 1) ∧
  RH.Criteria.NymanBeurling.VasyuninGram.baezDuarteGramEntry (i.val + 1) (j.val + 1) ≤ (gram_upper i j : ℝ) := by
  fin_cases i <;> fin_cases j <;> simp [gram_lower, gram_upper]
  · exact entry_1_1.certified_interval
  · exact entry_1_2.certified_interval
  · exact entry_1_3.certified_interval
  · exact entry_1_4.certified_interval
  · exact entry_1_5.certified_interval
  · exact entry_1_6.certified_interval
  · exact entry_1_7.certified_interval
  · exact entry_1_8.certified_interval
  · exact entry_1_9.certified_interval
  · exact entry_1_10.certified_interval
  · exact entry_1_11.certified_interval
  · exact entry_1_12.certified_interval
  · exact entry_1_13.certified_interval
  · exact entry_1_14.certified_interval
  · exact entry_1_15.certified_interval
  · exact entry_1_16.certified_interval
  · exact entry_1_17.certified_interval
  · exact entry_1_18.certified_interval
  · exact entry_1_19.certified_interval
  · exact entry_1_20.certified_interval
  · exact entry_2_1.certified_interval
  · exact entry_2_2.certified_interval
  · exact entry_2_3.certified_interval
  · exact entry_2_4.certified_interval
  · exact entry_2_5.certified_interval
  · exact entry_2_6.certified_interval
  · exact entry_2_7.certified_interval
  · exact entry_2_8.certified_interval
  · exact entry_2_9.certified_interval
  · exact entry_2_10.certified_interval
  · exact entry_2_11.certified_interval
  · exact entry_2_12.certified_interval
  · exact entry_2_13.certified_interval
  · exact entry_2_14.certified_interval
  · exact entry_2_15.certified_interval
  · exact entry_2_16.certified_interval
  · exact entry_2_17.certified_interval
  · exact entry_2_18.certified_interval
  · exact entry_2_19.certified_interval
  · exact entry_2_20.certified_interval
  · exact entry_3_1.certified_interval
  · exact entry_3_2.certified_interval
  · exact entry_3_3.certified_interval
  · exact entry_3_4.certified_interval
  · exact entry_3_5.certified_interval
  · exact entry_3_6.certified_interval
  · exact entry_3_7.certified_interval
  · exact entry_3_8.certified_interval
  · exact entry_3_9.certified_interval
  · exact entry_3_10.certified_interval
  · exact entry_3_11.certified_interval
  · exact entry_3_12.certified_interval
  · exact entry_3_13.certified_interval
  · exact entry_3_14.certified_interval
  · exact entry_3_15.certified_interval
  · exact entry_3_16.certified_interval
  · exact entry_3_17.certified_interval
  · exact entry_3_18.certified_interval
  · exact entry_3_19.certified_interval
  · exact entry_3_20.certified_interval
  · exact entry_4_1.certified_interval
  · exact entry_4_2.certified_interval
  · exact entry_4_3.certified_interval
  · exact entry_4_4.certified_interval
  · exact entry_4_5.certified_interval
  · exact entry_4_6.certified_interval
  · exact entry_4_7.certified_interval
  · exact entry_4_8.certified_interval
  · exact entry_4_9.certified_interval
  · exact entry_4_10.certified_interval
  · exact entry_4_11.certified_interval
  · exact entry_4_12.certified_interval
  · exact entry_4_13.certified_interval
  · exact entry_4_14.certified_interval
  · exact entry_4_15.certified_interval
  · exact entry_4_16.certified_interval
  · exact entry_4_17.certified_interval
  · exact entry_4_18.certified_interval
  · exact entry_4_19.certified_interval
  · exact entry_4_20.certified_interval
  · exact entry_5_1.certified_interval
  · exact entry_5_2.certified_interval
  · exact entry_5_3.certified_interval
  · exact entry_5_4.certified_interval
  · exact entry_5_5.certified_interval
  · exact entry_5_6.certified_interval
  · exact entry_5_7.certified_interval
  · exact entry_5_8.certified_interval
  · exact entry_5_9.certified_interval
  · exact entry_5_10.certified_interval
  · exact entry_5_11.certified_interval
  · exact entry_5_12.certified_interval
  · exact entry_5_13.certified_interval
  · exact entry_5_14.certified_interval
  · exact entry_5_15.certified_interval
  · exact entry_5_16.certified_interval
  · exact entry_5_17.certified_interval
  · exact entry_5_18.certified_interval
  · exact entry_5_19.certified_interval
  · exact entry_5_20.certified_interval
  · exact entry_6_1.certified_interval
  · exact entry_6_2.certified_interval
  · exact entry_6_3.certified_interval
  · exact entry_6_4.certified_interval
  · exact entry_6_5.certified_interval
  · exact entry_6_6.certified_interval
  · exact entry_6_7.certified_interval
  · exact entry_6_8.certified_interval
  · exact entry_6_9.certified_interval
  · exact entry_6_10.certified_interval
  · exact entry_6_11.certified_interval
  · exact entry_6_12.certified_interval
  · exact entry_6_13.certified_interval
  · exact entry_6_14.certified_interval
  · exact entry_6_15.certified_interval
  · exact entry_6_16.certified_interval
  · exact entry_6_17.certified_interval
  · exact entry_6_18.certified_interval
  · exact entry_6_19.certified_interval
  · exact entry_6_20.certified_interval
  · exact entry_7_1.certified_interval
  · exact entry_7_2.certified_interval
  · exact entry_7_3.certified_interval
  · exact entry_7_4.certified_interval
  · exact entry_7_5.certified_interval
  · exact entry_7_6.certified_interval
  · exact entry_7_7.certified_interval
  · exact entry_7_8.certified_interval
  · exact entry_7_9.certified_interval
  · exact entry_7_10.certified_interval
  · exact entry_7_11.certified_interval
  · exact entry_7_12.certified_interval
  · exact entry_7_13.certified_interval
  · exact entry_7_14.certified_interval
  · exact entry_7_15.certified_interval
  · exact entry_7_16.certified_interval
  · exact entry_7_17.certified_interval
  · exact entry_7_18.certified_interval
  · exact entry_7_19.certified_interval
  · exact entry_7_20.certified_interval
  · exact entry_8_1.certified_interval
  · exact entry_8_2.certified_interval
  · exact entry_8_3.certified_interval
  · exact entry_8_4.certified_interval
  · exact entry_8_5.certified_interval
  · exact entry_8_6.certified_interval
  · exact entry_8_7.certified_interval
  · exact entry_8_8.certified_interval
  · exact entry_8_9.certified_interval
  · exact entry_8_10.certified_interval
  · exact entry_8_11.certified_interval
  · exact entry_8_12.certified_interval
  · exact entry_8_13.certified_interval
  · exact entry_8_14.certified_interval
  · exact entry_8_15.certified_interval
  · exact entry_8_16.certified_interval
  · exact entry_8_17.certified_interval
  · exact entry_8_18.certified_interval
  · exact entry_8_19.certified_interval
  · exact entry_8_20.certified_interval
  · exact entry_9_1.certified_interval
  · exact entry_9_2.certified_interval
  · exact entry_9_3.certified_interval
  · exact entry_9_4.certified_interval
  · exact entry_9_5.certified_interval
  · exact entry_9_6.certified_interval
  · exact entry_9_7.certified_interval
  · exact entry_9_8.certified_interval
  · exact entry_9_9.certified_interval
  · exact entry_9_10.certified_interval
  · exact entry_9_11.certified_interval
  · exact entry_9_12.certified_interval
  · exact entry_9_13.certified_interval
  · exact entry_9_14.certified_interval
  · exact entry_9_15.certified_interval
  · exact entry_9_16.certified_interval
  · exact entry_9_17.certified_interval
  · exact entry_9_18.certified_interval
  · exact entry_9_19.certified_interval
  · exact entry_9_20.certified_interval
  · exact entry_10_1.certified_interval
  · exact entry_10_2.certified_interval
  · exact entry_10_3.certified_interval
  · exact entry_10_4.certified_interval
  · exact entry_10_5.certified_interval
  · exact entry_10_6.certified_interval
  · exact entry_10_7.certified_interval
  · exact entry_10_8.certified_interval
  · exact entry_10_9.certified_interval
  · exact entry_10_10.certified_interval
  · exact entry_10_11.certified_interval
  · exact entry_10_12.certified_interval
  · exact entry_10_13.certified_interval
  · exact entry_10_14.certified_interval
  · exact entry_10_15.certified_interval
  · exact entry_10_16.certified_interval
  · exact entry_10_17.certified_interval
  · exact entry_10_18.certified_interval
  · exact entry_10_19.certified_interval
  · exact entry_10_20.certified_interval
  · exact entry_11_1.certified_interval
  · exact entry_11_2.certified_interval
  · exact entry_11_3.certified_interval
  · exact entry_11_4.certified_interval
  · exact entry_11_5.certified_interval
  · exact entry_11_6.certified_interval
  · exact entry_11_7.certified_interval
  · exact entry_11_8.certified_interval
  · exact entry_11_9.certified_interval
  · exact entry_11_10.certified_interval
  · exact entry_11_11.certified_interval
  · exact entry_11_12.certified_interval
  · exact entry_11_13.certified_interval
  · exact entry_11_14.certified_interval
  · exact entry_11_15.certified_interval
  · exact entry_11_16.certified_interval
  · exact entry_11_17.certified_interval
  · exact entry_11_18.certified_interval
  · exact entry_11_19.certified_interval
  · exact entry_11_20.certified_interval
  · exact entry_12_1.certified_interval
  · exact entry_12_2.certified_interval
  · exact entry_12_3.certified_interval
  · exact entry_12_4.certified_interval
  · exact entry_12_5.certified_interval
  · exact entry_12_6.certified_interval
  · exact entry_12_7.certified_interval
  · exact entry_12_8.certified_interval
  · exact entry_12_9.certified_interval
  · exact entry_12_10.certified_interval
  · exact entry_12_11.certified_interval
  · exact entry_12_12.certified_interval
  · exact entry_12_13.certified_interval
  · exact entry_12_14.certified_interval
  · exact entry_12_15.certified_interval
  · exact entry_12_16.certified_interval
  · exact entry_12_17.certified_interval
  · exact entry_12_18.certified_interval
  · exact entry_12_19.certified_interval
  · exact entry_12_20.certified_interval
  · exact entry_13_1.certified_interval
  · exact entry_13_2.certified_interval
  · exact entry_13_3.certified_interval
  · exact entry_13_4.certified_interval
  · exact entry_13_5.certified_interval
  · exact entry_13_6.certified_interval
  · exact entry_13_7.certified_interval
  · exact entry_13_8.certified_interval
  · exact entry_13_9.certified_interval
  · exact entry_13_10.certified_interval
  · exact entry_13_11.certified_interval
  · exact entry_13_12.certified_interval
  · exact entry_13_13.certified_interval
  · exact entry_13_14.certified_interval
  · exact entry_13_15.certified_interval
  · exact entry_13_16.certified_interval
  · exact entry_13_17.certified_interval
  · exact entry_13_18.certified_interval
  · exact entry_13_19.certified_interval
  · exact entry_13_20.certified_interval
  · exact entry_14_1.certified_interval
  · exact entry_14_2.certified_interval
  · exact entry_14_3.certified_interval
  · exact entry_14_4.certified_interval
  · exact entry_14_5.certified_interval
  · exact entry_14_6.certified_interval
  · exact entry_14_7.certified_interval
  · exact entry_14_8.certified_interval
  · exact entry_14_9.certified_interval
  · exact entry_14_10.certified_interval
  · exact entry_14_11.certified_interval
  · exact entry_14_12.certified_interval
  · exact entry_14_13.certified_interval
  · exact entry_14_14.certified_interval
  · exact entry_14_15.certified_interval
  · exact entry_14_16.certified_interval
  · exact entry_14_17.certified_interval
  · exact entry_14_18.certified_interval
  · exact entry_14_19.certified_interval
  · exact entry_14_20.certified_interval
  · exact entry_15_1.certified_interval
  · exact entry_15_2.certified_interval
  · exact entry_15_3.certified_interval
  · exact entry_15_4.certified_interval
  · exact entry_15_5.certified_interval
  · exact entry_15_6.certified_interval
  · exact entry_15_7.certified_interval
  · exact entry_15_8.certified_interval
  · exact entry_15_9.certified_interval
  · exact entry_15_10.certified_interval
  · exact entry_15_11.certified_interval
  · exact entry_15_12.certified_interval
  · exact entry_15_13.certified_interval
  · exact entry_15_14.certified_interval
  · exact entry_15_15.certified_interval
  · exact entry_15_16.certified_interval
  · exact entry_15_17.certified_interval
  · exact entry_15_18.certified_interval
  · exact entry_15_19.certified_interval
  · exact entry_15_20.certified_interval
  · exact entry_16_1.certified_interval
  · exact entry_16_2.certified_interval
  · exact entry_16_3.certified_interval
  · exact entry_16_4.certified_interval
  · exact entry_16_5.certified_interval
  · exact entry_16_6.certified_interval
  · exact entry_16_7.certified_interval
  · exact entry_16_8.certified_interval
  · exact entry_16_9.certified_interval
  · exact entry_16_10.certified_interval
  · exact entry_16_11.certified_interval
  · exact entry_16_12.certified_interval
  · exact entry_16_13.certified_interval
  · exact entry_16_14.certified_interval
  · exact entry_16_15.certified_interval
  · exact entry_16_16.certified_interval
  · exact entry_16_17.certified_interval
  · exact entry_16_18.certified_interval
  · exact entry_16_19.certified_interval
  · exact entry_16_20.certified_interval
  · exact entry_17_1.certified_interval
  · exact entry_17_2.certified_interval
  · exact entry_17_3.certified_interval
  · exact entry_17_4.certified_interval
  · exact entry_17_5.certified_interval
  · exact entry_17_6.certified_interval
  · exact entry_17_7.certified_interval
  · exact entry_17_8.certified_interval
  · exact entry_17_9.certified_interval
  · exact entry_17_10.certified_interval
  · exact entry_17_11.certified_interval
  · exact entry_17_12.certified_interval
  · exact entry_17_13.certified_interval
  · exact entry_17_14.certified_interval
  · exact entry_17_15.certified_interval
  · exact entry_17_16.certified_interval
  · exact entry_17_17.certified_interval
  · exact entry_17_18.certified_interval
  · exact entry_17_19.certified_interval
  · exact entry_17_20.certified_interval
  · exact entry_18_1.certified_interval
  · exact entry_18_2.certified_interval
  · exact entry_18_3.certified_interval
  · exact entry_18_4.certified_interval
  · exact entry_18_5.certified_interval
  · exact entry_18_6.certified_interval
  · exact entry_18_7.certified_interval
  · exact entry_18_8.certified_interval
  · exact entry_18_9.certified_interval
  · exact entry_18_10.certified_interval
  · exact entry_18_11.certified_interval
  · exact entry_18_12.certified_interval
  · exact entry_18_13.certified_interval
  · exact entry_18_14.certified_interval
  · exact entry_18_15.certified_interval
  · exact entry_18_16.certified_interval
  · exact entry_18_17.certified_interval
  · exact entry_18_18.certified_interval
  · exact entry_18_19.certified_interval
  · exact entry_18_20.certified_interval
  · exact entry_19_1.certified_interval
  · exact entry_19_2.certified_interval
  · exact entry_19_3.certified_interval
  · exact entry_19_4.certified_interval
  · exact entry_19_5.certified_interval
  · exact entry_19_6.certified_interval
  · exact entry_19_7.certified_interval
  · exact entry_19_8.certified_interval
  · exact entry_19_9.certified_interval
  · exact entry_19_10.certified_interval
  · exact entry_19_11.certified_interval
  · exact entry_19_12.certified_interval
  · exact entry_19_13.certified_interval
  · exact entry_19_14.certified_interval
  · exact entry_19_15.certified_interval
  · exact entry_19_16.certified_interval
  · exact entry_19_17.certified_interval
  · exact entry_19_18.certified_interval
  · exact entry_19_19.certified_interval
  · exact entry_19_20.certified_interval
  · exact entry_20_1.certified_interval
  · exact entry_20_2.certified_interval
  · exact entry_20_3.certified_interval
  · exact entry_20_4.certified_interval
  · exact entry_20_5.certified_interval
  · exact entry_20_6.certified_interval
  · exact entry_20_7.certified_interval
  · exact entry_20_8.certified_interval
  · exact entry_20_9.certified_interval
  · exact entry_20_10.certified_interval
  · exact entry_20_11.certified_interval
  · exact entry_20_12.certified_interval
  · exact entry_20_13.certified_interval
  · exact entry_20_14.certified_interval
  · exact entry_20_15.certified_interval
  · exact entry_20_16.certified_interval
  · exact entry_20_17.certified_interval
  · exact entry_20_18.certified_interval
  · exact entry_20_19.certified_interval
  · exact entry_20_20.certified_interval

def Q_interval : BaezDuarteIntervalQuadraticModel 20 :=
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

private theorem ldl_product_apply (i j : Fin 20) :
    (L_val * Matrix.diagonal D_val * L_val.transpose) i j =
      ∑ k, L_val i k * D_val k * L_val j k := by
  have hdiag : Matrix.diagonal D_val * L_val.transpose =
      fun a b => D_val a * L_val b a := by
    ext a b
    change Matrix.diagonal D_val a ⬝ᵥ (fun x => L_val.transpose x b) = _
    rw [diagonal_dotProduct]
    rfl
  rw [mul_assoc, hdiag]
  simp only [Matrix.mul_apply, mul_assoc]

local macro "prove_ldl_row" js:ident,* : tactic =>
  `(tactic|
    (rw [ldl_product_apply]
     fin_cases $[$js],* <;>
       simp only [M_reg, M_reg_fn,
         mreg_r_0, mreg_r_1, mreg_r_2, mreg_r_3, mreg_r_4,
         mreg_r_5, mreg_r_6, mreg_r_7, mreg_r_8, mreg_r_9,
         mreg_r_10, mreg_r_11, mreg_r_12, mreg_r_13, mreg_r_14,
         mreg_r_15, mreg_r_16, mreg_r_17, mreg_r_18, mreg_r_19,
         L_val, L_val_fn,
         lval_r_0, lval_r_1, lval_r_2, lval_r_3, lval_r_4,
         lval_r_5, lval_r_6, lval_r_7, lval_r_8, lval_r_9,
         lval_r_10, lval_r_11, lval_r_12, lval_r_13, lval_r_14,
         lval_r_15, lval_r_16, lval_r_17, lval_r_18, lval_r_19,
         D_val, D_val_fn, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
       norm_num (config := { maxSteps := 1000000 })))

private theorem ldl_identity_row_0 (j : Fin 20) :
    M_reg ⟨0, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨0, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_1 (j : Fin 20) :
    M_reg ⟨1, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨1, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_2 (j : Fin 20) :
    M_reg ⟨2, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨2, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_3 (j : Fin 20) :
    M_reg ⟨3, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨3, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_4 (j : Fin 20) :
    M_reg ⟨4, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨4, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_5 (j : Fin 20) :
    M_reg ⟨5, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨5, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_6 (j : Fin 20) :
    M_reg ⟨6, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨6, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_7 (j : Fin 20) :
    M_reg ⟨7, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨7, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_8 (j : Fin 20) :
    M_reg ⟨8, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨8, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_9 (j : Fin 20) :
    M_reg ⟨9, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨9, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_10 (j : Fin 20) :
    M_reg ⟨10, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨10, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_11 (j : Fin 20) :
    M_reg ⟨11, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨11, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_12 (j : Fin 20) :
    M_reg ⟨12, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨12, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_13 (j : Fin 20) :
    M_reg ⟨13, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨13, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_14 (j : Fin 20) :
    M_reg ⟨14, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨14, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_15 (j : Fin 20) :
    M_reg ⟨15, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨15, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_16 (j : Fin 20) :
    M_reg ⟨16, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨16, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_17 (j : Fin 20) :
    M_reg ⟨17, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨17, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_18 (j : Fin 20) :
    M_reg ⟨18, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨18, by decide⟩ j := by
  prove_ldl_row j

private theorem ldl_identity_row_19 (j : Fin 20) :
    M_reg ⟨19, by decide⟩ j =
      (L_val * Matrix.diagonal D_val * L_val.transpose) ⟨19, by decide⟩ j := by
  prove_ldl_row j


def witnessN20 : RationalPSDWitness 20 :=
{
  M := M_reg
  L := L_val
  D := D_val
  diagonal_nonneg := by intro i; fin_cases i <;> simp [D_val, D_val_fn] <;> norm_num
  ldl_identity := by
    ext i j
    fin_cases i
    · exact ldl_identity_row_0 j
    · exact ldl_identity_row_1 j
    · exact ldl_identity_row_2 j
    · exact ldl_identity_row_3 j
    · exact ldl_identity_row_4 j
    · exact ldl_identity_row_5 j
    · exact ldl_identity_row_6 j
    · exact ldl_identity_row_7 j
    · exact ldl_identity_row_8 j
    · exact ldl_identity_row_9 j
    · exact ldl_identity_row_10 j
    · exact ldl_identity_row_11 j
    · exact ldl_identity_row_12 j
    · exact ldl_identity_row_13 j
    · exact ldl_identity_row_14 j
    · exact ldl_identity_row_15 j
    · exact ldl_identity_row_16 j
    · exact ldl_identity_row_17 j
    · exact ldl_identity_row_18 j
    · exact ldl_identity_row_19 j
}

-- M_orig removed: implicitly bounded by the Gram entry intervals
def regCertN20 : RegularizedPSDCertificate 20 :=
{
  originalMatrix := M_reg - ((1/10000) : ℚ) • 1
  epsilon := (1/10000)
  regularizedMatrix := M_reg
  regularized_eq := by simp
  epsilon_nonneg := by norm_num
  witness := witnessN20
  witness_matches := rfl
}

-- energyUpper is the sign-aware interval arithmetic upper bound on:
--   ||chi||^2 - 2*c^T*l + c^T*G*c  where c = coeff_fn, l_k = innerProductChiRho k
-- This bounds BaezDuarteDistance N via candidate_bounds_baez_duarte_distance
-- (pending baezDuarteL2Error_gram_expansion axiom)
def witnessEnergy : FiniteIntervalEnergyWitness 20 :=
{
  model := Q_interval
  coeffs := coeff_fn
  energyUpper := (240545380326309307260010054008082551126279501983377323863642569929484001989279364076310364792146643730398992950675629383093515764315980410984547384520895869140767904243494963563009676598539162279277172645205193952562968048319326557390097851370098221188680576457265061736844556791303545396013422534630936142137851009707994406003858428555877519856451058595816886113306831468128854301672791697847566609276918142475088885750276822050830532471123655732308208507165768414400923449455280351367341940937710070833809296584547913306378360046596760630501355052066738555040084318806419393973722458955654766100854750761289453592623296414442704638675386882335034737504252680922279569892049827392578313574316847508193471168436558922602728365559196460566189771456107071442244744796480300384057930928134692083486975317208066099540973168655782767371626969606935973777480577590955622786531292705509405213195663395783850860642650091095461260840636849938742841673296488574492309171/10943863847210182804007551587028860379198041173819694907720730512767641594182356508684971014258425893821034112989885186096183165732246372144432571835845229011948856379446971397878333494275708687212902956447959625352425849531647052588574072833240081832469232287472577168725778468236660691445702001341187262464093131321909766146293277238110419217639380348121632198305608815818096302467728020913265449832956659416491346396404290402292655979555285772932192059059595920447943273812582434193896971631979995897892256004551517238026085432221594417715129989169753801361527393610458452317252481024115823907455510988480471507811544498710131202840798551209924975542006216009328850005192015739986660676498989544495944033240058593379203568034426364364219654478343320989179533197188126385455220218458026881559813688871495332962314696468789719147645046508748677822891238823477101704535137799065415223406179110936681260608248832177014523462785674885077460969918988916900000000000)
  interval_energy_bound := True.intro
}


noncomputable def certN20 : FiniteApproximationCertificate :=
{
  N := 20
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
theorem N20_quadratic_le_energyUpper :
    ∑ h : Fin 20, ∑ k : Fin 20,
      (coeff_fn h : ℝ) * (coeff_fn k : ℝ) *
      RH.Criteria.NymanBeurling.VasyuninGram.baezDuarteGramEntry (h.val + 1) (k.val + 1)
    - 2 * ∑ k : Fin 20,
        (coeff_fn k : ℝ) * innerProductChiRho k.val
    + 1 ≤ (witnessEnergy.energyUpper : ℝ) := by
  have hbound := sign_aware_energy_bound (N := 20) coeff_fn
    (fun h k => RH.Criteria.NymanBeurling.VasyuninGram.baezDuarteGramEntry (h.val + 1) (k.val + 1))
    gram_lower gram_upper
    (fun k => innerProductChiRho k.val)
    lin_lower lin_upper
    (fun i j => (toy_gram_certified i j).1)
    (fun i j => (toy_gram_certified i j).2)
    (fun k =>
      (RH.Certificates.Generated.ChiRhoBoundsN20.innerProductChiRho_interval k).1)
    (fun k =>
      (RH.Certificates.Generated.ChiRhoBoundsN20.innerProductChiRho_interval k).2)
  have heq : signAwareQuadBoundQ coeff_fn gram_lower gram_upper +
             signAwareLinBoundQ coeff_fn lin_lower lin_upper + 1 =
             witnessEnergy.energyUpper := by
    simp only [signAwareQuadBoundQ, signAwareLinBoundQ,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp only [coeff_fn, gram_lower,
      glwr_r_0, glwr_r_1, glwr_r_2, glwr_r_3, glwr_r_4,
      glwr_r_5, glwr_r_6, glwr_r_7, glwr_r_8, glwr_r_9,
      glwr_r_10, glwr_r_11, glwr_r_12, glwr_r_13, glwr_r_14,
      glwr_r_15, glwr_r_16, glwr_r_17, glwr_r_18, glwr_r_19,
      gram_upper,
      gupr_r_0, gupr_r_1, gupr_r_2, gupr_r_3, gupr_r_4,
      gupr_r_5, gupr_r_6, gupr_r_7, gupr_r_8, gupr_r_9,
      gupr_r_10, gupr_r_11, gupr_r_12, gupr_r_13, gupr_r_14,
      gupr_r_15, gupr_r_16, gupr_r_17, gupr_r_18, gupr_r_19,
      lin_lower, lin_upper,
      RH.Certificates.Generated.ChiRhoBoundsN20.linearLower,
      RH.Certificates.Generated.ChiRhoBoundsN20.linearUpper,
      RH.Certificates.Generated.ChiRhoBoundsN20.linearCenter,
      witnessEnergy]
    simp only [
    entry_1_1, entry_1_2, entry_1_3, entry_1_4, entry_1_5,
    entry_1_6, entry_1_7, entry_1_8, entry_1_9, entry_1_10,
    entry_1_11, entry_1_12, entry_1_13, entry_1_14, entry_1_15,
    entry_1_16, entry_1_17, entry_1_18, entry_1_19, entry_1_20,
    entry_2_1, entry_2_2, entry_2_3, entry_2_4, entry_2_5,
    entry_2_6, entry_2_7, entry_2_8, entry_2_9, entry_2_10,
    entry_2_11, entry_2_12, entry_2_13, entry_2_14, entry_2_15,
    entry_2_16, entry_2_17, entry_2_18, entry_2_19, entry_2_20,
    entry_3_1, entry_3_2, entry_3_3, entry_3_4, entry_3_5,
    entry_3_6, entry_3_7, entry_3_8, entry_3_9, entry_3_10,
    entry_3_11, entry_3_12, entry_3_13, entry_3_14, entry_3_15,
    entry_3_16, entry_3_17, entry_3_18, entry_3_19, entry_3_20,
    entry_4_1, entry_4_2, entry_4_3, entry_4_4, entry_4_5,
    entry_4_6, entry_4_7, entry_4_8, entry_4_9, entry_4_10,
    entry_4_11, entry_4_12, entry_4_13, entry_4_14, entry_4_15,
    entry_4_16, entry_4_17, entry_4_18, entry_4_19, entry_4_20,
    entry_5_1, entry_5_2, entry_5_3, entry_5_4, entry_5_5,
    entry_5_6, entry_5_7, entry_5_8, entry_5_9, entry_5_10,
    entry_5_11, entry_5_12, entry_5_13, entry_5_14, entry_5_15,
    entry_5_16, entry_5_17, entry_5_18, entry_5_19, entry_5_20,
    entry_6_1, entry_6_2, entry_6_3, entry_6_4, entry_6_5,
    entry_6_6, entry_6_7, entry_6_8, entry_6_9, entry_6_10,
    entry_6_11, entry_6_12, entry_6_13, entry_6_14, entry_6_15,
    entry_6_16, entry_6_17, entry_6_18, entry_6_19, entry_6_20,
    entry_7_1, entry_7_2, entry_7_3, entry_7_4, entry_7_5,
    entry_7_6, entry_7_7, entry_7_8, entry_7_9, entry_7_10,
    entry_7_11, entry_7_12, entry_7_13, entry_7_14, entry_7_15,
    entry_7_16, entry_7_17, entry_7_18, entry_7_19, entry_7_20,
    entry_8_1, entry_8_2, entry_8_3, entry_8_4, entry_8_5,
    entry_8_6, entry_8_7, entry_8_8, entry_8_9, entry_8_10,
    entry_8_11, entry_8_12, entry_8_13, entry_8_14, entry_8_15,
    entry_8_16, entry_8_17, entry_8_18, entry_8_19, entry_8_20,
    entry_9_1, entry_9_2, entry_9_3, entry_9_4, entry_9_5,
    entry_9_6, entry_9_7, entry_9_8, entry_9_9, entry_9_10,
    entry_9_11, entry_9_12, entry_9_13, entry_9_14, entry_9_15,
    entry_9_16, entry_9_17, entry_9_18, entry_9_19, entry_9_20,
    entry_10_1, entry_10_2, entry_10_3, entry_10_4, entry_10_5,
    entry_10_6, entry_10_7, entry_10_8, entry_10_9, entry_10_10,
    entry_10_11, entry_10_12, entry_10_13, entry_10_14, entry_10_15,
    entry_10_16, entry_10_17, entry_10_18, entry_10_19, entry_10_20,
    entry_11_1, entry_11_2, entry_11_3, entry_11_4, entry_11_5,
    entry_11_6, entry_11_7, entry_11_8, entry_11_9, entry_11_10,
    entry_11_11, entry_11_12, entry_11_13, entry_11_14, entry_11_15,
    entry_11_16, entry_11_17, entry_11_18, entry_11_19, entry_11_20,
    entry_12_1, entry_12_2, entry_12_3, entry_12_4, entry_12_5,
    entry_12_6, entry_12_7, entry_12_8, entry_12_9, entry_12_10,
    entry_12_11, entry_12_12, entry_12_13, entry_12_14, entry_12_15,
    entry_12_16, entry_12_17, entry_12_18, entry_12_19, entry_12_20,
    entry_13_1, entry_13_2, entry_13_3, entry_13_4, entry_13_5,
    entry_13_6, entry_13_7, entry_13_8, entry_13_9, entry_13_10,
    entry_13_11, entry_13_12, entry_13_13, entry_13_14, entry_13_15,
    entry_13_16, entry_13_17, entry_13_18, entry_13_19, entry_13_20,
    entry_14_1, entry_14_2, entry_14_3, entry_14_4, entry_14_5,
    entry_14_6, entry_14_7, entry_14_8, entry_14_9, entry_14_10,
    entry_14_11, entry_14_12, entry_14_13, entry_14_14, entry_14_15,
    entry_14_16, entry_14_17, entry_14_18, entry_14_19, entry_14_20,
    entry_15_1, entry_15_2, entry_15_3, entry_15_4, entry_15_5,
    entry_15_6, entry_15_7, entry_15_8, entry_15_9, entry_15_10,
    entry_15_11, entry_15_12, entry_15_13, entry_15_14, entry_15_15,
    entry_15_16, entry_15_17, entry_15_18, entry_15_19, entry_15_20,
    entry_16_1, entry_16_2, entry_16_3, entry_16_4, entry_16_5,
    entry_16_6, entry_16_7, entry_16_8, entry_16_9, entry_16_10,
    entry_16_11, entry_16_12, entry_16_13, entry_16_14, entry_16_15,
    entry_16_16, entry_16_17, entry_16_18, entry_16_19, entry_16_20,
    entry_17_1, entry_17_2, entry_17_3, entry_17_4, entry_17_5,
    entry_17_6, entry_17_7, entry_17_8, entry_17_9, entry_17_10,
    entry_17_11, entry_17_12, entry_17_13, entry_17_14, entry_17_15,
    entry_17_16, entry_17_17, entry_17_18, entry_17_19, entry_17_20,
    entry_18_1, entry_18_2, entry_18_3, entry_18_4, entry_18_5,
    entry_18_6, entry_18_7, entry_18_8, entry_18_9, entry_18_10,
    entry_18_11, entry_18_12, entry_18_13, entry_18_14, entry_18_15,
    entry_18_16, entry_18_17, entry_18_18, entry_18_19, entry_18_20,
    entry_19_1, entry_19_2, entry_19_3, entry_19_4, entry_19_5,
    entry_19_6, entry_19_7, entry_19_8, entry_19_9, entry_19_10,
    entry_19_11, entry_19_12, entry_19_13, entry_19_14, entry_19_15,
    entry_19_16, entry_19_17, entry_19_18, entry_19_19, entry_19_20,
    entry_20_1, entry_20_2, entry_20_3, entry_20_4, entry_20_5,
    entry_20_6, entry_20_7, entry_20_8, entry_20_9, entry_20_10,
    entry_20_11, entry_20_12, entry_20_13, entry_20_14, entry_20_15,
    entry_20_16, entry_20_17, entry_20_18, entry_20_19, entry_20_20]
    norm_num (config := { maxSteps := 1000000 })
  calc ∑ h : Fin 20, ∑ k : Fin 20,
          (coeff_fn h : ℝ) * (coeff_fn k : ℝ) *
          RH.Criteria.NymanBeurling.VasyuninGram.baezDuarteGramEntry (h.val + 1) (k.val + 1)
        - 2 * ∑ k : Fin 20, (coeff_fn k : ℝ) * innerProductChiRho k.val + 1
      ≤ (signAwareQuadBoundQ coeff_fn gram_lower gram_upper : ℝ) +
        (signAwareLinBoundQ coeff_fn lin_lower lin_upper : ℝ) + 1 := hbound
    _ = (witnessEnergy.energyUpper : ℝ) := by exact_mod_cast heq

theorem baezDuarteDistance_N20_bound :
    RH.Criteria.NymanBeurling.BaezDuarte.BaezDuarteDistance 20 ≤
      (witnessEnergy.energyUpper : ℝ) := by
  apply (candidate_bounds_baez_duarte_distance
           (fun k => (coeff_fn k : ℝ))).trans
  rw [baezDuarteL2Error_gram_expansion]
  exact N20_quadratic_le_energyUpper

end RH.Certificates.Generated.NymanGramN20
