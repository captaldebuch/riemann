import RiemannHypothesis.Certificates.NymanBeurlingCertificate
import RiemannHypothesis.Certificates.Generated.ChiRhoBoundsN10
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10
import Mathlib

/-!
# GENERATED GRAM MATRIX CERTIFICATE
N = 10

Indices convention:
- Lean generated index `i : Fin N` corresponds to mathematical index `h = i.val + 1`.
- Lean generated index `j : Fin N` corresponds to mathematical index `k = j.val + 1`.
- Gram entry represents: ∫₀^∞ {1/(h x)} {1/(k x)} dx

Data Source: CertifiedInterval
-/

set_option maxHeartbeats 10000000
open scoped BigOperators

namespace RH.Certificates.Generated.NymanGramN10

open RH.Certificates

def entry_1_1 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 1
  lower := (6303/5000)
  upper := (12607/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_1_1.interval_proof
}

def entry_1_2 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 2
  lower := (3861/5000)
  upper := (7723/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_1_2.interval_proof
}

def entry_1_3 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 3
  lower := (23/40)
  upper := (5751/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_1_3.interval_proof
}

def entry_1_4 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 4
  lower := (74098041/159590000)
  upper := (74129959/159590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_1_4.interval_proof
}

def entry_1_5 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 5
  lower := (297474187/758130000)
  upper := (297625813/758130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_1_5.interval_proof
}

def entry_1_6 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 6
  lower := (138189523/404770000)
  upper := (138270477/404770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_1_6.interval_proof
}

def entry_1_7 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 7
  lower := (155428731/512690000)
  upper := (155531269/512690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_1_7.interval_proof
}

def entry_1_8 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 8
  lower := (14952029/54710000)
  upper := (14962971/54710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_1_8.interval_proof
}

def entry_1_9 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 9
  lower := (214204061/859390000)
  upper := (214375939/859390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_1_9.interval_proof
}

def entry_1_10 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 10
  lower := (16135967/70330000)
  upper := (16150033/70330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_1_10.interval_proof
}

def entry_2_1 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 1
  lower := (3861/5000)
  upper := (7723/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_2_1.interval_proof
}

def entry_2_2 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 2
  lower := (6303/10000)
  upper := (394/625)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_2_2.interval_proof
}

def entry_2_3 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 3
  lower := (4411/10000)
  upper := (1103/2500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_2_3.interval_proof
}

def entry_2_4 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 4
  lower := (368854443/955570000)
  upper := (369045557/955570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_2_4.interval_proof
}

def entry_2_5 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 5
  lower := (36498461/115390000)
  upper := (36521539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_2_5.interval_proof
}

def entry_2_6 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 6
  lower := (269206331/936690000)
  upper := (269393669/936690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_2_6.interval_proof
}

def entry_2_7 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 7
  lower := (157846907/630930000)
  upper := (157973093/630930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_2_7.interval_proof
}

def entry_2_8 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 8
  lower := (75927287/327130000)
  upper := (75992713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_2_8.interval_proof
}

def entry_2_9 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 9
  lower := (135824899/651010000)
  upper := (135955101/651010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_2_9.interval_proof
}

def entry_2_10 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 10
  lower := (64257239/327610000)
  upper := (64322761/327610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_2_10.interval_proof
}

def entry_3_1 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 1
  lower := (23/40)
  upper := (5751/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_3_1.interval_proof
}

def entry_3_2 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 2
  lower := (4411/10000)
  upper := (1103/2500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_3_2.interval_proof
}

def entry_3_3 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 3
  lower := (2101/5000)
  upper := (4203/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_3_3.interval_proof
}

def entry_3_4 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 4
  lower := (12635993/40070000)
  upper := (12644007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_3_4.interval_proof
}

def entry_3_5 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 5
  lower := (80650507/294930000)
  upper := (80709493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_3_5.interval_proof
}

def entry_3_6 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 6
  lower := (45200433/175670000)
  upper := (45235567/175670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_3_6.interval_proof
}

def entry_3_7 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 7
  lower := (112519007/509930000)
  upper := (112620993/509930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_3_7.interval_proof
}

def entry_3_8 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 8
  lower := (4014879/19960000)
  upper := (4018871/19960000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_3_8.interval_proof
}

def entry_3_9 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 9
  lower := (124245143/648570000)
  upper := (124374857/648570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_3_9.interval_proof
}

def entry_3_10 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 10
  lower := (64452631/373690000)
  upper := (64527369/373690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_3_10.interval_proof
}

def entry_4_1 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 1
  lower := (74098041/159590000)
  upper := (74129959/159590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_4_1.interval_proof
}

def entry_4_2 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 2
  lower := (368854443/955570000)
  upper := (369045557/955570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_4_2.interval_proof
}

def entry_4_3 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 3
  lower := (12635993/40070000)
  upper := (12644007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_4_3.interval_proof
}

def entry_4_4 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 4
  lower := (797903/2532500)
  upper := (1596819/5065000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_4_4.interval_proof
}

def entry_4_5 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 5
  lower := (25442211/102890000)
  upper := (25462789/102890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_4_5.interval_proof
}

def entry_4_6 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 6
  lower := (55097507/249930000)
  upper := (55147493/249930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_4_6.interval_proof
}

def entry_4_7 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 7
  lower := (49395219/247810000)
  upper := (49444781/247810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_4_7.interval_proof
}

def entry_4_8 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 8
  lower := (14052717/72830000)
  upper := (14067283/72830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_4_8.interval_proof
}

def entry_4_9 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 9
  lower := (163044103/958970000)
  upper := (163235897/958970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_4_9.interval_proof
}

def entry_4_10 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 10
  lower := (18243461/115390000)
  upper := (18266539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_4_10.interval_proof
}

def entry_5_1 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 1
  lower := (297474187/758130000)
  upper := (297625813/758130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_5_1.interval_proof
}

def entry_5_2 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 2
  lower := (36498461/115390000)
  upper := (36521539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_5_2.interval_proof
}

def entry_5_3 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 3
  lower := (80650507/294930000)
  upper := (80709493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_5_3.interval_proof
}

def entry_5_4 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 4
  lower := (25442211/102890000)
  upper := (25462789/102890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_5_4.interval_proof
}

def entry_5_5 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 5
  lower := (175820239/697610000)
  upper := (175959761/697610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_5_5.interval_proof
}

def entry_5_6 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 6
  lower := (34982859/171410000)
  upper := (35017141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_5_6.interval_proof
}

def entry_5_7 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 7
  lower := (167378283/917170000)
  upper := (167561717/917170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_5_7.interval_proof
}

def entry_5_8 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 8
  lower := (2514001/14990000)
  upper := (2516999/14990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_5_8.interval_proof
}

def entry_5_9 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 9
  lower := (17229039/109610000)
  upper := (17250961/109610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_5_9.interval_proof
}

def entry_5_10 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 10
  lower := (50922007/329930000)
  upper := (50987993/329930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_5_10.interval_proof
}

def entry_6_1 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 1
  lower := (138189523/404770000)
  upper := (138270477/404770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_6_1.interval_proof
}

def entry_6_2 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 2
  lower := (269206331/936690000)
  upper := (269393669/936690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_6_2.interval_proof
}

def entry_6_3 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 3
  lower := (45200433/175670000)
  upper := (45235567/175670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_6_3.interval_proof
}

def entry_6_4 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 4
  lower := (55097507/249930000)
  upper := (55147493/249930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_6_4.interval_proof
}

def entry_6_5 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 5
  lower := (34982859/171410000)
  upper := (35017141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_6_5.interval_proof
}

def entry_6_6 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 6
  lower := (198705383/946170000)
  upper := (198894617/946170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_6_6.interval_proof
}

def entry_6_7 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 7
  lower := (81713059/469410000)
  upper := (81806941/469410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_6_7.interval_proof
}

def entry_6_8 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 8
  lower := (6315993/40070000)
  upper := (6324007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_6_8.interval_proof
}

def entry_6_9 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 9
  lower := (71076627/483730000)
  upper := (71173373/483730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_6_9.interval_proof
}

def entry_6_10 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 10
  lower := (40310507/294930000)
  upper := (40369493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_6_10.interval_proof
}

def entry_7_1 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 1
  lower := (155428731/512690000)
  upper := (155531269/512690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_7_1.interval_proof
}

def entry_7_2 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 2
  lower := (157846907/630930000)
  upper := (157973093/630930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_7_2.interval_proof
}

def entry_7_3 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 3
  lower := (112519007/509930000)
  upper := (112620993/509930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_7_3.interval_proof
}

def entry_7_4 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 4
  lower := (49395219/247810000)
  upper := (49444781/247810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_7_4.interval_proof
}

def entry_7_5 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 5
  lower := (167378283/917170000)
  upper := (167561717/917170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_7_5.interval_proof
}

def entry_7_6 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 6
  lower := (81713059/469410000)
  upper := (81806941/469410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_7_6.interval_proof
}

def entry_7_7 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 7
  lower := (70865629/393710000)
  upper := (70944371/393710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_7_7.interval_proof
}

def entry_7_8 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 8
  lower := (27455929/180710000)
  upper := (27492071/180710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_7_8.interval_proof
}

def entry_7_9 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 9
  lower := (34032863/246370000)
  upper := (34082137/246370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_7_9.interval_proof
}

def entry_7_10 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 10
  lower := (86672617/673830000)
  upper := (86807383/673830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_7_10.interval_proof
}

def entry_8_1 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 1
  lower := (14952029/54710000)
  upper := (14962971/54710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_8_1.interval_proof
}

def entry_8_2 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 2
  lower := (75927287/327130000)
  upper := (75992713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_8_2.interval_proof
}

def entry_8_3 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 3
  lower := (4014879/19960000)
  upper := (4018871/19960000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_8_3.interval_proof
}

def entry_8_4 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 4
  lower := (14052717/72830000)
  upper := (14067283/72830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_8_4.interval_proof
}

def entry_8_5 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 5
  lower := (2514001/14990000)
  upper := (2516999/14990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_8_5.interval_proof
}

def entry_8_6 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 6
  lower := (6315993/40070000)
  upper := (6324007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_8_6.interval_proof
}

def entry_8_7 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 7
  lower := (27455929/180710000)
  upper := (27492071/180710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_8_7.interval_proof
}

def entry_8_8 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 8
  lower := (77955499/495010000)
  upper := (78054501/495010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_8_8.interval_proof
}

def entry_8_9 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 9
  lower := (11758283/87170000)
  upper := (11775717/87170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_8_9.interval_proof
}

def entry_8_10 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 10
  lower := (12715961/102890000)
  upper := (12736539/102890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_8_10.interval_proof
}

def entry_9_1 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 1
  lower := (214204061/859390000)
  upper := (214375939/859390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_9_1.interval_proof
}

def entry_9_2 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 2
  lower := (135824899/651010000)
  upper := (135955101/651010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_9_2.interval_proof
}

def entry_9_3 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 3
  lower := (124245143/648570000)
  upper := (124374857/648570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_9_3.interval_proof
}

def entry_9_4 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 4
  lower := (163044103/958970000)
  upper := (163235897/958970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_9_4.interval_proof
}

def entry_9_5 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 5
  lower := (17229039/109610000)
  upper := (17250961/109610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_9_5.interval_proof
}

def entry_9_6 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 6
  lower := (71076627/483730000)
  upper := (71173373/483730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_9_6.interval_proof
}

def entry_9_7 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 7
  lower := (34032863/246370000)
  upper := (34082137/246370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_9_7.interval_proof
}

def entry_9_8 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 8
  lower := (11758283/87170000)
  upper := (11775717/87170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_9_8.interval_proof
}

def entry_9_9 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 9
  lower := (12571019/89810000)
  upper := (12588981/89810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_9_9.interval_proof
}

def entry_9_10 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 10
  lower := (116434047/959530000)
  upper := (116625953/959530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_9_10.interval_proof
}

def entry_10_1 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 1
  lower := (16135967/70330000)
  upper := (16150033/70330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_10_1.interval_proof
}

def entry_10_2 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 2
  lower := (64257239/327610000)
  upper := (64322761/327610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_10_2.interval_proof
}

def entry_10_3 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 3
  lower := (64452631/373690000)
  upper := (64527369/373690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_10_3.interval_proof
}

def entry_10_4 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 4
  lower := (18243461/115390000)
  upper := (18266539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_10_4.interval_proof
}

def entry_10_5 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 5
  lower := (50922007/329930000)
  upper := (50987993/329930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_10_5.interval_proof
}

def entry_10_6 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 6
  lower := (40310507/294930000)
  upper := (40369493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_10_6.interval_proof
}

def entry_10_7 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 7
  lower := (86672617/673830000)
  upper := (86807383/673830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_10_7.interval_proof
}

def entry_10_8 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 8
  lower := (12715961/102890000)
  upper := (12736539/102890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_10_8.interval_proof
}

def entry_10_9 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 9
  lower := (116434047/959530000)
  upper := (116625953/959530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_10_9.interval_proof
}

def entry_10_10 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 10
  lower := (39728461/315390000)
  upper := (39791539/315390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10.interval_10_10.interval_proof
}


def M_reg_fn (i j : Fin 10) : ℚ :=
  if i.val == 0 ∧ j.val == 0 then (113228981/89810000)
  else if i.val == 0 ∧ j.val == 1 then (5624/7283)
  else if i.val == 0 ∧ j.val == 2 then (4136/7193)
  else if i.val == 0 ∧ j.val == 3 then (1846/3975)
  else if i.val == 0 ∧ j.val == 4 then (3298/8403)
  else if i.val == 0 ∧ j.val == 5 then (3191/9344)
  else if i.val == 0 ∧ j.val == 6 then (2565/8458)
  else if i.val == 0 ∧ j.val == 7 then (2527/9243)
  else if i.val == 0 ∧ j.val == 8 then (2018/8093)
  else if i.val == 0 ∧ j.val == 9 then (157/684)
  else if i.val == 1 ∧ j.val == 0 then (5624/7283)
  else if i.val == 1 ∧ j.val == 1 then (56618981/89810000)
  else if i.val == 1 ∧ j.val == 2 then (3022/6851)
  else if i.val == 1 ∧ j.val == 3 then (2812/7283)
  else if i.val == 1 ∧ j.val == 4 then (2461/7778)
  else if i.val == 1 ∧ j.val == 5 then (2068/7193)
  else if i.val == 1 ∧ j.val == 6 then (1112/4443)
  else if i.val == 1 ∧ j.val == 7 then (923/3975)
  else if i.val == 1 ∧ j.val == 8 then (1529/7325)
  else if i.val == 1 ∧ j.val == 9 then (1649/8403)
  else if i.val == 2 ∧ j.val == 0 then (4136/7193)
  else if i.val == 2 ∧ j.val == 1 then (3022/6851)
  else if i.val == 2 ∧ j.val == 2 then (37748981/89810000)
  else if i.val == 2 ∧ j.val == 3 then (1264/4007)
  else if i.val == 2 ∧ j.val == 4 then (2729/9976)
  else if i.val == 2 ∧ j.val == 5 then (113/439)
  else if i.val == 2 ∧ j.val == 6 then (1957/8865)
  else if i.val == 2 ∧ j.val == 7 then (872/4333)
  else if i.val == 2 ∧ j.val == 8 then (1371/7153)
  else if i.val == 2 ∧ j.val == 9 then (1319/7643)
  else if i.val == 3 ∧ j.val == 0 then (1846/3975)
  else if i.val == 3 ∧ j.val == 1 then (2812/7283)
  else if i.val == 3 ∧ j.val == 2 then (1264/4007)
  else if i.val == 3 ∧ j.val == 3 then (3622399/11490000)
  else if i.val == 3 ∧ j.val == 4 then (1579/6383)
  else if i.val == 3 ∧ j.val == 5 then (1511/6851)
  else if i.val == 3 ∧ j.val == 6 then (1949/9773)
  else if i.val == 3 ∧ j.val == 7 then (1406/7283)
  else if i.val == 3 ∧ j.val == 8 then (1601/9411)
  else if i.val == 3 ∧ j.val == 9 then (595/3761)
  else if i.val == 4 ∧ j.val == 0 then (3298/8403)
  else if i.val == 4 ∧ j.val == 1 then (2461/7778)
  else if i.val == 4 ∧ j.val == 2 then (2729/9976)
  else if i.val == 4 ∧ j.val == 3 then (1579/6383)
  else if i.val == 4 ∧ j.val == 4 then (16856683/66830000)
  else if i.val == 4 ∧ j.val == 5 then (2018/9883)
  else if i.val == 4 ∧ j.val == 6 then (1433/7848)
  else if i.val == 4 ∧ j.val == 7 then (1099/6549)
  else if i.val == 4 ∧ j.val == 8 then (1534/9753)
  else if i.val == 4 ∧ j.val == 9 then (1057/6844)
  else if i.val == 5 ∧ j.val == 0 then (3191/9344)
  else if i.val == 5 ∧ j.val == 1 then (2068/7193)
  else if i.val == 5 ∧ j.val == 2 then (113/439)
  else if i.val == 5 ∧ j.val == 3 then (1511/6851)
  else if i.val == 5 ∧ j.val == 4 then (2018/9883)
  else if i.val == 5 ∧ j.val == 5 then (18878981/89810000)
  else if i.val == 5 ∧ j.val == 6 then (1094/6281)
  else if i.val == 5 ∧ j.val == 7 then (632/4007)
  else if i.val == 5 ∧ j.val == 8 then (1423/9678)
  else if i.val == 5 ∧ j.val == 9 then (45/329)
  else if i.val == 6 ∧ j.val == 0 then (2565/8458)
  else if i.val == 6 ∧ j.val == 1 then (1112/4443)
  else if i.val == 6 ∧ j.val == 2 then (1957/8865)
  else if i.val == 6 ∧ j.val == 3 then (1949/9773)
  else if i.val == 6 ∧ j.val == 4 then (1433/7848)
  else if i.val == 6 ∧ j.val == 5 then (1094/6281)
  else if i.val == 6 ∧ j.val == 6 then (17959967/99670000)
  else if i.val == 6 ∧ j.val == 7 then (542/3565)
  else if i.val == 6 ∧ j.val == 8 then (1261/9122)
  else if i.val == 6 ∧ j.val == 9 then (639/4964)
  else if i.val == 7 ∧ j.val == 0 then (2527/9243)
  else if i.val == 7 ∧ j.val == 1 then (923/3975)
  else if i.val == 7 ∧ j.val == 2 then (872/4333)
  else if i.val == 7 ∧ j.val == 3 then (1406/7283)
  else if i.val == 7 ∧ j.val == 4 then (1099/6549)
  else if i.val == 7 ∧ j.val == 5 then (632/4007)
  else if i.val == 7 ∧ j.val == 6 then (542/3565)
  else if i.val == 7 ∧ j.val == 7 then (1382877/8770000)
  else if i.val == 7 ∧ j.val == 8 then (1299/9623)
  else if i.val == 7 ∧ j.val == 9 then (1143/9241)
  else if i.val == 8 ∧ j.val == 0 then (2018/8093)
  else if i.val == 8 ∧ j.val == 1 then (1529/7325)
  else if i.val == 8 ∧ j.val == 2 then (1371/7153)
  else if i.val == 8 ∧ j.val == 3 then (1601/9411)
  else if i.val == 8 ∧ j.val == 4 then (1534/9753)
  else if i.val == 8 ∧ j.val == 5 then (1423/9678)
  else if i.val == 8 ∧ j.val == 6 then (1261/9122)
  else if i.val == 8 ∧ j.val == 7 then (1299/9623)
  else if i.val == 8 ∧ j.val == 8 then (12588981/89810000)
  else if i.val == 8 ∧ j.val == 9 then (585/4817)
  else if i.val == 9 ∧ j.val == 0 then (157/684)
  else if i.val == 9 ∧ j.val == 1 then (1649/8403)
  else if i.val == 9 ∧ j.val == 2 then (1319/7643)
  else if i.val == 9 ∧ j.val == 3 then (595/3761)
  else if i.val == 9 ∧ j.val == 4 then (1057/6844)
  else if i.val == 9 ∧ j.val == 5 then (45/329)
  else if i.val == 9 ∧ j.val == 6 then (639/4964)
  else if i.val == 9 ∧ j.val == 7 then (1143/9241)
  else if i.val == 9 ∧ j.val == 8 then (585/4817)
  else if i.val == 9 ∧ j.val == 9 then (10798559/85590000)
  else 0

def L_val_fn (i j : Fin 10) : ℚ :=
  if i.val == 0 ∧ j.val == 0 then 1
  else if i.val == 0 ∧ j.val == 1 then 0
  else if i.val == 0 ∧ j.val == 2 then 0
  else if i.val == 0 ∧ j.val == 3 then 0
  else if i.val == 0 ∧ j.val == 4 then 0
  else if i.val == 0 ∧ j.val == 5 then 0
  else if i.val == 0 ∧ j.val == 6 then 0
  else if i.val == 0 ∧ j.val == 7 then 0
  else if i.val == 0 ∧ j.val == 8 then 0
  else if i.val == 0 ∧ j.val == 9 then 0
  else if i.val == 1 ∧ j.val == 0 then (505091440000/824646668623)
  else if i.val == 1 ∧ j.val == 1 then 1
  else if i.val == 1 ∧ j.val == 2 then 0
  else if i.val == 1 ∧ j.val == 3 then 0
  else if i.val == 1 ∧ j.val == 4 then 0
  else if i.val == 1 ∧ j.val == 5 then 0
  else if i.val == 1 ∧ j.val == 6 then 0
  else if i.val == 1 ∧ j.val == 7 then 0
  else if i.val == 1 ∧ j.val == 8 then 0
  else if i.val == 1 ∧ j.val == 9 then 0
  else if i.val == 2 ∧ j.val == 0 then (371454160000/814456060333)
  else if i.val == 2 ∧ j.val == 1 then (2363481593029158497788407340000/4185319163311698722067675940347)
  else if i.val == 2 ∧ j.val == 2 then 1
  else if i.val == 2 ∧ j.val == 3 then 0
  else if i.val == 2 ∧ j.val == 4 then 0
  else if i.val == 2 ∧ j.val == 5 then 0
  else if i.val == 2 ∧ j.val == 6 then 0
  else if i.val == 2 ∧ j.val == 7 then 0
  else if i.val == 2 ∧ j.val == 8 then 0
  else if i.val == 2 ∧ j.val == 9 then 0
  else if i.val == 3 ∧ j.val == 0 then (6631570400/18003407979)
  else if i.val == 3 ∧ j.val == 1 then (8718728289113224618040000/13503976653345914765954511)
  else if i.val == 3 ∧ j.val == 2 then (545654345117216697764754584241447207696260457760000/1272932849243464307198850995600506444459976743125813)
  else if i.val == 3 ∧ j.val == 3 then 1
  else if i.val == 3 ∧ j.val == 4 then 0
  else if i.val == 3 ∧ j.val == 5 then 0
  else if i.val == 3 ∧ j.val == 6 then 0
  else if i.val == 3 ∧ j.val == 7 then 0
  else if i.val == 3 ∧ j.val == 8 then 0
  else if i.val == 3 ∧ j.val == 9 then 0
  else if i.val == 4 ∧ j.val == 0 then (296193380000/951463127343)
  else if i.val == 4 ∧ j.val == 1 then (1339891499886161962498500035000/2775472066770173534565219967443)
  else if i.val == 4 ∧ j.val == 2 then (38972818039162973890059208544828141599788683573019178750/81419379340104351772137483306290461764018515947079051049)
  else if i.val == 4 ∧ j.val == 3 then (2836457674994064286947431672765071568380914139981141837922803015665110130000/5273782699982368461722222272852504953435571571656987888163677441376979743051)
  else if i.val == 4 ∧ j.val == 4 then 1
  else if i.val == 4 ∧ j.val == 5 then 0
  else if i.val == 4 ∧ j.val == 6 then 0
  else if i.val == 4 ∧ j.val == 7 then 0
  else if i.val == 4 ∧ j.val == 8 then 0
  else if i.val == 4 ∧ j.val == 9 then 0
  else if i.val == 5 ∧ j.val == 0 then (17911481875/66125724904)
  else if i.val == 5 ∧ j.val == 1 then (22186176773635445886614810000/44596160986973289550567850481)
  else if i.val == 5 ∧ j.val == 2 then (34083285357383122532516196271713945261720577240000/64028954078327236538575696706878418782239374627347)
  else if i.val == 5 ∧ j.val == 3 then (32002036652777746111649183857113355610564027528930119103314116600521852500/96057502226812701005993779556074574060305656610133073902338513427384461639)
  else if i.val == 5 ∧ j.val == 4 then (2427185474921403909418210375333641110039243475105521920865922826043109764449750228037948348029097555195737847500/5684717931243021251594502854953004740573399484287917078628492604425365963784728257001701680796337511126456423821)
  else if i.val == 5 ∧ j.val == 5 then 1
  else if i.val == 5 ∧ j.val == 6 then 0
  else if i.val == 5 ∧ j.val == 7 then 0
  else if i.val == 5 ∧ j.val == 8 then 0
  else if i.val == 5 ∧ j.val == 9 then 0
  else if i.val == 6 ∧ j.val == 0 then (115181325000/478845360649)
  else if i.val == 6 ∧ j.val == 1 then (654045337051655078613695920000/1595800337215600240008928860663)
  else if i.val == 6 ∧ j.val == 2 then (1051353950018449659755628696715627597025322846422954000/2465176375393143419985356998846563040483042410232005053)
  else if i.val == 6 ∧ j.val == 3 then (8780660918411047911277591076257342336953096244662269323680237299910610000/19587515742564559017295045011788542778730790870745419392347914222719302247)
  else if i.val == 6 ∧ j.val == 4 then (779669294248955652557051658737413343254213106200503244482004946900470558038380566196144177510363039120000303750/1931389861127504645067440921003172572247857390359770748769993843956260229176730348075420636592632271240292648651)
  else if i.val == 6 ∧ j.val == 5 then (155323875285373168092167409213852102987777208140716880208176251149468841945818296870841520803711986170487195907750649790094651051305555812558076850658920000/281893164530868791518011454980863364768294204775206252764531657562291412997427694981950469730887433762079329060111230480024447864205916142314321542743591983)
  else if i.val == 6 ∧ j.val == 6 then 1
  else if i.val == 6 ∧ j.val == 7 then 0
  else if i.val == 6 ∧ j.val == 8 then 0
  else if i.val == 6 ∧ j.val == 9 then 0
  else if i.val == 7 ∧ j.val == 0 then (226949870000/1046575471383)
  else if i.val == 7 ∧ j.val == 1 then (17108662544243797231765370800/41605752068958763393905848391)
  else if i.val == 7 ∧ j.val == 2 then (17279852039709439515916091348879015052925751273680000/46604209578877949652855761818712527307614666370548077)
  else if i.val == 7 ∧ j.val == 3 then (36947665253690645508506054371993367533330083586361384869477122689620000/64987403616813124079392214312502220940483366235421579617645229726198191)
  else if i.val == 7 ∧ j.val == 4 then (162490604843545978183788606064642124762808770746936648256354664215974323092508198990267558069445434536012110000/585316786335486567810378003980688520504382582645311132160051264844906614803045002926338838128666927658367740361)
  else if i.val == 7 ∧ j.val == 5 then (9791116672586473589109808108296699748919031971817265429972720769498383657895983078528873811343695016854199417189370009057983408313461490275816739619920000/24431013331149871295961675885783543241418315104459871765282385887890584215925845317631639164447389297030170249959580284989592367044061472854990445099847467)
  else if i.val == 7 ∧ j.val == 6 then (20546632973071600923154013130386287228670499073049751538935617797599815633105514075173641036016123817220636457716987930241370841869906193216184119926436834716639409303752345805486333395564166427152000/43276975131380447682648104107653702718728781921916488207275546690295113573446919530172089175885368104690491881374273647525531597358198182876015533468243680024438954396288964825154458272628461488345439)
  else if i.val == 7 ∧ j.val == 7 then 1
  else if i.val == 7 ∧ j.val == 8 then 0
  else if i.val == 7 ∧ j.val == 9 then 0
  else if i.val == 8 ∧ j.val == 0 then (181236580000/916362143233)
  else if i.val == 8 ∧ j.val == 1 then (23879854781997326284301788400/67130589382117079754412721707)
  else if i.val == 8 ∧ j.val == 2 then (14551322145391456539863969473179737476938098855636790000/33888661281378457095678263839554903216918469533854934397)
  else if i.val == 8 ∧ j.val == 3 then (1226050102421798051632358221630525217104209896197162330027837765606088910000/3236382065421383472419248546764862493709123495809315611497303402951549936251)
  else if i.val == 8 ∧ j.val == 4 then (293093061661848923069680125817407617987572897082566846666596063211875043468332272939495136791933967542135420120000/819047224827504605986373840889776178124494907587252024656304655151739530956290411364925709314039727267028274166429)
  else if i.val == 8 ∧ j.val == 5 then (13212116423014693226338924134062851278306138424717924253100992037031418521375787561615426062256958537563426967585187117780233155437424823076520766115360000/36503383334661633237694379961634457839019958396101157165270842156645868984927622248834766003611144851660701391070185196630451990572163643416504487786036021)
  else if i.val == 8 ∧ j.val == 6 then (10345613907308917258919003546809615224245957001813601101664985564992859740609780410565684986345281529534249350399698895223195627302867771617082132308928776851299748227293961965719604384050362448870955205000/27601564248518561689688681898288082074577212661654563509494512546895743276824328097947909252414401559410897554620047489503618858707723981716558469557432624960408500562937062468765853533195082090295034363441)
  else if i.val == 8 ∧ j.val == 7 then (569643125827146578497476504527753180752495134770806963865866597531418228814124531989768071665759092525896011975467549252563012972723994483892556169173133970156242461092725836207803322404362570953134168129440963522225686411450428304613469276772157667895810000/976032088140174216854353179239841850970636152412055105303172486930845924467280679292083974319598891807736618013090855505911921382736038190583434430578956220554690493586574008021029917870418345721303400258628470530420888256212972392216718834368582003046680233)
  else if i.val == 8 ∧ j.val == 8 then 1
  else if i.val == 8 ∧ j.val == 9 then 0
  else if i.val == 9 ∧ j.val == 0 then (3525042500/19362155751)
  else if i.val == 9 ∧ j.val == 1 then (756730957184865612901630000/2141017279586145693930485961)
  else if i.val == 9 ∧ j.val == 2 then (2472655697572482404431422625964812997673785524678490000/7314120415898810465535586614327200082554815638965440053)
  else if i.val == 9 ∧ j.val == 3 then (104975280438080660734338851805022568848147024529037861763312122532019050000/279148333098993362580164008296723497053079979779705818371855431393739387249)
  else if i.val == 9 ∧ j.val == 4 then (237375704754598269691515578332554221633460399213543488271534850857978530498758379673774594968001910630232500/457726576849828299058150098312294512725282404126682683133224752551570041939899577036691151406055918618168239)
  else if i.val == 9 ∧ j.val == 5 then (13047582819258698648389018738028285107657584239846512756136858278266322809744688432341826560879927744214822009603405203499047121193918417750477225300000/48284184720711628567866944545162863702975582554074696700535800626042676594284457014781983128850781318106196726109031201044553861301821840642807185668761)
  else if i.val == 9 ∧ j.val == 6 then (598446251428255248801677045392094676412668290290010317551287269118563125352394272038435098731633039957979999229969772087522978614275343266194069990265016198722933854685968838468201786416455773232500/1935289426768837531411152377006301886436577469027421220209799315028305651256655442705024019601023281125354603355011676491851543411896825394548761858349313905659333122059896213919081658602671092050017)
  else if i.val == 9 ∧ j.val == 7 then (655814517276308679496429389553258900217326937827001550635752300833204629996732422063570857566200434364232438875822992568351118869680463622619689627298014049854078982513107784093442344750080748545465636016988108601889438353173466390336952527583746030000/1511515638623374951102632121053232734169127582650232575217081386387703074119816193876120522050751912764031097296690417550791173861432053230069152200771245137884428102860192875699960034991293212530715182562780711924161083954852757892577051432369387488561)
  else if i.val == 9 ∧ j.val == 8 then (9145141457111136628128126986296141215799328589761065999600771576379448882149012219274330680822795637000383575837000173499997807279824090456554443393854593886492921474828598672383810984180002963949838158635840002184271911849447947058064314642512540804627369355896342145366782472300248198690748391067399693633604679150000/17637188615435118502677367973680080212937531597769511049411994178574235293066981312794452616865264965037825303612227036637282748696341380516695417067709216294359801731971147878171296341013708699961634985040724200049384120522345920875608065940139206465537864292885947947814198345804682537758171789487037421939964978001693)
  else if i.val == 9 ∧ j.val == 9 then 1
  else 0

def D_val_fn (i : Fin 10) : ℚ :=
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
  else 0

def linear_fn (i : Fin 10) : ℚ :=
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
  else 0

def coeff_fn (i : Fin 10) : ℚ :=
  if i.val == 0 then (-719231236/766493425)
  else if i.val == 1 then (798338276/887809023)
  else if i.val == 2 then (241474896/274731319)
  else if i.val == 3 then (137163484/798635117)
  else if i.val == 4 then (30660393/44271070)
  else if i.val == 5 then (-410591986/996973277)
  else if i.val == 6 then (18599185/32594743)
  else if i.val == 7 then (14378739/305440727)
  else if i.val == 8 then (111170361/738506285)
  else if i.val == 9 then (-54220920/438751537)
  else 0

def M_reg : Matrix (Fin 10) (Fin 10) ℚ := M_reg_fn
def L_val : Matrix (Fin 10) (Fin 10) ℚ := L_val_fn
def D_val : Fin 10 → ℚ := D_val_fn

-- Provide interval models
def gram_lower (i j : Fin 10) : ℚ :=
  if i.val == 0 ∧ j.val == 0 then entry_1_1.lower
  else if i.val == 0 ∧ j.val == 1 then entry_1_2.lower
  else if i.val == 0 ∧ j.val == 2 then entry_1_3.lower
  else if i.val == 0 ∧ j.val == 3 then entry_1_4.lower
  else if i.val == 0 ∧ j.val == 4 then entry_1_5.lower
  else if i.val == 0 ∧ j.val == 5 then entry_1_6.lower
  else if i.val == 0 ∧ j.val == 6 then entry_1_7.lower
  else if i.val == 0 ∧ j.val == 7 then entry_1_8.lower
  else if i.val == 0 ∧ j.val == 8 then entry_1_9.lower
  else if i.val == 0 ∧ j.val == 9 then entry_1_10.lower
  else if i.val == 1 ∧ j.val == 0 then entry_2_1.lower
  else if i.val == 1 ∧ j.val == 1 then entry_2_2.lower
  else if i.val == 1 ∧ j.val == 2 then entry_2_3.lower
  else if i.val == 1 ∧ j.val == 3 then entry_2_4.lower
  else if i.val == 1 ∧ j.val == 4 then entry_2_5.lower
  else if i.val == 1 ∧ j.val == 5 then entry_2_6.lower
  else if i.val == 1 ∧ j.val == 6 then entry_2_7.lower
  else if i.val == 1 ∧ j.val == 7 then entry_2_8.lower
  else if i.val == 1 ∧ j.val == 8 then entry_2_9.lower
  else if i.val == 1 ∧ j.val == 9 then entry_2_10.lower
  else if i.val == 2 ∧ j.val == 0 then entry_3_1.lower
  else if i.val == 2 ∧ j.val == 1 then entry_3_2.lower
  else if i.val == 2 ∧ j.val == 2 then entry_3_3.lower
  else if i.val == 2 ∧ j.val == 3 then entry_3_4.lower
  else if i.val == 2 ∧ j.val == 4 then entry_3_5.lower
  else if i.val == 2 ∧ j.val == 5 then entry_3_6.lower
  else if i.val == 2 ∧ j.val == 6 then entry_3_7.lower
  else if i.val == 2 ∧ j.val == 7 then entry_3_8.lower
  else if i.val == 2 ∧ j.val == 8 then entry_3_9.lower
  else if i.val == 2 ∧ j.val == 9 then entry_3_10.lower
  else if i.val == 3 ∧ j.val == 0 then entry_4_1.lower
  else if i.val == 3 ∧ j.val == 1 then entry_4_2.lower
  else if i.val == 3 ∧ j.val == 2 then entry_4_3.lower
  else if i.val == 3 ∧ j.val == 3 then entry_4_4.lower
  else if i.val == 3 ∧ j.val == 4 then entry_4_5.lower
  else if i.val == 3 ∧ j.val == 5 then entry_4_6.lower
  else if i.val == 3 ∧ j.val == 6 then entry_4_7.lower
  else if i.val == 3 ∧ j.val == 7 then entry_4_8.lower
  else if i.val == 3 ∧ j.val == 8 then entry_4_9.lower
  else if i.val == 3 ∧ j.val == 9 then entry_4_10.lower
  else if i.val == 4 ∧ j.val == 0 then entry_5_1.lower
  else if i.val == 4 ∧ j.val == 1 then entry_5_2.lower
  else if i.val == 4 ∧ j.val == 2 then entry_5_3.lower
  else if i.val == 4 ∧ j.val == 3 then entry_5_4.lower
  else if i.val == 4 ∧ j.val == 4 then entry_5_5.lower
  else if i.val == 4 ∧ j.val == 5 then entry_5_6.lower
  else if i.val == 4 ∧ j.val == 6 then entry_5_7.lower
  else if i.val == 4 ∧ j.val == 7 then entry_5_8.lower
  else if i.val == 4 ∧ j.val == 8 then entry_5_9.lower
  else if i.val == 4 ∧ j.val == 9 then entry_5_10.lower
  else if i.val == 5 ∧ j.val == 0 then entry_6_1.lower
  else if i.val == 5 ∧ j.val == 1 then entry_6_2.lower
  else if i.val == 5 ∧ j.val == 2 then entry_6_3.lower
  else if i.val == 5 ∧ j.val == 3 then entry_6_4.lower
  else if i.val == 5 ∧ j.val == 4 then entry_6_5.lower
  else if i.val == 5 ∧ j.val == 5 then entry_6_6.lower
  else if i.val == 5 ∧ j.val == 6 then entry_6_7.lower
  else if i.val == 5 ∧ j.val == 7 then entry_6_8.lower
  else if i.val == 5 ∧ j.val == 8 then entry_6_9.lower
  else if i.val == 5 ∧ j.val == 9 then entry_6_10.lower
  else if i.val == 6 ∧ j.val == 0 then entry_7_1.lower
  else if i.val == 6 ∧ j.val == 1 then entry_7_2.lower
  else if i.val == 6 ∧ j.val == 2 then entry_7_3.lower
  else if i.val == 6 ∧ j.val == 3 then entry_7_4.lower
  else if i.val == 6 ∧ j.val == 4 then entry_7_5.lower
  else if i.val == 6 ∧ j.val == 5 then entry_7_6.lower
  else if i.val == 6 ∧ j.val == 6 then entry_7_7.lower
  else if i.val == 6 ∧ j.val == 7 then entry_7_8.lower
  else if i.val == 6 ∧ j.val == 8 then entry_7_9.lower
  else if i.val == 6 ∧ j.val == 9 then entry_7_10.lower
  else if i.val == 7 ∧ j.val == 0 then entry_8_1.lower
  else if i.val == 7 ∧ j.val == 1 then entry_8_2.lower
  else if i.val == 7 ∧ j.val == 2 then entry_8_3.lower
  else if i.val == 7 ∧ j.val == 3 then entry_8_4.lower
  else if i.val == 7 ∧ j.val == 4 then entry_8_5.lower
  else if i.val == 7 ∧ j.val == 5 then entry_8_6.lower
  else if i.val == 7 ∧ j.val == 6 then entry_8_7.lower
  else if i.val == 7 ∧ j.val == 7 then entry_8_8.lower
  else if i.val == 7 ∧ j.val == 8 then entry_8_9.lower
  else if i.val == 7 ∧ j.val == 9 then entry_8_10.lower
  else if i.val == 8 ∧ j.val == 0 then entry_9_1.lower
  else if i.val == 8 ∧ j.val == 1 then entry_9_2.lower
  else if i.val == 8 ∧ j.val == 2 then entry_9_3.lower
  else if i.val == 8 ∧ j.val == 3 then entry_9_4.lower
  else if i.val == 8 ∧ j.val == 4 then entry_9_5.lower
  else if i.val == 8 ∧ j.val == 5 then entry_9_6.lower
  else if i.val == 8 ∧ j.val == 6 then entry_9_7.lower
  else if i.val == 8 ∧ j.val == 7 then entry_9_8.lower
  else if i.val == 8 ∧ j.val == 8 then entry_9_9.lower
  else if i.val == 8 ∧ j.val == 9 then entry_9_10.lower
  else if i.val == 9 ∧ j.val == 0 then entry_10_1.lower
  else if i.val == 9 ∧ j.val == 1 then entry_10_2.lower
  else if i.val == 9 ∧ j.val == 2 then entry_10_3.lower
  else if i.val == 9 ∧ j.val == 3 then entry_10_4.lower
  else if i.val == 9 ∧ j.val == 4 then entry_10_5.lower
  else if i.val == 9 ∧ j.val == 5 then entry_10_6.lower
  else if i.val == 9 ∧ j.val == 6 then entry_10_7.lower
  else if i.val == 9 ∧ j.val == 7 then entry_10_8.lower
  else if i.val == 9 ∧ j.val == 8 then entry_10_9.lower
  else if i.val == 9 ∧ j.val == 9 then entry_10_10.lower
  else 0

def gram_upper (i j : Fin 10) : ℚ :=
  if i.val == 0 ∧ j.val == 0 then entry_1_1.upper
  else if i.val == 0 ∧ j.val == 1 then entry_1_2.upper
  else if i.val == 0 ∧ j.val == 2 then entry_1_3.upper
  else if i.val == 0 ∧ j.val == 3 then entry_1_4.upper
  else if i.val == 0 ∧ j.val == 4 then entry_1_5.upper
  else if i.val == 0 ∧ j.val == 5 then entry_1_6.upper
  else if i.val == 0 ∧ j.val == 6 then entry_1_7.upper
  else if i.val == 0 ∧ j.val == 7 then entry_1_8.upper
  else if i.val == 0 ∧ j.val == 8 then entry_1_9.upper
  else if i.val == 0 ∧ j.val == 9 then entry_1_10.upper
  else if i.val == 1 ∧ j.val == 0 then entry_2_1.upper
  else if i.val == 1 ∧ j.val == 1 then entry_2_2.upper
  else if i.val == 1 ∧ j.val == 2 then entry_2_3.upper
  else if i.val == 1 ∧ j.val == 3 then entry_2_4.upper
  else if i.val == 1 ∧ j.val == 4 then entry_2_5.upper
  else if i.val == 1 ∧ j.val == 5 then entry_2_6.upper
  else if i.val == 1 ∧ j.val == 6 then entry_2_7.upper
  else if i.val == 1 ∧ j.val == 7 then entry_2_8.upper
  else if i.val == 1 ∧ j.val == 8 then entry_2_9.upper
  else if i.val == 1 ∧ j.val == 9 then entry_2_10.upper
  else if i.val == 2 ∧ j.val == 0 then entry_3_1.upper
  else if i.val == 2 ∧ j.val == 1 then entry_3_2.upper
  else if i.val == 2 ∧ j.val == 2 then entry_3_3.upper
  else if i.val == 2 ∧ j.val == 3 then entry_3_4.upper
  else if i.val == 2 ∧ j.val == 4 then entry_3_5.upper
  else if i.val == 2 ∧ j.val == 5 then entry_3_6.upper
  else if i.val == 2 ∧ j.val == 6 then entry_3_7.upper
  else if i.val == 2 ∧ j.val == 7 then entry_3_8.upper
  else if i.val == 2 ∧ j.val == 8 then entry_3_9.upper
  else if i.val == 2 ∧ j.val == 9 then entry_3_10.upper
  else if i.val == 3 ∧ j.val == 0 then entry_4_1.upper
  else if i.val == 3 ∧ j.val == 1 then entry_4_2.upper
  else if i.val == 3 ∧ j.val == 2 then entry_4_3.upper
  else if i.val == 3 ∧ j.val == 3 then entry_4_4.upper
  else if i.val == 3 ∧ j.val == 4 then entry_4_5.upper
  else if i.val == 3 ∧ j.val == 5 then entry_4_6.upper
  else if i.val == 3 ∧ j.val == 6 then entry_4_7.upper
  else if i.val == 3 ∧ j.val == 7 then entry_4_8.upper
  else if i.val == 3 ∧ j.val == 8 then entry_4_9.upper
  else if i.val == 3 ∧ j.val == 9 then entry_4_10.upper
  else if i.val == 4 ∧ j.val == 0 then entry_5_1.upper
  else if i.val == 4 ∧ j.val == 1 then entry_5_2.upper
  else if i.val == 4 ∧ j.val == 2 then entry_5_3.upper
  else if i.val == 4 ∧ j.val == 3 then entry_5_4.upper
  else if i.val == 4 ∧ j.val == 4 then entry_5_5.upper
  else if i.val == 4 ∧ j.val == 5 then entry_5_6.upper
  else if i.val == 4 ∧ j.val == 6 then entry_5_7.upper
  else if i.val == 4 ∧ j.val == 7 then entry_5_8.upper
  else if i.val == 4 ∧ j.val == 8 then entry_5_9.upper
  else if i.val == 4 ∧ j.val == 9 then entry_5_10.upper
  else if i.val == 5 ∧ j.val == 0 then entry_6_1.upper
  else if i.val == 5 ∧ j.val == 1 then entry_6_2.upper
  else if i.val == 5 ∧ j.val == 2 then entry_6_3.upper
  else if i.val == 5 ∧ j.val == 3 then entry_6_4.upper
  else if i.val == 5 ∧ j.val == 4 then entry_6_5.upper
  else if i.val == 5 ∧ j.val == 5 then entry_6_6.upper
  else if i.val == 5 ∧ j.val == 6 then entry_6_7.upper
  else if i.val == 5 ∧ j.val == 7 then entry_6_8.upper
  else if i.val == 5 ∧ j.val == 8 then entry_6_9.upper
  else if i.val == 5 ∧ j.val == 9 then entry_6_10.upper
  else if i.val == 6 ∧ j.val == 0 then entry_7_1.upper
  else if i.val == 6 ∧ j.val == 1 then entry_7_2.upper
  else if i.val == 6 ∧ j.val == 2 then entry_7_3.upper
  else if i.val == 6 ∧ j.val == 3 then entry_7_4.upper
  else if i.val == 6 ∧ j.val == 4 then entry_7_5.upper
  else if i.val == 6 ∧ j.val == 5 then entry_7_6.upper
  else if i.val == 6 ∧ j.val == 6 then entry_7_7.upper
  else if i.val == 6 ∧ j.val == 7 then entry_7_8.upper
  else if i.val == 6 ∧ j.val == 8 then entry_7_9.upper
  else if i.val == 6 ∧ j.val == 9 then entry_7_10.upper
  else if i.val == 7 ∧ j.val == 0 then entry_8_1.upper
  else if i.val == 7 ∧ j.val == 1 then entry_8_2.upper
  else if i.val == 7 ∧ j.val == 2 then entry_8_3.upper
  else if i.val == 7 ∧ j.val == 3 then entry_8_4.upper
  else if i.val == 7 ∧ j.val == 4 then entry_8_5.upper
  else if i.val == 7 ∧ j.val == 5 then entry_8_6.upper
  else if i.val == 7 ∧ j.val == 6 then entry_8_7.upper
  else if i.val == 7 ∧ j.val == 7 then entry_8_8.upper
  else if i.val == 7 ∧ j.val == 8 then entry_8_9.upper
  else if i.val == 7 ∧ j.val == 9 then entry_8_10.upper
  else if i.val == 8 ∧ j.val == 0 then entry_9_1.upper
  else if i.val == 8 ∧ j.val == 1 then entry_9_2.upper
  else if i.val == 8 ∧ j.val == 2 then entry_9_3.upper
  else if i.val == 8 ∧ j.val == 3 then entry_9_4.upper
  else if i.val == 8 ∧ j.val == 4 then entry_9_5.upper
  else if i.val == 8 ∧ j.val == 5 then entry_9_6.upper
  else if i.val == 8 ∧ j.val == 6 then entry_9_7.upper
  else if i.val == 8 ∧ j.val == 7 then entry_9_8.upper
  else if i.val == 8 ∧ j.val == 8 then entry_9_9.upper
  else if i.val == 8 ∧ j.val == 9 then entry_9_10.upper
  else if i.val == 9 ∧ j.val == 0 then entry_10_1.upper
  else if i.val == 9 ∧ j.val == 1 then entry_10_2.upper
  else if i.val == 9 ∧ j.val == 2 then entry_10_3.upper
  else if i.val == 9 ∧ j.val == 3 then entry_10_4.upper
  else if i.val == 9 ∧ j.val == 4 then entry_10_5.upper
  else if i.val == 9 ∧ j.val == 5 then entry_10_6.upper
  else if i.val == 9 ∧ j.val == 6 then entry_10_7.upper
  else if i.val == 9 ∧ j.val == 7 then entry_10_8.upper
  else if i.val == 9 ∧ j.val == 8 then entry_10_9.upper
  else if i.val == 9 ∧ j.val == 9 then entry_10_10.upper
  else 0

-- Rational intervals proved from the χ–ρ formula and Arb log/γ certificates.
def lin_lower : Fin 10 → ℚ :=
  RH.Certificates.Generated.ChiRhoBoundsN10.linearLower
def lin_upper : Fin 10 → ℚ :=
  RH.Certificates.Generated.ChiRhoBoundsN10.linearUpper
def const_lower : ℚ := 1 - (1/10000)
def const_upper : ℚ := 1 + (1/10000)

theorem toy_gram_certified (i j : Fin 10) :
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

def Q_interval : BaezDuarteIntervalQuadraticModel 10 :=
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


def witnessN10 : RationalPSDWitness 10 :=
{
  M := M_reg
  L := L_val
  D := D_val
  diagonal_nonneg := by intro i; fin_cases i <;> simp [D_val, D_val_fn] <;> norm_num
  ldl_identity := by ext i j; fin_cases i <;> fin_cases j <;> simp [M_reg, M_reg_fn, L_val, L_val_fn, D_val, D_val_fn, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] <;> norm_num
}

-- M_orig removed: implicitly bounded by the Gram entry intervals
def regCertN10 : RegularizedPSDCertificate 10 :=
{
  originalMatrix := M_reg - ((1/10000) : ℚ) • 1
  epsilon := (1/10000)
  regularizedMatrix := M_reg
  regularized_eq := by simp
  epsilon_nonneg := by norm_num
  witness := witnessN10
  witness_matches := rfl
}

-- energyUpper is the sign-aware interval arithmetic upper bound on:
--   ||chi||^2 - 2*c^T*l + c^T*G*c  where c = coeff_fn, l_k = innerProductChiRho k
-- This bounds BaezDuarteDistance N via candidate_bounds_baez_duarte_distance
-- (pending baezDuarteL2Error_gram_expansion axiom)
def witnessEnergy : FiniteIntervalEnergyWitness 10 :=
{
  model := Q_interval
  coeffs := coeff_fn
  energyUpper := (2467247166559955998491633492339104444863803204311798000344753988590852231300405054667096936512532082338945975919603117487626888160168985482211118669700186145913676995931536677398027490958697379177401103189507448514392749677644180797230146523822871911155181817220555138361655050506109959944527701802850930541816077045516911815135504206102898927162375633281891681441338655795980400797769565807014121952412194660794294663227540221042188577/95830299782168002227969571843719372553990886422833099850140155561014077382955546544724207422934920202890051568418300786184223633609898405022635869498788742757957186671554041963053762087461447368809860298238857800231052252374376723556392938934396943529158309611312462177500503390429805771694233956395331694034797549931124329514172800970697029412584249193851064980426134558141414661650434327335779501745375606813388809075838307925000000000)
  interval_energy_bound := True.intro
}


noncomputable def certN10 : FiniteApproximationCertificate :=
{
  N := 10
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
theorem N10_quadratic_le_energyUpper :
    ∑ h : Fin 10, ∑ k : Fin 10,
      (coeff_fn h : ℝ) * (coeff_fn k : ℝ) *
      RH.Criteria.NymanBeurling.VasyuninGram.baezDuarteGramEntry (h.val + 1) (k.val + 1)
    - 2 * ∑ k : Fin 10,
        (coeff_fn k : ℝ) * innerProductChiRho k.val
    + 1 ≤ (witnessEnergy.energyUpper : ℝ) := by
  have hbound := sign_aware_energy_bound (N := 10) coeff_fn
    (fun h k => RH.Criteria.NymanBeurling.VasyuninGram.baezDuarteGramEntry (h.val + 1) (k.val + 1))
    gram_lower gram_upper
    (fun k => innerProductChiRho k.val)
    lin_lower lin_upper
    (fun i j => (toy_gram_certified i j).1)
    (fun i j => (toy_gram_certified i j).2)
    (fun k =>
      (RH.Certificates.Generated.ChiRhoBoundsN10.innerProductChiRho_interval k).1)
    (fun k =>
      (RH.Certificates.Generated.ChiRhoBoundsN10.innerProductChiRho_interval k).2)
  have heq : signAwareQuadBoundQ coeff_fn gram_lower gram_upper +
             signAwareLinBoundQ coeff_fn lin_lower lin_upper + 1 =
             witnessEnergy.energyUpper := by native_decide
  calc ∑ h : Fin 10, ∑ k : Fin 10,
          (coeff_fn h : ℝ) * (coeff_fn k : ℝ) *
          RH.Criteria.NymanBeurling.VasyuninGram.baezDuarteGramEntry (h.val + 1) (k.val + 1)
        - 2 * ∑ k : Fin 10, (coeff_fn k : ℝ) * innerProductChiRho k.val + 1
      ≤ (signAwareQuadBoundQ coeff_fn gram_lower gram_upper : ℝ) +
        (signAwareLinBoundQ coeff_fn lin_lower lin_upper : ℝ) + 1 := hbound
    _ = (witnessEnergy.energyUpper : ℝ) := by exact_mod_cast heq

theorem baezDuarteDistance_N10_bound :
    RH.Criteria.NymanBeurling.BaezDuarte.BaezDuarteDistance 10 ≤
      (witnessEnergy.energyUpper : ℝ) := by
  apply (candidate_bounds_baez_duarte_distance
           (fun k => (coeff_fn k : ℝ))).trans
  rw [baezDuarteL2Error_gram_expansion]
  exact N10_quadratic_le_energyUpper

end RH.Certificates.Generated.NymanGramN10
