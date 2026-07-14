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

def entry_1_1 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 1
  lower := (6303/5000)
  upper := (12607/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_1.interval_proof
}

def entry_1_2 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 2
  lower := (3861/5000)
  upper := (7723/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_2.interval_proof
}

def entry_1_3 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 3
  lower := (23/40)
  upper := (5751/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_3.interval_proof
}

def entry_1_4 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 4
  lower := (74098041/159590000)
  upper := (74129959/159590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_4.interval_proof
}

def entry_1_5 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 5
  lower := (297474187/758130000)
  upper := (297625813/758130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_5.interval_proof
}

def entry_1_6 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 6
  lower := (138189523/404770000)
  upper := (138270477/404770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_6.interval_proof
}

def entry_1_7 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 7
  lower := (155428731/512690000)
  upper := (155531269/512690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_7.interval_proof
}

def entry_1_8 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 8
  lower := (14952029/54710000)
  upper := (14962971/54710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_8.interval_proof
}

def entry_1_9 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 9
  lower := (214204061/859390000)
  upper := (214375939/859390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_9.interval_proof
}

def entry_1_10 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 10
  lower := (16135967/70330000)
  upper := (16150033/70330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_10.interval_proof
}

def entry_1_11 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 11
  lower := (12924551/60740000)
  upper := (12936699/60740000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_11.interval_proof
}

def entry_1_12 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 12
  lower := (47665997/240030000)
  upper := (47714003/240030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_12.interval_proof
}

def entry_1_13 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 13
  lower := (53581241/287590000)
  upper := (53638759/287590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_13.interval_proof
}

def entry_1_14 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 14
  lower := (150274417/855830000)
  upper := (150445583/855830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_14.interval_proof
}

def entry_1_15 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 15
  lower := (161452817/971830000)
  upper := (161647183/971830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_15.interval_proof
}

def entry_1_16 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 16
  lower := (149864983/950170000)
  upper := (150055017/950170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_16.interval_proof
}

def entry_1_17 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 17
  lower := (149910189/998110000)
  upper := (150109811/998110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_17.interval_proof
}

def entry_1_18 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 18
  lower := (65389403/455970000)
  upper := (65480597/455970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_18.interval_proof
}

def entry_1_19 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 19
  lower := (2263351/16490000)
  upper := (2266649/16490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_19.interval_proof
}

def entry_1_20 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 20
  lower := (44721031/339690000)
  upper := (44788969/339690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_20.interval_proof
}

def entry_1_21 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 21
  lower := (97053293/767070000)
  upper := (97206707/767070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_21.interval_proof
}

def entry_1_22 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 22
  lower := (7348967/60330000)
  upper := (7361033/60330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_22.interval_proof
}

def entry_1_23 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 23
  lower := (57700879/491210000)
  upper := (57799121/491210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_23.interval_proof
}

def entry_1_24 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 24
  lower := (71586897/631030000)
  upper := (71713103/631030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_24.interval_proof
}

def entry_1_25 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 25
  lower := (21774153/198470000)
  upper := (21813847/198470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_25.interval_proof
}

def entry_1_26 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 26
  lower := (32829097/309030000)
  upper := (32890903/309030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_26.interval_proof
}

def entry_1_27 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 27
  lower := (95806971/930290000)
  upper := (95993029/930290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_27.interval_proof
}

def entry_1_28 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 28
  lower := (14749243/147570000)
  upper := (14778757/147570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_28.interval_proof
}

def entry_1_29 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 29
  lower := (81985563/844370000)
  upper := (82154437/844370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_29.interval_proof
}

def entry_1_30 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 30
  lower := (42375119/448810000)
  upper := (42464881/448810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_30.interval_proof
}

def entry_1_31 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 31
  lower := (23764139/258610000)
  upper := (23815861/258610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_31.interval_proof
}

def entry_1_32 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 32
  lower := (8855107/98930000)
  upper := (8874893/98930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_32.interval_proof
}

def entry_1_33 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 33
  lower := (61299747/702530000)
  upper := (61440253/702530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_33.interval_proof
}

def entry_1_34 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 34
  lower := (12988741/152590000)
  upper := (13019259/152590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_34.interval_proof
}

def entry_1_35 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 35
  lower := (7660781/92190000)
  upper := (7679219/92190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_35.interval_proof
}

def entry_1_36 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 36
  lower := (18107693/223070000)
  upper := (18152307/223070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_36.interval_proof
}

def entry_1_37 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 37
  lower := (2290713/28870000)
  upper := (2296487/28870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_37.interval_proof
}

def entry_1_38 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 38
  lower := (24708161/318390000)
  upper := (24771839/318390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_38.interval_proof
}

def entry_1_39 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 39
  lower := (26080657/343430000)
  upper := (26149343/343430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_39.interval_proof
}

def entry_1_40 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 40
  lower := (7366343/99070000)
  upper := (7386157/99070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_40.interval_proof
}

def entry_1_41 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 41
  lower := (56422537/774630000)
  upper := (56577463/774630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_41.interval_proof
}

def entry_1_42 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 42
  lower := (1234271/17290000)
  upper := (1237729/17290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_42.interval_proof
}

def entry_1_43 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 43
  lower := (60583447/865530000)
  upper := (60756553/865530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_43.interval_proof
}

def entry_1_44 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 44
  lower := (17097599/249010000)
  upper := (17147401/249010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_44.interval_proof
}

def entry_1_45 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 45
  lower := (58483207/867930000)
  upper := (58656793/867930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_45.interval_proof
}

def entry_1_46 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 46
  lower := (25791013/389870000)
  upper := (25868987/389870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_46.interval_proof
}

def entry_1_47 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 47
  lower := (10068503/154970000)
  upper := (10099497/154970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_47.interval_proof
}

def entry_1_48 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 48
  lower := (17622393/276070000)
  upper := (17677607/276070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_48.interval_proof
}

def entry_1_49 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 49
  lower := (1974977/31480000)
  upper := (1981273/31480000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_49.interval_proof
}

def entry_1_50 : GramEntryIntervalCertificate :=
{
  h := 1
  k := 50
  lower := (8232653/133470000)
  upper := (8259347/133470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_1_50.interval_proof
}

def entry_2_1 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 1
  lower := (3861/5000)
  upper := (7723/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_1.interval_proof
}

def entry_2_2 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 2
  lower := (6303/10000)
  upper := (394/625)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_2.interval_proof
}

def entry_2_3 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 3
  lower := (4411/10000)
  upper := (1103/2500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_3.interval_proof
}

def entry_2_4 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 4
  lower := (368854443/955570000)
  upper := (369045557/955570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_4.interval_proof
}

def entry_2_5 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 5
  lower := (36498461/115390000)
  upper := (36521539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_5.interval_proof
}

def entry_2_6 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 6
  lower := (269206331/936690000)
  upper := (269393669/936690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_6.interval_proof
}

def entry_2_7 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 7
  lower := (157846907/630930000)
  upper := (157973093/630930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_7.interval_proof
}

def entry_2_8 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 8
  lower := (75927287/327130000)
  upper := (75992713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_8.interval_proof
}

def entry_2_9 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 9
  lower := (135824899/651010000)
  upper := (135955101/651010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_9.interval_proof
}

def entry_2_10 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 10
  lower := (64257239/327610000)
  upper := (64322761/327610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_10.interval_proof
}

def entry_2_11 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 11
  lower := (146398607/813930000)
  upper := (146561393/813930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_11.interval_proof
}

def entry_2_12 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 12
  lower := (69074523/404770000)
  upper := (69155477/404770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_12.interval_proof
}

def entry_2_13 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 13
  lower := (104703999/660010000)
  upper := (104836001/660010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_13.interval_proof
}

def entry_2_14 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 14
  lower := (77688731/512690000)
  upper := (77791269/512690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_14.interval_proof
}

def entry_2_15 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 15
  lower := (8406591/59090000)
  upper := (8418409/59090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_15.interval_proof
}

def entry_2_16 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 16
  lower := (7473279/54710000)
  upper := (7484221/54710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_16.interval_proof
}

def entry_2_17 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 17
  lower := (856697/6630000)
  upper := (858023/6630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_17.interval_proof
}

def entry_2_18 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 18
  lower := (40807243/327570000)
  upper := (40872757/327570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_18.interval_proof
}

def entry_2_19 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 19
  lower := (37213607/313930000)
  upper := (37276393/313930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_19.interval_proof
}

def entry_2_20 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 20
  lower := (40714493/355070000)
  upper := (40785507/355070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_20.interval_proof
}

def entry_2_21 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 21
  lower := (36416783/332170000)
  upper := (36483217/332170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_21.interval_proof
}

def entry_2_22 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 22
  lower := (47010793/442070000)
  upper := (47099207/442070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_22.interval_proof
}

def entry_2_23 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 23
  lower := (100961091/989090000)
  upper := (101158909/989090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_23.interval_proof
}

def entry_2_24 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 24
  lower := (23820997/240030000)
  upper := (23869003/240030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_24.interval_proof
}

def entry_2_25 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 25
  lower := (42475557/444430000)
  upper := (42564443/444430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_25.interval_proof
}

def entry_2_26 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 26
  lower := (26776241/287590000)
  upper := (26833759/287590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_26.interval_proof
}

def entry_2_27 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 27
  lower := (30266339/336610000)
  upper := (30333661/336610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_27.interval_proof
}

def entry_2_28 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 28
  lower := (75094417/855830000)
  upper := (75265583/855830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_28.interval_proof
}

def entry_2_29 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 29
  lower := (37485869/441310000)
  upper := (37574131/441310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_29.interval_proof
}

def entry_2_30 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 30
  lower := (13074251/157490000)
  upper := (13105749/157490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_30.interval_proof
}

def entry_2_31 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 31
  lower := (10839041/134590000)
  upper := (10865959/134590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_31.interval_proof
}

def entry_2_32 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 32
  lower := (74884983/950170000)
  upper := (75075017/950170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_32.interval_proof
}

def entry_2_33 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 33
  lower := (76350321/996790000)
  upper := (76549679/996790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_33.interval_proof
}

def entry_2_34 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 34
  lower := (3445409/45910000)
  upper := (3454591/45910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_34.interval_proof
}

def entry_2_35 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 35
  lower := (57311551/784490000)
  upper := (57468449/784490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_35.interval_proof
}

def entry_2_36 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 36
  lower := (6770551/94490000)
  upper := (6789449/94490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_36.interval_proof
}

def entry_2_37 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 37
  lower := (12552031/179690000)
  upper := (12587969/179690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_37.interval_proof
}

def entry_2_38 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 38
  lower := (1130851/16490000)
  upper := (1134149/16490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_38.interval_proof
}

def entry_2_39 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 39
  lower := (10803861/161390000)
  upper := (10836139/161390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_39.interval_proof
}

def entry_2_40 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 40
  lower := (59749163/908370000)
  upper := (59930837/908370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_40.interval_proof
}

def entry_2_41 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 41
  lower := (62362987/970130000)
  upper := (62557013/970130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_41.interval_proof
}

def entry_2_42 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 42
  lower := (5320583/84170000)
  upper := (5337417/84170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_42.interval_proof
}

def entry_2_43 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 43
  lower := (8678467/140330000)
  upper := (8706533/140330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_43.interval_proof
}

def entry_2_44 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 44
  lower := (3671467/60330000)
  upper := (3683533/60330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_44.interval_proof
}

def entry_2_45 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 45
  lower := (56764751/952490000)
  upper := (56955249/952490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_45.interval_proof
}

def entry_2_46 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 46
  lower := (28825879/491210000)
  upper := (28924121/491210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_46.interval_proof
}

def entry_2_47 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 47
  lower := (1821633/31670000)
  upper := (1827967/31670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_47.interval_proof
}

def entry_2_48 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 48
  lower := (51469181/908190000)
  upper := (51650819/908190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_48.interval_proof
}

def entry_2_49 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 49
  lower := (54961137/988630000)
  upper := (55158863/988630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_49.interval_proof
}

def entry_2_50 : GramEntryIntervalCertificate :=
{
  h := 2
  k := 50
  lower := (2106157/38430000)
  upper := (2113843/38430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_2_50.interval_proof
}

def entry_3_1 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 1
  lower := (23/40)
  upper := (5751/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_1.interval_proof
}

def entry_3_2 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 2
  lower := (4411/10000)
  upper := (1103/2500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_2.interval_proof
}

def entry_3_3 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 3
  lower := (2101/5000)
  upper := (4203/10000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_3.interval_proof
}

def entry_3_4 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 4
  lower := (12635993/40070000)
  upper := (12644007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_4.interval_proof
}

def entry_3_5 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 5
  lower := (80650507/294930000)
  upper := (80709493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_5.interval_proof
}

def entry_3_6 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 6
  lower := (45200433/175670000)
  upper := (45235567/175670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_6.interval_proof
}

def entry_3_7 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 7
  lower := (112519007/509930000)
  upper := (112620993/509930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_7.interval_proof
}

def entry_3_8 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 8
  lower := (4014879/19960000)
  upper := (4018871/19960000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_8.interval_proof
}

def entry_3_9 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 9
  lower := (124245143/648570000)
  upper := (124374857/648570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_9.interval_proof
}

def entry_3_10 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 10
  lower := (64452631/373690000)
  upper := (64527369/373690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_10.interval_proof
}

def entry_3_11 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 11
  lower := (142731359/886410000)
  upper := (142908641/886410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_11.interval_proof
}

def entry_3_12 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 12
  lower := (50607287/327130000)
  upper := (50672713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_12.interval_proof
}

def entry_3_13 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 13
  lower := (50979311/356890000)
  upper := (51050689/356890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_13.interval_proof
}

def entry_3_14 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 14
  lower := (110508283/817170000)
  upper := (110671717/817170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_14.interval_proof
}

def entry_3_15 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 15
  lower := (42827239/327610000)
  upper := (42892761/327610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_15.interval_proof
}

def entry_3_16 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 16
  lower := (19793853/161470000)
  upper := (19826147/161470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_16.interval_proof
}

def entry_3_17 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 17
  lower := (6694909/57160000)
  upper := (6706341/57160000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_17.interval_proof
}

def entry_3_18 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 18
  lower := (9472921/83290000)
  upper := (9489579/83290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_18.interval_proof
}

def entry_3_19 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 19
  lower := (9353321/86790000)
  upper := (9370679/86790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_19.interval_proof
}

def entry_3_20 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 20
  lower := (37633689/363110000)
  upper := (37706311/363110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_20.interval_proof
}

def entry_3_21 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 21
  lower := (95535399/946010000)
  upper := (95724601/946010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_21.interval_proof
}

def entry_3_22 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 22
  lower := (68828611/713890000)
  upper := (68971389/713890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_22.interval_proof
}

def entry_3_23 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 23
  lower := (55640283/597170000)
  upper := (55759717/597170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_23.interval_proof
}

def entry_3_24 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 24
  lower := (14941087/164130000)
  upper := (14973913/164130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_24.interval_proof
}

def entry_3_25 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 25
  lower := (58183431/665690000)
  upper := (58316569/665690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_25.interval_proof
}

def entry_3_26 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 26
  lower := (6220663/73370000)
  upper := (6235337/73370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_26.interval_proof
}

def entry_3_27 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 27
  lower := (71344061/859390000)
  upper := (71515939/859390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_27.interval_proof
}

def entry_3_28 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 28
  lower := (44074949/550510000)
  upper := (44185051/550510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_28.interval_proof
}

def entry_3_29 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 29
  lower := (11764897/151030000)
  upper := (11795103/151030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_29.interval_proof
}

def entry_3_30 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 30
  lower := (5373967/70330000)
  upper := (5388033/70330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_30.interval_proof
}

def entry_3_31 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 31
  lower := (8773137/118630000)
  upper := (8796863/118630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_31.interval_proof
}

def entry_3_32 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 32
  lower := (38546561/534390000)
  upper := (38653439/534390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_32.interval_proof
}

def entry_3_33 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 33
  lower := (31325793/442070000)
  upper := (31414207/442070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_33.interval_proof
}

def entry_3_34 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 34
  lower := (62189587/904130000)
  upper := (62370413/904130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_34.interval_proof
}

def entry_3_35 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 35
  lower := (52531859/781410000)
  upper := (52688141/781410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_35.interval_proof
}

def entry_3_36 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 36
  lower := (47617991/720090000)
  upper := (47762009/720090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_36.interval_proof
}

def entry_3_37 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 37
  lower := (3872981/60190000)
  upper := (3885019/60190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_37.interval_proof
}

def entry_3_38 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 38
  lower := (42292867/671330000)
  upper := (42427133/671330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_38.interval_proof
}

def entry_3_39 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 39
  lower := (17841241/287590000)
  upper := (17898759/287590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_39.interval_proof
}

def entry_3_40 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 40
  lower := (170281/2815000)
  upper := (42711/703750)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_40.interval_proof
}

def entry_3_41 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 41
  lower := (47599747/802530000)
  upper := (47760253/802530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_41.interval_proof
}

def entry_3_42 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 42
  lower := (50034417/855830000)
  upper := (50205583/855830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_42.interval_proof
}

def entry_3_43 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 43
  lower := (17634121/308790000)
  upper := (17695879/308790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_43.interval_proof
}

def entry_3_44 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 44
  lower := (33989377/606230000)
  upper := (34110623/606230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_44.interval_proof
}

def entry_3_45 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 45
  lower := (53752817/971830000)
  upper := (53947183/971830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_45.interval_proof
}

def entry_3_46 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 46
  lower := (21989363/406370000)
  upper := (22070637/406370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_46.interval_proof
}

def entry_3_47 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 47
  lower := (289331/5440000)
  upper := (290419/5440000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_47.interval_proof
}

def entry_3_48 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 48
  lower := (44784709/852910000)
  upper := (44955291/852910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_48.interval_proof
}

def entry_3_49 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 49
  lower := (25181047/489530000)
  upper := (25278953/489530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_49.interval_proof
}

def entry_3_50 : GramEntryIntervalCertificate :=
{
  h := 3
  k := 50
  lower := (4600909/90910000)
  upper := (4619091/90910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_3_50.interval_proof
}

def entry_4_1 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 1
  lower := (74098041/159590000)
  upper := (74129959/159590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_1.interval_proof
}

def entry_4_2 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 2
  lower := (368854443/955570000)
  upper := (369045557/955570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_2.interval_proof
}

def entry_4_3 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 3
  lower := (12635993/40070000)
  upper := (12644007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_3.interval_proof
}

def entry_4_4 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 4
  lower := (797903/2532500)
  upper := (1596819/5065000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_4.interval_proof
}

def entry_4_5 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 5
  lower := (25442211/102890000)
  upper := (25462789/102890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_5.interval_proof
}

def entry_4_6 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 6
  lower := (55097507/249930000)
  upper := (55147493/249930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_6.interval_proof
}

def entry_4_7 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 7
  lower := (49395219/247810000)
  upper := (49444781/247810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_7.interval_proof
}

def entry_4_8 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 8
  lower := (14052717/72830000)
  upper := (14067283/72830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_8.interval_proof
}

def entry_4_9 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 9
  lower := (163044103/958970000)
  upper := (163235897/958970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_9.interval_proof
}

def entry_4_10 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 10
  lower := (18243461/115390000)
  upper := (18266539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_10.interval_proof
}

def entry_4_11 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 11
  lower := (4931041/33340000)
  upper := (4937709/33340000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_11.interval_proof
}

def entry_4_12 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 12
  lower := (134556331/936690000)
  upper := (134743669/936690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_12.interval_proof
}

def entry_4_13 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 13
  lower := (4026447/30530000)
  upper := (4032553/30530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_13.interval_proof
}

def entry_4_14 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 14
  lower := (103337357/826430000)
  upper := (103502643/826430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_14.interval_proof
}

def entry_4_15 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 15
  lower := (22107413/185870000)
  upper := (22144587/185870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_15.interval_proof
}

def entry_4_16 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 16
  lower := (37947287/327130000)
  upper := (38012713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_16.interval_proof
}

def entry_4_17 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 17
  lower := (3296469/30310000)
  upper := (3302531/30310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_17.interval_proof
}

def entry_4_18 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 18
  lower := (52819343/506570000)
  upper := (52920657/506570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_18.interval_proof
}

def entry_4_19 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 19
  lower := (13139383/131170000)
  upper := (13165617/131170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_19.interval_proof
}

def entry_4_20 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 20
  lower := (32112239/327610000)
  upper := (32177761/327610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_20.interval_proof
}

def entry_4_21 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 21
  lower := (21699187/233130000)
  upper := (21745813/233130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_21.interval_proof
}

def entry_4_22 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 22
  lower := (73158607/813930000)
  upper := (73321393/813930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_22.interval_proof
}

def entry_4_23 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 23
  lower := (1713229/19710000)
  upper := (1717171/19710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_23.interval_proof
}

def entry_4_24 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 24
  lower := (71156557/834430000)
  upper := (71323443/834430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_24.interval_proof
}

def entry_4_25 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 25
  lower := (11106401/135990000)
  upper := (11133599/135990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_25.interval_proof
}

def entry_4_26 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 26
  lower := (61252729/772710000)
  upper := (61407271/772710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_26.interval_proof
}

def entry_4_27 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 27
  lower := (16558501/214990000)
  upper := (16601499/214990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_27.interval_proof
}

def entry_4_28 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 28
  lower := (38818731/512690000)
  upper := (38921269/512690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_28.interval_proof
}

def entry_4_29 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 29
  lower := (686559/9410000)
  upper := (688441/9410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_29.interval_proof
}

def entry_4_30 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 30
  lower := (4200341/59090000)
  upper := (4212159/59090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_30.interval_proof
}

def entry_4_31 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 31
  lower := (57127577/824230000)
  upper := (57292423/824230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_31.interval_proof
}

def entry_4_32 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 32
  lower := (233369/3419375)
  upper := (1872423/27355000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_32.interval_proof
}

def entry_4_33 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 33
  lower := (8676867/131330000)
  upper := (8703133/131330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_33.interval_proof
}

def entry_4_34 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 34
  lower := (17073553/264470000)
  upper := (17126447/264470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_34.interval_proof
}

def entry_4_35 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 35
  lower := (2750143/43570000)
  upper := (2758857/43570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_35.interval_proof
}

def entry_4_36 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 36
  lower := (20387243/327570000)
  upper := (20452757/327570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_36.interval_proof
}

def entry_4_37 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 37
  lower := (1817931/30065000)
  upper := (227993/3758125)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_37.interval_proof
}

def entry_4_38 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 38
  lower := (43945793/742070000)
  upper := (44094207/742070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_38.interval_proof
}

def entry_4_39 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 39
  lower := (2680381/46190000)
  upper := (2689619/46190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_39.interval_proof
}

def entry_4_40 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 40
  lower := (20339493/355070000)
  upper := (20410507/355070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_40.interval_proof
}

def entry_4_41 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 41
  lower := (17598469/315310000)
  upper := (17661531/315310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_41.interval_proof
}

def entry_4_42 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 42
  lower := (18191783/332170000)
  upper := (18258217/332170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_42.interval_proof
}

def entry_4_43 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 43
  lower := (41882097/779030000)
  upper := (42037903/779030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_43.interval_proof
}

def entry_4_44 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 44
  lower := (37459483/705170000)
  upper := (37600517/705170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_44.interval_proof
}

def entry_4_45 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 45
  lower := (21338869/411310000)
  upper := (21421131/411310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_45.interval_proof
}

def entry_4_46 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 46
  lower := (50431091/989090000)
  upper := (50628909/989090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_46.interval_proof
}

def entry_4_47 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 47
  lower := (5113/102000)
  upper := (25667/510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_47.interval_proof
}

def entry_4_48 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 48
  lower := (11898497/240030000)
  upper := (11946503/240030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_48.interval_proof
}

def entry_4_49 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 49
  lower := (36714313/756870000)
  upper := (36865687/756870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_49.interval_proof
}

def entry_4_50 : GramEntryIntervalCertificate :=
{
  h := 4
  k := 50
  lower := (21215557/444430000)
  upper := (21304443/444430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_4_50.interval_proof
}

def entry_5_1 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 1
  lower := (297474187/758130000)
  upper := (297625813/758130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_1.interval_proof
}

def entry_5_2 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 2
  lower := (36498461/115390000)
  upper := (36521539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_2.interval_proof
}

def entry_5_3 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 3
  lower := (80650507/294930000)
  upper := (80709493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_3.interval_proof
}

def entry_5_4 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 4
  lower := (25442211/102890000)
  upper := (25462789/102890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_4.interval_proof
}

def entry_5_5 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 5
  lower := (175820239/697610000)
  upper := (175959761/697610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_5.interval_proof
}

def entry_5_6 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 6
  lower := (34982859/171410000)
  upper := (35017141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_6.interval_proof
}

def entry_5_7 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 7
  lower := (167378283/917170000)
  upper := (167561717/917170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_7.interval_proof
}

def entry_5_8 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 8
  lower := (2514001/14990000)
  upper := (2516999/14990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_8.interval_proof
}

def entry_5_9 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 9
  lower := (17229039/109610000)
  upper := (17250961/109610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_9.interval_proof
}

def entry_5_10 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 10
  lower := (50922007/329930000)
  upper := (50987993/329930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_10.interval_proof
}

def entry_5_11 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 11
  lower := (47031043/339570000)
  upper := (47098957/339570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_11.interval_proof
}

def entry_5_12 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 12
  lower := (40823471/315290000)
  upper := (40886529/315290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_12.interval_proof
}

def entry_5_13 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 13
  lower := (114946181/938190000)
  upper := (115133819/938190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_13.interval_proof
}

def entry_5_14 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 14
  lower := (3848713/32870000)
  upper := (3855287/32870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_14.interval_proof
}

def entry_5_15 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 15
  lower := (107626331/936690000)
  upper := (107813669/936690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_15.interval_proof
}

def entry_5_16 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 16
  lower := (19049673/178270000)
  upper := (19085327/178270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_16.interval_proof
}

def entry_5_17 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 17
  lower := (43667113/428870000)
  upper := (43752887/428870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_17.interval_proof
}

def entry_5_18 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 18
  lower := (24899519/254810000)
  upper := (24950481/254810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_18.interval_proof
}

def entry_5_19 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 19
  lower := (37759987/400130000)
  upper := (37840013/400130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_19.interval_proof
}

def entry_5_20 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 20
  lower := (21841459/235410000)
  upper := (21888541/235410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_20.interval_proof
}

def entry_5_21 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 21
  lower := (95329/1085000)
  upper := (47773/542500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_21.interval_proof
}

def entry_5_22 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 22
  lower := (18870197/223030000)
  upper := (18914803/223030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_22.interval_proof
}

def entry_5_23 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 23
  lower := (12263023/149770000)
  upper := (12292977/149770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_23.interval_proof
}

def entry_5_24 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 24
  lower := (1583011/19890000)
  upper := (1586989/19890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_24.interval_proof
}

def entry_5_25 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 25
  lower := (59434187/758130000)
  upper := (59585813/758130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_25.interval_proof
}

def entry_5_26 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 26
  lower := (13661797/182030000)
  upper := (13698203/182030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_26.interval_proof
}

def entry_5_27 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 27
  lower := (8113849/111510000)
  upper := (8136151/111510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_27.interval_proof
}

def entry_5_28 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 28
  lower := (1402619/19810000)
  upper := (1406581/19810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_28.interval_proof
}

def entry_5_29 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 29
  lower := (12793493/185070000)
  upper := (12830507/185070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_29.interval_proof
}

def entry_5_30 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 30
  lower := (5680421/83290000)
  upper := (5697079/83290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_30.interval_proof
}

def entry_5_31 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 31
  lower := (35955331/546690000)
  upper := (36064669/546690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_31.interval_proof
}

def entry_5_32 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 32
  lower := (10091747/157530000)
  upper := (10123253/157530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_32.interval_proof
}

def entry_5_33 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 33
  lower := (19768411/315890000)
  upper := (19831589/315890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_33.interval_proof
}

def entry_5_34 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 34
  lower := (52684049/859510000)
  upper := (52855951/859510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_34.interval_proof
}

def entry_5_35 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 35
  lower := (2560771/42290000)
  upper := (2569229/42290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_35.interval_proof
}

def entry_5_36 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 36
  lower := (11111071/189290000)
  upper := (11148929/189290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_36.interval_proof
}

def entry_5_37 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 37
  lower := (5869769/102310000)
  upper := (5890231/102310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_37.interval_proof
}

def entry_5_38 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 38
  lower := (49422073/879270000)
  upper := (49597927/879270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_38.interval_proof
}

def entry_5_39 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 39
  lower := (53652783/972170000)
  upper := (53847217/972170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_39.interval_proof
}

def entry_5_40 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 40
  lower := (42731707/782930000)
  upper := (42888293/782930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_40.interval_proof
}

def entry_5_41 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 41
  lower := (15520779/292210000)
  upper := (15579221/292210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_41.interval_proof
}

def entry_5_42 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 42
  lower := (39534049/759510000)
  upper := (39685951/759510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_42.interval_proof
}

def entry_5_43 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 43
  lower := (29103059/569410000)
  upper := (29216941/569410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_43.interval_proof
}

def entry_5_44 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 44
  lower := (22944367/456330000)
  upper := (23035633/456330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_44.interval_proof
}

def entry_5_45 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 45
  lower := (44690207/897930000)
  upper := (44869793/897930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_45.interval_proof
}

def entry_5_46 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 46
  lower := (11670977/240230000)
  upper := (11719023/240230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_46.interval_proof
}

def entry_5_47 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 47
  lower := (41393239/867610000)
  upper := (41566761/867610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_47.interval_proof
}

def entry_5_48 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 48
  lower := (2906931/61940000)
  upper := (2919319/61940000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_48.interval_proof
}

def entry_5_49 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 49
  lower := (2444713/52870000)
  upper := (2455287/52870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_49.interval_proof
}

def entry_5_50 : GramEntryIntervalCertificate :=
{
  h := 5
  k := 50
  lower := (16264493/355070000)
  upper := (16335507/355070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_5_50.interval_proof
}

def entry_6_1 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 1
  lower := (138189523/404770000)
  upper := (138270477/404770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_1.interval_proof
}

def entry_6_2 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 2
  lower := (269206331/936690000)
  upper := (269393669/936690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_2.interval_proof
}

def entry_6_3 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 3
  lower := (45200433/175670000)
  upper := (45235567/175670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_3.interval_proof
}

def entry_6_4 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 4
  lower := (55097507/249930000)
  upper := (55147493/249930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_4.interval_proof
}

def entry_6_5 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 5
  lower := (34982859/171410000)
  upper := (35017141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_5.interval_proof
}

def entry_6_6 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 6
  lower := (198705383/946170000)
  upper := (198894617/946170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_6.interval_proof
}

def entry_6_7 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 7
  lower := (81713059/469410000)
  upper := (81806941/469410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_7.interval_proof
}

def entry_6_8 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 8
  lower := (6315993/40070000)
  upper := (6324007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_8.interval_proof
}

def entry_6_9 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 9
  lower := (71076627/483730000)
  upper := (71173373/483730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_9.interval_proof
}

def entry_6_10 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 10
  lower := (40310507/294930000)
  upper := (40369493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_10.interval_proof
}

def entry_6_11 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 11
  lower := (38255551/294490000)
  upper := (38314449/294490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_11.interval_proof
}

def entry_6_12 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 12
  lower := (56760863/441370000)
  upper := (56849137/441370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_12.interval_proof
}

def entry_6_13 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 13
  lower := (12443359/106410000)
  upper := (12464641/106410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_13.interval_proof
}

def entry_6_14 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 14
  lower := (2713939/24610000)
  upper := (2718861/24610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_14.interval_proof
}

def entry_6_15 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 15
  lower := (12158461/115390000)
  upper := (12181539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_15.interval_proof
}

def entry_6_16 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 16
  lower := (4012883/39920000)
  upper := (4020867/39920000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_16.interval_proof
}

def entry_6_17 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 17
  lower := (79068453/815470000)
  upper := (79231547/815470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_17.interval_proof
}

def entry_6_18 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 18
  lower := (48279569/504310000)
  upper := (48380431/504310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_18.interval_proof
}

def entry_6_19 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 19
  lower := (16491647/183530000)
  upper := (16528353/183530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_19.interval_proof
}

def entry_6_20 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 20
  lower := (32207631/373690000)
  upper := (32282369/373690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_20.interval_proof
}

def entry_6_21 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 21
  lower := (76268471/915290000)
  upper := (76451529/915290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_21.interval_proof
}

def entry_6_22 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 22
  lower := (71321359/886410000)
  upper := (71498641/886410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_22.interval_proof
}

def entry_6_23 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 23
  lower := (75273793/962070000)
  upper := (75466207/962070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_23.interval_proof
}

def entry_6_24 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 24
  lower := (25287287/327130000)
  upper := (25352713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_24.interval_proof
}

def entry_6_25 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 25
  lower := (4757297/64530000)
  upper := (4770203/64530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_25.interval_proof
}

def entry_6_26 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 26
  lower := (21325121/298790000)
  upper := (21384879/298790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_26.interval_proof
}

def entry_6_27 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 27
  lower := (13089161/188390000)
  upper := (13126839/188390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_27.interval_proof
}

def entry_6_28 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 28
  lower := (20589527/304730000)
  upper := (20650473/304730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_28.interval_proof
}

def entry_6_29 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 29
  lower := (17842981/270190000)
  upper := (17897019/270190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_29.interval_proof
}

def entry_6_30 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 30
  lower := (21397239/327610000)
  upper := (21462761/327610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_30.interval_proof
}

def entry_6_31 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 31
  lower := (1077287/17130000)
  upper := (1080713/17130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_31.interval_proof
}

def entry_6_32 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 32
  lower := (9888853/161470000)
  upper := (9921147/161470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_32.interval_proof
}

def entry_6_33 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 33
  lower := (52302667/873330000)
  upper := (52477333/873330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_33.interval_proof
}

def entry_6_34 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 34
  lower := (55065891/941090000)
  upper := (55254109/941090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_34.interval_proof
}

def entry_6_35 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 35
  lower := (2254871/39290000)
  upper := (2262729/39290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_35.interval_proof
}

def entry_6_36 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 36
  lower := (31135201/547990000)
  upper := (31244799/547990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_36.interval_proof
}

def entry_6_37 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 37
  lower := (35934733/652670000)
  upper := (36065267/652670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_37.interval_proof
}

def entry_6_38 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 38
  lower := (4672321/86790000)
  upper := (4689679/86790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_38.interval_proof
}

def entry_6_39 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 39
  lower := (46761459/885410000)
  upper := (46938541/885410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_39.interval_proof
}

def entry_6_40 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 40
  lower := (18798689/363110000)
  upper := (18871311/363110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_40.interval_proof
}

def entry_6_41 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 41
  lower := (5844769/114810000)
  upper := (5867731/114810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_41.interval_proof
}

def entry_6_42 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 42
  lower := (43453857/861430000)
  upper := (43626143/861430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_42.interval_proof
}

def entry_6_43 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 43
  lower := (41345801/841990000)
  upper := (41514199/841990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_43.interval_proof
}

def entry_6_44 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 44
  lower := (34378611/713890000)
  upper := (34521389/713890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_44.interval_proof
}

def entry_6_45 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 45
  lower := (8394773/177270000)
  upper := (8430227/177270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_45.interval_proof
}

def entry_6_46 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 46
  lower := (27790283/597170000)
  upper := (27909717/597170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_46.interval_proof
}

def entry_6_47 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 47
  lower := (4534111/98890000)
  upper := (4553889/98890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_47.interval_proof
}

def entry_6_48 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 48
  lower := (42456619/933810000)
  upper := (42643381/933810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_48.interval_proof
}

def entry_6_49 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 49
  lower := (25113451/565490000)
  upper := (25226549/565490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_49.interval_proof
}

def entry_6_50 : GramEntryIntervalCertificate :=
{
  h := 6
  k := 50
  lower := (22219099/509010000)
  upper := (22320901/509010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_6_50.interval_proof
}

def entry_7_1 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 1
  lower := (155428731/512690000)
  upper := (155531269/512690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_1.interval_proof
}

def entry_7_2 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 2
  lower := (157846907/630930000)
  upper := (157973093/630930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_2.interval_proof
}

def entry_7_3 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 3
  lower := (112519007/509930000)
  upper := (112620993/509930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_3.interval_proof
}

def entry_7_4 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 4
  lower := (49395219/247810000)
  upper := (49444781/247810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_4.interval_proof
}

def entry_7_5 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 5
  lower := (167378283/917170000)
  upper := (167561717/917170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_5.interval_proof
}

def entry_7_6 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 6
  lower := (81713059/469410000)
  upper := (81806941/469410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_6.interval_proof
}

def entry_7_7 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 7
  lower := (70865629/393710000)
  upper := (70944371/393710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_7.interval_proof
}

def entry_7_8 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 8
  lower := (27455929/180710000)
  upper := (27492071/180710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_8.interval_proof
}

def entry_7_9 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 9
  lower := (34032863/246370000)
  upper := (34082137/246370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_9.interval_proof
}

def entry_7_10 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 10
  lower := (86672617/673830000)
  upper := (86807383/673830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_10.interval_proof
}

def entry_7_11 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 11
  lower := (96270517/794830000)
  upper := (96429483/794830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_11.interval_proof
}

def entry_7_12 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 12
  lower := (94797571/824290000)
  upper := (94962429/824290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_12.interval_proof
}

def entry_7_13 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 13
  lower := (13636439/123110000)
  upper := (13661061/123110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_13.interval_proof
}

def entry_7_14 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 14
  lower := (52417441/475590000)
  upper := (52512559/475590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_14.interval_proof
}

def entry_7_15 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 15
  lower := (28931421/285790000)
  upper := (28988579/285790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_15.interval_proof
}

def entry_7_16 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 16
  lower := (1045709/10910000)
  upper := (1047891/10910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_16.interval_proof
}

def entry_7_17 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 17
  lower := (41439803/451970000)
  upper := (41530197/451970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_17.interval_proof
}

def entry_7_18 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 18
  lower := (42916311/486890000)
  upper := (43013689/486890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_18.interval_proof
}

def entry_7_19 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 19
  lower := (2231877/26230000)
  upper := (2237123/26230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_19.interval_proof
}

def entry_7_20 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 20
  lower := (78045703/942970000)
  upper := (78234297/942970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_20.interval_proof
}

def entry_7_21 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 21
  lower := (76816371/936290000)
  upper := (77003629/936290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_21.interval_proof
}

def entry_7_22 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 22
  lower := (67792577/874230000)
  upper := (67967423/874230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_22.interval_proof
}

def entry_7_23 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 23
  lower := (5624463/75370000)
  upper := (5639537/75370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_23.interval_proof
}

def entry_7_24 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 24
  lower := (7952993/110070000)
  upper := (7975007/110070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_24.interval_proof
}

def entry_7_25 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 25
  lower := (5122699/73010000)
  upper := (5137301/73010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_25.interval_proof
}

def entry_7_26 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 26
  lower := (59183361/866390000)
  upper := (59356639/866390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_26.interval_proof
}

def entry_7_27 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 27
  lower := (32032073/479270000)
  upper := (32127927/479270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_27.interval_proof
}

def entry_7_28 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 28
  lower := (1518957/22930000)
  upper := (1523543/22930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_28.interval_proof
}

def entry_7_29 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 29
  lower := (58198369/916310000)
  upper := (58381631/916310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_29.interval_proof
}

def entry_7_30 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 30
  lower := (10882351/176490000)
  upper := (10917649/176490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_30.interval_proof
}

def entry_7_31 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 31
  lower := (607739/10110000)
  upper := (609761/10110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_31.interval_proof
}

def entry_7_32 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 32
  lower := (4100517/69830000)
  upper := (4114483/69830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_32.interval_proof
}

def entry_7_33 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 33
  lower := (47127989/820110000)
  upper := (47292011/820110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_33.interval_proof
}

def entry_7_34 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 34
  lower := (11709253/207470000)
  upper := (11750747/207470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_34.interval_proof
}

def entry_7_35 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 35
  lower := (5759709/102910000)
  upper := (5780291/102910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_35.interval_proof
}

def entry_7_36 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 36
  lower := (48739947/900530000)
  upper := (48920053/900530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_36.interval_proof
}

def entry_7_37 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 37
  lower := (48069017/909830000)
  upper := (48250983/909830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_37.interval_proof
}

def entry_7_38 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 38
  lower := (31459193/608070000)
  upper := (31580807/608070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_38.interval_proof
}

def entry_7_39 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 39
  lower := (25250233/497670000)
  upper := (25349767/497670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_39.interval_proof
}

def entry_7_40 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 40
  lower := (47015637/943630000)
  upper := (47204363/943630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_40.interval_proof
}

def entry_7_41 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 41
  lower := (8067557/164430000)
  upper := (8100443/164430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_41.interval_proof
}

def entry_7_42 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 42
  lower := (2546769/52310000)
  upper := (2557231/52310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_42.interval_proof
}

def entry_7_43 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 43
  lower := (20117513/424870000)
  upper := (20202487/424870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_43.interval_proof
}

def entry_7_44 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 44
  lower := (19662619/423810000)
  upper := (19747381/423810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_44.interval_proof
}

def entry_7_45 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 45
  lower := (4649797/102030000)
  upper := (4670203/102030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_45.interval_proof
}

def entry_7_46 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 46
  lower := (8715553/194470000)
  upper := (8754447/194470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_46.interval_proof
}

def entry_7_47 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 47
  lower := (14417323/326770000)
  upper := (14482677/326770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_47.interval_proof
}

def entry_7_48 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 48
  lower := (21395851/491490000)
  upper := (21494149/491490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_48.interval_proof
}

def entry_7_49 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 49
  lower := (5894363/136370000)
  upper := (5921637/136370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_49.interval_proof
}

def entry_7_50 : GramEntryIntervalCertificate :=
{
  h := 7
  k := 50
  lower := (8150689/193110000)
  upper := (8189311/193110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_7_50.interval_proof
}

def entry_8_1 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 1
  lower := (14952029/54710000)
  upper := (14962971/54710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_1.interval_proof
}

def entry_8_2 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 2
  lower := (75927287/327130000)
  upper := (75992713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_2.interval_proof
}

def entry_8_3 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 3
  lower := (4014879/19960000)
  upper := (4018871/19960000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_3.interval_proof
}

def entry_8_4 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 4
  lower := (14052717/72830000)
  upper := (14067283/72830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_4.interval_proof
}

def entry_8_5 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 5
  lower := (2514001/14990000)
  upper := (2516999/14990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_5.interval_proof
}

def entry_8_6 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 6
  lower := (6315993/40070000)
  upper := (6324007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_6.interval_proof
}

def entry_8_7 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 7
  lower := (27455929/180710000)
  upper := (27492071/180710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_7.interval_proof
}

def entry_8_8 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 8
  lower := (77955499/495010000)
  upper := (78054501/495010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_8.interval_proof
}

def entry_8_9 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 9
  lower := (11758283/87170000)
  upper := (11775717/87170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_9.interval_proof
}

def entry_8_10 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 10
  lower := (12715961/102890000)
  upper := (12736539/102890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_10.interval_proof
}

def entry_8_11 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 11
  lower := (27808387/241130000)
  upper := (27856613/241130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_11.interval_proof
}

def entry_8_12 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 12
  lower := (14656697/133030000)
  upper := (14683303/133030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_12.interval_proof
}

def entry_8_13 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 13
  lower := (9109969/87810000)
  upper := (9127531/87810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_13.interval_proof
}

def entry_8_14 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 14
  lower := (24685219/247810000)
  upper := (24734781/247810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_14.interval_proof
}

def entry_8_15 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 15
  lower := (52665471/545290000)
  upper := (52774529/545290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_15.interval_proof
}

def entry_8_16 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 16
  lower := (7022717/72830000)
  upper := (7037283/72830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_16.interval_proof
}

def entry_8_17 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 17
  lower := (10578151/118490000)
  upper := (10601849/118490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_17.interval_proof
}

def entry_8_18 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 18
  lower := (81474103/958970000)
  upper := (81665897/958970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_18.interval_proof
}

def entry_8_19 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 19
  lower := (36585097/449030000)
  upper := (36674903/449030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_19.interval_proof
}

def entry_8_20 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 20
  lower := (9115961/115390000)
  upper := (9139039/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_20.interval_proof
}

def entry_8_21 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 21
  lower := (32896733/432670000)
  upper := (32983267/432670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_21.interval_proof
}

def entry_8_22 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 22
  lower := (69875447/945530000)
  upper := (70064553/945530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_22.interval_proof
}

def entry_8_23 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 23
  lower := (909141/12590000)
  upper := (911659/12590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_23.interval_proof
}

def entry_8_24 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 24
  lower := (67346171/938290000)
  upper := (67533829/938290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_24.interval_proof
}

def entry_8_25 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 25
  lower := (39971401/585990000)
  upper := (40088599/585990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_25.interval_proof
}

def entry_8_26 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 26
  lower := (27463321/416790000)
  upper := (27546679/416790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_26.interval_proof
}

def entry_8_27 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 27
  lower := (8291033/129670000)
  upper := (8316967/129670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_27.interval_proof
}

def entry_8_28 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 28
  lower := (51627357/826430000)
  upper := (51792643/826430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_28.interval_proof
}

def entry_8_29 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 29
  lower := (19837337/326630000)
  upper := (19902663/326630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_29.interval_proof
}

def entry_8_30 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 30
  lower := (36179113/608870000)
  upper := (36300887/608870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_30.interval_proof
}

def entry_8_31 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 31
  lower := (57152033/979670000)
  upper := (57347967/979670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_31.interval_proof
}

def entry_8_32 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 32
  lower := (18957287/327130000)
  upper := (19022713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_32.interval_proof
}

def entry_8_33 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 33
  lower := (53583961/960390000)
  upper := (53776039/960390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_33.interval_proof
}

def entry_8_34 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 34
  lower := (40116161/738390000)
  upper := (40263839/738390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_34.interval_proof
}

def entry_8_35 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 35
  lower := (13968677/263230000)
  upper := (14021323/263230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_35.interval_proof
}

def entry_8_36 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 36
  lower := (8286091/159090000)
  upper := (8317909/159090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_36.interval_proof
}

def entry_8_37 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 37
  lower := (43554487/855130000)
  upper := (43725513/855130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_37.interval_proof
}

def entry_8_38 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 38
  lower := (41227603/823970000)
  upper := (41392397/823970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_38.interval_proof
}

def entry_8_39 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 39
  lower := (4020591/81590000)
  upper := (4036909/81590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_39.interval_proof
}

def entry_8_40 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 40
  lower := (26116657/533430000)
  upper := (26223343/533430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_40.interval_proof
}

def entry_8_41 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 41
  lower := (5499673/115770000)
  upper := (5522827/115770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_41.interval_proof
}

def entry_8_42 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 42
  lower := (756373/16270000)
  upper := (759627/16270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_42.interval_proof
}

def entry_8_43 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 43
  lower := (44672033/979670000)
  upper := (44867967/979670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_43.interval_proof
}

def entry_8_44 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 44
  lower := (36538607/813930000)
  upper := (36701393/813930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_44.interval_proof
}

def entry_8_45 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 45
  lower := (3411259/77410000)
  upper := (3426741/77410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_45.interval_proof
}

def entry_8_46 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 46
  lower := (855629/19710000)
  upper := (859571/19710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_46.interval_proof
}

def entry_8_47 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 47
  lower := (571167/13330000)
  upper := (573833/13330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_47.interval_proof
}

def entry_8_48 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 48
  lower := (35536557/834430000)
  upper := (35703443/834430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_48.interval_proof
}

def entry_8_49 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 49
  lower := (25059667/603330000)
  upper := (25180333/603330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_49.interval_proof
}

def entry_8_50 : GramEntryIntervalCertificate :=
{
  h := 8
  k := 50
  lower := (5546401/135990000)
  upper := (5573599/135990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_8_50.interval_proof
}

def entry_9_1 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 1
  lower := (214204061/859390000)
  upper := (214375939/859390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_1.interval_proof
}

def entry_9_2 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 2
  lower := (135824899/651010000)
  upper := (135955101/651010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_2.interval_proof
}

def entry_9_3 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 3
  lower := (124245143/648570000)
  upper := (124374857/648570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_3.interval_proof
}

def entry_9_4 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 4
  lower := (163044103/958970000)
  upper := (163235897/958970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_4.interval_proof
}

def entry_9_5 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 5
  lower := (17229039/109610000)
  upper := (17250961/109610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_5.interval_proof
}

def entry_9_6 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 6
  lower := (71076627/483730000)
  upper := (71173373/483730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_6.interval_proof
}

def entry_9_7 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 7
  lower := (34032863/246370000)
  upper := (34082137/246370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_7.interval_proof
}

def entry_9_8 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 8
  lower := (11758283/87170000)
  upper := (11775717/87170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_8.interval_proof
}

def entry_9_9 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 9
  lower := (12571019/89810000)
  upper := (12588981/89810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_9.interval_proof
}

def entry_9_10 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 10
  lower := (116434047/959530000)
  upper := (116625953/959530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_10.interval_proof
}

def entry_9_11 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 11
  lower := (5335219/47810000)
  upper := (5344781/47810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_11.interval_proof
}

def entry_9_12 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 12
  lower := (12627979/120210000)
  upper := (12652021/120210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_12.interval_proof
}

def entry_9_13 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 13
  lower := (16962929/170710000)
  upper := (16997071/170710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_13.interval_proof
}

def entry_9_14 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 14
  lower := (23572643/248570000)
  upper := (23622357/248570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_14.interval_proof
}

def entry_9_15 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 15
  lower := (80591521/884790000)
  upper := (80768479/884790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_15.interval_proof
}

def entry_9_16 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 16
  lower := (12042277/137230000)
  upper := (12069723/137230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_16.interval_proof
}

def entry_9_17 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 17
  lower := (25929723/302770000)
  upper := (25990277/302770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_17.interval_proof
}

def entry_9_18 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 18
  lower := (37825863/441370000)
  upper := (37914137/441370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_18.interval_proof
}

def entry_9_19 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 19
  lower := (25068609/313910000)
  upper := (25131391/313910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_19.interval_proof
}

def entry_9_20 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 20
  lower := (6915927/90730000)
  upper := (6934073/90730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_20.interval_proof
}

def entry_9_21 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 21
  lower := (65980213/897870000)
  upper := (66159787/897870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_21.interval_proof
}

def entry_9_22 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 22
  lower := (13487/190000)
  upper := (541/7600)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_22.interval_proof
}

def entry_9_23 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 23
  lower := (29981449/435510000)
  upper := (30068551/435510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_23.interval_proof
}

def entry_9_24 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 24
  lower := (4010887/59880000)
  upper := (4022863/59880000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_24.interval_proof
}

def entry_9_25 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 25
  lower := (31516713/482870000)
  upper := (31613287/482870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_25.interval_proof
}

def entry_9_26 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 26
  lower := (8696423/135770000)
  upper := (8723577/135770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_26.interval_proof
}

def entry_9_27 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 27
  lower := (32169569/504310000)
  upper := (32270431/504310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_27.interval_proof
}

def entry_9_28 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 28
  lower := (2958641/48590000)
  upper := (2968359/48590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_28.interval_proof
}

def entry_9_29 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 29
  lower := (699813/11870000)
  upper := (702187/11870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_29.interval_proof
}

def entry_9_30 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 30
  lower := (7291303/126970000)
  upper := (7316697/126970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_30.interval_proof
}

def entry_9_31 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 31
  lower := (2748841/49090000)
  upper := (2758659/49090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_31.interval_proof
}

def entry_9_32 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 32
  lower := (10301179/188210000)
  upper := (10338821/188210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_32.interval_proof
}

def entry_9_33 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 33
  lower := (14727527/274730000)
  upper := (14782473/274730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_33.interval_proof
}

def entry_9_34 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 34
  lower := (6567503/124970000)
  upper := (6592497/124970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_34.interval_proof
}

def entry_9_35 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 35
  lower := (35471471/685290000)
  upper := (35608529/685290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_35.interval_proof
}

def entry_9_36 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 36
  lower := (16847287/327130000)
  upper := (16912713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_36.interval_proof
}

def entry_9_37 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 37
  lower := (49260983/990170000)
  upper := (49459017/990170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_37.interval_proof
}

def entry_9_38 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 38
  lower := (2837903/58470000)
  upper := (2849597/58470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_38.interval_proof
}

def entry_9_39 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 39
  lower := (16969311/356890000)
  upper := (17040689/356890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_39.interval_proof
}

def entry_9_40 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 40
  lower := (2338109/50160000)
  upper := (2348141/50160000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_40.interval_proof
}

def entry_9_41 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 41
  lower := (45740069/999310000)
  upper := (45939931/999310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_41.interval_proof
}

def entry_9_42 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 42
  lower := (41148581/914190000)
  upper := (41331419/914190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_42.interval_proof
}

def entry_9_43 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 43
  lower := (1448729/32710000)
  upper := (1455271/32710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_43.interval_proof
}

def entry_9_44 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 44
  lower := (13763527/314730000)
  upper := (13826473/314730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_44.interval_proof
}

def entry_9_45 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 45
  lower := (42761717/982830000)
  upper := (42958283/982830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_45.interval_proof
}

def entry_9_46 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 46
  lower := (7140631/168690000)
  upper := (7174369/168690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_46.interval_proof
}

def entry_9_47 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 47
  lower := (728993/17570000)
  upper := (732507/17570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_47.interval_proof
}

def entry_9_48 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 48
  lower := (19761559/484410000)
  upper := (19858441/484410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_48.interval_proof
}

def entry_9_49 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 49
  lower := (35272109/878910000)
  upper := (35447891/878910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_49.interval_proof
}

def entry_9_50 : GramEntryIntervalCertificate :=
{
  h := 9
  k := 50
  lower := (10732847/271530000)
  upper := (10787153/271530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_9_50.interval_proof
}

def entry_10_1 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 1
  lower := (16135967/70330000)
  upper := (16150033/70330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_1.interval_proof
}

def entry_10_2 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 2
  lower := (64257239/327610000)
  upper := (64322761/327610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_2.interval_proof
}

def entry_10_3 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 3
  lower := (64452631/373690000)
  upper := (64527369/373690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_3.interval_proof
}

def entry_10_4 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 4
  lower := (18243461/115390000)
  upper := (18266539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_4.interval_proof
}

def entry_10_5 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 5
  lower := (50922007/329930000)
  upper := (50987993/329930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_5.interval_proof
}

def entry_10_6 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 6
  lower := (40310507/294930000)
  upper := (40369493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_6.interval_proof
}

def entry_10_7 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 7
  lower := (86672617/673830000)
  upper := (86807383/673830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_7.interval_proof
}

def entry_10_8 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 8
  lower := (12715961/102890000)
  upper := (12736539/102890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_8.interval_proof
}

def entry_10_9 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 9
  lower := (116434047/959530000)
  upper := (116625953/959530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_9.interval_proof
}

def entry_10_10 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 10
  lower := (39728461/315390000)
  upper := (39791539/315390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_10.interval_proof
}

def entry_10_11 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 11
  lower := (79467961/720390000)
  upper := (79612039/720390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_11.interval_proof
}

def entry_10_12 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 12
  lower := (17482859/171410000)
  upper := (17517141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_12.interval_proof
}

def entry_10_13 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 13
  lower := (22993523/239770000)
  upper := (23041477/239770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_13.interval_proof
}

def entry_10_14 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 14
  lower := (18160087/199130000)
  upper := (18199913/199130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_14.interval_proof
}

def entry_10_15 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 15
  lower := (2109169/23935000)
  upper := (528489/5983750)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_15.interval_proof
}

def entry_10_16 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 16
  lower := (1256251/14990000)
  upper := (1259249/14990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_16.interval_proof
}

def entry_10_17 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 17
  lower := (35975501/444990000)
  upper := (36064499/444990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_17.interval_proof
}

def entry_10_18 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 18
  lower := (8609039/109610000)
  upper := (8630961/109610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_18.interval_proof
}

def entry_10_19 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 19
  lower := (12617601/163990000)
  upper := (12650399/163990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_19.interval_proof
}

def entry_10_20 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 20
  lower := (73694443/955570000)
  upper := (73885557/955570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_20.interval_proof
}

def entry_10_21 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 21
  lower := (6974347/96530000)
  upper := (6993653/96530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_21.interval_proof
}

def entry_10_22 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 22
  lower := (1336269/19310000)
  upper := (1340131/19310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_22.interval_proof
}

def entry_10_23 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 23
  lower := (60339593/904070000)
  upper := (60520407/904070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_23.interval_proof
}

def entry_10_24 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 24
  lower := (59527979/920210000)
  upper := (59712021/920210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_24.interval_proof
}

def entry_10_25 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 25
  lower := (7290461/115390000)
  upper := (7313539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_25.interval_proof
}

def entry_10_26 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 26
  lower := (57426181/938190000)
  upper := (57613819/938190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_26.interval_proof
}

def entry_10_27 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 27
  lower := (13717033/229670000)
  upper := (13762967/229670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_27.interval_proof
}

def entry_10_28 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 28
  lower := (1922713/32870000)
  upper := (1929287/32870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_28.interval_proof
}

def entry_10_29 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 29
  lower := (10078489/175110000)
  upper := (10113511/175110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_29.interval_proof
}

def entry_10_30 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 30
  lower := (53766331/936690000)
  upper := (53953669/936690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_30.interval_proof
}

def entry_10_31 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 31
  lower := (2198003/39970000)
  upper := (2205997/39970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_31.interval_proof
}

def entry_10_32 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 32
  lower := (15825353/296470000)
  upper := (15884647/296470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_32.interval_proof
}

def entry_10_33 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 33
  lower := (25471043/489570000)
  upper := (25568957/489570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_33.interval_proof
}

def entry_10_34 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 34
  lower := (21812113/428870000)
  upper := (21897887/428870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_34.interval_proof
}

def entry_10_35 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 35
  lower := (195329/3910000)
  upper := (196111/3910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_35.interval_proof
}

def entry_10_36 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 36
  lower := (7985639/163610000)
  upper := (8018361/163610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_36.interval_proof
}

def entry_10_37 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 37
  lower := (6596231/137690000)
  upper := (6623769/137690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_37.interval_proof
}

def entry_10_38 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 38
  lower := (18859987/400130000)
  upper := (18940013/400130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_38.interval_proof
}

def entry_10_39 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 39
  lower := (9280051/199490000)
  upper := (9319949/199490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_39.interval_proof
}

def entry_10_40 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 40
  lower := (10908959/235410000)
  upper := (10956041/235410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_40.interval_proof
}

def entry_10_41 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 41
  lower := (40180489/895110000)
  upper := (40359511/895110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_41.interval_proof
}

def entry_10_42 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 42
  lower := (190441/4340000)
  upper := (191309/4340000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_42.interval_proof
}

def entry_10_43 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 43
  lower := (36375437/845630000)
  upper := (36544563/845630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_43.interval_proof
}

def entry_10_44 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 44
  lower := (6888697/163030000)
  upper := (6921303/163030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_44.interval_proof
}

def entry_10_45 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 45
  lower := (1503889/36110000)
  upper := (1511111/36110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_45.interval_proof
}

def entry_10_46 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 46
  lower := (39124317/956830000)
  upper := (39315683/956830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_46.interval_proof
}

def entry_10_47 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 47
  lower := (39142817/971830000)
  upper := (39337183/971830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_47.interval_proof
}

def entry_10_48 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 48
  lower := (790511/19890000)
  upper := (794489/19890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_48.interval_proof
}

def entry_10_49 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 49
  lower := (2877679/73210000)
  upper := (2892321/73210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_49.interval_proof
}

def entry_10_50 : GramEntryIntervalCertificate :=
{
  h := 10
  k := 50
  lower := (35519269/907310000)
  upper := (35700731/907310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_10_50.interval_proof
}

end RH.Certificates.Generated.NymanGramN50
