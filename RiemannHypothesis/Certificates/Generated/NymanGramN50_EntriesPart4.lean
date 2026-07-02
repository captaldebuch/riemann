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

def entry_31_1 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 1
  lower := (23764139/258610000)
  upper := (23815861/258610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_1.interval_proof
}

def entry_31_2 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 2
  lower := (10839041/134590000)
  upper := (10865959/134590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_2.interval_proof
}

def entry_31_3 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 3
  lower := (8773137/118630000)
  upper := (8796863/118630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_3.interval_proof
}

def entry_31_4 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 4
  lower := (57127577/824230000)
  upper := (57292423/824230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_4.interval_proof
}

def entry_31_5 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 5
  lower := (35955331/546690000)
  upper := (36064669/546690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_5.interval_proof
}

def entry_31_6 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 6
  lower := (1077287/17130000)
  upper := (1080713/17130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_6.interval_proof
}

def entry_31_7 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 7
  lower := (607739/10110000)
  upper := (609761/10110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_7.interval_proof
}

def entry_31_8 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 8
  lower := (57152033/979670000)
  upper := (57347967/979670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_8.interval_proof
}

def entry_31_9 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 9
  lower := (2748841/49090000)
  upper := (2758659/49090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_9.interval_proof
}

def entry_31_10 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 10
  lower := (2198003/39970000)
  upper := (2205997/39970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_10.interval_proof
}

def entry_31_11 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 11
  lower := (51792233/977670000)
  upper := (51987767/977670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_11.interval_proof
}

def entry_31_12 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 12
  lower := (21053881/411190000)
  upper := (21136119/411190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_12.interval_proof
}

def entry_31_13 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 13
  lower := (11080317/221830000)
  upper := (11124683/221830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_13.interval_proof
}

def entry_31_14 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 14
  lower := (48012237/977630000)
  upper := (48207763/977630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_14.interval_proof
}

def entry_31_15 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 15
  lower := (8036093/164070000)
  upper := (8068907/164070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_15.interval_proof
}

def entry_31_16 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 16
  lower := (4036567/84330000)
  upper := (4053433/84330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_16.interval_proof
}

def entry_31_17 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 17
  lower := (5416193/118070000)
  upper := (5439807/118070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_17.interval_proof
}

def entry_31_18 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 18
  lower := (12506921/280790000)
  upper := (12563079/280790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_18.interval_proof
}

def entry_31_19 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 19
  lower := (39698773/912270000)
  upper := (39881227/912270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_19.interval_proof
}

def entry_31_20 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 20
  lower := (42580339/996610000)
  upper := (42779661/996610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_20.interval_proof
}

def entry_31_21 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 21
  lower := (2075067/49330000)
  upper := (2084933/49330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_21.interval_proof
}

def entry_31_22 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 22
  lower := (15776707/382930000)
  upper := (15853293/382930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_22.interval_proof
}

def entry_31_23 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 23
  lower := (17816153/438470000)
  upper := (17903847/438470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_23.interval_proof
}

def entry_31_24 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 24
  lower := (27082421/675790000)
  upper := (27217579/675790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_24.interval_proof
}

def entry_31_25 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 25
  lower := (10244177/258230000)
  upper := (10295823/258230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_25.interval_proof
}

def entry_31_26 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 26
  lower := (29036201/737990000)
  upper := (29183799/737990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_26.interval_proof
}

def entry_31_27 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 27
  lower := (38950479/995210000)
  upper := (39149521/995210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_27.interval_proof
}

def entry_31_28 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 28
  lower := (35299649/903510000)
  upper := (35480351/903510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_28.interval_proof
}

def entry_31_29 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 29
  lower := (35140293/897070000)
  upper := (35319707/897070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_29.interval_proof
}

def entry_31_30 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 30
  lower := (3872703/97970000)
  upper := (3892297/97970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_30.interval_proof
}

def entry_31_31 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 31
  lower := (36689557/904430000)
  upper := (36870443/904430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_31.interval_proof
}

def entry_31_32 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 32
  lower := (3613567/94330000)
  upper := (3632433/94330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_32.interval_proof
}

def entry_31_33 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 33
  lower := (32092833/871670000)
  upper := (32267167/871670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_33.interval_proof
}

def entry_31_34 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 34
  lower := (24670741/692590000)
  upper := (24809259/692590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_34.interval_proof
}

def entry_31_35 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 35
  lower := (16671829/481710000)
  upper := (16768171/481710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_35.interval_proof
}

def entry_31_36 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 36
  lower := (33510657/993430000)
  upper := (33709343/993430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_36.interval_proof
}

def entry_31_37 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 37
  lower := (27466657/833430000)
  upper := (27633343/833430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_37.interval_proof
}

def entry_31_38 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 38
  lower := (2618879/81210000)
  upper := (2635121/81210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_38.interval_proof
}

def entry_31_39 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 39
  lower := (6696327/211730000)
  upper := (6738673/211730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_39.interval_proof
}

def entry_31_40 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 40
  lower := (28258921/910790000)
  upper := (28441079/910790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_40.interval_proof
}

def entry_31_41 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 41
  lower := (3650543/119570000)
  upper := (3674457/119570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_41.interval_proof
}

def entry_31_42 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 42
  lower := (3984717/132830000)
  upper := (4011283/132830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_42.interval_proof
}

def entry_31_43 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 43
  lower := (27187861/921390000)
  upper := (27372139/921390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_43.interval_proof
}

def entry_31_44 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 44
  lower := (2822791/97090000)
  upper := (2842209/97090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_44.interval_proof
}

def entry_31_45 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 45
  lower := (4934803/171970000)
  upper := (4969197/171970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_45.interval_proof
}

def entry_31_46 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 46
  lower := (7608217/267830000)
  upper := (7661783/267830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_46.interval_proof
}

def entry_31_47 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 47
  lower := (27491899/981010000)
  upper := (27688101/981010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_47.interval_proof
}

def entry_31_48 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 48
  lower := (2310613/83870000)
  upper := (2327387/83870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_48.interval_proof
}

def entry_31_49 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 49
  lower := (687967/25330000)
  upper := (693033/25330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_49.interval_proof
}

def entry_31_50 : GramEntryIntervalCertificate :=
{
  h := 31
  k := 50
  lower := (4762241/177590000)
  upper := (4797759/177590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_31_50.interval_proof
}

def entry_32_1 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 1
  lower := (8855107/98930000)
  upper := (8874893/98930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_1.interval_proof
}

def entry_32_2 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 2
  lower := (74884983/950170000)
  upper := (75075017/950170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_2.interval_proof
}

def entry_32_3 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 3
  lower := (38546561/534390000)
  upper := (38653439/534390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_3.interval_proof
}

def entry_32_4 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 4
  lower := (233369/3419375)
  upper := (1872423/27355000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_4.interval_proof
}

def entry_32_5 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 5
  lower := (10091747/157530000)
  upper := (10123253/157530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_5.interval_proof
}

def entry_32_6 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 6
  lower := (9888853/161470000)
  upper := (9921147/161470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_6.interval_proof
}

def entry_32_7 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 7
  lower := (4100517/69830000)
  upper := (4114483/69830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_7.interval_proof
}

def entry_32_8 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 8
  lower := (18957287/327130000)
  upper := (19022713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_8.interval_proof
}

def entry_32_9 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 9
  lower := (10301179/188210000)
  upper := (10338821/188210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_9.interval_proof
}

def entry_32_10 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 10
  lower := (15825353/296470000)
  upper := (15884647/296470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_10.interval_proof
}

def entry_32_11 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 11
  lower := (23729591/454090000)
  upper := (23820409/454090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_11.interval_proof
}

def entry_32_12 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 12
  lower := (48912587/974130000)
  upper := (49107413/974130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_12.interval_proof
}

def entry_32_13 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 13
  lower := (18312553/374470000)
  upper := (18387447/374470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_13.interval_proof
}

def entry_32_14 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 14
  lower := (522309/10910000)
  upper := (524491/10910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_14.interval_proof
}

def entry_32_15 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 15
  lower := (9438081/199190000)
  upper := (9477919/199190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_15.interval_proof
}

def entry_32_16 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 16
  lower := (3507717/72830000)
  upper := (3522283/72830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_16.interval_proof
}

def entry_32_17 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 17
  lower := (12412621/273790000)
  upper := (12467379/273790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_17.interval_proof
}

def entry_32_18 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 18
  lower := (6014277/137230000)
  upper := (6041723/137230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_18.interval_proof
}

def entry_32_19 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 19
  lower := (327593/7663750)
  upper := (1316503/30655000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_19.interval_proof
}

def entry_32_20 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 20
  lower := (40383511/964890000)
  upper := (40576489/964890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_20.interval_proof
}

def entry_32_21 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 21
  lower := (359129/8710000)
  upper := (360871/8710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_21.interval_proof
}

def entry_32_22 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 22
  lower := (10763381/266190000)
  upper := (10816619/266190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_22.interval_proof
}

def entry_32_23 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 23
  lower := (36966953/930470000)
  upper := (37153047/930470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_23.interval_proof
}

def entry_32_24 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 24
  lower := (1575993/40070000)
  upper := (1584007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_24.interval_proof
}

def entry_32_25 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 25
  lower := (195199/5041250)
  upper := (784829/20165000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_25.interval_proof
}

def entry_32_26 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 26
  lower := (2070601/53990000)
  upper := (2081399/53990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_26.interval_proof
}

def entry_32_27 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 27
  lower := (7598041/199590000)
  upper := (7637959/199590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_27.interval_proof
}

def entry_32_28 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 28
  lower := (3290071/86790000)
  upper := (3307429/86790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_28.interval_proof
}

def entry_32_29 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 29
  lower := (1323503/34970000)
  upper := (1330497/34970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_29.interval_proof
}

def entry_32_30 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 30
  lower := (3841879/101210000)
  upper := (3862121/101210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_30.interval_proof
}

def entry_32_31 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 31
  lower := (3613567/94330000)
  upper := (3632433/94330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_31.interval_proof
}

def entry_32_32 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 32
  lower := (12393461/315390000)
  upper := (12456539/315390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_32.interval_proof
}

def entry_32_33 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 33
  lower := (2568089/69110000)
  upper := (2581911/69110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_33.interval_proof
}

def entry_32_34 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 34
  lower := (18029561/504390000)
  upper := (18130439/504390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_34.interval_proof
}

def entry_32_35 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 35
  lower := (1774871/51290000)
  upper := (1785129/51290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_35.interval_proof
}

def entry_32_36 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 36
  lower := (6638271/197290000)
  upper := (6677729/197290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_36.interval_proof
}

def entry_32_37 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 37
  lower := (15652277/477230000)
  upper := (15747723/477230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_37.interval_proof
}

def entry_32_38 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 38
  lower := (16817533/524670000)
  upper := (16922467/524670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_38.interval_proof
}

def entry_32_39 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 39
  lower := (2265281/72190000)
  upper := (2279719/72190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_39.interval_proof
}

def entry_32_40 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 40
  lower := (14652461/475390000)
  upper := (14747539/475390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_40.interval_proof
}

def entry_32_41 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 41
  lower := (3695267/122330000)
  upper := (3719733/122330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_41.interval_proof
}

def entry_32_42 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 42
  lower := (391339/13172500)
  upper := (787947/26345000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_42.interval_proof
}

def entry_32_43 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 43
  lower := (12183347/416530000)
  upper := (12266653/416530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_43.interval_proof
}

def entry_32_44 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 44
  lower := (1903381/66190000)
  upper := (1916619/66190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_44.interval_proof
}

def entry_32_45 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 45
  lower := (4372567/154330000)
  upper := (4403433/154330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_45.interval_proof
}

def entry_32_46 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 46
  lower := (5154059/184410000)
  upper := (5190941/184410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_46.interval_proof
}

def entry_32_47 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 47
  lower := (20605429/745710000)
  upper := (20754571/745710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_47.interval_proof
}

def entry_32_48 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 48
  lower := (3654197/133030000)
  upper := (3680803/133030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_48.interval_proof
}

def entry_32_49 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 49
  lower := (14296881/531190000)
  upper := (14403119/531190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_49.interval_proof
}

def entry_32_50 : GramEntryIntervalCertificate :=
{
  h := 32
  k := 50
  lower := (6089533/229670000)
  upper := (6135467/229670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_32_50.interval_proof
}

def entry_33_1 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 1
  lower := (61299747/702530000)
  upper := (61440253/702530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_1.interval_proof
}

def entry_33_2 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 2
  lower := (76350321/996790000)
  upper := (76549679/996790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_2.interval_proof
}

def entry_33_3 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 3
  lower := (31325793/442070000)
  upper := (31414207/442070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_3.interval_proof
}

def entry_33_4 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 4
  lower := (8676867/131330000)
  upper := (8703133/131330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_4.interval_proof
}

def entry_33_5 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 5
  lower := (19768411/315890000)
  upper := (19831589/315890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_5.interval_proof
}

def entry_33_6 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 6
  lower := (52302667/873330000)
  upper := (52477333/873330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_6.interval_proof
}

def entry_33_7 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 7
  lower := (47127989/820110000)
  upper := (47292011/820110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_7.interval_proof
}

def entry_33_8 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 8
  lower := (53583961/960390000)
  upper := (53776039/960390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_8.interval_proof
}

def entry_33_9 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 9
  lower := (14727527/274730000)
  upper := (14782473/274730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_9.interval_proof
}

def entry_33_10 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 10
  lower := (25471043/489570000)
  upper := (25568957/489570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_10.interval_proof
}

def entry_33_11 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 11
  lower := (3752807/71930000)
  upper := (3767193/71930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_11.interval_proof
}

def entry_33_12 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 12
  lower := (19106193/388070000)
  upper := (19183807/388070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_12.interval_proof
}

def entry_33_13 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 13
  lower := (6895597/144030000)
  upper := (6924403/144030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_13.interval_proof
}

def entry_33_14 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 14
  lower := (4819697/103030000)
  upper := (4840303/103030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_14.interval_proof
}

def entry_33_15 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 15
  lower := (40362447/875530000)
  upper := (40537553/875530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_15.interval_proof
}

def entry_33_16 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 16
  lower := (1251281/27190000)
  upper := (1256719/27190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_16.interval_proof
}

def entry_33_17 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 17
  lower := (5036317/111830000)
  upper := (5058683/111830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_17.interval_proof
}

def entry_33_18 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 18
  lower := (18606963/430370000)
  upper := (18693037/430370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_18.interval_proof
}

def entry_33_19 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 19
  lower := (7943591/189090000)
  upper := (7981409/189090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_19.interval_proof
}

def entry_33_20 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 20
  lower := (37528661/913390000)
  upper := (37711339/913390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_20.interval_proof
}

def entry_33_21 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 21
  lower := (8705901/215990000)
  upper := (8749099/215990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_21.interval_proof
}

def entry_33_22 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 22
  lower := (14673317/366830000)
  upper := (14746683/366830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_22.interval_proof
}

def entry_33_23 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 23
  lower := (1830303/46970000)
  upper := (1839697/46970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_23.interval_proof
}

def entry_33_24 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 24
  lower := (9253387/241130000)
  upper := (9301613/241130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_24.interval_proof
}

def entry_33_25 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 25
  lower := (19019847/501530000)
  upper := (19120153/501530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_25.interval_proof
}

def entry_33_26 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 26
  lower := (15109667/403330000)
  upper := (15190333/403330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_26.interval_proof
}

def entry_33_27 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 27
  lower := (1775219/47810000)
  upper := (1784781/47810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_27.interval_proof
}

def entry_33_28 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 28
  lower := (19158051/519490000)
  upper := (19261949/519490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_28.interval_proof
}

def entry_33_29 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 29
  lower := (33758097/919030000)
  upper := (33941903/919030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_29.interval_proof
}

def entry_33_30 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 30
  lower := (32920309/896910000)
  upper := (33099691/896910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_30.interval_proof
}

def entry_33_31 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 31
  lower := (32092833/871670000)
  upper := (32267167/871670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_31.interval_proof
}

def entry_33_32 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 32
  lower := (2568089/69110000)
  upper := (2581911/69110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_32.interval_proof
}

def entry_33_33 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 33
  lower := (26580239/697610000)
  upper := (26719761/697610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_33.interval_proof
}

def entry_33_34 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 34
  lower := (20303723/562770000)
  upper := (20416277/562770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_34.interval_proof
}

def entry_33_35 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 35
  lower := (27012227/777730000)
  upper := (27167773/777730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_35.interval_proof
}

def entry_33_36 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 36
  lower := (30708737/912630000)
  upper := (30891263/912630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_36.interval_proof
}

def entry_33_37 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 37
  lower := (12481857/381430000)
  upper := (12558143/381430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_37.interval_proof
}

def entry_33_38 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 38
  lower := (4667377/146230000)
  upper := (4696623/146230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_38.interval_proof
}

def entry_33_39 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 39
  lower := (27282571/874290000)
  upper := (27457429/874290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_39.interval_proof
}

def entry_33_40 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 40
  lower := (11178421/365790000)
  upper := (11251579/365790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_40.interval_proof
}

def entry_33_41 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 41
  lower := (12892011/429890000)
  upper := (12977989/429890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_41.interval_proof
}

def entry_33_42 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 42
  lower := (17331121/588790000)
  upper := (17448879/588790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_42.interval_proof
}

def entry_33_43 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 43
  lower := (839599/29010000)
  upper := (845401/29010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_43.interval_proof
}

def entry_33_44 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 44
  lower := (12595923/440770000)
  upper := (12684077/440770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_44.interval_proof
}

def entry_33_45 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 45
  lower := (64987/2317500)
  upper := (130901/4635000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_45.interval_proof
}

def entry_33_46 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 46
  lower := (215221/7790000)
  upper := (216779/7790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_46.interval_proof
}

def entry_33_47 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 47
  lower := (1342573/49270000)
  upper := (1352427/49270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_47.interval_proof
}

def entry_33_48 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 48
  lower := (21500143/798570000)
  upper := (21659857/798570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_48.interval_proof
}

def entry_33_49 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 49
  lower := (1718557/64430000)
  upper := (1731443/64430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_49.interval_proof
}

def entry_33_50 : GramEntryIntervalCertificate :=
{
  h := 33
  k := 50
  lower := (637579/24210000)
  upper := (642421/24210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_33_50.interval_proof
}

def entry_34_1 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 1
  lower := (12988741/152590000)
  upper := (13019259/152590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_1.interval_proof
}

def entry_34_2 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 2
  lower := (3445409/45910000)
  upper := (3454591/45910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_2.interval_proof
}

def entry_34_3 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 3
  lower := (62189587/904130000)
  upper := (62370413/904130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_3.interval_proof
}

def entry_34_4 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 4
  lower := (17073553/264470000)
  upper := (17126447/264470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_4.interval_proof
}

def entry_34_5 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 5
  lower := (52684049/859510000)
  upper := (52855951/859510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_5.interval_proof
}

def entry_34_6 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 6
  lower := (55065891/941090000)
  upper := (55254109/941090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_6.interval_proof
}

def entry_34_7 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 7
  lower := (11709253/207470000)
  upper := (11750747/207470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_7.interval_proof
}

def entry_34_8 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 8
  lower := (40116161/738390000)
  upper := (40263839/738390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_8.interval_proof
}

def entry_34_9 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 9
  lower := (6567503/124970000)
  upper := (6592497/124970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_9.interval_proof
}

def entry_34_10 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 10
  lower := (21812113/428870000)
  upper := (21897887/428870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_10.interval_proof
}

def entry_34_11 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 11
  lower := (35030131/698690000)
  upper := (35169869/698690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_11.interval_proof
}

def entry_34_12 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 12
  lower := (8864197/183030000)
  upper := (8900803/183030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_12.interval_proof
}

def entry_34_13 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 13
  lower := (2316307/49430000)
  upper := (2326193/49430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_13.interval_proof
}

def entry_34_14 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 14
  lower := (5927057/129430000)
  upper := (5952943/129430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_14.interval_proof
}

def entry_34_15 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 15
  lower := (67001/1490000)
  upper := (67299/1490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_15.interval_proof
}

def entry_34_16 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 16
  lower := (5283151/118490000)
  upper := (5306849/118490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_16.interval_proof
}

def entry_34_17 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 17
  lower := (4563681/100690000)
  upper := (4583819/100690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_17.interval_proof
}

def entry_34_18 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 18
  lower := (12949723/302770000)
  upper := (13010277/302770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_18.interval_proof
}

def entry_34_19 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 19
  lower := (468867/11330000)
  upper := (471133/11330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_19.interval_proof
}

def entry_34_20 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 20
  lower := (17965501/444990000)
  upper := (18054499/444990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_20.interval_proof
}

def entry_34_21 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 21
  lower := (30363211/767890000)
  upper := (30516789/767890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_21.interval_proof
}

def entry_34_22 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 22
  lower := (1791397/46030000)
  upper := (1800603/46030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_22.interval_proof
}

def entry_34_23 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 23
  lower := (38350069/999310000)
  upper := (38549931/999310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_23.interval_proof
}

def entry_34_24 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 24
  lower := (6335663/168370000)
  upper := (6369337/168370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_24.interval_proof
}

def entry_34_25 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 25
  lower := (12007649/323510000)
  upper := (12072351/323510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_25.interval_proof
}

def entry_34_26 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 26
  lower := (31304643/853570000)
  upper := (31475357/853570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_26.interval_proof
}

def entry_34_27 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 27
  lower := (33308237/917630000)
  upper := (33491763/917630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_27.interval_proof
}

def entry_34_28 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 28
  lower := (1914679/53210000)
  upper := (1925321/53210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_28.interval_proof
}

def entry_34_29 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 29
  lower := (33945093/949070000)
  upper := (34134907/949070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_29.interval_proof
}

def entry_34_30 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 30
  lower := (27572633/773670000)
  upper := (27727367/773670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_30.interval_proof
}

def entry_34_31 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 31
  lower := (24670741/692590000)
  upper := (24809259/692590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_31.interval_proof
}

def entry_34_32 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 32
  lower := (18029561/504390000)
  upper := (18130439/504390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_32.interval_proof
}

def entry_34_33 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 33
  lower := (20303723/562770000)
  upper := (20416277/562770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_33.interval_proof
}

def entry_34_34 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 34
  lower := (3321019/89810000)
  upper := (3338981/89810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_34.interval_proof
}

def entry_34_35 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 35
  lower := (2337333/66670000)
  upper := (2350667/66670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_35.interval_proof
}

def entry_34_36 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 36
  lower := (16815217/497830000)
  upper := (16914783/497830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_36.interval_proof
}

def entry_34_37 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 37
  lower := (30606513/934870000)
  upper := (30793487/934870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_37.interval_proof
}

def entry_34_38 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 38
  lower := (4621493/145070000)
  upper := (4650507/145070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_38.interval_proof
}

def entry_34_39 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 39
  lower := (246831/7940000)
  upper := (248419/7940000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_39.interval_proof
}

def entry_34_40 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 40
  lower := (21499279/707210000)
  upper := (21640721/707210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_40.interval_proof
}

def entry_34_41 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 41
  lower := (1209689/40610000)
  upper := (1217811/40610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_41.interval_proof
}

def entry_34_42 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 42
  lower := (17370559/594410000)
  upper := (17489441/594410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_42.interval_proof
}

def entry_34_43 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 43
  lower := (11898547/414530000)
  upper := (11981453/414530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_43.interval_proof
}

def entry_34_44 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 44
  lower := (346273/12270000)
  upper := (348727/12270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_44.interval_proof
}

def entry_34_45 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 45
  lower := (305153/10970000)
  upper := (307347/10970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_45.interval_proof
}

def entry_34_46 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 46
  lower := (928483/33920000)
  upper := (935267/33920000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_46.interval_proof
}

def entry_34_47 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 47
  lower := (23990999/890010000)
  upper := (24169001/890010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_47.interval_proof
}

def entry_34_48 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 48
  lower := (6107033/229670000)
  upper := (6152967/229670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_48.interval_proof
}

def entry_34_49 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 49
  lower := (21378589/814110000)
  upper := (21541411/814110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_49.interval_proof
}

def entry_34_50 : GramEntryIntervalCertificate :=
{
  h := 34
  k := 50
  lower := (23798419/915810000)
  upper := (23981581/915810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_34_50.interval_proof
}

def entry_35_1 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 1
  lower := (7660781/92190000)
  upper := (7679219/92190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_1.interval_proof
}

def entry_35_2 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 2
  lower := (57311551/784490000)
  upper := (57468449/784490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_2.interval_proof
}

def entry_35_3 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 3
  lower := (52531859/781410000)
  upper := (52688141/781410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_3.interval_proof
}

def entry_35_4 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 4
  lower := (2750143/43570000)
  upper := (2758857/43570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_4.interval_proof
}

def entry_35_5 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 5
  lower := (2560771/42290000)
  upper := (2569229/42290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_5.interval_proof
}

def entry_35_6 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 6
  lower := (2254871/39290000)
  upper := (2262729/39290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_6.interval_proof
}

def entry_35_7 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 7
  lower := (5759709/102910000)
  upper := (5780291/102910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_7.interval_proof
}

def entry_35_8 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 8
  lower := (13968677/263230000)
  upper := (14021323/263230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_8.interval_proof
}

def entry_35_9 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 9
  lower := (35471471/685290000)
  upper := (35608529/685290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_9.interval_proof
}

def entry_35_10 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 10
  lower := (195329/3910000)
  upper := (196111/3910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_10.interval_proof
}

def entry_35_11 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 11
  lower := (46314997/950030000)
  upper := (46505003/950030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_11.interval_proof
}

def entry_35_12 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 12
  lower := (4024091/84090000)
  upper := (4040909/84090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_12.interval_proof
}

def entry_35_13 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 13
  lower := (79587/1730000)
  upper := (79933/1730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_13.interval_proof
}

def entry_35_14 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 14
  lower := (36429227/807730000)
  upper := (36590773/807730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_14.interval_proof
}

def entry_35_15 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 15
  lower := (1159867/26330000)
  upper := (1165133/26330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_15.interval_proof
}

def entry_35_16 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 16
  lower := (15514261/357390000)
  upper := (15585739/357390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_16.interval_proof
}

def entry_35_17 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 17
  lower := (4729103/108970000)
  upper := (4750897/108970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_17.interval_proof
}

def entry_35_18 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 18
  lower := (11263511/264890000)
  upper := (11316489/264890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_18.interval_proof
}

def entry_35_19 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 19
  lower := (2254483/55170000)
  upper := (2265517/55170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_19.interval_proof
}

def entry_35_20 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 20
  lower := (38742621/973790000)
  upper := (38937379/973790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_20.interval_proof
}

def entry_35_21 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 21
  lower := (1792277/45980000)
  upper := (1801473/45980000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_21.interval_proof
}

def entry_35_22 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 22
  lower := (18571327/486730000)
  upper := (18668673/486730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_22.interval_proof
}

def entry_35_23 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 23
  lower := (18271511/484890000)
  upper := (18368489/484890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_23.interval_proof
}

def entry_35_24 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 24
  lower := (27575481/745190000)
  upper := (27724519/745190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_24.interval_proof
}

def entry_35_25 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 25
  lower := (18898109/518910000)
  upper := (19001891/518910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_25.interval_proof
}

def entry_35_26 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 26
  lower := (19595521/544790000)
  upper := (19704479/544790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_26.interval_proof
}

def entry_35_27 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 27
  lower := (8860057/249430000)
  upper := (8909943/249430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_27.interval_proof
}

def entry_35_28 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 28
  lower := (16752461/475390000)
  upper := (16847539/475390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_28.interval_proof
}

def entry_35_29 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 29
  lower := (12259887/351130000)
  upper := (12330113/351130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_29.interval_proof
}

def entry_35_30 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 30
  lower := (9243389/266110000)
  upper := (9296611/266110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_30.interval_proof
}

def entry_35_31 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 31
  lower := (16671829/481710000)
  upper := (16768171/481710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_31.interval_proof
}

def entry_35_32 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 32
  lower := (1774871/51290000)
  upper := (1785129/51290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_32.interval_proof
}

def entry_35_33 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 33
  lower := (27012227/777730000)
  upper := (27167773/777730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_33.interval_proof
}

def entry_35_34 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 34
  lower := (2337333/66670000)
  upper := (2350667/66670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_34.interval_proof
}

def entry_35_35 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 35
  lower := (11328461/315390000)
  upper := (11391539/315390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_35.interval_proof
}

def entry_35_36 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 36
  lower := (14622113/428870000)
  upper := (14707887/428870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_36.interval_proof
}

def entry_35_37 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 37
  lower := (17975317/546830000)
  upper := (18084683/546830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_37.interval_proof
}

def entry_35_38 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 38
  lower := (25310607/793930000)
  upper := (25469393/793930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_38.interval_proof
}

def entry_35_39 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 39
  lower := (5512239/177610000)
  upper := (5547761/177610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_39.interval_proof
}

def entry_35_40 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 40
  lower := (2630321/86790000)
  upper := (2647679/86790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_40.interval_proof
}

def entry_35_41 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 41
  lower := (14979463/505370000)
  upper := (15080537/505370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_41.interval_proof
}

def entry_35_42 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 42
  lower := (4982859/171410000)
  upper := (5017141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_42.interval_proof
}

def entry_35_43 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 43
  lower := (24175179/848210000)
  upper := (24344821/848210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_43.interval_proof
}

def entry_35_44 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 44
  lower := (5348411/190890000)
  upper := (5386589/190890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_44.interval_proof
}

def entry_35_45 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 45
  lower := (3816147/138530000)
  upper := (3843853/138530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_45.interval_proof
}

def entry_35_46 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 46
  lower := (26980551/994490000)
  upper := (27179449/994490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_46.interval_proof
}

def entry_35_47 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 47
  lower := (200351/7490000)
  upper := (201849/7490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_47.interval_proof
}

def entry_35_48 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 48
  lower := (16168583/614170000)
  upper := (16291417/614170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_48.interval_proof
}

def entry_35_49 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 49
  lower := (4664549/179510000)
  upper := (4700451/179510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_49.interval_proof
}

def entry_35_50 : GramEntryIntervalCertificate :=
{
  h := 35
  k := 50
  lower := (16007581/624190000)
  upper := (16132419/624190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_35_50.interval_proof
}

def entry_36_1 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 1
  lower := (18107693/223070000)
  upper := (18152307/223070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_1.interval_proof
}

def entry_36_2 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 2
  lower := (6770551/94490000)
  upper := (6789449/94490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_2.interval_proof
}

def entry_36_3 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 3
  lower := (47617991/720090000)
  upper := (47762009/720090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_3.interval_proof
}

def entry_36_4 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 4
  lower := (20387243/327570000)
  upper := (20452757/327570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_4.interval_proof
}

def entry_36_5 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 5
  lower := (11111071/189290000)
  upper := (11148929/189290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_5.interval_proof
}

def entry_36_6 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 6
  lower := (31135201/547990000)
  upper := (31244799/547990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_6.interval_proof
}

def entry_36_7 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 7
  lower := (48739947/900530000)
  upper := (48920053/900530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_7.interval_proof
}

def entry_36_8 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 8
  lower := (8286091/159090000)
  upper := (8317909/159090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_8.interval_proof
}

def entry_36_9 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 9
  lower := (16847287/327130000)
  upper := (16912713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_9.interval_proof
}

def entry_36_10 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 10
  lower := (7985639/163610000)
  upper := (8018361/163610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_10.interval_proof
}

def entry_36_11 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 11
  lower := (27252747/572530000)
  upper := (27367253/572530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_11.interval_proof
}

def entry_36_12 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 12
  lower := (37910717/792830000)
  upper := (38069283/792830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_12.interval_proof
}

def entry_36_13 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 13
  lower := (22570103/498970000)
  upper := (22669897/498970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_13.interval_proof
}

def entry_36_14 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 14
  lower := (41336101/938990000)
  upper := (41523899/938990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_14.interval_proof
}

def entry_36_15 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 15
  lower := (12481037/289630000)
  upper := (12538963/289630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_15.interval_proof
}

def entry_36_16 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 16
  lower := (671667/15830000)
  upper := (674833/15830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_16.interval_proof
}

def entry_36_17 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 17
  lower := (20296787/482130000)
  upper := (20393213/482130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_17.interval_proof
}

def entry_36_18 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 18
  lower := (18890863/441370000)
  upper := (18979137/441370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_18.interval_proof
}

def entry_36_19 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 19
  lower := (6100927/150730000)
  upper := (6131073/150730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_19.interval_proof
}

def entry_36_20 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 20
  lower := (4299039/109610000)
  upper := (4320961/109610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_20.interval_proof
}

def entry_36_21 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 21
  lower := (20695919/540810000)
  upper := (20804081/540810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_21.interval_proof
}

def entry_36_22 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 22
  lower := (16032257/427430000)
  upper := (16117743/427430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_22.interval_proof
}

def entry_36_23 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 23
  lower := (1385743/37570000)
  upper := (1393257/37570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_23.interval_proof
}

def entry_36_24 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 24
  lower := (4876697/133030000)
  upper := (4903303/133030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_24.interval_proof
}

def entry_36_25 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 25
  lower := (10341087/289130000)
  upper := (10398913/289130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_25.interval_proof
}

def entry_36_26 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 26
  lower := (13491719/382810000)
  upper := (13568281/382810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_26.interval_proof
}

def entry_36_27 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 27
  lower := (12603937/360630000)
  upper := (12676063/360630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_27.interval_proof
}

def entry_36_28 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 28
  lower := (5837061/169390000)
  upper := (5870939/169390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_28.interval_proof
}

def entry_36_29 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 29
  lower := (6385307/186930000)
  upper := (6422693/186930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_29.interval_proof
}

def entry_36_30 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 30
  lower := (17448577/514230000)
  upper := (17551423/514230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_30.interval_proof
}

def entry_36_31 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 31
  lower := (33510657/993430000)
  upper := (33709343/993430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_31.interval_proof
}

def entry_36_32 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 32
  lower := (6638271/197290000)
  upper := (6677729/197290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_32.interval_proof
}

def entry_36_33 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 33
  lower := (30708737/912630000)
  upper := (30891263/912630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_33.interval_proof
}

def entry_36_34 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 34
  lower := (16815217/497830000)
  upper := (16914783/497830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_34.interval_proof
}

def entry_36_35 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 35
  lower := (14622113/428870000)
  upper := (14707887/428870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_35.interval_proof
}

def entry_36_36 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 36
  lower := (3136019/89810000)
  upper := (3153981/89810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_36.interval_proof
}

def entry_36_37 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 37
  lower := (9566171/288290000)
  upper := (9623829/288290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_37.interval_proof
}

def entry_36_38 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 38
  lower := (4750163/148370000)
  upper := (4779837/148370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_38.interval_proof
}

def entry_36_39 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 39
  lower := (1305797/42030000)
  upper := (1314203/42030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_39.interval_proof
}

def entry_36_40 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 40
  lower := (1723679/56960000)
  upper := (1735071/56960000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_40.interval_proof
}

def entry_36_41 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 41
  lower := (2023153/68470000)
  upper := (2036847/68470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_41.interval_proof
}

def entry_36_42 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 42
  lower := (25342399/876010000)
  upper := (25517601/876010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_42.interval_proof
}

def entry_36_43 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 43
  lower := (21255023/749770000)
  upper := (21404977/749770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_43.interval_proof
}

def entry_36_44 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 44
  lower := (1330219/47810000)
  upper := (1339781/47810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_44.interval_proof
}

def entry_36_45 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 45
  lower := (20794071/759290000)
  upper := (20945929/759290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_45.interval_proof
}

def entry_36_46 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 46
  lower := (26083011/969890000)
  upper := (26276989/969890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_46.interval_proof
}

def entry_36_47 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 47
  lower := (20582293/777070000)
  upper := (20737707/777070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_47.interval_proof
}

def entry_36_48 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 48
  lower := (3147979/120210000)
  upper := (3172021/120210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_48.interval_proof
}

def entry_36_49 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 49
  lower := (4024359/156410000)
  upper := (4055641/156410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_49.interval_proof
}

def entry_36_50 : GramEntryIntervalCertificate :=
{
  h := 36
  k := 50
  lower := (25360057/999430000)
  upper := (25559943/999430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_36_50.interval_proof
}

def entry_37_1 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 1
  lower := (2290713/28870000)
  upper := (2296487/28870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_1.interval_proof
}

def entry_37_2 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 2
  lower := (12552031/179690000)
  upper := (12587969/179690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_2.interval_proof
}

def entry_37_3 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 3
  lower := (3872981/60190000)
  upper := (3885019/60190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_3.interval_proof
}

def entry_37_4 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 4
  lower := (1817931/30065000)
  upper := (227993/3758125)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_4.interval_proof
}

def entry_37_5 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 5
  lower := (5869769/102310000)
  upper := (5890231/102310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_5.interval_proof
}

def entry_37_6 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 6
  lower := (35934733/652670000)
  upper := (36065267/652670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_6.interval_proof
}

def entry_37_7 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 7
  lower := (48069017/909830000)
  upper := (48250983/909830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_7.interval_proof
}

def entry_37_8 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 8
  lower := (43554487/855130000)
  upper := (43725513/855130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_8.interval_proof
}

def entry_37_9 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 9
  lower := (49260983/990170000)
  upper := (49459017/990170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_9.interval_proof
}

def entry_37_10 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 10
  lower := (6596231/137690000)
  upper := (6623769/137690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_10.interval_proof
}

def entry_37_11 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 11
  lower := (41800289/897110000)
  upper := (41979711/897110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_11.interval_proof
}

def entry_37_12 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 12
  lower := (16623917/360830000)
  upper := (16696083/360830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_12.interval_proof
}

def entry_37_13 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 13
  lower := (21571627/483730000)
  upper := (21668373/483730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_13.interval_proof
}

def entry_37_14 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 14
  lower := (27127231/627690000)
  upper := (27252769/627690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_14.interval_proof
}

def entry_37_15 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 15
  lower := (26716867/631330000)
  upper := (26843133/631330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_15.interval_proof
}

def entry_37_16 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 16
  lower := (11133181/268190000)
  upper := (11186819/268190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_16.interval_proof
}

def entry_37_17 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 17
  lower := (6554027/159730000)
  upper := (6585973/159730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_17.interval_proof
}

def entry_37_18 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 18
  lower := (3880549/94510000)
  upper := (3899451/94510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_18.interval_proof
}

def entry_37_19 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 19
  lower := (7229549/179510000)
  upper := (7265451/179510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_19.interval_proof
}

def entry_37_20 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 20
  lower := (7464737/192630000)
  upper := (7503263/192630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_20.interval_proof
}

def entry_37_21 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 21
  lower := (3353111/88890000)
  upper := (3370889/88890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_21.interval_proof
}

def entry_37_22 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 22
  lower := (15797233/427670000)
  upper := (15882767/427670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_22.interval_proof
}

def entry_37_23 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 23
  lower := (7008161/193390000)
  upper := (7046839/193390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_23.interval_proof
}

def entry_37_24 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 24
  lower := (14419643/403570000)
  upper := (14500357/403570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_24.interval_proof
}

def entry_37_25 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 25
  lower := (20601609/583910000)
  upper := (20718391/583910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_25.interval_proof
}

def entry_37_26 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 26
  lower := (34290977/990230000)
  upper := (34489023/990230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_26.interval_proof
}

def entry_37_27 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 27
  lower := (6261677/183230000)
  upper := (6298323/183230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_27.interval_proof
}

def entry_37_28 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 28
  lower := (2367003/69970000)
  upper := (2380997/69970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_28.interval_proof
}

def entry_37_29 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 29
  lower := (33160849/991510000)
  upper := (33359151/991510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_29.interval_proof
}

def entry_37_30 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 30
  lower := (14600983/440170000)
  upper := (14689017/440170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_30.interval_proof
}

def entry_37_31 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 31
  lower := (27466657/833430000)
  upper := (27633343/833430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_31.interval_proof
}

def entry_37_32 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 32
  lower := (15652277/477230000)
  upper := (15747723/477230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_32.interval_proof
}

def entry_37_33 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 33
  lower := (12481857/381430000)
  upper := (12558143/381430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_33.interval_proof
}

def entry_37_34 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 34
  lower := (30606513/934870000)
  upper := (30793487/934870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_34.interval_proof
}

def entry_37_35 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 35
  lower := (17975317/546830000)
  upper := (18084683/546830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_35.interval_proof
}

def entry_37_36 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 36
  lower := (9566171/288290000)
  upper := (9623829/288290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_36.interval_proof
}

def entry_37_37 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 37
  lower := (3051019/89810000)
  upper := (3068981/89810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_37.interval_proof
}

def entry_37_38 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 38
  lower := (1409389/43610000)
  upper := (1418111/43610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_38.interval_proof
}

def entry_37_39 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 39
  lower := (14448693/463070000)
  upper := (14541307/463070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_39.interval_proof
}

def entry_37_40 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 40
  lower := (17990611/593890000)
  upper := (18109389/593890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_40.interval_proof
}

def entry_37_41 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 41
  lower := (14660331/496690000)
  upper := (14759669/496690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_41.interval_proof
}

def entry_37_42 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 42
  lower := (5550749/192510000)
  upper := (5589251/192510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_42.interval_proof
}

def entry_37_43 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 43
  lower := (12864427/455730000)
  upper := (12955573/455730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_43.interval_proof
}

def entry_37_44 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 44
  lower := (25657293/927070000)
  upper := (25842707/927070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_44.interval_proof
}

def entry_37_45 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 45
  lower := (4700201/172990000)
  upper := (4734799/172990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_45.interval_proof
}

def entry_37_46 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 46
  lower := (2647593/99070000)
  upper := (2667407/99070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_46.interval_proof
}

def entry_37_47 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 47
  lower := (24307501/924990000)
  upper := (24492499/924990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_47.interval_proof
}

def entry_37_48 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 48
  lower := (16167529/624710000)
  upper := (16292471/624710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_48.interval_proof
}

def entry_37_49 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 49
  lower := (22790783/892170000)
  upper := (22969217/892170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_49.interval_proof
}

def entry_37_50 : GramEntryIntervalCertificate :=
{
  h := 37
  k := 50
  lower := (1245551/49490000)
  upper := (1255449/49490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_37_50.interval_proof
}

def entry_38_1 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 1
  lower := (24708161/318390000)
  upper := (24771839/318390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_1.interval_proof
}

def entry_38_2 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 2
  lower := (1130851/16490000)
  upper := (1134149/16490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_2.interval_proof
}

def entry_38_3 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 3
  lower := (42292867/671330000)
  upper := (42427133/671330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_3.interval_proof
}

def entry_38_4 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 4
  lower := (43945793/742070000)
  upper := (44094207/742070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_4.interval_proof
}

def entry_38_5 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 5
  lower := (49422073/879270000)
  upper := (49597927/879270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_5.interval_proof
}

def entry_38_6 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 6
  lower := (4672321/86790000)
  upper := (4689679/86790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_6.interval_proof
}

def entry_38_7 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 7
  lower := (31459193/608070000)
  upper := (31580807/608070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_7.interval_proof
}

def entry_38_8 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 8
  lower := (41227603/823970000)
  upper := (41392397/823970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_8.interval_proof
}

def entry_38_9 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 9
  lower := (2837903/58470000)
  upper := (2849597/58470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_9.interval_proof
}

def entry_38_10 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 10
  lower := (18859987/400130000)
  upper := (18940013/400130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_10.interval_proof
}

def entry_38_11 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 11
  lower := (528843/11570000)
  upper := (531157/11570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_11.interval_proof
}

def entry_38_12 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 12
  lower := (8236647/183530000)
  upper := (8273353/183530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_12.interval_proof
}

def entry_38_13 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 13
  lower := (20498557/464430000)
  upper := (20591443/464430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_13.interval_proof
}

def entry_38_14 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 14
  lower := (29869709/702910000)
  upper := (30010291/702910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_14.interval_proof
}

def entry_38_15 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 15
  lower := (31334581/754190000)
  upper := (31485419/754190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_15.interval_proof
}

def entry_38_16 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 16
  lower := (18270097/449030000)
  upper := (18359903/449030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_16.interval_proof
}

def entry_38_17 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 17
  lower := (201373/5020000)
  upper := (202377/5020000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_17.interval_proof
}

def entry_38_18 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 18
  lower := (12518609/313910000)
  upper := (12581391/313910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_18.interval_proof
}

def entry_38_19 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 19
  lower := (2952717/72830000)
  upper := (2967283/72830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_19.interval_proof
}

def entry_38_20 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 20
  lower := (4625461/120390000)
  upper := (4649539/120390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_20.interval_proof
}

def entry_38_21 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 21
  lower := (30627761/822390000)
  upper := (30792239/822390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_21.interval_proof
}

def entry_38_22 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 22
  lower := (807779/22210000)
  upper := (812221/22210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_22.interval_proof
}

def entry_38_23 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 23
  lower := (8837739/247610000)
  upper := (8887261/247610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_23.interval_proof
}

def entry_38_24 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 24
  lower := (1483271/42290000)
  upper := (1491729/42290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_24.interval_proof
}

def entry_38_25 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 25
  lower := (22874069/659310000)
  upper := (23005931/659310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_25.interval_proof
}

def entry_38_26 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 26
  lower := (9247891/271090000)
  upper := (9302109/271090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_26.interval_proof
}

def entry_38_27 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 27
  lower := (5409889/161110000)
  upper := (5442111/161110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_27.interval_proof
}

def entry_38_28 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 28
  lower := (9915119/298810000)
  upper := (9974881/298810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_28.interval_proof
}

def entry_38_29 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 29
  lower := (30008583/914170000)
  upper := (30191417/914170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_29.interval_proof
}

def entry_38_30 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 30
  lower := (24135749/742510000)
  upper := (24284251/742510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_30.interval_proof
}

def entry_38_31 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 31
  lower := (2618879/81210000)
  upper := (2635121/81210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_31.interval_proof
}

def entry_38_32 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 32
  lower := (16817533/524670000)
  upper := (16922467/524670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_32.interval_proof
}

def entry_38_33 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 33
  lower := (4667377/146230000)
  upper := (4696623/146230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_33.interval_proof
}

def entry_38_34 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 34
  lower := (4621493/145070000)
  upper := (4650507/145070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_34.interval_proof
}

def entry_38_35 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 35
  lower := (25310607/793930000)
  upper := (25469393/793930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_35.interval_proof
}

def entry_38_36 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 36
  lower := (4750163/148370000)
  upper := (4779837/148370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_36.interval_proof
}

def entry_38_37 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 37
  lower := (1409389/43610000)
  upper := (1418111/43610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_37.interval_proof
}

def entry_38_38 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 38
  lower := (7081091/214090000)
  upper := (7123909/214090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_38.interval_proof
}

def entry_38_39 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 39
  lower := (6145489/195110000)
  upper := (6184511/195110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_39.interval_proof
}

def entry_38_40 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 40
  lower := (27140809/891910000)
  upper := (27319191/891910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_40.interval_proof
}

def entry_38_41 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 41
  lower := (29460329/996710000)
  upper := (29659671/996710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_41.interval_proof
}

def entry_38_42 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 42
  lower := (27046127/938730000)
  upper := (27233873/938730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_42.interval_proof
}

def entry_38_43 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 43
  lower := (11030821/391790000)
  upper := (11109179/391790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_43.interval_proof
}

def entry_38_44 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 44
  lower := (442769/16060000)
  upper := (445981/16060000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_44.interval_proof
}

def entry_38_45 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 45
  lower := (18421867/681330000)
  upper := (18558133/681330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_45.interval_proof
}

def entry_38_46 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 46
  lower := (7048457/265430000)
  upper := (7101543/265430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_46.interval_proof
}

def entry_38_47 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 47
  lower := (25791229/987710000)
  upper := (25988771/987710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_47.interval_proof
}

def entry_38_48 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 48
  lower := (24185881/941190000)
  upper := (24374119/941190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_48.interval_proof
}

def entry_38_49 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 49
  lower := (952237/37630000)
  upper := (959763/37630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_49.interval_proof
}

def entry_38_50 : GramEntryIntervalCertificate :=
{
  h := 38
  k := 50
  lower := (850991/34090000)
  upper := (857809/34090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_38_50.interval_proof
}

def entry_39_1 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 1
  lower := (26080657/343430000)
  upper := (26149343/343430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_1.interval_proof
}

def entry_39_2 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 2
  lower := (10803861/161390000)
  upper := (10836139/161390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_2.interval_proof
}

def entry_39_3 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 3
  lower := (17841241/287590000)
  upper := (17898759/287590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_3.interval_proof
}

def entry_39_4 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 4
  lower := (2680381/46190000)
  upper := (2689619/46190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_4.interval_proof
}

def entry_39_5 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 5
  lower := (53652783/972170000)
  upper := (53847217/972170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_5.interval_proof
}

def entry_39_6 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 6
  lower := (46761459/885410000)
  upper := (46938541/885410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_6.interval_proof
}

def entry_39_7 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 7
  lower := (25250233/497670000)
  upper := (25349767/497670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_7.interval_proof
}

def entry_39_8 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 8
  lower := (4020591/81590000)
  upper := (4036909/81590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_8.interval_proof
}

def entry_39_9 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 9
  lower := (16969311/356890000)
  upper := (17040689/356890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_9.interval_proof
}

def entry_39_10 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 10
  lower := (9280051/199490000)
  upper := (9319949/199490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_10.interval_proof
}

def entry_39_11 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 11
  lower := (41886633/933670000)
  upper := (42073367/933670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_11.interval_proof
}

def entry_39_12 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 12
  lower := (35309559/804410000)
  upper := (35470441/804410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_12.interval_proof
}

def entry_39_13 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 13
  lower := (34970757/792430000)
  upper := (35129243/792430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_13.interval_proof
}

def entry_39_14 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 14
  lower := (783129/18710000)
  upper := (786871/18710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_14.interval_proof
}

def entry_39_15 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 15
  lower := (38595341/946590000)
  upper := (38784659/946590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_15.interval_proof
}

def entry_39_16 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 16
  lower := (37994907/950930000)
  upper := (38185093/950930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_16.interval_proof
}

def entry_39_17 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 17
  lower := (4118269/104810000)
  upper := (4139231/104810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_17.interval_proof
}

def entry_39_18 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 18
  lower := (8106667/208330000)
  upper := (8148333/208330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_18.interval_proof
}

def entry_39_19 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 19
  lower := (6868371/176290000)
  upper := (6903629/176290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_19.interval_proof
}

def entry_39_20 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 20
  lower := (36454699/953010000)
  upper := (36645301/953010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_20.interval_proof
}

def entry_39_21 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 21
  lower := (736003/19970000)
  upper := (739997/19970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_21.interval_proof
}

def entry_39_22 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 22
  lower := (21280701/592990000)
  upper := (21399299/592990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_22.interval_proof
}

def entry_39_23 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 23
  lower := (26494613/753870000)
  upper := (26645387/753870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_23.interval_proof
}

def entry_39_24 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 24
  lower := (18207249/527510000)
  upper := (18312751/527510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_24.interval_proof
}

def entry_39_25 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 25
  lower := (32354849/951510000)
  upper := (32545151/951510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_25.interval_proof
}

def entry_39_26 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 26
  lower := (20319937/600630000)
  upper := (20440063/600630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_26.interval_proof
}

def entry_39_27 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 27
  lower := (5642929/170710000)
  upper := (5677071/170710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_27.interval_proof
}

def entry_39_28 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 28
  lower := (30426651/933490000)
  upper := (30613349/933490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_28.interval_proof
}

def entry_39_29 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 29
  lower := (20825453/645470000)
  upper := (20954547/645470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_29.interval_proof
}

def entry_39_30 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 30
  lower := (7648523/239770000)
  upper := (7696477/239770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_30.interval_proof
}

def entry_39_31 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 31
  lower := (6696327/211730000)
  upper := (6738673/211730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_31.interval_proof
}

def entry_39_32 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 32
  lower := (2265281/72190000)
  upper := (2279719/72190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_32.interval_proof
}

def entry_39_33 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 33
  lower := (27282571/874290000)
  upper := (27457429/874290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_33.interval_proof
}

def entry_39_34 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 34
  lower := (246831/7940000)
  upper := (248419/7940000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_34.interval_proof
}

def entry_39_35 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 35
  lower := (5512239/177610000)
  upper := (5547761/177610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_35.interval_proof
}

def entry_39_36 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 36
  lower := (1305797/42030000)
  upper := (1314203/42030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_36.interval_proof
}

def entry_39_37 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 37
  lower := (14448693/463070000)
  upper := (14541307/463070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_37.interval_proof
}

def entry_39_38 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 38
  lower := (6145489/195110000)
  upper := (6184511/195110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_38.interval_proof
}

def entry_39_39 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 39
  lower := (22480239/697610000)
  upper := (22619761/697610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_39.interval_proof
}

def entry_39_40 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 40
  lower := (5450257/177430000)
  upper := (5485743/177430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_40.interval_proof
}

def entry_39_41 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 41
  lower := (908503/30595000)
  upper := (457311/15297500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_41.interval_proof
}

def entry_39_42 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 42
  lower := (26876869/931310000)
  upper := (27063131/931310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_42.interval_proof
}

def entry_39_43 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 43
  lower := (120721/4290000)
  upper := (121579/4290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_43.interval_proof
}

def entry_39_44 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 44
  lower := (3629307/131930000)
  upper := (3655693/131930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_44.interval_proof
}

def entry_39_45 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 45
  lower := (6329011/234890000)
  upper := (6375989/234890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_45.interval_proof
}

def entry_39_46 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 46
  lower := (18370497/695030000)
  upper := (18509503/695030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_46.interval_proof
}

def entry_39_47 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 47
  lower := (3705731/142690000)
  upper := (3734269/142690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_47.interval_proof
}

def entry_39_48 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 48
  lower := (1378601/53990000)
  upper := (1389399/53990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_48.interval_proof
}

def entry_39_49 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 49
  lower := (21404881/851190000)
  upper := (21575119/851190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_49.interval_proof
}

def entry_39_50 : GramEntryIntervalCertificate :=
{
  h := 39
  k := 50
  lower := (3326563/134370000)
  upper := (3353437/134370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_39_50.interval_proof
}

def entry_40_1 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 1
  lower := (7366343/99070000)
  upper := (7386157/99070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_1.interval_proof
}

def entry_40_2 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 2
  lower := (59749163/908370000)
  upper := (59930837/908370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_2.interval_proof
}

def entry_40_3 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 3
  lower := (170281/2815000)
  upper := (42711/703750)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_3.interval_proof
}

def entry_40_4 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 4
  lower := (20339493/355070000)
  upper := (20410507/355070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_4.interval_proof
}

def entry_40_5 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 5
  lower := (42731707/782930000)
  upper := (42888293/782930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_5.interval_proof
}

def entry_40_6 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 6
  lower := (18798689/363110000)
  upper := (18871311/363110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_6.interval_proof
}

def entry_40_7 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 7
  lower := (47015637/943630000)
  upper := (47204363/943630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_7.interval_proof
}

def entry_40_8 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 8
  lower := (26116657/533430000)
  upper := (26223343/533430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_8.interval_proof
}

def entry_40_9 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 9
  lower := (2338109/50160000)
  upper := (2348141/50160000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_9.interval_proof
}

def entry_40_10 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 10
  lower := (10908959/235410000)
  upper := (10956041/235410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_10.interval_proof
}

def entry_40_11 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 11
  lower := (295569/6710000)
  upper := (296911/6710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_11.interval_proof
}

def entry_40_12 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 12
  lower := (37014009/859910000)
  upper := (37185991/859910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_12.interval_proof
}

def entry_40_13 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 13
  lower := (6708259/157410000)
  upper := (6739741/157410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_13.interval_proof
}

def entry_40_14 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 14
  lower := (38975703/942970000)
  upper := (39164297/942970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_14.interval_proof
}

def entry_40_15 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 15
  lower := (30863129/768710000)
  upper := (31016871/768710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_15.interval_proof
}

def entry_40_16 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 16
  lower := (4552211/115390000)
  upper := (4575289/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_16.interval_proof
}

def entry_40_17 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 17
  lower := (28127059/729410000)
  upper := (28272941/729410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_17.interval_proof
}

def entry_40_18 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 18
  lower := (3453427/90730000)
  upper := (3471573/90730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_18.interval_proof
}

def entry_40_19 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 19
  lower := (25602411/675890000)
  upper := (25737589/675890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_19.interval_proof
}

def entry_40_20 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 20
  lower := (2804717/72830000)
  upper := (2819283/72830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_20.interval_proof
}

def entry_40_21 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 21
  lower := (441293/12070000)
  upper := (443707/12070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_21.interval_proof
}

def entry_40_22 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 22
  lower := (19225797/542030000)
  upper := (19334203/542030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_22.interval_proof
}

def entry_40_23 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 23
  lower := (161883/4670000)
  upper := (162817/4670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_23.interval_proof
}

def entry_40_24 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 24
  lower := (10055507/294930000)
  upper := (10114493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_24.interval_proof
}

def entry_40_25 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 25
  lower := (12223471/365290000)
  upper := (12296529/365290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_25.interval_proof
}

def entry_40_26 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 26
  lower := (1324739/40110000)
  upper := (1332761/40110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_26.interval_proof
}

def entry_40_27 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 27
  lower := (27505753/842470000)
  upper := (27674247/842470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_27.interval_proof
}

def entry_40_28 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 28
  lower := (3686509/114910000)
  upper := (3709491/114910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_28.interval_proof
}

def entry_40_29 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 29
  lower := (28669469/905310000)
  upper := (28850531/905310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_29.interval_proof
}

def entry_40_30 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 30
  lower := (1259993/40070000)
  upper := (1268007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_30.interval_proof
}

def entry_40_31 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 31
  lower := (28258921/910790000)
  upper := (28441079/910790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_31.interval_proof
}

def entry_40_32 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 32
  lower := (14652461/475390000)
  upper := (14747539/475390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_32.interval_proof
}

def entry_40_33 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 33
  lower := (11178421/365790000)
  upper := (11251579/365790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_33.interval_proof
}

def entry_40_34 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 34
  lower := (21499279/707210000)
  upper := (21640721/707210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_34.interval_proof
}

def entry_40_35 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 35
  lower := (2630321/86790000)
  upper := (2647679/86790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_35.interval_proof
}

def entry_40_36 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 36
  lower := (1723679/56960000)
  upper := (1735071/56960000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_36.interval_proof
}

def entry_40_37 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 37
  lower := (17990611/593890000)
  upper := (18109389/593890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_37.interval_proof
}

def entry_40_38 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 38
  lower := (27140809/891910000)
  upper := (27319191/891910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_38.interval_proof
}

def entry_40_39 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 39
  lower := (5450257/177430000)
  upper := (5485743/177430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_39.interval_proof
}

def entry_40_40 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 40
  lower := (9908461/315390000)
  upper := (9971539/315390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_40.interval_proof
}

def entry_40_41 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 41
  lower := (24418539/814610000)
  upper := (24581461/814610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_41.interval_proof
}

def entry_40_42 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 42
  lower := (16817/580000)
  upper := (16933/580000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_42.interval_proof
}

def entry_40_43 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 43
  lower := (229187/8130000)
  upper := (230813/8130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_43.interval_proof
}

def entry_40_44 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 44
  lower := (13077451/475490000)
  upper := (13172549/475490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_44.interval_proof
}

def entry_40_45 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 45
  lower := (14685403/545970000)
  upper := (14794597/545970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_45.interval_proof
}

def entry_40_46 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 46
  lower := (39553/1501250)
  upper := (159413/6005000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_46.interval_proof
}

def entry_40_47 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 47
  lower := (196739/7610000)
  upper := (198261/7610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_47.interval_proof
}

def entry_40_48 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 48
  lower := (4357859/171410000)
  upper := (4392141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_48.interval_proof
}

def entry_40_49 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 49
  lower := (6254963/250370000)
  upper := (6305037/250370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_49.interval_proof
}

def entry_40_50 : GramEntryIntervalCertificate :=
{
  h := 40
  k := 50
  lower := (11712461/475390000)
  upper := (11807539/475390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_40_50.interval_proof
}

end RH.Certificates.Generated.NymanGramN50
