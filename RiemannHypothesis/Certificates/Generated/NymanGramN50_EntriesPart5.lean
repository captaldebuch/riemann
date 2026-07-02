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

def entry_41_1 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 1
  lower := (56422537/774630000)
  upper := (56577463/774630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_1.interval_proof
}

def entry_41_2 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 2
  lower := (62362987/970130000)
  upper := (62557013/970130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_2.interval_proof
}

def entry_41_3 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 3
  lower := (47599747/802530000)
  upper := (47760253/802530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_3.interval_proof
}

def entry_41_4 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 4
  lower := (17598469/315310000)
  upper := (17661531/315310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_4.interval_proof
}

def entry_41_5 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 5
  lower := (15520779/292210000)
  upper := (15579221/292210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_5.interval_proof
}

def entry_41_6 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 6
  lower := (5844769/114810000)
  upper := (5867731/114810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_6.interval_proof
}

def entry_41_7 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 7
  lower := (8067557/164430000)
  upper := (8100443/164430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_7.interval_proof
}

def entry_41_8 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 8
  lower := (5499673/115770000)
  upper := (5522827/115770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_8.interval_proof
}

def entry_41_9 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 9
  lower := (45740069/999310000)
  upper := (45939931/999310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_9.interval_proof
}

def entry_41_10 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 10
  lower := (40180489/895110000)
  upper := (40359511/895110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_10.interval_proof
}

def entry_41_11 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 11
  lower := (6439141/148590000)
  upper := (6468859/148590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_11.interval_proof
}

def entry_41_12 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 12
  lower := (892261/21140000)
  upper := (896489/21140000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_12.interval_proof
}

def entry_41_13 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 13
  lower := (1534309/36910000)
  upper := (1541691/36910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_13.interval_proof
}

def entry_41_14 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 14
  lower := (38875081/949190000)
  upper := (39064919/949190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_14.interval_proof
}

def entry_41_15 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 15
  lower := (34372949/870510000)
  upper := (34547051/870510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_15.interval_proof
}

def entry_41_16 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 16
  lower := (4620031/119690000)
  upper := (4643969/119690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_16.interval_proof
}

def entry_41_17 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 17
  lower := (22031821/581790000)
  upper := (22148179/581790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_17.interval_proof
}

def entry_41_18 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 18
  lower := (25242343/676570000)
  upper := (25377657/676570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_18.interval_proof
}

def entry_41_19 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 19
  lower := (31435011/849890000)
  upper := (31604989/849890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_19.interval_proof
}

def entry_41_20 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 20
  lower := (10003013/269870000)
  upper := (10056987/269870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_20.interval_proof
}

def entry_41_21 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 21
  lower := (12096789/332110000)
  upper := (12163211/332110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_21.interval_proof
}

def entry_41_22 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 22
  lower := (27800853/791470000)
  upper := (27959147/791470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_22.interval_proof
}

def entry_41_23 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 23
  lower := (31268649/913510000)
  upper := (31451351/913510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_23.interval_proof
}

def entry_41_24 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 24
  lower := (27677457/825430000)
  upper := (27842543/825430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_24.interval_proof
}

def entry_41_25 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 25
  lower := (2472497/75030000)
  upper := (2487503/75030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_25.interval_proof
}

def entry_41_26 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 26
  lower := (439583/13545000)
  upper := (110573/3386250)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_26.interval_proof
}

def entry_41_27 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 27
  lower := (3828091/119090000)
  upper := (3851909/119090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_27.interval_proof
}

def entry_41_28 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 28
  lower := (30324157/958430000)
  upper := (30515843/958430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_28.interval_proof
}

def entry_41_29 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 29
  lower := (27980213/897870000)
  upper := (28159787/897870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_29.interval_proof
}

def entry_41_30 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 30
  lower := (184521/5990000)
  upper := (185719/5990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_30.interval_proof
}

def entry_41_31 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 31
  lower := (3650543/119570000)
  upper := (3674457/119570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_31.interval_proof
}

def entry_41_32 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 32
  lower := (3695267/122330000)
  upper := (3719733/122330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_32.interval_proof
}

def entry_41_33 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 33
  lower := (12892011/429890000)
  upper := (12977989/429890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_33.interval_proof
}

def entry_41_34 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 34
  lower := (1209689/40610000)
  upper := (1217811/40610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_34.interval_proof
}

def entry_41_35 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 35
  lower := (14979463/505370000)
  upper := (15080537/505370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_35.interval_proof
}

def entry_41_36 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 36
  lower := (2023153/68470000)
  upper := (2036847/68470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_36.interval_proof
}

def entry_41_37 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 37
  lower := (14660331/496690000)
  upper := (14759669/496690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_37.interval_proof
}

def entry_41_38 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 38
  lower := (29460329/996710000)
  upper := (29659671/996710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_38.interval_proof
}

def entry_41_39 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 39
  lower := (908503/30595000)
  upper := (457311/15297500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_39.interval_proof
}

def entry_41_40 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 40
  lower := (24418539/814610000)
  upper := (24581461/814610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_40.interval_proof
}

def entry_41_41 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 41
  lower := (21380239/697610000)
  upper := (21519761/697610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_41.interval_proof
}

def entry_41_42 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 42
  lower := (2251059/76910000)
  upper := (2266441/76910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_42.interval_proof
}

def entry_41_43 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 43
  lower := (23098457/815430000)
  upper := (23261543/815430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_43.interval_proof
}

def entry_41_44 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 44
  lower := (2923141/106090000)
  upper := (2944359/106090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_44.interval_proof
}

def entry_41_45 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 45
  lower := (3708209/137910000)
  upper := (3735791/137910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_45.interval_proof
}

def entry_41_46 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 46
  lower := (13448869/511310000)
  upper := (13551131/511310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_46.interval_proof
}

def entry_41_47 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 47
  lower := (22682009/879910000)
  upper := (22857991/879910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_47.interval_proof
}

def entry_41_48 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 48
  lower := (16534651/653490000)
  upper := (16665349/653490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_48.interval_proof
}

def entry_41_49 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 49
  lower := (4173219/167810000)
  upper := (4206781/167810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_49.interval_proof
}

def entry_41_50 : GramEntryIntervalCertificate :=
{
  h := 41
  k := 50
  lower := (22059803/901970000)
  upper := (22240197/901970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_41_50.interval_proof
}

def entry_42_1 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 1
  lower := (1234271/17290000)
  upper := (1237729/17290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_1.interval_proof
}

def entry_42_2 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 2
  lower := (5320583/84170000)
  upper := (5337417/84170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_2.interval_proof
}

def entry_42_3 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 3
  lower := (50034417/855830000)
  upper := (50205583/855830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_3.interval_proof
}

def entry_42_4 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 4
  lower := (18191783/332170000)
  upper := (18258217/332170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_4.interval_proof
}

def entry_42_5 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 5
  lower := (39534049/759510000)
  upper := (39685951/759510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_5.interval_proof
}

def entry_42_6 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 6
  lower := (43453857/861430000)
  upper := (43626143/861430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_6.interval_proof
}

def entry_42_7 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 7
  lower := (2546769/52310000)
  upper := (2557231/52310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_7.interval_proof
}

def entry_42_8 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 8
  lower := (756373/16270000)
  upper := (759627/16270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_8.interval_proof
}

def entry_42_9 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 9
  lower := (41148581/914190000)
  upper := (41331419/914190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_9.interval_proof
}

def entry_42_10 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 10
  lower := (190441/4340000)
  upper := (191309/4340000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_10.interval_proof
}

def entry_42_11 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 11
  lower := (7747863/181370000)
  upper := (7784137/181370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_11.interval_proof
}

def entry_42_12 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 12
  lower := (38088471/915290000)
  upper := (38271529/915290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_12.interval_proof
}

def entry_42_13 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 13
  lower := (4696459/115410000)
  upper := (4719541/115410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_13.interval_proof
}

def entry_42_14 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 14
  lower := (32450797/792030000)
  upper := (32609203/792030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_14.interval_proof
}

def entry_42_15 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 15
  lower := (1280713/32870000)
  upper := (1287287/32870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_15.interval_proof
}

def entry_42_16 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 16
  lower := (16426733/432670000)
  upper := (16513267/432670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_16.interval_proof
}

def entry_42_17 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 17
  lower := (30119241/807590000)
  upper := (30280759/807590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_17.interval_proof
}

def entry_42_18 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 18
  lower := (5816149/158510000)
  upper := (5847851/158510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_18.interval_proof
}

def entry_42_19 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 19
  lower := (24213137/668630000)
  upper := (24346863/668630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_19.interval_proof
}

def entry_42_20 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 20
  lower := (3482347/96530000)
  upper := (3501653/96530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_20.interval_proof
}

def entry_42_21 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 21
  lower := (16185863/441370000)
  upper := (16274137/441370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_21.interval_proof
}

def entry_42_22 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 22
  lower := (27700577/794230000)
  upper := (27859423/794230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_22.interval_proof
}

def entry_42_23 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 23
  lower := (27887639/823610000)
  upper := (28052361/823610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_23.interval_proof
}

def entry_42_24 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 24
  lower := (24635657/743430000)
  upper := (24784343/743430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_24.interval_proof
}

def entry_42_25 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 25
  lower := (12047949/370510000)
  upper := (12122051/370510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_25.interval_proof
}

def entry_42_26 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 26
  lower := (23636051/739490000)
  upper := (23783949/739490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_26.interval_proof
}

def entry_42_27 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 27
  lower := (30822289/977110000)
  upper := (31017711/977110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_27.interval_proof
}

def entry_42_28 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 28
  lower := (29246879/931210000)
  upper := (29433121/931210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_28.interval_proof
}

def entry_42_29 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 29
  lower := (1621721/52790000)
  upper := (1632279/52790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_29.interval_proof
}

def entry_42_30 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 30
  lower := (6040087/199130000)
  upper := (6079913/199130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_30.interval_proof
}

def entry_42_31 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 31
  lower := (3984717/132830000)
  upper := (4011283/132830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_31.interval_proof
}

def entry_42_32 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 32
  lower := (391339/13172500)
  upper := (787947/26345000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_32.interval_proof
}

def entry_42_33 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 33
  lower := (17331121/588790000)
  upper := (17448879/588790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_33.interval_proof
}

def entry_42_34 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 34
  lower := (17370559/594410000)
  upper := (17489441/594410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_34.interval_proof
}

def entry_42_35 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 35
  lower := (4982859/171410000)
  upper := (5017141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_35.interval_proof
}

def entry_42_36 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 36
  lower := (25342399/876010000)
  upper := (25517601/876010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_36.interval_proof
}

def entry_42_37 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 37
  lower := (5550749/192510000)
  upper := (5589251/192510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_37.interval_proof
}

def entry_42_38 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 38
  lower := (27046127/938730000)
  upper := (27233873/938730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_38.interval_proof
}

def entry_42_39 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 39
  lower := (26876869/931310000)
  upper := (27063131/931310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_39.interval_proof
}

def entry_42_40 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 40
  lower := (16817/580000)
  upper := (16933/580000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_40.interval_proof
}

def entry_42_41 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 41
  lower := (2251059/76910000)
  upper := (2266441/76910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_41.interval_proof
}

def entry_42_42 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 42
  lower := (28305383/946170000)
  upper := (28494617/946170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_42.interval_proof
}

def entry_42_43 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 43
  lower := (26317961/920390000)
  upper := (26502039/920390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_43.interval_proof
}

def entry_42_44 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 44
  lower := (3248269/117310000)
  upper := (3271731/117310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_44.interval_proof
}

def entry_42_45 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 45
  lower := (16339363/606370000)
  upper := (16460637/606370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_45.interval_proof
}

def entry_42_46 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 46
  lower := (25303803/961970000)
  upper := (25496197/961970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_46.interval_proof
}

def entry_42_47 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 47
  lower := (4861113/188870000)
  upper := (4898887/188870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_47.interval_proof
}

def entry_42_48 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 48
  lower := (9661719/382810000)
  upper := (9738281/382810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_48.interval_proof
}

def entry_42_49 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 49
  lower := (11633059/469410000)
  upper := (11726941/469410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_49.interval_proof
}

def entry_42_50 : GramEntryIntervalCertificate :=
{
  h := 42
  k := 50
  lower := (23503469/965310000)
  upper := (23696531/965310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_42_50.interval_proof
}

def entry_43_1 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 1
  lower := (60583447/865530000)
  upper := (60756553/865530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_1.interval_proof
}

def entry_43_2 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 2
  lower := (8678467/140330000)
  upper := (8706533/140330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_2.interval_proof
}

def entry_43_3 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 3
  lower := (17634121/308790000)
  upper := (17695879/308790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_3.interval_proof
}

def entry_43_4 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 4
  lower := (41882097/779030000)
  upper := (42037903/779030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_4.interval_proof
}

def entry_43_5 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 5
  lower := (29103059/569410000)
  upper := (29216941/569410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_5.interval_proof
}

def entry_43_6 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 6
  lower := (41345801/841990000)
  upper := (41514199/841990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_6.interval_proof
}

def entry_43_7 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 7
  lower := (20117513/424870000)
  upper := (20202487/424870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_7.interval_proof
}

def entry_43_8 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 8
  lower := (44672033/979670000)
  upper := (44867967/979670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_8.interval_proof
}

def entry_43_9 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 9
  lower := (1448729/32710000)
  upper := (1455271/32710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_9.interval_proof
}

def entry_43_10 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 10
  lower := (36375437/845630000)
  upper := (36544563/845630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_10.interval_proof
}

def entry_43_11 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 11
  lower := (13847219/327810000)
  upper := (13912781/327810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_11.interval_proof
}

def entry_43_12 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 12
  lower := (7595377/186230000)
  upper := (7632623/186230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_12.interval_proof
}

def entry_43_13 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 13
  lower := (3418937/85630000)
  upper := (3436063/85630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_13.interval_proof
}

def entry_43_14 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 14
  lower := (17535767/442330000)
  upper := (17624233/442330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_14.interval_proof
}

def entry_43_15 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 15
  lower := (18362319/476810000)
  upper := (18457681/476810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_15.interval_proof
}

def entry_43_16 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 16
  lower := (1055179/28210000)
  upper := (1060821/28210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_16.interval_proof
}

def entry_43_17 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 17
  lower := (27664609/753910000)
  upper := (27815391/753910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_17.interval_proof
}

def entry_43_18 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 18
  lower := (19595569/544310000)
  upper := (19704431/544310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_18.interval_proof
}

def entry_43_19 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 19
  lower := (17121803/481970000)
  upper := (17218197/481970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_19.interval_proof
}

def entry_43_20 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 20
  lower := (867539/24610000)
  upper := (872461/24610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_20.interval_proof
}

def entry_43_21 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 21
  lower := (13950533/394670000)
  upper := (14029467/394670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_21.interval_proof
}

def entry_43_22 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 22
  lower := (5538069/159310000)
  upper := (5569931/159310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_22.interval_proof
}

def entry_43_23 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 23
  lower := (17517797/522030000)
  upper := (17622203/522030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_23.interval_proof
}

def entry_43_24 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 24
  lower := (22710597/694030000)
  upper := (22849403/694030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_24.interval_proof
}

def entry_43_25 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 25
  lower := (23257467/725330000)
  upper := (23402533/725330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_25.interval_proof
}

def entry_43_26 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 26
  lower := (570691/18090000)
  upper := (574309/18090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_26.interval_proof
}

def entry_43_27 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 27
  lower := (13451679/433210000)
  upper := (13538321/433210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_27.interval_proof
}

def entry_43_28 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 28
  lower := (10924419/355810000)
  upper := (10995581/355810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_28.interval_proof
}

def entry_43_29 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 29
  lower := (5344907/175930000)
  upper := (5380093/175930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_29.interval_proof
}

def entry_43_30 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 30
  lower := (1092343/36570000)
  upper := (1099657/36570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_30.interval_proof
}

def entry_43_31 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 31
  lower := (27187861/921390000)
  upper := (27372139/921390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_31.interval_proof
}

def entry_43_32 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 32
  lower := (12183347/416530000)
  upper := (12266653/416530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_32.interval_proof
}

def entry_43_33 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 33
  lower := (839599/29010000)
  upper := (845401/29010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_33.interval_proof
}

def entry_43_34 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 34
  lower := (11898547/414530000)
  upper := (11981453/414530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_34.interval_proof
}

def entry_43_35 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 35
  lower := (24175179/848210000)
  upper := (24344821/848210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_35.interval_proof
}

def entry_43_36 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 36
  lower := (21255023/749770000)
  upper := (21404977/749770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_36.interval_proof
}

def entry_43_37 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 37
  lower := (12864427/455730000)
  upper := (12955573/455730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_37.interval_proof
}

def entry_43_38 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 38
  lower := (11030821/391790000)
  upper := (11109179/391790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_38.interval_proof
}

def entry_43_39 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 39
  lower := (120721/4290000)
  upper := (121579/4290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_39.interval_proof
}

def entry_43_40 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 40
  lower := (229187/8130000)
  upper := (230813/8130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_40.interval_proof
}

def entry_43_41 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 41
  lower := (23098457/815430000)
  upper := (23261543/815430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_41.interval_proof
}

def entry_43_42 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 42
  lower := (26317961/920390000)
  upper := (26502039/920390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_42.interval_proof
}

def entry_43_43 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 43
  lower := (15805903/540970000)
  upper := (15914097/540970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_43.interval_proof
}

def entry_43_44 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 44
  lower := (23725117/848830000)
  upper := (23894883/848830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_44.interval_proof
}

def entry_43_45 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 45
  lower := (7512259/277410000)
  upper := (7567741/277410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_45.interval_proof
}

def entry_43_46 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 46
  lower := (4626451/175490000)
  upper := (4661549/175490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_46.interval_proof
}

def entry_43_47 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 47
  lower := (1096989/42610000)
  upper := (1105511/42610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_47.interval_proof
}

def entry_43_48 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 48
  lower := (2388521/94790000)
  upper := (2407479/94790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_48.interval_proof
}

def entry_43_49 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 49
  lower := (1715059/69410000)
  upper := (1728941/69410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_49.interval_proof
}

def entry_43_50 : GramEntryIntervalCertificate :=
{
  h := 43
  k := 50
  lower := (21869869/901310000)
  upper := (22050131/901310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_43_50.interval_proof
}

def entry_44_1 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 1
  lower := (17097599/249010000)
  upper := (17147401/249010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_1.interval_proof
}

def entry_44_2 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 2
  lower := (3671467/60330000)
  upper := (3683533/60330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_2.interval_proof
}

def entry_44_3 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 3
  lower := (33989377/606230000)
  upper := (34110623/606230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_3.interval_proof
}

def entry_44_4 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 4
  lower := (37459483/705170000)
  upper := (37600517/705170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_4.interval_proof
}

def entry_44_5 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 5
  lower := (22944367/456330000)
  upper := (23035633/456330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_5.interval_proof
}

def entry_44_6 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 6
  lower := (34378611/713890000)
  upper := (34521389/713890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_6.interval_proof
}

def entry_44_7 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 7
  lower := (19662619/423810000)
  upper := (19747381/423810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_7.interval_proof
}

def entry_44_8 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 8
  lower := (36538607/813930000)
  upper := (36701393/813930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_8.interval_proof
}

def entry_44_9 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 9
  lower := (13763527/314730000)
  upper := (13826473/314730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_9.interval_proof
}

def entry_44_10 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 10
  lower := (6888697/163030000)
  upper := (6921303/163030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_10.interval_proof
}

def entry_44_11 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 11
  lower := (1596709/37910000)
  upper := (1604291/37910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_11.interval_proof
}

def entry_44_12 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 12
  lower := (18538861/461390000)
  upper := (18631139/461390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_12.interval_proof
}

def entry_44_13 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 13
  lower := (33265189/848110000)
  upper := (33434811/848110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_13.interval_proof
}

def entry_44_14 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 14
  lower := (33852577/874230000)
  upper := (34027423/874230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_14.interval_proof
}

def entry_44_15 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 15
  lower := (37751183/988170000)
  upper := (37948817/988170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_15.interval_proof
}

def entry_44_16 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 16
  lower := (895573/24270000)
  upper := (900427/24270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_16.interval_proof
}

def entry_44_17 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 17
  lower := (22796791/632090000)
  upper := (22923209/632090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_17.interval_proof
}

def entry_44_18 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 18
  lower := (10071583/284170000)
  upper := (10128417/284170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_18.interval_proof
}

def entry_44_19 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 19
  lower := (2071067/59330000)
  upper := (2082933/59330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_19.interval_proof
}

def entry_44_20 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 20
  lower := (26573089/769110000)
  upper := (26726911/769110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_20.interval_proof
}

def entry_44_21 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 21
  lower := (19782547/574530000)
  upper := (19897453/574530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_21.interval_proof
}

def entry_44_22 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 22
  lower := (28039887/801130000)
  upper := (28200113/801130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_22.interval_proof
}

def entry_44_23 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 23
  lower := (26031919/780810000)
  upper := (26188081/780810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_23.interval_proof
}

def entry_44_24 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 24
  lower := (22749787/702130000)
  upper := (22890213/702130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_24.interval_proof
}

def entry_44_25 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 25
  lower := (222501/7021250)
  upper := (895621/28085000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_25.interval_proof
}

def entry_44_26 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 26
  lower := (15869001/509990000)
  upper := (15970999/509990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_26.interval_proof
}

def entry_44_27 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 27
  lower := (1410393/46070000)
  upper := (1419607/46070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_27.interval_proof
}

def entry_44_28 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 28
  lower := (29223251/967490000)
  upper := (29416749/967490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_28.interval_proof
}

def entry_44_29 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 29
  lower := (4195987/140130000)
  upper := (4224013/140130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_29.interval_proof
}

def entry_44_30 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 30
  lower := (17002367/576330000)
  upper := (17117633/576330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_30.interval_proof
}

def entry_44_31 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 31
  lower := (2822791/97090000)
  upper := (2842209/97090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_31.interval_proof
}

def entry_44_32 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 32
  lower := (1903381/66190000)
  upper := (1916619/66190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_32.interval_proof
}

def entry_44_33 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 33
  lower := (12595923/440770000)
  upper := (12684077/440770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_33.interval_proof
}

def entry_44_34 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 34
  lower := (346273/12270000)
  upper := (348727/12270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_34.interval_proof
}

def entry_44_35 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 35
  lower := (5348411/190890000)
  upper := (5386589/190890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_35.interval_proof
}

def entry_44_36 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 36
  lower := (1330219/47810000)
  upper := (1339781/47810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_36.interval_proof
}

def entry_44_37 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 37
  lower := (25657293/927070000)
  upper := (25842707/927070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_37.interval_proof
}

def entry_44_38 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 38
  lower := (442769/16060000)
  upper := (445981/16060000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_38.interval_proof
}

def entry_44_39 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 39
  lower := (3629307/131930000)
  upper := (3655693/131930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_39.interval_proof
}

def entry_44_40 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 40
  lower := (13077451/475490000)
  upper := (13172549/475490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_40.interval_proof
}

def entry_44_41 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 41
  lower := (2923141/106090000)
  upper := (2944359/106090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_41.interval_proof
}

def entry_44_42 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 42
  lower := (3248269/117310000)
  upper := (3271731/117310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_42.interval_proof
}

def entry_44_43 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 43
  lower := (23725117/848830000)
  upper := (23894883/848830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_43.interval_proof
}

def entry_44_44 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 44
  lower := (3876423/135770000)
  upper := (3903577/135770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_44.interval_proof
}

def entry_44_45 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 45
  lower := (2944229/107710000)
  upper := (2965771/107710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_45.interval_proof
}

def entry_44_46 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 46
  lower := (866729/32710000)
  upper := (873271/32710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_46.interval_proof
}

def entry_44_47 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 47
  lower := (16187273/627270000)
  upper := (16312727/627270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_47.interval_proof
}

def entry_44_48 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 48
  lower := (7669579/304210000)
  upper := (7730421/304210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_48.interval_proof
}

def entry_44_49 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 49
  lower := (11662747/472530000)
  upper := (11757253/472530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_49.interval_proof
}

def entry_44_50 : GramEntryIntervalCertificate :=
{
  h := 44
  k := 50
  lower := (11875939/490610000)
  upper := (11974061/490610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_44_50.interval_proof
}

def entry_45_1 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 1
  lower := (58483207/867930000)
  upper := (58656793/867930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_1.interval_proof
}

def entry_45_2 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 2
  lower := (56764751/952490000)
  upper := (56955249/952490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_2.interval_proof
}

def entry_45_3 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 3
  lower := (53752817/971830000)
  upper := (53947183/971830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_3.interval_proof
}

def entry_45_4 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 4
  lower := (21338869/411310000)
  upper := (21421131/411310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_4.interval_proof
}

def entry_45_5 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 5
  lower := (44690207/897930000)
  upper := (44869793/897930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_5.interval_proof
}

def entry_45_6 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 6
  lower := (8394773/177270000)
  upper := (8430227/177270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_6.interval_proof
}

def entry_45_7 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 7
  lower := (4649797/102030000)
  upper := (4670203/102030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_7.interval_proof
}

def entry_45_8 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 8
  lower := (3411259/77410000)
  upper := (3426741/77410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_8.interval_proof
}

def entry_45_9 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 9
  lower := (42761717/982830000)
  upper := (42958283/982830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_9.interval_proof
}

def entry_45_10 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 10
  lower := (1503889/36110000)
  upper := (1511111/36110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_10.interval_proof
}

def entry_45_11 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 11
  lower := (35273743/862570000)
  upper := (35446257/862570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_11.interval_proof
}

def entry_45_12 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 12
  lower := (24099113/608870000)
  upper := (24220887/608870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_12.interval_proof
}

def entry_45_13 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 13
  lower := (4076941/105590000)
  upper := (4098059/105590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_13.interval_proof
}

def entry_45_14 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 14
  lower := (8871619/233810000)
  upper := (8918381/233810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_14.interval_proof
}

def entry_45_15 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 15
  lower := (2757787/72130000)
  upper := (2772213/72130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_15.interval_proof
}

def entry_45_16 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 16
  lower := (6534561/179390000)
  upper := (6570439/179390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_16.interval_proof
}

def entry_45_17 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 17
  lower := (25388563/714370000)
  upper := (25531437/714370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_17.interval_proof
}

def entry_45_18 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 18
  lower := (12135383/346170000)
  upper := (12204617/346170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_18.interval_proof
}

def entry_45_19 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 19
  lower := (1547989/45110000)
  upper := (1557011/45110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_19.interval_proof
}

def entry_45_20 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 20
  lower := (537017/15830000)
  upper := (540183/15830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_20.interval_proof
}

def entry_45_21 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 21
  lower := (28874263/857370000)
  upper := (29045737/857370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_21.interval_proof
}

def entry_45_22 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 22
  lower := (241239/7141250)
  upper := (970669/28565000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_22.interval_proof
}

def entry_45_23 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 23
  lower := (30757487/925130000)
  upper := (30942513/925130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_23.interval_proof
}

def entry_45_24 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 24
  lower := (13054367/406330000)
  upper := (13135633/406330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_24.interval_proof
}

def entry_45_25 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 25
  lower := (3437039/109610000)
  upper := (3458961/109610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_25.interval_proof
}

def entry_45_26 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 26
  lower := (14637361/476390000)
  upper := (14732639/476390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_26.interval_proof
}

def entry_45_27 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 27
  lower := (30290017/999830000)
  upper := (30489983/999830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_27.interval_proof
}

def entry_45_28 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 28
  lower := (13135873/441270000)
  upper := (13224127/441270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_28.interval_proof
}

def entry_45_29 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 29
  lower := (9517639/323610000)
  upper := (9582361/323610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_29.interval_proof
}

def entry_45_30 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 30
  lower := (14176627/483730000)
  upper := (14273373/483730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_30.interval_proof
}

def entry_45_31 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 31
  lower := (4934803/171970000)
  upper := (4969197/171970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_31.interval_proof
}

def entry_45_32 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 32
  lower := (4372567/154330000)
  upper := (4403433/154330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_32.interval_proof
}

def entry_45_33 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 33
  lower := (64987/2317500)
  upper := (130901/4635000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_33.interval_proof
}

def entry_45_34 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 34
  lower := (305153/10970000)
  upper := (307347/10970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_34.interval_proof
}

def entry_45_35 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 35
  lower := (3816147/138530000)
  upper := (3843853/138530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_35.interval_proof
}

def entry_45_36 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 36
  lower := (20794071/759290000)
  upper := (20945929/759290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_36.interval_proof
}

def entry_45_37 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 37
  lower := (4700201/172990000)
  upper := (4734799/172990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_37.interval_proof
}

def entry_45_38 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 38
  lower := (18421867/681330000)
  upper := (18558133/681330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_38.interval_proof
}

def entry_45_39 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 39
  lower := (6329011/234890000)
  upper := (6375989/234890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_39.interval_proof
}

def entry_45_40 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 40
  lower := (14685403/545970000)
  upper := (14794597/545970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_40.interval_proof
}

def entry_45_41 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 41
  lower := (3708209/137910000)
  upper := (3735791/137910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_41.interval_proof
}

def entry_45_42 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 42
  lower := (16339363/606370000)
  upper := (16460637/606370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_42.interval_proof
}

def entry_45_43 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 43
  lower := (7512259/277410000)
  upper := (7567741/277410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_43.interval_proof
}

def entry_45_44 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 44
  lower := (2944229/107710000)
  upper := (2965771/107710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_44.interval_proof
}

def entry_45_45 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 45
  lower := (2507019/89810000)
  upper := (2524981/89810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_45.interval_proof
}

def entry_45_46 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 46
  lower := (2506877/93730000)
  upper := (2525623/93730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_46.interval_proof
}

def entry_45_47 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 47
  lower := (6186151/238490000)
  upper := (6233849/238490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_47.interval_proof
}

def entry_45_48 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 48
  lower := (2557879/101210000)
  upper := (2578121/101210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_48.interval_proof
}

def entry_45_49 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 49
  lower := (6558443/265570000)
  upper := (6611557/265570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_49.interval_proof
}

def entry_45_50 : GramEntryIntervalCertificate :=
{
  h := 45
  k := 50
  lower := (24060531/994690000)
  upper := (24259469/994690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_45_50.interval_proof
}

def entry_46_1 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 1
  lower := (25791013/389870000)
  upper := (25868987/389870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_1.interval_proof
}

def entry_46_2 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 2
  lower := (28825879/491210000)
  upper := (28924121/491210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_2.interval_proof
}

def entry_46_3 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 3
  lower := (21989363/406370000)
  upper := (22070637/406370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_3.interval_proof
}

def entry_46_4 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 4
  lower := (50431091/989090000)
  upper := (50628909/989090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_4.interval_proof
}

def entry_46_5 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 5
  lower := (11670977/240230000)
  upper := (11719023/240230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_5.interval_proof
}

def entry_46_6 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 6
  lower := (27790283/597170000)
  upper := (27909717/597170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_6.interval_proof
}

def entry_46_7 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 7
  lower := (8715553/194470000)
  upper := (8754447/194470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_7.interval_proof
}

def entry_46_8 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 8
  lower := (855629/19710000)
  upper := (859571/19710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_8.interval_proof
}

def entry_46_9 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 9
  lower := (7140631/168690000)
  upper := (7174369/168690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_9.interval_proof
}

def entry_46_10 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 10
  lower := (39124317/956830000)
  upper := (39315683/956830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_10.interval_proof
}

def entry_46_11 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 11
  lower := (2041151/50990000)
  upper := (2051349/50990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_11.interval_proof
}

def entry_46_12 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 12
  lower := (3750401/95990000)
  upper := (3769599/95990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_12.interval_proof
}

def entry_46_13 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 13
  lower := (8293179/218210000)
  upper := (8336821/218210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_13.interval_proof
}

def entry_46_14 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 14
  lower := (2808463/75370000)
  upper := (2823537/75370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_14.interval_proof
}

def entry_46_15 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 15
  lower := (6163369/166310000)
  upper := (6196631/166310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_15.interval_proof
}

def entry_46_16 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 16
  lower := (453941/12590000)
  upper := (456459/12590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_16.interval_proof
}

def entry_46_17 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 17
  lower := (15490793/442070000)
  upper := (15579207/442070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_17.interval_proof
}

def entry_46_18 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 18
  lower := (9133427/265730000)
  upper := (9186573/265730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_18.interval_proof
}

def entry_46_19 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 19
  lower := (22294007/659930000)
  upper := (22425993/659930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_19.interval_proof
}

def entry_46_20 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 20
  lower := (19112641/573590000)
  upper := (19227359/573590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_20.interval_proof
}

def entry_46_21 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 21
  lower := (3529309/106910000)
  upper := (3550691/106910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_21.interval_proof
}

def entry_46_22 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 22
  lower := (29959039/909610000)
  upper := (30140961/909610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_22.interval_proof
}

def entry_46_23 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 23
  lower := (5880433/175670000)
  upper := (5915567/175670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_23.interval_proof
}

def entry_46_24 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 24
  lower := (21383041/669590000)
  upper := (21516959/669590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_24.interval_proof
}

def entry_46_25 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 25
  lower := (30342271/977290000)
  upper := (30537729/977290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_25.interval_proof
}

def entry_46_26 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 26
  lower := (11681551/384490000)
  upper := (11758449/384490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_26.interval_proof
}

def entry_46_27 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 27
  lower := (1143169/38310000)
  upper := (1150831/38310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_27.interval_proof
}

def entry_46_28 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 28
  lower := (17769529/604710000)
  upper := (17890471/604710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_28.interval_proof
}

def entry_46_29 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 29
  lower := (4279231/147690000)
  upper := (4308769/147690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_29.interval_proof
}

def entry_46_30 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 30
  lower := (23119403/805970000)
  upper := (23280597/805970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_30.interval_proof
}

def entry_46_31 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 31
  lower := (7608217/267830000)
  upper := (7661783/267830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_31.interval_proof
}

def entry_46_32 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 32
  lower := (5154059/184410000)
  upper := (5190941/184410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_32.interval_proof
}

def entry_46_33 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 33
  lower := (215221/7790000)
  upper := (216779/7790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_33.interval_proof
}

def entry_46_34 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 34
  lower := (928483/33920000)
  upper := (935267/33920000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_34.interval_proof
}

def entry_46_35 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 35
  lower := (26980551/994490000)
  upper := (27179449/994490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_35.interval_proof
}

def entry_46_36 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 36
  lower := (26083011/969890000)
  upper := (26276989/969890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_36.interval_proof
}

def entry_46_37 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 37
  lower := (2647593/99070000)
  upper := (2667407/99070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_37.interval_proof
}

def entry_46_38 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 38
  lower := (7048457/265430000)
  upper := (7101543/265430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_38.interval_proof
}

def entry_46_39 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 39
  lower := (18370497/695030000)
  upper := (18509503/695030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_39.interval_proof
}

def entry_46_40 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 40
  lower := (39553/1501250)
  upper := (159413/6005000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_40.interval_proof
}

def entry_46_41 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 41
  lower := (13448869/511310000)
  upper := (13551131/511310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_41.interval_proof
}

def entry_46_42 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 42
  lower := (25303803/961970000)
  upper := (25496197/961970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_42.interval_proof
}

def entry_46_43 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 43
  lower := (4626451/175490000)
  upper := (4661549/175490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_43.interval_proof
}

def entry_46_44 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 44
  lower := (866729/32710000)
  upper := (873271/32710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_44.interval_proof
}

def entry_46_45 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 45
  lower := (2506877/93730000)
  upper := (2525623/93730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_45.interval_proof
}

def entry_46_46 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 46
  lower := (5218389/191110000)
  upper := (5256611/191110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_46.interval_proof
}

def entry_46_47 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 47
  lower := (5531373/211270000)
  upper := (5573627/211270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_47.interval_proof
}

def entry_46_48 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 48
  lower := (10598281/417190000)
  upper := (10681719/417190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_48.interval_proof
}

def entry_46_49 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 49
  lower := (15606967/630330000)
  upper := (15733033/630330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_49.interval_proof
}

def entry_46_50 : GramEntryIntervalCertificate :=
{
  h := 46
  k := 50
  lower := (20335977/840230000)
  upper := (20504023/840230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_46_50.interval_proof
}

def entry_47_1 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 1
  lower := (10068503/154970000)
  upper := (10099497/154970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_1.interval_proof
}

def entry_47_2 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 2
  lower := (1821633/31670000)
  upper := (1827967/31670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_2.interval_proof
}

def entry_47_3 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 3
  lower := (289331/5440000)
  upper := (290419/5440000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_3.interval_proof
}

def entry_47_4 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 4
  lower := (5113/102000)
  upper := (25667/510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_4.interval_proof
}

def entry_47_5 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 5
  lower := (41393239/867610000)
  upper := (41566761/867610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_5.interval_proof
}

def entry_47_6 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 6
  lower := (4534111/98890000)
  upper := (4553889/98890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_6.interval_proof
}

def entry_47_7 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 7
  lower := (14417323/326770000)
  upper := (14482677/326770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_7.interval_proof
}

def entry_47_8 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 8
  lower := (571167/13330000)
  upper := (573833/13330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_8.interval_proof
}

def entry_47_9 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 9
  lower := (728993/17570000)
  upper := (732507/17570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_9.interval_proof
}

def entry_47_10 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 10
  lower := (39142817/971830000)
  upper := (39337183/971830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_10.interval_proof
}

def entry_47_11 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 11
  lower := (23689717/602830000)
  upper := (23810283/602830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_11.interval_proof
}

def entry_47_12 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 12
  lower := (35647851/921490000)
  upper := (35832149/921490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_12.interval_proof
}

def entry_47_13 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 13
  lower := (16052083/429170000)
  upper := (16137917/429170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_13.interval_proof
}

def entry_47_14 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 14
  lower := (2553033/69670000)
  upper := (2566967/69670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_14.interval_proof
}

def entry_47_15 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 15
  lower := (12495517/344830000)
  upper := (12564483/344830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_15.interval_proof
}

def entry_47_16 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 16
  lower := (9159413/255870000)
  upper := (9210587/255870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_16.interval_proof
}

def entry_47_17 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 17
  lower := (125597/3630000)
  upper := (126323/3630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_17.interval_proof
}

def entry_47_18 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 18
  lower := (25624307/756930000)
  upper := (25775693/756930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_18.interval_proof
}

def entry_47_19 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 19
  lower := (107677/3230000)
  upper := (108323/3230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_19.interval_proof
}

def entry_47_20 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 20
  lower := (12686317/386830000)
  upper := (12763683/386830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_20.interval_proof
}

def entry_47_21 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 21
  lower := (1186341/36590000)
  upper := (1193659/36590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_21.interval_proof
}

def entry_47_22 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 22
  lower := (9779657/303430000)
  upper := (9840343/303430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_22.interval_proof
}

def entry_47_23 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 23
  lower := (13916977/430230000)
  upper := (14003023/430230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_23.interval_proof
}

def entry_47_24 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 24
  lower := (1207709/37910000)
  upper := (1215291/37910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_24.interval_proof
}

def entry_47_25 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 25
  lower := (28846369/936310000)
  upper := (29033631/936310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_25.interval_proof
}

def entry_47_26 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 26
  lower := (838811/27890000)
  upper := (844389/27890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_26.interval_proof
}

def entry_47_27 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 27
  lower := (7153253/242470000)
  upper := (7201747/242470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_27.interval_proof
}

def entry_47_28 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 28
  lower := (4786019/164810000)
  upper := (4818981/164810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_28.interval_proof
}

def entry_47_29 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 29
  lower := (1118089/39110000)
  upper := (1125911/39110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_29.interval_proof
}

def entry_47_30 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 30
  lower := (28090519/994810000)
  upper := (28289481/994810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_30.interval_proof
}

def entry_47_31 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 31
  lower := (27491899/981010000)
  upper := (27688101/981010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_31.interval_proof
}

def entry_47_32 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 32
  lower := (20605429/745710000)
  upper := (20754571/745710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_32.interval_proof
}

def entry_47_33 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 33
  lower := (1342573/49270000)
  upper := (1352427/49270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_33.interval_proof
}

def entry_47_34 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 34
  lower := (23990999/890010000)
  upper := (24169001/890010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_34.interval_proof
}

def entry_47_35 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 35
  lower := (200351/7490000)
  upper := (201849/7490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_35.interval_proof
}

def entry_47_36 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 36
  lower := (20582293/777070000)
  upper := (20737707/777070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_36.interval_proof
}

def entry_47_37 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 37
  lower := (24307501/924990000)
  upper := (24492499/924990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_37.interval_proof
}

def entry_47_38 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 38
  lower := (25791229/987710000)
  upper := (25988771/987710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_38.interval_proof
}

def entry_47_39 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 39
  lower := (3705731/142690000)
  upper := (3734269/142690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_39.interval_proof
}

def entry_47_40 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 40
  lower := (196739/7610000)
  upper := (198261/7610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_40.interval_proof
}

def entry_47_41 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 41
  lower := (22682009/879910000)
  upper := (22857991/879910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_41.interval_proof
}

def entry_47_42 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 42
  lower := (4861113/188870000)
  upper := (4898887/188870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_42.interval_proof
}

def entry_47_43 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 43
  lower := (1096989/42610000)
  upper := (1105511/42610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_43.interval_proof
}

def entry_47_44 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 44
  lower := (16187273/627270000)
  upper := (16312727/627270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_44.interval_proof
}

def entry_47_45 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 45
  lower := (6186151/238490000)
  upper := (6233849/238490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_45.interval_proof
}

def entry_47_46 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 46
  lower := (5531373/211270000)
  upper := (5573627/211270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_46.interval_proof
}

def entry_47_47 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 47
  lower := (1876727/70230000)
  upper := (1890773/70230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_47.interval_proof
}

def entry_47_48 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 48
  lower := (4041737/157630000)
  upper := (4073263/157630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_48.interval_proof
}

def entry_47_49 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 49
  lower := (23774483/955170000)
  upper := (23965517/955170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_49.interval_proof
}

def entry_47_50 : GramEntryIntervalCertificate :=
{
  h := 47
  k := 50
  lower := (23313933/960670000)
  upper := (23506067/960670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_47_50.interval_proof
}

def entry_48_1 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 1
  lower := (17622393/276070000)
  upper := (17677607/276070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_1.interval_proof
}

def entry_48_2 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 2
  lower := (51469181/908190000)
  upper := (51650819/908190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_2.interval_proof
}

def entry_48_3 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 3
  lower := (44784709/852910000)
  upper := (44955291/852910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_3.interval_proof
}

def entry_48_4 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 4
  lower := (11898497/240030000)
  upper := (11946503/240030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_4.interval_proof
}

def entry_48_5 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 5
  lower := (2906931/61940000)
  upper := (2919319/61940000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_5.interval_proof
}

def entry_48_6 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 6
  lower := (42456619/933810000)
  upper := (42643381/933810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_6.interval_proof
}

def entry_48_7 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 7
  lower := (21395851/491490000)
  upper := (21494149/491490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_7.interval_proof
}

def entry_48_8 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 8
  lower := (35536557/834430000)
  upper := (35703443/834430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_8.interval_proof
}

def entry_48_9 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 9
  lower := (19761559/484410000)
  upper := (19858441/484410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_9.interval_proof
}

def entry_48_10 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 10
  lower := (790511/19890000)
  upper := (794489/19890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_10.interval_proof
}

def entry_48_11 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 11
  lower := (13265673/343270000)
  upper := (13334327/343270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_11.interval_proof
}

def entry_48_12 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 12
  lower := (12627287/327130000)
  upper := (12692713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_12.interval_proof
}

def entry_48_13 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 13
  lower := (239351/6490000)
  upper := (240649/6490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_13.interval_proof
}

def entry_48_14 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 14
  lower := (3970993/110070000)
  upper := (3993007/110070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_14.interval_proof
}

def entry_48_15 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 15
  lower := (10540353/296470000)
  upper := (10599647/296470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_15.interval_proof
}

def entry_48_16 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 16
  lower := (33626171/938290000)
  upper := (33813829/938290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_16.interval_proof
}

def entry_48_17 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 17
  lower := (23491331/686690000)
  upper := (23628669/686690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_17.interval_proof
}

def entry_48_18 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 18
  lower := (12128731/362690000)
  upper := (12201269/362690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_18.interval_proof
}

def entry_48_19 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 19
  lower := (29041609/883910000)
  upper := (29218391/883910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_19.interval_proof
}

def entry_48_20 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 20
  lower := (29717979/920210000)
  upper := (29902021/920210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_20.interval_proof
}

def entry_48_21 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 21
  lower := (1043527/32730000)
  upper := (1050073/32730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_21.interval_proof
}

def entry_48_22 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 22
  lower := (13851189/438110000)
  upper := (13938811/438110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_22.interval_proof
}

def entry_48_23 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 23
  lower := (25987663/823370000)
  upper := (26152337/823370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_23.interval_proof
}

def entry_48_24 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 24
  lower := (7008151/218490000)
  upper := (7051849/218490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_24.interval_proof
}

def entry_48_25 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 25
  lower := (23523231/767690000)
  upper := (23676769/767690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_25.interval_proof
}

def entry_48_26 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 26
  lower := (27956219/937810000)
  upper := (28143781/937810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_26.interval_proof
}

def entry_48_27 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 27
  lower := (134539/4610000)
  upper := (135461/4610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_27.interval_proof
}

def entry_48_28 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 28
  lower := (23637571/824290000)
  upper := (23802429/824290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_28.interval_proof
}

def entry_48_29 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 29
  lower := (10796799/382010000)
  upper := (10873201/382010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_29.interval_proof
}

def entry_48_30 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 30
  lower := (417751/14990000)
  upper := (420749/14990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_30.interval_proof
}

def entry_48_31 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 31
  lower := (2310613/83870000)
  upper := (2327387/83870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_31.interval_proof
}

def entry_48_32 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 32
  lower := (3654197/133030000)
  upper := (3680803/133030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_32.interval_proof
}

def entry_48_33 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 33
  lower := (21500143/798570000)
  upper := (21659857/798570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_33.interval_proof
}

def entry_48_34 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 34
  lower := (6107033/229670000)
  upper := (6152967/229670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_34.interval_proof
}

def entry_48_35 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 35
  lower := (16168583/614170000)
  upper := (16291417/614170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_35.interval_proof
}

def entry_48_36 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 36
  lower := (3147979/120210000)
  upper := (3172021/120210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_36.interval_proof
}

def entry_48_37 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 37
  lower := (16167529/624710000)
  upper := (16292471/624710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_37.interval_proof
}

def entry_48_38 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 38
  lower := (24185881/941190000)
  upper := (24374119/941190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_38.interval_proof
}

def entry_48_39 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 39
  lower := (1378601/53990000)
  upper := (1389399/53990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_39.interval_proof
}

def entry_48_40 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 40
  lower := (4357859/171410000)
  upper := (4392141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_40.interval_proof
}

def entry_48_41 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 41
  lower := (16534651/653490000)
  upper := (16665349/653490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_41.interval_proof
}

def entry_48_42 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 42
  lower := (9661719/382810000)
  upper := (9738281/382810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_42.interval_proof
}

def entry_48_43 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 43
  lower := (2388521/94790000)
  upper := (2407479/94790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_43.interval_proof
}

def entry_48_44 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 44
  lower := (7669579/304210000)
  upper := (7730421/304210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_44.interval_proof
}

def entry_48_45 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 45
  lower := (2557879/101210000)
  upper := (2578121/101210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_45.interval_proof
}

def entry_48_46 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 46
  lower := (10598281/417190000)
  upper := (10681719/417190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_46.interval_proof
}

def entry_48_47 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 47
  lower := (4041737/157630000)
  upper := (4073263/157630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_47.interval_proof
}

def entry_48_48 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 48
  lower := (24755383/946170000)
  upper := (24944617/946170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_48.interval_proof
}

def entry_48_49 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 49
  lower := (11927521/474790000)
  upper := (12022479/474790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_49.interval_proof
}

def entry_48_50 : GramEntryIntervalCertificate :=
{
  h := 48
  k := 50
  lower := (173741/7121250)
  upper := (700661/28485000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_48_50.interval_proof
}

def entry_49_1 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 1
  lower := (1974977/31480000)
  upper := (1981273/31480000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_1.interval_proof
}

def entry_49_2 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 2
  lower := (54961137/988630000)
  upper := (55158863/988630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_2.interval_proof
}

def entry_49_3 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 3
  lower := (25181047/489530000)
  upper := (25278953/489530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_3.interval_proof
}

def entry_49_4 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 4
  lower := (36714313/756870000)
  upper := (36865687/756870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_4.interval_proof
}

def entry_49_5 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 5
  lower := (2444713/52870000)
  upper := (2455287/52870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_5.interval_proof
}

def entry_49_6 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 6
  lower := (25113451/565490000)
  upper := (25226549/565490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_6.interval_proof
}

def entry_49_7 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 7
  lower := (5894363/136370000)
  upper := (5921637/136370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_7.interval_proof
}

def entry_49_8 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 8
  lower := (25059667/603330000)
  upper := (25180333/603330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_8.interval_proof
}

def entry_49_9 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 9
  lower := (35272109/878910000)
  upper := (35447891/878910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_9.interval_proof
}

def entry_49_10 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 10
  lower := (2877679/73210000)
  upper := (2892321/73210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_10.interval_proof
}

def entry_49_11 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 11
  lower := (15274867/401330000)
  upper := (15355133/401330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_11.interval_proof
}

def entry_49_12 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 12
  lower := (4419481/117690000)
  upper := (4443019/117690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_12.interval_proof
}

def entry_49_13 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 13
  lower := (23784659/653410000)
  upper := (23915341/653410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_13.interval_proof
}

def entry_49_14 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 14
  lower := (139409/3910000)
  upper := (140191/3910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_14.interval_proof
}

def entry_49_15 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 15
  lower := (6194767/177330000)
  upper := (6230233/177330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_15.interval_proof
}

def entry_49_16 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 16
  lower := (4469653/128470000)
  upper := (4495347/128470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_16.interval_proof
}

def entry_49_17 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 17
  lower := (20748779/612210000)
  upper := (20871221/612210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_17.interval_proof
}

def entry_49_18 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 18
  lower := (23957329/726710000)
  upper := (24102671/726710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_18.interval_proof
}

def entry_49_19 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 19
  lower := (29658291/917090000)
  upper := (29841709/917090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_19.interval_proof
}

def entry_49_20 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 20
  lower := (1109017/34830000)
  upper := (1115983/34830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_20.interval_proof
}

def entry_49_21 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 21
  lower := (12719539/404610000)
  upper := (12800461/404610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_21.interval_proof
}

def entry_49_22 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 22
  lower := (8004233/257670000)
  upper := (8055767/257670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_22.interval_proof
}

def entry_49_23 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 23
  lower := (11482847/371530000)
  upper := (11557153/371530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_23.interval_proof
}

def entry_49_24 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 24
  lower := (3671917/118330000)
  upper := (3695583/118330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_24.interval_proof
}

def entry_49_25 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 25
  lower := (7485521/244790000)
  upper := (7534479/244790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_25.interval_proof
}

def entry_49_26 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 26
  lower := (9786933/330670000)
  upper := (9853067/330670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_26.interval_proof
}

def entry_49_27 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 27
  lower := (305817/10580000)
  upper := (307933/10580000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_27.interval_proof
}

def entry_49_28 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 28
  lower := (7035219/247810000)
  upper := (7084781/247810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_28.interval_proof
}

def entry_49_29 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 29
  lower := (23535683/843170000)
  upper := (23704317/843170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_29.interval_proof
}

def entry_49_30 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 30
  lower := (6207433/225670000)
  upper := (6252567/225670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_30.interval_proof
}

def entry_49_31 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 31
  lower := (687967/25330000)
  upper := (693033/25330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_31.interval_proof
}

def entry_49_32 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 32
  lower := (14296881/531190000)
  upper := (14403119/531190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_32.interval_proof
}

def entry_49_33 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 33
  lower := (1718557/64430000)
  upper := (1731443/64430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_33.interval_proof
}

def entry_49_34 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 34
  lower := (21378589/814110000)
  upper := (21541411/814110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_34.interval_proof
}

def entry_49_35 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 35
  lower := (4664549/179510000)
  upper := (4700451/179510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_35.interval_proof
}

def entry_49_36 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 36
  lower := (4024359/156410000)
  upper := (4055641/156410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_36.interval_proof
}

def entry_49_37 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 37
  lower := (22790783/892170000)
  upper := (22969217/892170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_37.interval_proof
}

def entry_49_38 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 38
  lower := (952237/37630000)
  upper := (959763/37630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_38.interval_proof
}

def entry_49_39 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 39
  lower := (21404881/851190000)
  upper := (21575119/851190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_39.interval_proof
}

def entry_49_40 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 40
  lower := (6254963/250370000)
  upper := (6305037/250370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_40.interval_proof
}

def entry_49_41 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 41
  lower := (4173219/167810000)
  upper := (4206781/167810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_41.interval_proof
}

def entry_49_42 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 42
  lower := (11633059/469410000)
  upper := (11726941/469410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_42.interval_proof
}

def entry_49_43 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 43
  lower := (1715059/69410000)
  upper := (1728941/69410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_43.interval_proof
}

def entry_49_44 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 44
  lower := (11662747/472530000)
  upper := (11757253/472530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_44.interval_proof
}

def entry_49_45 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 45
  lower := (6558443/265570000)
  upper := (6611557/265570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_45.interval_proof
}

def entry_49_46 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 46
  lower := (15606967/630330000)
  upper := (15733033/630330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_46.interval_proof
}

def entry_49_47 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 47
  lower := (23774483/955170000)
  upper := (23965517/955170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_47.interval_proof
}

def entry_49_48 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 48
  lower := (11927521/474790000)
  upper := (12022479/474790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_48.interval_proof
}

def entry_49_49 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 49
  lower := (15681/611875)
  upper := (126427/4895000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_49.interval_proof
}

def entry_49_50 : GramEntryIntervalCertificate :=
{
  h := 49
  k := 50
  lower := (1223531/49690000)
  upper := (1233469/49690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_49_50.interval_proof
}

def entry_50_1 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 1
  lower := (8232653/133470000)
  upper := (8259347/133470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_1.interval_proof
}

def entry_50_2 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 2
  lower := (2106157/38430000)
  upper := (2113843/38430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_2.interval_proof
}

def entry_50_3 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 3
  lower := (4600909/90910000)
  upper := (4619091/90910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_3.interval_proof
}

def entry_50_4 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 4
  lower := (21215557/444430000)
  upper := (21304443/444430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_4.interval_proof
}

def entry_50_5 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 5
  lower := (16264493/355070000)
  upper := (16335507/355070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_5.interval_proof
}

def entry_50_6 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 6
  lower := (22219099/509010000)
  upper := (22320901/509010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_6.interval_proof
}

def entry_50_7 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 7
  lower := (8150689/193110000)
  upper := (8189311/193110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_7.interval_proof
}

def entry_50_8 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 8
  lower := (5546401/135990000)
  upper := (5573599/135990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_8.interval_proof
}

def entry_50_9 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 9
  lower := (10732847/271530000)
  upper := (10787153/271530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_9.interval_proof
}

def entry_50_10 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 10
  lower := (35519269/907310000)
  upper := (35700731/907310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_10.interval_proof
}

def entry_50_11 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 11
  lower := (36133637/963630000)
  upper := (36326363/963630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_11.interval_proof
}

def entry_50_12 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 12
  lower := (3649087/99130000)
  upper := (3668913/99130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_12.interval_proof
}

def entry_50_13 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 13
  lower := (1159279/32210000)
  upper := (1165721/32210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_13.interval_proof
}

def entry_50_14 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 14
  lower := (2557699/73010000)
  upper := (2572301/73010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_14.interval_proof
}

def entry_50_15 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 15
  lower := (29594009/859910000)
  upper := (29765991/859910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_15.interval_proof
}

def entry_50_16 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 16
  lower := (762511/22390000)
  upper := (766989/22390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_16.interval_proof
}

def entry_50_17 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 17
  lower := (6069477/180230000)
  upper := (6105523/180230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_17.interval_proof
}

def entry_50_18 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 18
  lower := (11404999/350010000)
  upper := (11475001/350010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_18.interval_proof
}

def entry_50_19 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 19
  lower := (21941223/687770000)
  upper := (22078777/687770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_19.interval_proof
}

def entry_50_20 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 20
  lower := (6092683/193170000)
  upper := (6131317/193170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_20.interval_proof
}

def entry_50_21 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 21
  lower := (7089569/229310000)
  upper := (7135431/229310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_21.interval_proof
}

def entry_50_22 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 22
  lower := (180011/5890000)
  upper := (181189/5890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_22.interval_proof
}

def entry_50_23 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 23
  lower := (19107011/629890000)
  upper := (19232989/629890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_23.interval_proof
}

def entry_50_24 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 24
  lower := (838433/27670000)
  upper := (843967/27670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_24.interval_proof
}

def entry_50_25 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 25
  lower := (12265163/398370000)
  upper := (12344837/398370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_25.interval_proof
}

def entry_50_26 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 26
  lower := (13115467/445330000)
  upper := (13204533/445330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_26.interval_proof
}

def entry_50_27 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 27
  lower := (13657361/476390000)
  upper := (13752639/476390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_27.interval_proof
}

def entry_50_28 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 28
  lower := (4421751/157490000)
  upper := (4453249/157490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_28.interval_proof
}

def entry_50_29 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 29
  lower := (4379129/158710000)
  upper := (4410871/158710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_29.interval_proof
}

def entry_50_30 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 30
  lower := (169939/6235000)
  upper := (85593/3117500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_30.interval_proof
}

def entry_50_31 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 31
  lower := (4762241/177590000)
  upper := (4797759/177590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_31.interval_proof
}

def entry_50_32 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 32
  lower := (6089533/229670000)
  upper := (6135467/229670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_32.interval_proof
}

def entry_50_33 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 33
  lower := (637579/24210000)
  upper := (642421/24210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_33.interval_proof
}

def entry_50_34 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 34
  lower := (23798419/915810000)
  upper := (23981581/915810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_34.interval_proof
}

def entry_50_35 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 35
  lower := (16007581/624190000)
  upper := (16132419/624190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_35.interval_proof
}

def entry_50_36 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 36
  lower := (25360057/999430000)
  upper := (25559943/999430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_36.interval_proof
}

def entry_50_37 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 37
  lower := (1245551/49490000)
  upper := (1255449/49490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_37.interval_proof
}

def entry_50_38 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 38
  lower := (850991/34090000)
  upper := (857809/34090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_38.interval_proof
}

def entry_50_39 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 39
  lower := (3326563/134370000)
  upper := (3353437/134370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_39.interval_proof
}

def entry_50_40 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 40
  lower := (11712461/475390000)
  upper := (11807539/475390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_40.interval_proof
}

def entry_50_41 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 41
  lower := (22059803/901970000)
  upper := (22240197/901970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_41.interval_proof
}

def entry_50_42 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 42
  lower := (23503469/965310000)
  upper := (23696531/965310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_42.interval_proof
}

def entry_50_43 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 43
  lower := (21869869/901310000)
  upper := (22050131/901310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_43.interval_proof
}

def entry_50_44 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 44
  lower := (11875939/490610000)
  upper := (11974061/490610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_44.interval_proof
}

def entry_50_45 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 45
  lower := (24060531/994690000)
  upper := (24259469/994690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_45.interval_proof
}

def entry_50_46 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 46
  lower := (20335977/840230000)
  upper := (20504023/840230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_46.interval_proof
}

def entry_50_47 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 47
  lower := (23313933/960670000)
  upper := (23506067/960670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_47.interval_proof
}

def entry_50_48 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 48
  lower := (173741/7121250)
  upper := (700661/28485000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_48.interval_proof
}

def entry_50_49 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 49
  lower := (1223531/49690000)
  upper := (1233469/49690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_49.interval_proof
}

def entry_50_50 : GramEntryIntervalCertificate :=
{
  h := 50
  k := 50
  lower := (4563827/181730000)
  upper := (4600173/181730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_50_50.interval_proof
}


end RH.Certificates.Generated.NymanGramN50
