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

def entry_21_1 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 1
  lower := (97053293/767070000)
  upper := (97206707/767070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_1.interval_proof
}

def entry_21_2 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 2
  lower := (36416783/332170000)
  upper := (36483217/332170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_2.interval_proof
}

def entry_21_3 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 3
  lower := (95535399/946010000)
  upper := (95724601/946010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_3.interval_proof
}

def entry_21_4 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 4
  lower := (21699187/233130000)
  upper := (21745813/233130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_4.interval_proof
}

def entry_21_5 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 5
  lower := (95329/1085000)
  upper := (47773/542500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_5.interval_proof
}

def entry_21_6 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 6
  lower := (76268471/915290000)
  upper := (76451529/915290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_6.interval_proof
}

def entry_21_7 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 7
  lower := (76816371/936290000)
  upper := (77003629/936290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_7.interval_proof
}

def entry_21_8 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 8
  lower := (32896733/432670000)
  upper := (32983267/432670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_8.interval_proof
}

def entry_21_9 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 9
  lower := (65980213/897870000)
  upper := (66159787/897870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_9.interval_proof
}

def entry_21_10 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 10
  lower := (6974347/96530000)
  upper := (6993653/96530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_10.interval_proof
}

def entry_21_11 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 11
  lower := (17212859/246410000)
  upper := (17262141/246410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_11.interval_proof
}

def entry_21_12 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 12
  lower := (49345657/743430000)
  upper := (49494343/743430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_12.interval_proof
}

def entry_21_13 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 13
  lower := (47346051/739490000)
  upper := (47493949/739490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_13.interval_proof
}

def entry_21_14 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 14
  lower := (58586879/931210000)
  upper := (58773121/931210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_14.interval_proof
}

def entry_21_15 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 15
  lower := (12100087/199130000)
  upper := (12139913/199130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_15.interval_proof
}

def entry_21_16 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 16
  lower := (3135981/52690000)
  upper := (3146519/52690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_16.interval_proof
}

def entry_21_17 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 17
  lower := (34800559/594410000)
  upper := (34919441/594410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_17.interval_proof
}

def entry_21_18 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 18
  lower := (50772399/876010000)
  upper := (50947601/876010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_18.interval_proof
}

def entry_21_19 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 19
  lower := (4814659/83410000)
  upper := (4831341/83410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_19.interval_proof
}

def entry_21_20 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 20
  lower := (8423/145000)
  upper := (2113/36250)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_20.interval_proof
}

def entry_21_21 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 21
  lower := (23595629/393710000)
  upper := (23674371/393710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_21.interval_proof
}

def entry_21_22 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 22
  lower := (1708483/30795000)
  upper := (857321/15397500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_22.interval_proof
}

def entry_21_23 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 23
  lower := (50703803/961970000)
  upper := (50896197/961970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_23.interval_proof
}

def entry_21_24 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 24
  lower := (9139929/180710000)
  upper := (9176071/180710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_24.interval_proof
}

def entry_21_25 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 25
  lower := (42063797/862030000)
  upper := (42236203/862030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_25.interval_proof
}

def entry_21_26 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 26
  lower := (23545219/497810000)
  upper := (23644781/497810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_26.interval_proof
}

def entry_21_27 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 27
  lower := (11327863/246370000)
  upper := (11377137/246370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_27.interval_proof
}

def entry_21_28 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 28
  lower := (12611951/280490000)
  upper := (12668049/280490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_28.interval_proof
}

def entry_21_29 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 29
  lower := (32735151/748490000)
  upper := (32884849/748490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_29.interval_proof
}

def entry_21_30 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 30
  lower := (531259/12410000)
  upper := (533741/12410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_30.interval_proof
}

def entry_21_31 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 31
  lower := (2075067/49330000)
  upper := (2084933/49330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_31.interval_proof
}

def entry_21_32 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 32
  lower := (359129/8710000)
  upper := (360871/8710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_32.interval_proof
}

def entry_21_33 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 33
  lower := (8705901/215990000)
  upper := (8749099/215990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_33.interval_proof
}

def entry_21_34 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 34
  lower := (30363211/767890000)
  upper := (30516789/767890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_34.interval_proof
}

def entry_21_35 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 35
  lower := (1792277/45980000)
  upper := (1801473/45980000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_35.interval_proof
}

def entry_21_36 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 36
  lower := (20695919/540810000)
  upper := (20804081/540810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_36.interval_proof
}

def entry_21_37 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 37
  lower := (3353111/88890000)
  upper := (3370889/88890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_37.interval_proof
}

def entry_21_38 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 38
  lower := (30627761/822390000)
  upper := (30792239/822390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_38.interval_proof
}

def entry_21_39 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 39
  lower := (736003/19970000)
  upper := (739997/19970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_39.interval_proof
}

def entry_21_40 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 40
  lower := (441293/12070000)
  upper := (443707/12070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_40.interval_proof
}

def entry_21_41 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 41
  lower := (12096789/332110000)
  upper := (12163211/332110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_41.interval_proof
}

def entry_21_42 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 42
  lower := (16185863/441370000)
  upper := (16274137/441370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_42.interval_proof
}

def entry_21_43 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 43
  lower := (13950533/394670000)
  upper := (14029467/394670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_43.interval_proof
}

def entry_21_44 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 44
  lower := (19782547/574530000)
  upper := (19897453/574530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_44.interval_proof
}

def entry_21_45 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 45
  lower := (28874263/857370000)
  upper := (29045737/857370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_45.interval_proof
}

def entry_21_46 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 46
  lower := (3529309/106910000)
  upper := (3550691/106910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_46.interval_proof
}

def entry_21_47 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 47
  lower := (1186341/36590000)
  upper := (1193659/36590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_47.interval_proof
}

def entry_21_48 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 48
  lower := (1043527/32730000)
  upper := (1050073/32730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_48.interval_proof
}

def entry_21_49 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 49
  lower := (12719539/404610000)
  upper := (12800461/404610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_49.interval_proof
}

def entry_21_50 : GramEntryIntervalCertificate :=
{
  h := 21
  k := 50
  lower := (7089569/229310000)
  upper := (7135431/229310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_21_50.interval_proof
}

def entry_22_1 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 1
  lower := (7348967/60330000)
  upper := (7361033/60330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_1.interval_proof
}

def entry_22_2 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 2
  lower := (47010793/442070000)
  upper := (47099207/442070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_2.interval_proof
}

def entry_22_3 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 3
  lower := (68828611/713890000)
  upper := (68971389/713890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_3.interval_proof
}

def entry_22_4 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 4
  lower := (73158607/813930000)
  upper := (73321393/813930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_4.interval_proof
}

def entry_22_5 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 5
  lower := (18870197/223030000)
  upper := (18914803/223030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_5.interval_proof
}

def entry_22_6 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 6
  lower := (71321359/886410000)
  upper := (71498641/886410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_6.interval_proof
}

def entry_22_7 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 7
  lower := (67792577/874230000)
  upper := (67967423/874230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_7.interval_proof
}

def entry_22_8 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 8
  lower := (69875447/945530000)
  upper := (70064553/945530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_8.interval_proof
}

def entry_22_9 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 9
  lower := (13487/190000)
  upper := (541/7600)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_9.interval_proof
}

def entry_22_10 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 10
  lower := (1336269/19310000)
  upper := (1340131/19310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_10.interval_proof
}

def entry_22_11 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 11
  lower := (41151297/587030000)
  upper := (41268703/587030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_11.interval_proof
}

def entry_22_12 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 12
  lower := (27931963/430370000)
  upper := (28018037/430370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_12.interval_proof
}

def entry_22_13 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 13
  lower := (58376347/936530000)
  upper := (58563653/936530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_13.interval_proof
}

def entry_22_14 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 14
  lower := (58543251/967490000)
  upper := (58736749/967490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_14.interval_proof
}

def entry_22_15 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 15
  lower := (39662891/671090000)
  upper := (39797109/671090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_15.interval_proof
}

def entry_22_16 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 16
  lower := (3813381/66190000)
  upper := (3826619/66190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_16.interval_proof
}

def entry_22_17 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 17
  lower := (693773/12270000)
  upper := (696227/12270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_17.interval_proof
}

def entry_22_18 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 18
  lower := (2665219/47810000)
  upper := (2674781/47810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_18.interval_proof
}

def entry_22_19 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 19
  lower := (110893/2007500)
  upper := (222589/4015000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_19.interval_proof
}

def entry_22_20 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 20
  lower := (39697961/720390000)
  upper := (39842039/720390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_20.interval_proof
}

def entry_22_21 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 21
  lower := (1708483/30795000)
  upper := (857321/15397500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_21.interval_proof
}

def entry_22_22 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 22
  lower := (56511209/987910000)
  upper := (56708791/987910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_22.interval_proof
}

def entry_22_23 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 23
  lower := (13012991/245090000)
  upper := (13062009/245090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_23.interval_proof
}

def entry_22_24 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 24
  lower := (15369579/304210000)
  upper := (15430421/304210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_24.interval_proof
}

def entry_22_25 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 25
  lower := (9163611/188890000)
  upper := (9201389/188890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_25.interval_proof
}

def entry_22_26 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 26
  lower := (13655857/291430000)
  upper := (13714143/291430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_26.interval_proof
}

def entry_22_27 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 27
  lower := (9479139/208610000)
  upper := (9520861/208610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_27.interval_proof
}

def entry_22_28 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 28
  lower := (23427001/529990000)
  upper := (23532999/529990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_28.interval_proof
}

def entry_22_29 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 29
  lower := (40506113/938870000)
  upper := (40693887/938870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_29.interval_proof
}

def entry_22_30 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 30
  lower := (260257/6180000)
  upper := (261493/6180000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_30.interval_proof
}

def entry_22_31 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 31
  lower := (15776707/382930000)
  upper := (15853293/382930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_31.interval_proof
}

def entry_22_32 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 32
  lower := (10763381/266190000)
  upper := (10816619/266190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_32.interval_proof
}

def entry_22_33 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 33
  lower := (14673317/366830000)
  upper := (14746683/366830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_33.interval_proof
}

def entry_22_34 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 34
  lower := (1791397/46030000)
  upper := (1800603/46030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_34.interval_proof
}

def entry_22_35 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 35
  lower := (18571327/486730000)
  upper := (18668673/486730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_35.interval_proof
}

def entry_22_36 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 36
  lower := (16032257/427430000)
  upper := (16117743/427430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_36.interval_proof
}

def entry_22_37 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 37
  lower := (15797233/427670000)
  upper := (15882767/427670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_37.interval_proof
}

def entry_22_38 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 38
  lower := (807779/22210000)
  upper := (812221/22210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_38.interval_proof
}

def entry_22_39 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 39
  lower := (21280701/592990000)
  upper := (21399299/592990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_39.interval_proof
}

def entry_22_40 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 40
  lower := (19225797/542030000)
  upper := (19334203/542030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_40.interval_proof
}

def entry_22_41 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 41
  lower := (27800853/791470000)
  upper := (27959147/791470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_41.interval_proof
}

def entry_22_42 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 42
  lower := (27700577/794230000)
  upper := (27859423/794230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_42.interval_proof
}

def entry_22_43 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 43
  lower := (5538069/159310000)
  upper := (5569931/159310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_43.interval_proof
}

def entry_22_44 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 44
  lower := (28039887/801130000)
  upper := (28200113/801130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_44.interval_proof
}

def entry_22_45 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 45
  lower := (241239/7141250)
  upper := (970669/28565000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_45.interval_proof
}

def entry_22_46 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 46
  lower := (29959039/909610000)
  upper := (30140961/909610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_46.interval_proof
}

def entry_22_47 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 47
  lower := (9779657/303430000)
  upper := (9840343/303430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_47.interval_proof
}

def entry_22_48 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 48
  lower := (13851189/438110000)
  upper := (13938811/438110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_48.interval_proof
}

def entry_22_49 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 49
  lower := (8004233/257670000)
  upper := (8055767/257670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_49.interval_proof
}

def entry_22_50 : GramEntryIntervalCertificate :=
{
  h := 22
  k := 50
  lower := (180011/5890000)
  upper := (181189/5890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_22_50.interval_proof
}

def entry_23_1 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 1
  lower := (57700879/491210000)
  upper := (57799121/491210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_1.interval_proof
}

def entry_23_2 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 2
  lower := (100961091/989090000)
  upper := (101158909/989090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_2.interval_proof
}

def entry_23_3 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 3
  lower := (55640283/597170000)
  upper := (55759717/597170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_3.interval_proof
}

def entry_23_4 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 4
  lower := (1713229/19710000)
  upper := (1717171/19710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_4.interval_proof
}

def entry_23_5 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 5
  lower := (12263023/149770000)
  upper := (12292977/149770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_5.interval_proof
}

def entry_23_6 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 6
  lower := (75273793/962070000)
  upper := (75466207/962070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_6.interval_proof
}

def entry_23_7 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 7
  lower := (5624463/75370000)
  upper := (5639537/75370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_7.interval_proof
}

def entry_23_8 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 8
  lower := (909141/12590000)
  upper := (911659/12590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_8.interval_proof
}

def entry_23_9 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 9
  lower := (29981449/435510000)
  upper := (30068551/435510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_9.interval_proof
}

def entry_23_10 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 10
  lower := (60339593/904070000)
  upper := (60520407/904070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_10.interval_proof
}

def entry_23_11 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 11
  lower := (1953439/29610000)
  upper := (1959361/29610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_11.interval_proof
}

def entry_23_12 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 12
  lower := (42833041/669590000)
  upper := (42966959/669590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_12.interval_proof
}

def entry_23_13 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 13
  lower := (23401551/384490000)
  upper := (23478449/384490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_13.interval_proof
}

def entry_23_14 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 14
  lower := (38664323/656770000)
  upper := (38795677/656770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_14.interval_proof
}

def entry_23_15 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 15
  lower := (2429273/42270000)
  upper := (2437727/42270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_15.interval_proof
}

def entry_23_16 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 16
  lower := (36085559/644410000)
  upper := (36214441/644410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_16.interval_proof
}

def entry_23_17 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 17
  lower := (930179/16960000)
  upper := (933571/16960000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_17.interval_proof
}

def entry_23_18 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 18
  lower := (53750251/997490000)
  upper := (53949749/997490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_18.interval_proof
}

def entry_23_19 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 19
  lower := (11945051/224490000)
  upper := (11989949/224490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_19.interval_proof
}

def entry_23_20 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 20
  lower := (634049/12010000)
  upper := (636451/12010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_20.interval_proof
}

def entry_23_21 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 21
  lower := (50703803/961970000)
  upper := (50896197/961970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_21.interval_proof
}

def entry_23_22 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 22
  lower := (13012991/245090000)
  upper := (13062009/245090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_22.interval_proof
}

def entry_23_23 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 23
  lower := (10455889/191110000)
  upper := (10494111/191110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_23.interval_proof
}

def entry_23_24 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 24
  lower := (21238281/417190000)
  upper := (21321719/417190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_24.interval_proof
}

def entry_23_25 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 25
  lower := (40755977/840230000)
  upper := (40924023/840230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_25.interval_proof
}

def entry_23_26 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 26
  lower := (39984247/857530000)
  upper := (40155753/857530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_26.interval_proof
}

def entry_23_27 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 27
  lower := (29235137/648630000)
  upper := (29364863/648630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_27.interval_proof
}

def entry_23_28 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 28
  lower := (38142789/872110000)
  upper := (38317211/872110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_28.interval_proof
}

def entry_23_29 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 29
  lower := (25250703/592970000)
  upper := (25369297/592970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_29.interval_proof
}

def entry_23_30 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 30
  lower := (40143363/966370000)
  upper := (40336637/966370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_30.interval_proof
}

def entry_23_31 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 31
  lower := (17816153/438470000)
  upper := (17903847/438470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_31.interval_proof
}

def entry_23_32 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 32
  lower := (36966953/930470000)
  upper := (37153047/930470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_32.interval_proof
}

def entry_23_33 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 33
  lower := (1830303/46970000)
  upper := (1839697/46970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_33.interval_proof
}

def entry_23_34 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 34
  lower := (38350069/999310000)
  upper := (38549931/999310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_34.interval_proof
}

def entry_23_35 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 35
  lower := (18271511/484890000)
  upper := (18368489/484890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_35.interval_proof
}

def entry_23_36 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 36
  lower := (1385743/37570000)
  upper := (1393257/37570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_36.interval_proof
}

def entry_23_37 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 37
  lower := (7008161/193390000)
  upper := (7046839/193390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_37.interval_proof
}

def entry_23_38 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 38
  lower := (8837739/247610000)
  upper := (8887261/247610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_38.interval_proof
}

def entry_23_39 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 39
  lower := (26494613/753870000)
  upper := (26645387/753870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_39.interval_proof
}

def entry_23_40 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 40
  lower := (161883/4670000)
  upper := (162817/4670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_40.interval_proof
}

def entry_23_41 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 41
  lower := (31268649/913510000)
  upper := (31451351/913510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_41.interval_proof
}

def entry_23_42 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 42
  lower := (27887639/823610000)
  upper := (28052361/823610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_42.interval_proof
}

def entry_23_43 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 43
  lower := (17517797/522030000)
  upper := (17622203/522030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_43.interval_proof
}

def entry_23_44 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 44
  lower := (26031919/780810000)
  upper := (26188081/780810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_44.interval_proof
}

def entry_23_45 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 45
  lower := (30757487/925130000)
  upper := (30942513/925130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_45.interval_proof
}

def entry_23_46 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 46
  lower := (5880433/175670000)
  upper := (5915567/175670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_46.interval_proof
}

def entry_23_47 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 47
  lower := (13916977/430230000)
  upper := (14003023/430230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_47.interval_proof
}

def entry_23_48 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 48
  lower := (25987663/823370000)
  upper := (26152337/823370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_48.interval_proof
}

def entry_23_49 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 49
  lower := (11482847/371530000)
  upper := (11557153/371530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_49.interval_proof
}

def entry_23_50 : GramEntryIntervalCertificate :=
{
  h := 23
  k := 50
  lower := (19107011/629890000)
  upper := (19232989/629890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_23_50.interval_proof
}

def entry_24_1 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 1
  lower := (71586897/631030000)
  upper := (71713103/631030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_1.interval_proof
}

def entry_24_2 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 2
  lower := (23820997/240030000)
  upper := (23869003/240030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_2.interval_proof
}

def entry_24_3 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 3
  lower := (14941087/164130000)
  upper := (14973913/164130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_3.interval_proof
}

def entry_24_4 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 4
  lower := (71156557/834430000)
  upper := (71323443/834430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_4.interval_proof
}

def entry_24_5 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 5
  lower := (1583011/19890000)
  upper := (1586989/19890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_5.interval_proof
}

def entry_24_6 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 6
  lower := (25287287/327130000)
  upper := (25352713/327130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_6.interval_proof
}

def entry_24_7 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 7
  lower := (7952993/110070000)
  upper := (7975007/110070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_7.interval_proof
}

def entry_24_8 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 8
  lower := (67346171/938290000)
  upper := (67533829/938290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_8.interval_proof
}

def entry_24_9 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 9
  lower := (4010887/59880000)
  upper := (4022863/59880000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_9.interval_proof
}

def entry_24_10 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 10
  lower := (59527979/920210000)
  upper := (59712021/920210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_10.interval_proof
}

def entry_24_11 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 11
  lower := (27746189/438110000)
  upper := (27833811/438110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_11.interval_proof
}

def entry_24_12 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 12
  lower := (14038151/218490000)
  upper := (14081849/218490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_12.interval_proof
}

def entry_24_13 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 13
  lower := (3969603/66470000)
  upper := (3982897/66470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_13.interval_proof
}

def entry_24_14 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 14
  lower := (47357571/824290000)
  upper := (47522429/824290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_14.interval_proof
}

def entry_24_15 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 15
  lower := (837001/14990000)
  upper := (839999/14990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_15.interval_proof
}

def entry_24_16 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 16
  lower := (7321697/133030000)
  upper := (7348303/133030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_16.interval_proof
}

def entry_24_17 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 17
  lower := (48798413/915870000)
  upper := (48981587/915870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_17.interval_proof
}

def entry_24_18 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 18
  lower := (6307979/120210000)
  upper := (6332021/120210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_18.interval_proof
}

def entry_24_19 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 19
  lower := (48465881/941190000)
  upper := (48654119/941190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_19.interval_proof
}

def entry_24_20 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 20
  lower := (8732859/171410000)
  upper := (8767141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_20.interval_proof
}

def entry_24_21 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 21
  lower := (9139929/180710000)
  upper := (9176071/180710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_21.interval_proof
}

def entry_24_22 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 22
  lower := (15369579/304210000)
  upper := (15430421/304210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_22.interval_proof
}

def entry_24_23 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 23
  lower := (21238281/417190000)
  upper := (21321719/417190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_23.interval_proof
}

def entry_24_24 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 24
  lower := (49605383/946170000)
  upper := (49794617/946170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_24.interval_proof
}

def entry_24_25 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 25
  lower := (7857929/160710000)
  upper := (7890071/160710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_25.interval_proof
}

def entry_24_26 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 26
  lower := (653599/14010000)
  upper := (656401/14010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_26.interval_proof
}

def entry_24_27 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 27
  lower := (43872281/977190000)
  upper := (44067719/977190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_27.interval_proof
}

def entry_24_28 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 28
  lower := (20393059/469410000)
  upper := (20486941/469410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_28.interval_proof
}

def entry_24_29 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 29
  lower := (3269247/77530000)
  upper := (3284753/77530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_29.interval_proof
}

def entry_24_30 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 30
  lower := (19552461/475390000)
  upper := (19647539/475390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_30.interval_proof
}

def entry_24_31 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 31
  lower := (27082421/675790000)
  upper := (27217579/675790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_31.interval_proof
}

def entry_24_32 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 32
  lower := (1575993/40070000)
  upper := (1584007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_32.interval_proof
}

def entry_24_33 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 33
  lower := (9253387/241130000)
  upper := (9301613/241130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_33.interval_proof
}

def entry_24_34 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 34
  lower := (6335663/168370000)
  upper := (6369337/168370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_34.interval_proof
}

def entry_24_35 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 35
  lower := (27575481/745190000)
  upper := (27724519/745190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_35.interval_proof
}

def entry_24_36 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 36
  lower := (4876697/133030000)
  upper := (4903303/133030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_36.interval_proof
}

def entry_24_37 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 37
  lower := (14419643/403570000)
  upper := (14500357/403570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_37.interval_proof
}

def entry_24_38 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 38
  lower := (1483271/42290000)
  upper := (1491729/42290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_38.interval_proof
}

def entry_24_39 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 39
  lower := (18207249/527510000)
  upper := (18312751/527510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_39.interval_proof
}

def entry_24_40 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 40
  lower := (10055507/294930000)
  upper := (10114493/294930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_40.interval_proof
}

def entry_24_41 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 41
  lower := (27677457/825430000)
  upper := (27842543/825430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_41.interval_proof
}

def entry_24_42 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 42
  lower := (24635657/743430000)
  upper := (24784343/743430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_42.interval_proof
}

def entry_24_43 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 43
  lower := (22710597/694030000)
  upper := (22849403/694030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_43.interval_proof
}

def entry_24_44 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 44
  lower := (22749787/702130000)
  upper := (22890213/702130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_44.interval_proof
}

def entry_24_45 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 45
  lower := (13054367/406330000)
  upper := (13135633/406330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_45.interval_proof
}

def entry_24_46 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 46
  lower := (21383041/669590000)
  upper := (21516959/669590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_46.interval_proof
}

def entry_24_47 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 47
  lower := (1207709/37910000)
  upper := (1215291/37910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_47.interval_proof
}

def entry_24_48 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 48
  lower := (7008151/218490000)
  upper := (7051849/218490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_48.interval_proof
}

def entry_24_49 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 49
  lower := (3671917/118330000)
  upper := (3695583/118330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_49.interval_proof
}

def entry_24_50 : GramEntryIntervalCertificate :=
{
  h := 24
  k := 50
  lower := (838433/27670000)
  upper := (843967/27670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_24_50.interval_proof
}

def entry_25_1 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 1
  lower := (21774153/198470000)
  upper := (21813847/198470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_1.interval_proof
}

def entry_25_2 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 2
  lower := (42475557/444430000)
  upper := (42564443/444430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_2.interval_proof
}

def entry_25_3 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 3
  lower := (58183431/665690000)
  upper := (58316569/665690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_3.interval_proof
}

def entry_25_4 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 4
  lower := (11106401/135990000)
  upper := (11133599/135990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_4.interval_proof
}

def entry_25_5 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 5
  lower := (59434187/758130000)
  upper := (59585813/758130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_5.interval_proof
}

def entry_25_6 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 6
  lower := (4757297/64530000)
  upper := (4770203/64530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_6.interval_proof
}

def entry_25_7 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 7
  lower := (5122699/73010000)
  upper := (5137301/73010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_7.interval_proof
}

def entry_25_8 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 8
  lower := (39971401/585990000)
  upper := (40088599/585990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_8.interval_proof
}

def entry_25_9 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 9
  lower := (31516713/482870000)
  upper := (31613287/482870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_9.interval_proof
}

def entry_25_10 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 10
  lower := (7290461/115390000)
  upper := (7313539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_10.interval_proof
}

def entry_25_11 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 11
  lower := (360611/5890000)
  upper := (361789/5890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_11.interval_proof
}

def entry_25_12 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 12
  lower := (32336729/532710000)
  upper := (32443271/532710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_12.interval_proof
}

def entry_25_13 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 13
  lower := (13729231/232690000)
  upper := (13775769/232690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_13.interval_proof
}

def entry_25_14 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 14
  lower := (8859251/157490000)
  upper := (8890749/157490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_14.interval_proof
}

def entry_25_15 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 15
  lower := (40356103/738970000)
  upper := (40503897/738970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_15.interval_proof
}

def entry_25_16 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 16
  lower := (4537709/85410000)
  upper := (4554791/85410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_16.interval_proof
}

def entry_25_17 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 17
  lower := (47688419/915810000)
  upper := (47871581/915810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_17.interval_proof
}

def entry_25_18 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 18
  lower := (50820057/999430000)
  upper := (51019943/999430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_18.interval_proof
}

def entry_25_19 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 19
  lower := (23597829/471710000)
  upper := (23692171/471710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_19.interval_proof
}

def entry_25_20 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 20
  lower := (23472461/475390000)
  upper := (23567539/475390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_20.interval_proof
}

def entry_25_21 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 21
  lower := (42063797/862030000)
  upper := (42236203/862030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_21.interval_proof
}

def entry_25_22 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 22
  lower := (9163611/188890000)
  upper := (9201389/188890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_22.interval_proof
}

def entry_25_23 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 23
  lower := (40755977/840230000)
  upper := (40924023/840230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_23.interval_proof
}

def entry_25_24 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 24
  lower := (7857929/160710000)
  upper := (7890071/160710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_24.interval_proof
}

def entry_25_25 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 25
  lower := (12273113/243870000)
  upper := (12321887/243870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_25.interval_proof
}

def entry_25_26 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 26
  lower := (7300479/155210000)
  upper := (7331521/155210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_26.interval_proof
}

def entry_25_27 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 27
  lower := (15819791/352090000)
  upper := (15890209/352090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_27.interval_proof
}

def entry_25_28 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 28
  lower := (10792559/249410000)
  upper := (10842441/249410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_28.interval_proof
}

def entry_25_29 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 29
  lower := (38398339/916610000)
  upper := (38581661/916610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_29.interval_proof
}

def entry_25_30 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 30
  lower := (6982859/171410000)
  upper := (7017141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_30.interval_proof
}

def entry_25_31 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 31
  lower := (10244177/258230000)
  upper := (10295823/258230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_31.interval_proof
}

def entry_25_32 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 32
  lower := (195199/5041250)
  upper := (784829/20165000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_32.interval_proof
}

def entry_25_33 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 33
  lower := (19019847/501530000)
  upper := (19120153/501530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_33.interval_proof
}

def entry_25_34 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 34
  lower := (12007649/323510000)
  upper := (12072351/323510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_34.interval_proof
}

def entry_25_35 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 35
  lower := (18898109/518910000)
  upper := (19001891/518910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_35.interval_proof
}

def entry_25_36 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 36
  lower := (10341087/289130000)
  upper := (10398913/289130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_36.interval_proof
}

def entry_25_37 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 37
  lower := (20601609/583910000)
  upper := (20718391/583910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_37.interval_proof
}

def entry_25_38 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 38
  lower := (22874069/659310000)
  upper := (23005931/659310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_38.interval_proof
}

def entry_25_39 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 39
  lower := (32354849/951510000)
  upper := (32545151/951510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_39.interval_proof
}

def entry_25_40 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 40
  lower := (12223471/365290000)
  upper := (12296529/365290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_40.interval_proof
}

def entry_25_41 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 41
  lower := (2472497/75030000)
  upper := (2487503/75030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_41.interval_proof
}

def entry_25_42 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 42
  lower := (12047949/370510000)
  upper := (12122051/370510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_42.interval_proof
}

def entry_25_43 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 43
  lower := (23257467/725330000)
  upper := (23402533/725330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_43.interval_proof
}

def entry_25_44 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 44
  lower := (222501/7021250)
  upper := (895621/28085000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_44.interval_proof
}

def entry_25_45 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 45
  lower := (3437039/109610000)
  upper := (3458961/109610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_45.interval_proof
}

def entry_25_46 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 46
  lower := (30342271/977290000)
  upper := (30537729/977290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_46.interval_proof
}

def entry_25_47 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 47
  lower := (28846369/936310000)
  upper := (29033631/936310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_47.interval_proof
}

def entry_25_48 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 48
  lower := (23523231/767690000)
  upper := (23676769/767690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_48.interval_proof
}

def entry_25_49 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 49
  lower := (7485521/244790000)
  upper := (7534479/244790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_49.interval_proof
}

def entry_25_50 : GramEntryIntervalCertificate :=
{
  h := 25
  k := 50
  lower := (12265163/398370000)
  upper := (12344837/398370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_25_50.interval_proof
}

def entry_26_1 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 1
  lower := (32829097/309030000)
  upper := (32890903/309030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_1.interval_proof
}

def entry_26_2 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 2
  lower := (26776241/287590000)
  upper := (26833759/287590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_2.interval_proof
}

def entry_26_3 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 3
  lower := (6220663/73370000)
  upper := (6235337/73370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_3.interval_proof
}

def entry_26_4 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 4
  lower := (61252729/772710000)
  upper := (61407271/772710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_4.interval_proof
}

def entry_26_5 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 5
  lower := (13661797/182030000)
  upper := (13698203/182030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_5.interval_proof
}

def entry_26_6 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 6
  lower := (21325121/298790000)
  upper := (21384879/298790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_6.interval_proof
}

def entry_26_7 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 7
  lower := (59183361/866390000)
  upper := (59356639/866390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_7.interval_proof
}

def entry_26_8 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 8
  lower := (27463321/416790000)
  upper := (27546679/416790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_8.interval_proof
}

def entry_26_9 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 9
  lower := (8696423/135770000)
  upper := (8723577/135770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_9.interval_proof
}

def entry_26_10 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 10
  lower := (57426181/938190000)
  upper := (57613819/938190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_10.interval_proof
}

def entry_26_11 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 11
  lower := (1793857/30180000)
  upper := (1799893/30180000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_11.interval_proof
}

def entry_26_12 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 12
  lower := (44563717/762830000)
  upper := (44716283/762830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_12.interval_proof
}

def entry_26_13 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 13
  lower := (34811297/587030000)
  upper := (34928703/587030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_13.interval_proof
}

def entry_26_14 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 14
  lower := (1105003/19970000)
  upper := (1108997/19970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_14.interval_proof
}

def entry_26_15 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 15
  lower := (25631903/480970000)
  upper := (25728097/480970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_15.interval_proof
}

def entry_26_16 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 16
  lower := (9094451/175490000)
  upper := (9129549/175490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_16.interval_proof
}

def entry_26_17 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 17
  lower := (7071081/139190000)
  upper := (7098919/139190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_17.interval_proof
}

def entry_26_18 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 18
  lower := (8472929/170710000)
  upper := (8507071/170710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_18.interval_proof
}

def entry_26_19 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 19
  lower := (2966403/60970000)
  upper := (2978597/60970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_19.interval_proof
}

def entry_26_20 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 20
  lower := (8749733/182670000)
  upper := (8786267/182670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_20.interval_proof
}

def entry_26_21 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 21
  lower := (23545219/497810000)
  upper := (23644781/497810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_21.interval_proof
}

def entry_26_22 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 22
  lower := (13655857/291430000)
  upper := (13714143/291430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_22.interval_proof
}

def entry_26_23 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 23
  lower := (39984247/857530000)
  upper := (40155753/857530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_23.interval_proof
}

def entry_26_24 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 24
  lower := (653599/14010000)
  upper := (656401/14010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_24.interval_proof
}

def entry_26_25 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 25
  lower := (7300479/155210000)
  upper := (7331521/155210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_25.interval_proof
}

def entry_26_26 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 26
  lower := (1653383/34170000)
  upper := (1660217/34170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_26.interval_proof
}

def entry_26_27 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 27
  lower := (6200317/136830000)
  upper := (6227683/136830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_27.interval_proof
}

def entry_26_28 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 28
  lower := (3821183/88170000)
  upper := (3838817/88170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_28.interval_proof
}

def entry_26_29 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 29
  lower := (37819463/905370000)
  upper := (38000537/905370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_29.interval_proof
}

def entry_26_30 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 30
  lower := (19945711/492890000)
  upper := (20044289/492890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_30.interval_proof
}

def entry_26_31 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 31
  lower := (29036201/737990000)
  upper := (29183799/737990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_31.interval_proof
}

def entry_26_32 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 32
  lower := (2070601/53990000)
  upper := (2081399/53990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_32.interval_proof
}

def entry_26_33 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 33
  lower := (15109667/403330000)
  upper := (15190333/403330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_33.interval_proof
}

def entry_26_34 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 34
  lower := (31304643/853570000)
  upper := (31475357/853570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_34.interval_proof
}

def entry_26_35 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 35
  lower := (19595521/544790000)
  upper := (19704479/544790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_35.interval_proof
}

def entry_26_36 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 36
  lower := (13491719/382810000)
  upper := (13568281/382810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_36.interval_proof
}

def entry_26_37 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 37
  lower := (34290977/990230000)
  upper := (34489023/990230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_37.interval_proof
}

def entry_26_38 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 38
  lower := (9247891/271090000)
  upper := (9302109/271090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_38.interval_proof
}

def entry_26_39 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 39
  lower := (20319937/600630000)
  upper := (20440063/600630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_39.interval_proof
}

def entry_26_40 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 40
  lower := (1324739/40110000)
  upper := (1332761/40110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_40.interval_proof
}

def entry_26_41 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 41
  lower := (439583/13545000)
  upper := (110573/3386250)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_41.interval_proof
}

def entry_26_42 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 42
  lower := (23636051/739490000)
  upper := (23783949/739490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_42.interval_proof
}

def entry_26_43 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 43
  lower := (570691/18090000)
  upper := (574309/18090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_43.interval_proof
}

def entry_26_44 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 44
  lower := (15869001/509990000)
  upper := (15970999/509990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_44.interval_proof
}

def entry_26_45 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 45
  lower := (14637361/476390000)
  upper := (14732639/476390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_45.interval_proof
}

def entry_26_46 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 46
  lower := (11681551/384490000)
  upper := (11758449/384490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_46.interval_proof
}

def entry_26_47 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 47
  lower := (838811/27890000)
  upper := (844389/27890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_47.interval_proof
}

def entry_26_48 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 48
  lower := (27956219/937810000)
  upper := (28143781/937810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_48.interval_proof
}

def entry_26_49 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 49
  lower := (9786933/330670000)
  upper := (9853067/330670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_49.interval_proof
}

def entry_26_50 : GramEntryIntervalCertificate :=
{
  h := 26
  k := 50
  lower := (13115467/445330000)
  upper := (13204533/445330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_26_50.interval_proof
}

def entry_27_1 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 1
  lower := (95806971/930290000)
  upper := (95993029/930290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_1.interval_proof
}

def entry_27_2 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 2
  lower := (30266339/336610000)
  upper := (30333661/336610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_2.interval_proof
}

def entry_27_3 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 3
  lower := (71344061/859390000)
  upper := (71515939/859390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_3.interval_proof
}

def entry_27_4 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 4
  lower := (16558501/214990000)
  upper := (16601499/214990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_4.interval_proof
}

def entry_27_5 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 5
  lower := (8113849/111510000)
  upper := (8136151/111510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_5.interval_proof
}

def entry_27_6 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 6
  lower := (13089161/188390000)
  upper := (13126839/188390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_6.interval_proof
}

def entry_27_7 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 7
  lower := (32032073/479270000)
  upper := (32127927/479270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_7.interval_proof
}

def entry_27_8 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 8
  lower := (8291033/129670000)
  upper := (8316967/129670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_8.interval_proof
}

def entry_27_9 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 9
  lower := (32169569/504310000)
  upper := (32270431/504310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_9.interval_proof
}

def entry_27_10 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 10
  lower := (13717033/229670000)
  upper := (13762967/229670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_10.interval_proof
}

def entry_27_11 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 11
  lower := (5244943/90570000)
  upper := (5263057/90570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_11.interval_proof
}

def entry_27_12 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 12
  lower := (54284103/958970000)
  upper := (54475897/958970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_12.interval_proof
}

def entry_27_13 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 13
  lower := (29647261/527390000)
  upper := (29752739/527390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_13.interval_proof
}

def entry_27_14 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 14
  lower := (13547757/247430000)
  upper := (13597243/247430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_14.interval_proof
}

def entry_27_15 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 15
  lower := (17207117/328830000)
  upper := (17272883/328830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_15.interval_proof
}

def entry_27_16 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 16
  lower := (42057073/829270000)
  upper := (42222927/829270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_16.interval_proof
}

def entry_27_17 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 17
  lower := (35897419/725810000)
  upper := (36042581/725810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_17.interval_proof
}

def entry_27_18 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 18
  lower := (6506697/133030000)
  upper := (6533303/133030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_18.interval_proof
}

def entry_27_19 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 19
  lower := (19972921/420790000)
  upper := (20057079/420790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_19.interval_proof
}

def entry_27_20 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 20
  lower := (7711481/165190000)
  upper := (7744519/165190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_20.interval_proof
}

def entry_27_21 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 21
  lower := (11327863/246370000)
  upper := (11377137/246370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_21.interval_proof
}

def entry_27_22 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 22
  lower := (9479139/208610000)
  upper := (9520861/208610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_22.interval_proof
}

def entry_27_23 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 23
  lower := (29235137/648630000)
  upper := (29364863/648630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_23.interval_proof
}

def entry_27_24 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 24
  lower := (43872281/977190000)
  upper := (44067719/977190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_24.interval_proof
}

def entry_27_25 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 25
  lower := (15819791/352090000)
  upper := (15890209/352090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_25.interval_proof
}

def entry_27_26 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 26
  lower := (6200317/136830000)
  upper := (6227683/136830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_26.interval_proof
}

def entry_27_27 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 27
  lower := (12553057/269430000)
  upper := (12606943/269430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_27.interval_proof
}

def entry_27_28 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 28
  lower := (42502771/972290000)
  upper := (42697229/972290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_28.interval_proof
}

def entry_27_29 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 29
  lower := (40223891/961090000)
  upper := (40416109/961090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_29.interval_proof
}

def entry_27_30 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 30
  lower := (29546831/731690000)
  upper := (29693169/731690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_30.interval_proof
}

def entry_27_31 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 31
  lower := (38950479/995210000)
  upper := (39149521/995210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_31.interval_proof
}

def entry_27_32 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 32
  lower := (7598041/199590000)
  upper := (7637959/199590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_32.interval_proof
}

def entry_27_33 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 33
  lower := (1775219/47810000)
  upper := (1784781/47810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_33.interval_proof
}

def entry_27_34 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 34
  lower := (33308237/917630000)
  upper := (33491763/917630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_34.interval_proof
}

def entry_27_35 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 35
  lower := (8860057/249430000)
  upper := (8909943/249430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_35.interval_proof
}

def entry_27_36 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 36
  lower := (12603937/360630000)
  upper := (12676063/360630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_36.interval_proof
}

def entry_27_37 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 37
  lower := (6261677/183230000)
  upper := (6298323/183230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_37.interval_proof
}

def entry_27_38 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 38
  lower := (5409889/161110000)
  upper := (5442111/161110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_38.interval_proof
}

def entry_27_39 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 39
  lower := (5642929/170710000)
  upper := (5677071/170710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_39.interval_proof
}

def entry_27_40 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 40
  lower := (27505753/842470000)
  upper := (27674247/842470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_40.interval_proof
}

def entry_27_41 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 41
  lower := (3828091/119090000)
  upper := (3851909/119090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_41.interval_proof
}

def entry_27_42 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 42
  lower := (30822289/977110000)
  upper := (31017711/977110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_42.interval_proof
}

def entry_27_43 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 43
  lower := (13451679/433210000)
  upper := (13538321/433210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_43.interval_proof
}

def entry_27_44 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 44
  lower := (1410393/46070000)
  upper := (1419607/46070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_44.interval_proof
}

def entry_27_45 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 45
  lower := (30290017/999830000)
  upper := (30489983/999830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_45.interval_proof
}

def entry_27_46 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 46
  lower := (1143169/38310000)
  upper := (1150831/38310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_46.interval_proof
}

def entry_27_47 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 47
  lower := (7153253/242470000)
  upper := (7201747/242470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_47.interval_proof
}

def entry_27_48 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 48
  lower := (134539/4610000)
  upper := (135461/4610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_48.interval_proof
}

def entry_27_49 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 49
  lower := (305817/10580000)
  upper := (307933/10580000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_49.interval_proof
}

def entry_27_50 : GramEntryIntervalCertificate :=
{
  h := 27
  k := 50
  lower := (13657361/476390000)
  upper := (13752639/476390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_27_50.interval_proof
}

def entry_28_1 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 1
  lower := (14749243/147570000)
  upper := (14778757/147570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_1.interval_proof
}

def entry_28_2 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 2
  lower := (75094417/855830000)
  upper := (75265583/855830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_2.interval_proof
}

def entry_28_3 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 3
  lower := (44074949/550510000)
  upper := (44185051/550510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_3.interval_proof
}

def entry_28_4 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 4
  lower := (38818731/512690000)
  upper := (38921269/512690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_4.interval_proof
}

def entry_28_5 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 5
  lower := (1402619/19810000)
  upper := (1406581/19810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_5.interval_proof
}

def entry_28_6 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 6
  lower := (20589527/304730000)
  upper := (20650473/304730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_6.interval_proof
}

def entry_28_7 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 7
  lower := (1518957/22930000)
  upper := (1523543/22930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_7.interval_proof
}

def entry_28_8 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 8
  lower := (51627357/826430000)
  upper := (51792643/826430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_8.interval_proof
}

def entry_28_9 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 9
  lower := (2958641/48590000)
  upper := (2968359/48590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_9.interval_proof
}

def entry_28_10 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 10
  lower := (1922713/32870000)
  upper := (1929287/32870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_10.interval_proof
}

def entry_28_11 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 11
  lower := (48823551/864490000)
  upper := (48996449/864490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_11.interval_proof
}

def entry_28_12 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 12
  lower := (22289539/404610000)
  upper := (22370461/404610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_12.interval_proof
}

def entry_28_13 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 13
  lower := (79129/1460000)
  upper := (79421/1460000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_13.interval_proof
}

def entry_28_14 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 14
  lower := (24300863/441370000)
  upper := (24389137/441370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_14.interval_proof
}

def entry_28_15 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 15
  lower := (32506923/630770000)
  upper := (32633077/630770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_15.interval_proof
}

def entry_28_16 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 16
  lower := (12330219/247810000)
  upper := (12379781/247810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_16.interval_proof
}

def entry_28_17 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 17
  lower := (706141/14590000)
  upper := (709059/14590000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_17.interval_proof
}

def entry_28_18 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 18
  lower := (46282289/977110000)
  upper := (46477711/977110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_18.interval_proof
}

def entry_28_19 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 19
  lower := (1937337/41630000)
  upper := (1945663/41630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_19.interval_proof
}

def entry_28_20 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 20
  lower := (9070087/199130000)
  upper := (9109913/199130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_20.interval_proof
}

def entry_28_21 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 21
  lower := (12611951/280490000)
  upper := (12668049/280490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_21.interval_proof
}

def entry_28_22 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 22
  lower := (23427001/529990000)
  upper := (23532999/529990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_22.interval_proof
}

def entry_28_23 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 23
  lower := (38142789/872110000)
  upper := (38317211/872110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_23.interval_proof
}

def entry_28_24 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 24
  lower := (20393059/469410000)
  upper := (20486941/469410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_24.interval_proof
}

def entry_28_25 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 25
  lower := (10792559/249410000)
  upper := (10842441/249410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_25.interval_proof
}

def entry_28_26 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 26
  lower := (3821183/88170000)
  upper := (3838817/88170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_26.interval_proof
}

def entry_28_27 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 27
  lower := (42502771/972290000)
  upper := (42697229/972290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_27.interval_proof
}

def entry_28_28 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 28
  lower := (14168461/315390000)
  upper := (14231539/315390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_28.interval_proof
}

def entry_28_29 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 29
  lower := (6881203/162970000)
  upper := (6913797/162970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_29.interval_proof
}

def entry_28_30 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 30
  lower := (24539363/606370000)
  upper := (24660637/606370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_30.interval_proof
}

def entry_28_31 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 31
  lower := (35299649/903510000)
  upper := (35480351/903510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_31.interval_proof
}

def entry_28_32 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 32
  lower := (3290071/86790000)
  upper := (3307429/86790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_32.interval_proof
}

def entry_28_33 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 33
  lower := (19158051/519490000)
  upper := (19261949/519490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_33.interval_proof
}

def entry_28_34 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 34
  lower := (1914679/53210000)
  upper := (1925321/53210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_34.interval_proof
}

def entry_28_35 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 35
  lower := (16752461/475390000)
  upper := (16847539/475390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_35.interval_proof
}

def entry_28_36 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 36
  lower := (5837061/169390000)
  upper := (5870939/169390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_36.interval_proof
}

def entry_28_37 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 37
  lower := (2367003/69970000)
  upper := (2380997/69970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_37.interval_proof
}

def entry_28_38 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 38
  lower := (9915119/298810000)
  upper := (9974881/298810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_38.interval_proof
}

def entry_28_39 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 39
  lower := (30426651/933490000)
  upper := (30613349/933490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_39.interval_proof
}

def entry_28_40 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 40
  lower := (3686509/114910000)
  upper := (3709491/114910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_40.interval_proof
}

def entry_28_41 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 41
  lower := (30324157/958430000)
  upper := (30515843/958430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_41.interval_proof
}

def entry_28_42 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 42
  lower := (29246879/931210000)
  upper := (29433121/931210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_42.interval_proof
}

def entry_28_43 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 43
  lower := (10924419/355810000)
  upper := (10995581/355810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_43.interval_proof
}

def entry_28_44 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 44
  lower := (29223251/967490000)
  upper := (29416749/967490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_44.interval_proof
}

def entry_28_45 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 45
  lower := (13135873/441270000)
  upper := (13224127/441270000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_45.interval_proof
}

def entry_28_46 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 46
  lower := (17769529/604710000)
  upper := (17890471/604710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_46.interval_proof
}

def entry_28_47 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 47
  lower := (4786019/164810000)
  upper := (4818981/164810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_47.interval_proof
}

def entry_28_48 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 48
  lower := (23637571/824290000)
  upper := (23802429/824290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_48.interval_proof
}

def entry_28_49 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 49
  lower := (7035219/247810000)
  upper := (7084781/247810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_49.interval_proof
}

def entry_28_50 : GramEntryIntervalCertificate :=
{
  h := 28
  k := 50
  lower := (4421751/157490000)
  upper := (4453249/157490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_28_50.interval_proof
}

def entry_29_1 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 1
  lower := (81985563/844370000)
  upper := (82154437/844370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_1.interval_proof
}

def entry_29_2 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 2
  lower := (37485869/441310000)
  upper := (37574131/441310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_2.interval_proof
}

def entry_29_3 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 3
  lower := (11764897/151030000)
  upper := (11795103/151030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_3.interval_proof
}

def entry_29_4 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 4
  lower := (686559/9410000)
  upper := (688441/9410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_4.interval_proof
}

def entry_29_5 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 5
  lower := (12793493/185070000)
  upper := (12830507/185070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_5.interval_proof
}

def entry_29_6 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 6
  lower := (17842981/270190000)
  upper := (17897019/270190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_6.interval_proof
}

def entry_29_7 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 7
  lower := (58198369/916310000)
  upper := (58381631/916310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_7.interval_proof
}

def entry_29_8 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 8
  lower := (19837337/326630000)
  upper := (19902663/326630000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_8.interval_proof
}

def entry_29_9 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 9
  lower := (699813/11870000)
  upper := (702187/11870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_9.interval_proof
}

def entry_29_10 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 10
  lower := (10078489/175110000)
  upper := (10113511/175110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_10.interval_proof
}

def entry_29_11 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 11
  lower := (54900389/996110000)
  upper := (55099611/996110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_11.interval_proof
}

def entry_29_12 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 12
  lower := (47351681/883190000)
  upper := (47528319/883190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_12.interval_proof
}

def entry_29_13 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 13
  lower := (9853757/187430000)
  upper := (9891243/187430000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_13.interval_proof
}

def entry_29_14 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 14
  lower := (43447003/829970000)
  upper := (43612997/829970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_14.interval_proof
}

def entry_29_15 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 15
  lower := (14501609/283910000)
  upper := (14558391/283910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_15.interval_proof
}

def entry_29_16 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 16
  lower := (2229189/45610000)
  upper := (2238311/45610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_16.interval_proof
}

def entry_29_17 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 17
  lower := (202947/4280000)
  upper := (203803/4280000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_17.interval_proof
}

def entry_29_18 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 18
  lower := (29725781/642190000)
  upper := (29854219/642190000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_18.interval_proof
}

def entry_29_19 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 19
  lower := (7351849/161510000)
  upper := (7384151/161510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_19.interval_proof
}

def entry_29_20 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 20
  lower := (5203323/116770000)
  upper := (5226677/116770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_20.interval_proof
}

def entry_29_21 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 21
  lower := (32735151/748490000)
  upper := (32884849/748490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_21.interval_proof
}

def entry_29_22 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 22
  lower := (40506113/938870000)
  upper := (40693887/938870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_22.interval_proof
}

def entry_29_23 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 23
  lower := (25250703/592970000)
  upper := (25369297/592970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_23.interval_proof
}

def entry_29_24 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 24
  lower := (3269247/77530000)
  upper := (3284753/77530000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_24.interval_proof
}

def entry_29_25 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 25
  lower := (38398339/916610000)
  upper := (38581661/916610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_25.interval_proof
}

def entry_29_26 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 26
  lower := (37819463/905370000)
  upper := (38000537/905370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_26.interval_proof
}

def entry_29_27 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 27
  lower := (40223891/961090000)
  upper := (40416109/961090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_27.interval_proof
}

def entry_29_28 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 28
  lower := (6881203/162970000)
  upper := (6913797/162970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_28.interval_proof
}

def entry_29_29 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 29
  lower := (17075629/393710000)
  upper := (17154371/393710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_29.interval_proof
}

def entry_29_30 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 30
  lower := (14474551/354490000)
  upper := (14545449/354490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_30.interval_proof
}

def entry_29_31 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 31
  lower := (35140293/897070000)
  upper := (35319707/897070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_31.interval_proof
}

def entry_29_32 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 32
  lower := (1323503/34970000)
  upper := (1330497/34970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_32.interval_proof
}

def entry_29_33 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 33
  lower := (33758097/919030000)
  upper := (33941903/919030000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_33.interval_proof
}

def entry_29_34 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 34
  lower := (33945093/949070000)
  upper := (34134907/949070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_34.interval_proof
}

def entry_29_35 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 35
  lower := (12259887/351130000)
  upper := (12330113/351130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_35.interval_proof
}

def entry_29_36 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 36
  lower := (6385307/186930000)
  upper := (6422693/186930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_36.interval_proof
}

def entry_29_37 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 37
  lower := (33160849/991510000)
  upper := (33359151/991510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_37.interval_proof
}

def entry_29_38 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 38
  lower := (30008583/914170000)
  upper := (30191417/914170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_38.interval_proof
}

def entry_29_39 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 39
  lower := (20825453/645470000)
  upper := (20954547/645470000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_39.interval_proof
}

def entry_29_40 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 40
  lower := (28669469/905310000)
  upper := (28850531/905310000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_40.interval_proof
}

def entry_29_41 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 41
  lower := (27980213/897870000)
  upper := (28159787/897870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_41.interval_proof
}

def entry_29_42 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 42
  lower := (1621721/52790000)
  upper := (1632279/52790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_42.interval_proof
}

def entry_29_43 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 43
  lower := (5344907/175930000)
  upper := (5380093/175930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_43.interval_proof
}

def entry_29_44 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 44
  lower := (4195987/140130000)
  upper := (4224013/140130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_44.interval_proof
}

def entry_29_45 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 45
  lower := (9517639/323610000)
  upper := (9582361/323610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_45.interval_proof
}

def entry_29_46 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 46
  lower := (4279231/147690000)
  upper := (4308769/147690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_46.interval_proof
}

def entry_29_47 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 47
  lower := (1118089/39110000)
  upper := (1125911/39110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_47.interval_proof
}

def entry_29_48 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 48
  lower := (10796799/382010000)
  upper := (10873201/382010000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_48.interval_proof
}

def entry_29_49 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 49
  lower := (23535683/843170000)
  upper := (23704317/843170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_49.interval_proof
}

def entry_29_50 : GramEntryIntervalCertificate :=
{
  h := 29
  k := 50
  lower := (4379129/158710000)
  upper := (4410871/158710000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_29_50.interval_proof
}

def entry_30_1 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 1
  lower := (42375119/448810000)
  upper := (42464881/448810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_1.interval_proof
}

def entry_30_2 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 2
  lower := (13074251/157490000)
  upper := (13105749/157490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_2.interval_proof
}

def entry_30_3 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 3
  lower := (5373967/70330000)
  upper := (5388033/70330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_3.interval_proof
}

def entry_30_4 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 4
  lower := (4200341/59090000)
  upper := (4212159/59090000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_4.interval_proof
}

def entry_30_5 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 5
  lower := (5680421/83290000)
  upper := (5697079/83290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_5.interval_proof
}

def entry_30_6 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 6
  lower := (21397239/327610000)
  upper := (21462761/327610000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_6.interval_proof
}

def entry_30_7 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 7
  lower := (10882351/176490000)
  upper := (10917649/176490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_7.interval_proof
}

def entry_30_8 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 8
  lower := (36179113/608870000)
  upper := (36300887/608870000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_8.interval_proof
}

def entry_30_9 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 9
  lower := (7291303/126970000)
  upper := (7316697/126970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_9.interval_proof
}

def entry_30_10 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 10
  lower := (53766331/936690000)
  upper := (53953669/936690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_10.interval_proof
}

def entry_30_11 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 11
  lower := (19384071/359290000)
  upper := (19455929/359290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_11.interval_proof
}

def entry_30_12 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 12
  lower := (6073461/115390000)
  upper := (6096539/115390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_12.interval_proof
}

def entry_30_13 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 13
  lower := (297419/5810000)
  upper := (298581/5810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_13.interval_proof
}

def entry_30_14 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 14
  lower := (14451421/285790000)
  upper := (14508579/285790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_14.interval_proof
}

def entry_30_15 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 15
  lower := (16952007/329930000)
  upper := (17017993/329930000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_15.interval_proof
}

def entry_30_16 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 16
  lower := (26305471/545290000)
  upper := (26414529/545290000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_16.interval_proof
}

def entry_30_17 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 17
  lower := (25285717/542830000)
  upper := (25394283/542830000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_17.interval_proof
}

def entry_30_18 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 18
  lower := (40251521/884790000)
  upper := (40428479/884790000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_18.interval_proof
}

def entry_30_19 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 19
  lower := (9328993/210070000)
  upper := (9371007/210070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_19.interval_proof
}

def entry_30_20 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 20
  lower := (38143331/866690000)
  upper := (38316669/866690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_20.interval_proof
}

def entry_30_21 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 21
  lower := (531259/12410000)
  upper := (533741/12410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_21.interval_proof
}

def entry_30_22 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 22
  lower := (260257/6180000)
  upper := (261493/6180000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_22.interval_proof
}

def entry_30_23 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 23
  lower := (40143363/966370000)
  upper := (40336637/966370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_23.interval_proof
}

def entry_30_24 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 24
  lower := (19552461/475390000)
  upper := (19647539/475390000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_24.interval_proof
}

def entry_30_25 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 25
  lower := (6982859/171410000)
  upper := (7017141/171410000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_25.interval_proof
}

def entry_30_26 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 26
  lower := (19945711/492890000)
  upper := (20044289/492890000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_26.interval_proof
}

def entry_30_27 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 27
  lower := (29546831/731690000)
  upper := (29693169/731690000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_27.interval_proof
}

def entry_30_28 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 28
  lower := (24539363/606370000)
  upper := (24660637/606370000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_28.interval_proof
}

def entry_30_29 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 29
  lower := (14474551/354490000)
  upper := (14545449/354490000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_29.interval_proof
}

def entry_30_30 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 30
  lower := (39665383/946170000)
  upper := (39854617/946170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_30.interval_proof
}

def entry_30_31 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 31
  lower := (3872703/97970000)
  upper := (3892297/97970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_31.interval_proof
}

def entry_30_32 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 32
  lower := (3841879/101210000)
  upper := (3862121/101210000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_32.interval_proof
}

def entry_30_33 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 33
  lower := (32920309/896910000)
  upper := (33099691/896910000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_33.interval_proof
}

def entry_30_34 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 34
  lower := (27572633/773670000)
  upper := (27727367/773670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_34.interval_proof
}

def entry_30_35 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 35
  lower := (9243389/266110000)
  upper := (9296611/266110000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_35.interval_proof
}

def entry_30_36 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 36
  lower := (17448577/514230000)
  upper := (17551423/514230000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_36.interval_proof
}

def entry_30_37 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 37
  lower := (14600983/440170000)
  upper := (14689017/440170000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_37.interval_proof
}

def entry_30_38 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 38
  lower := (24135749/742510000)
  upper := (24284251/742510000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_38.interval_proof
}

def entry_30_39 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 39
  lower := (7648523/239770000)
  upper := (7696477/239770000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_39.interval_proof
}

def entry_30_40 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 40
  lower := (1259993/40070000)
  upper := (1268007/40070000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_40.interval_proof
}

def entry_30_41 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 41
  lower := (184521/5990000)
  upper := (185719/5990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_41.interval_proof
}

def entry_30_42 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 42
  lower := (6040087/199130000)
  upper := (6079913/199130000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_42.interval_proof
}

def entry_30_43 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 43
  lower := (1092343/36570000)
  upper := (1099657/36570000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_43.interval_proof
}

def entry_30_44 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 44
  lower := (17002367/576330000)
  upper := (17117633/576330000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_44.interval_proof
}

def entry_30_45 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 45
  lower := (14176627/483730000)
  upper := (14273373/483730000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_45.interval_proof
}

def entry_30_46 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 46
  lower := (23119403/805970000)
  upper := (23280597/805970000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_46.interval_proof
}

def entry_30_47 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 47
  lower := (28090519/994810000)
  upper := (28289481/994810000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_47.interval_proof
}

def entry_30_48 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 48
  lower := (417751/14990000)
  upper := (420749/14990000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_48.interval_proof
}

def entry_30_49 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 49
  lower := (6207433/225670000)
  upper := (6252567/225670000)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_49.interval_proof
}

def entry_30_50 : GramEntryIntervalCertificate :=
{
  h := 30
  k := 50
  lower := (169939/6235000)
  upper := (85593/3117500)
  source := GramEntrySource.CertifiedInterval
  lower_le_upper := by norm_num
  certified_interval := RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50.interval_30_50.interval_proof
}

end RH.Certificates.Generated.NymanGramN50
