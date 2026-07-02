import RiemannHypothesis.Certificates.Generated.ChiRhoBoundsN50

/-! Generated χ–ρ interval projection for N=20. -/

namespace RH.Certificates.Generated.ChiRhoBoundsN20

open RH.Certificates

def linearCenter (i : Fin 20) : ℚ :=
  if i.val == 0 then (334885130399 / 792094461875)
  else if i.val == 1 then (539229655814 / 966420695621)
  else if i.val == 2 then (429555871558 / 847029364035)
  else if i.val == 3 then (365803125173 / 808816390216)
  else if i.val == 4 then (310041832416 / 762814777745)
  else if i.val == 5 then (185905148602 / 503684275485)
  else if i.val == 6 then (217680372953 / 643292168266)
  else if i.val == 7 then (265373981399 / 848441330135)
  else if i.val == 8 then (94134966137 / 323363287511)
  else if i.val == 9 then (204131695733 / 749005597659)
  else if i.val == 10 then (238998603362 / 932039438163)
  else if i.val == 11 then (209301576511 / 863784676978)
  else if i.val == 12 then (228196111150 / 992909593093)
  else if i.val == 13 then (57329321650 / 262133248871)
  else if i.val == 14 then (158608442467 / 759901748079)
  else if i.val == 15 then (9491117430 / 47524303471)
  else if i.val == 16 then (158172395365 / 825839262239)
  else if i.val == 17 then (102860339921 / 558828520785)
  else if i.val == 18 then (32547503008 / 183653562427)
  else if i.val == 19 then (44895414341 / 262660208977)
  else 0

def linearLower (i : Fin 20) : ℚ := linearCenter i - (1 / 1000000000)
def linearUpper (i : Fin 20) : ℚ := linearCenter i + (1 / 1000000000)

theorem innerProductChiRho_interval_0 :
    ((linearLower (0 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 0 ∧
      innerProductChiRho 0 ≤ ((linearUpper (0 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_0

theorem innerProductChiRho_interval_1 :
    ((linearLower (1 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 1 ∧
      innerProductChiRho 1 ≤ ((linearUpper (1 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_1

theorem innerProductChiRho_interval_2 :
    ((linearLower (2 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 2 ∧
      innerProductChiRho 2 ≤ ((linearUpper (2 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_2

theorem innerProductChiRho_interval_3 :
    ((linearLower (3 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 3 ∧
      innerProductChiRho 3 ≤ ((linearUpper (3 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_3

theorem innerProductChiRho_interval_4 :
    ((linearLower (4 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 4 ∧
      innerProductChiRho 4 ≤ ((linearUpper (4 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_4

theorem innerProductChiRho_interval_5 :
    ((linearLower (5 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 5 ∧
      innerProductChiRho 5 ≤ ((linearUpper (5 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_5

theorem innerProductChiRho_interval_6 :
    ((linearLower (6 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 6 ∧
      innerProductChiRho 6 ≤ ((linearUpper (6 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_6

theorem innerProductChiRho_interval_7 :
    ((linearLower (7 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 7 ∧
      innerProductChiRho 7 ≤ ((linearUpper (7 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_7

theorem innerProductChiRho_interval_8 :
    ((linearLower (8 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 8 ∧
      innerProductChiRho 8 ≤ ((linearUpper (8 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_8

theorem innerProductChiRho_interval_9 :
    ((linearLower (9 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 9 ∧
      innerProductChiRho 9 ≤ ((linearUpper (9 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_9

theorem innerProductChiRho_interval_10 :
    ((linearLower (10 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 10 ∧
      innerProductChiRho 10 ≤ ((linearUpper (10 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_10

theorem innerProductChiRho_interval_11 :
    ((linearLower (11 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 11 ∧
      innerProductChiRho 11 ≤ ((linearUpper (11 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_11

theorem innerProductChiRho_interval_12 :
    ((linearLower (12 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 12 ∧
      innerProductChiRho 12 ≤ ((linearUpper (12 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_12

theorem innerProductChiRho_interval_13 :
    ((linearLower (13 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 13 ∧
      innerProductChiRho 13 ≤ ((linearUpper (13 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_13

theorem innerProductChiRho_interval_14 :
    ((linearLower (14 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 14 ∧
      innerProductChiRho 14 ≤ ((linearUpper (14 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_14

theorem innerProductChiRho_interval_15 :
    ((linearLower (15 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 15 ∧
      innerProductChiRho 15 ≤ ((linearUpper (15 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_15

theorem innerProductChiRho_interval_16 :
    ((linearLower (16 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 16 ∧
      innerProductChiRho 16 ≤ ((linearUpper (16 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_16

theorem innerProductChiRho_interval_17 :
    ((linearLower (17 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 17 ∧
      innerProductChiRho 17 ≤ ((linearUpper (17 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_17

theorem innerProductChiRho_interval_18 :
    ((linearLower (18 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 18 ∧
      innerProductChiRho 18 ≤ ((linearUpper (18 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_18

theorem innerProductChiRho_interval_19 :
    ((linearLower (19 : Fin 20) : ℚ) : ℝ) ≤ innerProductChiRho 19 ∧
      innerProductChiRho 19 ≤ ((linearUpper (19 : Fin 20) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_19

theorem innerProductChiRho_interval (k : Fin 20) :
    ((linearLower k : ℚ) : ℝ) ≤ innerProductChiRho k.val ∧
      innerProductChiRho k.val ≤ ((linearUpper k : ℚ) : ℝ) := by
  fin_cases k
  · exact innerProductChiRho_interval_0
  · exact innerProductChiRho_interval_1
  · exact innerProductChiRho_interval_2
  · exact innerProductChiRho_interval_3
  · exact innerProductChiRho_interval_4
  · exact innerProductChiRho_interval_5
  · exact innerProductChiRho_interval_6
  · exact innerProductChiRho_interval_7
  · exact innerProductChiRho_interval_8
  · exact innerProductChiRho_interval_9
  · exact innerProductChiRho_interval_10
  · exact innerProductChiRho_interval_11
  · exact innerProductChiRho_interval_12
  · exact innerProductChiRho_interval_13
  · exact innerProductChiRho_interval_14
  · exact innerProductChiRho_interval_15
  · exact innerProductChiRho_interval_16
  · exact innerProductChiRho_interval_17
  · exact innerProductChiRho_interval_18
  · exact innerProductChiRho_interval_19

noncomputable def innerProductChiRho_certificate (k : Fin 20) :
    ChiRhoIntervalCertificate k.val := {
  lower := linearLower k
  upper := linearUpper k
  lower_le_upper := by unfold linearLower linearUpper; linarith
  certified := innerProductChiRho_interval k
}

end RH.Certificates.Generated.ChiRhoBoundsN20
