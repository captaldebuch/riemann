import RiemannHypothesis.Certificates.Generated.ChiRhoBoundsN50

/-! Generated χ–ρ interval projection for N=10. -/

namespace RH.Certificates.Generated.ChiRhoBoundsN10

open RH.Certificates

def linearCenter (i : Fin 10) : ℚ :=
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
  else 0

def linearLower (i : Fin 10) : ℚ := linearCenter i - (1 / 1000000000)
def linearUpper (i : Fin 10) : ℚ := linearCenter i + (1 / 1000000000)

theorem innerProductChiRho_interval_0 :
    ((linearLower (0 : Fin 10) : ℚ) : ℝ) ≤ innerProductChiRho 0 ∧
      innerProductChiRho 0 ≤ ((linearUpper (0 : Fin 10) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_0

theorem innerProductChiRho_interval_1 :
    ((linearLower (1 : Fin 10) : ℚ) : ℝ) ≤ innerProductChiRho 1 ∧
      innerProductChiRho 1 ≤ ((linearUpper (1 : Fin 10) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_1

theorem innerProductChiRho_interval_2 :
    ((linearLower (2 : Fin 10) : ℚ) : ℝ) ≤ innerProductChiRho 2 ∧
      innerProductChiRho 2 ≤ ((linearUpper (2 : Fin 10) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_2

theorem innerProductChiRho_interval_3 :
    ((linearLower (3 : Fin 10) : ℚ) : ℝ) ≤ innerProductChiRho 3 ∧
      innerProductChiRho 3 ≤ ((linearUpper (3 : Fin 10) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_3

theorem innerProductChiRho_interval_4 :
    ((linearLower (4 : Fin 10) : ℚ) : ℝ) ≤ innerProductChiRho 4 ∧
      innerProductChiRho 4 ≤ ((linearUpper (4 : Fin 10) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_4

theorem innerProductChiRho_interval_5 :
    ((linearLower (5 : Fin 10) : ℚ) : ℝ) ≤ innerProductChiRho 5 ∧
      innerProductChiRho 5 ≤ ((linearUpper (5 : Fin 10) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_5

theorem innerProductChiRho_interval_6 :
    ((linearLower (6 : Fin 10) : ℚ) : ℝ) ≤ innerProductChiRho 6 ∧
      innerProductChiRho 6 ≤ ((linearUpper (6 : Fin 10) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_6

theorem innerProductChiRho_interval_7 :
    ((linearLower (7 : Fin 10) : ℚ) : ℝ) ≤ innerProductChiRho 7 ∧
      innerProductChiRho 7 ≤ ((linearUpper (7 : Fin 10) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_7

theorem innerProductChiRho_interval_8 :
    ((linearLower (8 : Fin 10) : ℚ) : ℝ) ≤ innerProductChiRho 8 ∧
      innerProductChiRho 8 ≤ ((linearUpper (8 : Fin 10) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_8

theorem innerProductChiRho_interval_9 :
    ((linearLower (9 : Fin 10) : ℚ) : ℝ) ≤ innerProductChiRho 9 ∧
      innerProductChiRho 9 ≤ ((linearUpper (9 : Fin 10) : ℚ) : ℝ) := by
  simpa [linearLower, linearUpper, linearCenter,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearLower, RH.Certificates.Generated.ChiRhoBoundsN50.linearUpper,
    RH.Certificates.Generated.ChiRhoBoundsN50.linearCenter] using
    RH.Certificates.Generated.ChiRhoBoundsN50.innerProductChiRho_interval_9

theorem innerProductChiRho_interval (k : Fin 10) :
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

noncomputable def innerProductChiRho_certificate (k : Fin 10) :
    ChiRhoIntervalCertificate k.val := {
  lower := linearLower k
  upper := linearUpper k
  lower_le_upper := by unfold linearLower linearUpper; linarith
  certified := innerProductChiRho_interval k
}

end RH.Certificates.Generated.ChiRhoBoundsN10
