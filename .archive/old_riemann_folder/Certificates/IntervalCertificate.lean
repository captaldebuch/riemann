import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace RH.Certificates

inductive IntervalBackend where
  | arb
  | sageArb
  | mpmathUncertified
  | handwritten
  deriving Repr, DecidableEq

def IntervalBackend.isCertified : IntervalBackend → Prop
  | .arb => True
  | .sageArb => True
  | .mpmathUncertified => False
  | .handwritten => False

structure ExternalRealIntervalCertificate (x : ℝ) where
  lower : ℚ
  upper : ℚ
  backend : IntervalBackend
  lower_le_upper : lower ≤ upper
  certified_backend : backend.isCertified
  certified : ((lower : ℚ) : ℝ) ≤ x ∧ x ≤ ((upper : ℚ) : ℝ)

structure UncertifiedRealIntervalData (x : ℝ) where
  lower : ℚ
  upper : ℚ
  backend : IntervalBackend
  lower_le_upper : lower ≤ upper

end RH.Certificates
