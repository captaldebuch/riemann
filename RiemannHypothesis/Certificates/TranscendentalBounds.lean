import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import RiemannHypothesis.Certificates.IntervalCertificate
import RiemannHypothesis.Certificates.Generated.TranscendentalBoundsGenerated

namespace RH.Certificates.TranscendentalBounds

open RH.Certificates.Generated

theorem log_two_pi_interval_theorem :
  (((183787 / 100000 : ℚ) : ℝ) ≤ Real.log (2 * Real.pi)) ∧
  (Real.log (2 * Real.pi) ≤ ((183788 / 100000 : ℚ) : ℝ)) := by
  have h := log_two_pi_certified_bounds
  have h_lower : ((183787 / 100000 : ℚ) : ℝ) ≤ ((log_two_pi_lower : ℚ) : ℝ) := by unfold log_two_pi_lower; norm_num
  have h_upper : ((log_two_pi_upper : ℚ) : ℝ) ≤ ((183788 / 100000 : ℚ) : ℝ) := by unfold log_two_pi_upper; norm_num
  exact ⟨le_trans h_lower h.1, le_trans h.2 h_upper⟩

theorem euler_gamma_interval_theorem :
  (((57721 / 100000 : ℚ) : ℝ) ≤ Real.eulerMascheroniConstant) ∧
  (Real.eulerMascheroniConstant ≤ ((57722 / 100000 : ℚ) : ℝ)) := by
  have h := euler_gamma_certified_bounds
  have h_lower : ((57721 / 100000 : ℚ) : ℝ) ≤ ((euler_gamma_lower : ℚ) : ℝ) := by unfold euler_gamma_lower; norm_num
  have h_upper : ((euler_gamma_upper : ℚ) : ℝ) ≤ ((57722 / 100000 : ℚ) : ℝ) := by unfold euler_gamma_upper; norm_num
  exact ⟨le_trans h_lower h.1, le_trans h.2 h_upper⟩

end RH.Certificates.TranscendentalBounds
