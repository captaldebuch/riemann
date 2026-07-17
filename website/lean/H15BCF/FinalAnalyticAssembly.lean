/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.ExactCancellationTarget
import NBMellinTools.H15BCF.GenusOneMajorantReduction
import NBMellinTools.H15BCF.HeightTruncationProduct

/-!
# Final conditional BCF assembly from the genus-one analytic core

This file closes every *formal* implication remaining in the H15 BCF route.
It deliberately does not assert the three outstanding analytic inputs:

* compact summable majorants for the genus-one factors, obtained classically
  from multiplicity-weighted zero counting;
* the Hadamard identification of xi with the resulting product, including its
  affine exponential prefactor; and
* height-truncation logarithmic-derivative convergence, together with the
  separate integrated critical-line cancellation estimate.

Once these are supplied as proved results, the zero-weight formula, normalized
BCF asymptotic, and published epsilon formulation follow without any further
analytic gap.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped Topology
open Filter Topology Set

/-- The classical Hadamard inputs that remain after the finite genus-one
algebra and Weierstrass reductions already formalized in `GenusOneProduct`.
The first field yields locally uniform product convergence; the second and
third fields identify and differentiate that product at the two xi endpoints. -/
structure BCFGenusOneAnalyticCore : Prop where
  locallySummableMajorant : BCFGenusOneLocallySummableMajorantOn Set.univ
  factorization : BCFXiGenusOneFactorization
  endpointLogDerivConvergence : BCFGenusOneEndpointLogDerivConvergence

/-- Construct the Hadamard analytic core from the more elementary
inverse-square zero-summability and compact-factor-bound package. -/
def BCFGenusOneAnalyticCore.ofMajorantData
    (hmajorant : BCFGenusOneMajorantData)
    (hfactor : BCFXiGenusOneFactorization)
    (hderiv : BCFGenusOneEndpointLogDerivConvergence) :
    BCFGenusOneAnalyticCore :=
  { locallySummableMajorant := hmajorant.locallySummableMajorant
    factorization := hfactor
    endpointLogDerivConvergence := hderiv }

/-- The core's zero-counting majorant yields locally uniform convergence of
the genuine genus-one product across the complex plane. -/
theorem BCFGenusOneAnalyticCore.multipliableLocallyUniformly
    (hcore : BCFGenusOneAnalyticCore) :
    MultipliableLocallyUniformlyOn
      (fun rho : bcfNontrivialZetaZeros ↦ fun s : ℂ ↦
        bcfXiGenusOneFactor (rho : ℂ) s) Set.univ :=
  bcfGenusOneProduct_multipliableLocallyUniformlyOn_of_majorant isOpen_univ
    hcore.locallySummableMajorant

/-- The same majorant supplies the pointwise absolute-convergence target used
by the endpoint nonvanishing infrastructure. -/
theorem BCFGenusOneAnalyticCore.absoluteConvergence
    (hcore : BCFGenusOneAnalyticCore) :
    BCFGenusOneProductAbsoluteConvergence :=
  bcfGenusOneProduct_absoluteConvergence_of_locallyMajorant_univ
    hcore.locallySummableMajorant

/-- The core's majorant also proves convergence of the concrete BCF products
along the original height cutoff.  What remains is convergence of their
logarithmic derivatives, not convergence of the products themselves. -/
theorem BCFGenusOneAnalyticCore.heightProductTendsto
    (hcore : BCFGenusOneAnalyticCore) (s : ℂ) :
    Tendsto (fun T : ℝ ↦ bcfXiFiniteGenusOneProduct T s) atTop
      (𝓝 (bcfXiInfiniteGenusOneProduct s)) :=
  tendsto_bcfXiFiniteGenusOneProduct_atTop_of_absoluteConvergence
    hcore.absoluteConvergence s

/-- The factorization and height derivative convergence fields give exactly
the missing xi endpoint product formula. -/
theorem BCFGenusOneAnalyticCore.hadamardEndpointFormula
    (hcore : BCFGenusOneAnalyticCore) :
    BCFHadamardEndpointFormula :=
  bcfHadamardEndpointFormula_of_genusOneProduct hcore.factorization
    hcore.endpointLogDerivConvergence

/-- Under the existing explicit RH and zero-simplicity package, the analytic
core supplies the BCF zero-weight constant. -/
theorem bcfZeroWeightFormula_of_genusOneAnalyticCore
    (hcond : BCFConditionalHypotheses) (hcore : BCFGenusOneAnalyticCore) :
    BCFZeroWeightFormula :=
  bcfZeroWeightFormula_of_canonicalEndpoint_of_simplicity
    hcond.rh hcond.simplicity hcore.hadamardEndpointFormula

/-- The remaining critical-line cancellation estimate, combined with the
genus-one core, yields the normalized BCF logarithmic asymptotic.  The
moment-bound component of `hcond` is reserved for the proof of this
cancellation estimate; no unused assumption is silently converted into a
theorem here. -/
theorem bcfLogAsymptotic_of_genusOneAnalyticCore_of_exactCancellation
    (hcond : BCFConditionalHypotheses) (hcore : BCFGenusOneAnalyticCore)
    (hcancel : BCFExactCriticalLineCancellation) :
    BCFLogAsymptotic :=
  bcfLogAsymptotic_of_exactCriticalLineCancellation
    (bcfZeroWeightFormula_of_genusOneAnalyticCore hcond hcore) hcancel

/-- The exact published epsilon-over-logarithm BCF estimate follows from the
assembled genus-one core and the true integrated cancellation input. -/
theorem bcfPublishedAsymptotic_of_genusOneAnalyticCore_of_exactCancellation
    (hcond : BCFConditionalHypotheses) (hcore : BCFGenusOneAnalyticCore)
    (hcancel : BCFExactCriticalLineCancellation) :
    BCFPublishedAsymptotic :=
  (bcfLogAsymptotic_of_genusOneAnalyticCore_of_exactCancellation
    hcond hcore hcancel).published

end

end NBMellinTools.H15BCF
