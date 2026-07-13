import RiemannHypothesis.Criteria.NymanBeurling.H14FEFactorBound

/-!
# H14: assembled de la Vallée Poussin dependency chain

This module records the part of the H14 chain which is already theorem-level
and wires the remaining named analytic packages without weakening their
contracts.  In particular, `H14ZetaEM` proves the Euler--Maclaurin identity on
`Re s > 1`, its continuation to `Re s > 0`, and the component bounds; the
right-half vertical-growth package is therefore unconditional.  The FE-factor
interpolation, Borel--Jensen factorization, and effective Perron/contour decay
remain explicit inputs.
-/

namespace RH.Criteria.NymanBeurling

open MobiusSummatory
open H14ZetaEM
open H14ZetaFETransport

/--
The E1/E2 Euler--Maclaurin continuation and the V-R component estimates give
an unconditional right-half vertical-growth package (with `t₀ = 1`).
-/
noncomputable def zetaRightHalfLinearVerticalGrowthAtHeight_unconditional :
    MobiusSummatory.ZetaRightHalfLinearVerticalGrowthAtHeight :=
  MobiusSummatory.zetaRightHalfLinearVerticalGrowthAtHeight_of_eulerMaclaurinComponents
    H14ZetaEM.zetaRightHalfEulerMaclaurinComponents

/--
Conditional A2 assembly: an interior FE-factor interpolation estimate transports
the unconditional V-R bound to the frozen full-strip growth package.
-/
noncomputable def zetaLinearVerticalGrowthInStripAtHeight_of_interior_interpolation
    (H : H14ZetaFETransport.FEFactorInteriorInterpolation) :
    MobiusSummatory.ZetaLinearVerticalGrowthInStripAtHeight :=
  MobiusSummatory.zetaLinearVerticalGrowthInStripAtHeight_of_rightHalf_and_leftStrip
    zetaRightHalfLinearVerticalGrowthAtHeight_unconditional
    (H14ZetaFETransport.zetaLeftStripLinearVerticalGrowthAtHeight_of_factorBound
      (H14ZetaFETransport.zetaFEFactorVerticalBound_of_interior H))

/--
Conditional A2--Z5 assembly.  Once the FE interpolation package and the
Borel--Jensen factorization package are supplied, the existing zero-free-region
constructor applies directly.  No claim is made here that either package is
currently inhabited.
-/
noncomputable def deLaValleePoussinZeroFreeRegion_of_interior_and_borelJensen
    (H : H14ZetaFETransport.FEFactorInteriorInterpolation)
    (B : MobiusSummatory.ZetaBorelJensenFactorizationAtHeight
      (zetaLinearVerticalGrowthInStripAtHeight_of_interior_interpolation H)) :
    MobiusSummatory.DeLaValleePoussinZeroFreeRegion :=
  MobiusSummatory.deLaValleePoussinZeroFreeRegion_of_borelJensenDiscEstimateAtHeight
    (MobiusSummatory.zetaBorelJensenLogDerivDiscEstimateAtHeight_of_factorization B)

end RH.Criteria.NymanBeurling
