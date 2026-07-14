import RiemannHypothesis.Criteria.NymanBeurling.BaezDuarte
import RiemannHypothesis.Criteria.NymanBeurling.RHBridge
import RiemannHypothesis.Certificates.NymanBeurlingCertificate
import RiemannHypothesis.Certificates.Generated.NymanGramN10
import RiemannHypothesis.Certificates.Generated.NymanGramN20
import RiemannHypothesis.Certificates.Generated.NymanGramN50

/-!
# Phase 10J: Dependency-Pruned Axiom Audit

This file uses `#print axioms` to identify exactly which axioms appear on the
dependency chain of each main theorem. Compare against the global project axiom count
to distinguish "main pipeline" from "discovery scaffold" assumptions.

Run `lake build` then open in the editor to see the #print axioms output.
-/

namespace RH.Phase10J

open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Certificates

-- -----------------------------------------------------------------------
-- MAIN CRITERION THEOREMS
-- -----------------------------------------------------------------------

-- The bridge: L2 completeness → Báez-Duarte criterion
#print axioms baezDuarteCriterion_of_l2_completeness

-- Phase 10C bridge: certified energy sequence → Báez-Duarte criterion
#print axioms baezDuarteCriterion_of_certified_energy_sequence

-- The main equivalence (proof via Nyman-Beurling)
-- RH_of_baezDuarteCriterion bridges from BaezDuarteCriterion to RH using explicit debts
#print axioms RH.Criteria.NymanBeurling.RHBridge.RH_of_baezDuarteCriterion

-- -----------------------------------------------------------------------
-- FINITE DISTANCE BOUNDS
-- -----------------------------------------------------------------------

-- N = 10 certified bound
#print axioms RH.Certificates.Generated.NymanGramN10.baezDuarteDistance_N10_bound

-- N = 20 certified bound
#print axioms RH.Certificates.Generated.NymanGramN20.baezDuarteDistance_N20_bound

-- N = 50 certified bound
#print axioms RH.Certificates.Generated.NymanGramN50.baezDuarteDistance_N50_bound

-- -----------------------------------------------------------------------
-- KEY ANALYTIC LEMMAS
-- -----------------------------------------------------------------------

-- Gram expansion (proved; should have minimal axiom dependencies)
#print axioms RH.Certificates.baezDuarteL2Error_gram_expansion

-- Sign-aware energy bound (key analytic step in the certificate pipeline)
#print axioms RH.Certificates.sign_aware_energy_bound

end RH.Phase10J
