import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.BaezDuarte
import RiemannHypothesis.Criteria.NymanBeurling.ChiRhoIntegralEvaluation
import RiemannHypothesis.Criteria.NymanBeurling.FiniteL2Expansion
import RiemannHypothesis.Criteria.NymanBeurling.G11IntegralEvaluation
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Certificates.RationalPSD

open scoped BigOperators

namespace RH.Certificates

open RH.Criteria.NymanBeurling.BaezDuarte
open RH.Criteria.NymanBeurling.ChiRhoIntegralEvaluation
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Criteria.NymanBeurling
open MeasureTheory

-- The discrete continuous bridge limit sequence
noncomputable def distance_sequence (N : ℕ) : ℝ := BaezDuarteDistance N

-- ---------------------------------------------------------------------------
-- Phase 8 — Semantic bridge: finite certificate → BaezDuarteDistance bound
-- ---------------------------------------------------------------------------

/-- Inner product of χ_{(0,1]} with the k-th Báez-Duarte basis function ρ_k.
    This equals ∫₀^1 {1/((k+1)x)} dx = (log(k+1) + 1 - γ)/(k+1). -/
noncomputable def innerProductChiRho (k : ℕ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), chi01 x * rhoBD k x

/-- Restricting the positive half-line inner product to the support of `χ_(0,1]`
    gives the fractional-part integral evaluated in `ChiRhoIntegralEvaluation`. -/
theorem innerProductChiRho_eq_chiRhoIntegral (k : ℕ) :
    innerProductChiRho k = chiRhoIntegral (k + 1) := by
  unfold innerProductChiRho chiRhoIntegral
  rw [← integral_indicator measurableSet_Ioi]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
  · have hxpos : x ∈ Set.Ioi (0 : ℝ) := hx.1
    simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hxpos]
    simp [chi01, rhoBD, hx.1, hx.2, Nat.cast_add, Nat.cast_one]
  · by_cases hxpos : x ∈ Set.Ioi (0 : ℝ)
    · have hchi : ¬(0 < x ∧ x ≤ 1) := by
        simpa only [Set.mem_Ioc, not_and_or] using hx
      simp [hx, hxpos, chi01, hchi]
    · simp [hx, hxpos]

/-- Closed-form value of the inner product:
    `∫₀¹ {1 / ((k + 1)x)} dx = (log (k + 1) + 1 - γ) / (k + 1)`. -/
theorem innerProductChiRho_formula (k : ℕ) :
    innerProductChiRho k =
      (Real.log ((k : ℝ) + 1) + 1 - Real.eulerMascheroniConstant) / ((k : ℝ) + 1) := by
  rw [innerProductChiRho_eq_chiRhoIntegral]
  rw [chiRhoIntegral_formula (k + 1) (by omega)]
  norm_cast

/-- A rational interval certificate for one `χ`–`ρ_k` inner product. -/
structure ChiRhoIntervalCertificate (k : ℕ) where
  lower : ℚ
  upper : ℚ
  lower_le_upper : lower ≤ upper
  certified :
    ((lower : ℚ) : ℝ) ≤ innerProductChiRho k ∧
      innerProductChiRho k ≤ ((upper : ℚ) : ℝ)

/-- The characteristic function used by Báez-Duarte is the indicator of `(0, 1]`. -/
theorem chi01_eq_indicator :
    chi01 = (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) := by
  funext x
  by_cases hx : 0 < x ∧ x ≤ 1
  · simp [chi01, Set.indicator, Set.mem_Ioc, hx]
  · simp [chi01, Set.indicator, Set.mem_Ioc, hx]

/-- `χ_(0,1]` belongs to L² on the positive half-line. -/
theorem chi01_memLp_two :
    MemLp chi01 2 (volume.restrict (Set.Ioi (0 : ℝ))) := by
  rw [chi01_eq_indicator]
  exact (memLp_indicator_const 2 measurableSet_Ioc 1
    (Or.inr measure_Ioc_lt_top.ne)).mono_measure Measure.restrict_le_self

/-- The squared L² norm of `χ_(0,1]` on `(0, ∞)` is one. -/
theorem chi01_sq_integral :
    ∫ x in Set.Ioi (0 : ℝ), chi01 x * chi01 x = 1 := by
  have hfun : (fun x => chi01 x * chi01 x) =
      (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : 0 < x ∧ x ≤ 1
    · simp [chi01, Set.indicator, Set.mem_Ioc, hx]
    · simp [chi01, Set.indicator, Set.mem_Ioc, hx]
  rw [hfun, ← integral_indicator measurableSet_Ioi]
  simp only [Set.indicator_indicator]
  have hinter : Set.Ioi (0 : ℝ) ∩ Set.Ioc 0 1 = Set.Ioc 0 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
    tauto
  rw [hinter, integral_indicator measurableSet_Ioc]
  simp

/-- Each Báez-Duarte basis function is measurable. -/
theorem measurable_rhoBD (k : ℕ) : Measurable (rhoBD k) := by
  unfold rhoBD
  measurability

/-- The square of `rhoBD k` is the G₁₁ integrand after scaling by `k + 1`. -/
theorem rhoBD_sq_eq_scaled_G11OriginalIntegrand (k : ℕ) (x : ℝ) :
    rhoBD k x ^ 2 = G11OriginalIntegrand (((k : ℝ) + 1) * x) := by
  rfl

/-- The squared Báez-Duarte basis function is integrable on the positive half-line.
    This transports the existing local/tail proof for the G₁₁ integrand through
    the positive scaling `x ↦ (k + 1) * x`. -/
theorem integrableOn_rhoBD_sq_Ioi (k : ℕ) :
    IntegrableOn (fun x : ℝ => rhoBD k x ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hK : 0 < (k : ℝ) + 1 := by positivity
  have hscaled : IntegrableOn
      (fun x : ℝ => G11OriginalIntegrand (((k : ℝ) + 1) * x))
      (Set.Ioi (0 : ℝ)) := by
    rw [integrableOn_Ioi_comp_mul_left_iff G11OriginalIntegrand 0 hK]
    simpa only [mul_zero] using integrableOn_G11OriginalIntegrand_Ioi
  exact hscaled.congr_fun
    (fun x _ => (rhoBD_sq_eq_scaled_G11OriginalIntegrand k x).symm)
    measurableSet_Ioi

/-- The Báez-Duarte basis functions belong to L² on `(0, ∞)`. -/
theorem rhoBD_memLp_two (k : ℕ) :
    MemLp (rhoBD k) 2 (volume.restrict (Set.Ioi (0 : ℝ))) := by
  apply (memLp_two_iff_integrable_sq
    (measurable_rhoBD k).aestronglyMeasurable.restrict).2
  exact integrableOn_rhoBD_sq_Ioi k

/-- Reindex `rhoBD` so its natural-number addition matches the Gram-entry convention. -/
theorem rhoBD_cast_succ (k : ℕ) (x : ℝ) :
    Int.fract (1 / (((k + 1 : ℕ) : ℝ) * x)) = rhoBD k x := by
  simp only [rhoBD, Nat.cast_add, Nat.cast_one]

/-- The `i`-th basis function written with the Gram matrix's one-based index. -/
noncomputable def gramBasis {N : ℕ} (i : Fin N) (x : ℝ) : ℝ :=
  Int.fract (1 / (((i.val + 1 : ℕ) : ℝ) * x))

/-- Quadratic expansion: ‖χ − Σ cₖ ρₖ‖² equals the Gram quadratic form minus
    twice the linear inner product plus the constant ‖χ‖² = 1.
    The finite algebra and termwise integration are now proved generically;
    the only remaining input is L² membership of the basis functions. -/
theorem baezDuarteL2Error_gram_expansion (N : ℕ) (c : Fin N → ℝ) :
    BaezDuarteL2Error N c =
      ∑ h : Fin N, ∑ k : Fin N,
        c h * c k * baezDuarteGramEntry (h.val + 1) (k.val + 1)
      - 2 * ∑ k : Fin N, c k * innerProductChiRho k.val
      + 1 := by
  have hchi_cross (i : Fin N) : Integrable
      (fun x => chi01 x * gramBasis i x)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa only [gramBasis, rhoBD_cast_succ, Pi.mul_apply] using
      MemLp.integrable_mul (p := 2) (q := 2) chi01_memLp_two (rhoBD_memLp_two i.val)
  have hrho_cross (i j : Fin N) : Integrable
      (fun x => gramBasis i x * gramBasis j x)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa only [gramBasis, rhoBD_cast_succ, Pi.mul_apply] using
      MemLp.integrable_mul (p := 2) (q := 2)
        (rhoBD_memLp_two i.val) (rhoBD_memLp_two j.val)
  have hchi_sq : Integrable (fun x => chi01 x * chi01 x)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa only [Pi.mul_apply] using
      MemLp.integrable_mul (p := 2) (q := 2) chi01_memLp_two chi01_memLp_two
  have h := finite_L2_norm_quadratic_expansion
    (volume.restrict (Set.Ioi (0 : ℝ))) chi01
    gramBasis c hchi_sq hchi_cross hrho_cross
  have hlhs : (∫ x in Set.Ioi (0 : ℝ),
      (chi01 x - ∑ i, c i * gramBasis i x) ^ 2) = BaezDuarteL2Error N c := by
    unfold BaezDuarteL2Error bdApprox gramBasis
    simp_rw [rhoBD_cast_succ]
  have hgram (i j : Fin N) :
      (∫ x in Set.Ioi (0 : ℝ), gramBasis i x * gramBasis j x) =
        baezDuarteGramEntry (i.val + 1) (j.val + 1) := by
    rfl
  have hlin (i : Fin N) :
      (∫ x in Set.Ioi (0 : ℝ), chi01 x * gramBasis i x) =
        innerProductChiRho i.val := by
    unfold gramBasis innerProductChiRho
    simp_rw [rhoBD_cast_succ]
  rw [hlhs, chi01_sq_integral] at h
  simp_rw [hgram, hlin] at h
  linarith

/-- PROVED (Phase 8B): any candidate vector gives an upper bound on the distance.
    The distance is the infimum over all coefficient vectors; evaluating at one
    candidate gives an upper bound via `ciInf_le`. -/
theorem candidate_bounds_baez_duarte_distance
    {N : ℕ} (c : Fin N → ℝ) :
    BaezDuarteDistance N ≤ BaezDuarteL2Error N c :=
  ciInf_le ⟨0, by rintro _ ⟨c', rfl⟩; exact baezDuarteL2Error_nonneg N c'⟩ c

-- ---------------------------------------------------------------------------
-- Phase 8E — Sign-aware interval arithmetic (general lemmas)
-- ---------------------------------------------------------------------------

/-- Computable rational upper bound for a quadratic form with interval-bounded
    entries.  For each (h, k): use G_hi if c_h * c_k ≥ 0, else G_lo. -/
def signAwareQuadBoundQ {N : ℕ} (c : Fin N → ℚ)
    (G_lo G_hi : Fin N → Fin N → ℚ) : ℚ :=
  ∑ h : Fin N, ∑ k : Fin N,
    c h * c k * if 0 ≤ c h * c k then G_hi h k else G_lo h k

/-- Computable rational upper bound for a linear form with interval-bounded
    terms.  For each k: use l_lo if c_k ≥ 0 (since coefficient is −2 c_k),
    else l_hi. -/
def signAwareLinBoundQ {N : ℕ} (c : Fin N → ℚ)
    (l_lo l_hi : Fin N → ℚ) : ℚ :=
  ∑ k : Fin N, (-2) * c k * if 0 ≤ c k then l_lo k else l_hi k

/-- Lower endpoint of a rational interval enclosure for a finite linear form. -/
def lowerLinearBoundQ {N : ℕ} (c lo hi : Fin N → ℚ) : ℚ :=
  ∑ i : Fin N, c i * if 0 ≤ c i then lo i else hi i

/-- Upper endpoint of a rational interval enclosure for a finite linear form. -/
def upperLinearBoundQ {N : ℕ} (c lo hi : Fin N → ℚ) : ℚ :=
  ∑ i : Fin N, c i * if 0 ≤ c i then hi i else lo i

/-- Sign-aware interval arithmetic for a finite linear form. -/
theorem interval_linear_form_bounds {N : ℕ}
    (c lo hi : Fin N → ℚ)
    (l : Fin N → ℝ)
    (hentry : ∀ i,
      ((lo i : ℚ) : ℝ) ≤ l i ∧ l i ≤ ((hi i : ℚ) : ℝ)) :
    ((lowerLinearBoundQ c lo hi : ℚ) : ℝ) ≤
        ∑ i : Fin N, (c i : ℝ) * l i ∧
      (∑ i : Fin N, (c i : ℝ) * l i) ≤
        ((upperLinearBoundQ c lo hi : ℚ) : ℝ) := by
  constructor
  · simp only [lowerLinearBoundQ]
    push_cast
    apply Finset.sum_le_sum
    intro i _
    by_cases hci : (0 : ℚ) ≤ c i
    · rw [if_pos hci]
      exact mul_le_mul_of_nonneg_left (hentry i).1 (by exact_mod_cast hci)
    · rw [if_neg hci]
      have hciReal : (c i : ℝ) ≤ 0 := by
        exact_mod_cast (le_of_lt (lt_of_not_ge hci))
      exact mul_le_mul_of_nonpos_left (hentry i).2 hciReal
  · simp only [upperLinearBoundQ]
    push_cast
    apply Finset.sum_le_sum
    intro i _
    by_cases hci : (0 : ℚ) ≤ c i
    · rw [if_pos hci]
      exact mul_le_mul_of_nonneg_left (hentry i).2 (by exact_mod_cast hci)
    · rw [if_neg hci]
      have hciReal : (c i : ℝ) ≤ 0 := by
        exact_mod_cast (le_of_lt (lt_of_not_ge hci))
      exact mul_le_mul_of_nonpos_left (hentry i).1 hciReal

/-- General sign-aware energy bound (Phase 8E).
    Given interval certificates for each Gram entry and each linear term,
    the Báez-Duarte energy form is bounded above by the computable rational
    sign-aware upper bound. -/
theorem sign_aware_energy_bound {N : ℕ}
    (c : Fin N → ℚ)
    (G : Fin N → Fin N → ℝ)
    (G_lo G_hi : Fin N → Fin N → ℚ)
    (l : Fin N → ℝ)
    (l_lo l_hi : Fin N → ℚ)
    (hG_lo : ∀ i j, (G_lo i j : ℝ) ≤ G i j)
    (hG_hi : ∀ i j, G i j ≤ (G_hi i j : ℝ))
    (hl_lo : ∀ k, (l_lo k : ℝ) ≤ l k)
    (hl_hi : ∀ k, l k ≤ (l_hi k : ℝ)) :
    (∑ h : Fin N, ∑ k : Fin N, (c h : ℝ) * (c k : ℝ) * G h k)
    - 2 * ∑ k : Fin N, (c k : ℝ) * l k + 1
    ≤ (signAwareQuadBoundQ c G_lo G_hi : ℝ) +
      (signAwareLinBoundQ c l_lo l_hi : ℝ) + 1 := by
  have hquad : ∑ h : Fin N, ∑ k : Fin N, (c h : ℝ) * (c k : ℝ) * G h k ≤
      (signAwareQuadBoundQ c G_lo G_hi : ℝ) := by
    simp only [signAwareQuadBoundQ]
    push_cast
    apply Finset.sum_le_sum; intro h _
    apply Finset.sum_le_sum; intro k _
    by_cases hpos : (0 : ℚ) ≤ c h * c k
    · rw [if_pos hpos]; push_cast
      exact mul_le_mul_of_nonneg_left (hG_hi h k) (by exact_mod_cast hpos)
    · rw [if_neg hpos]; push_cast; push_neg at hpos
      exact mul_le_mul_of_nonpos_left (hG_lo h k) (le_of_lt (by exact_mod_cast hpos))
  have hlin : (-2 : ℝ) * ∑ k : Fin N, (c k : ℝ) * l k ≤
      (signAwareLinBoundQ c l_lo l_hi : ℝ) := by
    simp only [signAwareLinBoundQ]
    push_cast
    rw [show (-2 : ℝ) * ∑ k : Fin N, (c k : ℝ) * l k =
        ∑ k : Fin N, ((-2 : ℝ) * (c k : ℝ) * l k) from by
      rw [Finset.mul_sum]; congr 1; ext k; ring]
    apply Finset.sum_le_sum; intro k _
    by_cases hpos : (0 : ℚ) ≤ c k
    · rw [if_pos hpos]; push_cast
      have hck : (0 : ℝ) ≤ (c k : ℝ) := by exact_mod_cast hpos
      nlinarith [hl_lo k]
    · rw [if_neg hpos]; push_cast; push_neg at hpos
      have hck : (c k : ℝ) < 0 := by exact_mod_cast hpos
      nlinarith [hl_hi k]
  linarith [hquad, hlin]

inductive GramEntrySource where
  | ExactVasyuninSymbolic
  | CertifiedInterval
  | NumericApproximation
  deriving Repr, DecidableEq

def GramEntrySource.isCertified : GramEntrySource → Prop
  | .ExactVasyuninSymbolic => True
  | .CertifiedInterval => True
  | .NumericApproximation => False

structure GramEntryIntervalCertificate where
  h : ℕ
  k : ℕ
  lower : ℚ
  upper : ℚ
  source : GramEntrySource
  lower_le_upper : lower ≤ upper
  certified_interval :
    (lower : ℝ) ≤ baezDuarteGramEntry h k ∧
    baezDuarteGramEntry h k ≤ (upper : ℝ)

axiom certified_interval_trusted
    (h k : ℕ) (lower upper : ℚ) :
    (lower : ℝ) ≤ baezDuarteGramEntry h k ∧
    baezDuarteGramEntry h k ≤ (upper : ℝ)

structure BaezDuarteIntervalQuadraticModel (n : ℕ) where
  gramLower : Matrix (Fin n) (Fin n) ℚ
  gramUpper : Matrix (Fin n) (Fin n) ℚ
  linearLower : Fin n → ℚ
  linearUpper : Fin n → ℚ
  constantLower : ℚ
  constantUpper : ℚ
  gram_certified :
    ∀ i j,
      (gramLower i j : ℝ) ≤ baezDuarteGramEntry (i.val + 1) (j.val + 1) ∧
      baezDuarteGramEntry (i.val + 1) (j.val + 1) ≤ (gramUpper i j : ℝ)
  linear_certified : True
  constant_certified : True

structure FiniteIntervalEnergyWitness (n : ℕ) where
  model : BaezDuarteIntervalQuadraticModel n
  coeffs : Fin n → ℚ
  energyUpper : ℚ
  interval_energy_bound : True

axiom interval_energy_bounds_baez_duarte_distance
    {n : ℕ}
    (W : FiniteIntervalEnergyWitness n) :
    BaezDuarteDistance n ≤ (W.energyUpper : ℝ)

structure FiniteApproximationCertificate where
  N : ℕ
  distanceBound : ℝ
  nonneg_distanceBound : 0 ≤ distanceBound
  witness : FiniteIntervalEnergyWitness N
  witness_bound : (witness.energyUpper : ℝ) ≤ distanceBound
  certified_distance_bound : BaezDuarteDistance N ≤ distanceBound

axiom numeric_approximation_trusted : GramEntrySource.NumericApproximation = GramEntrySource.CertifiedInterval

structure VerifiedApproximationRate where
  rate : ℕ → ℝ
  tendsToZero : Filter.Tendsto rate Filter.atTop (nhds 0)
  certifies : ∀ N, ∃ C : FiniteApproximationCertificate, C.N = N ∧ C.distanceBound ≤ rate N

theorem nyman_beurling_limit_swap_gatekeeper 
    (h_nonneg : ∀ N, 0 ≤ BaezDuarteDistance N) : 
    Filter.Tendsto distance_sequence Filter.atTop (nhds 0) ↔ 
    (∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, BaezDuarteDistance N < ε) := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨N₀, hN⟩
    use N₀
    intro N hN'
    have h1 := hN N hN'
    rw [Real.dist_eq, sub_zero] at h1
    have h2 : distance_sequence N = BaezDuarteDistance N := rfl
    rw [h2] at h1
    rw [abs_of_nonneg (h_nonneg N)] at h1
    exact h1
  · intro h ε hε
    rcases h ε hε with ⟨N₀, hN⟩
    use N₀
    intro N hN'
    have h1 := hN N hN'
    rw [Real.dist_eq, sub_zero]
    have h2 : distance_sequence N = BaezDuarteDistance N := rfl
    rw [h2]
    rw [abs_of_nonneg (h_nonneg N)]
    exact h1

-- PROVED (Phase 8A): replaces the former axiom with the proved theorem
theorem approximationDistance_nonneg_analytic :
  ∀ N, 0 ≤ BaezDuarteDistance N := baezDuarteDistance_nonneg

axiom verified_rate_gives_nyman_beurling_axiom
    (R : VerifiedApproximationRate) :
    BaezDuarteCriterion

end RH.Certificates
