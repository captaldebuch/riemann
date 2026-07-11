# Technical Report: Certified Nyman-Beurling Pipeline for the Riemann Hypothesis

**Authors:** Xavier Fresquet and Gérard Biau, Sorbonne Université

## Closing-state ledger (2026-07-11, updated post `verified-final-assembly`)

The latest verified baseline is `verified-final-assembly` (main `8c029e1`).
The endgame theorem now EXISTS, honestly parameterized:

```lean
theorem riemannHypothesis_of_pair_and_NBforward
    (H_decay : ClassicalMertensDecay)
    (H_pair  : QuadraticInteractionBernoulliCorrelationEstimate H_decay)
    (h_forward : NBForward) : RiemannHypothesis
```

Independently audited on the merged tree, its `#print axioms` list is exactly
`[propext, Classical.choice, Quot.sound, setIntegral_Ioo_inv_substitution_bridge]`
— three standard axioms plus the one documented Gram-integral substitution
bridge. Notably, the historical `nyman_beurling_criterion_iff_RH` axiom is
NOT in this theorem's trust chain: the forward implication enters as an
explicit hypothesis (`NBForward`, from the NB0 split).

RH now follows from exactly THREE named statements (`H_vasyunin` was
discharged: `vasyuninBridgeLocalDebts_of_proved_chain`, constructed from the
proved H13 chain, tag `verified-rh-three-hypotheses`). Of the three:
`H_decay` is the 1899 de la Vallée Poussin Mertens bound, with a fully staged
formalization route (Euler–Maclaurin continuation → left-strip functional
equation transport → Borel–Jensen factorization → zero-free region →
effective Perron → contour shift), each stage a named structure with proved
consumers; `H_pair` is the centered Möbius–Bernoulli correlation estimate —
numerically robust, four independent decomposition attempts proved or
demonstrated insufficient, and the subject of the external consultation
(`docs/rh_pipeline_report.tex`, `docs/h15_quadratic_pair_consultation.tex`) —
its sharpest known form is the uniform-in-`A` weighted Möbius–sawtooth
correlation `∑_{k≤N} μ(k)(1−k/(N+1))·B₁(A/k)`, which classical Mertens decay
does not control;
`NBForward` is the forward Nyman–Beurling implication (Mellin route staged,
Plancherel stop-gate identified).

Hygiene performed alongside: generator-level long-line linter headers (no
certificates regenerated); stale worktree/branch deletion pending human
confirmation. One decorative `sorry` project-wide (`baezDuarte_prop21`,
paper-fidelity, used by nothing).

## 0. Methodology: A Digital Humanities Approach to the Riemann Hypothesis

This project applies a **Digital Humanities (DH) and Knowledge Engineering methodology** to the Riemann Hypothesis. Rather than attempting a direct, isolated mathematical attack, it treats the centuries-long history of RH research as a vast corpus to be mapped, filtered, and reverse-engineered — using machine-verified formal proof as the ultimate rigour gate.

The core insight, drawn from a systematic survey of 98 foundational sources spanning number theory, quantum mechanics, noncommutative geometry, functional analysis, and automated theorem proving, is that the primary barrier to an RH proof is no longer a shortage of intuition. It is the **human inability to guarantee absolute local rigour over global infinite bounds**. The DH pipeline addresses this by shifting the burden of proof from fallible human checking to strict machine-checked code in the **Lean 4 interactive theorem prover**.

The strategy unfolds in three phases:

1. **Corpus Mapping.** Historical RH barriers are categorised: numerical deception by slow-growing functions (like $\log\log T$); spectral gaps in defining workable self-adjoint operators; hidden convergence and positivity failures (Turán, de Branges, Li); and disciplinary silos preventing cross-field rigour.

2. **Extracting Formal Targets.** Of the five core modern heuristic frameworks (Quantum Chaos/RMT, Connes' trace formula, Nyman–Beurling/Báez-Duarte analytic criteria, arithmetic function fields, and quasicrystalline lattices), this project focuses on the **Nyman–Beurling–Báez-Duarte criterion**: the Riemann Hypothesis is equivalent to the characteristic function $\chi_{(0,1]}$ lying in the closure of the span of $\rho_k(x) = \{1/(kx)\}$ in $L^2(0,\infty)$.

3. **Autoformalization in Lean 4.** An AI-guided pipeline systematically converts analytic intuitions into machine-verified theorems, using Lean's type-checker as an aggressive formal gatekeeper that rejects any step where absolute convergence, positivity, or integrability is heuristically assumed. This is precisely the class of errors that historically discredited the proofs of Turán, de Branges, and Li.

> **Core philosophy.** The role of the mathematician shifts from traditional "prover" to *Knowledge Architect*. Human intuition is mechanically forced to either fail fast or stand as completely verified.

---

## 1. Overview
The project is focused on building a fully rigorous, mechanically verified computational pipeline in Lean 4 to compute and certify lower bounds for the Riemann Hypothesis via the **Nyman-Beurling-Báez-Duarte criterion**. 
Specifically, the distance of the constant function $1$ to the span of integer-dilated fractional part functions $\rho_k(x) = \{ \frac{1}{k x} \}$ in $L^2(0, \infty)$ dictates the truth of the Riemann Hypothesis.
By verifying the Positive Semi-Definiteness (PSD) of Gram matrices derived from these fractional part functions (Vasyunin formulation), we systematically provide mathematical certificates of RH.

## 2. Architecture & The Vasyunin Pipeline

### 2.1 The Gram Matrix & Vasyunin's Formula
For a cutoff $N$, we analyze the finite-dimensional Gram matrix $G_N$ of elements $h, k \le N$. The elements of this matrix $G_{h,k}$ are real-analytic constants (involving $\pi$, $\log(2\pi)$, $\gamma$, and generalized cotangent integrals). 

Because Lean's `norm_num` cannot automatically compute exact equalities for non-algebraic real integrations, we have established a **Rigorous Interval Provenance** architecture.

### 2.2 Rigorous Interval Certificates
Instead of claiming exact rational values for $G_{h,k}$, the generator script (`experiments/gram_matrix_search.py`) calculates rational lower and upper bounds for every matrix entry:
$$ G_{h,k} \in \left[ \frac{a}{b}, \frac{c}{d} \right] $$
Where $\frac{a}{b}$ and $\frac{c}{d}$ are explicitly defined rational constants, cast directly into $\mathbb{R}$ in Lean.

This is formalized in the core certificate structure `GramEntryIntervalCertificate` and the main matrix structure `NymanGramCertificate`:
```lean
structure GramEntryIntervalCertificate (h k : ℕ) where
  lower : ℚ
  upper : ℚ
  source : GramEntrySource
  lower_le_upper : lower ≤ upper
  certified_interval : (lower : ℝ) ≤ baezDuarteGramEntry h k ∧ 
                       baezDuarteGramEntry h k ≤ (upper : ℝ)
```

## 3. Results & Current Progress

We have successfully migrated the numerical pipeline to use this strictly rational bounded approach. The build of the entire project is currently **GREEN**, signifying that the Lean 4 type-checker verifies all interval and PSD logic.

### 3.1 N = 3 Small Vasyunin Milestone
What was achieved:
- N=1,2,3 generated certificates contain no `numeric_trust`.
- N=1,2,3 no longer rely on generic `certified_interval_trusted`.
- Each Gram entry Gᵢⱼ for i,j ≤ 3 is routed through a named theorem: `G11_interval_axiom`, `G12_interval_axiom`, `G13_interval_axiom`, `G22_interval_axiom`, `G23_interval_axiom`, `G33_interval_axiom`.

Trust-layer classification:
- **Lean-proved finite algebra**: Rational LDLᵀ → PSD.
- **Named symbolic formula axioms**: G11, G22, G33 diagonal formulas; G12, G13, G23 opaque symbolic values.
- **Named numeric interval axioms**: rational interval bounds for those symbolic values.
- **Analytic bridge axioms**: interval energy → Báez-Duarte distance; Báez-Duarte criterion → RH.

What this does NOT prove:
- It does not prove RH.
- It does not prove Vasyunin's general formula.
- It does not prove the numerical interval bounds from first principles.
- It certifies the architecture and eliminates untracked numeric approximations up to N=3.

### 3.2 N = 5 Milestone & Diagonal Scaling Consolidation
We have extended the structured Trust-Layer architecture to $N=5$. What was achieved:
- N=5 generated certificates contain no `numeric_trust` and no generic `certified_interval_trusted`.
- The generator (`gram_matrix_search.py`) now computes exact analytical constants for entries up to N=5 instead of falling back to numerical integration, ensuring pristine fractional bounds.
- All $G_{i,j}$ entries up to $N=5$ are routed through explicit named interval theorems (e.g. `G15_interval_axiom`, `G45_interval_axiom`).

Furthermore, we instituted **Diagonal Scaling Consolidation**:
Instead of distinct formula axioms for each diagonal entry, we established one unified general scaling **theorem** (fully machine-verified, no axiom):
```lean
theorem baez_duarte_diagonal_scaling (k : ℕ) (hk : 0 < k) :
  baezDuarteGramEntry k k = (1 / (k : ℝ)) * baezDuarteGramEntry 1 1
```
This theorem is proved directly from the concrete $L^2(0,\infty)$ integral definition of `baezDuarteGramEntry` using Mathlib's `integral_comp_mul_right_Ioi`. The diagonal formula theorems `G22_formula_axiom`, `G33_formula_axiom`, `G44_formula_axiom`, and `G55_formula_axiom` are now completely derived from this single master theorem and `G11_formula_theorem`, with **zero axiom trust** on the diagonal.

### 3.3 N = 10 Milestone & Table-Based Automated Interval Generation
We achieved the $N=10$ milestone without relying on `numeric_trust` fallback or expanding arbitrary axioms. To support this gracefully, we implemented a table-based automated generation infrastructure. 
The Python generator (`gram_matrix_search.py`) was entirely refactored to emit a modular definitions file `VasyuninIntervalsN{N}.lean` containing:
- 45 opaque numeric constants for all $1 \le h < k \le 10$ pairs.
- Generated interval bounding theorems for these independent pairs.
- Exact generation of all $G_{k,k}$ diagonal elements using the unified `baez_duarte_diagonal_scaling_axiom` rather than any new opaque constants.
- 100 `NamedVasyuninInterval` structured instances which organize these bounding theorems cleanly.

The generated $N=10$ certificates now import these theorems and invoke them seamlessly. The `lake build` for $N=10$ completes successfully, and a search confirms `numeric_trust` and `certified_interval_trusted` have been completely eliminated from the codebase for $N=10$.

#### 3.3.1 Phase 4B: Certificate Audit
To ensure generator fidelity before scaling further, we deployed a rigorous structural audit for $N=10$.
1. **Python-side Asserts:** The generator script enforces internal constraints before emitting any Lean code (symmetry, exact counts of diagonal vs off-diagonal pairs, correct lower/upper bounding, and total absence of `NumericApproximation`).
2. **Lean-side Verification:** The generator outputs a sister file, `NymanGramN10Audit.lean`, which systematically verifies that every one of the 100 structured interval records correctly declares its provenance (`diagonalScaling` vs `opaqueOffDiagonal`) exactly as mathematically mandated, using unforgeable `rfl` proofs.
The $N=10$ generator passed all Python audits, correctly produced 10 diagonal elements and 90 off-diagonal elements in the structure list, and built cleanly on the Lean side.

### 3.4 Phase 8: Semantic Bridge (finite certificate → `BaezDuarteDistance` bound)

Phase 8 establishes the formal Lean 4 chain connecting the numerical Gram matrix certificates to the abstract Báez-Duarte distance. This completes the **proof-of-meaning** layer: certificates no longer just "build"; they now formally bound a mathematically defined quantity.

**Phase 8A–8D (completed, all green)**

The key definitions and proved theorems in `RiemannHypothesis/Certificates/NymanBeurlingCertificate.lean`:

- `innerProductChiRho k` — inner product of $\chi_{(0,1]}$ with the $k$-th Báez-Duarte basis function $\rho_k$.  
  Axiomatically equal to $(\log(k+1) + 1 - \gamma)/(k+1)$ (`innerProductChiRho_formula`).
- `baezDuarteL2Error_gram_expansion` (axiom) — the $L^2$ error equals the quadratic Gram form minus twice the linear term plus the constant $\|\chi\|^2 = 1$.
- `candidate_bounds_baez_duarte_distance` (**proved**) — evaluating the energy at any candidate coefficient vector gives an upper bound on `BaezDuarteDistance N` via `ciInf_le`.
- `baezDuarteDistance_nonneg` (**proved**) — the distance is non-negative, replacing the former axiom.

For $N \in \{10, 20, 50\}$, the theorem:
```lean
theorem baezDuarteDistance_N{N}_bound :
    BaezDuarteDistance {N} ≤ (witnessEnergy.energyUpper : ℝ)
```
is proved via the chain: `candidate_bounds` → `gram_expansion` (axiom) → `N{N}_quadratic_le_energyUpper`.

Certified upper bounds:
| $N$ | `energyUpper` (≈) | sorry count |
|-----|-------------------|-------------|
| 10  | 0.02575           | 0           |
| 20  | 0.02198           | 1 (`ldl_identity` only) |
| 50  | 0.03451           | 1 (`ldl_identity` only) |

*(N=50 is slightly worse than N=20 because coefficient truncation at $10^9$ denominator limit introduces slack; the bound remains valid. N=50 could match N=20 by embedding the N=20 optimal vector padded with zeros — deferred to Phase 9.)*

**Phase 8E (completed, all green)**

Phase 8E eliminates the `sorry` in `N{N}_quadratic_le_energyUpper` for all three values of $N$.

**Key new theorem** — `sign_aware_energy_bound` in `NymanBeurlingCertificate.lean`:

Given interval certificates $G_{lo}(h,k) \le G_{hk} \le G_{hi}(h,k)$ and $l_{lo}(k) \le l_k \le l_{hi}(k)$, the energy form is bounded above by the computable rational quantity:
$$
\underbrace{\sum_{h,k} c_h c_k \cdot \begin{cases} G_{hi}(h,k) & \text{if } c_h c_k \ge 0 \\ G_{lo}(h,k) & \text{otherwise} \end{cases}}_{\text{signAwareQuadBoundQ}} + \underbrace{\sum_k (-2) c_k \cdot \begin{cases} l_{lo}(k) & \text{if } c_k \ge 0 \\ l_{hi}(k) & \text{otherwise} \end{cases}}_{\text{signAwareLinBoundQ}} + 1
$$
Proof: two `Finset.sum_le_sum` applications with `by_cases` on signs + `nlinarith`. Fully machine-verified, no `sorry`.

**Proof structure** for `N{N}_quadratic_le_energyUpper`:
```lean
  have hbound := sign_aware_energy_bound ... (toy_gram_certified) (lin_certified)
  have heq : signAwareQuadBoundQ ... + signAwareLinBoundQ ... + 1 = witnessEnergy.energyUpper
           := by native_decide   -- rational arithmetic equality
  calc energy_form ≤ signAware... + 1 := hbound
                 _ = energyUpper      := by exact_mod_cast heq
```

**Sorry inventory after Phase 8E:**

| File | Sorry | Status |
|------|-------|--------|
| `NymanGramN10.lean` | 0 | ✓ fully verified |
| `NymanGramN20.lean` | 1 (`ldl_identity`) | LDL^T exact identity fails after rational truncation — only used by `certN`, not by the distance bound proof |
| `NymanGramN50.lean` | 1 (`ldl_identity`) | Same as N=20 |
| `NymanBeurlingCertificate.lean` | 0 (in new code) | ✓ |
| Cross-cutting axioms | `innerProductChiRho_formula`, `baezDuarteL2Error_gram_expansion`, `lin_certified` | Analytic axioms deferred to Phase 9+ |

The `ldl_identity` sorry does **not** appear in the proof of `baezDuarteDistance_N{N}_bound`. It lives only inside `regCertN{N}` → `certN{N}`, whose distance certificate is axiom-backed (`interval_energy_bounds_baez_duarte_distance`) and separate from the main proof chain.

### 3.5 Phase 9: Asymptotic Phase (monotonicity + conditional tendsto)

Phase 9 establishes the asymptotic structure in `BaezDuarte.lean`, proving — modulo a single clearly-stated analytic axiom — that `BaezDuarteDistance N → 0`.

**Phase 9A — Monotonicity (proved, no sorry)**

```lean
theorem baezDuarteDistance_antitone : Antitone BaezDuarteDistance
```

Proof chain:
1. `bdApprox_embed_zero` — embedding N coefficients into N+1 with last = 0 preserves the approximation function pointwise (by `Fin.sum_univ_castSucc` + `Fin.snoc` simp lemmas).
2. `baezDuarteL2Error_embed_zero` — therefore the L² error is unchanged (by congruence on the integrand).
3. `baezDuarteDistance_antitone` — for each N, the infimum over `Fin (N+1) → ℝ` is ≤ infimum over `Fin N → ℝ` (by `ciInf_le` with the embedded vector + the embed-zero lemma).

**Phase 9G — Squeeze theorem (proved, no sorry)**

```lean
theorem baezDuarteDistance_tendsto_zero_of_energy_bound
    (f : ℕ → ℝ) (hf_bound : ∀ N, BaezDuarteDistance N ≤ f N)
    (hf_nonneg : ∀ N, 0 ≤ f N) (hf_tendsto : Filter.Tendsto f Filter.atTop (nhds 0)) :
    BaezDuarteCriterion
```
Proof: `squeeze_zero` (Mathlib) applied to `baezDuarteDistance_nonneg`, `hf_bound`, and `hf_tendsto`.

**Phase 9F — Analytic completeness → criterion (proved from axiom)**

The key analytic axiom, clearly named and scoped:
```lean
axiom nyman_beurling_l2_completeness :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∃ c : Fin N₀ → ℝ, BaezDuarteL2Error N₀ c < ε
```
This is the formal statement that $\chi_{(0,1]}$ lies in the $L^2$ closure of $\text{span}\{\rho_k : k \ge 1\}$. It is the crucial analytic content of the Nyman-Beurling theorem, which follows from RH (Báez-Duarte 2003) and conversely implies RH.

From this axiom, `BaezDuarteCriterion` is **proved** (not axiomized):
```lean
theorem baezDuarteCriterion_of_l2_completeness : BaezDuarteCriterion
```
Proof: given ε > 0, obtain N₀ and c from the axiom; `BaezDuarteDistance N₀ ≤ BaezDuarteL2Error N₀ c < ε` by `ciInf_le`; for all N ≥ N₀, `BaezDuarteDistance N ≤ BaezDuarteDistance N₀ < ε` by `baezDuarteDistance_antitone`.

### 3.6 Phase 10A: Axiom Decomposition and Honest Ledger

**Status framing (important):** Phase 9/10 does NOT prove RH. It formalizes the conditional route:

```
NymanBeurlingCriterion (RH-equivalent axiom)
  → BaezDuarteCriterion (proved via monotonicity + ciInf)
  → RH (Nyman-Beurling theorem axiom)
```

**Phase 10A** replaces the single opaque `axiom baez_duarte_criterion_implies_RH` with a named, structured decomposition:

1. `NymanBeurlingCriterion` — *defined* as the ε-ε completeness statement (not axiomized)
2. `nymanBeurlingCriterion_iff_baezDuarteCriterion` — **proved** (Phase 10A): the two criteria are equivalent via monotonicity + `ciInf` contradiction argument
3. `nyman_beurling_criterion_iff_RH` — **axiom** (sole remaining RH-level axiom): the classical Nyman-Beurling theorem
4. `baez_duarte_criterion_implies_RH` — **theorem** (derived, no longer axiom): follows from 2 + 3

**Complete axiom ledger (Phase 10A state)**

| Axiom / sorry | Location | Class |
|--------------|----------|-------|
| `nyman_beurling_criterion_iff_RH` | `BaezDuarte.lean` | **RH-equivalent** — the deep analytic content |
| `innerProductChiRho_formula` | `NymanBeurlingCertificate.lean` | Integral evaluation (deferred analytic) |
| `baezDuarteL2Error_gram_expansion` | `NymanBeurlingCertificate.lean` | Quadratic expansion identity (deferred analytic) |
| `lin_certified` (N=10,20,50) | Generated files | Rational bounds on $(log(k+1)+1-\gamma)/(k+1)$ |
| `ldl_identity` sorry (N=20,50) | Generated files | LDL^T truncation artefact (non-critical, not in main chain) |
| `certified_interval_trusted` | `NymanBeurlingCertificate.lean` | Numeric interval bounds for Gram entries |
| `interval_energy_bounds_baez_duarte_distance` | `NymanBeurlingCertificate.lean` | Bridge from interval model to distance bound |

**Honest status of the project:**

```text
We have formalized a large part of the Nyman-Báez-Duarte proof architecture:
  - certified finite Gram/energy machinery (N=10/20/50);
  - a formal bridge from finite certificates to BaezDuarteDistance bounds;
  - a proved monotonicity theorem (BaezDuarteDistance antitone);
  - a proved equivalence NymanBeurlingCriterion ↔ BaezDuarteCriterion;
  - a proved squeeze theorem (energy-bound → criterion).

We do NOT have:
  - a proof of nyman_beurling_criterion_iff_RH (the Nyman-Beurling theorem itself);
  - a proof of innerProductChiRho_formula or baezDuarteL2Error_gram_expansion;
  - an infinite certified energy sequence tending to 0 without RH-level assumptions.
```

The **main proof chain** (Phase 10A):
```
nyman_beurling_criterion_iff_RH             [1 axiom — RH-equivalent]
  → nymanBeurlingCriterion_iff_baezDuarteCriterion  [PROVED, Phase 10A]
  → baez_duarte_criterion_implies_RH        [THEOREM — derived]
  → RiemannHypothesis
```

For the finite numerical certificates (Phase 8E):
```
sign_aware_energy_bound (PROVED) + toy_gram_certified (named axioms) + lin_certified (axiom)
  → N{N}_quadratic_le_energyUpper (PROVED via native_decide)
  → baezDuarteDistance_N{N}_bound (PROVED)
```

### 3.7 Phase 10B/10C: Certified Energy Bridge and Criterion Architecture

**Phase 10B** clarifies that `nyman_beurling_l2_completeness` (axiomized in previous sessions) has been **removed**. Its content is now split into:
- `NymanBeurlingCriterion` — a *definition* (proved equivalent to `BaezDuarteCriterion` in Phase 10A)
- `nyman_beurling_criterion_iff_RH` — the *sole* RH-level axiom

This makes the proof debt explicit: one axiom encapsulates the full Nyman-Beurling theorem.

**Phase 10C** adds the bridge theorem:

```lean
theorem baezDuarteCriterion_of_certified_energy_sequence
    (E : ℕ → ℝ)
    (hcert : ∀ N, BaezDuarteDistance N ≤ E N)
    (hE : Filter.Tendsto E Filter.atTop (nhds 0)) :
    BaezDuarteCriterion
```

This is **proved** (trivially from Phase 9G squeeze theorem). It names the precise shape of what an infinite certified energy sequence would need to satisfy to close the argument without the RH axiom:

> *Produce a constructive E : ℕ → ℝ with E N → 0 and BaezDuarteDistance N ≤ E N for all N — without assuming NymanBeurlingCriterion — and RH is proved.*

The Phase 8E certificates give three data points:
- E(10) ≤ 0.02575, E(20) ≤ 0.02198, E(50) ≤ 0.03451

The N=50 value is worse than N=20 due to LDL^T truncation artefacts in the generator. With exact LDL^T, the sequence should be monotone decreasing (proved by `baezDuarteDistance_antitone`). Generating certificates for growing N with verified bounds tending to 0 is the next concrete computational target.

**Full build status (2026-06-30): 8488 jobs, 0 errors. Sorry inventory:**

| File | Line | Content |
|------|------|---------|
| `Basic/CriticalStrip.lean` | 18, 23 | Basic RH setup stubs |
| `Criteria/NymanBeurling/VasyuninGram.lean` | 23, 27 | Gram integral identity |
| `Criteria/NymanBeurling/G11IntegralEvaluation.lean` | 108 | G(1,1) analytic evaluation |
Total: **4 sorries** (down from ~20+ at Phase 8D start). None in the main proof chain except the RH-level axiom `nyman_beurling_criterion_iff_RH`.

### 3.8 Phase 10G: LDLᵀ Identity Closure

**Status (2026-06-30):** Zero sorries in `RiemannHypothesis/Certificates/`.

**N=20**: `ldl_identity` proved by `native_decide` using **exact** LDL^T entries (no `limit_denominator` truncation). The exact L and D have entries up to ~1500 digits; total 143K chars added to the file (new size 342K). `native_decide` compiles to native code and verifies the 20×20 rational matrix equality efficiently.

**N=50**: `witnessN50`/`regCertN50`/`certN50` blocks **not emitted**. These were dead code — `baezDuarteDistance_N50_bound` uses `baezDuarteL2Error_gram_expansion + sign_aware_energy_bound`, not the LDL^T witness. Exact LDL^T entries for N=50 would reach ~8750 digits (4.4MB), making `native_decide` infeasible. The comment in the generated file documents this explicitly.

**Generator design (reproducible for all N):**
```python
WITNESS_PROOF_MAX_N = 10    # fin_cases + norm_num (N²=100 cases)
NATIVE_DECIDE_MAX_N = 20    # exact LDL^T + native_decide
# N > 20: witness scaffolding not emitted (dead code at scale)
```

The witness scaffolding (`witnessN*`/`regCertN*`/`certN*`) was pre-Phase-10D legacy code. Phase 10D proved `baezDuarteL2Error_gram_expansion` directly, making the LDL^T witness unnecessary for any certificate's main distance bound proof.

**Remaining sorry inventory (4 total):**

| File | Line | Content |
|------|------|---------|
| `Basic/CriticalStrip.lean` | 18, 23 | Basic RH setup stubs |
| `Criteria/NymanBeurling/VasyuninGram.lean` | 23, 27 | Gram integral identity |
| `Criteria/NymanBeurling/G11IntegralEvaluation.lean` | 108 | G(1,1) analytic evaluation |

---

## 4. Phase 10T: Eliminating the Cotangent-Interval Axiom Family (k = 1..50)

At the start of this phase the project's honest weak point was numeric, not structural: `RiemannHypothesis/Certificates/Generated/VasyuninPrimitiveBoundsCore.lean` contained **1,225 `axiom cot_pi_A_K_bounds`** declarations — rational interval bounds on `cotangentTermV a k = cos(πa/k)/sin(πa/k)`, originally computed by an external Python/Arb script and simply *asserted* into Lean rather than kernel-checked. A green `lake build` therefore did **not** mean these specific numeric claims had been verified by anything other than trust in the external tool.

**Method.** Each bound is proved by: bounding the target angle via `Real.pi_gt_d20`/`Real.pi_lt_d20` (Mathlib's 20-digit π bounds), halving the angle down to a small base value, Taylor-bounding `cos`/`sin` there via `Real.cos_bound`/`Real.sin_bound`, then re-doubling `n` times (`cos(2θ)=2cos²θ-1`, `sin(2θ)=2sinθcosθ`) back up to the target angle, and finally dividing via a generic `cot_bound_of_sin_cos_bounds` lemma. Reusable infrastructure lives in `RiemannHypothesis/Certificates/TrigIntervalSweep.lean` / `CotangentBoundsCore.lean`.

**Structural shortcuts** avoid a fresh 32-level halving proof for every pair `(a,k)`:
- exact `π/2` (`2a = k`) → `cot = 0` trivially;
- obtuse pairs (`2a > k`) reduce via `cotangentTermV a k = -cotangentTermV (k-a) k`;
- reducible fractions (`gcd(a,k) > 1`) reduce via `cotangentTermV_gcd_reduce`;
- when a reduction target's own public bound is numerically too loose to imply the original pair's *exact pre-declared literal* (checked via exact `Fraction` arithmetic before writing any Lean), a private `_fresh_aux` certificate is generated for the reduction target's acute companion angle instead — chaining gcd-reduction and obtuse-negation together where both apply.

**Progression** (each stage independently `#print axioms`-verified — not taken from any tool's self-report — and tagged):

| Stage | k-range | Axioms retired | Tag |
|---|---|---|---|
| 10T₁ | k ≤ 10 | 45 | — |
| 10T₂ | k ≤ 20 | 145 | `verified-phase-10T2-13B` |
| 10T₃ | k ≤ 30 | ~210 | `verified-phase-10T3-k30` |
| 10T₄ | k = 31–40 | 345 | `verified-phase-10T4-k40` |
| 10T₅ | k = 41–50 | 445 | `verified-phase-10T5-k50` |

**Final state: 1225 → 0.** Every `cot_pi_A_K_bounds` in the project (k = 1 through 50) is now a kernel-checked `theorem`, not an `axiom` — 1225 theorems, 0 axioms remaining for this family, project-wide.

### 4.1 A regression, caught and fixed twice

This project's own methodology caught two real defects during Phase 10T, both by the same discipline: never trust a tool's "built, verified, done" self-report — independently re-run `lake build` and `#print axioms`, and for generated-file diffs, compare `def` values as a **sorted name+value set**, not a positional `git diff`.

1. **2026-07-02 incident.** A tool committing directly to `main` silently changed several pre-existing `def cot_pi_A_K_lower`/`upper` rational literals into symbolic references to other pairs' bounds (e.g. `def cot_pi_10_22_upper := - cot_pi_12_22_upper`) — plausible-looking, but not the literal the surrounding proofs were built against. Caught by an independent rebuild, not by the committing tool's own report. This incident motivated the `AGENTS.md` "Multi-tool coordination protocol" (§6) and `scripts/verify.sh`.
2. **2026-07-04 recurrence, Phase 10T₅.** The exact same defect class reappeared: a generator script's `def`-line handler had a stray branch that replaced gcd-reducible pairs' literals with symbolic references (306 pairs / 606 lines affected). Caught the same way — an exhaustive sorted-set comparison of all 2450 `cot_pi_*` def lines against the last verified tag showed 606 non-empty diffs where 0 were expected. Root-caused and fixed by removing the offending branch entirely: generator scripts must never touch `def` lines under any circumstance; all reductions happen inside the `theorem := by ...` proof body.

**Lesson embedded in tooling**: `scripts/verify.sh` Step 2 checks exactly this — do the pre-existing `def name : Type := value` lines, taken as a set, change at all. It is now the mandatory pre-merge gate for this project, run by whichever tool proposes a merge, checked independently by whichever tool proposes to accept it.

## 5. Phase 10U: Removing `native_decide`

Seven generated certificate files (`NymanGramN1/2/3/5/10/20.lean`, `NymanGramN50_Tail.lean`) used `native_decide` — 16 occurrences total — to close a decidable rational-equality goal (`signAwareQuadBoundQ ... + signAwareLinBoundQ ... + 1 = witnessEnergy.energyUpper`) or, for N=20, an LDL^T certificate match. `native_decide` compiles to native machine code and trusts the whole Lean compiler, not just the kernel — disallowed by this project's own `AGENTS.md` rule, and a strictly weaker trust guarantee than everything else in the pipeline.

**Replacements, all genuine kernel-checked proofs:**
- N=1/2/3/5/10: direct `norm_num` unfolding of the relevant definitions.
- N=20: the single `ldl_identity` `native_decide` (a 20×20 exact-rational matrix identity) was split into 20 per-row lemmas (`ldl_identity_row_0`..`19`), each closed by explicit computation — notably slow to compile (order of an hour) since kernel-checking this much large-rational arithmetic is exactly what `native_decide`'s compiled-code path existed to avoid, but fully trustworthy.
- N=50: already documented as infeasible for `native_decide` at this scale (exact LDL^T entries would run to ~8,500 digits) — closed instead via `simp` with a raised `maxSteps` bound, unfolding the ~50 gram-entry definitions directly.

**Result: 16 → 0 `native_decide` occurrences, project-wide.** Tag `verified-phase-10U-native-decide-removed`.

## 6. Verification Tooling and Multi-Tool Coordination

As the project scaled, it began being worked by multiple independent AI tools (Claude Code, Codex, Google Antigravity/Gemini) across separate sessions — never concurrently on the same branch, always via isolated git worktrees each with a **real copy** (never a symlink — a symlinked `.lake` build cache caused real cross-session corruption once) of the `.lake` build cache.

**`scripts/verify.sh`** is the mandatory pre-merge gate, run before any branch reaches `main`, regardless of which tool produced it:
1. Full `lake build RiemannHypothesis` must succeed.
2. Every pre-existing `def` line, compared as a **sorted name+value set** (not positional `git diff`, which produced a recurring false-positive class on large generated-file diffs — a short axiom replaced by a long theorem proof causes git's Myers diff to represent unrelated, byte-identical lines elsewhere as "moved"), must be unchanged unless the change is a deliberate, disclosed, reviewed correction.
3. Repo-wide `axiom`/`sorry`/`native_decide` counts, reported and compared against the baseline.
4. `#print axioms` on a bounded sample of new/changed theorems since baseline — including theorems whose signature pre-existed as a `sorry`-stub with only the body filled in (a second blind spot fixed alongside the first) — checked against `scripts/verify_known_sorries.txt`, an explicit allowlist of names individually confirmed to carry a genuinely documented, open `sorry` rather than a silent gap.

**A note on trusting tool self-reports.** Every substantive claim in this report — every "proved," every "clean," every "verified" — was independently re-derived by a human-directed audit (a fresh `lake build`, a fresh `#print axioms`, a fresh exhaustive diff), not accepted from any tool's own narration. This discipline caught the two regressions in §4.1, a genuinely false pre-existing axiom (§7.3), and, separately, a pattern where one tool's own wrap-up summaries became disconnected from its concurrent real work (accurate edits, confused narration) — underscoring that in a multi-tool pipeline, the code and build state are the only reliable source of truth.

## 7. Phase 13: The Vasyunin Local Bridge

### 7.1 A false theorem, found and corrected

An earlier version of the Vasyunin bridge asserted `baezDuarteGramEntry_eq_tsum_intervals`: that `baezDuarteGramEntry h k` equals the sum, over `m`, of the fractional-part integral on `[1/(m+1), 1/m]`. This is **false** — those intervals tile `(0,1]`, but `baezDuarteGramEntry` integrates over all of `(0,∞)`, and the tail `(1,∞)` contributes a generically nonzero amount (e.g. for `h=k=1`, numerically `≈0.2605` vs. `≈0.9800`). This was formally disproved (`baezDuarteGramEntry_ne_tsum_intervals_disproof`) rather than silently worked around, and replaced with the honest decomposition: `baezDuarteGramEntry_eq_tsum_intervals_add_tail` (fully proved) splits the entry into the interval-tsum piece plus an explicit tail term, and the corrected target field `interval_sum_add_tail_eq_cotangent_formula` requires the tsum **plus** the tail (not the tsum alone) to equal the Vasyunin cotangent formula.

### 7.2 V1–V7: decomposing the remaining hard theorem

`interval_sum_add_tail_eq_cotangent_formula`'s remaining gap — now isolated to a single theorem, `tsum_shifted_integrals_eq_cotangent_sum` in `VasyuninBridge.lean` — was deliberately **not** attempted directly (this project's own rule: never point an agent at a theorem this large in one pass). A dedicated file, `VasyuninCotangentRecognition.lean`, builds supporting infrastructure incrementally:

- **`real_cot_series_rep'`**: Mathlib's own Mittag-Leffler cotangent expansion (`Complex.cot_series_rep'`) is valid on all of `ℂ_ℤ`, not merely the upper half-plane as `VasyuninBridge.lean`'s own (now corrected) doc-comment assumed — but its *iterated-derivative* form, needed for the trigamma-type series this problem actually requires, **is** restricted to the upper half-plane. This theorem builds the genuine real-variable version directly, unrestricted.
- **`realTrigammaSeriesInt_reflection`**: the real-variable reflection identity `∑'_{n∈ℤ} 1/(x+n)² = π²/sin²(πx)` — a closed form Mathlib does not otherwise provide — proved via term-by-term differentiation of the real Mittag-Leffler series on integer-avoiding intervals (`Mathlib.Analysis.Calculus.SmoothSeries.hasDerivAt_tsum_of_isPreconnected`).
- **`shiftedIntegralTsum_eq_integral_of_rescaled_series'`**: the sum-integral interchange needed to connect the shifted-integral tsum to the trigamma series, made fully **unconditional** by discharging its integrability hypothesis outright — via the global, non-asymptotic bound `Int.fract y ≤ y` for all `y ≥ 0` (no case split), showing the integrand's apparent `1/s²`-type singularity at `s=0` is exactly cancelled, not a genuine obstacle (unlike a *different*, harder integrand — `genIntegrandTransformed` — elsewhere in `VasyuninBridge.lean`, whose own open `sorry` this does *not* discharge).

Every theorem above is independently confirmed `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]` only). **What remains open**: connecting the one-sided (`ℕ`-indexed) trigamma series actually used downstream to the two-sided reflection identity, and — the genuinely deep remaining mathematical core — the classical sub-arc partition and Dedekind-sum-style cotangent reciprocity argument (Vasyunin's own multi-page computation) inside `shiftedIntegralTsum_period_reduction`, which is precisely and honestly marked `sorry`.

### 7.3 A false axiom, found and corrected

Independently of the above, an audit ahead of a mechanical axiom-elimination pass (Phase 10V, log-bound axioms) found that a pre-existing, widely-used (1,548 call sites across 27 files) definition asserted something **mathematically false**: `prim_pi_upper : ℚ := 884279719003555 / 281474976710656`, evaluating to `3.141592653589793115...`, is strictly *less* than `π = 3.14159265358979323846...` — so the axiom `Real.pi ≤ prim_pi_upper` could never have been proved, because it isn't true. Confirmed independently via exact decimal comparison before any fix was applied. Corrected to the next representable value (`884279719003556/...`, genuinely `≥ π`), converted from `axiom` to a real `theorem` (via Mathlib's `Real.pi_gt_d20`/`pi_lt_d20`), and re-verified with a full project rebuild to confirm no downstream proof depended on the old, too-tight (and false) value in a way that broke.

### 7.4 The H13-J period-reduction chain (Báez-Duarte–Balazard–Landreau–Saias)

The open core of §7.2, `shiftedIntegralTsum_period_reduction`, turned out to have a tractable elementary proof chain in the literature — not via the initially-investigated digamma route (a cited "Belhadj–Goubi identity" could not be located or verified and was **abandoned as a dead end**, not silently assumed), but via Propositions 12/15/16/21/22/88/89 of Báez-Duarte–Balazard–Landreau–Saias, arXiv:math/0306251, formalized in `VasyuninPeriodReduction.lean`. Status, each item independently `#print axioms`-checked:

- **Proposition 15** (Gauss-sum/floor-sum identity) and **Proposition 12** (lattice-point double-counting: `∑⌊mθ⌋ + ∑⌊n/θ⌋ = ⌊x⌋⌊θx⌋ + ⌊x/h⌋` for `θ = k/h` coprime): fully proved.
- **A real convention bug caught by numerics before formalization**: the paper's `B₁` is the *Dedekind sawtooth* (value `0` at exact integers, not `-1/2`); the first frozen statement used the wrong convention and was numerically refuted, then corrected — the same "verify the statement before proving it" discipline as §7.1/§7.3.
- **Proposition 21, rational case** (`baezDuarte_prop21_rat_of_prop12`): fully proved, unconditional, for every real `x > 0`. (The paper's general-real-θ statement `baezDuarte_prop21` is kept as a documented, allowlisted `sorry` purely for fidelity; nothing downstream uses it.)
- **Proposition 22's four analytic ingredients**, each proved: two discrete Abel/Stieltjes summation-by-parts identities (`stepFunction_abel_stieltjes_identity` and its scaled companion, `∑_{m≤x} a_m/m = S(x)/x + ∫₀ˣ S(u)/u² du`), the quadratic change-of-variables identity (`fract_sq_scaled_integral`), and **Proposition 16**, the Frullani-type identity `∫₀ˣ t⁻²({θt} − θ{t}) dt = θ log(1/θ) + θ∫ₓ^{θx} u⁻²{u} du`, proved for *general* positive real `θ, x` (stronger than the rational case needed) with new local integrability infrastructure for discontinuous fractional-part integrands.
- **Proposition 22 itself** (`baezDuarte_prop22_rat`): the full Stieltjes-integral identity for the weighted sums `∑ B₁(mθ)/m + θ∑ B₁(n/θ)/n`, **assembled and proved** from the four ingredients plus Proposition 21 applied pointwise inside the integral — `#print axioms`-clean, merged and tagged (`verified-h13-prop22-proved`).

**The chain is now COMPLETE** (tag `verified-h13-complete`), closing every remaining H13 `sorry`:

- **Proposition 48** (`BBLSPhiOne.lean`): the conditionally convergent `φ₁(p/q) = ∑_{k≥1} B₁(kp/q)/k` converges to `(π/2q)·V(p,q)` — for **all** positive `p, q`, coprime or not (numerically confirmed on non-coprime pairs before formalization). Proved with no digamma API at all: an absolutely convergent surrogate series, the reflection identity derived from this project's own real Mittag-Leffler cotangent expansion (§7.2), and a periodic-mean-zero Dirichlet-series limit theorem (existence via the discrete Abel identity + uniformly bounded partial sums; value via the block subsequence `N = mq`).
- **Proposition 87**: `A(1) = ∫₀^∞ {t}²/t² dt = log 2π − γ`, via exact block integrals telescoping to `2N − H_N − 2N·log N + 2·log N!`, then Mathlib's Stirling (`tendsto_stirlingSeq_sqrt_pi`) and Euler–Mascheroni (`tendsto_eulerMascheroniSeq`) limits.
- **Propositions 88–89, fused**: the `x → ∞` limit of Proposition 22 gives `A(k/h)` in closed cotangent form for all positive `h, k` — the conditional-convergence risk flagged for Proposition 88 dissolved entirely, because Proposition 48's generality supplies convergence at every rational directly, with the limit identity taken along the reduced coprime pair and the series limits evaluated at the non-reduced pair.
- **The period reduction**: unfolding the shifted-integral tsum over `lcm`-periods (translation + countable disjoint-union integration), substituting `s = t·h`, and assembling into `vasyuninBEntry` — discharging `shiftedIntegralTsum_period_reduction`, `tsum_shifted_integrals_eq_cotangent_sum`, and `vasyuninBEntry_correct_axiom`.
- **A third false statement caught and corrected** (continuing §7.1/§7.3's pattern): `vasyuninBEntry_correct_axiom` as originally recorded was hypothesis-free and therefore **false at `h = 0`** (the Gram integrand vanishes identically while `vasyuninBEntryFormula 0 k = (log 2π − γ)/(2k) ≠ 0`). Positivity hypotheses were added and all 2,004 call sites across the generated certificate files patched; the full 8,616-job rebuild and verification gate passed.

**H13 status: closed.** Exactly one `sorry` remains in the entire project — `baezDuarte_prop21`, the general-real-θ statement of Proposition 21, kept purely for fidelity to the paper's own phrasing; nothing depends on it.

## 8. Phase 14: Linear Möbius / Dirichlet Estimates

The linear half of the analytic-debt program targets `explicitLinearCenteredRemainder N = 2·(explicitLinearMobiusSum N + 1)`, split into two classical Dirichlet-style sums, `cutoffMobiusOverKSum N → 0` and `cutoffMobiusLogOverKSum N → -1`, each at rate `O(1/log N)` — smoothed/cutoff analogues of `∑μ(k)/k ≈ 0` and `∑μ(k)log k/k ≈ -1`, which follow classically from the behavior of `1/ζ(s)` near `s=1`.

**Proved**: exact finite Abel-summation identities (`cutoffMobiusOverKSum_eq_abel_sum`, `cutoffMobiusLogOverKSum_eq_abel_sum`), replacing what were previously `sorry`-stubbed placeholder statements, via an explicit induction lemma (`sum_Icc_mul_sub_endpoint_eq_sum_partial`).

**Explicitly and honestly isolated, not proved**: the actual quantitative analytic input, as a new hypothesis structure `MobiusPNTStyleEstimates` (bounds on the Abel-transformed Möbius/Möbius-log summatory functions at rate `O(1/log N)`) — the same "debts as explicit structure fields" pattern used throughout this project. A research pass (§ methodology: check Mathlib before assuming a gap) confirmed Mathlib has finite/continuous Abel summation, the Möbius-zeta convolution identity `L_μ(s) = 1/ζ(s)` for `Re(s) > 1`, and closed-half-plane zeta nonvanishing — but **not** quantitative Mertens/PNT-type bounds for the relevant partial sums, nor the boundary-passage argument at `s=1`. This is genuinely substantial classical analytic number theory, not a short formalization gap.

Tag `verified-phase-14-linear-abel`.

### 8.1 The H14M track: no shortcut, then classical groundwork (now parked)

Two independent research passes converged on the same verdict, **do not re-litigate without new information**: the `MobiusPNTStyleEstimates`/`ClassicalMertensAPI` fields cannot be obtained from any weaker-than-PNT input. The quantitative requirement is `M(x) ≪ x/log²x`; Mathlib's qualitative PNT (Wiener–Ikehara, and `pi_alt` in the external `PrimeNumberTheoremAnd` project) is Tauberian and *in principle* cannot yield an effective rate. Even the purely qualitative field `mobius_sum_zero` (`∑μ(k)/k → 0`) was confirmed by targeted reconnaissance to be missing from both Mathlib and `PrimeNumberTheoremAnd` — the bridge (a sign-changing Tauberian theorem for `1/ζ`, or any `M(N)/N → 0` result) does not exist there yet. The genuinely good news: the classical **1899 de la Vallée Poussin zero-free region alone** already gives `M(x) ≪ x·exp(-c√log x)`, far stronger than needed — so this debt is 125-year-old textbook material actively being formalized upstream, not open research.

On that basis a lettered plan (H14M-A…I) was drawn up and its first two steps banked, both merged after independent verification:

- **H14M-A** (`verified-h14m-a-zero-free-api`): the zero-free-region *statement* frozen as a hypothesis structure `DeLaValleePoussinZeroFreeRegion` (`ζ(s) ≠ 0` for `Re s > 1 − c/log(|Im s|+2)`), with proved sanity corollaries (consistency with the closed-half-plane nonvanishing Mathlib already has).
- **H14M-B, ingredients only** (`verified-h14m-b-zero-free-subpieces`, 13 lemmas, no `sorry`): the elementary `3-4-1` inequality `0 ≤ 3 + 4cos θ + cos 2θ`; its unit-circle and logarithmic Euler-factor positivity forms (a public reproof of a *private* Mathlib lemma in `Nonvanishing.lean`, via the Taylor series of `−log(1−z)`); von Mangoldt log-derivative wrappers `L↗Λ(s) = −ζ'(s)/ζ(s)` with the termwise cosine expansion `Λ(n)n^{−σ}cos(t log n)`; and local wrappers at `s = 1` (residue, regular-part boundedness, and a genuinely new simple-zero log-derivative residue lemma).

**Honestly not done, stated in the code's own docstrings**: no *instance* of `DeLaValleePoussinZeroFreeRegion` is constructed — that requires combining the positivity across `σ, σ+it, σ+2it`, handling zeros of arbitrary multiplicity (the residue lemma above covers only simple zeros), and the global contour/growth estimates.

**Architecture finalized** (tag `verified-h14-finalized-decay`): the quantitative Mertens debt is now reduced to a *single* classical statement, `ClassicalMertensDecay` (`|M(N)| ≤ C·N·exp(−a√(log N))` — exactly the output of the 1899 de la Vallée Poussin zero-free region), with the conversion to the project's `N/log³N` bound **proved unconditionally** (`mertens_bound_of_decay`, via elementary `t^A·e^{−a√t}` calculus). The three fields not yet derived from decay (`mobiusLogSummatory_bound`, `mobius_sum_zero`, `mobiusLog_sum_neg_one` — the Abel/Axer-type arguments) remain explicitly named in `ClassicalMertensResidualInputs`, and `ClassicalMertensAPI.ofDecay` assembles the full API from the two. Since then, the residual has been actively shrunk (tags `verified-h14-residuals-partial`, `verified-h14-r1-logbound`): the log-summatory bound `|L(N)| ≤ C_L·N/log²(N+2)` is now **derived from the decay statement alone** (split-sum tail estimate + the conversion calculus), and the convergence of `∑ μ(k)/k` to *some* limit is proved under decay (Abel/Cauchy argument). H14's remaining debt is the decay statement plus **exactly two normalization identifications**: `MobiusOverKLimitIsZero` (the Axer step — that the limit is `0`) and `mobiusLog_sum_neg_one` (the `−1` limit). A quantitative Axer attempt (hyperbola identity + blockwise Abel against the Möbius summatory, targeting `|∑_{k≤N}μ(k)/k| ≤ C·e^{−c√log N}`, which would also unlock the `−1` limit via a Chebyshev-`O(N)` argument) is in flight.

## 9. Phase 15: Quadratic Log-Cotangent Interaction

The deepest of the three analytic debts. The target, `explicitQuadraticInteractionRemainder N = (double sum of an interaction kernel) - 1 → 0` at rate `O(1/log N)`, was deliberately **not** approached by attempting the bound directly. Per this project's own rule for problems at this scale — freeze the exact object, gather numerical evidence, decompose structurally, and only then consider an actual estimate — the sequence so far:

- **Kernel frozen and symmetric** (`quadraticInteractionKernel_symm`, handling `h=0`/`k=0` edge cases explicitly, not by omission).
- **Numerical diagnostics** (`experiments/phase15_quadratic_interaction_diagnostics.py`, independently re-run and reproduced exactly): at N=1000, the diagonal contributes **exactly 0**; the target `+1` limit comes from broad cancellation between coprime pairs (`-0.30`) and non-coprime pairs (`+1.31`), not from any single narrow window — a `gcd`-exact breakdown shows wild swings (gcd 6–10 alone: `+1.72`, larger in magnitude than the whole target).
- **Structural decomposition** motivated directly by that finding: diagonal/off-diagonal split, then a `gcd`-stratified partition of the off-diagonal part (`quadraticInteractionGcdSlice`, plus an exact identity that the full double sum equals `∑_g gcdSlice`).
- **The diagonal case, resolved exactly** (not merely bounded): `cotangentSumVFormula h h = 0` identically, because each summand contains `Int.fract(a·h/h) = Int.fract(a) = 0` for the integer `a` — so `quadraticInteractionKernel h h = 0` and hence `quadraticInteractionDiagonal N = 0` for every `N`, trivially satisfying its share of the interaction bound.
- **A bridge theorem**, `explicitQuadraticInteractionRemainder_bound_of_analytic_subEstimates`, that takes three still-open hypothesis structures (`QuadraticInteractionDiagonalEstimate`, `QuadraticInteractionGcdMainTermEstimate`, `QuadraticInteractionGcdSliceErrorEstimate`, bundled as `QuadraticInteractionAnalyticSubEstimates`) — none of them proved true — and derives the combined interaction bound via genuine triangle-inequality/finite-sum algebra. This is pure logical wiring: *if* the three sub-estimates hold, the combined bound follows; it says nothing about whether they do.

**What remains completely open**: identifying and proving the actual per-`gcd`-stratum main term (why the sharp `gcd` 6–10 contribution?) and bounding the error mass — the genuinely deep, unattempted mathematical core of this debt, likely the hardest single piece in the whole project per its own diagnostics.

### 9.1 Reframing the open core: Estermann route (partial) and the Farey-cell correlation

Two further structural steps, both merged after independent verification, sharpened *what kind* of problem the open core actually is:

- **BBLS/Estermann contour route, a partial success** (`BBLS_EstermannContourPackage` + wiring theorems): the mysterious `+1` main term is *explained* by a genuine, checkable residue mechanism (the pole structure of the Estermann function in the Báez-Duarte–Balazard–Landreau–Saias contour argument) — but the route does **not** by itself close the error estimates; the package honestly isolates what the contour argument would still require as unproved hypothesis fields.
- **The canonical reframing** (`fareyCellMobiusCorrelationSum`, `FareyCellMobiusCorrelationEstimate`, `FareyCellGcdSliceErrorDecomposition` + wiring): the remaining gap is a **two-linear-forms Möbius correlation estimate over Farey cells** — a Chowla/Elliott-type correlation problem, explicitly **not** a Bombieri–Vinogradov/equidistribution problem (a tempting but wrong reduction, recorded as such to prevent future re-derivation). Relevant modern literature to consult when this is picked up: Matomäki–Radziwiłł–Tao, Tao–Teräväinen, Lichtman–Teräväinen, Frantzikinakis–Host, Harper/Klurman/Mangerel. The hypothesis structures isolate exactly this correlation estimate as the single named debt; everything around it is proved wiring.

### 9.2 The norm representation (Phase 15H), unlocked by H13's closure

With the Vasyunin bridge proved (§7.4), the interaction kernel acquired an **unconditional integral representation** (tags `verified-h15-kernel-gram`, `verified-h15-h3-norm-identity`):

- `quadraticInteractionKernel h k = baezDuarteGramEntry h k − (log 2π − γ)/2·(1/h + 1/k)` — the H15 kernel is *literally* the Báez-Duarte Gram integral minus its smooth part (the first identity is one `ring` away from the definitions; nobody had noticed).
- The **norm identity**, proved for a general weight and instantiated at the Möbius cutoff: `∑∑ c(h)c(k)·K(h,k) = ∫₀^∞ (∑ c(h)·{1/(hx)})² dx − (log 2π − γ)·(∑ c(h)/h)·(∑ c(k))`, wired all the way to `explicitQuadraticInteractionRemainder`.
- **The first unconditional inequality on the H15 quadratic form** (`quadratic_form_ge_neg_linear`), free from the positive-semidefiniteness of the norm term.

**What this changes**: the "mysterious broad cancellation across gcd strata" from the §9 diagnostics is now *structural* — the wild per-stratum cotangent fluctuations live inside a manifestly nonnegative squared L²-norm, and per-stratum bounding is provably the wrong decomposition.

The staged finish attempt then ran to its designed conclusion (tag `verified-h15-norm-residual`): exact χ–ρ cross identities and the completed-square decomposition are proved; H14's linear machinery provably controls the centered linear term; and everything that resists is isolated in **one field** — `QuadraticInteractionNormResidual`, a single `C/log(N+2)` bound on the defect-energy/log-gamma package — with proved bridges delivering full `QuadraticInteractionEstimates` from (H14 classical inputs) + (that one field). A strict no-RH-circularity guard governed the whole derivation (nothing on the conclusion side of the Báez-Duarte criterion was assumed). Numerical diagnostics (independently re-run) confirm the isolated bound holds with room to spare: the remainder empirically decays like `≈ 0.72/log²N`, a full logarithm faster than required. H15's open content is that single bound.

## 10. The Fourth Debt: Nyman–Beurling ⇒ RH

Even a fully closed set of analytic debts (§7–9) only yields a theorem-proved Báez–Duarte criterion. The step from there to unconditional RH is `nyman_beurling_criterion_iff_RH` (`BaezDuarte.lean`), still a bare, explicitly-labeled axiom — the classical Nyman (1950) / Beurling (1955) / Báez-Duarte (2003) theorem itself. A staged plan for this ("Phase NB") exists but has not been started: split the bare `↔` into two one-directional theorems and pursue only the forward direction (`NymanBeurlingCriterion → RH`, the direction that actually turns this project's work into RH) via a Mellin-transform vanishing argument, deferring the converse (the full classical Beurling density/cyclicity theorem) indefinitely. Notably, `nymanBeurlingCriterion_iff_baezDuarteCriterion` — a step the plan initially assumed was still open — is **already proved** in the repo (Phase 10A); the actual remaining gap is narrower than it first appears.

## 11. Current Honest Status

```text
Axiom count:            1364 (original) → 133 (current), a reduction of >90%
  of which cot_pi_*_bounds:   1225 → 0        (Phase 10T, fully closed)
  of which native_decide:       16 → 0        (Phase 10U, fully closed)
  of which prim_log/log_certified/euler_gamma:  87 (open, mechanical, Phase 10V, in progress)
  of which dead axioms from abandoned exploratory strategies: ~46 (not on the active path)
sorry count:             1 — baezDuarte_prop21 (general-real-θ Proposition 21,
                           kept for paper fidelity only, used by nothing; allowlisted
                           in scripts/verify_known_sorries.txt)

Three analytic debts (H13, H14, H15) toward a proved Báez-Duarte criterion:
  H13 (Vasyunin local bridge):        CLOSED (§7.4, tag verified-h13-complete) — the
                                       full BBLS chain incl. Props 48/87/88/89 and the
                                       period reduction; all Bridge sorries discharged
  H14 (linear Möbius/Dirichlet):      debt = ClassicalMertensDecay + exactly TWO
                                       normalization fields (§8.1): the Axer limit-zero
                                       identification and the −1 log-limit; both
                                       quantitative bounds now DERIVED from decay
  H15 (quadratic log-cotangent):      debt = ONE named field (§9.2):
                                       QuadraticInteractionNormResidual, a C/log(N+2)
                                       defect-energy bound, numerically ~1/log²N;
                                       bridges to full QuadraticInteractionEstimates
                                       from H14 inputs are proved

Total analytic debt toward a theorem-proved Báez-Duarte criterion: TWO
named statements — ClassicalMertensDecay (the 1899 de la Vallée Poussin
Mertens bound; the ENTIRE H14 API now follows from it alone, tag
verified-h14-complete-from-decay) and the centered Möbius–Bernoulli
correlation estimate (single 1/log²-rate field, tag
verified-h15-bernoulli-correlation, numerically supported with headroom;
proved bridges deliver the full quadratic estimates from these two) — plus
the separate Nyman–Beurling ⇒ RH bridge axiom (§10) for unconditional RH.
A companion LaTeX exposition for external mathematicians is at
docs/rh_pipeline_report.tex.

A fourth, separate gap beyond all three debts:
  nyman_beurling_criterion_iff_RH:    still a bare axiom; a staged plan exists,
                                       not yet started
```

**This project is, honestly, a certified reduction with explicit, named, individually-tracked analytic debts — not a proof of the Riemann Hypothesis.** What has changed since the original 1,364-axiom, trust-everything state is that every remaining gap is now precisely named, precisely stated, and independently `#print axioms`-auditable — nothing is hidden inside a misleadingly "green" build. Closing H13, H14, H15, and the Nyman–Beurling bridge would yield a genuine, unconditional, machine-checked proof of RH; each of the four remaining pieces is, on its own merits, a substantial, multi-session (or genuinely open-research-level) undertaking, and none should be assumed tractable merely because the surrounding architecture is now clean.

## References

### The criterion and its refinements

- B. Riemann, *Über die Anzahl der Primzahlen unter einer gegebenen Größe*, Monatsberichte der Berliner Akademie, 1859.
- B. Nyman, *On the One-Dimensional Translation Group and Semi-Group in Certain Function Spaces*, Ph.D. thesis, University of Uppsala, 1950.
- A. Beurling, *A closure problem related to the Riemann zeta-function*, Proc. Nat. Acad. Sci. USA **41** (1955), 312–314.
- L. Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the Riemann hypothesis*, Atti Accad. Naz. Lincei Rend. Lincei Mat. Appl. **14** (2003), 5–11.
- V. I. Vasyunin, *On a biorthogonal system associated with the Riemann hypothesis*, Algebra i Analiz **7** (1995); English transl. St. Petersburg Math. J. **7** (1996), 405–419.

### Sources directly formalized or numerically re-verified in this project

- L. Báez-Duarte, M. Balazard, B. Landreau, E. Saias, *Étude de l'autocorrélation multiplicative de la fonction « partie fractionnaire »*, Ramanujan J. **9** (2005), 215–240; arXiv:math/0306251. (Propositions 12, 15, 16, 21, 22 — the §7.4 period-reduction chain; Propositions 88–89 pending.)
- J.-F. Burnol, *A lower bound in an approximation problem involving the zeros of the Riemann zeta function*, Adv. Math. **170** (2002), 56–70.
- S. Bettin, J. B. Conrey, *Period functions and cotangent sums*, Algebra & Number Theory **7** (2013), 215–242. (Cotangent-sum growth bounds informing the Phase 10T certificate track.)
- T. Estermann, *On the representations of a number as the sum of two products*, Proc. London Math. Soc. (2) **31** (1930), 123–133. (The Estermann zeta function underlying the §9.1 contour package.)

### Classical analytic number theory background

- C.-J. de la Vallée Poussin, *Sur la fonction ζ(s) de Riemann et le nombre des nombres premiers inférieurs à une limite donnée*, Mém. Couronnés Acad. Roy. Sci. Belgique **59** (1899). (The zero-free region targeted by the H14M track, §8.1.)
- S. Ikehara, *An extension of Landau's theorem in the analytical theory of numbers*, J. Math. Phys. MIT **10** (1931), 1–12; N. Wiener, *Tauberian theorems*, Ann. of Math. **33** (1932), 1–100. (The Tauberian route already in Mathlib, shown in §8.1 to be inherently non-quantitative for this project's needs.)

### Historical framing (§0): discredited or heuristic approaches surveyed

- P. Turán, *On some approximative Dirichlet-polynomials in the theory of the zeta-function of Riemann*, Danske Vid. Selsk. Mat.-Fys. Medd. **24** (1948).
- L. de Branges, *The Riemann hypothesis for Hilbert spaces of entire functions*, Bull. Amer. Math. Soc. **15** (1986), 1–17.
- X.-J. Li, *The positivity of a sequence of numbers and the Riemann hypothesis*, J. Number Theory **65** (1997), 325–333.
- A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta function*, Selecta Math. (N.S.) **5** (1999), 29–106.

### Literature identified for the open H15 correlation estimate (§9.1; pointers recorded, not yet used)

- K. Matomäki, M. Radziwiłł, T. Tao, *An averaged form of Chowla's conjecture*, Algebra & Number Theory **9** (2015), 2167–2196.
- T. Tao, *The logarithmically averaged Chowla and Elliott conjectures for two-point correlations*, Forum Math. Pi **4** (2016).
- T. Tao, J. Teräväinen, *The structure of logarithmically averaged correlations of multiplicative functions, with applications to the Chowla and Elliott conjectures*, Duke Math. J. **168** (2019), 1977–2027.
- N. Frantzikinakis, B. Host, *The logarithmic Sarnak conjecture for ergodic weights*, Ann. of Math. **187** (2018), 869–931.
- Further works of J. D. Lichtman and J. Teräväinen, and of A. J. Harper, O. Klurman, and A. P. Mangerel, on correlations of multiplicative functions, as recorded in the project's research notes.

### Formal verification tools

- The mathlib Community, *The Lean mathematical library*, Proc. 9th ACM SIGPLAN Conf. on Certified Programs and Proofs (CPP 2020), 367–381.
- L. de Moura, S. Ullrich, *The Lean 4 theorem prover and programming language*, Proc. 28th Int. Conf. on Automated Deduction (CADE-28), 2021, 625–635.
- A. Kontorovich et al., *PrimeNumberTheoremAnd*, Lean 4 formalization repository, `github.com/AlexKontorovich/PrimeNumberTheoremAnd`. (Consulted for the §8.1 inventory; no code imported.)
