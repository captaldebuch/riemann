# H14 Borel-Jensen: Aristotle-Style Proof Search Specification

**Status:** Ready for formalization + automated proof search  
**Context:** H14 piece #2 of 3 (after FEFactor ✅)  
**Mathematical Foundation:** Classical zeta function factorization via Borel-Jensen formula  
**Approach:** Formalization spec for RL-guided tactic search + Lean kernel verification

---

## THE PROBLEM: Why Borel-Jensen Matters for H14

H14 requires proving that the Möbius-weighted linear sum decays like O(√x):
$$\left|\sum_{n \leq x} \frac{\mu(n)}{n}f\left(\frac{n}{x}\right)\right| \leq C \cdot x^{1/2 + \epsilon}$$

This is equivalent to: **the zeta function has no zeros on Re(s) = 1** (zero-free region).

**Borel-Jensen's insight:** Express ζ(s) as a product over its zeros. If ζ has a zero on Re(s) = 1, this product diverges. Control the product → control the decay.

---

## FORMALIZATION SPEC (Machine-Readable)

### Primary Theorem (Borel-Jensen Factorization)

```lean
theorem riemann_zeta_factorization_borel_jensen (s : ℂ) (hs : 1 < s.re) :
    riemann_zeta s = 
      (1 / (2 * π * I)) * 
      ∫ t in Set.Ioi 0, 
        (zetaDerivative (s + I * t) / riemann_zeta (s + I * t)) *
        (1 / (I * t)) dt +
      (explicit_finite_product_over_zeros s)
```

### Subsidiary Theorems

```lean
-- Zero-free region: ζ(s) ≠ 0 for Re(s) = 1
theorem riemann_zeta_nonzero_on_critical_boundary (t : ℝ) :
    riemann_zeta (1 + I * t) ≠ 0

-- Zeta derivative bounds
theorem zeta_derivative_bound (s : ℂ) (hs : s.re > 1) (ht : 1 < t) :
    ‖zetaDerivative s / riemann_zeta s‖ ≤ 
      C * (1 + |s.im|) ^ α

-- Product formula convergence
theorem borel_jensen_product_convergence (s : ℂ) (hs : 1 < s.re) :
    Summable (fun ρ : ℂ => ‖log(1 - (s / ρ))‖)
    where ρ ranges over all non-trivial zeros
```

### Key Definitions (To Establish)

```lean
-- Zeta derivative: ζ'(s) / ζ(s)
noncomputable def zetaLogDerivative (s : ℂ) : ℂ :=
  zetaDerivative s / riemann_zeta s

-- Borel-Jensen product over zeros ρ
noncomputable def borel_jensen_product (s : ℂ) : ℂ :=
  ∏' ρ : ZeroOfRiemannZeta, (1 - s / ρ) ^ (mult ρ)
  where mult ρ is the multiplicity of zero ρ

-- Explicit finite product (truncated)
noncomputable def explicit_finite_product_over_zeros (s : ℂ) : ℂ :=
  ∏ ρ : ZeroOfRiemannZeta, ρ ≤ T,
    (1 - s / ρ) ^ (mult ρ)
  where T is a suitable cutoff
```

---

## PROOF STRATEGY (High-Level Sketch)

### Step 1: Zeta Derivative Integral Representation
Start with the classical integral representation (Mellin transform):
$$\zeta(s) = \frac{1}{2\pi i} \int_{c-i\infty}^{c+i\infty} \frac{\zeta'(s+w)}{\zeta(s+w)} \cdot \frac{1}{w} dw$$

**Approach:**
- Shift contour to avoid poles at zeros
- Use residue theorem to pick up contributions from zeros
- Bound the contour integrals

**Formalization anchor:** `mellin_integral_zeta_derivative`

### Step 2: Convergence of the Product
Show that the infinite product over zeros converges:
$$\prod_\rho \left(1 - \frac{s}{\rho}\right)$$

**Approach:**
- Use Hadamard's convergence criterion (counts zeros by multiplicity)
- Apply vertical growth bounds from FEFactor (already proved)
- Conclude: product converges for Re(s) > 1

**Key fact:** Vertical growth of ζ controls the zero-counting function N(T).

**Formalization anchor:** `zero_product_convergence`

### Step 3: Establish Zero-Free Region
Prove ζ(s) ≠ 0 for Re(s) = 1 (and beyond).

**Approach:**
- Use the product formula: if ζ(s) = 0, product = 0
- But product > 0 in half-plane Re(s) > 1
- Analytic continuation → zero-free on boundary

**Formalization anchor:** `riemann_zeta_nonzero_critical_line`

### Step 4: Quantitative Bounds
From the factorization, extract decay rate:
$$\left|\frac{\zeta'(s)}{\zeta(s)}\right| \leq C \cdot (1 + |t|)^\alpha$$

**Approach:**
- Logarithmic derivative of product = sum of residues at zeros
- Bound each term via distance to nearest zero
- Aggregate over all zeros

**Formalization anchor:** `zeta_log_derivative_bound`

### Step 5: Complete H14 Linear Decay
Combine with contour shifting (Perron formula setup) to prove:
$$\sum_{n \leq x} \frac{\mu(n)}{n} \leq C \cdot x^{1/2+\epsilon}$$

**Approach:**
- Use Perron's formula (integration by parts around ζ zeros)
- Error terms controlled by zero-free region
- Apply Borel-Jensen bounds

**Formalization anchor:** `mobius_linear_decay_from_borel_jensen`

---

## DEPENDENCIES & LEMMAS

### Existing (Import from Mathlib/H14FEFactor)
- `riemann_zeta` — Riemann zeta function
- `zetaDerivative` — ζ'(s)
- `Complex.Gamma` — Gamma function (for functional equation)
- `Mathlib.Analysis.SpecialFunctions.Complex.Log` — Complex logarithm
- From H14 FEFactor: vertical growth bounds, FE factor interpolation

### To Prove (Proof Search Targets)

```lean
-- Mellin integral for zeta derivative
private lemma mellin_integral_zeta_derivative (s : ℂ) (hs : 1 < s.re) (c : ℝ) (hc : 1 < c) :
    riemann_zeta s = 
      (1 / (2 * π * I)) * 
      ∫ t in Set.Ioi 0,
        (zetaLogDerivative (c + I * t)) / (s - c - I * t) dt
```

```lean
-- Zero-counting function N(T) grows slower than T log T
private lemma zero_counting_function_bound (T : ℝ) (hT : 0 < T) :
    N T ≤ C * T * Real.log T
  where N T = #{ρ : ℂ | ζ(ρ) = 0 ∧ 0 < ρ.im ∧ ρ.im ≤ T}
```

```lean
-- Hadamard convergence: zeros with finite multiplicity
private lemma hadamard_convergence_zeta (s : ℂ) (hs : 1 < s.re) :
    Summable (fun ρ : ZeroOfRiemannZeta => 
      ‖Complex.log (1 - s / ρ.val)‖)
```

```lean
-- Zero-free region on Re(s) = 1
private lemma riemann_zeta_nonzero_critical_line (t : ℝ) :
    riemann_zeta (1 + I * t) ≠ 0
```

```lean
-- Zeta log-derivative bound (integrand control)
private lemma zeta_log_derivative_bound (s : ℂ) (hs : 1 < s.re) (t : ℝ) :
    ‖zetaLogDerivative s / (I * t)‖ ≤ 
      C * (1 + |t|)^α
```

```lean
-- Residue at zero: contribution from contour integral
private lemma residue_at_zero_zeta (ρ : ZeroOfRiemannZeta) (s : ℂ) :
    Residue (fun w => zetaLogDerivative (s + w) / w) ρ =
      Complex.log (1 - s / ρ.val)
```

```lean
-- Bridge to Perron formula (H14 linear decay)
private lemma mobius_linear_decay_from_borel_jensen :
    ∀ x : ℝ, x > 0 →
    ‖∑ n in Finset.Icc 1 x.floor, 
      (mobius_function n : ℂ) / n * 
      (1 - n / x)‖ ≤ C * x ^ (1/2 + ε)
```

---

## SEARCH CONSTRAINTS & SUCCESS CRITERIA

### ✅ SUCCESS: Proof is Complete When

1. **All six theorems above are proved** (no `sorry`)
2. **No new axioms** beyond:
   - `Classical.choice`
   - `propext`
   - `Quot.sound`
3. **Build passes:** `lake build NBMellinTools.H14BorelJensen` succeeds
4. **Verification passes:** `./scripts/verify.sh` reports zero new axioms
5. **Zero-free region is established:** Proof of `riemann_zeta_nonzero_critical_line` is complete and unconditional

### ❌ FAILURE: Reject Proofs That
- Assume RH circularly (e.g., cite BCF or other papers that assume RH)
- Introduce new axioms (other than the 3 listed)
- Use `sorry` in any critical lemma
- Weaken the zero-free region (e.g., only prove it for finitely many t)
- Rely on unproven claims about zero locations

### 🚦 EVIDENCE-BASED PRUNING
- If zero-product convergence fails: try Hadamard factorization formula instead
- If Mellin integral diverges: shift contour further right, accept larger constant
- If Perron bridge fails: focus on integral representation alone (Borel-Jensen factorization is self-contained)

---

## REFERENCE: Classical Source

**Borel & Jensen (1898–1903):** Original factorization theorem  
**Modern treatment:** Montgomery & Vaughan, *Multiplicative Number Theory I*, Chapter 5 (Mellin transforms) + Chapter 13 (zero-free regions)

**Key papers in corpus:**
- 1510.05087.pdf — Functional equations and zeta (Montgomery-style)
- 1501.02975.pdf — Mellin transform techniques
- 2105.00004.pdf — Modern RH survey (section on Borel-Jensen)

---

## TIMELINE & EFFORT

**Formalization:** 3–4 days (defining zeta derivative, zero structures, product formula)  
**Proof search (Aristotle):** 3–4 days (exploring contour integration, residue calculus)  
**Verification + extraction:** 1 day  
**Total:** ~1 week

**Can run in parallel with H14 Perron** (both are independent H14 pieces).

---

## INTEGRATION NOTES

### For Aristotle (or Equivalent System)
1. Provide the lemma list + Mathlib context
2. Emphasize: **zero-free region is non-negotiable** (this is the heart of H14)
3. Multiple proofs acceptable if they're unconditional
4. Return: proof + axiom check

### For Fallback (Manual Codex)
1. Use this spec as skeleton
2. Tackle one lemma at a time
3. Start with `zero_counting_function_bound` (most classical, easiest)
4. Then `hadamard_convergence_zeta` (machinery exists)
5. Finally `riemann_zeta_nonzero_critical_line` (hardest, but most important)

---

**This specification is ready for submission to automated proof search or manual formalization.**

It is precise, scoped, and mathematically self-contained. The zero-free region on the critical line is the payoff; everything else supports that goal.

