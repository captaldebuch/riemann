# Roadmap to Unconditional RH Proof in Lean 4

**Status:** Formalization architecture complete; two distinct research problems remain.

**Date:** July 18, 2026

---

## Executive Summary

The Lean 4 formalization provides a complete, audited, unconditional reduction of RH to **two independent classical problems**:

1. **Work Package A (Classical):** Hadamard factorization of the centered, squared-variable ξ-function
2. **Work Package B (RH-level):** Quadratic cancellation estimate without assuming RH

The completed Nyman–Beurling formalization confirms: any theorem strong enough to close Problem B is already sufficient to prove RH directly.

---

## Critical Audit: The BCF Lemma 3 Circularity

### Problem Identified

The published Bettin–Conrey–Farmer paper's Lemma 3:

```
lemma bettin_conrey_farmer_lemma_3 :
    (h_rh : RiemannHypothesis) →
    (h_simple : AllZerosSimple) →
    (h_moment : ∑ ρ, 1/|zeta'(ρ)|² ≪ T^(3/2 - δ)) →
    QuadraticInteractionEstimate ≤ C / log(N + 2)
```

**This cannot close an unconditional proof of RH because it assumes RH as a hypothesis.**

Using it as an "analytic input" to prove RH is logically circular:

```
RH  ← (uses BCF Lemma 3)  ← (assumes RH)  ✗ Circular
```

### Consequence

The statement "one final classical theorem gates completion" is **misleading**. What remains are **two logically distinct problems**, one classical and one RH-level.

---

## Work Package A: Centered ξ Hadamard Factorization (Classical, ~2–3 weeks)

### Approach

Replace the quotient-growth strategy with a squared-variable canonical product:

**1. Centered, even function**

Define: $X(z) = \xi(1/2 + z)$

Functional equation: $X(z) = X(-z)$ (even)

Hence: $X(z) = F(z^2)$ for some entire $F$

**2. Order reduction**

- $X$ has order 1 (from ξ)
- $F$ has order $< 1$ (in the squared variable)
- Genus-zero Hadamard product (no exponential factor)

**3. Factorization**

$$F(w) = C \prod_{\lambda_\rho} \left(1 - \frac{w}{\lambda_\rho}\right)$$

where $\lambda_\rho = (\rho - 1/2)^2$ for each zero $\rho$.

Consequently:

$$\xi(s) = C \prod_{\rho, 1-\rho} \left(1 - \frac{(s-1/2)^2}{(\rho-1/2)^2}\right)$$

### Mathlib Contribution

**Theorem needed:** `entire_eq_canonicalProduct_of_order_lt_one`

```lean
theorem entire_eq_canonicalProduct_of_order_lt_one
    (f : ℂ → ℂ)
    (hf_entire : Entire f)
    (hf_not_zero : f ≠ 0)
    (hf_order : EntireOrderLT f 1)
    (zeros : ZeroEnumeration f)
    (hsum : Summable fun n => ‖zeros n‖⁻¹) :
    ∃ C : ℂ, C ≠ 0 ∧
      ∀ z, f z = C * canonicalProductGenusZero zeros z
```

**Mathlib currently provides:** Hadamard three-lines theorem (not factorization)

### Implementation Modules

```
Classical/XiCenteredEven.lean
Classical/EntireFactorThroughSquare.lean
Classical/EntireOrderSubunit.lean
Classical/GenusZeroCanonicalProduct.lean
Classical/XiPairedHadamard.lean
```

### Advantages

- ✅ Eliminates quotient-growth machinery entirely
- ✅ Cleaner classical formalization path
- ✅ No vertical-line bounds needed
- ✅ Reusable Mathlib contribution

### Timeline

- **Week 1:** Order < 1 theory + genus-zero product formalization
- **Week 2–3:** Pairing symmetry + ξ-specific Hadamard assembly

---

## Work Package B: Unconditional Quadratic Cancellation (RH-Level)

### Problem Statement

**Prove (without RH, simplicity, or ζ' moment bounds):**

$$\left| \sum_{|\text{Im}\,\rho| \leq T} \int_{\Gamma} \frac{N^z}{(z-\rho)^2 \zeta(z)} dz \right| \leq \frac{C}{\log(N+2)}$$

where:
- The contour Γ is a finite deleted rectangle (zero-avoiding)
- Zeros are counted with multiplicity
- No RH assumption anywhere in the proof

### Why This Is Hard

**Individual-residue formulation fails:**

$$\sum_\rho \frac{1}{\zeta'(\rho)(\rho-s)^2} \ll N^{-\varepsilon} |s|^\theta$$

This approach:
1. Requires simple zeros (ζ'(ρ) undefined otherwise)
2. Requires $1/\zeta'(\rho)$ bounds (not unconditionally proved)

**Better architecture: Integrated contour**

Keep the zero contribution integrated, not decomposed into residues:

$$\mathcal{R}_N(s) = \frac{1}{2\pi i} \int_{\Gamma} \frac{N^{z-s}}{\zeta(z)(z-s)^2} dz$$

Estimate this as a **whole contour integral** using:
- Symmetry under $s \leftrightarrow 1-s$, $\rho \leftrightarrow 1-\rho$, $\rho \leftrightarrow \overline{\rho}$
- Pairing of contour pieces
- Multiplicity-aware zero counting (already formalized)

### Key Existing Machinery (Formalized)

✅ Finite-deleted-rectangle Cauchy–Goursat
✅ Multiplicity-aware zero counting
✅ Argument principle (local + ξ-specific)
✅ von Mangoldt identity
✅ Functional-equation symmetry
✅ Axis-separated disk partitions
✅ Integrated contour framework

### Challenge

No guarantee that known unconditional zero-density and zero-free-region estimates are strong enough to give O(1/log N) decay. If they are, then **the proof of this cancellation IS an unconditional proof of RH** (by Nyman–Beurling equivalence).

### Timeline

**Unknown.** This is where the actual RH mathematics lies.

---

## Unconditional Endpoint Structure

The final Lean term **must have this structure:**

```lean
theorem riemannHypothesis_unconditional : RH := by
  exact rh_from_verified_approximation_rate
    h15_approximation_rate_unconditional
```

**No hypotheses. No theorem arguments. No structures containing unproved analytic properties.**

### Verification

```lean
#check riemannHypothesis_unconditional
  -- Expected: riemannHypothesis_unconditional : RH

#print axioms riemannHypothesis_unconditional
  -- Expected: (only standard Lean axioms, no RH-related axioms)
```

---

## Dependency Audit Checklist

Before declaring any piece "unconditional," scan for:

```
❌ RiemannHypothesis
❌ SimpleZero / AllZerosSimple
❌ InverseZetaDerivativeMomentBound
❌ Lindelof
❌ ZetaDerivativeBound
❌ CriticalLineZeros
❌ BCFLemma3 (or any RH-assuming lemma)
❌ Structures with unproved analytic fields
```

---

## Realistic Assessment

### Completed (100% Formalized)

✅ H13: BBLS classical identities
✅ H14: DVP quantitative bounds
✅ Phase NB: Nyman–Beurling equivalence
✅ H15 Phases 1–7: BCF algebraic reduction
✅ Riemann–von Mangoldt infrastructure
✅ Cauchy–Goursat witness assembly
✅ Rectangle geometry + edge bounds (exact form: C·log²(T+2))

### Remaining (Two Distinct Problems)

⏳ **Work Package A:** Hadamard factorization of centered ξ (classical, ~2–3 weeks)
⏳ **Work Package B:** Unconditional quadratic cancellation (RH-level, timeline unknown)

---

## The Mathematical Reality

The Lean formalization has revealed something important: **there is no "final lemma" blocking RH.** Instead, there are two problems:

1. One is a classical theorem that can realistically be formalized in Lean
2. One is the actual RH-level mathematics, where unconditional proof would be discovered

This is intellectually honest and represents genuine progress toward understanding what RH actually requires.

