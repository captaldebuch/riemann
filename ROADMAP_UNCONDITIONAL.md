# Research Program: Unconditional Integrated Cancellation for H15

**Status:** Shifting from BCF Lemma 3 (circular) to residue-free contour formulation.

**Date:** July 18, 2026

---

## Executive Summary

The program refocuses from trying to avoid BCF Lemma 3's assumptions to **discovering the unconditional cancellation mechanism entirely independently**.

**Core insight:** Rather than estimating Möbius-weighted zero residues individually (which requires simplicity and inverse-derivative bounds), estimate the **integrated quadratic interaction globally** using paired contours and spectral decomposition.

**Minimal theorem needed:**
$$\mathcal{E}_N \to 0$$

where

$$\mathcal{E}_N = \frac{1}{2\pi} \int_{-\infty}^{\infty} \left| 1 - \zeta\left(\frac{1}{2} + it\right) V_N\left(\frac{1}{2} + it\right) \right|^2 \frac{dt}{\frac{1}{4} + t^2}$$

This alone, by the Nyman–Beurling–Báez–Duarte criterion, proves RH unconditionally. No need initially for the conjecturally optimal $\mathcal{E}_N \sim \frac{2+\gamma-\log 4\pi}{\log N}$.

---

## The Mathematical Obstruction

BCF's unconditional identity is:

$$V_N(s) = \frac{1}{\zeta(s)} \left( 1 - \frac{1}{\log N} \frac{\zeta'}{\zeta}(s) \right) + \frac{1}{\log N} \mathcal{Z}_N(s) + \frac{1}{\log N} F_s(1/N)$$

The problem is **not the identity**. The problem is estimating the square of the bracket without assuming RH or zero simplicity.

**Central question:**
$$\boxed{\text{Can the integrated quadratic contribution of } \mathcal{Z}_N \text{ be estimated without estimating individual residues?}}$$

---

## Work Package 1: Residue-Free Master Identity

### Objective

Replace the infinite zero sum by a finite contour expression before taking absolute values or multiplying factors.

For a height T, introduce a zero-deleted rectangle $\Gamma_T$ and define:

$$\mathcal{Z}_{N,T}(s) = \frac{1}{2\pi i} \int_{\Gamma_T} \frac{N^{z-s}}{\zeta(z)(z-s)^2} dz$$

By the residue theorem:

$$\mathcal{Z}_{N,T}(s) = \sum_{\substack{|\text{Im}\,\rho| \leq T}} \text{Res}_{z=\rho} \frac{N^{z-s}}{\zeta(z)(z-s)^2} + \text{explicit boundary terms}$$

**Key advantage:** Allows arbitrary multiplicities, never divides by $\zeta'(\rho)$, fits multi-hole Cauchy–Goursat machinery.

### Crucial Operation

**Do NOT first estimate $\mathcal{Z}_{N,T}(s)$.** Substitute both contour copies directly into the quadratic interaction and integrate in $s$ first:

$$\mathcal{R}_{N,T}^{\mathrm{quad}} = \frac{1}{\log^2 N} \iint_{\Gamma_T \times \Gamma_T} \frac{N^{z+w-1}}{\zeta(z)\zeta(w)} \mathfrak{K}(z,w) \, dz \, dw + \mathcal{B}_{N,T}$$

where $\mathfrak{K}(z,w)$ is obtained from the exact inner integral:

$$\mathfrak{K}(z,w) = \frac{1}{2\pi i} \int_{\Re s = 1/2 - \varepsilon} \frac{\zeta(s)\zeta(1-s)}{s(1-s)(z-s)^2(w-1+s)^2} ds$$

### Lean Deliverable

```lean
theorem quadraticResidual_eq_doubleContourLimit :
    quadraticInteractionResidual N =
      limUnderControlledConvergence
        (fun T => doubleContourResidual N T)
```

### Acceptance Criterion

WP1 succeeds only when the resulting formula contains NONE of:
- $\zeta'(\rho)^{-1}$
- Simple-zero hypotheses
- RH assumption
- Pointwise bounds for $\mathcal{Z}_N(s)$

---

## Work Package 2: Finite Arithmetic Form via Centered Kernel

### Objective

Complement the contour representation with a completely finite Nyman–Beurling Gram representation.

Define the weight:
$$a_N(n) = \mu(n) \left(1 - \frac{\log n}{\log N}\right)$$

The approximation error is a finite Hilbert-space quadratic form. Expanding and subtracting every explicitly controllable component produces a centered kernel:

$$\mathcal{R}_N^{\mathrm{quad}} = \sum_{m,n \leq N} \mu(m)\mu(n) w_N(m) w_N(n) K^\circ(m,n)$$

### GCD–Ratio Reduction

Write $m = gh$, $n = gk$, $(h,k) = 1$. The target form becomes:

$$\boxed{\mathcal{R}_N^{\mathrm{quad}} = \sum_{\substack{h,k \leq N \\ (h,k)=1}} \mu(h)\mu(k) A_N(h,k) \mathcal{V}^\circ(h,k)}$$

where:
$$A_N(h,k) = \sum_{\substack{g \leq N/\max(h,k) \\ (g,hk)=1}} \frac{\mu(g)^2}{g^\alpha} w_N(gh) w_N(gk)$$

**Key insight:** The gcd variable carries $\mu(g)^2$ (positive), while oscillating cancellation concentrates in coprime ratios $(h,k)$.

### Lean Deliverable

```lean
theorem doubleContourResidual_eq_centeredVasyuninForm :
    doubleContourResidualLimit N =
      centeredVasyuninQuadraticForm N
```

---

## Work Package 3: Spectral Diagonalization of Centered Kernel

### Objective

Seek an actual spectral or Mellin diagonalization of the centered Vasyunin/BBLS kernel:

$$\mathcal{V}^\circ(h,k) = \int_{\mathbb{R}} \Phi(t) \left(\frac{h}{k}\right)^{it} dt + \sum_j c_j \frac{\lambda_j(h)\overline{\lambda_j(k)}}{\sqrt{hk}} + \mathcal{E}(h,k)$$

where:
- The integral represents the Eisenstein contribution
- Discrete sum: possible cuspidal or spectral components
- $\mathcal{E}(h,k)$: elementary or rapidly decaying remainder

### Transformed Quadratic Form

Substitution produces expressions resembling:

$$\int_{\mathbb{R}} \Phi_N(t) \left| \sum_{h \leq N} \mu(h) b_N(h) h^{it} \right|^2 dt$$

and

$$\sum_j c_{j,N} \left| \sum_{h \leq N} \mu(h) b_N(h) \lambda_j(h) \right|^2$$

The problem becomes a collection of explicit estimates for:
- Möbius Dirichlet polynomials
- Möbius twists by automorphic coefficients
- Shifted-convolution averages
- Eisenstein continuous-spectrum integrals

**Advantage:** Multiplicity and very small zero derivatives disappear entirely.

### Dyadic Decomposition

Treat four regimes separately:
- **Unbalanced** ($H \ll K$ or $K \ll H$): Vasyunin/Estermann reciprocity → Type I estimates
- **Balanced, far diagonal** ($|h-k| \gg H^\theta$): Spectral large-sieve or oscillatory integrals
- **Balanced, near diagonal** ($h = k+r$, $|r| \leq H^\theta$): Averaged Möbius correlations
- **Small-denominator ratios:** Reciprocity → explicit shorter dual sums

---

## Work Package 4: Paired Double-Contour Route (Fallback)

### Principle

Pair the two factors using $s \leftrightarrow 1-s$ and apply the functional equation **before** taking absolute values.

### Geometry

The double-contour kernel has an oscillating factor:

$$N^{z+w-1} = N^{\Re(z+w)-1} e^{i \log N(\Im z + \Im w)}$$

Separate:
- Resonant surface: $z+w=1$
- Non-resonant region: $|z+w-1| \geq \Delta$
- Zero neighborhoods
- Outer contour tails

### Target Theorem

$$\mathcal{R}_N^{\mathrm{quad}} = \mathcal{R}_N^{\mathrm{res}} + \mathcal{R}_N^{\mathrm{off}} + \mathcal{R}_N^{\mathrm{tail}}$$

with:
- $\mathcal{R}_N^{\mathrm{res}} = O(1/\log N)$ (explicit vanishing contribution)
- $\mathcal{R}_N^{\mathrm{tail}} = o(1)$ (Stirling + contour decay)
- $\mathcal{R}_N^{\mathrm{off}} = o(1)$ (oscillation in $e^{i\log N(u+v)}$)

### Operator Estimate

View off-resonant contribution as:

$$(T_N f)(u) = \int e^{i\log N(u+v)} K_N(u,v) f(v) dv$$

The theorem becomes an operator estimate:
$$\|T_N\|_{L^2 \to L^2} \to 0$$

### Non-Negotiable Rule

**Never apply:**
$$\left| \sum_\rho R_N(\rho,s) \right| \leq \sum_\rho |R_N(\rho,s)|$$

before the $s$-integration. This destroys exactly the cancellation being discovered.

---

## Work Package 5: Weight Optimization

### Principle

Don't treat the BCF triangular weight as sacred. Introduce:

$$V_{N,W}(s) = \sum_{n \leq N} \mu(n) W\left(\frac{\log n}{\log N}\right) n^{-s}$$

where $W$ is supported on $[0,1]$, satisfies $W(0)=1$, and has vanishing boundary derivatives:

$$W^{(j)}(1) = 0, \quad 0 \leq j < J$$

The Mellin/Perron kernel decays like:
$$|\widehat{W}(\sigma+it)| \ll_J (1+|t|)^{-J}$$

### Research Question

$$\exists W \quad \text{such that} \quad \mathcal{E}_{N,W} \to 0?$$

### Potential Weight Families

- Higher-order Cesàro weights
- Compactly supported splines
- Polynomials with prescribed vanishing moments
- Rational-coefficient weights from numerical optimization

A successful weight might trade the conjecturally optimal $1/\log N$ rate for an easier rate like:
$$\mathcal{E}_{N,W} \ll \frac{1}{(\log\log N)^c}$$

which still proves RH.

---

## Work Package 6: Computational Discovery and Falsification

### Objective

Identify **where the cancellation actually occurs** by computing the exact centered quadratic matrix:

$$C_N(h,k) = \mu(h)\mu(k) A_N(h,k) \mathcal{V}^\circ(h,k)$$

### Key Diagnostic Maps

1. **Signed versus absolute mass:**
   $$\left| \sum_{h,k} C_N(h,k) \right| \quad \text{vs} \quad \sum_{h,k} |C_N(h,k)|$$
   This quantifies required cancellation preservation.

2. **Shift profile:**
   $$S_N(r) = \sum_h C_N(h, h+r)$$
   Determines if residual concentrates on fixed small shifts or spreads widely.

3. **Spectral profile:**
   Numerically diagonalize centered kernel. Test if dominant modes resemble:
   - $n^{it}$
   - $d(n) n^{it}$
   - $\lambda_j(n)$ (automorphic coefficients)
   - Continued-fraction modes

4. **Weight optimization:**
   For finite-dimensional family $W_\theta$, minimize:
   $$\mathcal{E}_{N,W_\theta}$$
   simultaneously for several $N$, while penalizing unstable coefficients.

5. **Adversarial controls:**
   Replace $\mu(n)$ with:
   - Random signs
   - $\mu(n)^2$
   - All positive
   - Permuted signs within dyadic blocks

### Decision Criterion

> If kernel concentrates on finitely many shifts, arithmetic route likely blocked by Chowla-type barrier.
> 
> If kernel naturally averages over growing shift range, dispersion and spectral methods remain plausible.

---

## Work Package 7: Terminal Estimate Architecture

### Principle

Don't end with one enormous theorem. Compile the residual into a finite family of terminal estimates:

```lean
inductive CancellationRegion
  | unbalanced
  | balancedOffDiagonal
  | balancedNearDiagonal
  | rationalResonant
  | contourTail
  | spectralContinuous
  | spectralDiscrete

structure TerminalCancellationEstimate where
  region : CancellationRegion
  quantity : ℝ
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  verified : quantity ≤ bound
```

### Proof Compiler

```lean
theorem residual_bound_from_terminal_estimates
    (certs : List TerminalCancellationEstimate)
    (hcover : certsCoverAllDyadicRegions certs) :
    ‖quadraticInteractionResidual N‖
      ≤ certs.map TerminalCancellationEstimate.bound |>.sum
```

### Asymptotic Endpoint

```lean
theorem terminal_bounds_tendsto_zero :
    Tendsto
      (fun N => terminalBoundSum N)
      atTop
      (nhds 0)
```

### Existing Oracle Categories

These become proved theorems, not opaque assumptions:
- `typeI`
- `typeII`
- `bilinear`
- `spectralShiftedConvolution`
- `circleMethod`
- `delogarithmization`
- `entropy`

---

## Decision Gates

### Gate 1: Identity Gate

After WP1 and WP2, the same scalar must have both:
- Residue-free double-contour representation
- Finite centered arithmetic representation

**Failure criterion:** Cannot eliminate $1/\zeta'(\rho)$ — program has not escaped BCF Lemma 3.

### Gate 2: Localization Gate

Numerical atlas must determine where ≥90% of signed residual arises:
- Near diagonal
- Off diagonal
- Exceptional rational ratios
- High spectral frequencies
- Contour resonance

This determines which mathematics deserves investment.

### Gate 3: Exponent Ledger

For every dyadic region, record:
$$\text{available bound} \quad \text{vs} \quad \text{required bound} \quad \Rightarrow \quad \text{missing saving}$$

A region missing by a logarithm differs fundamentally from one missing by a fixed power of $N$.

### Gate 4: Chowla Barrier Test

If remaining estimate implies non-averaged fixed-shift bound:
$$\sum_{n \leq X} \mu(n)\mu(n+r)$$

declare arithmetic route blocked unless additional kernel cancellation overlooked.

### Gate 5: Smoothing Test

Before declaring failure, repeat exponent ledger for smoother weights $W$. A small weight change may remove fatal boundary or near-diagonal term.

---

## Priority Ranking

### Priority 1: Finite Centered Kernel + GCD–Ratio Decomposition
Uses strongest part of existing H13 infrastructure. Removes zero multiplicity completely.

### Priority 2: Spectral Diagonalization of Vasyunin/Estermann Kernel
Most plausible place for genuinely new mathematical mechanism.

### Priority 3: Paired Double-Contour Operator Estimate
Main fallback if arithmetic form reduces to fixed-shift Möbius correlations.

### Priority 4: Smoothing-Weight Search
Run in parallel from beginning—can fundamentally change difficulty of main routes.

### Abandon as Principal Route
- Bounding individual $R_N(\rho,s)$
- Assuming simplicity then trying to remove it
- Using zero density to control inverse derivatives
- Proving full BCF asymptotic before proving decay
- Taking absolute values before pairing factors

---

## What Constitutes Genuine Progress?

Even before RH, seven meaningful outcomes:

1. ✅ **Exact multiplicity-aware, residue-free formula** for H15 quadratic interaction (contour form exists)
2. ⏳ **Exact equivalence** between contour and Vasyunin-kernel formulations
3. ⏳ **Spectral expansion** of centered BBLS kernel
4. ⏳ **Vanishing estimates** for all unbalanced and off-diagonal dyadic regions
5. ⏳ **Isolation** of one balanced near-diagonal estimate as sole remaining theorem
6. ⏳ **Discovery** of smoother approximant reducing required estimate
7. ⏳ **Proof** of any bound: $\mathcal{R}_N^{\mathrm{quad}} \leq \eta_N$, $\eta_N \to 0$

**Item 7 closes the unconditional proof.**

**Central scientific bet:** Missing cancellation is visible only after **global pairing, centering, and spectral transformation**—not at level of individual zeta zeros.

---

## Classical Formalization Track (Optional)

While pursuing the research program above, a parallel track can formalize classical Hadamard factorization:

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

## Unconditional Endpoint Structure

The final Lean term **must have this structure:**

```lean
theorem riemannHypothesis_unconditional : RH := by
  exact rh_from_verified_approximation_rate
    quadratic_residual_decays_to_zero
```

**No hypotheses. No theorem arguments. No structures containing unproved analytic properties.**

### Verification Checklist

Scan for forbidden hypotheses:
```
❌ RiemannHypothesis
❌ SimpleZero / AllZerosSimple
❌ InverseZetaDerivativeMomentBound
❌ Lindelof / ZetaDerivativeBound
❌ BCFLemma3 (or any RH-assuming lemma)
❌ Structures with unproved analytic fields
```

---

## Completed Infrastructure (Exists Now)

✅ H13: BBLS classical identities (verified)
✅ H14: DVP quantitative bounds (verified)
✅ Phase NB: Nyman–Beurling equivalence (verified)
✅ H15 Phases 1–7: BCF algebraic reduction
✅ Riemann–von Mangoldt infrastructure
✅ Cauchy–Goursat witness assembly
✅ Rectangle geometry + edge bounds
✅ Multiplicity-aware zero counting
✅ Digamma vertical reductions (b396550)

---

## Next Immediate Steps

1. **Begin WP1:** Formalize residue-free double-contour integral over finite deleted rectangle $\Gamma_T$
2. **Begin WP6 (parallel):** Implement computational diagnostic pipeline
3. **Maintain decision gates:** Use Gate 1 (identity equivalence) as first checkpoint

---

## The Mathematical Reality

There is no "missing classical lemma." There are **seven work packages** solving one fundamental problem:

**Can the integrated quadratic interaction of Möbius weights vanish unconditionally?**

The answer requires:
- Pairing factors before taking absolute values
- Centering the kernel to extract oscillations
- Separating dyadic regions structurally
- Either spectral diagonalization (WP3) or operator estimates (WP4)
- Computational discovery of where cancellation actually occurs (WP6)

This is intellectually honest and represents the **actual RH mathematics**—not a missing lemma, but a research program.

