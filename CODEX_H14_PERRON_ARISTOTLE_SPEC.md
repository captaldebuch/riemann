# H14 Perron: Aristotle-Style Proof Search Specification

**Status:** Ready for formalization + automated proof search  
**Context:** H14 piece #3 of 3 (final piece; after FEFactor ✅ and Borel-Jensen)  
**Mathematical Foundation:** Classical Perron formula + contour shifting  
**Approach:** Formalization spec for RL-guided tactic search + Lean kernel verification

---

## THE PROBLEM: Why Perron Matters for H14

Once we have the zero-free region (from Borel-Jensen), we need to **convert it into a concrete bound on Dirichlet sums**.

The Perron formula relates:
- Sum of arithmetic function: $\sum_{n \leq x} f(n)$
- Integral along critical line: $\int_{c-iT}^{c+iT} F(s) x^s ds$

**Perron's key idea:** By shifting the contour, we can use the zero-free region to bound the tail beyond the critical strip. This gives:
$$\left|\sum_{n \leq x} \frac{\mu(n)}{n}\right| \leq C \cdot x^{1/2 + \epsilon}$$

---

## FORMALIZATION SPEC (Machine-Readable)

### Primary Theorem (Perron Formula with Contour Shift)

```lean
theorem perron_formula_mobius_bound (x : ℝ) (hx : x > 1) (T : ℝ) (hT : T > 0) :
    ‖∑ n in Finset.Icc 1 x.floor, 
      (mobius_function n : ℂ)‖ ≤
    (1 / (2 * π)) * 
    ∫ t in Set.Icc (-T) T,
      ‖(1 / (riemann_zeta (1/2 + I*t))) * x^(1/2 + I*t)‖ dt +
    C * x^(1/2) * (log T + log x)
```

### Subsidiary Theorems

```lean
-- Main term (on critical line)
theorem perron_main_integral_bound (T : ℝ) (hT : T > 0) :
    ∫ t in Set.Icc (-T) T,
      ‖(1 / riemann_zeta (1/2 + I*t))‖ dt ≤
      C * T * Real.log T

-- Horizontal shift lemma (shift contour)
theorem horizontal_contour_shift (a b c : ℝ) (ha : 0 < a) (hb : a < b) (hc : 1/2 < c) :
    ‖∫ t in Set.Icc (-T) T,
      f (c + I*t) dt -
      ∫ t in Set.Icc (-T) T,
      f (1/2 + I*t) dt‖ ≤
      (error_from_horizontal_shift c)

-- Vertical tail bound (outside [-T, T])
theorem vertical_tail_bound (t : ℝ) (ht : |t| > T) :
    ‖(1 / riemann_zeta (1/2 + I*t)) * x^(1/2 + I*t)‖ ≤
      C * x^(1/2) * (1 + |t|)^(-2)

-- Rectangle residues (corners contribute negligibly)
theorem rectangle_corner_contributions (x : ℝ) (T : ℝ) :
    ‖∑ corners of rectangle,
      Residue f corner * x^corner‖ ≤
      C * x^(1/2) * (1 + T)^(-1)
```

### Key Definitions (To Establish)

```lean
-- Möbius function (already in Mathlib, but needed for context)
noncomputable def mobius_function (n : ℕ) : ℤ :=
  if n = 1 then 1
  else if (squarefree n) then (-1)^(Nat.factors n).length
  else 0

-- Dirichlet generating function for Möbius
noncomputable def mobius_dirichlet_series (s : ℂ) : ℂ :=
  ∑' n : ℕ, (mobius_function n : ℂ) / (n : ℂ) ^ s

-- This equals 1/ζ(s) for Re(s) > 1
theorem mobius_dirichlet_inverse_zeta (s : ℂ) (hs : 1 < s.re) :
    mobius_dirichlet_series s = 1 / riemann_zeta s

-- Rectangular contour integral (for Perron)
noncomputable def perron_rectangle_integral (a b : ℝ) (T : ℝ) (f : ℂ → ℂ) (x : ℝ) :
    ℂ :=
  (1 / (2 * π * I)) * (
    (∫ t in Set.Icc (-T) T, f (a + I*t) * x^(a + I*t) dt) -  -- right vertical
    (∫ t in Set.Icc (-T) T, f (b + I*t) * x^(b + I*t) dt)    -- left vertical
    + [horizontal segments, calculated separately]
  )

-- Effective Perron formula (truncated, with error term)
theorem effective_perron_formula (x : ℝ) (hx : 1 < x) (T : ℝ) (hT : T > 0) :
    (∑ n in Finset.Icc 1 x.floor, mobius_function n) =
    perron_rectangle_integral (1/2) (2) T (fun s => 1/riemann_zeta s) x +
    O(x^(1/2) * (log T + log x))
```

---

## PROOF STRATEGY (High-Level Sketch)

### Step 1: Translate Sum to Integral (Perron Inversion)
Convert:
$$\sum_{n \leq x} \mu(n) = \frac{1}{2\pi i} \int_{c-i\infty}^{c+i\infty} \frac{x^s}{s} \cdot \frac{1}{\zeta(s)} ds$$

**Approach:**
- Start from Möbius = inverse of ζ (Dirichlet inversion)
- Apply Mellin inversion formula
- Truncate to finite interval [-T, T]

**Formalization anchor:** `perron_inversion_mobius`

### Step 2: Shift Contour to Critical Line (1/2 instead of 1)
Move integration contour from Re(s) = 1 to Re(s) = 1/2.

**Approach:**
- Residue theorem: pick up poles/zeros between the contours
- Zero-free region (Borel-Jensen): ζ(s) ≠ 0 for Re(s) = 1
- Main residue at s = 1 contributes $x$ (pole of 1/ζ if RH fails; but we have zero-free region)
- No simple pole if zero-free

**Formalization anchor:** `contour_shift_zero_free_region`

### Step 3: Bound the Shifted Integral (Critical Line)
On Re(s) = 1/2:
$$\left|\int_{-T}^T \frac{x^{1/2 + it}}{\zeta(1/2 + it)} dt\right| \leq C \cdot x^{1/2} \cdot T \cdot \log T$$

**Approach:**
- Use |ζ^(-1)(1/2 + it)| ≤ C · (1 + |t|)^α (from Borel-Jensen bounds)
- |x^(1/2 + it)| = x^(1/2) (magnitude independent of t)
- Integrate |x^(1/2)| · (1 + |t|)^α dt over [-T, T]

**Formalization anchor:** `critical_line_integral_bound`

### Step 4: Bound Vertical Tails (Outside [-T, T])
For |t| > T, the integrand decays rapidly.

**Approach:**
- Vertical growth of 1/ζ: |(1/ζ)(σ + it)| ≤ C · (1 + |t|)^β for σ ≥ 1/2
- Choose β small enough so ∫_T^∞ (1 + t)^(-2) dt converges
- Bound tail contribution: O(x^(1/2) / T)

**Formalization anchor:** `vertical_tail_decay`

### Step 5: Optimize over T
Choose T = log x to balance integral and tail terms.

**Approach:**
- Main integral: C · x^(1/2) · (log x)^2
- Tail: O(x^(1/2) / log x)
- Optimum: T = log x, error = O(x^(1/2) · log x)

**Formalization anchor:** `perron_optimize_cutoff`

### Step 6: Complete H14 Decay
$$\left|\sum_{n \leq x} \frac{\mu(n)}{n}\right| \leq C \cdot x^{1/2 + \epsilon}$$

**Approach:**
- Möbius sum ≤ critical line integral + tails
- Apply Borel-Jensen bounds on critical line
- Result follows from step 5

**Formalization anchor:** `mobius_linear_decay_complete`

---

## DEPENDENCIES & LEMMAS

### Existing (Import from Mathlib/Earlier H14 Pieces)
- `mobius_function` (Mathlib)
- `riemann_zeta` (Mathlib)
- `zetaDerivative` (Mathlib)
- From Borel-Jensen: zero-free region, ζ log-derivative bounds
- From FEFactor: vertical growth interpolation

### To Prove (Proof Search Targets)

```lean
-- Möbius is inverse of zeta (Dirichlet inversion)
private lemma mobius_inverse_zeta (s : ℂ) (hs : 1 < s.re) :
    (∑' n : ℕ, (mobius_function n : ℂ) / (n : ℂ) ^ s) = 
    1 / riemann_zeta s
```

```lean
-- Perron inversion: sum to integral conversion
private lemma perron_inversion_formula (x : ℝ) (hx : 1 < x) (c : ℝ) (hc : 1 < c) :
    (∑ n in Finset.Icc 1 x.floor, mobius_function n) =
    (1 / (2 * π * I)) * 
    ∫ t in Set.Ioi (-∞),
      (1 / riemann_zeta (c + I*t)) * (x^(c + I*t) / (c + I*t)) dt
```

```lean
-- Contour shift: move from Re(s)=c to Re(s)=1/2 using zero-free region
private lemma contour_shift_via_zero_free (x : ℝ) (T : ℝ) (hT : T > 0) :
    ‖∫ t in Set.Icc (-T) T,
      (1 / riemann_zeta (1 + I*t)) * x^(1 + I*t) dt -
      ∫ t in Set.Icc (-T) T,
      (1 / riemann_zeta (1/2 + I*t)) * x^(1/2 + I*t) dt‖ ≤
      C * x^(1/2) * (log T + log x)
```

```lean
-- Critical line bound (using Borel-Jensen)
private lemma critical_line_integral_bound (x : ℝ) (hx : x > 1) (T : ℝ) (hT : T > 0) :
    ‖∫ t in Set.Icc (-T) T,
      (1 / riemann_zeta (1/2 + I*t)) * x^(1/2 + I*t) dt‖ ≤
      C * x^(1/2) * T * Real.log T
```

```lean
-- Vertical tail decay: |t| > T contributes negligibly
private lemma vertical_tail_decay (x : ℝ) (T : ℝ) (hT : T > 0) :
    ‖∫ t in (Set.Ioi T ∪ Set.Iio (-T)),
      (1 / riemann_zeta (1/2 + I*t)) * x^(1/2 + I*t) dt‖ ≤
      (C * x^(1/2) / T)
```

```lean
-- Optimize cutoff T = log x
private lemma perron_optimize_cutoff (x : ℝ) (hx : x > 1) :
    let T := Real.log x
    (critical_line_integral_bound x hx T (by norm_num)) +
    (vertical_tail_decay x T (by norm_num)) ≤
    C * x^(1/2) * Real.log x
```

```lean
-- Final H14 result: Möbius linear decay
theorem mobius_linear_decay_perron (x : ℝ) (hx : x > 1) (ε : ℝ) (hε : 0 < ε) :
    ‖∑ n in Finset.Icc 1 x.floor,
      (mobius_function n : ℂ) / n‖ ≤
      C(ε) * x ^ (1/2 + ε)
```

---

## SEARCH CONSTRAINTS & SUCCESS CRITERIA

### ✅ SUCCESS: Proof is Complete When

1. **All six theorems above are proved** (no `sorry`)
2. **No new axioms** beyond:
   - `Classical.choice`
   - `propext`
   - `Quot.sound`
3. **Build passes:** `lake build NBMellinTools.H14Perron` succeeds
4. **Verification passes:** `./scripts/verify.sh` confirms zero new axioms
5. **H14 is now complete:** `mobius_linear_decay_perron` gives the final linear decay bound

### ❌ FAILURE: Reject Proofs That
- Assume RH (circular logic)
- Weaken the zero-free region assumption (must use Borel-Jensen result)
- Introduce new axioms
- Use `sorry` in critical lemmas
- Fail to optimize the cutoff T (sloppy error bounds allowed, but must be polynomial)

### 🚦 EVIDENCE-BASED PRUNING
- If contour shift fails: may need to expand "zero-free region" further right
- If critical line integral diverges: check ζ log-derivative bounds (may need refinement from Borel-Jensen)
- If tail doesn't decay: adjust the exponent α in vertical growth (currently unspecified)

---

## REFERENCE: Classical Source

**Perron (1909):** Original inversion formula  
**Modern treatment:** Montgomery & Vaughan, *Multiplicative Number Theory I*, Chapter 13 (Contour shifting and zero-free regions)

**Key papers in corpus:**
- 1510.05087.pdf — Functional equations and zeta
- 1501.02975.pdf — Mellin transform techniques
- 2105.00004.pdf — Modern RH survey (Perron section)

---

## TIMELINE & EFFORT

**Formalization:** 3–4 days (setting up Perron integral, contour machinery)  
**Proof search (Aristotle):** 3–4 days (contour shifting, integral bounds)  
**Verification + extraction:** 1 day  
**Total:** ~1 week

**Can run in parallel with H14 Borel-Jensen** (they're independent; both feed into final H14 result).

---

## INTEGRATION NOTES

### For Aristotle (or Equivalent System)
1. **Critical dependency:** Must have Borel-Jensen complete first (zero-free region)
2. Provide the lemma list + context from Borel-Jensen
3. Emphasize: **contour shift is the heart** (this is where zero-free region gets used)
4. Multiple approaches acceptable (can use residue calculus or mechanical integration bounds)

### For Fallback (Manual Codex)
1. Use this spec as skeleton
2. **Start with easiest:** `mobius_inverse_zeta` (pure Dirichlet analysis)
3. **Then:** `perron_inversion_formula` (standard machinery)
4. **Then:** `contour_shift_via_zero_free` (uses Borel-Jensen)
5. **Finally:** Integral bounds and optimization

---

## H14 COMPLETION CHECKPOINT

Once this piece is done:
- ✅ FEFactor (vertical interpolation)
- ✅ Borel-Jensen (zero-free region)
- ✅ Perron (contour shifting)
- **→ H14 COMPLETE**

Then: Move to H15 Phase 1 diagnostics or Phase NB formalization.

---

**This specification is ready for submission to automated proof search or manual formalization.**

It builds directly on Borel-Jensen, integrates with classical Perron machinery, and completes the H14 linear decay bound.

