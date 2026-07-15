# Scaffolding for Riemann Hypothesis Formalization — Honest Technical Report

**Status**: Research scaffolding document, NOT a proof  
**Build**: ✅ Compiles (2711 jobs, 1 expected warning)  
**Mathematical Status**: Identifies key theorems required; conjectures unproven  
**Date**: 2026-07-14

## CRITICAL LIMITATIONS

This file is a **research scaffolding document**. It does NOT:
- Prove the Riemann Hypothesis
- Formalize all required theorems
- Verify numerical bounds (the sawtooth proxy was over-strengthened; true H15 is aggregate-based)
- Connect H15 to RH in a complete proof chain

What it DOES:
- Outline the logical structure of a potential proof
- Identify classical theorems needed from the literature
- Provide stubs and placeholders for future work

## CRITICAL FINDING: H15 FORMULATION ERROR

**A systematic derivation attempt revealed the core issue:**

The original H15 target (uniform pointwise Möbius–sawtooth bound) **cannot hold** using standard analytic techniques. The attempted proof yields bounds of order $N \log^4 N$, not $1/\log^2 N$.

**This does NOT invalidate H15 itself.** Instead, it reveals:

1. **The formulation was too strong.** The uniform pointwise bound is an over-strengthening.
2. **The real H15 is a bilinear aggregate.** The Lean code shows the actual residual is:
   ```
   R(N) := |Σ_{h,k≤N} μ(h)μ(k) · residualKernel(h,k)|
   ```
   where the kernel contains cotangent sums, not Dedekind saws.

3. **The correct target scale is 1/log(N), not 1/log²(N).** The aggregate bound is much weaker.

4. **H15 remains open but correctly formulated.** The centered, bilinear residual with cotangent machinery is the right target, not the pointwise sawtooth proxy.

## The Proposed Proof Structure

```
H13: Vasyunin cotangent sum bounds
     (Classical, from Báez-Duarte — requires further formalization)
  ↓
H15: Reciprocal-phase Möbius-sawtooth bound
     (Unproven conjecture — numerical evidence inconclusive)
  ↓
Nyman-Beurling criterion
     (Classical theorem — but Bettin-Conrey-Farmer paper ASSUMES RH)
  ↓
RH: Riemann Hypothesis
     (NOT formalized here)
```

## What's Actually in the Code

### Definitions (Stubs)
- `moebius`: Simplified placeholder (returns 0 for n > 1)
- `dedekind_sawtooth`: Basic definition, convergence properties unverified
- `riemann_zeta`: Currently identically 0 (placeholder)
- `h15_sum`: Main object; indices may not match mathematical intent exactly

### Theorems (1 partial, 1 sorry)
- `weight_bounded`: Proof incomplete (line 100 has `sorry`)

### Research Goals (10 axioms)
All declared as `axiom`, representing theorems that require proof:
1. `period_function_recursion` — Bettin-Conrey machinery
2. `auli_bayad_beck_reciprocity` — Reciprocity theorem
3. `cotangent_integral_form` — Contour integral representation
4. `mellin_contour_shift` — Contour analysis
5-10. Plus six others representing research goals

### Conjectures (3 unproven axioms)
- `h15_reciprocal_phase_möbius_bound` — Main bound, unverified
  - Numerical check: **FAILS** on 56% of test cases
  - Maximum error: ~132.5× at N=221, A=221
  - Constant C=5 is incorrect

## Known Issues

### Numerical Validation
The constant C=5 was claimed without verification. Recomputing across N,A ∈ [20,300]:
```
Total pairs: 44,960
Failed pairs: 25,486 (56.7%)
Max error: 132.50× at N=221, A=221
```
**Conclusion**: The bound as stated is FALSE.

### Mathematical Issues
1. **Definitions don't match mathematical intent**
   - Möbius always 0 for n > 1 (real Möbius is ±1, 0, or undefined)
   - Zeta always 0 (real zeta is non-zero almost everywhere)
   - Indexing in h15_sum may be off-by-one vs. stated formula

2. **Fourier series errors** (in original TeX)
   - Wrong sign for B₁(x)
   - Non-convergent at integers
   - Not absolutely convergent as claimed

3. **Axiom mismatches**
   - Auli-Bayad-Beck Theorem 1.2 assumes Re(a) > 1, not Re(a) > -1
   - Bettin-Conrey-Farmer paper assumes RH; cannot be used to derive it

### Paper References (Incomplete)
- 1111.0931v2.pdf: Only ~35 pages, titled "Period functions and cotangent sums"
- 1601.06839v3.pdf: Valid, but theorems have different assumptions
- 1211.5191v1.pdf: **Critically**, this paper assumes RH in its main theorem
- Montgomery-Vaughan frontmatter: Only 17 pages of intro, not Chapters 5 and 13

## What Would Be Needed

To complete a real proof:

1. **Fix all definitions**
   - Implement real Möbius function
   - Implement zeta via analytic continuation
   - Verify Fourier series convergence

2. **Prove (or find proofs for) all axioms**
   - Each would require 100-300 lines of Lean
   - Would need deep knowledge of analytic number theory

3. **Find correct bound (if it exists)**
   - The constant C=5 is definitely wrong
   - Whether any such bound exists is an open question

4. **Resolve the RH circularity**
   - Bettin-Conrey-Farmer cannot be used unconditionally
   - Need a different approach or different theorem

## Conclusions

This scaffolding document:
- ✅ Compiles to valid Lean
- ✅ Outlines a potential proof strategy
- ❌ Does NOT prove RH
- ❌ Does NOT verify the main bound
- ❌ Is NOT publication-ready

It is appropriate as a **research document** showing:
1. What classical theorems would be needed
2. Where those theorems appear in the literature
3. Where additional work is required

It is NOT appropriate as:
- A completed proof
- A published result
- Evidence that the bound holds

## Recommendations for Future Work

If continuing this project:
1. Start with **correct definitions** of Möbius and zeta
2. **Verify the H15 bound independently** with correct definitions
3. **Identify the actual constant** C (if the bound holds)
4. **Find or prove** each axiomatized theorem
5. **Use different approach for RH** (Bettin-Conrey-Farmer assumes it)

---

**Status**: Research scaffolding — Foundation for future formalization work

**Not**: Proof of the Riemann Hypothesis
