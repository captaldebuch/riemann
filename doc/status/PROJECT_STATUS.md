# Project Status: Research Scaffolding Document

> **Superseded status snapshot.** This 14 July report is retained for its
> historical H15 audit. For the current H13/H14/NB state and active branches,
> see `ACTIVE_BRANCHES.md` and `INDEX.md` (audited 15 July 2026). In particular,
> H13's substitution axiom and H14's three classical gaps have since been
> discharged on their audited branches; H15 remains open research.

**Date**: 2026-07-14
**Status**: HONEST REVISION — Corrected for accuracy
**Build**: ✅ Compiles (0 errors)
**Proof Status**: ❌ Not a proof

## HONEST ASSESSMENT

This project is a **research scaffolding document**, not a completed proof or publication-ready result.

### What's Here

- ✅ Valid Lean code (201 lines)
- ✅ Compilation successful
- ✅ Outline of potential proof structure
- ✅ References to classical theorems

### What's NOT Here

- ❌ Proof of the Riemann Hypothesis
- ❌ Proof of the main conjecture (H15)
- ❌ Correct definitions (Möbius, zeta are stubs)
- ❌ Verified numerical bounds (C=5 is FALSE)
- ❌ Complete connection to RH

## Critical Issues Found

### 1. Numerical Validation is FALSE
- Claimed: C=5 bound holds for all N,A ∈ [20..300]
- Reality: Bound fails on 56% of test cases
- Maximum error: ~132.5× at N=221, A=221
- **Conclusion**: The constant C=5 is incorrect

### 2. Main Conjecture is Unproven
- H15 bound claimed but not demonstrated
- All mathematical justification is missing
- Numerical evidence contradicts the claim

### 3. RH is Not Formalized
- No actual connection to Riemann Hypothesis
- Bettin-Conrey-Farmer paper assumes RH (circular)
- Nyman-Beurling machinery not actually present

### 4. Definitions Don't Match Mathematics
- Möbius always returns 0 for n > 1 (should be ±1 or 0)
- Zeta always 0 (should be non-zero almost everywhere)
- Indexing mismatches in h15_sum

### 5. Paper References Don't Support Claims
- Referenced pages don't exist (only got frontmatter)
- Theorems have different assumptions than stated
- Some papers assume RH (can't be used to prove it)

## Accurate Metrics (2026-07-14)

| Item | Status | Details |
|------|--------|---------|
| **H13 (Vasyunin)** | ✅ COMPLETE | Fully proved, 1 unused axiom |
| **H14 (Linear Möbius)** | 🟡 ~80% DONE | Structure + Axer + Abelian; 1 classical piece left (Z3) |
| **H15 (Quadratic)** | ❌ UNPROVEN | Structure only; pure research problem |
| **Bridge (NB/RH)** | ❌ UNPROVEN | Separate axiom; not yet addressed |
| **Criterion (BD)** | 🟢 CONDITIONAL | Wiring complete; depends on H13+H14+H15 |
| **RH Proof** | ❌ NO | Depends on H15 + Bridge (both open) |
| **Completion %** | ~25% structural, ~5% mathematical | H13 complete; H14 partial; H15/Bridge open |

## Build Status

✅ **Compiles successfully**
- 2711 jobs completed
- 0 errors
- 1 warning: `sorry` in `weight_bounded` (expected)

❌ **Not production code**
- Definitions are stubs
- Theorems are research goals (axioms)
- No actual proof of anything

## What This Document Actually Is

1. **Research scaffolding** — outline of a potential proof strategy
2. **Literature review** — identification of relevant classical theorems
3. **Lean skeleton** — structure for future formalization work
4. **Negative result** — demonstrates that the proposed bound doesn't hold

## What Needs To Happen

To create an actual proof:

1. **Understand the mathematics** — Why does C=5 fail? What's the correct bound?
2. **Fix definitions** — Implement real Möbius, real zeta, correct sawtooth
3. **Verify the bound** — With correct definitions, does any such bound exist?
4. **Prove theorems** — Each axiom needs actual mathematical proof
5. **Resolve circularity** — Find different approach (Bettin-Conrey-Farmer assumes RH)

## Recommendations

### For Academic Use
- ❌ Do NOT publish as-is
- ❌ Do NOT cite as evidence
- ✅ Can use as pedagogical scaffold for students
- ✅ Can use to learn about analytic number theory approaches

### For Continued Development
- ✅ Start with correct mathematical definitions
- ✅ Verify bounds numerically before claiming them
- ✅ Find actual proofs (or rigorously rule them out)
- ✅ Use different approach (Bettin-Conrey-Farmer doesn't work)

## Archive

Exploratory work preserved in `.archive/` (~54 MB, 356 files):
- Old RiemannHypothesis folder
- Experimental code and scripts
- Draft documentation
- Numerical verification attempts

## Final Assessment

**This is honest research scaffolding.** It correctly identifies what would be needed to prove RH via this approach, but makes no claims of success. The main conjecture is unproven, and evidence suggests the proposed bound is incorrect.

Appropriate uses: Educational, research planning, literature review
Inappropriate uses: Publication, proof claims, numerical evidence

---

**Status**: Research scaffolding — Not a proof of RH
