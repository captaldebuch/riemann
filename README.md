# Riemann Hypothesis Formalization — Research Scaffolding

**Status**: Research scaffolding document  
**Build**: ✅ Compiles (0 errors)  
**Mathematical Status**: Outlines potential proof structure; main conjecture unproven  
**Date**: 2026-07-14

## IMPORTANT DISCLAIMER

This is **NOT a proof of the Riemann Hypothesis**. It is a scaffolding document outlining what such a proof would require. The main conjecture (H15) is unproven, and numerical validation shows the proposed constant is incorrect.

## What This Is

A research document that:
- Identifies key classical theorems from analytic number theory
- Sketches how these theorems could connect to RH
- Formalizes the structure in Lean (with definitions as stubs)
- Provides a foundation for future formalization work

## What This Is NOT

- ❌ A proof of RH
- ❌ A verification of any claimed bound
- ❌ Publication-ready mathematics
- ❌ Evidence that the main conjecture holds

## Quick Start

```bash
cd /Users/xavierfresquet/Documents/Musicologie/CAPTAL-LAB/4-MISC/math/riemann
lake build  # Compiles successfully
```

## Key Files

**Code**: 
- `mathlib/NBMellinTools/H15_RouteA.lean` (201 lines)
  - 1 partial theorem (with `sorry`)
  - 10 axioms representing research goals
  - All definitions are stubs

**Documentation**:
- `final_theorem/TECHNICAL_REPORT.md` — Full analysis of what's here and what's missing
- `final_theorem/H15_EXACT_THEOREM_SPECIFICATION.tex` — Mathematical statement (with errors noted)
- Papers in `final_theorem/` — Classical sources (incomplete; missing key chapters)

## The Proposed Proof Chain

```
H13: Vasyunin cotangent sums
     (Classical, unformalized here)
  ↓
H15: Möbius-sawtooth bound
     (Unproven conjecture, numerical evidence: FAILS)
  ↓
Nyman-Beurling criterion
     (Classical, but Bettin-Conrey-Farmer paper ASSUMES RH)
  ↓
RH: Riemann Hypothesis
     (NOT formalized)
```

## Critical Issues

**Numerical**: The constant C=5 fails on **56% of test cases** across N,A ∈ [20,300]
- Maximum error: ~132.5× the claimed bound
- Actual bounds for this sum are unknown

**Mathematical**: Key references don't support claimed theorems
- Bettin-Conrey-Farmer paper assumes RH; cannot be used to derive it
- Other papers have different assumptions than stated

**Lean**: Definitions are stubs (Möbius always 0 for n>1, zeta always 0)

## For Future Researchers

If you want to continue this work:

1. **Verify the H15 bound** with correct mathematical definitions
2. **Find the actual constant** C (if such a bound exists)
3. **Prove each axiomatized theorem** (or find rigorous justification)
4. **Resolve the RH circularity** (Bettin-Conrey-Farmer doesn't work)

See `final_theorem/TECHNICAL_REPORT.md` for detailed analysis.

## Build Status

✅ Compiles: `lake build` → 2711 jobs, 0 errors, 1 expected warning (in `weight_bounded`)

## Repository Structure

```
.
├── README.md                           (This file)
├── PROJECT_STATUS.md                   (Completion metrics)
├── lakefile.toml                       (Build config)
├── final_theorem/
│   ├── TECHNICAL_REPORT.md            (Full analysis)
│   ├── H15_EXACT_THEOREM_SPECIFICATION.tex
│   └── Papers (Bettin-Conrey, Auli-Bayad-Beck, Montgomery-Vaughan)
├── mathlib/NBMellinTools/
│   └── H15_RouteA.lean                (201 lines, main scaffolding)
└── .archive/                           (Exploratory work, ~54MB)
```

## License

Apache 2.0 (see LICENSE if present)

---

**This is research scaffolding. Not a proof. Not publication-ready.**
