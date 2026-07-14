# Phase 10F checkpoint

Date: 2026-06-30

## Build

`lake build` completed successfully: 8516 jobs.

Focused builds also passed for `NymanGramN10`, `NymanGramN20`, and
`NymanGramN50`.

## Result

The three opaque `lin_certified` assumptions are gone. The N=10, N=20, and
N=50 distance proofs now obtain every linear-term interval from:

```text
innerProductChiRho_formula
→ generated Arb interval for log(k + 1)
→ generated Arb interval for Euler's constant
→ Lean rational interval arithmetic
→ sign_aware_energy_bound
```

The rational centers and radius `1 / 10^9` are unchanged, so the existing
energy upper bounds and native rational equalities remain unchanged.

## Generated files

- `ChiRhoBoundsN50.lean` contains 49 primitive external Arb log certificates
  for `log 2` through `log 50`, plus 50 Lean-proved χ–ρ intervals.
- `ChiRhoBoundsN20.lean` projects the first 20 certified intervals.
- `ChiRhoBoundsN10.lean` projects the first 10 certified intervals.
- `chi_rho_bounds.json` records exact rational endpoints and a SHA-256 digest.
- `experiments/generate_chi_rho_bounds.py` regenerates and audits all files.

The generator's `--check` mode passes. It verifies the primitive log
enclosures and the final χ–ρ enclosures using python-flint/Arb at 256-bit
precision before checking that the committed generated files are current.

## Reusable finite linear algebra

`NymanBeurlingCertificate.lean` now contains:

- `ChiRhoIntervalCertificate`;
- `lowerLinearBoundQ` and `upperLinearBoundQ`;
- `interval_linear_form_bounds`, the general sign-aware finite linear-form
  enclosure theorem.

Lean reports that `interval_linear_form_bounds` depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Kernel dependency audit

The generated χ–ρ interval theorem uses exactly the relevant primitive
external facts:

- N=10: Euler γ and `log 2` through `log 10`;
- N=20: Euler γ and `log 2` through `log 20`;
- N=50: Euler γ and `log 2` through `log 50`.

No theorem depends on `lin_certified`, and the identifier has zero source
occurrences.

The finite distance bounds still depend on the unchanged quadratic trust
surface: Vasyunin formula/evaluation and interval assumptions, `sorryAx`, and
one generated native-decision witness per size. They now additionally expose
the primitive log/γ external certificate facts instead of an opaque χ–ρ vector
axiom.

There are 32 actual source `sorry` terms project-wide. The only two under
`RiemannHypothesis/Certificates` are the pre-existing truncated LDL identities
for N=20 and N=50.

There are 4199 explicit project axiom declarations. The total is larger than
at 10E because three opaque vector axioms were replaced by 49 separately
auditable primitive log facts; this phase improves provenance and granularity,
not the raw declaration count.
