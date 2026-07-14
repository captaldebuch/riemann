# Phase 10D′ checkpoint

Date: 2026-06-30

## Build

`lake build` completed successfully: 8512 jobs.

## Structural theorem audit

Lean reports:

```text
rhoBD_memLp_two:
  [propext, Classical.choice, Quot.sound]

baezDuarteL2Error_gram_expansion:
  [propext, Classical.choice, Quot.sound]
```

Thus neither theorem depends on a project axiom or `sorryAx`.

## Generated distance-bound audit

The N=10, N=20, and N=50 bounds still report `sorryAx` and project-level
certificate assumptions. Their dependency families are:

- `lin_certified` for the corresponding generated module;
- three G11 assumptions: inverse substitution, reconstruction from the unit
  series, and equality with the original integral;
- `vasyuninBEntry_correct_axiom` and 45 small-entry evaluation axioms;
- generated Vasyunin interval assumptions:
  - N=10: 10 diagonal log/gamma intervals;
  - N=20: 290 formula, 145 symbolic-interval, and 20 diagonal assumptions;
  - N=50: 2360 formula, 1180 symbolic-interval, and 50 diagonal assumptions;
- one generated `native_decide` trust axiom for the rational energy equality.

`innerProductChiRho_formula` is not yet a dependency of these bounds because
the generated `lin_certified` declarations directly assume the required
interval bounds.

The N=20 and N=50 LDL identity `sorry`s remain in their witness records, but
the displayed distance-bound theorem bodies use the direct quadratic-energy
route rather than those witness records.

## Source inventory

There are 32 source `sorry` terms in the project. On the Nyman-Beurling path,
the relevant ones are:

- 2 in `G11IntegralEvaluation.lean` (measurability/integrability inputs to the
  inverse-substitution theorem);
- 2 defining the symbolic Vasyunin cotangent sum and entry;
- 1 LDL identity at N=20;
- 1 LDL identity at N=50.

There are 4154 explicit `axiom` declarations project-wide. Of these, 4078 are
generated Vasyunin interval declarations and 49 are small-entry evaluation or
diagonal interval declarations. This explains the large axiom lists printed
for the finite distance bounds.

Three generated comments still say that the Gram expansion axiom is pending;
the comments are stale, while the declarations and kernel audit are current.
