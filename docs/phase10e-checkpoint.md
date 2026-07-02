# Phase 10E checkpoint

Date: 2026-06-30

## Build

`lake build` completed successfully: 8513 jobs.

## Result

`innerProductChiRho_formula` is now a theorem:

```text
innerProductChiRho k =
  (log (k + 1) + 1 - Real.eulerMascheroniConstant) / (k + 1)
```

The proof uses the actual `rhoBD` indexing convention, so the analytic scale
is `K = k + 1`.

## Analytic decomposition

`ChiRhoIntegralEvaluation.lean` proves the formula without project axioms:

1. decompose `(0, 1]` into the disjoint shells
   `(1 / (n + 2), 1 / (n + 1)]`;
2. prove `{1/x} = 1/x - (n + 1)` on each shell;
3. evaluate each shell integral;
4. identify the resulting infinite sum with the integral over `(0, 1]`;
5. telescope finite partial sums and use
   `Real.tendsto_harmonic_sub_log`;
6. transport the `K = 1` formula through positive scaling and add the top
   interval contribution `log K / K`.

No generic shell-decomposition or measure-substitution axiom remains.

## Kernel audit

Lean reports:

```text
chiRhoIntegral_formula:
  [propext, Classical.choice, Quot.sound]

innerProductChiRho_formula:
  [propext, Classical.choice, Quot.sound]

baezDuarteL2Error_gram_expansion:
  [propext, Classical.choice, Quot.sound]
```

Thus all three depend only on standard Lean axioms and not on a project axiom
or `sorryAx`.

## Remaining finite-certificate debt

The N=10, N=20, and N=50 distance bounds no longer list
`innerProductChiRho_formula` as an axiom. Their remaining trust surface still
includes `lin_certified`, generated Vasyunin interval/evaluation assumptions,
`sorryAx`, and generated native-decision witnesses.

The next target is Phase 10F: route `lin_certified` through the proved analytic
formula and generated rational/Arb interval certificates.
