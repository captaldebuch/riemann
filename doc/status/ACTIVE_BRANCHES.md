# Active branches and integration state

**Audited:** 15 July 2026

| Branch | Commit | Status | Next action |
|---|---:|---|---|
| `main` | `b163a23` | H13 and the active NB2--NB4 package proofs are merged. | Review the one-commit NB5 continuation. |
| `codex/nb-field-1-active-port` | `766acdc` | Merged into `main` through `b163a23`. | Retain as the NB3/NB4 checkpoint. |
| `codex/nb5-functional-equation-closure` | `HEAD` | Mathlib's zeta functional equation replaces the historical symmetry assumption and closes the conditional critical-strip theorem. | Review and merge into current `main`. |
| `codex/h14-corrected-aristotle-specs` | `b499bf2` | H14 reference/audit; qualitative and effective Mertens endpoints are project-axiom-free. | Retain as the H14 publication source. |
| `codex/bridge-field-1-mellin-continuity` | `11cde38` | Already an ancestor of `main`; the archived Field 1 file is byte-identical. | Use as a reference while porting the theorem to the active package. |
| `codex/nb-field-2-zero-detection-current` | `12a14d1` | Retained for NB2–NB5 work. Its Field 2 file is byte-identical to the archived file on `main`, but the branch is 63 main commits behind. | Refresh from current `main` before adding NB3–NB5 work. |

## H13 merge

The historical source branch `codex/h13-substitution-discharge` at `c57c7aa`
was merged through `24f44cc`. The proof now lives at
`.archive/old_riemann_folder/Criteria/NymanBeurling/G11IntegralEvaluation.lean`.
The original source branch remains recoverable from tag
`archive/2026-07-15/codex/h13-substitution-discharge`.

## NB3--NB5 audit

The active-package endpoints below report only `propext`,
`Classical.choice`, and `Quot.sound`:

- `NB2.baezDuarteL2Error_nonneg`;
- `NB2.chi_sub_bdApprox_eq_tail_of_one_lt`;
- `NB3.mellin_evaluation_continuous_on_critical_strip`;
- `NB4.vanishing_transport_of_field_1`;
- `NB4.vanishing_transport`;
- `NB4.riemannZeta_ne_zero_of_nymanBeurlingCriterion`;
- `NB5.riemannZeta_one_sub_eq_zero_of_eq_zero`;
- `NB5.riemannZeta_one_sub_eq_zero_iff`;
- `NB5.riemannZeta_ne_zero_left_half_of_nymanBeurlingCriterion`;
- `NB5.criticalStripRiemannHypothesis_of_no_zeros_right_half`;
- `NB5.criticalStripRiemannHypothesis_of_nymanBeurlingCriterion`.

The NB4 theorem proves, from the finite-approximation Nyman--Beurling
criterion, that `riemannZeta s ≠ 0` when `1/2 < Re(s) < 1`. NB5 derives zeta
zero reflection from Mathlib's `riemannZeta_one_sub`, rules out the left half,
and proves that every zero in `0 < Re(s) < 1` lies on the critical line. The
historical project symmetry assumption is no longer used by this active
chain.

This endpoint is the critical-strip formulation used by the historical
project. It is not silently identified with Mathlib's broader root-level
`RiemannHypothesis`, whose definition also packages the classification of all
zeros outside the strip.

## Active-package port boundary

On `codex/nb-field-1-active-port`, the active package now contains:

1. the canonical `NB2` API for `chi01`, `rhoBD`, `bdApprox`, and
   `BaezDuarteL2Error`;
2. the finite-approximation Nyman--Beurling criterion as a proposition, not an
   unconditional assumption;
3. the Field 1 Mellin continuity theorem on `1/2 < Re(s) < 1`;
4. finite Mellin linearity and Field 2 zero transport;
5. the conditional right-half critical-strip zero-free theorem;
6. project-assumption-free functional-equation reflection and the conditional
   full critical-strip closure.

The remaining mathematical boundary is proving the finite-approximation
Nyman--Beurling criterion itself from the upstream quantitative input; NB5
does not assert that criterion unconditionally. The 63-commit-behind
historical Field 2 branch remains a proof/reference branch and should not
receive further direct development.

## Archive

The branch cleanup manifest and recovery instructions are in
`.archive/branches/2026-07-15/`. Fifty-five exploratory refs were tagged; 34
detached branch refs were deleted, and 21 tagged refs remain attached to
pre-existing worktrees pending separate clean-worktree review.
