# Active branches and integration state

**Audited:** 15 July 2026

| Branch | Commit | Status | Next action |
|---|---:|---|---|
| `main` | `7d17f96` | H13 is merged and the NB2 active-package API/audit is integrated. | Review the active NB3/NB4 port before integration. |
| `codex/nb-field-1-active-port` | current work | Finite Báez--Duarte approximants, Field 1 continuity, and Field 2 right-half zero detection are ported to the active package and pass the package audit. | Review and merge; then isolate the left-half symmetry closure as the next NB field. |
| `codex/h14-corrected-aristotle-specs` | `b499bf2` | H14 reference/audit; qualitative and effective Mertens endpoints are project-axiom-free. | Retain as the H14 publication source. |
| `codex/bridge-field-1-mellin-continuity` | `11cde38` | Already an ancestor of `main`; the archived Field 1 file is byte-identical. | Use as a reference while porting the theorem to the active package. |
| `codex/nb-field-2-zero-detection-current` | `12a14d1` | Retained for NB2–NB5 work. Its Field 2 file is byte-identical to the archived file on `main`, but the branch is 63 main commits behind. | Refresh from current `main` before adding NB3–NB5 work. |

## H13 merge

The historical source branch `codex/h13-substitution-discharge` at `c57c7aa`
was merged through `24f44cc`. The proof now lives at
`.archive/old_riemann_folder/Criteria/NymanBeurling/G11IntegralEvaluation.lean`.
The original source branch remains recoverable from tag
`archive/2026-07-15/codex/h13-substitution-discharge`.

## NB Field 1 and Field 2 audit

The active-package endpoints below report only `propext`,
`Classical.choice`, and `Quot.sound`:

- `NB2.baezDuarteL2Error_nonneg`;
- `NB2.chi_sub_bdApprox_eq_tail_of_one_lt`;
- `NB3.mellin_evaluation_continuous_on_critical_strip`;
- `NB4.vanishing_transport_of_field_1`;
- `NB4.vanishing_transport`;
- `NB4.riemannZeta_ne_zero_of_nymanBeurlingCriterion`.

The last theorem proves, from the finite-approximation Nyman--Beurling
criterion, that `riemannZeta s ≠ 0` when `1/2 < Re(s) < 1`. It does not claim
the left half of the critical strip. The historical full-forward wrapper used
the project axiom `RH.Basic.zero_symmetry`; that wrapper was intentionally not
ported. A project-axiom-free symmetry or functional-equation closure remains
the next independent field.

## Active-package port boundary

On `codex/nb-field-1-active-port`, the active package now contains:

1. the canonical `NB2` API for `chi01`, `rhoBD`, `bdApprox`, and
   `BaezDuarteL2Error`;
2. the finite-approximation Nyman--Beurling criterion as a proposition, not an
   unconditional assumption;
3. the Field 1 Mellin continuity theorem on `1/2 < Re(s) < 1`;
4. finite Mellin linearity and Field 2 zero transport;
5. the conditional right-half critical-strip zero-free theorem.

The next boundary is the left-half closure. The 63-commit-behind historical
Field 2 branch remains a proof/reference branch and should not receive further
direct development.

## Archive

The branch cleanup manifest and recovery instructions are in
`.archive/branches/2026-07-15/`. Fifty-five exploratory refs were tagged; 34
detached branch refs were deleted, and 21 tagged refs remain attached to
pre-existing worktrees pending separate clean-worktree review.
