# Active branches and integration state

**Audited:** 15 July 2026

| Branch | Commit | Status | Next action |
|---|---:|---|---|
| `main` | `f65da6f` | H13 is merged and the NB2 active-package API/audit is integrated. | Continue active-package integration without restoring the retired monolithic library. |
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

The following endpoints report only `propext`, `Classical.choice`, and
`Quot.sound`:

- `mellin_evaluation_continuous_on_critical_strip`;
- `nyman_field_1`;
- `vanishing_transport_of_field_1`;
- `mellinNymanBridgeDebts_complete_proved`.

The wrapper `NBForward_of_complete_mellinNymanBridgeDebts` additionally
depends on the existing project axiom `RH.Basic.zero_symmetry`. Field 1 and
Field 2 are therefore clean, but the full forward bridge is not yet a
project-axiom-free endpoint.

## Active-package port boundary

The current `mathlib/NBMellinTools` package contains the unconditional NB2
base Mellin formula, but `BaezDuarteTail.lean` remains an archived placeholder.
Before the historical Field 1/2 files can become active modules, the package
needs:

1. one canonical namespace/API for `chi01`, `rhoBD`, `bdApprox`, and
   `BaezDuarteL2Error`;
2. the finite approximant and Nyman–Beurling criterion definitions;
3. a port of the Field 1 continuity theorem using the active Mellin API;
4. a port of Field 2 zero transport;
5. explicit isolation or discharge of `RH.Basic.zero_symmetry` in NB3–NB5.

The recommended implementation branch should start from current `main`; the
63-commit-behind Field 2 branch should remain a proof/reference branch rather
than receive further direct development.

## Archive

The branch cleanup manifest and recovery instructions are in
`.archive/branches/2026-07-15/`. Fifty-five exploratory refs were tagged; 34
detached branch refs were deleted, and 21 tagged refs remain attached to
pre-existing worktrees pending separate clean-worktree review.
