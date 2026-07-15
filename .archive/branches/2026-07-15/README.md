# Branch archive — 2026-07-15

This archive records the exploratory branch cleanup performed after the H13
substitution discharge. Every branch in `manifest.tsv` is preserved by the
lightweight tag

```text
archive/2026-07-15/<original-branch-name>
```

before its original branch ref is deleted. A branch can be recovered with:

```bash
git switch -c recovered/<name> archive/2026-07-15/<original-branch-name>
```

Branches attached to an existing worktree are tagged but retained until that
worktree is separately checked and removed. This avoids destroying uncommitted
work. Branches with no worktree are deleted after their archive tag is created.
The first cleanup pass created 55 tags, deleted 34 original branch refs, and
left 21 tagged refs attached to pre-existing worktrees.

## Active refs deliberately retained

| Branch | Commit | Role | Integration status |
|---|---|---|---|
| `codex/h14-corrected-aristotle-specs` | `b499bf2` | H14 reference/audit | Retained as the verified H14 source. |
| `codex/bridge-field-1-mellin-continuity` | `11cde38` | NB Field 1 | Already an ancestor of `main`; archived source is byte-identical. |
| `codex/nb-field-2-zero-detection-current` | `12a14d1` | NB Fields 2–5 continuation | Retained, but 63 main commits behind; its Field 2 source is byte-identical to the archived source on `main`. Refresh before NB3 work. |

## H13 integration

`codex/h13-substitution-discharge` (`c57c7aa`) was merged into `main` through
merge commit `24f44cc`. Git applied the change to
`.archive/old_riemann_folder/Criteria/NymanBeurling/G11IntegralEvaluation.lean`
without restoring the retired top-level source tree.

## Repository hosting

No Git remote was configured at archive time. The integration is therefore a
local merge rather than a hosted pull request; a PR can only be created after a
remote is added.
