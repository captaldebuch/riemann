# Paper-Claim Validity Protocol

## Rule

An artifact is not accepted merely because it can be linked to a published
paper. Whenever the project extracts, translates, applies, or formalizes a
claim from a paper, it records a `paperClaims` entry on the resulting artifact.
That entry is a review of the *specific use* being made here; it is not a claim
that the paper as a whole has been re-refereed.

Bibliographic `informs` and `motivatedBy` links signal relevance only. A
`derivedFrom` link to a `SourcePaper` is allowed only when a matching,
machine-validated `paperClaims` review exists.

## Required review

For each imported claim, record:

1. the exact paper artifact and a usable location (theorem, section, page, or
   equation where available);
2. the claim being imported or the proposed translation;
3. a definition and normalization check: variables, ranges, weights,
   multiplicity conventions, and indexing;
4. a hypothesis and scope check: domains, regularity, convergence, zero-free
   assumptions, and conditional hypotheses;
5. the review method, date, reviewer label, and a concise evidence note.

Use at least two independent checks whenever the artifact is intended to carry
a quantitative estimate or a route toward RH: source reading plus hypothesis
or definition checking, and a formalization or numerical check when feasible.

## Validity statuses

| Status | Meaning | Handling |
| --- | --- | --- |
| `sound` | The cited claim is faithfully stated and its hypotheses match this artifact’s use. | May support the artifact, but does not replace a Lean proof. |
| `conditional` | The translation is sound only under recorded assumptions. | List every condition; never display as unconditional. |
| `scope_mismatch` | A source result exists, but its hypotheses, normalization, or conclusion do not license this use. | Mark the artifact open and preserve the explanatory note. |
| `unsupported` | The paper does not yet support the encoded artifact—for example, the Lean statement is a placeholder. | Do not use it as proof evidence. |
| `contradicted` | A counterexample, failed required numerical test, or authoritative correction defeats the use. | Retain the artifact as a diagnostic, with the evidence note. |
| `unreviewed` | A source has been identified but the required review is incomplete. | Relevance only; do not create a proof dependency. |

Corrections are additive: retain the source location and the reason for the
change rather than overwriting a failed claim as if it had never existed.

## Registry enforcement

`artifacts/schema/artifact.schema.json` defines `paperClaims`, and
`scripts/build-artifact-index.py --validate` checks its structure. In
particular, a `derivedFrom` relationship targeting a `SourcePaper` fails
validation unless the source artifact has a matching review entry.
