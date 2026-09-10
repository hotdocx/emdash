# Homology Universality Research Checkpoint

Date: 2026-09-09

Status: preserved research artifacts; not active mathematical sources

These non-executable patch artifacts preserve the meaningful unpromoted
source states from the whole-homology/universality review. They include both
successful probes and rejected or incomplete alternatives. They are not
registered Lambdapi consumers, not a claim that every variant passes, and
not instructions to replace the active kernel.

The accepted whole-owned record implementation is checkpointed at
`74cefc18`; the row prototypes and their qualification were recorded in
`2605f42e`. Subsequent row-adapter code is preserved by this review's Git
checkpoint. The current living design is in
[the homology pilot](../../../docs/TYPESCRIPT_EMDASH_STRICT_INTERNAL_HOMOLOGY_PILOT_PLAN.md)
and [the broader universality audit](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_AUDIT_PLAN.md).

## Contents

| Artifact | Pinned baseline | Purpose |
|---|---|---|
| [mixed-mate-last-stage.patch](mixed-mate-last-stage.patch) | `21099f51` | Last mixed-mate/endpoint-alignment experiment; superseded and not a validated final architecture. |
| [two-field-record-stage.patch](two-field-record-stage.patch) | `21099f51` | Earlier two-field whole-owned homology record requiring the mixed-mate cut. |
| [actual-boundary-alias-stage.patch](actual-boundary-alias-stage.patch) | `21099f51` | Three-field record with immediate legacy alias migration; also includes isolated failed second-comparison diagnostics. |
| [pre-record-probes.patch](pre-record-probes.patch) | `21099f51` | Original whole-owned record and boundary-family probes, kept as isolated sources. |
| [current-reference-probes.patch](current-reference-probes.patch) | `2605f42e` | Direct row universals, current pullback cover and whole-H consumer, plus record zero-proof boundary. |
| [earlier-mixed-candidate.diff](earlier-mixed-candidate.diff) | `21099f51` | Earlier saved broad-alignment candidate; distinct from the last mixed stage. Not promoted. |
| [direct-connecting-experiments.patch](direct-connecting-experiments.patch) | `31cd9770` | Direct whole-H-endpoint connecting prototypes, mixed-presentation timeouts, diagnostics and an unused checked generic alternative. The consistent step-pair implementation is promoted separately. |

[manifest.json](manifest.json) records each source path, original temporary
location and SHA-256. [verification.json](verification.json) records recovery
checks: all seven patches apply to their pinned baselines, and all 92 embedded
source/driver versions were recovered with matching SHA-256 checksums. The
earlier saved diff was also preserved byte for byte.

The direct-connecting addition was independently verified on 2026-09-10.
Its manifest distinguishes checked prototypes, 90-second timeouts,
unqualified dependent scaffolding and diagnostic drivers. Original trailing
blank lines are preserved in these archived sources; their applicability
warnings do not indicate a hash mismatch or qualify a failed experiment.

## Recovery

Treat each patch as an independent experiment unless its dependencies and
the living ledger explicitly say otherwise. Several patches contain
alternative versions of the same files; do not apply all of them together.

When a separate experiment is authorized, materialize the indicated baseline
in an isolated checkout or source-only copy, inspect the patch, and use
`git apply --check` before applying it there. Do not apply these alternatives
over current user work. Existing ignored probe files may need a genuinely
fresh checkout rather than overwriting those files.

Keep every Lambdapi target bounded to 90 seconds with normal subject-reduction
checking. A failed or timed-out probe is preserved as a failed experiment;
patch recovery does not turn it into a qualified mathematical module.

No compiled objects, dependency trees or large raw logs are archived here.
The local attributes exempt only archival diff files from end-of-line/EOF
whitespace checks because unified-diff context markers require that spacing;
they do not relax source-code whitespace checks.
The existing logs remain under the goal worktree's ignored `emdash2/logs/`
and their relevant filenames/results are recorded in the living plan.
The ordinary promoted source/reviewer files and their Git history are the
authority for accepted computations. The general op/Sigma repair remains
separately deferred and is not part of these patches.
