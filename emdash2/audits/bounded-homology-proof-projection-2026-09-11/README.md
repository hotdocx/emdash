# Bounded Homology: Proof-Projection And Resource Diagnostics

Date: 2026-09-11
Git baseline: `fb5a9c09238af3010cb7d70a8cc2068a84f679a8`
Unchanged active mathematical baseline: `ff139362be71dfec03142d05dda2dc123b3624a5`

This is a non-executable research archive, not library promotion. The
[living plan](../../../docs/TYPESCRIPT_EMDASH_BOUNDED_LONG_EXACT_HOMOLOGY_AND_BOOK_PLAN.md#degreerole-indexing-current-representation-experiment)
still requires the complete bounded formal result, retained proof–CAS
consumer, final audit and book. Existing whole H, delta, window exactness,
finite iterator and native results remain unchanged.

## What The Isolation Establishes

The two inputs below are the already-checked overlapping three-row records
of adjacent finite windows. They agree by conversion before any observation
is applied. The installed checker, normal subject reduction, a 90-second
deadline and the new 2 GiB resource guard give these results:

| Compared observation | Result |
| --- | --- |
| Row, whole row functor, point, source vertex | Each passes in about 2 seconds |
| Source chain pair's incoming and outgoing differentials | Each passes in 2 seconds |
| Complete source chain pair | Allocation failure, 7 seconds |
| Derived chain-zero proof | Allocation failure, 7 seconds |
| Both chain-zero proofs declared separately | Passes in 1 second |
| Reflexivity comparison of those proofs | Allocation failure, 7 seconds |
| Lower row's selected monicity observation | Allocation failure, 8 seconds |
| Complete lower row point | Allocation failure, 8 seconds |

Thus no missing annihilation theorem is exposed. The first failing field
comparison in the source-pair ladder is its zero evidence; failure can also
be reproduced before applying the selected monicity proof. This is narrower
than saying that H itself fails. It does not prove that every earlier
timeout has this same cause or that proof irrelevance alone will fix it.

In particular, an earlier control with an opaque tail and Unit annotations
still contained a computed H arrow in its type indices. That H input in
turn contains derived chain-zero evidence. The earlier result excludes the
tail's exactness payload as a necessary cause; it does not exclude all
proof-bearing subterms of that computed index.

A guarded backtrace catches allocation failure in beta substitution during
rewrite matching (`Term.subst`, `Eval.whnf_stk`, `Eval.walk`, `Eval.eq`). It
does not identify a particular offending rule. A rewriting trace hits the
64 MiB file limit and repeatedly prints row/window projections; repeated
debug output alone is not evidence of a rewrite loop. No implicit guard,
generic cut, proof-irrelevance rule or checker change was promoted.

## Representation Alternatives And Their Boundaries

The direct OneCat input prototype forms the original zero-cone object from
the existing chain-zero proof and actual walking-arrow transformation,
without using a selected kernel just to introduce the input complex. An
explicit transformation endpoint annotation lets existing usability relate
its two diagram presentations. Six runtime observations recover the original
vertices/differentials and fixed-pair point action; a whole Hom-action query
also checks. This is not yet a general chain-map replacement or proof of
agreement of all kernel/cokernel selections.

The direct input and its H image still exhaust the guard when compared at
the two shared triples. It is therefore preserved as a structurally useful
candidate, not selected as a performance fix. The same-boundary selected-
cokernel usability definitions also check generically, but their actual
canonical delta consumer still fails under the guard. None introduces a
second H, object transport, opaque equality or new universal selection.

Three record variants are preserved:

- Stable whole row-family classifier/constructor/projections: source checking
  exhausts the guard at the function-valued data beta rule.
- Boxed row-family evidence, retaining the generic outer Sigma: owning source
  and prerequisites check, but the direct input comparison still fails.
- Stable `ComputationalShortExactTriple` with the same monic/epic/exact
  fields and three constructor beta rules: owning source, strict LHS audit
  and affected prerequisites check. Monicity sharing still fails, in
  14 seconds. It is not sufficient as a remedy.

Combining the first and third variants still fails while checking the
row-family source (18 seconds). Replacing its function-valued beta with an
applied point beta also fails. The latter one-line change is retained in
[point-beta-variant.patch](point-beta-variant.patch); apply it only to a
separate recovered copy of the stable row-family variant, together with
the stable short-exact-triple variant. No failed variant is an active owner.
There is no new proof postulate or proof erasure in these record experiments:
their constructor inputs remain precisely the original evidence.
Retaining all seven shared flat indices in the function-valued beta's LHS
also fails at source checking; [flat-guard-variant.patch](flat-guard-variant.patch)
preserves that separate test. Neither point application nor repeated flat
guards establish a solution to the subject-reduction reconstruction cost.

## Checker Experiments Are Diagnostics Only

The installed binary reports version 3.0.0 but is built from pinned revision
`db4f7809961b8c107247613067fb567491fb0b84`. The separate `lambdapi.3.0.0`
release source cache is not that baseline. The archive preserves the three
small evaluation patches and a smoke fixture:

- Release-cache control/trial builds time out on a fresh kernel and are not
  an appropriate installed-checker comparison.
- The exact pinned control checks its prerequisites; direct H-map sharing
  reaches 90 seconds.
- Early same-head congruence with rollback/fallback regresses an existing
  source-boundary-zero prerequisite to 90 seconds. It is rejected as a remedy.
- Full-spine comparison after weak-head normalization checks prerequisites;
  the final comparison has no successful completion record and is unqualified.

Smoke tests preserve erasing rewrites, unequal opaque arguments and common
normal forms, but are not a full checker validation. No variant was installed.
Compiled objects cannot be shared between different checker binaries; their
marshalled closures are binary-specific. Rebuild each private dependency graph
with its own binary. Future builds/checks must be serial and resource-bounded.

## Safety And Recovery

Kernel journal evidence confirms earlier global OOM kills of checker processes
using approximately 22–23 GiB anonymous resident memory. Missing terminal
records around that period cannot be attributed solely to conversational
interruptions. New allocation failures are contained by the guard and are
not mathematical counterexamples.

The guarded leaf and diagnostic drivers are included as recovery evidence.
Do not run an obsolete unguarded copy. Other existing staged gates are not
automatically covered: route each checker command through the guard, not the
entire aggregate through one outer 90-second deadline. The guard now also
sets a scope-wide deadline, and its nine tests include killing a descendant
that starts a separate process session.

[prototypes.patch](prototypes.patch) recovers 43 sources/patches into an EMPTY
directory. [manifest.json](manifest.json) records individual statuses, byte
counts and hashes; [verification.json](verification.json) records successful
patch application and exact recovery. Active-source dependencies come from
the baseline; prior probe dependencies are preserved in the earlier endpoint,
indexing and canonical-degree archives. Variant files are deliberately under
`variants/`, not mixed into active source paths. The local whitespace exemption
preserves raw patch contents only. Logs, compiled objects and binaries are not
committed.

Representative logs under `emdash2/logs/probes/`:

- `homology_direct_native_input_checks-leaf-20260910-231729.log`
- `homology_direct_input_sharing-leaf-20260910-233003.log`
- `homology-direct-input-backtrace-20260910.log`
- `homology_direct_input_match_trace-leaf-20260910-234925.log`
- `homology_projection_isolation_1-leaf-20260911-002741.log`
- `homology_projection_isolation_6-leaf-20260911-002800.log`
- `homology_projection_isolation_7-leaf-20260911-002817.log`
- `homology_projection_isolation_8-leaf-20260911-002819.log`
- `homology_source_path_declarations-leaf-20260911-002903.log`
- `homology_source_path_refl-leaf-20260911-003000.log`
- `homology_source_mono_sharing-leaf-20260911-003048.log`
- `short-evidence-owner-20260911-003258.log`
- `short-evidence-owner-20260911-003518.log`.

The two resource-lock refusals while a prior check was still running are
admission-control events, not failed mathematical checks; both intended
projection tests were subsequently run serially. The inherited op/Sigma
variance notices remain in force and are not repaired by these diagnostics.
