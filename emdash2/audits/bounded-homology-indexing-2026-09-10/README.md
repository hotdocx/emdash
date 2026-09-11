# Bounded Homology: Degree/Role Indexing Experiment

Date: 2026-09-10
Baseline: `581d3a2642b0d989e60f2da1e37ed8a54d7d554d`
Active LP baseline: `ff139362be71dfec03142d05dda2dc123b3624a5`

This non-executable archive preserves eleven prototype sources. Nine check;
two are unsuccessful alternatives. No active library owner, registered test,
native algorithm or book claim changes in this research checkpoint.
The [living decision](../../../docs/TYPESCRIPT_EMDASH_BOUNDED_LONG_EXACT_HOMOLOGY_AND_BOOK_PLAN.md#degreerole-indexing-current-representation-experiment)
retains the complete bounded theorem and proof–CAS/book obligations.

## Question And Result

Van Doorn's dissertation, §4.1.1, printed pages 68–69, replaces a flat
natural-number sequence index by degree × three roles to obtain direct
judgmental endpoint presentations. This experiment uses bounded indices
0,…,n and a separate A/B/C role. It does not import the dissertation's
homotopy-group construction, exactness definition or sign conventions.

The existing flat-tail failure can occur with an opaque tail and an already
supplied endpoint proof. Exactness proof payloads and comparison of two
proof bodies are not necessary causes. The new question is whether the
endpoint laws check when they refer directly to whole H at the first/last
indexed windows, without reconstructing a target from a trimmed exact tail.

Both laws check at an arbitrary symbolic bound. They retain the original
column pairs and whole H, and use the existing zero-middle theorem after
the row mono/epi cancellation. The operational data contain neither those
proof arguments nor object casts. This is not a proof of a runtime zero
rewrite and does not identify either H object with a different zero object.

## Checked Prototypes

- `finite_role_indices.lp`: bounded native index constructors, weakening,
  last index, three roles and role selection returning actual whole functors.
  Four explicit rules consist only of two fresh decoding clauses and two
  index-constructor computations; native recursors have their generated beta
  rules. The strict inferred-slot audit passes and the owner emits no new
  rule warning.
- `finite_role_indices_checks.lp`: six positive/three negative controls for
  symbolic index beta, bounds, role separation, whole selection and Hom action.
- `homology_finite_row_lookup.lp`: two transparent functions form three-row
  states and four-row windows from bounded original whole rows/maps/zero data.
  It checks in one second. No independent overlap equation is supplied.
- `homology_finite_row_context.lp`: a symbolic-bound consumer checks three
  actual overlap observations and the final delta component at its whole-H
  target, in three seconds. Its constants are reviewer inputs, not new
  library axioms or a constructed closed model.
- `homology_finite_indexed_endpoint_direct.lp` and
  `homology_finite_indexed_first_zero_direct.lp`: the two endpoint-zero proofs
  check in three seconds each, applying the existing theorem directly to
  the original left/right column pair.
- `homology_window_endpoint_zero_direct.lp`: abstracts those proofs into
  reusable parameterized whole-window lemmas; checks in two seconds.
- `homology_finite_indexed_endpoint_checks.lp`: applies the reusable lemmas
  to both indexed endpoints, checks whole H/delta Hom action and rejects
  evidence about an unrelated object or a missing zero proof. Quiet and
  warning-enabled runs check in two seconds.
- `homology_finite_indexed_exactness.lp`: applies all three existing window
  exactness theorems at arbitrary indexed windows, in three seconds. It
  does not yet construct the complete global degree/role result carrier.

The reviewers contain twelve positive and five negative assertions, in
addition to the checked proof definitions. The initial index reviewer had
a missing `⊢` parser token; the correction is routine fixture syntax, not
a mathematical or rule-design change.

## Unsuccessful Alternatives

`homology_finite_indexed_endpoint_zero.lp` passes the projected rows through
the older row-field zero helper. It reaches the 90-second bound in ordinary
and verbose runs, before the first H-zero definition completes. The direct
column-pair proofs above check without introducing a new unifier. Indexing
does not make every expanded re-expression cheap.

`finite_endpoint_congruence_consumer.lp` is the last unarchived experiment
from the preceding endpoint audit: all typed arguments are retained by a
congruence unifier for a stable final-target observer. Its consumer times out.
It requires the previous audit's copied stable-target owner, not the active
transparent owner. Neither that replacement nor this unifier is promoted.

## Evidence And Scope

Every Lambdapi invocation uses normal subject reduction and a 90-second
ceiling. The retained research graph
`/tmp/emdash-homology-boundary-research.FtixXS` was compared with all 516
active root LP sources, with zero byte mismatches. It reuses that graph's
checked dependency objects; this is not a new full fresh-graph library gate.

Representative logs under `emdash2/logs/probes/`:

- `homology_finite_row_context-leaf-20260910-201525.log`
- `homology_finite_indexed_endpoint_direct-leaf-20260910-201811.log`
- `homology_finite_indexed_first_zero_direct-leaf-20260910-201910.log`
- `homology_window_endpoint_zero_direct-leaf-20260910-202042.log`
- `homology_finite_indexed_endpoint_checks-leaf-20260910-202227.log`
- `homology_finite_indexed_endpoint_checks-leaf-20260910-202458.log`
- `homology_finite_indexed_exactness-leaf-20260910-202329.log`
- `finite_role_indices-leaf-20260910-202247.log`
- `finite_role_indices_checks-leaf-20260910-202457.log`
- `homology_finite_indexed_endpoint_zero-leaf-20260910-201834.log` (timeout).

The active 898-file source-health boundary and inherited kernel warning
inventory are unchanged. The documented inherited op/Sigma soundness
boundaries remain; green checks are not a consistency certificate.

Next: qualify the entire finite object/arrow family, neighboring-window
H(inclusion) sharing, role-specific law observations and one retained finite
input/native-model consumer. Only then promote the representation and update
the final bounded theorem/book. This checkpoint does not complete the goal.

## Recovery

[manifest.json](manifest.json) records every path, status, byte count and
SHA-256. [prototypes.patch](prototypes.patch) recreates the eleven ignored
sources in an EMPTY recovery directory. Do not apply it over an occupied
worktree. [verification.json](verification.json) records exact recovery.

The earlier `bounded-homology-endpoints-2026-09-10` archive supplies the reused
middle-zero predicate, old row-field helper alternatives and bounded leaf
runner. The active LP baseline supplies all actual mathematical owners.
Recover those dependencies before attempting source rechecks; do not run
the two explicitly unsuccessful alternatives as positive library tests.
No compilation objects or logs are committed.
