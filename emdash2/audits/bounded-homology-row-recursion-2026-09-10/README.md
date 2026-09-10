# Bounded Homology: Row-Recursion Boundary

Date: 2026-09-10
Baseline: `64d5cd28`

This is non-executable research evidence. No candidate here changes the active
Lambdapi library or proves the still-open bounded generator. The
[living plan](../../../docs/TYPESCRIPT_EMDASH_BOUNDED_LONG_EXACT_HOMOLOGY_AND_BOOK_PLAN.md#bounded-generator-and-endpoint-zero-continuation)
owns the next implementation and the unchanged full-goal completion boundary.

## Mathematical Question

For a coherent triple S of adjacent short-exact row families, let a(S) be
the original H(inclusion) arrow. Extending S by the next row/map/chain-zero
datum gives S′. The proved window has the form

```text
Hₙ(A) → Hₙ(B) → Hₙ(C) → Hₙ₋₁(A) → Hₙ₋₁(B).
```

Its last arrow is a(S′). The successor operation must therefore take an exact
tail beginning at a(S′) and prepend the three existing pairs/proofs, producing
an exact tail beginning at a(S). It must preserve all original H objects,
arrows and universal choices.

The mathematical successor construction is already the existing
`homology_whole_window_extend`. The expensive LF step compares its expected
continuation type, written with the individual retained rows/maps, with a
continuation written using point views of `homology_row_triple_shift`.

The typing trace reaches `check that rest is of type ...` and then conversion
between those two exact-tail presentations. The checker's word `coerce` in
that diagnostic is not a cast added to the implementation. No path transport,
equality assumption or new exactness theorem was inserted.

## Findings

- The six transparent triple pair/inclusion/H-point/action views check.
  The inclusion's type checks both through the short endpoint aliases and
  with the literal H endpoint terms.
- The exact-tail family and empty tail check independently. The latter takes
  two seconds inside the fresh staged check.
- Partially applying the existing window extension to the whole-row
  observations checks in four seconds. Thus it is not necessary to assume
  the window theorem at this new instance.
- Explicit continuation/result annotations through the shifted triple reach
  90 seconds. Removing only the result annotation or making the H objects
  literal does not solve that boundary.
- Stating the existing boundary arrows directly as H(inclusion), instead of
  projections of large proved pairs, gives a checked window-extension
  signature. This alone does not qualify the recursive generator.
- Ordinary Nat recursion, the explicit-IH variant and a Nat-guarded recursive
  rule candidate reach 90 seconds. The constructor-guarded candidate was
  prepared and LHS-audited but not run; it is not a checked solution.
- Keeping PA/normality explicit also times out at the shifted-record
  continuation comparison. It is not the selected fix.
- The field-indexed successor `homology_row_fields_extend` checks. Its input
  and output name the same original rows/maps directly, so their H expressions
  match without unfolding a shifted opaque triple at this boundary.
  A recheck of its final source, after removing an unused import, takes
  3.59 seconds.
- `HomologyRowFieldSpan` retains those original rows, maps and zero data as
  rigid indices. Its source and four local constructor beta rules check in
  0.64 seconds. This is a candidate input representation, not yet a promoted
  replacement or a tested full generator.
- The independent Nat prefix operation `finite_arrow_tail_take` checks
  zero/proper/full prefixes and preservation of an original annotation:
  four positive controls and one distinct-witness negative, in addition to
  the imported older fixture controls.

No timeout is treated as a mathematical counterexample, no warning count is
used as a veto, and no failed rule is installed in the library.

## Evidence And Recovery

[manifest.json](manifest.json) records all 38 versions, byte counts, SHA-256
values and qualification states. The two patches create only the recorded
ignored probe paths:

- [checked_building_blocks.patch](checked_building_blocks.patch);
- [unqualified_assembly_trials.patch](unqualified_assembly_trials.patch).

[verification.json](verification.json) records successful new-file patch
validation and byte-for-byte recovery of all 38 versions, including their
SHA-256 values and agreement with the current probe sources.

The first label means source checking, not that every proposed consumer or
the full recursive construction is qualified. The second includes unreached
reviewers and an unrun constructor-recursion candidate; their source text
must not be mistaken for passing tests.

The fresh exact-source staged runs are:

- `logs/probes/homology-row-span-generator-quiet-20260910-134652.log`;
- `logs/probes/homology-row-extension-comparison-warnings-20260910-135407.log`;
- `logs/probes/homology-row-span-canonical-quiet-20260910-140253.log`;
- `logs/probes/homology-row-span-inferred-step-quiet-20260910-140832.log`;
- `logs/probes/homology-row-span-direct-edges-warnings-20260910-141239.log`;
- `logs/probes/homology-row-span-induction-boundaries-warnings-20260910-142304.log`.

Later research calls reused a temporary copy of the last fresh checked
dependency tree. All 509 root LP source files were compared byte-for-byte
with the worktree, with no differences. Candidate source copies were
refreshed before checking, normal subject reduction remained enabled, and
every call was capped at 90 seconds. These temporary object files are not
archived and are not a substitute for final fresh-source qualification.

## Next Action

Complete the field-indexed finite-span prototype and its ordinary Nat
generator. Test the empty, one-window and actual two-window reductions,
the wrong-overlap boundary, and the retained original exactness witnesses.
Only after that comparison should the public triple/span facade be adapted
and the smallest coherent source change be promoted.

The original H/δ architecture and native proof–CAS consumer remain in place.
Endpoint-zero application, conventional degree ordering, final formal/native
integration and the Chapter 31 revision still belong to the full goal.
