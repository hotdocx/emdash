# Internal Opposite: Bounded Variance Repair Plan

Date: 2026-09-08

Status: active isolated design/probe tranche; no kernel migration promoted

Parent: [bounded long-exact homology and book](TYPESCRIPT_EMDASH_BOUNDED_LONG_EXACT_HOMOLOGY_AND_BOOK_PLAN.md)

Finding: [confirmed internal-op diagnostic](TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_DIAGNOSTIC.md)

## Objective And Scope

Correct the higher variance of internal opposite while retaining the existing
directed categories, whole functor/transfor action, and legitimate local
`Op_cat`, `Op_func`, and `Op_transf` observations. This is a prerequisite of
the unchanged long-exact goal, not a replacement for its remaining homology,
proof-CAS, and book work. Keep baseline `054b43bd` and all checkpoints.

The preceding clarification turn restated the confirmed diagnostic; it did
not repair the encoding. This tranche must add discriminating implementation
evidence, not merely repeat the soundness notice.

## Small Foundational Candidate

For the current strict working interpretation, first probe a dimension-two
opposite with unchanged objects and 1-arrows:

```text
Obj(Co₂(C)) = Obj(C)
Hom_Co₂(C)(x,y) = Op(Hom_C(x,y))
Co₂(Co₂(C)) = C.
```

The existing generic composition at the opposite Hom then reverses vertical
2-cell composition. Ambient 1-cell composition is unchanged. The corresponding
functor `Co₂(F)` has unchanged object/arrow action and whole Hom action
`Op(F₁(x,y))`. This expresses the dimension shift directly in the existing
iterated-Hom architecture; no new cell grammar is required.

The candidate corrected internal package has type

```text
op : Co₂(Cat) → Cat
op[C] = Op(C)
op[F] = Op(F)
op₁(A,B) : Op(Functor(A,B)) → Functor(Op(A),Op(B)).
```

Its transformation action must project to the existing `Op_transf` with
reversed endpoints. Preserve the whole hom functors at both stages and test
their next action, not just their capped components. Initially use a distinct
probe name so the active kernel is not partially migrated.

This is not a claim that finitely many projection checks establish all
omega/lax coherence. In particular, dualizing a lax transformation may change
its lax/oplax profile. Do not import the parallel strictness migration or hide
this question behind arbitrary invertibility assumptions. The existing
strict branch is the first qualification boundary.

## Omega Depth, Not A Two-Dimensional Truncation

The proposed `Co2_cat` reverses exactly dimension 2. Its Hom rule unfolds to

```text
Hom_(Hom_Co₂(C)(x,y))(f,g) = Hom_(Hom_C(x,y))(g,f),
```

and every further Hom keeps its original orientation. Thus dimension 3 and
all higher dimensions remain present. Both `Op_cat` (dimension 1 only) and
`Co2_cat` (dimension 2 only) are instances of dimension-selected duality.
They are not the odd/even dualities often also called `op`/`co` in the
omega-category literature. Do not change that convention silently.

The scalable mathematical rule for a set S of positive dimensions is

```text
S↓ = { n ≥ 1 | n+1 belongs to S }
Hom_(D_S C)(x,y) = D_(S↓)(Hom_C(y,x))  when 1 belongs to S,
Hom_(D_S C)(x,y) = D_(S↓)(Hom_C(x,y))  otherwise.
```

This follows the existing iterated-Hom architecture. For the strict
cartesian transformation interpretation, an n-transformation contributes an
(n+1)-cell of the category universe, so the internal universe source must
shift the reversed dimensions up by one. In particular `{1}` in the objects
requires `{2}` in the universe, which is exactly the proposed Co₂ source.
This is the mathematical justification to qualify, not a claim that all
universe rules have already been migrated or all higher computations checked.

Primary references reviewed:

- Ara and Guetta, [Lax functorialities of the comma construction for
  omega-categories, sections 2.4 and 2.22](https://arxiv.org/pdf/2503.08832v3):
  strict higher transformations and duality in a set of dimensions.
- Ara and Maltsiniotis, [Un theoreme A de Quillen pour les infinity-categories
  strictes II, sections 4.6–4.8](https://www.i2m.univ-amu.fr/perso/dimitri.ara/files/thmAII.pdf#page=32):
  dimension-selected, odd, even and total dualities, and the exchange of lax
  and oplax internal Homs under the odd/even dualities.

The latter formulas use the authors' odd/even conventions, not emdash's
dimension-1-only `Op_cat`. They warn against identifying all possible
transformation profiles; they are not a ready-made proof of a dimension-1
lax-profile implementation. The goal remains full omega-dimensional action,
with no truncation or collapse of arbitrary higher cells.

## Propagation Is Part Of The Repair

An arbitrary directed family `E : K → Cat` cannot simply retain its base and
be postcomposed with the corrected `op`. The candidate is instead

```text
Eᵒᵖ : Co₂(K) → Cat
Eᵒᵖ = op ∘ Co₂(E).
```

At objects and base 1-arrows this retains the desired familiar fibre formulas;
at base 2-cells it exposes the formerly missing reversal. A same-base interface
needs an explicitly justified base/coherence restriction or comparison.
Do not add an unrestricted `K → Co₂(K)` cast: that would recreate the defect.

For the same strict transformation interpretation, the candidate whole family
operator must also expose the shifted variance of transformations between
displayed maps:

```text
Op_catd_func(K) : Co₂(Catd(K)) → Catd(Co₂(K)).
```

It sends a displayed map `FF : E → D` to a displayed map between the new
opposite families, with component `Op_func(FF[k])`. A transformation between
such displayed maps reverses, because its components are ordinary
transformations of fibre functors. This signature is not yet implemented by
the local prototype; it is the next whole-family qualification obligation.
The generic Co₂ action on functor categories should own that construction,
rather than another untyped same-base identification.

Before migration, inventory the actual uses of `op`, `Op_catd`,
`Op_catd_func`, and `Op_funcd`. In particular test whether the old family
declarations can recreate the problematic covariant operation independently
of the literal `op` name. A rename/type change of one symbol is not sufficient
if another unrestricted constructor reinstates the same action.

## Execution Ledger

| Row | Status | Required evidence |
|---|---|---|
| OP-REPAIR-1 | baseline reproduced | original native-empty fixture accepted under the unchanged core; exact source and log retained |
| OP-REPAIR-2 | isolated prototype checked; not promoted | Co₂ category/functor projections, corrected whole op action, correctly directed transformation computation and a rejected wrong-direction application |
| OP-REPAIR-3 | family-only counterexample confirmed; propagation inventory still open | same-base family reconstruction control and source-level dependent-owner inventory |
| OP-REPAIR-4 | pending | smallest coherent owner-position migration that removes the bad covariant surfaces and qualifies their legitimate consumers |
| OP-REPAIR-5 | pending | positive opposite regressions, exact variance-negative fixture, warnings/SOP/health qualification and downstream homology consumer |

The append/import probes for row 2 establish local types and observations only:
the imported old kernel still contains the defect. They are not a consistency
proof or evidence that the active signature has been repaired. A final negative
must run against the migrated owner, not an unrelated import, syntax error,
missing symbol, or timed-out check.

## Checked Prototype And Family-Only Control

The durable non-library candidate and reviewer are
[`internal_op_co2_prototype.lp`](../emdash2/audits/internal_op_co2_prototype.lp)
and [`internal_op_co2_prototype_checks.lp`](../emdash2/audits/internal_op_co2_prototype_checks.lp).
They add no rules to the active kernel or positive source registry. The
prototype has twelve runtime rules, no unifier, and no primitive equality
witness. The two whole action views and opposite-family construction are
transparent definitions.

The eleven positive observations cover the second-Hom direction, unchanged
third-Hom direction, involution, whole Co₂ action, correct functor and
transformation projections, retained next whole hom action, and the original
fibre/1-arrow formulas at the corrected family base. The direction-correct
point-functor construction reduces to the original input arrow. Two negative
checks reject the swapped transformation type and the old diagnostic's
wrong-direction application. An initial reviewer typo used `@Transf` without
its category arguments and was rejected as an ill-formed expected type; it
was corrected before the passing run and is not counted as variance evidence.

The minimal Co₂ prototype passed subject reduction in
`hint_internal_op_co2_foundation-20260908-142422.log`. Its final ignored
reviewer passed in `hint_internal_op_co2_checks-20260908-142859.log`.
The strict inferred-LHS-slot audit reports zero unreviewed compound slots.
The tracked reviewer passes in
`internal_op_co2_prototype_checks-20260908-143113.log`; the warning-enabled
run is `internal_op_co2_prototype_checks-20260908-143245.log`. Its imported
core contributes the unchanged 1,125 critical-pair / 157 pattern reports.
The append-only prototype contributes 49 critical pairs and no new pattern
reports: four identity-projection pairs, sixteen composition/self pairs,
ten action/self pairs, eighteen composition/action pairs, and one Co₂-functor
involution pair. ANSI-stripped strict parsing accounts for all 1,174 pairs.
These are interaction families to qualify at the eventual owning position,
not a warning-count veto or a global confluence claim. The initial direct
parse of the colored log failed its location parser; stripping color restored
the expected complete classification without rerunning Lambdapi.

Active-reference and report-lifecycle/header checks pass. Registry inspection
confirms neither prototype file is a registered positive target. No kernel,
CAS, book source, generated catalog, or health snapshot changes in this
audit-only tranche; no unrelated aggregate is run.

A full copied-core control comments out the original `op` declaration and
all six rules that directly refer to it, while retaining the separate
same-base `Op_catd` formation, fibre and capped-action rules. In that core,

```text
reconstructed_covariant_op : Functor(Cat,Cat)
reconstructed_covariant_op = Op_catd(id_Cat)
```

still yields a closed native-empty witness by the original construction.
The copy and consumer are `hint_internal_op_family_only_core.lp` and
`hint_internal_op_family_only_empty.lp`; the bounded successful reproduction
is `hint_internal_op_family_only_empty-20260908-142523.log`. No new axiom,
rewrite or unification rule is needed by that control. The original unchanged
fixture was also rerun in `internal_op_empty_reproducer-20260908-141839.log`.

Therefore the family base change is necessary, not a speculative extension
of the repair. Keeping the old unrestricted same-base interface would undo
the correction even if no source expression mentioned the literal `op`.

## Validation And Handoff

Use ignored probes first and at most 90 seconds per Lambdapi invocation, with
ordinary subject-reduction checking. Put candidate rules at their intended
owning positions before promotion. Keep inferred endpoint slots free of
compound guards except for measured discriminators. Preserve mapped-arrow
composition orientation; no broad new cut or proof-time equality may hide an
ill-typed opposite action.

Documentation/audit checkpoints use exact diff and the owning link/lifecycle
checks, not repository aggregates. Kernel promotion requires its scoped
warning comparison, LHS audits and affected consumer checks under the parent
SOP. Local validated checkpoints are authorized; no push, merge, publication,
history rewriting, or worktree cleanup is authorized.
