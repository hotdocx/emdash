# TypeScript Elaborator v3.2 Mixed-Mode Displayed Telescope Plan

Date: 2026-07-31

Status: living approved architecture; `MIXED-NEST-0A` is implemented and
focused-green; `MIXED-NEST-1A` is the next dependency-ready slice

This is the dedicated successor to the completed bounded work recorded in
[`TYPESCRIPT_ELABORATOR_V3_2_DISPLAYED_BRACKET_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_DISPLAYED_BRACKET_PLAN.md).
It does not rewrite that plan's frozen completion history. It corrects and
continues the still-open claims named there: nested displayed abstraction,
mixed variance, and arbitrary finite telescope depth.

The user approved the corrected architecture and asked that its analysis be
recorded comprehensively before implementation continues. The decision
response is archived for recovery as
`infinity-codex:019fb460-a0c8-7373-926f-f754198d6e51:019fb5aa-316e-7082-9a86-802b25e1bc9d`.
The archive is decision evidence only; active code, the active Lambdapi
kernel, this plan, and repository SOP remain authoritative.

## Objective

Make categorical/displayed variables and binders recursively usable at
arbitrary finite telescope depth, including the mixed variance that appears
as soon as a nested target is itself a varying functor category.

The end state must preserve the project's internalization rule:

- a functorial binder constructs a genuine functor with object and arrow
  action;
- a natural/displayed binder constructs the corresponding coherent internal
  package;
- typed application selects `fapp*`, `tapp*`, `fdapp*`, or `tdapp*`
  projections;
- no pointwise function plus external naturality equations is accepted as a
  substitute; and
- unsupported coherence synthesis fails closed.

String parsing and browser promotion follow semantic TypeScript parity. They
are not architectural prerequisites and are not part of the first tranche.

## Authority And Recovery Order

Use these authorities in order:

1. `emdash2/emdash3_2.lp`;
2. `emdash2/emdash3_2_checks.lp`;
3. `emdash2/reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`;
4. `emdash2/reports/EMDASH_FOUNDATIONS.md`;
5. `emdash2/reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`;
6. this plan and its decision ledger;
7. the completed displayed-bracket plan and TypeScript handoff;
8. linked decision responses; and
9. raw Infinity Codex archives.

Follow root `AGENTS.md`, `emdash2/AGENTS.md` for every active-kernel action,
and
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md)
for long-running work and local checkpoints.

## Corrected Architectural Conclusion

### 1. Positive Sigma/product recursion is useful but insufficient

There is a valid positive fragment:

```text
K0 = K
K(i+1) = Sigma_cat(Ki,Ei).
```

Products represent independent sibling blocks, Sigma represents genuine
context extension, pullback represents weakening/substitution, and
projection/pairing represents variable occurrence. Repeating those
constructions is enough to carry object variables through a flat displayed
context. The implemented

```text
a : A;
b : B(a), c : C(a);
d : D(a,b,c)
```

consumer is evidence for this part.

That construction alone does not settle nested categorical abstraction.
Removing a hard-coded two/four-binding guard would graduate only an
uncurried positive context fragment.

### 2. Nested displayed abstraction is inherently mixed-variance

Once the body or target is itself a varying functor category, its source
varies contravariantly while its target varies covariantly. The active kernel
owns:

```text
Functor_catd [K]
  (A : Catd(Op_cat K))
  (B : Catd K)
  : Catd K
```

and:

```text
Hom_catd(Functor_catd A B,FF,GG)
  -> Transf_catd A B FF GG.
```

The canonical nested example is:

```text
k :^n K ; C[k] ⊢
  (z :^n Z ; E[k^-;z] ⊢ D[k;z]).
```

Morally:

```text
C : Catd K
E : K^op ⊢ Catd Z
D : K    ⊢ Catd Z.
```

The inner classifier is not a naive second covariant `Functord_cat`. It is
the family:

```text
Hom_catd
  (Const_catd K (Catd_cat Z))
  Ebar
  Dbar
```

where `Ebar` is a section of the pointwise opposite and `Dbar` a section of
the positive family. The full classifier is:

```text
Functord_cat C
  (Hom_catd
    (Const_catd K (Catd_cat Z))
    Ebar
    Dbar).
```

Therefore:

> Arbitrary context arity alone does not settle arbitrary nested binder
> usability.

Mixed variance is part of the arbitrary-depth architecture, not a detached
later feature.

### 3. `homd_int` is an architecture qualification, not decoration

The active kernel's representative target:

```text
homd_int(id_E)[x](u)
  : Π y :^n K^op,
      E[y^-] ⊢_[y]
      (Hom_K(x,y)^op ⊢ Cat)
```

combines:

- natural variation over `K^op`;
- a contravariant displayed source;
- a displayed functor category;
- an ordinary functor category over an opposite Hom category; and
- the internal projection ladder leading through `Transf_catd` and higher
  cells.

The `homd_int(FF)` owner intentionally retains the displayed-functor argument
so negative and positive action remain inside one internal owner. The
TypeScript graduation must eventually demonstrate that a nested
mixed-variance result can be consumed by `homd_int` or an equivalent
next-Hom projection. Merely serializing the outer object expression is not
enough.

### 4. No separate arrow-only binder is required

The phrase “explicit arrow/cell binders” is rejected as a description of the
ordinary categorical usability requirement.

For:

```text
λ^f x : A. body
```

`x` is the object coordinate of the internal categorical variable. The
abstraction constructs a genuine:

```text
F : Functor_cat A B.
```

The same `F` is then applicable through typed projections:

```text
x : Obj A       -> fapp0 F x
p : Hom A x y   -> fapp1 F p.
```

Arrow action is generated by the abstraction. It is not obtained by
separately binding an arrow variable. The same principle applies to `^fd`:
the result is a genuine `Functord`, whose action on base arrows and fibre
arrows belongs to that internal package.

The elaborator's `cellLevel` is an application/classification axis. It must
not be turned into one binder mode per dimension.

### 5. Modes and polarity are distinct but jointly lowered

- `^f` constructs an ordinary functor.
- `^n` constructs a section or naturally indexed term.
- `^fd` constructs a displayed functor and already combines a hidden
  `k :^n K` base with a fibrewise `a :^f E[k]` input.
- `^nd` constructs a displayed transformation from internally coherent
  components.

Polarity is derived from the expected classifier:

- `A` is positive;
- `Op_cat A` is negative;
- a pointwise opposite displayed family is represented through `Op_catd`;
- a family over an opposite base is represented as `Catd(Op_cat K)`; and
- mixed families are constructed by `Functor_catd`, `Hom_catd`, and
  `Transf_catd`.

An unchecked user “contravariant” flag is not the semantic owner. Surface
notation may expose orientation, but the expected type and explicit opposite
constructors determine lowering.

## Current TypeScript Status

The TypeScript implementation already contains:

- an outer dependent LF with scoped dependent Pi/lambda/application,
  bidirectional checking, metas, rewriting, and proof-time unification;
- backend-neutral explicit Core;
- generic declaration/runtime/proof transfer engines;
- opposite category and pointwise opposite displayed-family ingredients;
- the stable constant-domain `Functor_catd` evaluator;
- contravariant category families and dependent targets;
- generic products, Sigma totals, pullback/reindexing, projections, pairing,
  and one genuine dependency edge;
- direct bounded `^fd` and `^nd` consumers;
- transferred `homd_int` and next-Hom action infrastructure; and
- type-directed ordinary/displayed/higher application.

The missing integration is concrete:

- `Hom_catd` and `Transf_catd` are active in Lambdapi but absent from the
  TypeScript declaration/runtime environment;
- the displayed contextual compiler records only covariant brackets;
- arbitrary mixed-domain evaluation is not implemented;
- an applied displayed-functor subject must still be closed in the bounded
  bracket profile;
- `compileDisplayedContextual` explicitly rejects a nested
  `categorical-abstraction`; and
- the demonstrated dependent presentation is still hard-coded to selected
  binding shapes.

No evidence suggests a Lambdapi kernel redesign. The incomplete boundary is
the TypeScript classifier-directed abstraction interface.

## Selected Architecture

The implementation has two interacting components. They may share code where
natural, but no requirement is imposed that every ordinary and dependent case
use one algorithm.

### A. Generic contextual substitution and presentation

This component owns:

- independent sibling products;
- genuine Sigma extensions;
- pullback weakening and substitution;
- projection/pairing for variables;
- repeated lifting through arbitrary finite dependency graphs; and
- a typed locally nameless contextual representation.

Its output is an explicit context presentation and the projections needed by
the body. It does not decide by itself whether the result is a functor,
section, displayed functor, or displayed transfor.

### B. Classifier-directed abstraction algebra

This component selects an introduction law from the expected classifier:

| Expected classifier | Introduction/lowering route |
| --- | --- |
| `Functor_cat A B` | ordinary functorial bracket/curry |
| `Pi_cat D` | natural section abstraction |
| `Functord_cat E D` | displayed functorial bracket |
| `Transfd_cat FF GG` | displayed transformation bracket |
| varying functor family | `Functor_catd`, respecting the opposite source base |
| hom family between varying endpoints | `Hom_catd` |
| hom in a varying functor family | runtime fold to `Transf_catd` |
| internal dependent hom | `homd_int` and its projection ladder |

The contextual engine supplies free-variable projections. The abstraction
algebra determines how those projections occur in positive and negative
positions. Both components emit only internal kernel owners.

## Required Qualification Evidence

Arbitrary finite displayed depth may be claimed only after both witnesses
below pass.

### Positive deep telescope

```text
a : A;
b : B(a), c : C(a);
d : D(a,b,c);
e : E(a,b,c,d);
...
```

It must cover object action and nested-Sigma arrow action, not only object
projection.

### Canonical mixed-mode nested target

```text
k :^n K ; C[k] ⊢
  (z :^n Z ; E[k^-;z] ⊢ D[k;z])
```

It must lower to the exact `Functord_cat`/`Hom_catd` classifier and verify:

- the negative occurrence is represented by `Op_cat`/`Op_catd`;
- `Hom_catd(Functor_catd A B,FF,GG)` reduces to `Transf_catd A B FF GG`;
- outer base-arrow action reaches the inner construction internally;
- a `homd_int` projection or equivalent next-Hom consumer accepts the
  result;
- no external naturality or variance evidence appears; and
- flattened and nested/curry presentations are compared only at the
  kernel-selected runtime or proof-time boundary.

Runtime equality must not be invented where the active kernel supplies only
proof-time compatibility.

## Scope Boundaries

This plan does not require immediate synthesis of a coherent `Transfd` from
every imaginable pointwise `λ^nd` body. It distinguishes:

1. making `Transf_catd`, `homd_int`, and higher action available wherever
   nested classifier formation requires them; from
2. recursively synthesizing every general `^nd` body.

The first is mandatory for mixed-depth architecture. The second remains
fail-closed outside a qualified family of coherence-owning constructors and
expands consumer by consumer.

Also outside the first tranche:

- a string parser or notation consolidation;
- browser promotion;
- arbitrary mixed-domain evaluation beyond the selected witness;
- groupoidal specialization/closure;
- whole-library Lambdapi transfer;
- a new LF semantic feature;
- a new Lambdapi mathematical owner or rule; and
- remote Git operations, integration, publication, or release.

## Implementation Ledger

| Slice | Status | Dependency | Exact purpose |
| --- | --- | --- | --- |
| `MIXED-NEST-0A` | implemented and focused-green; local checkpoint pending | completed displayed-ND higher profile and approved architecture | Two existing opaque signatures and four existing runtime rules compile generically in isolated `fibred-displayed-mixed-nest-1`; seven typed constructors build/check the canonical nested classifier and prove its `Transf_catd` fold. The independent constant-`Cat` fold is deferred at its measured nested proof-conversion seam. Zero Lambdapi semantic delta. |
| `MIXED-NEST-1A` | pending | green `MIXED-NEST-0A` | Add the first recursive nested `categorical-abstraction` lowering selected by the expected `Functord_cat(...,Hom_catd(...))` classifier. Preserve callback-once locally nameless evidence and fail closed outside the qualified shape. |
| `MIXED-NEST-ACTION-1B` | pending | green `MIXED-NEST-1A` | Exercise base-arrow action through the inner mixed classifier and one `homd_int`/next-Hom consumer. Add no constructor-specific generic functoriality/naturality rules. |
| `DISPLAYED-TELESCOPE-GENERIC-1` | pending | mixed nested action plus current positive compiler | Replace selected presentation arities with a dependency-plan fold over arbitrary finite products/Sigma/pullbacks while retaining explicit classifier-directed result lowering. |
| `DISPLAYED-MIXED-GRADUATE-1` | pending | generic positive and mixed witnesses | Freeze the exact arbitrary-finite-depth claim, negatives, performance boundary, and conformance evidence. Do not silently graduate unrestricted `^nd`. |
| `MIXED-CONST-FOLD-0B` | deferred; not on the usability critical path | a concrete consumer or generic proof-conversion qualification | Transfer the active constant-`Cat` Hom fold only through a generic proof-aware nested conversion path. Do not add mirrors, coercions, owner-specific checker logic, or an external oracle. |
| `TEXT-PARITY-MIXED-1` | pending | semantic graduation | Bring the text adapter to parity with the graduated mathematical API and fail closed outside it. |
| `DISPLAYED-ND-CONSUMERS-N` | future, consumer-led | concrete requested coherent bodies | Expand recursively supported `^nd` body constructors while preserving internal coherence ownership. |

## Frozen `MIXED-NEST-0A` Boundary

The first slice is deliberately smaller than the final nested binder.

It may:

- transfer the existing opaque `Hom_catd` and `Transf_catd` signatures;
- transfer exactly their two fibre-projection rules, the
  `Hom_catd(Functor_catd(...))` family fold, and the existing `Op_catd` fibre
  projection required to type the negative endpoint;
- reuse the existing `Functor_catd`, `Op_catd`, `Op_func`, `Pi_cat`,
  `piapp0`, `Functord_cat`, `Transf_cat`, and generic action owners;
- add one isolated root-only successor profile;
- add typed constructors for:
  - `Catd_cat Z`,
  - `Op_cat K`,
  - a contravariant section of `Op_catd E`,
  - a general mixed `Functor_catd A B`,
  - `Hom_catd E X Y`,
  - and the rich `Functord_cat C H` category;
- construct the exact canonical nested classifier; and
- demonstrate the `Hom_catd(Functor_catd(...))` to `Transf_catd` runtime
  fold in the TypeScript kernel.

It may not:

- edit `emdash3_2.lp`;
- add a new mathematical owner or computation;
- claim that constructing the classifier is already recursive binder
  elaboration;
- add a second AST, checker, evaluator, or external coherence witness;
- weaken existing fail-closed behavior;
- alter earlier profiles; or
- promote the new profile to the browser/text product.

If an exact active declaration or rule fails generic subject checking, stop
and record the minimal dependency/refinement gap. Do not patch the checker or
duplicate a semantic body merely to force the slice through.

## Validation Policy

Use proportional gates:

1. focused transfer and canonical-classifier tests;
2. focused negative/profile-isolation tests;
3. root typecheck/lint;
4. the bounded active-kernel check when active names/computation are relied
   upon;
5. focused Lambdapi conformance only for the promoted mixed judgments; and
6. the aggregate root suite only at a coherent semantic checkpoint, not
   after documentation-only or small follow-up edits.

Do not repeatedly run the repository's long aggregate gate. Record and reuse
an unchanged green checkpoint when the changed surface cannot affect it.

## `MIXED-NEST-0A` Implementation Result

The first slice is implemented without an active-kernel edit.

The generic transfer adds:

- opaque existing `Hom_catd` and `Transf_catd` declarations;
- the existing `Op_catd` fibre projection needed by negative sections;
- the existing `Hom_catd` and `Transf_catd` fibre projections; and
- the existing
  `Hom_catd(Functor_catd(A,B),FF,GG) -> Transf_catd(A,B,FF,GG)`
  fold.

All four rules report `typescript-checked`. No external subject-reduction
oracle, proof-time mirror, intrinsic owner, or owner-specific checker path is
used.

The isolated root profile adds seven typed direct-TypeScript operations:

- `oppositeCategory`;
- `displayedCategoryCategory`;
- `oppositeDisplayedFamily`;
- `mixedDisplayedFunctorFamily`;
- `mixedDisplayedHomFamily`;
- `mixedDisplayedTransforFamily`; and
- `displayedFunctorCategory`.

Together with existing `constantDisplayedFamily`, `section`, and
`displayedFunctor`, they construct and check:

```text
Functord_cat C
  (Hom_catd
    (Const_catd K (Catd_cat Z))
    Ebar
    Dbar).
```

A second witness constructs `Functor_catd(A,B)`, its negative/positive
sections `FF` and `GG`, and observes the exact mixed-family runtime fold to
`Transf_catd(A,B,FF,GG)`.

This is classifier qualification, not yet recursive lowering of a nested
surface abstraction. `compileDisplayedContextual` remains fail-closed on the
nested abstraction node until `MIXED-NEST-1A`.

Focused validation:

- 4/4 generic transfer tests pass;
- 3/3 canonical classifier/fold/profile-isolation tests pass;
- 6/6 syntax-parity inventory tests pass after classifying the seven new
  constructors as the already-deferred typed-resolver seam;
- affected ESLint passes;
- root TypeScript typecheck passes; and
- the pre-edit bounded active-kernel `make check` passes.

The first cold inherited compilation took approximately 84-96 seconds; the
three profile tests took 104.3 seconds inside their test process. Compilation
is cached within a process. No performance redesign is included in this
semantic tranche.

The pre-edit root `check:ts` aggregate reached its known long CPU-bound phase
and then failed after approximately 25 minutes in the unrelated
`v3_2_release_completion_tests.ts` README assertion: current `README.md`
does not contain the older `release-ready exact profile` phrase. Neither file
is changed by this tranche. The failure is recorded as baseline evidence and
the long aggregate is not repeated here.

## Git And Approval Boundary

Work in the existing dedicated
`goal/typescript-elaborator-v3.2` worktree/branch. The user has authorized
bounded local checkpoint commits for coherent green tranches and has
delegated approval of a presented bounded proposal when no immediate human
response arrives, always with human supersession.

Before each checkpoint:

- synchronize this ledger and affected handoff;
- inspect staged and unstaged diffs separately;
- exclude unrelated files;
- run `git diff --cached --check`; and
- record proportional validation.

This authorizes no push, PR, merge to `main`, publication, release, amend,
rebase, reset, squash, history rewrite, branch/worktree removal, or unrelated
cleanup.

## Persistent `/goal` Launch Prompt

```text
Continue implementing
docs/TYPESCRIPT_ELABORATOR_V3_2_MIXED_MODE_DISPLAYED_TELESCOPE_PLAN.md and
treat its Persistent /goal Launch Prompt as part of the objective.

Recover actual worktrees, branch ancestry, staged and unstaged changes,
active authority, completed displayed-bracket/ND-higher evidence, this
plan's living ledger, and linked decisions. Follow root AGENTS.md,
emdash2/AGENTS.md, and docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md.

Advance the next dependency-ready slice toward genuinely usable arbitrary
finite displayed telescopes with classifier-directed mixed variance.
Prioritize the canonical nested
Functord_cat/Hom_catd/Transf_catd/homd_int witness before generalizing
presentation arity. Preserve the distinction between contextual
Sigma/product/pullback recursion and classifier-directed abstraction. Every
binder must construct an internal action package; never introduce external
naturality or variance evidence, and fail closed for unsupported coherence.

Treat the active Lambdapi v3.2 kernel as mathematical authority. A missing
TypeScript route is not permission for a new kernel rule. Audit existing
owners and dependencies first, use generic transfer/checking engines, and
make any genuine Lambdapi delta a separate measured proposal under the
nested SOP.

Keep string parsing, browser promotion, groupoidal closure, bulk
whole-library transfer, and unrestricted general :^nd outside this goal
until their dependency rows become ready. Use proportional focused gates;
do not repeat long aggregate validation for documentation-only or
semantically irrelevant changes.

The user authorizes bounded local checkpoint commits in the existing
goal/typescript-elaborator-v3.2 branch after a coherent tranche is green,
the living ledgers are synchronized, the exact staged diff is clean, and
unrelated work is excluded. If a newly frozen bounded proposal receives no
immediate human response, the standing unattended delegation may record a
separate approval/review with human supersession. No push, PR, merge,
publication, release, destructive history operation, branch/worktree
removal, or unrelated cleanup is authorized.

Continue through dependency-ready rows with minimal human supervision,
updating this plan whenever evidence changes the architecture. Stop for a
new mathematical owner/rule, a broader semantic claim, an unresolved
authority conflict, or an operation outside the stated Git boundary.
```

## Decision Ledger

- **2026-07-31 — mixed-mode correction approved.** The user agreed that the
  earlier separation of arbitrary depth from variance was too sharp and that
  “explicit arrow/cell binder” was misleading. Mixed variance and the
  complete internal action package are now graduation requirements.
- **2026-07-31 — dedicated successor selected.** The completed
  displayed-bracket plan remains historical authority for its bounded
  envelope. This file owns the mixed-mode/arbitrary-depth continuation.
- **2026-07-31 — `MIXED-NEST-0A` selected first.** The smallest executable
  dependency-ready slice is the existing-authority `Hom_catd`/`Transf_catd`
  transfer plus canonical typed classifier witness. It is intentionally not
  labeled completed nested abstraction.
- **2026-07-31 — negative-fibre dependency measured.** Generic subject
  checking found that TypeScript had the active `Op_catd` signature and
  involution but not its active fibre projection. `MIXED-NEST-0A` therefore
  includes that exact existing rule as a prerequisite, for two signatures
  and four transferred runtime rules total, with zero Lambdapi delta.
- **2026-07-31 — constant-`Cat` fold deferred at a generic seam.** The active
  `Hom_catd(Const_catd K Cat_cat,X,Y)` fold uses the proof-time
  `Pi_cat(Const_catd K A) ≡ Functor_cat K A` comparison inside the
  `Op_func(X)` argument. The generic runtime compiler can proof-check a whole
  subject comparison but does not use proof conversion while inferring that
  nested argument. This fold is not required by the canonical nested
  classifier or the selected `Transf_catd` witness, so `MIXED-NEST-0A`
  records it as a later generic proof-conversion qualification rather than
  adding a mirror, coercion, checker branch, or external oracle.
- **2026-07-31 — `MIXED-NEST-0A` implemented and focused-green.** The exact
  two-signature/four-rule generic closure, isolated profile, seven typed
  constructors, canonical nested classifier, and `Transf_catd` fold pass
  focused validation. The result deliberately leaves the recursive nested
  abstraction node to `MIXED-NEST-1A`.
