# TypeScript/emdash Affine Localization And Čech Delegation Plan

Date: 2026-08-31

Plan-ID: `TS-EMDASH-AFFINE-LOCALIZATION-CECH-DELEGATION`

Status: active living plan on a dedicated branch/worktree; architecture
reviewed, exact owner audit and implementation pending.

Baseline: `ae85a4bf02c0cea9fc68eda8f0b984172fd072e0`

Branch: `goal/affine-localization-cech-delegation-v3.2`

Worktree: `/home/user1/emdash1-affine-localization-cech-delegation-v1`

Decision-Response-Evidence:
`infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a058c9-907c-7830-8a83-8a1806588b80`

## Purpose

This plan governs the next proof–CAS usability layer: turn a computational
finite affine cover into selected formal localizations, basic-open charts,
overlap factors, and the existing packed formal Čech presentation without
requiring the caller to handwrite every algebraic law, universal-property
assumption, or face-unit term.

The completed predecessor already provides:

- exact named root goals;
- typed algebra operations and whole results;
- canonical formal/computational realizations;
- observation, checked-plan, and explicit trusted-assumption adoption;
- replay-safe direct TypeScript workflows;
- unimodular Zariski-cover law delegation; and
- ideal-membership quotient-equality delegation.

The remaining affine path is:

```text
computational affine cover
  -> adopted unimodular cover law                 [already implemented]
  -> compute each selected principal localization
  -> adopt its exact inverse equation
  -> explicitly trust its presentation semantics
  -> construct existing formal localization and chart
  -> derive face-denominator units formally
  -> derive overlap maps from localization contractibility
  -> construct the existing whole formal Cech presentation
  -> emit one durable computed-assumption source and formal artifact.
```

This goal may add narrowly selected proof-assistant mathematics when the
concrete affine/Čech consumer needs it. It does not organize the architecture
around proof certificates or require verification of the native CAS.

## Authority And Prerequisites

The immediate predecessor is
`docs/TYPESCRIPT_EMDASH_PROOF_CAS_DELEGATION_PLAN.md` at the baseline above.
Its operation/request/result/adoption/workflow boundaries remain fixed unless
this consumer supplies counterevidence.

Computational authorities include:

- `algebra_localization.ts` and
  `algebra_localization_reference_operations.ts`;
- `algebra_cech.ts` for ordered product simplices and face maps;
- the existing affine scheme, cover, tensor, quotient, polynomial, and
  presented-algebra owners; and
- the native algebra engine and computation graph.

Formal bridge authorities include:

- `algebra_formal_localization.ts`;
- `algebra_formal_overlap.ts`;
- `algebra_formal_cech.ts`;
- `algebra_formal_artifact.ts` and conformance emission; and
- the completed exact Zariski signature environment and adoption workspace
  foundations.

The mathematical authority is the active Lambdapi v3.2 one-way algebra chain,
especially:

- finite families and finite commutative-ring folds;
- `CommRingUnitEvidence` and its constructors/projections;
- localization properties and contractible factors;
- products of units and the projections from a unit product to each factor;
- iterated/product localization comparisons;
- finite Zariski cover families; and
- affine basic-open intersection comparisons.

Active source and the nested `emdash2/AGENTS.md` rule-design SOP outrank this
plan. Any new formal definition or theorem must be owner-positioned, tested
with positive and noncollapse consumers, and validated under the bounded
Lambdapi workflow. A missing TypeScript bridge is not authority for a runtime
rewrite.

The root `AGENTS.md`, elaborator handoff, and
`docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md` govern TypeScript, worktree,
validation, and checkpoint behavior.

`main` was fast-forwarded only to the completed proof–CAS baseline before this
branch was created. Orthogonal path-cubical and strictness-migration work
remains excluded.

## Evidence Classification

Every formal datum introduced by this goal belongs to exactly one class.

### Computed equation

The native engine constructs explicit algebraic data and validates a concrete
equation. Initial examples include:

```text
image(f) * inverse = 1
```

for an adjoined-inverse localization. The equation may become a formal claim
through the existing explicit adoption boundary.

### Trusted presentation semantics

The computational presentation strongly suggests, but does not itself prove
inside emdash Core, a universal semantic property. The principal example is:

```text
IsCommRingLocalizationAt(R,f,L,iota).
```

The native CAS constructs `L` and checks the inverse relation; it does not
compute contractibility of every future factorization space. Adoption of the
whole universal property must therefore be explicitly labeled
`trusted-presentation-semantics`, never `computed-equation` or checked proof.

### Derived formally

Once selected formal unit/localization data exists, consequences should be
constructed by the proof assistant whenever current mathematics suffices.
Targets include:

- unit evidence for factors of an invertible product;
- face-denominator units in product localizations;
- universal localization factor maps and agreements;
- overlap restriction maps; and
- whole formal Čech packaging.

No caller-supplied manual commuting triangle or face map is accepted.

## Current Gaps

### Inverse-law target circularity

`affineFormalInverseLawType(realization)` currently calls the unit-term
builder, which requires the inverse law being targeted. It must be refactored
to build the multiplication-equals-one type directly from the formal map,
localized element, and selected inverse while keeping formal unit/localization
constructors strict.

### Universal semantics remains manually supplied

The existing localization realization accepts a `universalTerm` but neither
constructs nor classifies its origin. The new adapter should target the whole
`IsCommRingLocalizationAt` property, explicitly adopt it as trusted
presentation semantics, and project the universal field through the existing
formal helper.

### Face units remain a manual evidence matrix

`buildAffineFormalCechOverlapTerms` derives whole factor maps and agreements
but currently accepts one prewritten unit term per face. The exact owner audit
must determine how much can be derived from existing product-unit theorems.

For binary products the active library already supplies left/right unit
projections. For arbitrary finite simplices the likely missing formal layer is
a finite multiplicative fold plus split/deletion comparison showing that the
lower-dimensional product is a factor of the total product. New mathematics
is selected only if this concrete consumer cannot use an existing theorem.

### Adoption is not yet durable source

Trusted adoption presently extends an immutable in-memory LF environment and
produces a canonical artifact. The live Zariski test reconstructs a source-
spanned declaration for emission. A cover with many localization assumptions
needs a first-class computed-assumption source/workspace with deterministic
ordering, spans, replay, and emission.

### General contextual goals are unnecessary initially

Every selected cover, localization, and unit claim can be represented as a
closed declaration-scope root goal. The first adoption workspace should
compose a finite sequence of those goals. Arbitrary nested/local goal
abstraction remains consumer-gated.

## Proposed Formal Mathematics

The audit should first attempt to reuse the active localization-comparison
owners. If a finite generalization is needed, the candidate layer is:

```text
comm_ring_finite_product R 0 () = 1
comm_ring_finite_product R (succ n) (x,xs)
  = x * comm_ring_finite_product R n xs
```

together with only the paths needed by the Čech consumer:

- preservation by structured ring maps;
- decomposition around one selected/deleted factor; and
- unit evidence for the product of the remaining family when the complete
  product is a unit.

The representation should use the current right-associated `FiniteFamily`
and Nat recursion. It should not introduce `Fin`, lists, permutations,
quotient syntax, or a second family representation merely for convenience.

Runtime computation should remain transparent Nat recursion. Theorems about
reassociation, commutation, and units are equality paths or ordinary
constructors; no rewrite/unification rule is expected unless an exact
projected consumer proves one necessary under the nested SOP.

## Computed-Assumption Source Workspace

The first durable source concept should be narrowly shaped as:

```text
ComputedAssumptionModule {
  module/source identity
  ordered exact Core declarations
  exact originating goal identities
  request/result/adoption receipts
  evidence classification per declaration
  deterministic virtual source spans
  explicit dependencies
}
```

It should:

- accumulate several independently adopted closed claims;
- require a separate explicit decision for every trusted declaration;
- preserve the distinction between computed equation and trusted presentation
  semantics;
- compile to the ordinary immutable LF declaration environment;
- emit deterministically through existing Core/Lambdapi serializers;
- replay against exact current requests/results;
- reject duplicates, reordering, dependency drift, missing decisions, stale
  results, and forged classification; and
- never relabel an opaque assumption as a checked theorem body.

This source is not a general Core-to-transfer-expression reifier and not a
new kernel declaration representation. It is a consumer-specific source
facade over exact Core types and existing checked environment extension.

## Localization Delegation

For one already-selected computational principal localization and formal
source/target reifiers, define a parent-aware realization retaining:

- source algebra and formal ring;
- localized quotient element and formal term;
- computed target presentation and formal target ring;
- canonical structure map;
- computational inverse and its formal term;
- exact inverse-law target;
- exact whole localization-property target; and
- classification of each prospective adoption.

The localization operation is the existing:

```text
algebra.principal-localization.compute
  : quotient element -> whole principal localization.
```

The adapter claims the inverse equation only when the exact output agrees
with the selected whole localization. A distinct semantics adapter may expose
the whole universal-property target from the same exact result, but it must
label the claim `trusted-presentation-semantics`.

After separate adoption, reconstruct an ordinary explicit-data formal
localization realization from the two actual Core references. The original
trusted/no-evidence realization remains unchanged.

## Whole Affine Cover And Čech Consumer

The first consumer is the binary affine-line cover `D(x),D(1-x)`. The second
is the ternary affine-plane cover `D(x),D(y),D(1-x-y)` through its retained
two-skeleton.

For every cover generator and simplex product:

1. run or compare the selected localization operation;
2. adopt the inverse equation as a computed equation;
3. explicitly adopt the universal property as trusted presentation semantics;
4. build the existing formal localization and basic-open chart;
5. derive face-unit evidence formally from product-unit structure;
6. let localization contractibility construct face factors, maps, and
   agreements; and
7. build the existing packed degreewise formal Čech presentation and artifact.

Completion must not accept caller-supplied face maps, commuting triangles, or
unclassified law arrays. The final formal artifact should state exactly which
opaque assumptions remain and which data was derived.

The formal Čech object still makes no claim of cosimplicial identities,
differentials, `d²=0`, exactness, sheaf cohomology, or descent. Those require a
later formal module/complex layer.

## Proposed Implementation Sequence

### 1. Exact owner and feasibility audit

Map every computational localization/Čech field to its formal owner, locate
the inverse-law circularity, classify universal-property semantics, and probe
the smallest binary/ternary face-unit derivation. Decide whether finite
product mathematics is needed and record the exact formal delta before
editing Lambdapi.

### 2. Computed-assumption source workspace

Implement deterministic exact-Core assumption modules, sequential environment
extension, per-declaration classification and decisions, canonical
serialization, replay/freshness, and source-spanned Lambdapi emission. Test a
small synthetic pair before consuming localization data.

### 3. Localization inverse equation

Refactor the inverse-law target to be noncircular. Implement the parent-aware
localization adapter, positive selected-output agreement, graph agreement,
negative/foreign cases, explicit equation adoption, and formal unit
construction.

### 4. Localization universal property

Implement the separately classified presentation-semantics adapter. Explicit
trust produces the whole property term; its existing projection supplies the
universal factorization field. Reconstruct and typecheck the existing whole
formal localization/chart.

### 5. Product/face-unit formal layer

Reuse existing binary/product-localization owners where possible. If the
ternary consumer needs a finite generalization, implement only the audited
finite product, split/deletion path, and factor-unit theorem under the full
Lambdapi SOP. Derive face units without separate trusted assumptions.

### 6. Binary whole-cover consumer

Build the selected formal cover family, both charts, overlap localization,
derived face factors/maps/agreements, packed formal Čech presentation, and
durable assumption source from the binary computational cover.

### 7. Ternary two-skeleton consumer

Scale the same architecture to all three generators, three pairwise products,
the triple product, and every ordered face. No arity-specific manual evidence
table or handwritten map is permitted.

### 8. Replay and conformance

Require deterministic direct/graph results, exact adoption replay, stable
assumption-module bytes, binary/ternary portable artifacts, and focused live
Lambdapi checking. Run only proportional TypeScript and formal gates; classify
the already-known unrelated aggregate source-pin failures rather than
rechecking the repository for reassurance.

## Implementation Ledger

| Row | Status | Dependency | Deliverable and acceptance boundary |
| --- | --- | --- | --- |
| `ALC-PLAN-0` | complete; plan checkpoint pending | completed proof–CAS delegation at `ae85a4b` and reviewed continuation | living plan, isolated branch/worktree, exact baseline, evidence classes, staged rows, validation, and Git limits |
| `ALC-AUDIT-1A` | pending | `ALC-PLAN-0` | exact computational/formal owner map, inverse circularity, universal-property classification, binary/ternary face-unit feasibility, selected formal delta |
| `ALC-SOURCE-2A` | pending | `ALC-AUDIT-1A` | exact-Core computed-assumption source/workspace, sequential adoption, per-claim classification, source spans, replay and emission |
| `ALC-INVERSE-3A` | pending | `ALC-SOURCE-2A` | noncircular inverse target, selected localization adapter, computed-equation adoption, formal unit, direct/graph agreement and negatives |
| `ALC-UNIVERSAL-3B` | pending | `ALC-INVERSE-3A` | explicitly trusted presentation-semantics adoption, whole property projection, reconstructed formal localization and chart |
| `ALC-FINITE-PRODUCT-4A` | pending or audit-rejected | `ALC-AUDIT-1A` | smallest necessary finite product/deletion/unit formal mathematics, or durable proof that existing owners suffice |
| `ALC-COVER-5A` | pending | preceding localization and face-unit rows | complete binary formal cover/localizations/overlap/Čech artifact with no manual face evidence |
| `ALC-CECH-6A` | pending | `ALC-COVER-5A` | ternary two-skeleton through the same uniform architecture |
| `ALC-CONFORMANCE-7A` | pending | all active rows | final portable artifacts, exact replay, graph agreement, source emission, focused live Lambdapi acceptance, proportional boundary audit |

Rows may be split into bounded lettered subtranches. A row completes only
after implementation, positive and negative consumers, proportional checks,
synchronized decisions/results, and a local checkpoint.

## Initial Decision Ledger

| Decision | Status | Rationale |
| --- | --- | --- |
| `D-ALC-001` | accepted | The immediate continuation is affine localization/Čech delegation, not a disconnected new CAS algorithm or premature full module theory. |
| `D-ALC-002` | accepted | Inverse equations are computed equations; localization universal properties are explicitly trusted presentation semantics unless formally proved. |
| `D-ALC-003` | accepted | Face units and overlap maps should be derived formally from product/localization mathematics rather than trusted independently whenever feasible. |
| `D-ALC-004` | accepted | New proof-assistant mathematics is consumer-driven and limited to the exact finite product/unit gap established by the owner audit. |
| `D-ALC-005` | accepted | The existing right-associated `FiniteFamily` and Nat recursion remain the only finite-family representation. |
| `D-ALC-006` | accepted | A computed-assumption source carries exact Core and per-declaration classifications; it does not introduce a general Core-to-transfer-AST reifier. |
| `D-ALC-007` | accepted | Every trusted declaration requires its own explicit decision; no bulk Boolean silently approves a cover. |
| `D-ALC-008` | accepted | Closed declaration-scope root goals suffice for the first finite adoption workspace; arbitrary contextual goals remain deferred. |
| `D-ALC-009` | accepted | No caller-supplied face map, commuting triangle, or unclassified evidence matrix is accepted. |
| `D-ALC-010` | accepted | Binary and ternary covers are the acceptance shapes; the latter must use one uniform architecture rather than arity-specific handwritten code. |
| `D-ALC-011` | accepted | The formal Čech result stops before differentials, `d²`, exactness, descent, and cohomology. |
| `D-ALC-012` | accepted | Formal finite free modules/matrices/presentations are the recommended following goal, not silently included here. |
| `D-ALC-013` | accepted | Local validated checkpoint commits are permitted on this dedicated branch; push, merge, publication, release, history rewriting, and cleanup are not. |
| `D-ALC-014` | accepted | `main` was fast-forwarded only through the completed proof–CAS baseline; orthogonal path-cubical/strictness work remains excluded. |

## Validation Policy

Use proportional affected checks:

- documentation diff/link hygiene for plan/audit rows;
- workspace check, focused tests, root typecheck, and affected-file lint for
  TypeScript rows;
- exact replay and deterministic serialization tests for assumption sources;
- owner-position probes, positive/noncollapse consumers, warning comparison,
  LHS audit, catalog/health synchronization, and bounded target/CI gates for
  any Lambdapi semantic change;
- every Lambdapi invocation bounded to at most 90 seconds per target;
- focused live binary/ternary probes after final Core emission; and
- no `check:all`, book, print, package, release, or repeated full TypeScript
  aggregate merely for reassurance.

The predecessor's one full TypeScript aggregate is recent evidence: all new
proof–CAS suites passed, while unrelated historical digest/position pins were
already stale on clean `main`. A later shared-boundary run, if required, must
be classified against that known baseline rather than reported as a new
feature failure.

## Git Authorization And Checkpoints

The user authorizes this dedicated branch/worktree and continuation according
to the living plan, including local validated checkpoint commits as bounded
rows complete. Every checkpoint requires synchronized plan decisions/results,
focused green evidence, path-scoped staging, exact staged-diff review, and
`git diff --cached --check`.

This authorization does not include push, merge, rebase, amend, reset,
history rewriting, publication, release, PR creation, branch deletion,
worktree removal, or integration of orthogonal branches.

## Non-Goals

- proving the native CAS correct;
- mislabeling universal-property trust as computed or checked proof;
- a formal concrete polynomial quotient implementation;
- a full semantic module category, quotient module, chain complex, homology,
  Čech differential, or cohomology;
- arbitrary nested/local goal delegation;
- a general Core-to-transfer-expression or arbitrary AST reifier;
- a mutable global tactic/realization registry;
- caller-written face maps or commuting triangles;
- new runtime rewrites without an owner-position consumer and full SOP;
- parser, CLI, hosted service, or package publication; or
- push, merge, release, or worktree cleanup.

## Completion Boundary

This goal is complete when every active ledger row is implemented, rejected
with durable evidence, or explicitly deferred behind a concrete prerequisite;
the binary and ternary computational covers produce deterministic formal cover
families, selected localizations/charts, derived overlap maps, and packed
formal Čech artifacts; every remaining opaque assumption is source-persistent
and correctly classified; no face map/triangle/unit array is handwritten;
replay and live Lambdapi conformance pass; and all proportional affected gates
are synchronized and checkpointed.

Completion does not require formal module/complex/cohomology theory, CAS
verification, a proof certificate, a parser, public package changes, a
repository aggregate, integration into `main`, or publication.

## Persistent `/goal` Launch Prompt

Work in `/home/user1/emdash1-affine-localization-cech-delegation-v1` on
`goal/affine-localization-cech-delegation-v3.2`. Implement the affine
localization/Čech proof–CAS delegation objective with every owner discovery,
formal-product decision, evidence classification, assumption-source API,
adapter design, binary/ternary consumer, validation result, checkpoint, and
completion condition delegated to this living plan. Preserve baseline
`ae85a4b`, exclude orthogonal path-cubical/strictness work, and re-read current
source/SOP/plan on every continuation. Keep computed equations, trusted
presentation semantics, and formally derived consequences distinct. Reuse
the completed proof–CAS workflow and existing formal localization/overlap/
Čech owners. Add only consumer-proven formal mathematics under the full
Lambdapi SOP; accept no handwritten face maps or commuting triangles. Use
proportional affected tests and bounded formal checks, make only authorized
local validated checkpoint commits, and do not push, merge, publish, release,
rewrite history, remove worktrees, or broaden unrelated formal/kernel theory.
