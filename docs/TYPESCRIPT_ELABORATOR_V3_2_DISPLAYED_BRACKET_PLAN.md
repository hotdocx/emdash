# TypeScript Elaborator v3.2 General Displayed Bracket Plan

## Status

This is the living successor plan to
[`TYPESCRIPT_ELABORATOR_V3_2_FIBRED_CONTEXT_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_FIBRED_CONTEXT_PLAN.md).
The predecessor is complete at its qualified demonstrated-authority boundary:
H-DTTLF-USABILITY-FIBRED-GRADUATE/D-DTTLF-USABILITY-008 is approved under
the user's delegated unattended authority, with a separate immutable review,
human supersession, and no automatic successor authorization.

This plan addresses the highest-priority withheld usability boundary:
generalizing direct displayed-functor abstraction from a rigid one-slot body
recognizer into a first-order contextual compiler. It does not resume
Lambdapi parsing or bulk transfer, promote a browser profile, assume a
total-category pullback/equivalence, complete groupoidal DTT, or claim
general displayed-transfor coherence.

The exact first decision is frozen in
`src/v3_2/categorical_displayed_bracket_proposal.ts`.
H-DTTLF-USABILITY-DISPLAYED-BRACKET-01/D-DTTLF-USABILITY-009 remains
pending. The proposal is non-self-authorizing and installs no semantic
authority.

## Authority And Relationship To The Completed Architecture

The active mathematical authority remains the Lambdapi v3.2 development
under `emdash2/`, in the order specified by `emdash2/AGENTS.md`. The
TypeScript side compiles a direct typed surface to backend-neutral explicit
Core and evaluates/checks it through the generic TypeScript LF machinery.
Lambdapi remains the conformance oracle and optional deterministic emission
backend.

D-DTTLF-USABILITY-008 settles the following architecture only within its
demonstrated envelope:

- outer dependent LF and locally nameless explicit Core;
- one-shot typed TypeScript callback reification;
- dependency-aware finite contextual planning;
- generic declaration/runtime/proof transfer engines;
- direct/proof category-presentation separation; and
- consumer-led owner qualification.

It deliberately withholds a general displayed bracket. This plan consumes
that settled infrastructure without changing its trust boundary.

There is no special requirement that ordinary and displayed lowering use the
same algorithm or deliberately different algorithms. Shared scoping,
locally nameless slots, dependency analysis, usage accounting, provenance,
and first-order IR are reused because they fit naturally. Displayed
projection, pairing, composition, reindexing, and coherence use their own
qualified categorical owners and rules.

## Problem Statement

The current direct form

```text
λ a :^fd E. body
```

is real but bounded. `displayedFunctorLambda` currently constructs a hidden
base/fibre telescope

```text
k :^n K; a :^f E[k]
```

and recognizes exactly:

- identity;
- eta;
- a finite chain of already-closed displayed functors; and
- the qualified closed-section weakening
  `λ a :^fd E. s[indexOf(a)]`.

This was the correct first executable witness, but extending that recognizer
with one pattern case per new surface expression would not be a scalable
general bracket architecture.

The completed ordinary bracket already demonstrates the right broad shape:
reify a callback once, retain first-order contextual terms and slot usage,
then compile variable use to explicit structural operations. The displayed
case needs the analogous architecture using displayed rather than ordinary
structural authority.

The immediate missing surface example is a finite independent sibling
context such as:

```text
λ (b :^fd B, c :^fd C).
  (FF[b], GG[c])
```

over a common base `K`, expected to lower to the transparent composite:

```text
Product_pair_funcd(
  comp_fapp0(FF, Product_projL_funcd(B,C)),
  comp_fapp0(GG, Product_projR_funcd(B,C)))
```

with the exact active implicit classifiers made explicit in Core.

Projection, exchange, and contraction should be instances of the same
compiler:

```text
λ (b,c). b       -- left projection
λ (b,c). (c,b)   -- reordered projections plus pairing
λ b. (b,b)       -- repeated compiled branch plus pairing
```

No primitive displayed swap or diagonal owner is required.

## Current Implementation Inventory

The reusable generic frontend mechanisms are:

- session-local opaque slot identities;
- locally nameless normalization and usage counts;
- callback-once immediate reification with no retained closure;
- derived dependency graphs and sibling classification;
- source provenance, scope checks, and fail-closed diagnostics;
- backend-neutral explicit Core; and
- generic LF checking, evaluation, runtime rewriting, and proof comparison.

The active displayed authority already qualified and transferred is:

- `id_funcd`;
- `comp_fapp0`;
- `Product_projL_funcd`;
- `Product_projR_funcd`;
- `Product_pair_funcd`;
- the transparent displayed product
  `uncurry(Product_cat_func) ∘ Product_pair(B,C)`;
- `section_pullback_func`; and
- `Pullback_catd_func`.

The current executable `CoreCategoricalContextualIr` contains slot,
explicit-Core, typed-application, and categorical-abstraction nodes. The
older surface specification also names typed pair and typed composition
nodes, but they are not presently executable node variants. The first row
therefore adds one generic `typed-pair` node; it does not add a new Core
owner. A dedicated typed-composition node is not required initially because
closed displayed-functor application can compile through
`typed-application` plus `comp_fapp0`.

## Alternatives

### A. Extend the rigid displayed-body recognizer

Rejected. Adding projection, pair, swap, diagonal, and later application
patterns directly to `displayedFunctorLambda` would encode a growing list of
surface shapes rather than a compositional language. It would make every
future consumer appear to need a new algorithm.

### B. Generic displayed contextual compiler

Selected. Reify a small first-order displayed body, derive dependencies and
usage from it, wire each independent contextual slot to an existing
displayed projection, and compile application/pair nodes compositionally.
The compiler emits existing displayed identity, composition, projection, and
pairing owners only.

### C. Compile only through total-context ordinary brackets

Deferred and not selected for the first row. The Sigma/Pi uncurrying rules
prove useful compatibility, but making every direct displayed abstraction a
total-context ordinary functor would lose the selected direct presentation
and make generality depend on the still-withheld Sigma arrow action and
total-category comparisons.

Total-context lowering remains an important candidate for genuine dependent
chains and should be measured there rather than assumed here.

### D. Add a primitive kernel displayed-bracket owner

Rejected as unnecessary for the first consumer. The active displayed
projection/pairing/composition basis already supplies its semantics. As
usual, a future primitive would require a concrete stuck consumer,
active-owner/Foundation audit, full owner-position probes, warning
comparison, and an exact separate decision.

## Selected Architecture

The selected public method is provisionally:

```ts
program.displayedContextLambda(
  [
    { name: "b", family: B },
    { name: "c", family: C },
  ],
  target,
  ([b, c], body) => body.fibrePair(
    body.apply(FF, b),
    body.apply(GG, c),
  ),
)
```

The precise TypeScript callback ergonomics may be adjusted during
implementation if the same frozen first-order semantics and fail-closed
boundary are preserved. The semantic method name is
`displayedContextLambda`; the pair constructor is `fibrePair`.

Construction proceeds as follows:

1. validate a finite nonempty list of displayed families over one literal
   base;
2. allocate one hidden natural base token and one displayed object token per
   binding;
3. evaluate the callback exactly once and retain no closure;
4. reify slot references, closed displayed-functor applications, and typed
   fibre pairs into immutable first-order IR;
5. derive the dependency graph and reject a requested independent block
   containing a genuine dependency edge;
6. form the left-associated transparent displayed-product source family;
7. wire each slot to the corresponding nested displayed projection;
8. compile closed-functor application through `comp_fapp0`;
9. compile typed pairs through `Product_pair_funcd`;
10. recover identity, projection/discard, exchange, and contraction from the
    same wiring; and
11. emit a closed direct `Functord_cat` term with provenance-bearing
    abstraction evidence.

The ordinary and displayed contextual compilers may share generic traversal
helpers, but no implementation-layout constraint is imposed. The invariant
is compositional, authority-correct behavior rather than code deduplication.

## Row Ledger

| row | status | dependency | exact scope |
| --- | --- | --- | --- |
| DISPLAYED-BRACKET-0A | proposal frozen and fully validated; checkpoint pending; awaiting H-DTTLF-USABILITY-DISPLAYED-BRACKET-01/D-DTTLF-USABILITY-009 | approved FIBRED-GRADUATE-1 review | Compare four architectures, select the generic first-order displayed contextual compiler, freeze DISPLAYED-BRACKET-1A, and authorize no mathematics by the proposal itself. Eight focused tests, the 821-test root gate, and unchanged 19-judgment live conformance pass |
| DISPLAYED-BRACKET-1A | blocked on D-DTTLF-USABILITY-009 | DISPLAYED-BRACKET-0A | Implement the root-only finite independent-sibling compiler, one `typed-pair` frontend node, existing-authority lowerings, positive/negative corpus, and runnable demo |
| DISPLAYED-CHAIN-0A | deferred; not authorized by D-009 | DISPLAYED-BRACKET-1A | Compare sequential-total, repeated pullback/Sigma, and direct displayed lowerings for a genuine dependency edge; identify exact Sigma-arrow/total-comparison needs |
| DISPLAYED-ND-0A | deferred; not authorized by D-009 | DISPLAYED-BRACKET-1A and chain evidence | Audit general `:^nd` coherence synthesis and higher action rather than extending coherent-eta recognition by cases |
| DISPLAYED-BRACKET-GRADUATE-1 | deferred | independent and genuine-chain evidence | Reassess general displayed usability, remaining mathematics, and product boundary |

## DISPLAYED-BRACKET-1A Frozen Contract

### Context boundary

- one or more displayed object bindings;
- all source families have the same literal base;
- source grouping is a left-associated transparent displayed product;
- the dependency graph, not user flags, must establish independence; and
- a genuine dependency edge fails with its recorded occurrence provenance.

The single-binding case preserves current identity, eta, finite closed
composition, and exact section weakening behavior.

### First-order body grammar

The accepted initial body grammar is:

```text
body ::= displayed-slot
       | closed-displayed-functor [ body ]
       | fibrePair(body, body)
```

Each node carries its exact indexed classifier, base index, source
provenance, and derived free-slot usage. Open/context-dependent functor
subjects remain negative in this row.

### Structural lowering

- a single selected slot lowers to `id_funcd` or its nested product
  projection;
- an unused sibling factor is discarded by selecting another projection;
- a repeated branch is compiled twice and combined with
  `Product_pair_funcd`;
- a permutation changes projection wiring and pairs the reordered branches;
- a closed displayed-functor application composes the closed functor after
  the compiled argument with `comp_fapp0`; and
- `fibrePair` compiles both branches from one literal source and uses
  `Product_pair_funcd`.

There is no primitive swap, diagonal, weakening, or `Product_catd` owner.

### Positive corpus

The implementation is not complete until all of these are executable:

1. `λ (b,c). b`;
2. `λ (b,c). (c,b)`;
3. `λ b. (b,b)`;
4. `λ (b,c). (FF[b],GG[c])`;
5. a three-sibling left-associated projection/pair consumer;
6. existing one-slot identity;
7. existing one-slot eta;
8. existing finite closed composition; and
9. existing exact closed-section weakening.

At least one consumer must exercise object and base-arrow computation through
the active displayed structural runtime clauses, not merely serialize the
term.

### Negative corpus

The implementation must reject:

- a genuine dependency edge grouped as independent;
- families over different bases;
- a body in the wrong target family;
- escaped and foreign tokens;
- an arbitrary pointwise family presented as coherent;
- an unsupported open displayed-functor subject; and
- access through default or earlier profiles.

### Semantic and product non-effects

DISPLAYED-BRACKET-1A adds:

- zero Lambdapi owners;
- zero Lambdapi runtime or proof rules;
- zero intrinsic Core semantic owners;
- zero owner-specific LF checker/evaluator branches;
- zero browser/default/deployed profile promotion; and
- zero parsing or bulk-transfer authority.

If implementation evidence contradicts any of those zeros, stop and freeze a
separate owner-position or product decision rather than silently broadening
D-DTTLF-USABILITY-009.

## Genuine Dependent Chains Remain First-Class

The independent-sibling row is selected because every required semantic
owner is already active and it is the next dependency-ready part of the
general bracket. It does not redefine the final goal as independent contexts
only.

For a genuine telescope:

```text
k : K
a : A[k]
b : B[k,a]
```

the compiler cannot simply exchange or group `a` and `b`. DISPLAYED-CHAIN-0A
must compare:

- an ordinary bracket over the sequential Sigma total category;
- repeated family pullback and Sigma extension;
- direct displayed substitution/section constructions; and
- any minimal missing Sigma arrow or total-comparison authority exposed by a
  concrete consumer.

The same frontend API and dependency planner should be reused where natural,
but the plan neither requires nor forbids the independent and genuine-chain
lowerers from sharing one implementation function.

## Exact Decision

**H-DTTLF-USABILITY-DISPLAYED-BRACKET-01 — pending.**

**D-DTTLF-USABILITY-009 — proposed.**

> Approve H-DTTLF-USABILITY-DISPLAYED-BRACKET-01/
> D-DTTLF-USABILITY-009 as proposed: select a generic first-order displayed
> contextual compiler instead of extending the rigid body recognizer;
> authorize root-only DISPLAYED-BRACKET-1A for finite independent sibling
> blocks using typed-pair IR plus existing identity, composition, projection,
> pairing, section-weakening, and reindexing authority; add no Lambdapi owner
> or rule; and keep genuine dependent-chain lowering, general `:^nd`
> coherence, Sigma arrow action, total-category comparison, parsing/bulk
> transfer, and browser promotion as separate rows?

Approval authorizes only DISPLAYED-BRACKET-1A as frozen above. It does not
authorize DISPLAYED-CHAIN-0A, DISPLAYED-ND-0A, a new mathematical owner/rule,
parser, bulk transfer, browser promotion, or broader Git action.

Under the user's plan-specific delegation, if no immediate human response
follows presentation of this exact frozen proposal during unattended
continuation, the coding agent may record a separate delegated approval with
human supersession and proceed only through a coherent green local
checkpoint. The proposal itself remains non-self-authorizing.

## Acceptance And Validation

DISPLAYED-BRACKET-0A is complete only when:

1. its executable proposal validates the approved graduation prerequisite,
   current one-slot binder contract, dependency planner, structural owner
   set, and semantic non-effects;
2. the four alternatives and exact selection remain deeply frozen;
3. focused tests check the decision, body grammar, finite corpus,
   dependent-chain boundary, browser exclusion, and fail-closed drift;
4. root typecheck, lint, and tests pass;
5. mandatory live Lambdapi conformance remains green; and
6. the living plans and exact local checkpoint are synchronized.

DISPLAYED-BRACKET-1A is complete only when:

1. the callback is evaluated once and no closure is stored;
2. the body is immutable first-order IR rather than a new recognizer case
   list;
3. dependencies and usage are derived, not duplicated by callers;
4. all nine positive cases and all seven negative families above pass;
5. object and arrow computation use the active displayed runtime authority;
6. earlier profiles and every semantic/product non-effect remain unchanged;
7. focused tests, `check:ts`, live conformance, proportional active-kernel
   checks, documentation synchronization, staged-diff review, and a local
   checkpoint pass.

All Lambdapi processes remain bounded to at most 60 seconds. Warnings are
diagnostic and do not veto a wanted design, but every primitive must still be
audited against active constructions and Foundations before it is proposed.

## DISPLAYED-BRACKET-0A Validation Record

The frozen successor proposal is green:

- all eight focused executable tests pass, including the graduation
  prerequisite, four-way selection, exact body grammar, structural routing,
  finite positive/negative corpus, genuine-chain deferral, browser exclusion,
  and fail-closed selection/authority/decision drift;
- root typecheck and lint pass;
- `./scripts/pnpmw run check:ts` passes 821 tests: 775 active passes, 46
  intentional skips, and zero failures; and
- the unchanged mandatory `./scripts/pnpmw run check:conformance` passes all
  19 live judgments in 29.2 seconds under the global 60-second bound.

No `.lp` source, kernel-owned report, catalog, health target, browser entry
point, parser, or product profile changed. The complete 41-file kernel CI
from the immediately preceding validated fibred-graduation boundary remains
applicable. The six preserved untracked timeout-artifact directories remain
excluded and untouched.

## Git Boundary

This plan inherits
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md).
Existing authorization permits exact local checkpoints on the current
`goal/typescript-elaborator-v3.2` branch only after a coherent tranche is
green, ledgers are synchronized, unrelated files are excluded, and
`git diff --cached --check` passes.

No push, merge, PR, publication, release, new branch/worktree, amend, rebase,
reset, history rewrite, cleanup, deletion, or worktree removal is authorized.

## Persistent `/goal` Launch Prompt

```text
Continue implementing
docs/TYPESCRIPT_ELABORATOR_V3_2_DISPLAYED_BRACKET_PLAN.md and treat this
Persistent /goal Launch Prompt as part of the objective.

Recover the actual descendant state, worktrees, staged/unstaged changes,
active authority, completed fibred-context plan, immutable
FIBRED-GRADUATE-1 proposal/review, and this plan's ledger. Follow root
AGENTS.md and emdash2/AGENTS.md for every active-kernel action.

Preserve the qualified D-DTTLF-USABILITY-008 conclusion and every withheld
claim. DISPLAYED-BRACKET-0A's exact executable proposal selects a generic
first-order displayed contextual compiler rather than extending the current
rigid body recognizer, compiling only through total categories, or adding a
kernel bracket owner. D-DTTLF-USABILITY-009 is pending until human or
separately recorded delegated unattended approval.

If D-DTTLF-USABILITY-009 is approved, implement only root-only
DISPLAYED-BRACKET-1A: finite nonempty independent sibling blocks over one
common base, one-shot callbacks, derived dependency/usage evidence, one
typed-pair frontend IR node, left-associated transparent displayed-product
source, and existing id_funcd/comp_fapp0/Product_projL_funcd/
Product_projR_funcd/Product_pair_funcd/section_pullback_func authority.
Exercise projection, exchange, contraction, mapped pairing, three-sibling
scaling, and all preserved one-slot cases. Add no Lambdapi owner/rule,
primitive Core binder mode, owner-specific LF path, Product_catd head,
browser profile, parser, or bulk transfer.

Keep genuine dependency-chain lowering first-class but separate as
DISPLAYED-CHAIN-0A. Do not assume Sigma arrow action, a generic total-category
pullback/equivalence, raw product-reindex equality, or general :^nd coherence.
Freeze a separate exact decision if implementation evidence exposes missing
mathematics.

Use the existing local-checkpoint authorization only after bounded green
validation, synchronized ledgers, exact staging, and
git diff --cached --check. Do not push, merge, publish, rewrite history, or
clean up the preserved worktree artifacts.
```
