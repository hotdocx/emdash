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
H-DTTLF-USABILITY-DISPLAYED-BRACKET-01/D-DTTLF-USABILITY-009 is approved
exactly as proposed under the user's delegated unattended authority after no
immediate human response. The separate immutable review records human
supersession and authorizes only root-only DISPLAYED-BRACKET-1A. The
pre-review proposal remains unchanged and non-self-authorizing.

DISPLAYED-BRACKET-1A is now implemented in the root TypeScript workbench.
Its public `fibred-displayed-bracket-1` profile accepts a finite independent
displayed sibling block, reifies its callback once, and compiles the frozen
slot/application/pair grammar through existing active-v3.2 displayed
identity, composition, projection, pairing, weakening, and reindexing
authority. No `.lp` owner or rule was added. The final repository-wide
TypeScript gate passes 841 tests: 795 active passes, 46 intentional skips,
and zero failures. The exact local implementation checkpoint is
`d4e0e9bc5ca4dc07dcdfa44e2cb048545f3ee8ab`.

DISPLAYED-LIFTING-0A is now frozen as the root-only executable proposal
`src/v3_2/categorical_displayed_lifting_proposal.ts`. Its ten focused tests
pass, as do the full 851-test root gate (805 active passes, 46 intentional
skips, zero failures), the repeated 19-judgment live conformance gate, and
the bounded active-kernel check. It records the existing recursive ordinary
cases, the exact restricted displayed cases, and the owner/action gaps
without extending the semantic grammar. In particular, active
`Functor_catd`, ordinary `Eval_func`/`fapp0_func`, and displayed pairing are
ingredients but are not silently treated as a selected coherent displayed
evaluator. The proposal awaits
H-DTTLF-USABILITY-DISPLAYED-LIFTING-01/D-DTTLF-USABILITY-010 and authorizes
no successor by its own existence.

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

## Recursive Contextual-Lifting Reassessment

The post-implementation usability review corrects one earlier framing. The
next architectural step is **not** another `RawExpr` language plus another
bidirectional elaborator/checker. The root workbench already has:

- a direct typed TypeScript construction surface;
- callback-once reification into scoped first-order contextual IR;
- classifier-directed ordinary and displayed application judgments;
- backend-neutral explicit emdash Core; and
- the generic bidirectional Core checker/evaluator.

A future textual parser may have a raw syntax tree, but that optional tree
would elaborate into this existing typed boundary. It must not duplicate the
categorical abstraction algorithm. The usability problem here is semantic:
variables bound categorically must be abstracted recursively through
subexpressions and lowered to the appropriate structural action.

### Bracket means an internal recursive compiler

The notation `[x]t` names an internal contextual-lifting operation. It does
not require an end user to put an explicit bracket around each subexpression.
For the already-completed ordinary compiler, the outer `lambda` invokes the
operation once and the bound token may then occur freely beneath every
supported typed IR constructor:

```text
[x] x                    -> id_func
[x] c                    -> Const_func(c)
[x] F(t[x])              -> F o [x]t              when F is closed
[x] S[x](T[x])           -> Eval_func o
                              Product_pair([x]S,[x]T)
[x] (s[x],t[x])          -> pair([x]s,[x]t)
[x] (lambda y. t[x,y])   -> curry([x,y]t)
```

This is a deterministic partial structural recursion over a typed finite
AST. It is not a search for an arbitrary semantic factorization modulo every
kernel equation. Every supported constructor has a declared contextual
action; an opaque or unsupported constructor fails closed at that node with
provenance. Arbitrary semantic factoring could be undecidable, but this
syntax-directed compiler is decidable over its registered grammar.

### Exact ordinary fixed-evaluation witness

The current implementation already accepts the direct TypeScript equivalent
of:

```text
F  : Functor A (Functor_cat B C)
y0 : Obj B

lambda x :^f A. F x y0
```

using only the outer abstraction plus recursive `apply` nodes:

```ts
emdash.lambda(
  "x",
  A,
  C,
  x => emdash.apply(emdash.apply(F, x), y0),
)
```

It compiles to:

```text
Eval_func(B,C) o
  Product_pair(F o id_func(A), Const_func(y0)).
```

The active kernel also has specialized fixed-evaluation presentations such
as `fapp0_func(y0)`. Selecting one later as a canonicalization is optional;
the general evaluation/pairing result is already authority-correct. A
permanent regression now freezes this example, including identity,
composition, constant abstraction, product, pairing, and evaluation
prerequisites. It proves that inner subexpressions do not need explicit
bracket syntax.

### Exact displayed limitation

DISPLAYED-BRACKET-1A is recursive, but only over its frozen initial grammar:

```text
body ::= displayed-slot
       | closed-displayed-functor [ body ]
       | fibrePair(body, body)
```

It recursively handles both pair branches and the argument of a closed
displayed functor. It does **not** yet abstract:

- an open displayed-functor-valued subject applied to a closed argument;
- an open displayed subject and open displayed argument paired for
  evaluation;
- nested displayed abstractions/currying;
- a later binding whose family genuinely depends on an earlier fibre
  binding;
- general `tapp*`/higher naturality actions;
- contravariant application positions; or
- general `:^fd`/`:^nd` coherence.

The old `displayedFunctorLambda` remains useful for its exact
identity/eta/closed-chain/section-weakening envelope, but adding more
whole-body recognizer cases is not the continuation architecture.
`displayedContextLambda` is the compositional replacement and should grow by
typed recursive lifting cases.

### Migration correction

The historical `MIGRATE-2` checkpoint physically removed the old root
HOAS-style `Term`/`Lam`/`App`/`Pi`, inference, implicit insertion, holes,
higher-order unification, rewriting, and proof-state source from this goal
branch. Those files remain recoverable from `main` and Git history. The cut
therefore did remove an integrated generic LF user-term frontend, and future
work should compare the old generic mechanisms with the current v3.2 modules
and selectively recover any still-missing reusable capability.

It did **not** remove a completed recursive categorical bracket compiler.
The old `LamMode` checked binder-mode metadata and reconstructed an outer LF
lambda/Pi while categorical action used explicit `FMap`/`FDApp`/`TDApp`
nodes. It did not lower a free functorial occurrence recursively to
identity/constant/pairing/evaluation/curry structure. The current ordinary
compiler is new functionality. Restoring the stale category-specific AST is
not selected.

### Revised feasibility and next architecture row

The ordinary first-order contextual-lifting architecture is substantially
settled and the independent displayed sibling compiler is a positive
compositional witness. No from-scratch redesign or second surface checker is
indicated. The remaining risk is coverage of authority-backed lifting laws:
some displayed, dependent, higher, or contravariant cases may expose a
missing kernel owner or coherence boundary.

The next bounded row is therefore `DISPLAYED-LIFTING-0A`, an executable
read-only proposal and owner audit. It must freeze a matrix indexed by:

- typed IR constructor and application judgment;
- binder variation/dependency mode (`:^f`, `:^n`, `:^fd`, `:^nd`);
- occurrence profile (closed/varying subject and argument);
- polarity/variance and cell level; and
- selected active owner or exact fail-closed gap.

For application it must distinguish at least:

```text
subject closed, argument varying  -> composition
subject varying, argument closed  -> fixed evaluation
subject varying, argument varying -> pairing then evaluation
contravariant position            -> opposite/precomposition action
displayed/dependent position      -> displayed composition/evaluation/reindexing
transformation-valued position    -> typed tapp*/higher action
```

The row also isolates the current dependent-target/direct-displayed profile
composition mismatch. Only after that frozen comparison may a separate
implementation row extend the displayed grammar. Genuine dependency-chain
lowering remains a first-class subsequent comparison rather than being
silently treated as an independent product.

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

`CoreCategoricalContextualIr` now contains slot, explicit-Core,
typed-application, typed-pair, and categorical-abstraction nodes. The
`typed-pair` node is construction IR only: it is eliminated by
`displayedContextLambda` into the existing displayed-product pairing owner
and does not add a Core semantic owner. A dedicated typed-composition node is
not required because closed displayed-functor application compiles through
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
| DISPLAYED-BRACKET-0A | proposal frozen, validated, checkpointed `e4b743f70c0454d63a93587dc045a3e2d0273ee5`, and approved exactly as proposed by a separate delegated review with human supersession | approved FIBRED-GRADUATE-1 review | Compare four architectures, select the generic first-order displayed contextual compiler, freeze DISPLAYED-BRACKET-1A, and authorize no mathematics by the proposal itself. Eight focused proposal tests, nine focused review tests, the 830-test reviewed root gate, and unchanged 19-judgment live conformance pass |
| DISPLAYED-BRACKET-1A | complete; validated; checkpointed `d4e0e9bc5ca4dc07dcdfa44e2cb048545f3ee8ab` | reviewed DISPLAYED-BRACKET-0A/D-009 | Root-only finite independent-sibling compiler, one `typed-pair` frontend node, existing-authority lowerings, positive/negative corpus, runnable compact demo, and permanent ordinary fixed-inner-evaluation regression |
| DISPLAYED-LIFTING-0A | executable proposal frozen and focused-green; H-DTTLF-USABILITY-DISPLAYED-LIFTING-01/D-DTTLF-USABILITY-010 pending | DISPLAYED-BRACKET-1A | Freeze the typed node/judgment × occurrence × mode × variance lifting matrix; prove the existing ordinary fixed-evaluation witness; audit existing owners for closed/open displayed application cases, nested abstraction, higher action, and contravariance; isolate the dependent-target/direct-displayed profile mismatch; add no semantic owner/rule |
| DISPLAYED-EVAL-0B | proposed read-only next row; not self-authorized | approved DISPLAYED-LIFTING-0A | Run owner-position and derived-construction probes for coherent evaluation of a `Functor_catd`-valued varying subject at fixed and varying arguments; determine whether active authority suffices or freeze a minimal new-owner proposal; classify the profile-join mismatch without a semantic patch |
| DISPLAYED-LIFTING-1A | deferred pending 0B evidence and a separate exact proposal/review | DISPLAYED-EVAL-0B | Extend the displayed recursive grammar only for exact licensed application judgments, with positive/negative consumers and no whole-body recognizer growth |
| DISPLAYED-CHAIN-0A | subsequent read-only comparison; not a product case | DISPLAYED-LIFTING-0A | Compare sequential-total, repeated pullback/Sigma, and direct displayed lowerings for one genuine dependency edge; identify exact Sigma-arrow/total-comparison needs before semantic implementation |
| DISPLAYED-ND-0A | deferred | DISPLAYED-LIFTING-0A and chain evidence | Audit general `:^nd` coherence synthesis and higher action rather than extending coherent-eta recognition by cases |
| DISPLAYED-BRACKET-GRADUATE-1 | deferred | independent and genuine-chain evidence | Reassess general displayed usability, remaining mathematics, and product boundary |

## DISPLAYED-LIFTING-0A Frozen Executable Proposal

The immutable proposal is
`src/v3_2/categorical_displayed_lifting_proposal.ts`; its focused test is
`tests/v3_2_categorical_displayed_lifting_proposal_tests.ts`. It is a
read-only architectural and owner audit. It adds no runtime behavior, Core
owner, Lambdapi declaration/rule, parser, checker, browser export, or profile
join.

### Architecture verdict

The source boundary remains the existing typed TypeScript construction IR.
The outer abstraction invokes a deterministic recursive contextual-lifting
operation. Bound variables may occur freely beneath supported typed
subexpressions; they do not require local bracket punctuation. The result is
backend-neutral explicit Core and is checked/evaluated by the existing
generic checker. An unsupported typed constructor fails closed with
provenance.

Accordingly, the proposal adds neither a parallel `RawExpr` language nor a
second bidirectional checker. It also imposes no implementation-layout dogma:
ordinary and displayed lowering may share helpers or differ as their typed
judgments naturally require. The invariant is scalable syntax-directed
recursion with explicit authority, not uniform source code.

The historical assessment remains:

- MIGRATE-2 physically deleted the old generic HOAS LF frontend from this
  branch, but those mechanisms remain recoverable from `main` and history;
- it did not delete an earlier recursive categorical bracket compiler,
  because the old mode-aware LF lambda plus explicit categorical action nodes
  did not perform the current structural abstraction; and
- restoring the stale category-specific frontend is not selected.

### Ordinary and displayed matrix

The ordinary compiler is already closed over the currently registered
first-order cases:

| occurrence form | status | lowering |
| --- | --- | --- |
| slot | implemented | identity |
| closed term | implemented | constant abstraction |
| closed subject, open argument | implemented | composition |
| open subject, closed argument | implemented and permanently tested | `Eval_func` after pairing `F o id` with `Const(y0)`; `fapp0_func` is an available specialized presentation |
| open subject, open argument | implemented | pairing followed by `Eval_func` |
| nested abstraction | implemented | curry package |

The displayed/dependent matrix is deliberately more qualified:

| occurrence or judgment | status | authority or exact gap |
| --- | --- | --- |
| slot/projection | implemented | `id_funcd`, `Product_projL_funcd`, `Product_projR_funcd` |
| closed coherent displayed subject, open argument | implemented | `comp_fapp0` |
| fibre pair | implemented | `Product_pair_funcd` |
| exact closed-section weakening | implemented, qualified | `section_pullback_func` |
| varying fibre-functor subject, fixed/coherent argument | unresolved owner/derived construction | `Functor_catd`, ordinary `Eval_func`/`fapp0_func` are ingredients; a coherent displayed evaluator and its reindexing behavior are not yet selected |
| varying subject, varying argument | unresolved owner/derived construction | displayed pairing exists, but pairing alone does not supply coherent evaluation |
| nested displayed abstraction | comparison required | direct displayed curry versus sequential totalization versus repeated pullback/Sigma |
| genuine dependency edge | separate `DISPLAYED-CHAIN-0A` | compare the three presentations and audit Sigma arrow action |
| contravariant position | frontend route unselected | `Functor_catd`, `Op_catd`, and pre/postcomposition ingredients require polarity-directed lowering |
| transformation/higher action | separate `DISPLAYED-ND-0A` | select among `tapp*`, `tdapp*`, and `fdapp*` by typed cell level; do not claim general coherence synthesis |
| dependent-target/direct-displayed profile composition | measured mismatch | preserve the `TYPE_MISMATCH` reproduction and isolate transfer/presentation interaction before any semantic patch |

The absence of a lexically obvious generic displayed-evaluation owner is not
a proof that the construction is mathematically impossible or that a new
primitive is necessary. It is an exact evidence gap. Before adding any
owner, the required workflow is to probe the relevant owner positions and
attempt a transparent derived construction from active authority. If that
fails, a separate proposal must state the minimal signature, computation,
coherence, warning impact, and consumer that justify a new owner.

### Feasibility conclusion and selected next evidence

The design is settled enough to continue systematically for ordinary
first-order abstraction and for the demonstrated independent displayed
grammar. The result is not yet a graduation proof for arbitrary
displayed/dependent, higher, or contravariant bodies. The remaining obstacle
is now localized: coherent displayed evaluation and related reindexing laws,
not a missing parser, cosmetic surface AST, or lost former compiler.

The proposal therefore selects `DISPLAYED-EVAL-0B` as the next bounded
read-only evidence row. Once separately approved, it must answer:

1. whether `Functor_catd` plus active evaluation/functoriality authority
   derives coherent displayed evaluation;
2. if not, the minimal owner and law set needed for it;
3. exactly which fixed-argument and both-open recursive frontend judgments
   the result licenses; and
4. whether the measured profile join is only a transfer/presentation problem
   or exposes a semantic mismatch.

Semantic DISPLAYED-LIFTING-1A remains withheld until that evidence freezes an
exact implementation row. Genuine dependency chains and general `:^nd`
coherence remain independent later rows.

### Exact decision gate

The executable proposal asks:

> Approve H-DTTLF-USABILITY-DISPLAYED-LIFTING-01/
> D-DTTLF-USABILITY-010 as proposed: preserve the existing typed TypeScript
> IR, recursive contextual compiler, explicit Core, and generic checker
> without adding RawExpr, a second bidirectional checker, parser, or bracket
> punctuation; accept the executable owner/action matrix and its exact
> coherent displayed-evaluation gap; authorize only root/active-authority
> DISPLAYED-EVAL-0B owner-position and derived-construction probes; and keep
> semantic DISPLAYED-LIFTING-1A, any new kernel owner/rule, genuine-chain
> lowering, general `:^nd` coherence, Sigma arrow action, parsing/bulk
> transfer, browser promotion, and broader Git authority withheld pending
> separate exact proposals?

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

**H-DTTLF-USABILITY-DISPLAYED-BRACKET-01 — approved under delegated
unattended authority; human supersession retained.**

**D-DTTLF-USABILITY-009 — approved as proposed.**

> Approve H-DTTLF-USABILITY-DISPLAYED-BRACKET-01/
> D-DTTLF-USABILITY-009 as proposed: select a generic first-order displayed
> contextual compiler instead of extending the rigid body recognizer;
> authorize root-only DISPLAYED-BRACKET-1A for finite independent sibling
> blocks using typed-pair IR plus existing identity, composition, projection,
> pairing, section-weakening, and reindexing authority; add no Lambdapi owner
> or rule; and keep genuine dependent-chain lowering, general `:^nd`
> coherence, Sigma arrow action, total-category comparison, parsing/bulk
> transfer, and browser promotion as separate rows?

The recorded approval authorizes only DISPLAYED-BRACKET-1A as frozen above.
It does not
authorize DISPLAYED-CHAIN-0A, DISPLAYED-ND-0A, a new mathematical owner/rule,
parser, bulk transfer, browser promotion, or broader Git action.

The separate executable review is
`src/v3_2/categorical_displayed_bracket_review.ts`. It records that no
immediate human response followed presentation of the exact frozen proposal,
uses the user's plan-specific unattended delegation, requires the Git
checkpoint SOP, and remains supersedable by a later human decision. The
proposal itself remains non-self-authorizing.

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
excluded and untouched. The exact green local proposal checkpoint is
`e4b743f70c0454d63a93587dc045a3e2d0273ee5`.

## D-DTTLF-USABILITY-009 Delegated Review Record

The separate immutable review records the exact frozen proposal snapshot,
the delegated unattended approval condition, and human supersession. It
authorizes only the root-only `fibred-displayed-bracket-1` implementation
row and one `typed-pair` frontend node using existing displayed authority.
It explicitly withholds DISPLAYED-CHAIN-0A, general `:^nd` coherence, Sigma
arrow action, total-category comparison, any semantic owner/rule, browser
promotion, parsing, bulk transfer, and broader Git action.

All nine focused review tests pass. The root reviewed gate passes 830 tests:
784 active passes, 46 intentional skips, and zero failures. No semantic
artifact changed, so the unchanged 19-judgment conformance result and the
complete 41-file kernel CI at the parent boundary remain applicable.

## DISPLAYED-BRACKET-1A Implementation Record

### End-user input and result

The direct typed TypeScript surface now accepts, for example:

```ts
const mapped = emdash.displayedContextLambda(
  [
    { name: "b", family: B },
    { name: "c", family: C },
  ],
  emdash.displayedProduct(D, Q),
  ([b, c]) => emdash.fibrePair(
    emdash.apply(FF, b),
    emdash.apply(GG, c),
  ),
)
```

where `B,C,D,Q : Catd K`, `FF : Functord B D`, and
`GG : Functord C Q`. It compiles to the direct displayed functor summarized
as

```text
Product_pair_funcd(
  comp_fapp0(FF, Product_projL_funcd(B,C)),
  comp_fapp0(GG, Product_projR_funcd(B,C)))
:
Functord(Product_catd(B,C),Product_catd(D,Q)).
```

Here `Product_catd` is the established readable name for the transparent
uncurried/product-pair construction, not a new primitive owner. The returned
programmatic compilation retains the complete backend-neutral explicit Core
term, inferred/expected classifiers, abstraction evidence, and prerequisite
sets. The CLI demo prints a compact stable synopsis instead of flooding the
end user with the complete serialized Core.

The same API and compiler handle:

- projection `λ (b,c). b`;
- exchange `λ (b,c). (c,b)`;
- contraction `λ b. (b,b)`;
- closed-functor mapped pairing;
- a three-sibling left-associated reordering; and
- the previously supported one-slot identity, eta, finite composition, and
  exact section weakening.

The projection demo evaluates at both `x : Obj K` and `p : Hom K x y`.
Object action reduces through the active displayed left-projection point
rule; arrow action reduces through its capped-action rule and the established
displayed full-action path.

Run the self-contained report with:

```bash
./scripts/pnpmw run demo:categorical-displayed-bracket
```

### Compiler pipeline

`displayedContextLambda`:

1. validates a finite nonempty same-base binding list and target;
2. asks the generic locally nameless dependency planner to prove that the
   requested displayed factors are siblings over one minimal base, without
   caller-supplied independence flags;
3. allocates one hidden base slot and one indexed fibre slot per binding;
4. invokes the TypeScript callback exactly once and retains no closure;
5. normalizes slot, indexed closed-functor application, and typed-pair nodes
   into immutable first-order contextual IR with usage and provenance;
6. forms the left-associated transparent displayed-product family;
7. recursively wires each factor to existing nested displayed projections;
8. compiles application by generic category composition at `Catd_cat K`;
9. compiles pairs through the existing displayed-product pair owner; and
10. returns a checked closed direct displayed functor plus explicit
    `categorical.displayed-context-bracket` evidence.

Discard, permutation, and contraction are consequences of projection wiring
and repeated branches. They are not separate primitive owners or recognizer
cases. The old one-slot exact section weakening remains a deliberately
qualified lowering because its closed-section input and active
`section_pullback_func` authority are stronger than arbitrary weakening.

### Fail-closed boundary

Executable negatives reject:

- empty and duplicate binding lists;
- families or targets over another base;
- a body with the wrong indexed target;
- escaped and foreign terms;
- pairing outside a valid active fibre context;
- a nested pointwise/open capture presented as a coherent displayed functor;
- access through the default and dependent-target profiles; and
- a genuine dependency edge requested as an independent sibling product.

The public API has no unchecked raw-node constructor, so an arbitrary
pointwise family cannot be forged as coherent first-order bracket input.
Closed displayed-functor subjects are admitted only when their usage is
disjoint from every active contextual slot and their source, target, and base
classifiers match literally.

### Profile composition finding

The new `fibred-displayed-bracket-1` profile deliberately uses the last green
`fibred-weaken-reindex-1` transfer as its runtime foundation. It does not
expose `fibred-dependent-target-1`. This is not a mathematical retreat or an
accidental omission: an implementation trial that layered the bracket on the
dependent-target transfer reproduced a pre-existing `TYPE_MISMATCH` for the
older two-closed-functor `displayedFunctorLambda` composition, while the same
consumer passes in `fibred-binder-1` and `fibred-weaken-reindex-1`.

Reciprocal tests now freeze the separation: the bracket profile rejects
dependent-target constructors, and the dependent-target profile rejects the
new bracket. DISPLAYED-CHAIN-0A must isolate the transfer/presentation
interaction before proposing a joined profile. It must not paper over the
failure by adding a new semantic rule.

The mapped-pair point test also preserves the existing distinction between
generic composition at the category of categories and the specialized
ordinary-category composition presentation. Expected terms are built
through already-qualified direct displayed functors; no unreviewed runtime
collapse between the two composition heads is assumed.

### Validation to date

- root typecheck and lint pass;
- all ten focused implementation/demo tests pass;
- the complete focused corpus takes approximately 4 minutes 43 seconds in
  the current evaluator, with no performance SLA claimed;
- the compact runnable demo passes and reports all five representative
  inputs, object/arrow computation, and a source-located cross-base
  diagnostic;
- the synchronized `./scripts/pnpmw run check:ts` gate passes 841 tests:
  795 active passes, 46 intentional skips, and zero failures in approximately
  8 minutes 4 seconds, including the permanent ordinary
  `lambda x :^f A. F x y0` regression;
- the mandatory live Lambdapi conformance oracle passes all 19 judgments in
  20.5 seconds under the global 60-second bound;
- `EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check` passes the active
  kernel, extensions, and diagnostics; and
- no `.lp`, kernel catalog, health report, browser entry point, parser, or
  transfer-acquisition artifact changed.

Exact staged-path review and `git diff --cached --check` passed. The local
implementation checkpoint is
`d4e0e9bc5ca4dc07dcdfa44e2cb048545f3ee8ab`.

## Change Log

- **2026-07-28 — DISPLAYED-BRACKET-0A frozen, validated, and
  checkpointed.** The executable four-way comparison selects a generic
  first-order displayed contextual compiler. It freezes a no-new-mathematics
  DISPLAYED-BRACKET-1A for finite independent sibling blocks, one typed-pair
  frontend node, and existing displayed identity/composition/projection/
  pairing/weakening/reindexing authority. Genuine dependency chains and
  general `:^nd` coherence remain separate. Eight focused tests, the
  821-test root gate, and all 19 live conformance judgments pass. The exact
  local checkpoint is `e4b743f70c0454d63a93587dc045a3e2d0273ee5`;
  its synchronized proposal-ledger checkpoint is
  `6ee1b55b395eec4a9a9909afff0f1b0f693312f4`.
- **2026-07-28 — D-DTTLF-USABILITY-009 approved under delegated
  unattended authority.** No immediate human response followed presentation
  of the exact frozen proposal, so the user's standing plan-specific
  delegation was exercised. The separate immutable review retains human
  supersession and authorizes only root-only DISPLAYED-BRACKET-1A. Nine
  focused tests and the 830-test reviewed root gate pass; no semantic,
  browser, acquisition, or broader Git authority was added.
- **2026-07-28 — DISPLAYED-BRACKET-1A implemented.** The new root-only
  profile reifies finite independent displayed contexts into first-order
  slot/application/pair IR and compiles them compositionally through existing
  displayed product structure. Projection, exchange, contraction, mapped
  pairing, three siblings, all preserved one-slot cases, fail-closed
  diagnostics, object/arrow computation, and a compact direct-TypeScript demo
  pass. The dependent-target profile remains deliberately separate pending
  DISPLAYED-LIFTING-0A and the later DISPLAYED-CHAIN-0A analysis. No
  Lambdapi owner/rule or deployed surface was added. The exact green local
  implementation checkpoint is
  `d4e0e9bc5ca4dc07dcdfa44e2cb048545f3ee8ab`.
- **2026-07-28 — Recursive contextual-lifting architecture corrected.**
  Confirmed by execution that the existing ordinary compiler recursively
  accepts `lambda x :^f A. F x y0` without inner bracket syntax and lowers it
  through identity, composition, constant abstraction, pairing, and
  `Eval_func`. Rejected an additional parallel `RawExpr`/checker as the
  immediate architecture. Recorded the exact restricted recursion of
  DISPLAYED-BRACKET-1A, the physical-but-recoverable MIGRATE-2 generic-LF
  deletion, and the distinction that no prior categorical bracket solution
  was discarded. Selected proposal-only DISPLAYED-LIFTING-0A to freeze the
  typed recursive lifting/owner matrix before extending the displayed
  grammar; genuine dependency chains remain a subsequent first-class row.
- **2026-07-28 — DISPLAYED-LIFTING-0A executable proposal frozen.** Added a
  deeply immutable root-only owner/action matrix with ten focused tests. It
  preserves the existing typed IR and recursive checker boundary, records
  all six implemented ordinary occurrence cases, distinguishes four
  implemented/qualified displayed cases from open-subject evaluation,
  nested, variance, higher, and genuine-chain gaps, and isolates the measured
  profile mismatch. The audit finds active `Functor_catd`, ordinary
  evaluation, and displayed-pairing ingredients but no selected generic
  coherent displayed evaluator; absence is not treated as proof that a new
  primitive is needed. It proposes only a separately reviewed
  DISPLAYED-EVAL-0B owner-position/derived-construction probe and adds no
  semantic or Git authority. Ten focused tests, the complete 851-test root
  gate (805 active passes, 46 intentional skips, zero failures), all 19 live
  conformance judgments, and the bounded active-kernel check pass.

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
kernel bracket owner. D-DTTLF-USABILITY-009 is approved exactly as proposed
by a separate immutable delegated review with human supersession.

Preserve completed DISPLAYED-BRACKET-1A: finite nonempty independent sibling
blocks over one common base, one-shot callbacks, derived dependency/usage
evidence, one typed-pair frontend IR node, left-associated transparent
displayed-product source, and existing
id_funcd/comp_fapp0/Product_projL_funcd/Product_projR_funcd/
Product_pair_funcd/section_pullback_func authority. If its final root gate or
exact implementation checkpoint is not yet recorded, complete only that
bounded synchronization first. Add no Lambdapi owner/rule, primitive Core
binder mode, owner-specific LF path, Product_catd head, browser profile,
parser, or bulk transfer.

Preserve the 2026-07-28 recursive contextual-lifting correction. Do not add a
parallel RawExpr language, parser, or bidirectional checker for this task.
The existing typed TypeScript construction IR, recursive contextual
compiler, explicit Core, and generic checker are the implementation
boundary. Treat `[x]t` as an internal syntax-directed recursion: the bound
token may occur freely under supported subexpressions, and an unsupported
typed node fails closed. Preserve the permanent ordinary
`lambda x :^f A. F x y0` fixed-evaluation regression.

Preserve frozen DISPLAYED-LIFTING-0A. Its executable matrix records the six
implemented ordinary recursive cases; the implemented displayed slot,
closed-subject/open-argument, pair, and qualified weakening cases; and the
exact unresolved coherent displayed-evaluation, nested abstraction,
contravariant, higher-cell, genuine-chain, and profile-composition rows. It
finds `Functor_catd`, ordinary `Eval_func`/`fapp0_func`, and displayed
pairing as ingredients but does not claim that they already form a coherent
displayed evaluator or that a new primitive is necessary. The proposal is
non-self-authorizing and awaits
H-DTTLF-USABILITY-DISPLAYED-LIFTING-01/D-DTTLF-USABILITY-010.

After an exact approval/review, implement only DISPLAYED-EVAL-0B as a
read-only owner-position and derived-construction probe. First attempt to
derive coherent displayed evaluation from active authority; if this is not
possible, freeze a separate minimal-owner proposal and do not add the owner
or rules in 0B. Isolate whether the measured dependent-target/direct-
displayed composition mismatch is a transfer/presentation issue or a
semantic one. Add no recursive grammar case, semantic owner/rule, second
surface checker, or profile join in 0B.

Keep DISPLAYED-LIFTING-1A and DISPLAYED-CHAIN-0A separate. The latter must
compare sequential-total, repeated pullback/Sigma, and direct displayed
lowerings on one genuine dependency edge. Do not assume Sigma arrow action,
a generic total-category pullback/equivalence, raw product-reindex equality,
or general :^nd coherence. Freeze a separate exact executable proposal
before any semantic implementation or new owner/rule.

For a future exact bounded gate in this goal, if no immediate human response
follows presentation of its frozen proposal, the user's standing delegation
permits a separate explicit unattended approval review. Keep the proposal
non-self-authorizing, retain human supersession, preserve every frozen
non-effect, and proceed only to a coherent green local checkpoint. Delegation
does not broaden semantic scope or authorize destructive, remote,
integration, publication, or history-rewrite actions.

Use the existing local-checkpoint authorization only after bounded green
validation, synchronized ledgers, exact staging, and
git diff --cached --check. Do not push, merge, publish, rewrite history, or
clean up the preserved worktree artifacts.
```
