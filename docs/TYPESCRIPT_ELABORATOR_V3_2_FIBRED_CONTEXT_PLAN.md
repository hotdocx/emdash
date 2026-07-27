# TypeScript Fibred-Context And Displayed-Product Usability For emdash v3.2 — Living Sub-Plan

Date: 2026-07-27
Plan-ID: TS-ELAB-V3.2-FIBRED-CONTEXT
Depends-On:
[`TYPESCRIPT_ELABORATOR_V3_2_USABILITY_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_USABILITY_PLAN.md),
approved H-01/D-007 dependent-first semantics, approved
H-DTTLF-USABILITY-DEPENDENT/D-DTTLF-USABILITY-003, and completed
USABILITY-DEPENDENT-1A
Status: active implementation sub-plan; the corrected architectural direction
is user-accepted, FIBRED-PLAN-0 and the read-only FIBRED-PRODUCT-0A authority
probe are complete, FIBRED-CONTEXT-0A's dependency-analysis foundation is
complete, FIBRED-CONTEXT-0B's categorical representation adapter is complete,
FIBRED-PRODUCT-0B is the next dependency-ready comparison, and any new
Lambdapi mathematical owner or rule remains behind H-DTTLF-USABILITY-02
Infinity-Codex-Decision-Responses:
`infinity-codex:019f9243-9fba-7c73-861b-ff4eacf0c56c:019fa4cd-724e-7cc0-8f16-a32c82870ef1`
and
`infinity-codex:019f9243-9fba-7c73-861b-ff4eacf0c56c:019fa4fb-cd38-7ac1-87dc-829f004f77f5`
Human-Decision-Record: on 2026-07-27 the user accepted the consolidated
displayed-binder and corrected fibred-sibling analyses, requested this
dedicated plan and continued implementation, and separately cautioned that a
generic total-category pullback must not be assumed
FIBRED-CONTEXT-0A implementation checkpoint:
`d25ddb349e97dc0629cd6bc1aa941e1cc200066e`

## Purpose And Exact Outcome

This sub-plan closes the next end-user-usability architecture question left
open by the completed first-order categorical frontend:

- general ordered dependent telescopes must remain expressible;
- variables that are independent siblings over a common dependent base must
  receive a complete fibrewise-cartesian structural treatment;
- convenient displayed functor and displayed transfor binders must elaborate
  through active directed-DTT semantics rather than pointwise TypeScript-only
  shortcuts; and
- the frontend must retain enough dependency information to choose, compare,
  and transport sequential Sigma and grouped fibrewise-product
  presentations.

The plan does **not** assume that ordinary and displayed lowering use either
one implementation function or two. It selects the natural,
authority-correct, scalable/generalizable solution and allows shared generic
dependency machinery plus authority-specific lowerers wherever the evidence
requires them.

This is an implementation continuation, not a request to redesign the
outer dependent LF, the backend-neutral explicit Core, or the completed
ordinary bracket compiler. It also does not resume bulk Lambdapi acquisition,
select a string parser, promote a browser profile, or complete the deferred
groupoidal-DTT specialization.

## Consolidated Correction: Dependency Edges Versus Fibred Siblings

The decisive distinction is between exchange across a genuine dependency
edge and exchange of sibling variables sharing a dependency base.

Let:

```text
Δ := Γ, a : A
B, C : Catd Δ.
```

The dependency graph for:

```text
Γ, a : A, b : B(a), c : C(a)
```

is:

```text
    a
   / \
  b   c
```

The sequential context is more precisely:

```text
Δ.B.(πB* C),
```

because the family `C` over `Δ` is pulled back along the projection
`πB : Δ.B -> Δ` before introducing `c`. It should be related to a grouped
presentation:

```text
Δ.(B ×Δ C),
```

where the desired displayed product has fibres:

```text
(B ×Δ C)[a] = B[a] × C[a].
```

For this sibling case, weakening, pairing, symmetry, diagonal, associativity,
and terminal-unit structure are meaningful fibrewise operations:

- either sibling can be discarded by a displayed projection;
- two sibling terms can be paired;
- the siblings can be exchanged by fibrewise symmetry;
- a single sibling can be duplicated by a fibrewise diagonal when the
  classifiers agree after reindexing; and
- a larger independent sibling block can be grouped by iterated products.

By contrast, in:

```text
Γ, a : A, b : B(a), c : C(a,b),
```

the graph contains `a -> b -> c`. The family `C` is not a family over
`Γ.A` alone. There is no general `B × C` over that prefix and no blanket
exchange of `b` and `c`.

The corrected structural rule is therefore:

> Arbitrary dependent telescope entries are not freely permutable. Variables
> with no dependency path between them can be exchanged with the required
> classifier and suffix transport, and variables that are siblings over a
> common dependent base admit a coherent fibrewise-cartesian structural
> package.

This distinction is inherited from ordinary dependent type theory. The
categorical setting adds explicit object/arrow/higher-cell action and
therefore needs owner-backed directed computations, but it does not require a
second, incompatible notion of dependency.

## Two Complementary Foundations

The displayed contextual frontend needs both of these structures.

### Comprehension/Sigma structure for genuine dependency

For `A : Catd Γ`:

```text
Γ.A  := Sigma_cat A
wk_A := Sigma_proj1_func A.
```

The general dependent-telescope path uses:

- `Sigma_cat` for context extension;
- `Sigma_proj1_func` for weakening/projection;
- `Pullback_catd` and `Pullback_catd_func` for family substitution;
- `section_pullback_func` for section substitution;
- a qualified contextual-pairing map
  `⟨σ,t⟩ : Δ -> Sigma_cat A`; and
- dependency-sensitive exchange and contraction only where the relevant
  reindexing makes them well typed.

The active kernel does not yet package the complete general
comprehension-pairing and Sigma-introduction arrow-action story. The audit of
that gap remains a required later row; the frontend must not manufacture it.

### Cartesian structure in each fibre for independent siblings

For `B,C : Catd K`, the provisional package is:

```text
Product_catd B C : Catd K
```

with intended computations:

```text
Fibre_cat (Product_catd B C) k
  ↦ Product_cat (Fibre_cat B k) (Fibre_cat C k)

catd_transport_func (Product_catd B C) p
  ↦ Product_map_func
      (catd_transport_func B p)
      (catd_transport_func C p).
```

Its structural maps should be genuine displayed functors:

```text
projL : Functord (Product_catd B C) B
projR : Functord (Product_catd B C) C

pair  : Functord E B
      → Functord E C
      → Functord E (Product_catd B C)

swap  : Functord
          (Product_catd B C)
          (Product_catd C B)

diag  : Functord B (Product_catd B B).
```

The terminal displayed family:

```text
Const_catd K Terminal_cat
```

supplies the fibrewise unit and a terminal presentation of weakening.
Reindexing should preserve the package in the exact runtime or proof-time
orientation selected by an owner-position audit:

```text
σ*(Product_catd B C)
  ≡ Product_catd (σ*B) (σ*C).
```

No separate unrelated `weakd`, `symd`, and `diagd` theory should be invented.
If stable names are needed, they form one product/comprehension package whose
higher behavior is inherited from generic categorical action wherever the
active authority supports it.

## `Product_catd`, Product Normalization, And The Stable-Head Question

The active v3.2 kernel has no declaration named `Product_catd` or
`Productd_catd`. It does contain:

- `Product_cat`, its projections, pairing, swap, identities, and
  componentwise hom action;
- the ordinary codomain normalization:

  ```text
  Functor_cat X (Product_cat A B)
    ↦ Product_cat (Functor_cat X A) (Functor_cat X B);
  ```

- paired product-valued functors;
- `Product_map_func(F,G)` with object, full-hom, and capped-arrow action;
- the internalized `Product_cat_func`; and
- curry/uncurry plus generic composition.

The user's proposed analogy is meaningful, but its displayed-level spelling
must be type correct. `Product_catd B C` is a family `K -> Cat`, not itself a
category. The direct fibre consequence is:

```text
Functor_cat X (Fibre_cat (Product_catd B C) k)
  ↦ Product_cat
      (Functor_cat X (Fibre_cat B k))
      (Functor_cat X (Fibre_cat C k)).
```

The corresponding family-level classifier comparison is provisionally:

```text
Functord_cat E (Product_catd B C)
  ≡ Product_cat
      (Functord_cat E B)
      (Functord_cat E C).
```

That comparison is desirable because it makes displayed projection and
pairing structure visible to elaboration, but this plan does not yet choose
runtime rewriting, proof-time comparison, or derivation. The owner audit must
check subject reduction, projection iteration, higher hom action,
reindexing, and critical pairs before selecting an orientation.

### FIBRED-PRODUCT-0A probe result

A bounded ignored Lambdapi probe constructed the obvious transparent
candidate:

```text
Product_catd_probe(B,C)
  := uncurry(Product_cat_func) ∘ ⟨B,C⟩.
```

The probe established:

```text
Fibre_cat (Product_catd_probe B C) k
  ≡ Product_cat (Fibre_cat B k) (Fibre_cat C k)
```

by ordinary runtime conversion.

It also established the required negative:

```text
catd_transport_func (Product_catd_probe B C) p
  ≢ Product_map_func
      (catd_transport_func B p)
      (catd_transport_func C p)
```

under the current active reductions. The reason agrees with the kernel's
existing boundary: the transfor/hom action of semantic uncurry depends on a
higher arrow action of `Product_cat_func` that is deliberately deferred.

The successful probe is:

```text
emdash2/tmp/probes/typescript_usability_fibred_product_0a.lp
```

and its successful local log is
`emdash2/logs/probes/typescript_usability_fibred_product_0a-20260727-163429.log`.
Both paths are ignored experiment evidence; the result is durably recorded
here rather than making ignored files an authority.

This rules out claiming that the transparent alias already supplies the
required directed product. It leaves two principled implementation routes:

1. complete the generic higher action needed by `Product_cat_func` and
   semantic uncurry, then retain a transparent `Product_catd` facade if all
   computations and critical pairs join; or
2. add a narrow stable `Product_catd` semantic head with owned fibre and
   base-arrow projections, deriving its projections/pair/swap/diagonal from
   existing generic structure where possible.

A hybrid semantic definition plus one narrow stable transport facade is also
admissible if the owner-position probe demonstrates that it is the smallest
coherent boundary. The next product row must compare these routes. It may not
choose a primitive merely for notation, and it may not force the general
uncurry action solely to make one demo pass.

## Total-Category Comparison Is A Theorem Boundary, Not An Assumed Rewrite

The semantic slogan:

```text
Sigma_cat (Product_catd B C)
  ≃ Sigma_cat B ×K Sigma_cat C
```

explains the relationship between grouped and sequential contexts, but the
right-hand `×K` is **not** currently a generic active computational owner.

In particular, active `Pullback_catd E F` is asymmetric: it reindexes a
Cat-valued family `E` along a functor `F`. Its computational behavior relies
on the family/fibration presentation. It is not a symmetric pullback
constructor for arbitrary functors
`Sigma_cat B -> K <- Sigma_cat C`.

Therefore this plan:

- does not postulate a generic categorical pullback or a rewrite using
  notation `×K`;
- first compares sequential and grouped contexts through the explicit
  Sigma projections, family pullbacks, displayed product projections, and
  contextual pairing maps;
- treats any total-category equivalence as a later theorem/conformance row;
  and
- requires a separate Lambdapi owner-position design if a computational
  total pullback/comma construction becomes a concrete consumer.

This boundary does not weaken the fibrewise-product architecture. The
frontend can elaborate sibling grouping and structural maps directly at the
displayed-family level without first internalizing a generic total-category
pullback.

## Displayed Binder Taxonomy And Semantic Lowering

Binder spelling does not map one-to-one to kernel owners. The frontend tracks
at least these orthogonal axes:

- outer-LF versus categorical abstraction layer;
- plicity;
- variation capability (`object-only`, functorial, natural, or a later
  qualified capability);
- covariance/contravariance;
- cell level; and
- ordinary versus displayed dependency.

Consequently:

- outer LF `λ x : A. t` is checked against an LF `Π` and lowers to
  `KernelLambda`;
- ordinary `λ a :^f A. t` is convenient functorial categorical abstraction;
- `k :^n K` means natural/indexed variation and is not specifically a binder
  for `Transf_cat`; and
- provisional `:^fd` and `:^nd` are useful surface constraints/sugar, not new
  primitive Core binder kinds.

A displayed-functor abstraction:

```text
λ a :^fd E. body
```

semantically hides a telescope like:

```text
λ (k :^n K; a :^f E[k]). body[k,a].
```

It must produce fibre-arrow and base-arrow coherence, not merely a pointwise
object function. The active Sigma/Pi comparison gives the principled route:

```text
Pi_cat
  (Sigma_cat E)
  (Sigma_proj1_pullback_catd E D)
≡ Functord_cat E D
```

at proof time. The corresponding next-hom comparison reaches
`Transfd_cat`. Thus direct:

```text
λ a :^fd E. ...
```

and nested:

```text
λ k :^n K. λ a :^f E[k]. ...
```

may check against compatible stable classifier presentations. The frontend
must preserve which classifier it elaborated and let explicit Core
conversion/proof-time unification establish the comparison. It must never
turn a proof-time comparison into an unreviewed runtime rewrite.

The exact notation remains provisional. `:^nd` should mean construction of a
coherent displayed transfor at the expected `Transfd_cat` cell level, not
simply binding an object of an arbitrary displayed category.

## Dependency-Aware Contextual IR

The current categorical contextual IR records ordered slot uses and the
ordinary/displayed distinction, but not a general dependency graph. The
next foundation records, for every stored contextual slot:

```text
slot identity and ordered position
classifier
direct dependencies
transitive dependency closure
least ordered dependency prefix
source provenance
```

The reusable analysis must:

- recover dependencies structurally from locally nameless Core classifiers,
  including occurrences beneath internal binders;
- distinguish a genuine dependency edge from independent slots;
- identify siblings with the same minimal dependency base;
- identify independent slots that become siblings only after weakening to a
  common base;
- permit adjacent exchange exactly when no dependency path is crossed and
  enumerate the dependent suffix that must be transported;
- plan discard, single use, and repeated use as weakening/projection,
  identity, and diagonal/contraction respectively; and
- reject malformed, escaping, or dependency-crossing requests with exact
  provenance.

The generic outer-LF Core telescope already implements scoped weakening,
dependency-sensitive adjacent exchange, and contraction using explicit
ambient-index maps. This plan extends that evidence with an inspectable
dependency graph rather than building a second independent dependency
language. The categorical contextual builder can then adapt the same
analysis while emitting its additional Sigma/pullback/product/action owners.

Sequential and grouped surface presentations remain two views of this one
model:

```text
λ a. λ b : B(a). λ c : C(a). t

λ a. λ (b,c) : Product_catd(B,C)(a). t.
```

The compiler may retain the sequential Sigma telescope, choose a grouped
displayed product, or compare both, according to the expected classifier and
available active owners. It may not erase dependency evidence before
checking.

## Qualification Corpus

The architecture is not considered mechanically settled for general
displayed binding until the following bounded cases are executable:

1. direct displayed-functor identity, composition, and eta through a
   provisional typed `displayedFunctorLambda`/`:^fd` API;
2. displayed weakening: pull a section back to `Sigma_cat E`, then check the
   Sigma-section presentation against `Functord_cat E D`;
3. substitution stability: abstract before versus after reindexing along
   `σ`, using `Pullback_catd_func`;
4. a genuinely fibre-dependent target `B[k,a]`, using
   `Sigma_catd_functord_catd` and the internal/pullback-Pi package;
5. direct displayed-transfor abstraction plus `tdapp0_fapp0` and one
   `tdapp1_int_cell` consumer;
6. sibling product projections, pairing, swap, and diagonal over one
   dependent base;
7. positive exchange of independent siblings and required rejection across
   a genuine dependency edge;
8. sequential-versus-grouped context conformance without assuming a generic
   total-category pullback;
9. reindexing stability of the displayed product; and
10. an explicit audit of comprehension pairing and the deferred
    Sigma-introduction arrow action.

The already completed representation-only scale slices are reusable evidence:

- SCALE-STRESS-2A: Sigma/Pi telescope uncurrying;
- SCALE-STRESS-2B1/2B2: internal/pullback Pi plus base-arrow action; and
- SCALE-STRESS-2B3: Sigma-total displayed-transfor uncurrying.

They do not by themselves promote those comparisons into the active
usability profile.

## Implementation Ledger

| Slice | Status | Depends on | Exact bounded result |
| --- | --- | --- | --- |
| FIBRED-PLAN-0 | complete | accepted consolidated review | This dedicated plan records the dependency-edge/sibling correction, the two-foundation architecture, displayed-binder semantics, product and total-category boundaries, qualification corpus, gates, and persistent launch prompt |
| FIBRED-PRODUCT-0A | complete; ignored read-only probe | active v3.2 product, uncurry, Catd, and composition owners | The transparent `uncurry(Product_cat_func) ∘ ⟨B,C⟩` candidate computes to pointwise product fibres but deliberately does not compute its base-arrow transport to `Product_map_func`; no active source, owner, rule, or catalog changed |
| FIBRED-CONTEXT-0A | complete | FIBRED-PLAN-0 | Added backend-neutral dependency-graph inspection for persistent Core telescopes: dependencies are recovered beneath internal binders; direct/closure/prefix data, shared-base versus weakened siblings, genuine edges, exchange suffix transport, owner-neutral usage planning, exact provenance, fail-closed errors, immutability, and six focused tests are green |
| FIBRED-CONTEXT-0B | complete | FIBRED-CONTEXT-0A | Adapted the generic graph to categorical contextual slots through explicit locally nameless classifier references; represents genuine edges/chains, direct versus pullback-then-Sigma sequential extension, shared-base versus weakened sibling groups, grouped displayed-product structural intent, exact errors/provenance, and a zero-owner boundary without changing completed ordinary or D-003 behavior |
| FIBRED-PRODUCT-0B | pending | FIBRED-PRODUCT-0A, concrete first categorical consumer | Compare the generic-product-higher-action, stable-`Product_catd`, and narrow-hybrid owner positions in a bounded full-file probe; specify exact type, fibre/transport/projection consumers, non-collapse, higher-action boundary, rule orientation, warnings, and critical-pair risks |
| FIBRED-PRODUCT-1A | blocked on H-DTTLF-USABILITY-02 if a new owner/rule is selected | FIBRED-PRODUCT-0B and human approval | Implement only the approved active Lambdapi product package, synchronize checks/catalog/health, transfer the minimal exact closure through generic TypeScript mechanisms, and preserve frozen profiles |
| FIBRED-STRUCTURE-1 | pending | FIBRED-CONTEXT-0B, FIBRED-PRODUCT-1A or a proved existing-owner derivation | Lower displayed projection, pairing, swap, diagonal, and reindexing stability for independent siblings with positive, negative, and higher-action evidence |
| FIBRED-BINDER-1 | pending | FIBRED-STRUCTURE-1 and existing Sigma/Pi comparisons | Implement the first direct `:^fd`-equivalent typed API and show direct/nested classifier compatibility without collapsing proof-time and runtime equality |
| FIBRED-TRANSFD-1 | pending | FIBRED-BINDER-1 and transferred exact `Transfd` application closure | Implement one coherent displayed-transfor abstraction and component/higher-cell consumer |
| FIBRED-COMPREHENSION-1 | pending owner audit | FIBRED-CONTEXT-0B | Qualify contextual pairing and the deferred Sigma-introduction arrow action for genuinely dependent chains; return any missing mathematical owner to H-DTTLF-USABILITY-02 |
| FIBRED-GROUPED-SEQUENTIAL-1 | pending | FIBRED-STRUCTURE-1, FIBRED-COMPREHENSION-1 | Demonstrate sequential and grouped sibling syntax through one dependency-aware model and explicit owner-backed Core |
| FIBRED-TOTAL-COMPARE-1 | deferred theorem/owner boundary | concrete need after grouped/sequential success | State or implement the total-category comparison only with an exact active pullback/comma/equivalence construction; never treat notation `×K` as an existing generic computational owner |
| FIBRED-GRADUATE-1 | pending | complete qualification corpus | Freeze the exact supported envelope, residual owner/action gaps, mechanical-reuse assessment, TypeScript/Lambdapi conformance, and a separate human graduation decision |

## FIBRED-CONTEXT-0A Completion Record

The first implementation slice extends the existing generic locally nameless
Core rather than creating a categorical-only dependency language:

- `kernelAmbientDependencies` traverses arbitrary stored Core, distinguishes
  internal Pi/lambda binders from ambient telescope variables, and retains
  every dependency occurrence's provenance;
- `coreContextDependencyGraph` derives direct dependencies, transitive
  closure, and the least outermost-first dependency prefix from each
  persistent `CoreContext` binding type;
- adjacent exchange analysis distinguishes a genuine dependency edge from
  independent slots, classifies shared-minimal-base siblings versus siblings
  needing weakening, and names every later classifier whose dependency
  evidence must be transported;
- contiguous sibling-block analysis records common dependencies, required
  weakening, sequential pullback positions, and projection/pairing/exchange/
  diagonal intent without claiming a displayed implementation owner; and
- slot-use analysis maps zero, one, and repeated occurrences to
  projection/weakening, identity, and iterated diagonal/contraction intent.

The focused corpus covers:

```text
Γ, a : A, b : B(a), c : C(a), d : D(b,c)
```

including a dependency occurrence beneath an internal Core binder. It
accepts and classifies the `b,c` sibling block, records that exchanging it
requires transport of `d`, rejects the `c,d` dependency edge at the exact
stored occurrence, and separately detects a constant sibling that must be
weakened to the common base.

Implementation:
`src/v3_2/kernel.ts`,
`src/v3_2/context_dependencies.ts`, and
`tests/v3_2_context_dependency_tests.ts`.

Validation:

```text
./scripts/pnpmw run typecheck
  passed

node --require ts-node/register --test \
  tests/v3_2_context_dependency_tests.ts
  6 passed, 0 failed

./scripts/pnpmw run check:ts
  687 tests, 645 passed, 42 opt-in skipped, 0 failed

./scripts/pnpmw run check:all
  root gate passed
  19 mandatory live TypeScript/Lambdapi differential tests passed
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure and 5 print registry tests passed
  warning/LHS/catalog/health/book/reference gates passed
```

This slice emits no categorical owner, changes no runtime/profile semantics,
and does not claim that the categorical surface already stores the new graph.
That adaptation is exactly FIBRED-CONTEXT-0B.

## FIBRED-CONTEXT-0B Completion Record

The categorical adapter now turns first-order contextual classifier syntax
into the same generic dependency graph used by persistent outer-LF Core:

- categorical classifier references are nearest-first locally nameless
  indices with source provenance, not caller-maintained dependency flags;
- the generic graph constructor validates that every occurrence points
  strictly backward, merges repeated evidence, and derives direct
  dependencies, transitive closure, and the least ordered dependency prefix;
- closed slots and displayed-family applications are retained as distinct
  classifiers, while the already implemented one-index
  `indexed-object` classifier has an explicit compatibility adapter;
- sequential planning distinguishes direct Sigma extension from a family
  that must first be pulled back past intervening independent slots;
- grouping distinguishes siblings with the same minimal dependency base from
  independent factors needing weakening to a common base, and retains
  projection, pairing, exchange, and diagonal intent; and
- every grouped product remains explicitly
  `representation-only-owner-unqualified`: its semantic candidate name is
  `Product_catd`, but `selectedCoreOwner` is `null`, emitted-owner count is
  zero, and generic total-category pullback is false.

The executable corpus uses:

```text
Γ, a : A, b : B(a), c : C(a), d : D(b,c).
```

It records the sequential pullback of `C` past `b`, recognizes `b,c` as
shared-base siblings, records the grouped pointwise-product and
componentwise-base-arrow obligations, and rejects grouping `c,d` at the
exact occurrence where `D` depends on `c`. A second case recognizes a
constant displayed factor as independent only after weakening. Escaping
indices and incompatible base categories fail closed.

Implementation:
`src/v3_2/context_dependencies.ts`,
`src/v3_2/categorical_context_dependencies.ts`, and
`tests/v3_2_categorical_context_dependency_tests.ts`.

Validation:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw run lint
  passed

node --require ts-node/register --test \
  tests/v3_2_context_dependency_tests.ts \
  tests/v3_2_categorical_context_dependency_tests.ts
  13 passed, 0 failed

./scripts/pnpmw run check:ts
  694 tests, 652 passed, 42 opt-in skipped, 0 failed

./scripts/pnpmw run check:all
  passed, including 19 mandatory live differential tests,
  41 active Lambdapi kernel/example files, warning/LHS/catalog/health,
  print, book, and reference gates
```

This is an inspectable planning boundary, not a new surface elaboration
claim. The completed ordinary bracket and D-003 `FF[k](s[k])` lowerers are
unchanged. Concrete displayed product and contextual Sigma owners are
selected only by the subsequent authority-qualified rows.

## Human Review Gates

### Existing H-DTTLF-USABILITY-02 — New Mathematical Owner Or Rule

FIBRED-PRODUCT-0B and FIBRED-COMPREHENSION-1 may trigger the existing
usability owner gate. Before any active Lambdapi change, the proposal must
name:

- the exact owner position and whether it completes generic product/uncurry
  action, adds stable `Product_catd`, or uses a narrower semantic facade;
- the complete type and intended stable normal form;
- positive fibre, base-arrow, projection/pairing, reindexing, and relevant
  higher-action consumers;
- a non-collapse case;
- runtime versus proof-time orientation;
- subject-reduction, overlap, termination, and warning evidence;
- interaction with `Pullback_catd`, `Sigma_cat`, ordinary product, and
  product-map composition; and
- the minimal TypeScript transfer/profile effect.

The user accepted investigating this high-priority package, not an
unspecified primitive or rewrite. An exact decision ID and approval question
will be added only after FIBRED-PRODUCT-0B has enough evidence to choose a
bounded proposal.

### Future FIBRED-GRADUATE-1 — General Displayed Usability

Completing individual product or binder examples does not by itself settle
the general architecture. Graduation requires the executable corpus above,
an explicit unsupported-action table, and separate statements about:

- frontend dependency/binder scalability;
- mathematical displayed-owner coverage;
- bulk library transfer throughput;
- optional acquisition/parsing;
- groupoidal closure; and
- product/browser promotion.

## Acceptance And Validation Policy

FIBRED-CONTEXT-0A and FIBRED-CONTEXT-0B are complete only when:

1. dependencies are derived from stored locally nameless Core rather than
   user-maintained duplicate flags;
2. the sibling graph and genuine chain examples receive different,
   deterministic classifications;
3. independent exchange names the later dependent suffix needing transport;
4. use counts select projection/identity/diagonal intent without emitting an
   unqualified categorical owner;
5. invalid positions/counts fail closed;
6. all public records and arrays are immutable; and
7. the categorical adapter retains sequential pullback and grouped-product
   obligations while emitting no unapproved owner; and
8. focused tests plus `./scripts/pnpmw run check:ts` pass.

Any active Lambdapi edit follows `emdash2/AGENTS.md` and the current v3.2 SOP:
intended-owner full-file probe, positive and negative consumers, bounded
checks, warning comparison, strict LHS audit, catalog and health
synchronization, examples where affected, and full local CI before a
checkpoint. Every Lambdapi process remains bounded to at most 60 seconds.

This sub-plan inherits
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md).
The user's existing authorization permits local checkpoint commits only on
the existing `goal/typescript-elaborator-v3.2` branch/worktree after a bounded
coherent tranche is green, all linked ledgers/navigation are synchronized,
the exact staged diff excludes unrelated work, and
`git diff --cached --check` passes.

No push, merge, PR, publication, release, new branch/worktree, amend, rebase,
reset, history rewrite, cleanup, branch deletion, or worktree removal is
authorized.

## Persistent `/goal` Launch Prompt

```text
Kick off or continue implementing
docs/TYPESCRIPT_ELABORATOR_V3_2_FIBRED_CONTEXT_PLAN.md.

Treat its Persistent /goal Launch Prompt as part of the objective. Recover
actual state from active code and tests, this sub-plan and its ledger, the
linked usability/scale/DTT-LF/master plans, all Git worktrees and
staged/unstaged diffs, and the active authority order. Follow root AGENTS.md
and, for every emdash2 action, emdash2/AGENTS.md and the current v3.2 SOP.
Resume an in-progress row or select the next dependency-ready bounded
implementation slice. Produce executable evidence and synchronize all
affected living documents.

Preserve the exact frozen emdash-v3.2-mvp-1 profile, the reviewed root-only
emdash-v3.2-dttlf-directed-1 continuation, the outer dependent LF,
backend-neutral locally nameless explicit Core, generic checker/evaluator and
transfer engines, completed ordinary categorical bracket, completed indexed
section eta, and completed D-003 non-eta `FF[k](s[k])` composition witness.
Preserve H-01/D-007 dependent-first semantics. It requires contexts as
categories, types as displayed families, terms as sections, substitution as
functorial pullback, and only authority-classified ordinary constant-family
bridges. It requires neither one shared nor deliberately separate
ordinary/displayed TypeScript algorithm.

Implement both general dependent telescopes and fibrewise-cartesian structure
for independent siblings as two presentations in one dependency-aware
contextual architecture. Distinguish a genuine dependency edge from sibling
variables over a common dependent base. Reuse the generic locally nameless
Core telescope's dependency, weakening, exchange, contraction, scope, and
provenance mechanisms where sound; add categorical Sigma/pullback/product and
higher-action lowering only through active authority-backed owners.

Preserve FIBRED-PRODUCT-0A's exact result: the transparent
`uncurry(Product_cat_func) ∘ ⟨B,C⟩` candidate computes pointwise fibres but
does not currently compute base-arrow transport to `Product_map_func`.
Do not claim it is a completed directed displayed product. Compare completing
the generic Product/uncurry higher action, adding a narrow stable
`Product_catd` semantic head, and a minimal hybrid facade. Prefer semantic
definitions, but let concrete fibre/transport/projection/higher-action and
critical-pair evidence decide. Do not add or alter a Lambdapi owner or rule
without first preparing the exact H-DTTLF-USABILITY-02 proposal and obtaining
human approval.

Treat the ordinary `Functor_cat X (Product_cat A B)` rule as useful evidence,
not as an automatically valid family-level rule. Audit the meaningful
`Functord_cat E (Product_catd B C)` product comparison and choose runtime,
proof-time, or derived status only from typed evidence. Preserve stable
heads where higher projections require them; never add a primitive merely
for notation.

Do not assume a generic computational total-category pullback
`Sigma_cat B ×K Sigma_cat C`. Active `Pullback_catd E F` is asymmetric
family reindexing. First implement grouped/sequential sibling behavior through
explicit displayed products, Sigma projections, pullbacks, contextual
pairing, and structural maps. Defer any total-category equivalence until an
exact pullback/comma/equivalence owner or theorem is separately qualified.

Treat provisional `:^fd` and `:^nd` as ergonomic combinations of abstraction
layer, plicity, variation, polarity, cell level, and displayed dependency,
not primitive Core binder modes or one-to-one owner names. A displayed
functor binder must supply fibre-arrow and base-arrow coherence. Use the
active Sigma/Pi uncurrying comparison to relate total-context sections to
`Functord_cat`, and the next-hom comparison to reach `Transfd_cat`; preserve
direct and nested classifier presentations and never turn proof-time
comparisons into runtime rewrites.

Keep canonical Lambdapi term/declaration parsing deferred and optional.
Direct typed TypeScript construction remains the default. Do not resume the
70-root/83-extension transfer closure, promote a browser/product profile,
claim complete groupoidal DTT, or broaden metatheory as a side effect of this
usability tranche.

Recover the actual descendant HEAD. Named baselines and checkpoints are
comparison/backtracking evidence, never permission to reset or rewrite.
Existing authorization permits local checkpoint commits only on the existing
goal branch after a bounded green tranche, synchronized ledgers/navigation,
exact staged-diff review, and `git diff --cached --check`. It authorizes no
push, merge, PR, publication, release, new branch/worktree, amend, rebase,
reset, cleanup, or deletion.

When a row reaches a human mathematical gate, record the exact evidence and
approval question, continue any independent dependency-ready row, and never
guess the missing rule. Keep every Lambdapi process bounded to at most 60
seconds and run all proportional warning, audit, catalog, health, example,
conformance, and CI obligations.
```

## Change Log

- **2026-07-27 — Dedicated fibred-context plan created.** Integrated the
  accepted displayed-binder analysis and the corrected distinction between
  dependency-chain exchange and fibrewise-cartesian sibling structure.
  Recorded the two complementary comprehension/product foundations,
  provisional `fd`/`nd` semantics, dependency-aware contextual IR, stress
  corpus, product owner gate, and total-category non-assumption.
- **2026-07-27 — Transparent displayed-product derivation measured.** A
  bounded ignored probe showed that
  `uncurry(Product_cat_func) ∘ ⟨B,C⟩` computes the desired pointwise fibre but
  not the desired `Product_map_func` base-arrow transport. The plan therefore
  retains generic higher-action and stable-head alternatives and authorizes
  neither active kernel change without H-DTTLF-USABILITY-02.
- **2026-07-27 — FIBRED-CONTEXT-0A completed.** Added generic locally nameless
  dependency-occurrence inspection and an immutable persistent-context graph
  with sibling/edge, weakening, exchange-suffix, and structural-use analysis.
  Six focused tests distinguish the accepted sibling and rejected chain
  examples without emitting or selecting a displayed product owner.
- **2026-07-27 — FIBRED-CONTEXT-0B completed.** Generalized the dependency
  graph over syntax-specific binding evidence and adapted categorical
  contextual classifiers to it. Seven focused cases now preserve genuine
  chains, sequential pullback intent, shared-base and weakened sibling
  grouping, structural obligations, provenance, immutability, and the
  explicit zero-owner/zero-total-pullback boundary. FIBRED-PRODUCT-0B is now
  the next comparison row.
