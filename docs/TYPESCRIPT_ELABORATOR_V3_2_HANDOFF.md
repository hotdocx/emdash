# TypeScript Elaborator For Emdash v3.2 — Start Here

Date: 2026-07-24
Status: the exact `emdash-v3.2-mvp-1` TypeScript runtime profile is graduated;
RELEASE-READY is complete, with mandatory conformance, final residual and
performance boundaries, and all validation gates recorded; forward outer-LF
and directed-DTT work has additionally graduated the exact root-only opt-in
`emdash-v3.2-dttlf-directed-1` continuation profile under H-DTTLF-03;
systematic whole-development transfer remains unqualified and is now the
subject of the active scale-qualification plan, whose shared transfer IR
SCALE-0B and generic declaration/runtime/proof compiler slices SCALE-0C
through SCALE-0E plus generic prior-runtime-fragment composition
SCALE-RUNTIME-DEPS-1 are complete; H-DTTLF-SCALE-02/D-DTTLF-SCALE-002 is
approved; the exact frozen engine review and SCALE-ACQUIRE-1A checked
canonical-command adapter/contracts are complete; representation-only
SCALE-STRESS-1A now covers the exact J/Pi/Sigma/Nat corpus and identifies
generic inductive compilation plus source-ordered mixed-phase planning as its
engine gaps; signature-only SCALE-INDUCTIVE-1A and source-order/runtime
composition SCALE-MIXED-PHASE-1A plus same-runtime-prefix proof composition
SCALE-MIXED-PHASE-1B and completed-signature proof execution
SCALE-MIXED-PHASE-1C are now complete; the mixed-phase parent is closed, the
dependency-closed SCALE-STRESS-1B proposal preparation and isolated
TypeScript/Lambdapi evidence are now complete; the exact
H-DTTLF-SCALE-STRESS-01 decision is pending; independent representation-only
SCALE-STRESS-2A now pins and executes the active Sigma/Pi uncurrying proof
rule in an isolated TypeScript program, with bounded Lambdapi agreement and
generic source-ordered SCALE-PROOF-CONSTRAINTS-1 now closes its dependent
generated-constraint typing gap without an oracle; generic
SCALE-MIXED-RUNTIME-PREFIX-1 now supplies an explicit immutable same-module
runtime lineage to later mixed continuations; representation-only
SCALE-STRESS-2B1 now compiles and executes the internal/pullback dependent-Pi
object, fold, and pointwise-component package over that exact lineage, and
representation-only SCALE-STRESS-2B2 extends it through both base-arrow-action
clauses without a generic engine change; representation-only
SCALE-STRESS-2B3 now pins and executes Sigma-total displayed-transfor
uncurrying, completing the selected SCALE-STRESS-2/2B qualification parent;
generated induction semantics, integrated batch deduplication, further
mechanism stress, plus the outer-LF TYPE/KIND Π-formation boundary remain
explicit later work before any newly promoted active stress profile or
whole-transfer claim

## Purpose

This document prepares the next fresh conversation to work from the Git root
on a TypeScript elaborator for the active emdash v3.2 Lambdapi kernel. It is a
handoff and design boundary, not a claim that the existing TypeScript category
layer already implements v3.2.

The first checked vertical slice now lives under `../src/v3_2/`, with its
evidence, architecture reassessment, validation record, and human review
points in
[`TYPESCRIPT_ELABORATOR_V3_2_ELAB_0_RFC.md`](./TYPESCRIPT_ELABORATOR_V3_2_ELAB_0_RFC.md).
The completed profile is governed historically by
[`TYPESCRIPT_ELABORATOR_V3_2_MASTER_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_MASTER_PLAN.md).
The exact implemented outer-LF and directed-DTT continuation is recorded by
[`TYPESCRIPT_ELABORATOR_V3_2_DTT_LF_CONTINUATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_DTT_LF_CONTINUATION_PLAN.md).
Forward systematic-transfer work is governed by
[`TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md).
Long-running goal branches and checkpoints follow
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md).

The intended word *syntax* is broad. Users may construct a typed surface AST
with ordinary TypeScript expressions; a string parser can be added later. The
first architectural problem is elaboration and compilation into explicit
emdash Core applications, not tokenization.

The scale plan's approved initial transfer path likewise uses a shared typed
TypeScript builder rather than a string parser. Canonical export remains a
separate developer/build inventory, drift, extraction, and conformance tool;
a fail-closed canonical term/pattern parser may later feed the same transfer
IR if bulk-acquisition evidence justifies it. Neither path is the optional
user-facing source parser or changes this surface-design boundary.

## Authority Boundary

Read these in order before selecting a semantic target:

1. `../emdash2/emdash3_2.lp` — active definitions and computation;
2. the four active one-way extension modules named in
   `../emdash2/AGENTS.md`;
3. `../emdash2/emdash3_2_checks.lp` — executable regression statements;
4. `../emdash2/reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`;
5. `../emdash2/reports/EMDASH_FOUNDATIONS.md`;
6. `../emdash2/reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`;
7. the active task plan selected through `../emdash2/reports/INDEX.md`;
8. `TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md` for the active
   systematic-transfer implementation ledger, subordinate to the
   mathematical sources above;
9. `TYPESCRIPT_ELABORATOR_V3_2_DTT_LF_CONTINUATION_PLAN.md` for the reviewed
   outer-LF/directed-profile implementation history;
10. `TYPESCRIPT_ELABORATOR_V3_2_MASTER_PLAN.md` for the completed exact-profile
    history.

The root `src/` implementation predates the current kernel. Its generic
elaboration machinery is feasibility evidence, but names such as
`FunctorTypeTerm`, `MkFunctorTerm`, `NatTransTypeTerm`, and the built-in
category rules do not define the v3.2 target. Do not port the active kernel
backward into those nodes piecemeal or recreate retired compatibility names.

## Intended Trust And Compilation Boundary

The selected implementation direction is:

```text
TypeScript surface AST (string parsing optional)
        ↓ scope, constraints, binder roles, and implicit recovery
backend-neutral explicit emdash Core IR
        ├──→ small TypeScript checker/evaluator
        │       ↓
        │    authoritative deployed kernel for
        │    exactly emdash-v3.2-mvp-1
        │
        └──→ deterministic Lambdapi conformance emitter
                ↓
             mandatory bounded differential CI
```

H-05/D-039 passed the explicit parity/trust graduation gate. TypeScript is now
the authoritative deployed checker/evaluator only for the content-pinned
`emdash-v3.2-mvp-1` manifest (16 owners and three runtime rules), through the
browser-safe entry point. Lambdapi remains the active mathematical
specification, required fixed-corpus CI and subject-reduction oracle, and
acceptance authority for five selected semantic-boundary changes. It is not a
per-term or production runtime dependency.

Those five changes are selected owner signatures; selected runtime-rule shape
or authority; promotion of an owner or rule into the product profile;
termination, confluence, or subject-reduction claims; and shared-corpus
backend bindings. Implementation refactors, surface/diagnostic changes, and
packaging changes that preserve the frozen semantic/import boundaries do not
need a new declaration-level authority review.

General confluence remains withheld, as does standalone TypeScript subject
reduction. No performance SLA is authorized. `CORE_MVP_RELEASE_POLICY` records
this boundary without mutating the historical H-03 manifest or H-05 approval.
The typed AST is the supported construction path; a string parser remains
unimplemented, and neither H-02 nor H-06 is triggered by this release.

`CORE_MVP_RELEASE_COMPLETION` is the separate final record. It marks only the
exact profile release-ready, retains the older proposal/review/policy records
unchanged, and records zero release blockers. The checker's 256-step budget is
a global rewrite-operation bound, not a wall-clock, latency, throughput, or
scale promise. Representative workload measurement plus separate review is
required before making any future performance claim.

Separately, H-DTTLF-03/D-DTTLF-001 authorizes the exact
`emdash-v3.2-dttlf-directed-1` checker/evaluator only through the root
`src/v3_2/index.ts` continuation API. Its named factory is
`createCoreDirectedContinuationKernel()`. The dependency-closed profile has
20 base signatures plus nine reviewed candidate declarations, seven directed
plus three inherited MVP runtime rules, zero proof-time rules, and one shared
256-step outer-LF budget. It is not imported by `browser.ts`, does not alter
the deployed MVP identity, is not release-ready, and has no production
Lambdapi dependency.

The continuation's fixed TypeScript/Lambdapi positive, negative, and
subject-reduction witnesses are mandatory through
`./scripts/pnpmw run check:directed-conformance`. The aggregate
`./scripts/pnpmw run check:continuation` first preserves the frozen MVP
`check:all` gate and then runs that separate corpus. Combined termination,
unrestricted normalization, confluence, standalone TypeScript subject
reduction, performance, release, internal-Pi/uncurrying, and systematic
groupoidal-closure claims remain withheld.

The continuation proves the foundational spine, not a full import
architecture: 29 signatures, ten runtime rules, and zero proof-time rules are
far smaller than the active module/rule/unification landscape. The scale plan
therefore tests one backend-neutral typed module/fragment IR, generic
declaration/runtime/proof engines, and a representative mechanism corpus
before any claim that future transfers are systematic or mechanical.
SCALE-0B now implements and validates that immutable IR, scoped direct
builder, body distinctions, separate runtime/proof programs, and separate
policy overlay without semantically installing its active witnesses.
SCALE-0C now compiles all 29 reviewed signatures through one generic
declaration engine: 20 existing Core owners are checked intrinsically and the
nine continuation declarations reproduce the reviewed catalog exactly from
separate typed module, policy, and linkage data. The existing continuation
factory and authority remain unchanged. SCALE-0D now compiles the exact ten
reviewed rules through one owner-agnostic typed matcher and reaches a stable
generic declaration/runtime fixed point. All ten rewrites and near misses
agree with the reviewed runtime; six pass strict TypeScript subject checking,
while the nested Sigma-fibre rule and three frozen MVP rules retain their
exact approved Lambdapi-oracle boundary. No missing `Const_catd` reduction was
promoted. SCALE-0E now adds a separate owner-agnostic typed proof-rule
compiler and bounded symmetric constraint engine over representation-only
fixtures. It preserves source order, matched/fresh roles, one shared budget,
session-local Miller assignments, runtime separation, and fail-closed
wildcard/higher-order boundaries without promoting the existing active
`Obj(Hom_cat ...)` witness or claiming all-61-rule coverage.
SCALE-RUNTIME-DEPS-1 now adds explicit dependency-module and earlier-fragment
runtime closure, deterministic transitive flattening/diamond deduplication,
prefix subject checking, shared execution budgets, and fail-closed
relation/order/cycle/rule-ID validation. A synthetic dependent type witness
passes only with its explicit prior runtime; no missing active `Const_catd`
rule was imported. H-DTTLF-SCALE-02/D-DTTLF-SCALE-002 is now approved and
frozen separately. It selects direct typed specifications plus small
fail-closed checked extraction adapters while deferring a complete canonical
term/pattern parser. SCALE-ACQUIRE-1A implements the first such root-only
adapter: it checks source/export/version/import/ordinal/kind/metadata/digest
contracts and selects the exact outer-J, decoded groupoidal Pi/Sigma, and
imported grouped-Nat canonical commands. It parses no terms, grants no
semantic policy, invokes no production Lambdapi, and remains outside the
browser. Representation-only SCALE-STRESS-1A now lowers all selected commands
into immutable mixed typed specs: J and Sigma source wildcards become typed
left-bound/right-unused motives, the Pi beta retains its dependent binder RHS,
and imported Nat retains one ordered three-clause recursive group. All
entries remain conformance-only. The executable refusal isolates generic
inductive compilation and generic source-order phase planning, rather than a
category-owner exception, as the next two infrastructure rows.
SCALE-INDUCTIVE-1A now supplies the first of those pieces as generic
signature erasure: it validates and lowers heads/constructors through the
existing declaration compiler, keeps generated eliminator identities
untyped, and fails closed if one is consumed. The active `τΣ_` shape compiles
only under a test-only opaque overlay; production policy remains
conformance-only. Positivity, recursive/indexed induction, and generated
eliminator semantics remain SCALE-INDUCTIVE-1B.

That tranche also exposed a separate outer-LF boundary: the current checker
rejects `Π A : TYPE, ...` because the binder annotation `TYPE` has sort
`KIND`. This is a product-sort question, not an assertion that
`TYPE : TYPE`; no checker semantics changed. SCALE-KIND-PI-1 and
H-DTTLF-LF-SORT-01 must settle the Lambdapi-aligned rule before arbitrary
polymorphic-signature transfer can be claimed. The active Sigma signature
does not require that rule.

SCALE-MIXED-PHASE-1A now supplies the second representation-time engine gap.
Its generic immutable planner produces exact source-order phase fragments,
keeps grouped runtime clauses atomic, projects one module-wide linkage,
threads the declaration environment, and composes dependency-module and
same-module runtime prefixes before calling the existing four compilers. The
core stress module becomes seven phases and imported Nat becomes a
declaration plus one ordered three-clause runtime phase; all policies remain
conformance-only. A synthetic four-kind module and a separate importing
consumer compile and execute without owner-specific orchestration.
SCALE-MIXED-PHASE-1B now composes source-separated proof phases that share
one exact runtime prefix. Their checked rules execute through one global
priority order, queue, metavariable session, generated-constraint schedule,
and comparison budget while the individual phase programs remain available
as exact compile evidence. A later module runtime is not silently visible to
that 1B source-prefix program.

SCALE-MIXED-PHASE-1C subsequently measured Lambdapi's command-order
semantics: the same typed proof witness fails before a required runtime rule
and succeeds after it, even though its `unif_rule` was registered earlier.
The final TypeScript view therefore uses the completed module's declaration
context and runtime, but accepts that runtime only when every source-time
runtime is an exact object-identical fragment prefix. Individual source
programs remain unchanged; one final program covers single or separated
proof phases under the existing shared priority/session/budget design.
Shorter or foreign runtime lineage fails closed, and no mutable global
registry was restored. The new bounded `check:scale-phase-conformance` lane
pins the Lambdapi positive/negative witness. The mixed-phase parent is
complete.

SCALE-STRESS-1B-PREP has now prepared the exact dependency-closed proposal.
The core selection adds pinned equality/reflexivity and native-Nat
dependencies before the acquired J/Pi/Sigma commands, then imports the
existing grouped-`nat_add` representation. Stress compilation found and
fixed only generic representation/orchestration gaps: the implicit `ind_eqr`
endpoint, constructor-local inherited-parameter modes required by
`Struct_sigma [a P]`, and preservation of intrinsic external linkage into
later mixed runtime/proof phases. All twelve proposed free signatures and
seven runtime rules compile; every runtime rule is TypeScript subject-checked
without an exception oracle. Isolated TypeScript guard/binder/priority
witnesses and a bounded Lambdapi positive/negative probe pass.

`CORE_LF_SCALE_STRESS_1B_PROPOSAL` remains a non-active root-development
review artifact. It withholds `ind_nat` and `ind_τΣ_`, changes no browser,
default, MVP, directed-continuation, or Lambdapi profile, and deliberately
does not merge duplicate `τΣ_`/`Struct_sigma` ownership with the reviewed
29-signature continuation. The exact next question is
H-DTTLF-SCALE-STRESS-01/D-DTTLF-SCALE-STRESS-001; no active stress profile
exists until that separate human review is approved.

Independent SCALE-STRESS-2A is nevertheless complete under the already
approved representation/engine boundary. It pins `Catd`,
`Functord_cat`, `Pi_cat`, `Sigma_cat`,
`Sigma_proj1_pullback_catd`, and the active Sigma-section uncurrying
`unif_rule`; reuses the reviewed continuation linkage for existing heads;
and compiles only transparent `Catd`, opaque
`Sigma_proj1_pullback_catd`, and one isolated proof-time rule. The generic
engine solves forward and symmetric positive witnesses and leaves a changed
dependent target stuck, matching a bounded Lambdapi positive/negative
consumer. Mixed declaration/proof-only extension now explicitly carries the
initial checking runtime and rejects any attempt to use a raw runtime as a
local runtime-fragment dependency.

SCALE-PROOF-CONSTRAINTS-1 has since removed that rule's exact typing oracle.
The proof compiler checks each generated equality under its accepted source
prefix and reflects only a direct capture equality to a replacement using
strictly earlier captures as an acyclic transparent checking alias. It
rebuilds the complete synthetic variable telescope through the same checked
declaration/runtime path; wrong source order and all still-heterogeneous
constraints fail closed. The Sigma/Pi rule records `K2 := K`, `R2 := R`, and
`D2 := D` in immutable typing evidence. This remains isolated executable
evidence, not an active proof-rule registration, general equality
reflection, or a mechanical-transfer qualification.

SCALE-MIXED-RUNTIME-PREFIX-1 closes the complementary runtime-bearing seam.
A mixed module may receive an explicit distinct same-module
`earlier-fragment` after its ordered dependency-module fragments. The
flattened object-identical closure checks intervening declarations,
inductive signatures, and proofs and prefixes every new local runtime phase.
Raw initial runtime plus fragment evidence, misclassified or foreign
relations, duplicates, and order drift fail closed. This is generic
orchestration only: no active declaration, rule, profile, or browser surface
changed.

SCALE-STRESS-2B1 exercises that seam with the first internal/pullback
dependent-Pi runtime continuation. One checked acquisition contract pins 18
exact active commands. The direct typed module reuses `Const_catd` and the
SCALE-STRESS-2A/reviewed-continuation declarations by qualified identity,
then compiles eight additional declarations and nine source-ordered rules
against the exact reviewed ten-rule same-module runtime prefix. Every clause
executes, and bounded Lambdapi acquisition, positive reduction,
non-conversion, and rejected-conversion evidence agrees.

`Functord` is checked transparently. The exact transparent
`Catd_cat_func` body opens a separate composition/functor-category closure,
so 2B1 retains its checked type opaquely. Six rule subjects are fully
TypeScript-checked; the internal-Pi component, pullback fold, and pullback
component keep exact self-invalidating Lambdapi normalization oracles.
Nothing is activated in a default, reviewed, MVP, browser, or product
profile.

SCALE-STRESS-2B2 then pins the smallest exact eight-command base-arrow-action
selection, compiles six declarations and both `fdapp1_int_cell` clauses after
the exact 19-rule 2B1 runtime, and executes both clauses in TypeScript.
`Fibre_cat` retains its transparent body. The two displayed-transport bodies
open a distinct computation closure and remain opaque, so both exact subjects
retain self-invalidating Lambdapi normalization oracles. Live acquisition,
unfolding, reduction, non-conversion, and rejected-conversion evidence agree.
This is a data/policy-only extension: no generic engine or active profile
changed.

SCALE-STRESS-2B3 then pins eight exact commands, reuses the reviewed
`Sigma_catd_functord_catd` declaration and fibre rule by identity, and adds
five declarations plus the `Sigma_transfd_funcd` object-component clause
after the exact 21-rule 2B2 lineage. `Transfd` is checked transparently.
`Fibre_func`'s exact body crosses a still-uninternalized Cat-valued
`Functord`/`Transf` conversion seam, so that body and the component subject
retain one exact opaque/self-invalidating-oracle boundary. The clause
executes, and live unfolding, reduction, non-conversion, and rejection agree
with Lambdapi. No generic engine or active profile changed. The selected
SCALE-STRESS-2/2B parent is complete as representation evidence;
SCALE-STRESS-3 is the next mechanism audit.

The TypeScript layer may recover omitted categories, endpoints, variances,
binder modes, and implicit arguments, and should produce useful constraints
and diagnostics. It must not silently invent functorial action, naturality, a
missing higher cell, or a displayed-to-ordinary equivalence that the active
design does not provide.

The Core IR should remain small and mechanical: variables, binders,
applications/classifiers described by audited owner schemas, explicit
semantically relevant arguments, and source/provenance metadata. Surface
macros and customized TypeScript automation live outside its trusted checker.

## What May Be Reused

Audit before retaining or deleting anything. Likely reusable mechanisms are:

- the generic `Term`/binder representation, or lessons from it;
- bidirectional `infer`/`check` organization;
- holes, constraint collection, occurs checking, and higher-order pattern
  unification;
- rewrite/unification separation as an implementation pattern;
- source-independent proof-state traversal;
- test harness organization and direct TypeScript AST construction.

Required redesign/replacement boundaries are:

- all hard-coded one-category constructors and their implicit-slot tables;
- the old `MkFunctorTerm` proof/coherence contract;
- built-in `Set`, ordinary natural-transformation, and hom-functor reductions;
- any claim that the TypeScript normalizer is the authority for v3.2;
- the parser grammar, until the typed AST and lowering contract stabilize.

The old category-specific code is intended for deletion, not compatibility
maintenance. Remove it after an inventory maps each retained test to a
reusable generic invariant or a current v3.2 consumer and replacement checks
exist. A wholesale first deletion would erase useful executable evidence and
make regressions difficult to classify; this sequencing does not grant the
old API a permanent place.

## Implemented Wiring Tranche

The ELAB-0 RFC and isolated `src/v3_2/` implementation now cover this first
vertical slice:

1. define a minimal source-located TypeScript surface AST and a distinct
   explicit kernel-target AST;
2. model explicit, implicit, functorial, natural, and object-only binder modes
   without committing to a string notation;
3. lower one small current family—preferably ordinary `fapp0`,
   `fapp1_fapp0`, and `tapp1_fapp0` applications—using symbol names and types
   relocated from the active kernel;
4. serialize the result into a focused `.lp` probe that imports the active
   owner and is accepted or rejected by Lambdapi as expected;
5. include one positive omission-recovery case and one wrong-endpoint or
   wrong-binder-mode negative case;
6. keep the existing prototype baseline passing until the master plan reaches
   an explicit migration or replacement boundary.

This slice is deliberately end to end. A larger AST taxonomy without a checked
Lambdapi consumer would not yet demonstrate an elaborator.

It is nevertheless only a wiring spike. It omits the diagonal transfor
component `tapp0_fapp0`, all full/uncapped owners (`fapp1_func`,
`tapp0_func`, and `tapp1_func`), recursive higher-cell action, `hom_int`,
displayed/dependent contexts, metavariables, and conversion. Do not extend its
three-case switch as the architecture; implement the schema-driven next slice
recorded in the master plan.

## Forward Stress Tests And Review Boundaries

The plan now requires these early stress tests:

- the complete full/capped projection ladder, including the previously omitted
  `tapp0_fapp0`;
- recursive `fapp1_func` action at the next hom level, rather than a special
  one-category or `fapp2` case;
- partial application/internalization through `hom_int` and `hom_con_int`;
- a dependent-first context experiment using `Catd`, `Pullback_catd`,
  `Const_catd`, and `Pi_cat`;
- weakening, dependency-permitted exchange, and contraction with explicit
  distinction between telescope operations, ordinary structural functors,
  displayed owners, and shape reindexing;
- positive and non-collapse comparisons between effectively nondependent
  displayed routes and optimized ordinary routes.

General displayed weakening/exchange/contraction is not presumed to exist.
Record a concrete elaboration consumer and failed owner-position probe before
proposing a kernel addition, then follow the complete nested SOP. The precise
dependent encoding, displayed structural owners, TypeScript MVP fragment, and
kernel-graduation claim remain human review gates in the master plan.

Do not mix these decisions with a physical monorepo split or restoration of
the retired D0/D1 compatibility layer.

## Worktree And Validation Workflow

From a fresh worktree rooted anywhere on the same disk:

```bash
./scripts/bootstrap-worktree.sh
./scripts/pnpmw run check:ts
EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
```

The bootstrap creates a local dependency-link graph from the machine-wide pnpm
content-addressable store. It does not share mutable `node_modules` directories
between branches.

During implementation, use focused TypeScript tests first. For every emitted
kernel form, use `emdash2/scripts/probe.sh` with a bounded temporary consumer,
then broaden to `make -C emdash2 check`. Run
`./scripts/pnpmw run check:conformance` to exercise the exact frozen shared
corpus against Lambdapi with no opt-in skips. Run
`./scripts/pnpmw run check:all` before handing off a substantial cross-layer
change; it includes that mandatory conformance command before full kernel CI.

For a persistent goal, use a dedicated branch/worktree and the checkpoint
authorization and recovery rules in
`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`. Persistence alone does not authorize
any Git mutation.

## Start The Long-Running Implementation

Use the ready-to-paste **Persistent `/goal` Launch Prompt** at the end of
`TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md`. It names the
completed-profile and reviewed-continuation comparison checkpoints, selects
the next dependency-ready implementation slice, and records the
continuation's Git boundary. The completed master plan's historical
checkpoint authorization does not authorize unrelated Git mutations.
