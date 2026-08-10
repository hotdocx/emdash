# TypeScript Elaborator v3.2 PathInd Trusted-Profile And PathOut Library Plan

Status: active selected standard-library continuation under
`TS-EMDASH-PROOF-ASSISTANT`; `PATHOUT-TRUST-BOUNDARY-0A` is complete and the
v2 `PATHOUT-LIBRARY-FOUNDATION-1B0` review is superseded by measured
counterevidence; non-authorizing proposal v3 selects the reviewed direct-
mixed-source-action predecessor and awaits its own separate review before
root-only `PATHOUT-LIBRARY-FOUNDATION-1B` resumes; no PathOut semantic or
public export is yet implemented

Authority: `emdash2/emdash3_2.lp`, especially its representable, fibre-
covariance, directed-Sigma, PathOut, PathInd, and transitivity sections;
`emdash2/emdash3_2_checks.lp` supplies the executable regression statements

## Purpose

Expose outgoing paths, fixed-source path induction, its internally varying-
source packaging, and the transitivity benchmark through two deliberately
separate layers: a sealed, vetted TypeScript emdash v3.2 theory profile for
existing opaque semantic owners and their computation/proof rules, followed
by an end-user standard library of transparent definitions and proof terms.
The eventual reviewer demonstration consumes both layers without hiding their
different trust status.

This is not a proposal for another TypeScript meta-kernel, another binder
architecture, or a Lambdapi-source parser. It is a trusted-profile and
library-integration plan over the completed dependent LF, explicit emdash
Core, generic declaration and rule compilers, and recursive categorical
construction surface. The historical filename is retained so existing plan
links remain stable; "standard library" in that filename does not place the
opaque PathInd rules inside the end-user library.

## Activation And Product Selection

The 2026-08-10 `POST-14B-AUDIT-16` review in
[`TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md`](./TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md)
selects this as the first curated TypeScript/emdash mathematical product
profile. This is a consumer-backed selection, not promotion by filename:

- the checked Emdash book already uses PathOut, its canonical reflexive-to-
  path arrow, fixed/varying-source arrow induction, and the transitivity
  benchmark as a central mathematical narrative;
- the existing research-overview artifact already identifies PathOut/PathInd
  diagram owners; and
- the public `@hotdocx/emdash@0.2.0` package supplies a verified distribution
  boundary but currently exports no PathOut/PathInd library.

The selection deliberately excludes the isolated Nat/generated-owner and
scale/stress profiles. Those are valuable mechanism evidence for a later
curated prelude, but they are not a public library and have no current product
consumer selecting their exact authority closure.

The active source inputs at selection time are pinned by byte digest:

```text
emdash2/emdash3_2.lp
  0a117742d326bad82fe72cc73c624a0c174e3b48dd4047ebd8f6ed6ff7837860
emdash2/emdash3_2_checks.lp
  fbbe7ed4b7675c46ad79f65e2f6799dfc3c87b9287b593e6f1f0e1bd8e37f26a
```

These identify audit input only. Owner-position inspection, exact dependency
closure, TypeScript checking, and a bounded Lambdapi oracle remain required
before any trusted profile or derived definition is claimed.

The rollback-safe activation/product-selection checkpoint is `fb65a80`.
`PATHOUT-TRUST-BOUNDARY-0A` must remain a descendant of that exact decision
unless a later human direction supersedes the selected profile.

## Architectural Verdict And Trust Boundary

The PathOut development separates into four layers.

1. The **generic TypeScript meta-kernel** checks dependent declarations,
   transparent definitions, runtime rules, proof-time comparisons, and
   explicit Core. It gains no PathInd-specific Core node, evaluator case, or
   checker branch.
2. A sealed **trusted emdash v3.2 theory profile** faithfully transfers the
   active authority's opaque semantic owners and the exact runtime/proof rules
   that specify their computation. Those declarations are data consumed by
   the generic meta-kernel, but they remain part of the trusted calculus.
3. The **end-user standard library** contains transparent definitions and
   checked proof terms constructed from the trusted profile. Its ordinary
   safe interface does not register new rewrite or unification rules.
4. Thin **typed, text, and reviewer facades** present the resulting library;
   they add no semantic engine.

Exact transcription plus the bounded Lambdapi oracle establishes fidelity to
the vetted active authority. It does not turn opaque owners or conversion
rules into end-user-derived theorems. Conversely, keeping those rules in a
sealed profile need not hard-code PathInd into the generic TypeScript
implementation.

### Standard-library definitions over existing owners

The following named constructions are transparent compositions in the active
authority and can be authored directly in TypeScript from existing emdash
owners:

- `Rep_catd_func`, `Rep_catd`, and `Rep_transport_func` from `hom_int`, the
  identity functor, and generic action;
- `PathOut_cat`, `PathOut_cat_func`, and `PathOut_transport_func` from
  `Sigma_cat`, `Sigma_func`, and representable action;
- `pathout_obj`, `pathout_refl_obj`, and `pathout_refl_arrow` from
  `Struct_sigma`, ordinary identity, and `sigma_transport_arrow`;
- motive pullbacks, Pi targets, Sigma-total presentations, and section
  pullback from existing `Pullback_catd`, `Pi_*`, `Sigma_*`, and generic
  displayed action;
- the transitivity motive and its ordinary representable precomposition
  normal form from existing mixed-variance and fibre-covariance owners.

These definitions need no new Core node, checker branch, evaluator case,
external naturality equation, curry encoding, or active Lambdapi owner.

### Existing semantic owners to install in the trusted profile

Fixed-source path induction is not definitionally derived from Sigma/Pi alone.
The active kernel already declares `path_ind_sec` and gives it component and
specialized computation rules. Its coherent packages include existing opaque
owners such as `PathOutReflEval_funcd`, `PathInd_func`, and `PathInd_transfd`.
The selected design is to import/transfer those existing owners and rules into
a sealed trusted emdash v3.2 profile through the explicit declarative LF
transfer machinery. Concretely, that machinery creates checked TypeScript
declarations; "transfer" here records active-authority identity and
provenance, not a runtime Lambdapi dependency or a requirement to parse `.lp`
source. The end-user library must neither replace these owners with a new
TypeScript primitive nor pretend to synthesize induction from pointwise data.

`PathInd_funcd` is transparent in the active authority and may therefore live
in the derived library once its opaque dependencies are present. Any related
opaque package enters the trusted profile only when a selected consumer needs
it; opacity is preserved rather than disguised as a library definition.

The generic TypeScript dependent LF already supports checked dependent
declarations, transparent bodies, runtime rewrite rules, proof-time
comparisons, evaluation, and deterministic Lambdapi emission. Consequently,
the remaining questions are exact trusted-profile closure, module sealing and
provenance, derived-library closure, and ergonomic presentation—not semantic
feasibility of the core.

This plan does not authorize an ordinary user API for adding conversion rules.
A future extensible-rewriting mode, if desired, must be separately trust-
labelled and gated by the project's chosen subject-reduction, termination,
confluence, and consistency policy. It is not part of this safe standard-
library program.

## Current TypeScript Inventory

| Layer | Current evidence | Future work |
| --- | --- | --- |
| Generic dependent LF | checked declarations, Pi/lambda, conversion, runtime and proof rules | no new kernel mechanism expected |
| Categorical prerequisites | `Catd`, fibres, Sigma/Pi, pullback, section evaluation, generic action, `hom_int`, `fib_cov_tapp0_func`, `sigma_transport_arrow`, and higher action occur in reviewed transfer descendants | add only the four measured missing prerequisite closures recorded below |
| Public typed construction API | categories, objects/arrows, displayed families, fibres, totals, dependent pairs, family transport, Sigma arrows, sections, application, and recursive binders | add thin classifier-checked identity-arrow, representable, canonical Sigma-transport, PathOut, and PathInd facades where useful |
| Trusted PathInd profile | generic checked declaration/rule machinery exists; named PathInd package is absent from `src/v3_2` | install the smallest sealed, provenance-pinned opaque-owner/rule closure |
| Derived PathOut/PathInd library | absent from `src/v3_2` at this completion boundary | author transparent definitions and proof terms over the trusted profile |
| Text/browser presentation | no PathOut grammar or preset | add only after direct typed construction and computation are green |

The public `sigmaArrow` operation accepts a general fibre component; the
canonical `sigma_transport_arrow` facade is a distinct useful operation. A
missing facade is not a missing semantic owner. Likewise, a representable
family may compile to the transparent `hom_int(id)` body while retaining the
named library presentation.

## Active Work Ledger

| Slice | State | Dependencies | Exact purpose |
| --- | --- | --- | --- |
| `PATHOUT-TRUST-BOUNDARY-0A` | complete with forward correction | active source and checks; current transfer profiles | The immutable root-only audit pins both sources, 34 selected declarations, seven observed rules, five opaque PathOut/PathInd owners, and four missing prerequisite closures. It installs no behavior or product export. |
| `PATHOUT-LIBRARY-FOUNDATION-1B0` | corrected v3 proposed; separate review pending | completed corrected 0A; superseded v1/v2 | Measured checking showed that mixed action lacks the active opposite-Hom endpoint rule needed by `Rep_transport_func`. Proposal v3 keeps the local 3/5/1/9 delta but selects the already-reviewed direct-mixed-source-action descendant. |
| `PATHOUT-LIBRARY-FOUNDATION-1B` | paused pending corrected-v3 review | separately reviewed v3 proposal | Resume the existing root-only implementation only after v3 is checkpointed and separately approved; retain seven positives, eight negatives, six bounded oracle assertions, and every existing denial. |
| `PATHIND-TRUSTED-PROFILE-1C` | pending | completed 1B | Import/transfer the existing fixed-source `path_ind_sec` owner and exact component/specialized rules into the sealed trusted profile; expose only a typed library consumer and one nontrivial computation above that boundary. |
| `PATHOUT-LIBRARY-INTERNALIZED-1D` | pending | completed 1C | Add needed opaque `PathInd_func`/`PathInd_transfd` owners to the trusted profile, then derive transparent internalized/Sigma-total library presentations where the authority does. Preserve internally owned source-arrow and higher action. |
| `PATHOUT-LIBRARY-TRANSITIVITY-1E` | pending | completed 1D | Add `CompTarget_catd`, `CompMotive_catd`, `path_comp_sec`, and the checked reduction to representable precomposition/composition, retaining the authority's transparent/opaque classification. |
| `PATHOUT-LIBRARY-PRESENTATION-1F` | pending | completed direct typed slices | Add narrow text syntax, CLI/browser reviewer material, and book-facing explanation without adding a second semantic engine. |
| `PATHOUT-TRUSTED-LIBRARY-GRADUATE-0G` | pending | all selected slices | State the exact trusted profile, derived library, and computation envelope; retain any unimplemented internalized or presentation layers honestly. |

### `PATHOUT-TRUST-BOUNDARY-0A` exact audit contract

This first row is source/profile evidence only. It must produce a deterministic
review record which:

1. pins the active source and checks digests above and rejects drift;
2. inventories every selected PathOut/PathInd declaration and rule in active
   source order, with exact owner kind, opacity, body/rule status, and source
   position;
3. computes the lexical and typed dependency closure against existing
   TypeScript transfer descendants and identifies every missing prerequisite
   without duplicating it by spelling;
4. partitions selected items into transparent derived-library definitions,
   opaque trusted-profile owners/rules, and later presentation-only facades;
5. measures the smallest usable fixed-source foundation separately from
   internalized PathInd and transitivity, so later slices do not import a
   whole-source prefix by convenience;
6. specifies profile sealing, provenance, ordinary-library inability to add
   runtime/proof rules, and deterministic optional Lambdapi emission; and
7. authorizes no semantic registration, browser/public barrel, package
   version, syntax, or release change.

The audit may add one root-only immutable TypeScript review module and focused
tests if executable structure materially improves drift detection. Such a
module remains contributor evidence and must not enter `package_core`,
`package_authoring`, or `package_workspace`.

Each behavioral slice requires its own frozen proposal and separate review.
The first executable slice must inventory existing transfer owners before
adding declarations. Transparent aliases should keep transparent bodies;
opaque existing semantic owners should keep opaque interfaces and their exact
active rules inside the sealed profile. No owner is promoted merely for naming
symmetry, and no trusted rule is exposed as an ordinary standard-library
declaration capability.

### `PATHOUT-TRUST-BOUNDARY-0A` completion evidence

The executable audit is
[`src/v3_2/pathout_trust_boundary_audit.ts`](../src/v3_2/pathout_trust_boundary_audit.ts),
with focused drift and non-export checks in
[`tests/v3_2_pathout_trust_boundary_audit_tests.ts`](../tests/v3_2_pathout_trust_boundary_audit_tests.ts).
It is deliberately imported by the contributor test runner only; it is not
exported by the contributor barrel, any npm public barrel, or the browser
surface.

The measured selected authority contains 34 declarations in source order.
Twenty-nine have bodies and therefore remain transparent derived-library
definitions. Exactly five are opaque semantic owners:

- `PathOutReflEval_funcd`;
- `path_ind_sec`;
- `path_ind_func_fapp0`;
- `PathInd_func`; and
- `PathInd_transfd`.

Six selected runtime rules specify their component or specialized
computation. The proof-time rule at source lines 19455--19475 is inventoried
but explicitly deferred with the following Path-category comparison library;
it is not needed by the smallest generic PathOut/PathInd/transitivity product.
The transparent equality/Path-category comparison declarations at lines
19488--19673 are likewise outside the selected closure. Recording those
exclusions is narrower and more faithful than importing the entire nearby
source interval.

The prior inventory's broad phrase "categorical prerequisites" concealed
four concrete product-profile gaps. The fourth was found by the post-checkpoint
`1B0` provider audit and recorded as a forward correction rather than by
rewriting the audit checkpoint:

1. **Represented-source action.** `hom_int` is transferred, but the opaque
   `hom_int_precomp_tele_func` and `hom_int_precomp_func` owners, their three
   runtime projections, and their one proof-time projection-order comparison
   are not in a current selected product profile. `Rep_transport_func` depends
   on this closure.
2. **Sigma-totalization functor action.** `Sigma_cat` and
   `sigma_map_func` are transferred, but the opaque/injective `Sigma_func`
   owner and its object and capped-arrow projection rules are not.
   `PathOut_cat_func` directly names `Sigma_func`, so this closure belongs to
   the foundation rather than a later convenience layer. The separate
   `sigma_map_transf` higher-action owner/rule is not needed by the smallest
   object-and-capped-arrow foundation and remains explicitly deferred for
   reassessment with internalized higher action.
3. **Covariant fibre transport.** `hom_con` and
   `fib_cov_tapp0_func` are transferred, but transparent
   `FibCov_target_catd`, opaque `fib_cov_int`, `fib_cov_src_func`, and
   `fib_cov_transf`, and their three runtime projections are not. The readable
   `FibCov_source_catd` alias is not in the selected typed or lexical closure.
4. **Sigma-total displayed-transformation uncurrying.** The opaque
   `Sigma_transfd_funcd` owner and its object-component rule have isolated
   scale-stress representation evidence, but are not part of a selected
   product profile. They are needed only by the later internalized
   `PathInd_funcd` presentation.

This repartitions the continuation without changing the generic Core or
checker. The smallest foundation consists of the represented-source-action
and Sigma-totalization functor-action closures plus nine transparent
definitions: `Rep_catd_func`, `Rep_catd`,
`Rep_transport_func`, `PathOut_cat`, `PathOut_cat_func`,
`PathOut_transport_func`, `pathout_obj`, `pathout_refl_obj`, and
`pathout_refl_arrow`. Fixed-source induction adds its own opaque owners and
the covariant-fibre closure; internalized induction later adds the Sigma-total
uncurrying closure; transitivity adds only its selected transparent consumer
definitions above inherited fixed-source computation.

The audit freezes the four-layer boundary exactly: ordinary library code may
declare checked transparent definitions but cannot install runtime or proof
rules; only sealed profile construction may install the provenance-pinned
rules; Lambdapi remains an optional deterministic backend and a required
bounded conformance oracle for later behavior. The audit does not authorize
its own continuation.

Proportional validation on 2026-08-10 was:

```text
./scripts/pnpmw run workspace:check
  passed; pnpm@11.16.0, Node 24.11.1

./scripts/pnpmw exec tsc --noEmit -p tsconfig.json
  passed

./scripts/pnpmw exec eslint \
  src/v3_2/pathout_trust_boundary_audit.ts \
  tests/v3_2_pathout_trust_boundary_audit_tests.ts \
  tests/main_tests.ts
  passed

node --require ts-node/register --test \
  tests/v3_2_pathout_trust_boundary_audit_tests.ts
  8 tests / 1 suite: 8 passed, 0 failed

git diff --check
  passed
```

No Lambdapi invocation was used as audit evidence: both active checked files
are immutable byte-pinned inputs, and this row adds no mathematical behavior
to reconfirm. The root `check:ts` aggregate was intentionally not rerun under
the standing instruction to avoid long aggregates unless their omission
blocks progress; full TypeScript checking, focused lint, and every new drift
test directly cover this read-only contributor artifact.

The rollback-safe initial `PATHOUT-TRUST-BOUNDARY-0A` implementation checkpoint
is `a05493b`. The later `1B0` provider inspection found the omitted
`Sigma_func` closure and corrects that evidence forward; `a05493b` remains
backtracking evidence but is not by itself the implementation predecessor.
The corrected audit checkpoint is `5a1ea75`; it is the exact evidence
predecessor for `1B0`. Neither checkpoint contains a semantic or package
export.

### `PATHOUT-LIBRARY-FOUNDATION-1B0` frozen proposal

The non-authorizing proposal is
[`src/v3_2/pathout_foundation_proposal.ts`](../src/v3_2/pathout_foundation_proposal.ts),
with focused tests in
[`tests/v3_2_pathout_foundation_proposal_tests.ts`](../tests/v3_2_pathout_foundation_proposal_tests.ts).
The checkpointed v1 proposal selected
`compileCoreCategoricalDisplayedNdHigherFoundationTransfer`. Independent
review found that `hom_` and the two object projections needed to compute
`Rep_catd(x)[y]` occur only in the reviewed mixed-action descendant. Proposal
v2 therefore selects `compileCoreCategoricalMixedActionTransfer` as the
smallest current reviewed predecessor. It reuses `hom_`, the `hom_int` object
projection, and the represented-hom object projection already checked there;
it neither duplicates that subset nor imports a scale profile. The proposed
new 3/5/1/9 delta is otherwise unchanged.

The proposed implementation boundary is exactly **3/5/1/9**:

- three opaque declarations: `hom_int_precomp_tele_func`,
  `hom_int_precomp_func`, and injective `Sigma_func`;
- five runtime rules: the three represented-source projections plus
  `Sigma_func` object and capped-arrow action;
- one proof-time projection-order comparison between
  `hom_precomp_along_fapp0` and `hom_int_precomp_func`; and
- nine transparent definitions: the three representables, three PathOut
  category/functor/action names, `pathout_obj`, `pathout_refl_obj`, and
  `pathout_refl_arrow`.

The phase plan first compiles the opaque declarations, composes the five
runtime rules, compiles the proof rule, checks the nine transparent
definitions, and finally rechecks the proof rule against the final declaration
context. Every phase uses the generic LF declaration/runtime/proof engines;
there is no intrinsic Core, checker, evaluator, or active Lambdapi delta.

The sealing contract distinguishes two APIs that already have different trust
roles. The existing low-level LF authoring machinery remains explicitly
trust-bearing and capable of describing theory profiles. The future ordinary
safe-library facade may add checked transparent definitions, but cannot add
opaque owners, runtime rules, or proof rules. Qualification remains root-only;
no contributor/npm/browser export is part of `1B`.

Seven positive consumers cover representable fibres/precomposition, PathOut
totalization, functor object action, source action, reflexive action, and the
canonical reflexive arrow. Eight negative cases cover wrong sources/endpoints,
wrong dependent-pair fibres, foreign scoped terms, and attempts to add rules
through the safe-library route. Six exact Lambdapi assertions, bounded to 20
seconds, are required for implementation acceptance but not for this
behavior-free proposal.

The proposal is deliberately non-self-authorizing under gate
`H-TS-EMDASH-PATHOUT-FOUNDATION-01` and decision
`D-TS-EMDASH-PATHOUT-FOUNDATION-001`. A separate immutable review checkpoint
must retain the exact proposal before `PATHOUT-LIBRARY-FOUNDATION-1B` may
start. Human direction may supersede any delegated unattended review.

Proportional proposal validation on 2026-08-10 is:

```text
./scripts/pnpmw run workspace:check
  passed; pnpm@11.16.0, Node 24.11.1

./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw exec eslint \
  src/v3_2/pathout_foundation_proposal.ts \
  tests/v3_2_pathout_foundation_proposal_tests.ts \
  tests/main_tests.ts
  passed

node --require ts-node/register --test \
  tests/v3_2_pathout_foundation_proposal_tests.ts
  8 tests / 1 suite: 8 passed, 0 failed

git diff --check
  passed
```

The proposal runs no Lambdapi or long aggregate: it installs no behavior, and
the direct type/lint/proposal gates cover its immutable data and current
provider evidence.

The rollback-safe non-authorizing v1 proposal checkpoint is `dd69325`, with
ledger checkpoint `3226a6a`. It remains review/backtracking evidence but is
superseded by the `hom_` predecessor correction and must not be approved.
The corrected non-authorizing v2 proposal checkpoint is `b3d6d71`; it is the
sole recommendation a later delegated or human review may approve. Semantic
implementation remains unauthorized until that separate review is itself
checkpointed.

### `PATHOUT-LIBRARY-FOUNDATION-1B0` separate review

The separate immutable review is
[`src/v3_2/pathout_foundation_review.ts`](../src/v3_2/pathout_foundation_review.ts),
with focused tests in
[`tests/v3_2_pathout_foundation_review_tests.ts`](../tests/v3_2_pathout_foundation_review_tests.ts).
It records that v1 checkpoint `dd69325` was rejected and approves only v2
checkpoint `b3d6d71` under gate
`H-TS-EMDASH-PATHOUT-FOUNDATION-01` / decision
`D-TS-EMDASH-PATHOUT-FOUNDATION-001` using the user's standing unattended
delegation. Any later human decision supersedes that approval.

Authorization is exact and root-only: three opaque prerequisite declarations,
five runtime rules, one proof rule, nine transparent definitions, seven
positive consumers, eight negatives, and six bounded-oracle assertions over
the mixed-action predecessor. It explicitly denies fixed-source induction,
internalized induction, transitivity, Sigma higher action, new Core/checker
semantics, safe-library rule registration, text/browser/package exposure,
active Lambdapi edits, and external integration or release.

Proportional review validation on 2026-08-10 is:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw exec eslint \
  src/v3_2/pathout_foundation_review.ts \
  tests/v3_2_pathout_foundation_review_tests.ts \
  tests/main_tests.ts
  passed

node --require ts-node/register --test \
  tests/v3_2_pathout_foundation_proposal_tests.ts \
  tests/v3_2_pathout_foundation_review_tests.ts
  14 tests / 2 suites: 14 passed, 0 failed

git diff --check
  passed
```

No Lambdapi or long aggregate is relevant to the immutable review itself.
The bounded oracle remains mandatory for the now-authorized implementation.

The rollback-safe separate-review checkpoint is `38ef8ae`. It was the exact
authorization predecessor for the first root-only implementation attempt and
remains historical evidence; the measured correction below supersedes its v2
predecessor recommendation while preserving every explicit denial.

### Measured predecessor correction and proposal v3

The preceding v2 authorization is historical backtracking evidence, not
current authority. The first semantic qualification attempt compiled the
reviewed three opaque declarations, five runtime rules, and one proof rule,
then failed while checking the third transparent definition,
`Rep_transport_func`. A focused diagnostic run identified the final normalized
problem exactly:

```text
left  = bound index 3                 // Z
right = Op_cat(bound index 3)         // Op_cat Z
reason = no-proof-rule
```

This is the type of the argument `p`: the body calls
`hom_int_precomp_func`, whose source arrow is presented in `Op_cat Z`, while
the transparent declaration receives `p : Hom Z x y`. The active authority
already closes that presentation at source line 3251:

```text
rule Hom_cat (Op_cat $A) $X $Y ↪ Hom_cat $A $Y $X;
```

TypeScript already transfers the exact rule as
`categorical.direct-mixed-source-action.opposite-hom-endpoints` in reviewed
`DIRECT-MIXED-SOURCE-ACTION-1E2`. It is absent from the v2 mixed-action
predecessor. The same reviewed descendant also inherits mixed action's
`hom_` declarations/object projections and the displayed-chain/Sigma
dependencies required by the frozen proposal. It is therefore the smallest
current reviewed provider found by the measured check.

A temporary generic proof-assisted declaration-checker experiment was used
only to disambiguate the failure. It did not solve this runtime presentation
gap, and the v2 contract explicitly records zero checker branches. The whole
experiment and its diagnostic hook were removed; no Core, checker, evaluator,
proof-engine, or active Lambdapi source change remains.

Proposal v3 updates only `selectedPredecessor` to
`compileCoreCategoricalDirectMixedSourceActionTransfer` at revision
`DIRECT-MIXED-SOURCE-ACTION-1E2-RUNTIME-1`. The required opposite-Hom rule
and that profile's separately reviewed source-action projection are inherited
dependencies, not duplicated PathOut rules. The local implementation remains
exactly three opaque declarations, five runtime rules, one proof rule, and
nine transparent definitions, with the same seven positives, eight
negatives, six oracle assertions, sealing contract, and non-effects.

The former v2 review is explicitly marked superseded and cannot authorize
further implementation. Proposal v3 remains non-self-authorizing until its
own checkpoint is named and a later separate immutable review approves that
exact checkpoint under the user's standing unattended delegation or a human
decision.

Proportional correction validation on 2026-08-10 is:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw exec eslint \
  src/v3_2/pathout_foundation_proposal.ts \
  src/v3_2/pathout_foundation_review.ts \
  tests/v3_2_pathout_foundation_proposal_tests.ts \
  tests/v3_2_pathout_foundation_review_tests.ts
  passed

node --require ts-node/register --test \
  tests/v3_2_pathout_foundation_proposal_tests.ts \
  tests/v3_2_pathout_foundation_review_tests.ts
  14 tests / 2 suites: 14 passed, 0 failed

git diff --check
  passed
```

The earlier six-assertion bounded Lambdapi oracle passed in 4.47 seconds and
the active source is unchanged; it remains implementation evidence, not
evidence that the incomplete TypeScript predecessor was sufficient. No long
aggregate was run, because focused type/lint/data gates directly cover this
behavior-free correction and omission does not block the required checkpoint.

## Required Evidence For Implementation

1. Exact active-source signatures/bodies/rules and owning positions.
2. A compiled, sealed TypeScript theory-profile module over the smallest
   reviewed prerequisite profile, with authority provenance and no duplicate
   owner.
3. Direct typed examples whose explicit Core agrees with the transparent
   active definitions.
4. Fixed-source point and arrow computation plus at least one internally
   varying-source or higher-action observation before claiming the
   internalized theorem.
5. Strict negative tests for wrong source object, wrong motive base, wrong
   transported endpoint, and foreign scoped terms.
6. A bounded Lambdapi conformance oracle for selected definitions and rules.
7. A negative capability check showing that the ordinary end-user library
   route cannot silently install runtime or proof-time conversion rules.
8. Text/browser parity only after the typed standard library is green.
9. Proportional validation under root and nested SOP; do not rerun unchanged
   repository aggregates for reassurance.

## Explicit Non-Goals

This active plan does not authorize:

- a generic Lambdapi parser or bulk acquisition redesign;
- a new TypeScript Core/checker/evaluator primitive for path induction;
- treating opaque PathInd owners or their conversion rules as end-user-
  authored standard-library definitions;
- an ordinary safe-library API for user rewrite or unification rules;
- external naturality or functoriality equations;
- curry or total-context encodings as binder substitutes;
- arbitrary variance/dependency DAG graduation;
- whole-library transfer graduation;
- groupoidal closure, general normalization, confluence, canonicity, or
  consistency claims;
- push, merge, publication, deployment, or worktree cleanup.

## Persistent `/goal` Continuation Contract

The active proof-assistant goal delegates this selected standard-library row
to the present plan. A later dedicated goal may reuse the following objective
without changing the current authority or Git boundary:

```text
Implement the living TypeScript/emdash v3.2 PathInd trusted-profile and
PathOut derived-library program
rooted at docs/TYPESCRIPT_ELABORATOR_V3_2_PATHOUT_STANDARD_LIBRARY_PLAN.md.
Treat its authority order, work ledger, evidence requirements, and explicit
non-goals as part of the objective. Recover actual Git/worktree state and
active Lambdapi owners on every continuation. Audit and reuse existing generic
TypeScript LF and categorical transfer owners before adding declarations.
Author transparent PathOut definitions and proof terms as end-user standard-
library compositions. Faithfully import/transfer existing opaque PathInd
owners and exact rules only into a sealed, provenance-pinned trusted emdash
v3.2 theory profile—not as end-user library rules and not as Core/checker
primitives or external coherence evidence. Preserve the active authority's
transparent/opaque classification. For each
bounded slice, freeze and independently review the proposal, implement focused
typed behavior and tests, run proportional validation, synchronize the plan,
and create rollback-safe local checkpoints only where authorized. Do not
resume bulk scale, text/browser presentation, push, merge, publication, or
cleanup unless a later exact gate authorizes it.
```

## Relationship To The Completed Usability Goal

The categorical-binder usability goal establishes the prerequisite
architecture: recursive ordinary and displayed binders, canonical finite
displayed telescopes, internally owned action, direct/text parity for the
reviewed grammar, and an executable reviewer. Deferring this trusted-profile
and derived-library program until the present selection did not reopen or
weaken that completion claim. Activating its separate trust-boundary audit
still does not revise the completed binder architecture; it begins the next
trusted-theory/library integration program above that prerequisite.
