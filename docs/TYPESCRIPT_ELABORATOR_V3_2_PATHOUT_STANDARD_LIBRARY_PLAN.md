# TypeScript Elaborator v3.2 PathInd Trusted-Profile And PathOut Library Plan

Status: active selected standard-library continuation under
`TS-EMDASH-PROOF-ASSISTANT`; `PATHOUT-TRUST-BOUNDARY-0A` is complete; measured
counterevidence supersedes the v3 `PATHOUT-LIBRARY-FOUNDATION-1B0` review;
measured TypeScript execution counterevidence now also supersedes the v4
review; measured source-action consumer counterevidence superseded the v5
review; measured proof-head counterevidence superseded the v6 review;
measured generic-format counterevidence superseded the v7 review; measured
reflexive-consumer counterevidence now also supersedes the v8 review;
checkpointed proposal v9 preserves v8 and adds only active line 8032's
identity-incoming precomposition computation, and is separately approved
under delegated unattended authority with human supersession; root-only
`PATHOUT-LIBRARY-FOUNDATION-1B` is implemented and final-proportional-green at
5/13/2/9; `PATHIND-TRUSTED-PROFILE-1C` proposal v1 is checkpointed at
`cc639fc` and was separately approved under delegated unattended authority,
but measured TypeScript rule-admission counterevidence supersedes that review;
corrected behavior-free proposal v2 at checkpoint `7413dd6` adds only active
`hom_con` object projection line 7865, changes the root-local boundary to
5/7/0/6, and is separately approved under delegated unattended authority with
human supersession at review checkpoint `3421647`; measured faithful-signature
compilation now supersedes that review at active displayed-functor object
projection line 9177; corrected proposal v3 at checkpoint `bfe09e3` changes
only the root-local boundary to 5/8/0/6 and is separately approved under
delegated unattended authority with human supersession at review checkpoint
`880593e`; measured nested-head execution counterevidence now supersedes that
review; corrected proposal v4 at checkpoint `f4101e2` adds only a subject-
checked lines-5481/9177 fusion, changes the boundary to 5/9/0/6, and is
separately approved under delegated unattended authority with human
supersession at review checkpoint `397472f`; semantic implementation may
resume, but no PathOut/PathInd profile or public export is yet qualified

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
| `PATHOUT-LIBRARY-FOUNDATION-1B0` | corrected v9 separately reviewed | completed corrected 0A; superseded v1/v2/v3/v4/v5/v6/v7/v8 | V8 makes general source action pass, but reflexive action stops at stable precomposition of `id_y` by `p`. Checkpointed v9 preserves v8, adds only active line 8032, and is approved at 5/13/2/9. |
| `PATHOUT-LIBRARY-FOUNDATION-1B` | complete; final-proportional-green | separately reviewed v9 proposal | The root-only 5/13/2/9 transfer compiles through generic engines; seven positives, eight negatives, six bounded oracle assertions, safe-library denials, and non-export checks are green. |
| `PATHIND-TRUSTED-PROFILE-1C` | corrected v4 separately reviewed; implementation ready | completed 1B; proposal/review checkpoints `f4101e2`/`397472f`; superseded v3 checkpoints `bfe09e3`/`880593e`, v2 checkpoints `7413dd6`/`3421647`, and v1 checkpoints `cc639fc`/`2deae91` | Line 9177 is registered but cannot match before nested line 5481 under head-only execution. V4 adds only their subject-checked fusion, yielding an approved root-only 5/9/0/6 boundary with unchanged consumer, negative, and nine-assertion oracle scope. |
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
further implementation. Non-authorizing proposal v3 is checkpointed at
`640d5ec`. Its separate immutable review approves only that exact checkpoint
under the user's standing unattended delegation, retains later human
supersession, and preserves every v3 denial. The review itself authorizes no
push, merge, publication, deployment, or cleanup.

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

The separate v3 review is
[`src/v3_2/pathout_foundation_review.ts`](../src/v3_2/pathout_foundation_review.ts).
Its focused tests retain both superseded checkpoints, exact v3 recommendation,
3/5/1/9 counts, corrected predecessor, human supersession, root-only status,
and every later-layer denial. `PATHOUT-LIBRARY-FOUNDATION-1B` may therefore
resume only on the current proof branch and only within that exact boundary.

### Measured covariant-action correction and proposal v4

The v3 proposal and review checkpoints, `640d5ec` and `36c368e`, remain exact
backtracking evidence but no longer authorize implementation. With v3's
corrected predecessor, focused semantic qualification checked all three
opaque declarations, all five local runtime rules, the proof rule, and the
first eight transparent definitions. The standard checker then stopped at
the ninth and final definition, `pathout_refl_arrow`. A compact normalization
diagnostic isolated the target pair's fibre component:

```text
left  = fapp0(fapp1_fapp0(hom_(id,x),p),id_x)
right = p
```

Transparent `PathOut_cat`, `pathout_obj`, `pathout_refl_obj`, `Rep_catd`, and
`Rep_catd_func` aliases and the mixed-action projections had all reduced.
The remaining expression is the covariant represented-Hom/postcomposition
action, not the already-imported represented-source/precomposition proof
rule. The active authority supplies its stable closure in four exact pieces:

- opaque `hom_postcomp_func` at line 7272;
- represented-Hom capped action to that functor at line 7298;
- its object action to existing `hom_postcomp_fapp0` at line 7302; and
- the identity-source unit reducing that action to `p` at line 7426.

Proposal v4 therefore keeps
`compileCoreCategoricalDirectMixedSourceActionTransfer` and changes only the
local boundary from **3/5/1/9** to **4/8/1/9**: one additional opaque
signature and those three active runtime rules, with the same one proof rule
and nine transparent definitions. `hom_postcomp_fapp0` is reused from the
existing predecessor chain. No generic composition-unit rule, checker or
proof-rule substitute, Core/evaluator branch, active Lambdapi edit, public
export, presentation, package, integration, or release effect is authorized.

The temporary diagnostic hook used to expose the normalized residue was
removed in full; the generic LF transfer compiler is unchanged. The v3 review
record now withdraws its earlier authorization and embeds exact
non-authorizing proposal v4. Proposal v4 still requires its own rollback-safe
checkpoint and separate immutable review before semantic implementation may
resume. Focused proposal/supersession validation is required; no Lambdapi or
long aggregate is relevant to this behavior-free correction.

Proportional proposal-v4/supersession validation on 2026-08-10 is:

```text
./scripts/pnpmw run workspace:check
  passed; pnpm@11.16.0, Node 24.11.1

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
```

The rollback-safe non-authorizing proposal-v4/supersession checkpoint is
`681d954`. Its separate immutable review approves only that exact checkpoint
under the user's standing unattended delegation, retains later human
supersession, and preserves every v4 denial. The review itself authorizes no
push, merge, publication, deployment, or cleanup. No Lambdapi or long
aggregate was run; neither is relevant to the behavior-free correction, and
their omission does not block the separate review checkpoint.

### Measured weak-head execution correction and proposal v5

The v4 proposal and review checkpoints, `681d954` and `ab556a9`, remain exact
backtracking evidence but no longer authorize implementation. V4's expanded
module closure and all three new active runtime rules subject-check. After
correcting two mechanical dependency declarations (`fapp0` duplication and
the explicit generic `id` owner), the one-shot semantic compiler again reaches
only the ninth transparent definition. `pathout_refl_arrow` still reports the
same outer `Struct_sigma` versus `pathout_obj` mismatch.

This second failure is not another missing mathematical law. The combined
TypeScript conversion engine deliberately performs beta, delta, and catalog
rewriting only at the current weak head. Its runtime matcher does not first
normalize a candidate rule's nested arguments. Consequently the outer term

```text
fapp0(fapp1_fapp0(hom_(F,W),f),g)
```

cannot use line 7302 until its nested functor argument has used line 7298,
but weak-head matching never visits that nested argument while the whole term
is being compared with `g`. Lambdapi's ordinary contextual rewriting can
compose the two source rules; the deliberately smaller TypeScript execution
model requires their explicit compiled fusion.

Proposal v5 therefore preserves all four opaque interfaces, all eight active
runtime rules, the proof rule, the nine transparent definitions, and v4's
predecessor. It adds exactly one generic-runtime, subject-checked fusion:

```text
fapp0(fapp1_fapp0(hom_(F,W),f),g)
  ↪ hom_postcomp_fapp0(F,W,f,g)
```

The fusion is derived only from active lines 7298 and 7302. It introduces no
new mathematical rule; its stable result lets active identity-source line
7426 fire at the next weak head. The corrected local boundary is therefore
**4/9/1/9**. No generic composition or identity unit, nested-normalization
engine, checker/proof substitute, Core/evaluator branch, active Lambdapi edit,
or later/public effect is imported.

The v4 review record now withdraws its authorization and embeds exact
non-authorizing proposal v5. The implementation draft remains preserved and
unstaged, but the fusion itself must not be added until proposal v5 has a
rollback-safe checkpoint and separate immutable review. No further expensive
semantic rerun is relevant to this behavior-free proposal correction.

Proportional proposal-v5/supersession validation on 2026-08-10 is:

```text
./scripts/pnpmw run workspace:check
  passed; pnpm@11.16.0, Node 24.11.1

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
```

No Lambdapi or long aggregate was run; neither is relevant to the
behavior-free correction, and their omission does not block its checkpoint.

The rollback-safe non-authorizing proposal-v5/supersession checkpoint is
`622a496`. Its separate immutable review approves only that exact checkpoint
under the user's standing unattended delegation, retains later human
supersession, and preserves every v5 denial. The review itself authorizes no
push, merge, publication, deployment, or cleanup.

### Measured represented-source component correction and proposal v6

Proposal-v5 checkpoint `622a496` and review checkpoint `c4dd293` remain exact
backtracking evidence but no longer authorize implementation. With v5's
checked-wildcard encoding of its authorized fusion, the one-shot TypeScript
semantic compiler succeeds through all nine transparent definitions,
including `pathout_refl_arrow`. The complete focused consumer suite then
passes sixteen checks, skips the opt-in Lambdapi oracle, and fails only the
two selected source-action observations.

Runtime comparison and the local proof program expose the same exact
unreduced subproblem:

```text
fapp0(
  tapp0_fapp0(hom_(id), z, hom_int_precomp_func(p)),
  q)
versus
comp(q,p)
```

The local line-8463 `hom-int-precomp-projection-order` proof rule expects the
stable `hom_precomp_along_fapp0` head, so it cannot match this earlier raw
component action. The active authority supplies the missing route in three
pieces that the original lexical audit did not select:

- opaque `hom_precomp_along_func` at line 7921;
- its object action to `hom_precomp_along_fapp0` at line 7977; and
- the `hom_int_precomp_func` component projection to that functor at line
  9704.

As with v5, TypeScript's deliberate weak-head execution cannot first reduce
the nested `tapp0_fapp0` before matching the surrounding `fapp0`. Proposal v6
therefore preserves every v5 entry, adds the opaque line-7921 interface and
the two active rules, and adds exactly one subject-checked fusion:

```text
fapp0(tapp0_fapp0(hom_int_precomp_func(p)),q)
  ↪ hom_precomp_along_fapp0(id,F(z),x,y,p,q)
```

The fusion is derived only from active lines 9704 and 7977. It makes the
already-selected proof rule reachable and adds no mathematical rule, generic
composition rewrite, nested-normalization engine, Core/checker/evaluator
branch, active Lambdapi edit, or later/public effect. The corrected local
boundary is **5/12/1/9**: five opaque interfaces, ten active runtime rules,
two derived weak-head fusions, one proof rule, and nine transparent
definitions.

The v5 review record now withdraws its authorization and embeds exact
non-authorizing proposal v6. The green compiler result and failing consumer
counterevidence remain preserved in the unstaged implementation draft, but
the new closure must not be implemented until proposal v6 has a rollback-safe
checkpoint and separate immutable review.

Proportional proposal-v6/supersession validation on 2026-08-10 is:

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

The unchanged workspace contract is carried forward from proposal v5. No
Lambdapi or long aggregate was run for this behavior-free correction; neither
would validate the proposal-data boundary, and their omission does not block
its checkpoint.

The rollback-safe non-authorizing proposal-v6/supersession checkpoint is
`f006ccb`. Its separate immutable review approves only that exact checkpoint
under the user's standing unattended delegation, retains later human
supersession, and preserves every v6 denial. The review itself authorizes no
push, merge, publication, deployment, or cleanup.

### Measured identity-family proof correction and proposal v7

Proposal-v6 checkpoint `f006ccb` and review checkpoint `bdcef29` remain exact
backtracking evidence but no longer authorize implementation. The v6 runtime
closure succeeds: a focused replay of the two previously failing consumers
normalizes both subjects through the new component/object fusion to the
stable head. The general case leaves exactly:

```text
hom_precomp_along_fapp0(Z,Z,id_func(Z),z,x,y,p,q)
versus
comp_fapp0(Z,x,y,z,q,p)
```

The reflexive case has the same left head with `q = id_y` and right side `p`.
The local line-8463 `hom-int-precomp-projection-order` rule is not malformed;
it is simply a different active comparison. Its right composite must retain
`hom_int_precomp_func(A,B,F,Y,X,p)` as a rigid factor, so it cannot match the
ordinary `p` factor above. Active source line 8079 gives the exact specialized
identity-family comparison between this stable precomposition head and raw
composition.

Non-authorizing proposal v7 preserves every v6 declaration, runtime rule,
derived weak-head fusion, proof rule, transparent definition, consumer,
negative, oracle assertion, and denial. It adds only active line 8079 as the
earlier of two source-ordered proof rules. The Lambdapi replacement contains
one reflexive `tt ≡ tt` obligation; the TypeScript representation elides that
already-solved obligation and generates zero residual proof problems. No
runtime rule, generic proof matcher, Core/checker/evaluator branch, active
Lambdapi edit, or public/package effect is added. The corrected boundary is
**5/12/2/9**.

The v6 review record withdraws its implementation authorization and embeds
the exact non-authorizing v7 proposal. The rollback-safe proposal checkpoint
is `2460ae9`. Its separate immutable review approves only that exact
checkpoint under the user's standing unattended delegation, retains later
human supersession, and restores only the root-local 5/12/2/9 implementation
authority. The proposal correction and review are behavior-free, so their
proportional gate is root typecheck, focused lint, the proposal/review tests,
and exact diff hygiene; no Lambdapi or long aggregate is relevant.

Proportional proposal-v7/supersession validation on 2026-08-10 is:

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

The unchanged workspace contract is carried forward from v6. No Lambdapi or
long aggregate was run for this behavior-free correction; neither would
validate the proposal-data boundary.

### Measured nonempty proof-constraint correction and proposal v8

Proposal-v7 checkpoint `2460ae9` and review checkpoint `7035922` remain exact
backtracking evidence but no longer authorize implementation. The first
focused semantic replay rejected the new proof module before compilation:

```text
CoreLfTransferError: Proof-time rule must generate at least one constraint
code: INVALID_RULE
path: module.proofRules[0].generatedConstraints
```

This is an intentional generic-format invariant in
`createCoreLfModuleSpec`, not a PathOut or matcher failure. The active source
closes line 8079 with the reflexive obligation `tt ≡ tt`, but the selected
TypeScript predecessor does not expose the native `unit` inductive or its
constructor `tt`. Importing that foundational owner solely to spell a trivial
proof-rule discharge would enlarge the prerequisite boundary.

Non-authorizing proposal v8 therefore preserves v7's exact 5/12/2/9
declarations and rules while representing source `tt ≡ tt` by one captured
`A ≡ A` generated constraint. Both are reflexive, and the generic comparison
engine discharges the TypeScript representative immediately. The change adds
no semantic rule, owner, runtime computation, generic engine branch,
active-source edit, or public effect; it only keeps the generic rule record
nonempty. The two proof rules now generate four TypeScript constraints in
total: one reflexive constraint for line 8079 and the three active
projection-order constraints for line 8463.

The v7 review record withdraws its authorization and embeds exact
non-authorizing proposal v8. The rollback-safe proposal checkpoint is
`6e4bb82`. Its separate immutable review approves only that exact checkpoint
under the user's standing unattended delegation, retains later human
supersession, and restores only the root-local 5/12/2/9 implementation
authority. As a behavior-free correction, its proportional gate remains root
typecheck, focused lint, the fourteen proposal/review tests, and exact diff
hygiene; no Lambdapi or long aggregate is relevant.

Proportional proposal-v8/supersession validation on 2026-08-10 is:

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

The unchanged workspace contract is carried forward from v7. No Lambdapi or
long aggregate was run for this behavior-free correction; neither would
validate the proposal-data boundary.

### Measured reflexive identity-incoming correction and proposal v9

Proposal-v8 checkpoint `6e4bb82` and review checkpoint `edda832` remain exact
backtracking evidence but no longer authorize implementation. With the v8
identity-family rule encoded using explicit inferred endpoints, the focused
two-consumer replay compiles the whole profile and passes general source
transport. Only the reflexive consumer remains:

```text
hom_precomp_along_fapp0(Z,Z,id_func(Z),y,x,y,p,id_y)
versus
p
```

The right side has already reduced `comp(id_y,p)` to `p`, so the line-8079
two-sided comparison no longer applies. Active source line 8032 supplies the
exact one-sided computation: precomposing an identity incoming arrow by `h`
reduces to `fapp1_fapp0(F,h)`. For `F = id_func(Z)`, the existing reviewed
structural runtime then reduces that action to `h`.

Non-authorizing proposal v9 preserves every v8 entry and adds only line 8032
as the eleventh active runtime rule; the two TypeScript-only weak-head fusions
remain unchanged. The corrected boundary is therefore **5/13/2/9**. No new
opaque owner, derived fusion, proof substitute, generic identity law, engine
branch, active-source edit, or public effect is authorized.

The v8 review record withdraws its authorization and embeds exact
non-authorizing proposal v9. The rollback-safe proposal checkpoint is
`b4277fb`. Its separate immutable review approves only that exact checkpoint
under the user's standing unattended delegation, retains later human
supersession, and restores only the root-local 5/13/2/9 implementation
authority. Its behavior-free proposal/review gate is root typecheck, focused
lint, the fourteen proposal/review tests, and exact diff hygiene; no Lambdapi
or long aggregate is relevant.

Proportional proposal-v9/supersession validation on 2026-08-10 is:

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

The unchanged workspace contract is carried forward from v8. No Lambdapi or
long aggregate was run for this behavior-free correction; neither would
validate the proposal-data boundary.

### `PATHOUT-LIBRARY-FOUNDATION-1B` completion evidence

The root-only implementation is
[`src/v3_2/pathout_foundation_transfer.ts`](../src/v3_2/pathout_foundation_transfer.ts),
with focused qualification in
[`tests/v3_2_pathout_foundation_transfer_tests.ts`](../tests/v3_2_pathout_foundation_transfer_tests.ts)
and contributor-runner discovery in `tests/main_tests.ts`. It remains absent
from contributor, npm, authoring, workspace, and browser barrels.
The complete semantic checkpoint is `550316a`.

The compiled boundary is exactly **5/13/2/9**:

- five opaque active-authority interfaces;
- thirteen runtime rules: eleven active computations plus the two reviewed
  weak-head fusions derived from active rule pairs;
- two active proof-time comparisons in source order, with the line-8079
  reflexive source discharge represented by one captured `A ≡ A` constraint
  and the line-8463 projection-order rule retaining its bounded external
  typing oracle; and
- nine checked transparent representable and PathOut definitions.

All thirteen runtime subjects validate through the generic TypeScript runtime
compiler. All nine transparent definitions compile through the generic
declaration engine. The general source-transport consumer uses the
identity-family proof comparison, while reflexive source transport now
computes definitionally through line 8032 and inherited identity-functor
action. The canonical Sigma arrow typechecks. Eight negative consumers reject
wrong categories, endpoints, fibres, scope, and ordinary-library attempts to
register runtime or proof rules.

Final proportional validation on 2026-08-10 is:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw exec eslint \
  src/v3_2/pathout_foundation_transfer.ts \
  tests/v3_2_pathout_foundation_transfer_tests.ts \
  tests/main_tests.ts
  passed

node --require ts-node/register --test \
  tests/v3_2_pathout_foundation_transfer_tests.ts
  19 tests / 1 suite: 18 passed, 0 failed, 1 opt-in oracle skipped

EMDASH_RUN_LAMBDAPI_PATHOUT_FOUNDATION_PROBES=1 \
node --require ts-node/register --test \
  --test-name-pattern="matches all six" \
  tests/v3_2_pathout_foundation_transfer_tests.ts
  1 test / 1 suite: 1 passed, 0 failed; all six assertions accepted

git diff --check
  passed
```

The workspace contract is unchanged and carried forward. No long
`check:ts`/repository aggregate was rerun: this tranche changes no shared LF
engine, package/workspace setup, public barrel, browser surface, or active
Lambdapi source, and the user's standing policy requires avoiding such an
aggregate unless its omission blocks progress. The focused compiler,
consumer, static, sealing, and bounded-oracle gates directly cover this
root-local qualification boundary.

### `PATHIND-TRUSTED-PROFILE-1C` frozen proposal v1 (superseded for implementation)

The behavior-free immutable proposal is
[`src/v3_2/pathind_fixed_source_proposal.ts`](../src/v3_2/pathind_fixed_source_proposal.ts),
with focused drift, sealing, and non-export checks in
[`tests/v3_2_pathind_fixed_source_proposal_tests.ts`](../tests/v3_2_pathind_fixed_source_proposal_tests.ts).
Proposal checkpoint `cc639fc` freezes those exact bytes. The separate review
is
[`src/v3_2/pathind_fixed_source_review.ts`](../src/v3_2/pathind_fixed_source_review.ts),
with focused checks in
[`tests/v3_2_pathind_fixed_source_review_tests.ts`](../tests/v3_2_pathind_fixed_source_review_tests.ts).
It pins active-source/check digests from the completed audit, the qualified
PathOut predecessor revision, semantic checkpoint `550316a`, and synchronized
ledger checkpoint `349b6d4`. The source digests still match the audited bytes.

Proposal v1 freezes an exact **5/6/0/6** local implementation delta:

- five opaque active-authority interfaces: `fib_cov_int`,
  `fib_cov_src_func`, `fib_cov_transf`, `path_ind_sec`, and
  `path_ind_func_fapp0`;
- six runtime rules in active source order: the three covariant-fibre
  projections, fixed-source component-object action, point computation, and
  the specialized Sigma-pullback computation;
- no proof-time rule; and
- six checked transparent definitions: `FibCov_target_catd`,
  `pathout_refl_eval_func`, `pathout_refl_eval_base_func`,
  `pathout_refl_arrow_sec`, `PathInd_src_catd`, and `PathInd_tgt_catd`.

This is narrower than the audit's broad fixed-source inventory. The opaque
whole displayed functor `PathInd_func` and its component rule are deliberately
paired with `PathInd_transfd` in internalized row 1D. The proposal also defers
`PathOutReflEval_funcd`, every varying-source/Sigma-total presentation,
transitivity definitions, `FibCov_source_catd`, and the Path-category
proof-time reflexive bridge. It neither copies a whole source prefix nor adds
a PathInd-specific Core, checker, evaluator, or public facade.

The sole library-facing witness selected for 1C is the transparent section

```text
pathout_refl_arrow_sec(x)
  : Pi(q : PathOut_Z(x), Hom_PathOut_Z(x)(reflout_x,q)).
```

Its nontrivial point observation is

```text
pathout_refl_arrow_sec(x)[(y,p)] = pathout_refl_arrow(x,y,p).
```

The implementation gate must additionally exercise all six imported runtime
rules through the generic compiler, the fixed-source component action, the
Sigma-pullback fold to `fib_cov_transf`, eight strict negative consumers, the
ordinary-library authority denials, non-export closure, and seven assertions
through a 20-second bounded Lambdapi oracle. This is conformance to existing
authority, not a runtime dependency on Lambdapi.

Proposal-only validation on 2026-08-10 is:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw exec eslint \
  src/v3_2/pathind_fixed_source_proposal.ts \
  tests/v3_2_pathind_fixed_source_proposal_tests.ts \
  tests/main_tests.ts
  passed

node --require ts-node/register --test \
  tests/v3_2_pathind_fixed_source_proposal_tests.ts
  8 tests / 1 suite: 8 passed, 0 failed

git diff --check
  passed
```

No Lambdapi or long repository aggregate was run for this immutable-data
proposal. It changes no semantic engine or active kernel, the active source
digests are unchanged, and direct proposal/static gates cover its only
behavior: rejecting drift and accidental authority. The decision question is
`H-TS-EMDASH-PATHIND-FIXED-SOURCE-01` /
`D-TS-EMDASH-PATHIND-FIXED-SOURCE-001`. The proposal remains non-authorizing
in its own immutable data. Its separate review approves only checkpoint
`cc639fc` under the user's standing unattended delegation, with later human
supersession, and authorizes only the exact root-local implementation. The
review does not authorize `PathInd_func`, `PathInd_transfd`, internalized
induction, transitivity, the Path-category proof bridge, public export, active
Lambdapi edits, integration, or release.

Separate-review validation on 2026-08-10 is:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw exec eslint \
  src/v3_2/pathind_fixed_source_review.ts \
  tests/v3_2_pathind_fixed_source_review_tests.ts \
  tests/main_tests.ts
  passed

node --require ts-node/register --test \
  tests/v3_2_pathind_fixed_source_proposal_tests.ts \
  tests/v3_2_pathind_fixed_source_review_tests.ts
  13 tests / 2 suites: 13 passed, 0 failed

git diff --check
  passed
```

No Lambdapi or long aggregate is relevant to this behavior-free review. Its
former exact 5/6/0/6 implementation authority is superseded by the measured
counterevidence below; the checkpoints remain review and backtracking
evidence.

### `PATHIND-TRUSTED-PROFILE-1C` corrected proposal v2

First semantic compilation under the v1 review reached the initial FibCov
package-component rule and rejected it with `INVALID_RUNTIME_RULE_TYPE`. The
left side retained the functor classifier while the right side expected the
Hom classifier. Read-only authority and predecessor inspection isolates one
missing computation: the predecessor declares `hom_con` but does not transfer
its active object projection at `emdash3_2.lp` line 7865,

```text
fapp0(hom_con(A,W,B,F),x) = Hom_cat(A,fapp0(F,x),W).
```

The corrected immutable proposal is
[`src/v3_2/pathind_fixed_source_proposal_v2.ts`](../src/v3_2/pathind_fixed_source_proposal_v2.ts),
with focused checks in
[`tests/v3_2_pathind_fixed_source_proposal_v2_tests.ts`](../tests/v3_2_pathind_fixed_source_proposal_v2_tests.ts).
It preserves proposal v1 and adds only that existing active runtime rule,
before the six selected FibCov/PathInd rules in authority order. The corrected
local delta is exactly **5/7/0/6**; selected runtime observations increase
from three to four and bounded Lambdapi assertions from seven to eight.

This is a predecessor-closure correction, not a new mathematical rule. V2
explicitly denies a generic checker change, an alternate FibCov body, and a
duplicate `hom_con` declaration. It preserves the same five opaque owners,
six transparent definitions, rho-section consumer, strict negatives, safe-
library authority denials, non-export boundary, and every 1D/1E/1F/public/
release denial. V1 proposal checkpoint `cc639fc` and review checkpoint
`2deae91` remain backtracking evidence but no longer authorize implementation.

Corrected-v2 proposal validation on 2026-08-10 is:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw exec eslint \
  src/v3_2/pathind_fixed_source_proposal_v2.ts \
  tests/v3_2_pathind_fixed_source_proposal_v2_tests.ts \
  tests/main_tests.ts
  passed

node --require ts-node/register --test \
  tests/v3_2_pathind_fixed_source_proposal_v2_tests.ts
  6 tests / 1 suite: 6 passed, 0 failed

node --require ts-node/register --test \
  tests/v3_2_pathind_fixed_source_proposal_tests.ts \
  tests/v3_2_pathind_fixed_source_review_tests.ts
  13 tests / 2 suites: 13 passed, 0 failed

git diff --check
  passed
```

No Lambdapi or long repository aggregate was run for this immutable-data
correction. Active source bytes, shared engines, package/workspace setup, and
public surfaces are unchanged; the focused drift, scope, authority, static,
and historical-regression gates directly cover it. Proposal v2 remains non-
authorizing and is frozen at checkpoint `7413dd6`.

The separate immutable review is
[`src/v3_2/pathind_fixed_source_review_v2.ts`](../src/v3_2/pathind_fixed_source_review_v2.ts),
with focused checks in
[`tests/v3_2_pathind_fixed_source_review_v2_tests.ts`](../tests/v3_2_pathind_fixed_source_review_v2_tests.ts).
Under `H-TS-EMDASH-PATHIND-FIXED-SOURCE-02` /
`D-TS-EMDASH-PATHIND-FIXED-SOURCE-002`, it approves only proposal checkpoint
`7413dd6` through the user's standing unattended delegation, with later human
supersession. The review authorizes the exact root-only 5/7/0/6 implementation
and nothing else: line 7865 is admitted, while checker changes, alternate
FibCov bodies, duplicate `hom_con`, internalized PathInd, transitivity,
presentation/public export, active Lambdapi edits, integration, and release
remain denied.

Separate-review validation on 2026-08-10 is:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw exec eslint \
  src/v3_2/pathind_fixed_source_review_v2.ts \
  tests/v3_2_pathind_fixed_source_review_v2_tests.ts \
  tests/main_tests.ts
  passed

node --require ts-node/register --test \
  tests/v3_2_pathind_fixed_source_proposal_v2_tests.ts \
  tests/v3_2_pathind_fixed_source_review_v2_tests.ts
  11 tests / 2 suites: 11 passed, 0 failed

git diff --check
  passed
```

No Lambdapi or long aggregate is relevant to this behavior-free review.
Review checkpoint `3421647` freezes that decision, but its implementation
authority is superseded by the measured counterevidence below.

### `PATHIND-TRUSTED-PROFILE-1C` corrected proposal v3

The v2 semantic experiment first restored the exact active Fibre-based
signatures for `fib_cov_src_func` and `fib_cov_transf` at lines 13952–13962.
With those faithful signatures and line 7865, the first two FibCov projections
subject-check. The third projection then fails during left-side inference with
`INVALID_RUNTIME_RULE_TYPE`: the transported value still has the stable
`Obj(Functord_cat(K,Rep(x),E))` presentation while `tapp0_fapp0` expects the
ordinary `Transf` classifier.

The predecessor already declares `Functord_cat`, `Transf_cat`, and the
transparent `Transf`-to-`Obj(Transf_cat)` runtime delta. Read-only transfer
inspection confirms that it does not carry active source line 9177,

```text
Obj(Functord_cat(K,E,D)) = Obj(Transf_cat(K,Cat_cat,E,D)).
```

The corrected immutable proposal is
[`src/v3_2/pathind_fixed_source_proposal_v3.ts`](../src/v3_2/pathind_fixed_source_proposal_v3.ts),
with focused checks in
[`tests/v3_2_pathind_fixed_source_proposal_v3_tests.ts`](../tests/v3_2_pathind_fixed_source_proposal_v3_tests.ts).
It preserves v2, inserts only line 9177 after line 7865 and before the six
FibCov/PathInd rules, and changes the exact local delta to **5/8/0/6**. The
focused runtime observations rise to five and bounded oracle assertions to
nine. No declaration, proof rule, mathematical rule, or later consumer is
added.

V3 requires the exact active Fibre signatures and explicitly denies a
canonical-signature substitution, generic checker change, or duplicate
classifier declaration. It preserves the rho-section consumer, eight strict
negatives, safe-library authority denials, non-export boundary, and every
1D/1E/1F/public/release denial. V2 checkpoints `7413dd6` and `3421647` remain
backtracking evidence but no longer authorize implementation.

Corrected-v3 proposal validation on 2026-08-10 is:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw exec eslint \
  src/v3_2/pathind_fixed_source_proposal_v3.ts \
  tests/v3_2_pathind_fixed_source_proposal_v3_tests.ts \
  tests/main_tests.ts
  passed

node --require ts-node/register --test \
  tests/v3_2_pathind_fixed_source_proposal_v3_tests.ts
  6 tests / 1 suite: 6 passed, 0 failed

git diff --check
  passed
```

No Lambdapi or long repository aggregate was run for this immutable-data
correction. Active source bytes, shared engines, package/workspace setup, and
public surfaces are unchanged; focused drift, scope, authorization, static,
and non-export gates directly cover it. Proposal v3 remains non-authorizing and
is frozen at checkpoint `bfe09e3`.

The separate immutable review is
[`src/v3_2/pathind_fixed_source_review_v3.ts`](../src/v3_2/pathind_fixed_source_review_v3.ts),
with focused checks in
[`tests/v3_2_pathind_fixed_source_review_v3_tests.ts`](../tests/v3_2_pathind_fixed_source_review_v3_tests.ts).
Under `H-TS-EMDASH-PATHIND-FIXED-SOURCE-03` /
`D-TS-EMDASH-PATHIND-FIXED-SOURCE-003`, it approves only proposal checkpoint
`bfe09e3` through the user's standing unattended delegation, with later human
supersession. It authorizes exact active Fibre signatures and only the
root-local 5/8/0/6 implementation. Signature substitution, checker changes,
alternate FibCov bodies, duplicate classifiers, internalized PathInd,
transitivity, public presentation, active Lambdapi edits, integration, and
release remain denied.

Separate-review validation on 2026-08-10 is:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw exec eslint \
  src/v3_2/pathind_fixed_source_review_v3.ts \
  tests/v3_2_pathind_fixed_source_review_v3_tests.ts \
  tests/main_tests.ts
  passed

node --require ts-node/register --test \
  tests/v3_2_pathind_fixed_source_proposal_v3_tests.ts \
  tests/v3_2_pathind_fixed_source_review_v3_tests.ts
  11 tests / 2 suites: 11 passed, 0 failed

git diff --check
  passed
```

No Lambdapi or long aggregate is relevant to this behavior-free review. Its
review checkpoint `880593e` freezes that decision. The next authorized action
is superseded by the measured counterevidence below.

### `PATHIND-TRUSTED-PROFILE-1C` corrected proposal v4

V3 registers line 9177, yet the third FibCov projection still fails at the
same object-versus-transfor classifier boundary. The reason is execution-
structural rather than mathematical: the runtime matches only the current
weak head, so the outer `Obj` rule at line 9177 cannot match until nested line
5481 has first changed `Hom_cat(Catd_cat(K),E,D)` into `Functord_cat(K,E,D)`.
Lambdapi's contextual rewriting composes those steps directly.

The corrected immutable proposal is
[`src/v3_2/pathind_fixed_source_proposal_v4.ts`](../src/v3_2/pathind_fixed_source_proposal_v4.ts),
with focused checks in
[`tests/v3_2_pathind_fixed_source_proposal_v4_tests.ts`](../tests/v3_2_pathind_fixed_source_proposal_v4_tests.ts).
It preserves v3 and adds one generic-runtime, subject-checked fusion derived
only from active lines 5481 and 9177:

```text
Obj(Hom_cat(Catd_cat(K),E,D))
  ↪ Obj(Transf_cat(K,Cat_cat,E,D)).
```

The exact local boundary becomes **5/9/0/6**. Five runtime observations, nine
bounded-oracle assertions, the rho-section consumer, and eight strict
negatives remain unchanged. The fusion introduces no mathematical rule,
nested-normalization engine, Core/checker/evaluator branch, signature
substitution, active Lambdapi edit, or later/public effect. V3 checkpoints
`bfe09e3` and `880593e` remain backtracking evidence but no longer authorize
implementation.

Corrected-v4 proposal validation on 2026-08-10 is:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw exec eslint \
  src/v3_2/pathind_fixed_source_proposal_v4.ts \
  tests/v3_2_pathind_fixed_source_proposal_v4_tests.ts \
  tests/main_tests.ts
  passed

node --require ts-node/register --test \
  tests/v3_2_pathind_fixed_source_proposal_v4_tests.ts
  6 tests / 1 suite: 6 passed, 0 failed

git diff --check
  passed
```

No Lambdapi or long repository aggregate was run for this immutable-data
correction. Active source bytes, shared engines, package/workspace setup, and
public surfaces are unchanged; focused gates directly cover it. Proposal v4
is non-authorizing, and checkpoint `f4101e2` freezes those exact bytes.

The separate immutable review is
[`src/v3_2/pathind_fixed_source_review_v4.ts`](../src/v3_2/pathind_fixed_source_review_v4.ts),
with focused checks in
[`tests/v3_2_pathind_fixed_source_review_v4_tests.ts`](../tests/v3_2_pathind_fixed_source_review_v4_tests.ts).
It approves only checkpoint `f4101e2` under the user's standing unattended
delegation, with later human supersession. Authorization is limited to the
exact root-only **5/9/0/6** implementation: exact active Fibre signatures,
lines 7865 and 9177, and the one subject-checked fusion derived from active
lines 5481 and 9177. It expressly denies a nested-normalization engine,
checker/signature/body/owner changes, every 1D/1E/1F or public effect, active
Lambdapi edits, and integration or release.

Corrected-v4 separate-review validation on 2026-08-10 is:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw exec eslint \
  src/v3_2/pathind_fixed_source_review_v4.ts \
  tests/v3_2_pathind_fixed_source_review_v4_tests.ts \
  tests/main_tests.ts
  passed

node --require ts-node/register --test \
  tests/v3_2_pathind_fixed_source_proposal_v4_tests.ts \
  tests/v3_2_pathind_fixed_source_review_v4_tests.ts
  11 tests / 2 suites: 11 passed, 0 failed

git diff --check
  passed
```

No Lambdapi or long aggregate is relevant to this behavior-free review.
Review checkpoint `397472f` freezes that decision. The exact v4 semantic
implementation may now resume; the review authorizes nothing beyond it.

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
