# TypeScript DTT/LF Continuation For emdash v3.2 — Living Plan

Date: 2026-07-24
Plan-ID: TS-ELAB-V3.2-DTT-LF-CONTINUATION
Depends-On: the completed
[`TYPESCRIPT_ELABORATOR_V3_2_MASTER_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_MASTER_PLAN.md),
the active emdash v3.2 mathematical authorities, and the exact
`emdash-v3.2-mvp-1` profile
Supersedes: forward TypeScript growth guidance after `emdash-v3.2-mvp-1`;
does not rewrite or supersede the completed profile's historical decisions,
approvals, artifacts, or trust claims
Side-Task-Ledger: architecture decisions, implementation slices, experiments,
validation, and human-review gates in this file
Infinity-Codex-Origin: consolidated architecture review
`infinity-codex:019f9243-9fba-7c73-861b-ff4eacf0c56c:019f9590-20ac-7b82-815e-2136c927554e`
Infinity-Codex-Decision-Responses: the review named above; active code,
authorities, and this plan outrank the archived response
Human-Decision-Record: on 2026-07-24 the user said that they mostly agreed
with the consolidated review, approved creating this separate continuation
plan, and directed implementation to start through a persistent `/goal`
objective; later on 2026-07-24 the user said “Approve H-DTTLF-01 and
H-DTTLF-02 as proposed”; and then “Approve
H-DTTLF-02/DIRECTED-1B as proposed.” The latter message also authorized
temporary local checkpoint commits when useful for tracking and backtracking.
Later on 2026-07-24 the user said “Approve
H-DTTLF-02/DIRECTED-FOUNDATION-1 as proposed.”
Status: active proposed continuation and implementation ledger;
DTTLF-PLAN-0, LF-1A through LF-1C, and LF-SURFACE-1 are complete;
H-DTTLF-01 and the DIRECTED-1A instance of H-DTTLF-02 are approved as
proposed; DIRECTED-1A is complete; the DIRECTED-1B instance of H-DTTLF-02 is
approved as proposed; isolated integration exposed an earlier unreviewed
three-rule facade prerequisite, so DIRECTED-FOUNDATION-1 is proposed and its
H-DTTLF-02 instance is approved and implemented; deeper executable checking
then exposed one decoded Cat-hom prerequisite, so DIRECTED-FOUNDATION-2 is
proposed and its H-DTTLF-02 instance is pending before DIRECTED-1B integration
can complete
Completed-profile comparison checkpoint:
`0b585e955c5a59f87be9daf9024f37e2b3403982`
Latest local implementation checkpoint:
`741668201b8af1a4c3eae9a104fa952b7f2ff9e7`
Historical pre-implementation baseline:
`a06433e57cba95e7d35f8577b7c71912862c3d25`

## Purpose And Operating Contract

This plan reopens TypeScript product development after completion of the exact
`emdash-v3.2-mvp-1` profile. It records the corrected dependent-type-theory
architecture, restores the required outer logical-framework layer, and then
drives consumer-led transfer of representative active categorical/directed
DTT constructions.

The completed master plan remains the historical authority for
`emdash-v3.2-mvp-1`, including H-01, H-03/D-023, H-04/D-030, H-05/D-039, the
16-owner manifest, its three reviewed runtime rules, and every claim that was
explicitly granted or withheld. This plan must not silently broaden or mutate
that profile. New computation, owners, rules, manifests, hashes, evaluators,
and trust claims belong to a new candidate boundary.

This is a living implementation plan. Recover actual state from active code,
checks, Git, the active mathematical authorities, and this ledger on every
continuation. Correct, refine, split, reorder, reject, or defer a slice when
bounded implementation evidence requires it, and synchronize that evidence
here. Architecture accepted for candidate implementation is not automatically
a product-trust or metatheory approval.

The authority order is:

1. `../emdash2/emdash3_2.lp`;
2. the active one-way extensions named in `../emdash2/AGENTS.md`;
3. `../emdash2/emdash3_2_checks.lp`;
4. the current SOP and status report;
5. `../emdash2/reports/EMDASH_FOUNDATIONS.md`;
6. the canonical-surface-syntax report;
7. the active plan selected through `../emdash2/reports/INDEX.md`;
8. this cross-layer implementation plan;
9. the completed TypeScript master plan and old TypeScript implementation as
   historical evidence only.

Lambdapi remains the mathematical specification and conformance oracle.
Until a new candidate crosses its own recorded graduation boundary, it is not
the deployed authority and does not change the already-deployed exact
`emdash-v3.2-mvp-1` boundary.

The persistent-goal Git workflow is defined by
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md).
The launch prompt at the end of this plan is part of this objective when the
user invokes it. On 2026-07-24 the user explicitly authorized temporary local
checkpoint commits when useful for tracking and backtracking. That
authorization applies only to bounded green tranches on the existing
`goal/typescript-elaborator-v3.2` branch/worktree after plan synchronization
and exact staged-diff review. It does not authorize new branches/worktrees,
amend, rebase, reset, history rewriting, push, merge, PR creation, publication,
release, branch/worktree deletion, or cleanup of unrelated state.

## Corrected Architectural Verdict

The earlier assessment was too narrow and is revised as follows:

- The active emdash categorical kernel already constitutes a
  categorical/directed DTT.
- The still-deferred `Σ_F ⊣ F* ⊣ Π_F` package is a stronger general
  adjunction/coherence interface, not a prerequisite for calling the existing
  theory directed DTT.
- The groupoid-level kernel already contains genuine DTT structure—`Grpd`,
  decoding, equality/J, `Σ_`, and `Pi_grpd`—but the systematic
  specialization/closure connecting the full directed categorical tower to
  the groupoidal/ordinary-DTT tower remains a separate research and
  kernel-development programme.
- The real architectural omission is in TypeScript: the new Core retained
  dependent binders and checking but deliberately omitted generic
  β-reduction, transparent definitions/δ-reduction, and let/ζ-reduction. It
  therefore does not yet implement the required outer λΠ logical framework.
- We should reopen the closed `mvp-1` sequence through this continuation, but
  we should not redesign everything from scratch.

## The Corrected Three-Layer Picture

| Layer | Mathematical role | Lambdapi v3.2 state | TypeScript state |
| --- | --- | --- | --- |
| Outer λΠ LF | Dependent binders, functions, application, definitions and computation; hosts the emdash object theory | Supplied by Lambdapi | Syntax and bidirectional checking exist, but generic β/δ computation is missing |
| Groupoidal/ordinary DTT | `Grpd`, `τ`, equality/J, dependent `Σ_` and `Pi_grpd` | Substantial active implementation; comprehensive closure against the directed tower remains future work | Mostly not transferred |
| Categorical/directed DTT | Categories as contexts/shapes, Cat-valued families, reindexing, totalization, sections, dependent homs and higher action | Active and computational | Only a very small owner subset has been transferred |

These are complementary layers, not alternatives. The intended TypeScript
product should eventually contain both the outer LF and the inner
categorical/directed theory:

```text
TypeScript surface / scoped builder
        ↓
minimal outer λΠ LF
  Π, λ, application, β, transparent definitions/δ,
  contextual metas, bidirectional elaboration
        ↓
backend-neutral explicit emdash Core
        ↓
inner categorical/directed DTT owners
  Catd, Pullback, Sigma_cat, Pi_cat, Functord/Transfd,
  internal Pi, dependent hom, total transport, uncurrying
        ├──→ bounded TypeScript evaluator/checker
        └──→ deterministic Lambdapi conformance emission
```

The groupoidal closure programme belongs alongside this architecture but does
not block the first two layers.

## Why The Inner Kernel Is Already Directed DTT

The active mathematical guide explicitly presents categories, Cat-valued
families, dependent sums, dependent products, and dependent homs as one
computational theory, with directedness arising from nontrivial base arrows
and their naturality data
([Foundations](../emdash2/reports/EMDASH_FOUNDATIONS.md)).

The active kernel supplies the relevant categorical judgments:

- `K : Cat` acts as a directed context or shape.
- `E : Catd K` is a functorial dependent category/type over `K`.
- `Pullback_catd E F` is substitution/reindexing along a functor
  (`emdash3_2.lp`, directed-family section beginning near line 11804).
- `Sigma_cat E` is the total category `Σ k : K, E[k]`, with dependent
  objects, dependent homs, composition, projection, and canonical transport
  arrows (`emdash3_2.lp`, Sigma section beginning near line 12314).
- `Pi_cat E` is the category of sections of `E`, with objects as dependent
  programs/terms and `Transfd_cat` as the next hom (`emdash3_2.lp`, Pi
  section beginning near line 12103).
- `Pi_int_funcd` internalizes Pi over varying bases, and
  `Pi_pullback_funcd` exposes its reindexed pointwise form
  (`emdash3_2.lp`, internal-Pi section beginning near line 12186).
- `Sigma_catd_functord_catd` converts a genuinely object-dependent telescope
  `FF : k ; R[k] ⊢ Cat` into a family over the total category `Σ k, R[k]`
  (`emdash3_2.lp`, telescope-uncurrying section beginning near line 12689).
- `Sigma_transfd_funcd` performs the corresponding
  transformation/program uncurrying.
- Sections over the Sigma first-projection pullback compare directly with
  displayed functors:
  `Pi_cat(Sigma_cat R, Sigma_proj1_pullback_catd R D) ≃ Functord_cat R D`
  (`emdash3_2.lp`, comparison section near line 12519, with executable checks
  in `emdash3_2_checks.lp` near line 11873).

Thus the appropriate reading of a dependent telescope is:

```text
K                         context/shape
R : Catd K                first dependent category
Sigma_cat R               extended context K.R
FF : k ; R[k] ⊢ Cat       second category depending on k and r
Sigma_catd_functord_catd FF
                          family over K.R
Sigma_cat (...)           further dependent totalization
Pi_cat (...)              sections/dependent programs
```

The earlier objection treated a fibrewise CwF-style `Σ_A B` or
`Π_A B : Ty(Γ)` as the only acceptable closure criterion. That was the wrong
criterion for assessing emdash on its own intended categorical terms. The
existing totalization, section, internal-Pi, and uncurrying tower is exactly
the directed-DTT machinery being developed.

The future general adjunctions `Σ_F ⊣ F* ⊣ Π_F` and full coherence APIs remain
valuable, but the active reports classify them as future extensions to an
already-existing foundation
([current status and SOP](../emdash2/reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md)).

## The Groupoidal Side

The kernel already begins with a real groupoid/type universe and dependent
equality:

- `Grpd : TYPE`, `τ : Grpd → TYPE`, equality, and dependent path induction
  (`emdash3_2.lp`, groupoid universe/equality section near line 259);
- dependent pairs `Σ_`, projections, elimination, and path-over computation
  (`emdash3_2.lp`, encoded-Sigma section near line 591);
- dependent products `Pi_grpd` with decoding to an outer dependent function
  type (`emdash3_2.lp`, groupoidal-Pi section near line 725).

It would therefore also be inaccurate to describe groupoidal DTT as absent.
What is incomplete is the systematic closure/specialization story connecting
the full directed categorical machinery to the groupoidal universe:

- which groupoidal bases and fibres are closed under the categorical Sigma/Pi
  constructions;
- how categorical transport, section action, and dependent hom reduce to path
  transport, `eq_apd`, `Σ_`, `Pi_grpd`, and J;
- whether existing owners such as `Pi_grpd`, `Path_cat`, `Grpd_cat`, and
  groupoidality witnesses suffice;
- which additional stable owners are justified by concrete consumers;
- what computational, proof-time, and theorem-level comparisons connect the
  outer LF, groupoidal DTT, and directed DTT.

This deserves its own Lambdapi-first plan. It must inventory existing bridges
before proposing new primitives, follow the ordinary owner-position/SOP
workflow, and transfer a reviewed result to TypeScript afterwards. It is not
a blocker for calling the current categorical theory directed DTT.

## What Happened To The Original TypeScript LF

The architecture review inspected `main` at `30394f9` and the clean descendant
goal worktree at the completed-profile checkpoint `0b585e9`.

The original TypeScript implementation contained most mechanics of an outer
dependent LF:

- HOAS-style `Pi`, `Lam`, and `Let`, generic application, holes, and dependent
  bodies in the former `src/types.ts`;
- bidirectional dependent application, implicit insertion, lambda checking,
  and Pi formation in the former `src/elaboration.ts`;
- β-reduction, ζ-reduction, transparent global unfolding, optional η, and
  user rewrite rules in the former `src/reduction.ts`;
- WHNF-based definitional equality in the former `src/equality.ts`;
- checked global definitions in the former `src/globals.ts`;
- Miller-pattern flex-rigid solving in the former `src/unification.ts`.

The focused equality, dependent-type, Church-encoding, implicit-Church, and
let-binding corpus passed 29 tests with no failures at the historical
checkpoint. The old LF capability was executable evidence, not merely an
abandoned design note.

It was nevertheless unsuitable for direct preservation as the trusted v3.2
kernel:

- `Type : Type` was accepted, unlike the current Lambdapi-aligned `TYPE/KIND`
  boundary.
- Definitions, holes, constraints, and rule registries were globally mutable.
- The term union mixed generic LF syntax with stale category-specific
  constructors.
- Arbitrary user rewriting had no frozen authority/profile boundary.
- Binder bodies were opaque JavaScript functions, complicating traversal,
  serialization, hashing, and persistence.
- Several algorithms reconstructed body syntax by opening closures with
  name-bearing variables and then performing name-based substitution.

The loss of outer computation was an explicit migration decision, not a
consequence forced by the new architecture. D-029 excluded generic-call beta
and declaration unfolding, while D-034 explicitly declined to port generic
beta/eta during migration. The migration inventory consequently retained only
structural alpha equality and dependent checking.

That was internally consistent with the narrowly frozen 16-owner/three-rule
`mvp-1`, but it was too narrow for the clarified overall product objective.
The sequencing decision revised here is deleting the old LF before generic LF
computation had been reimplemented in the new Core.

H-03, H-04, and H-05 remain valid. They approved exactly the content-pinned
`mvp-1` profile; they did not approve permanent exclusion of outer DTT. This
continuation preserves `mvp-1` unchanged and introduces a new candidate
rather than silently broadening it.

## HOAS Versus De Bruijn

The switch to a locally nameless Core was technically reasonable, although it
deserved a clearer comparative design record.

The old representation was ergonomic HOAS at construction time, but
operationally it was a hybrid:

- algorithms opened bodies using `Var(paramName, true)`;
- alpha comparison reused a chosen binder name;
- capture avoidance depended on `replaceFreeVar` and global fresh names;
- some traversals explicitly could not inspect lambda/Pi bodies because they
  were JavaScript functions.

JavaScript closures cannot be structurally inspected, deterministically
serialized, deep-frozen, hashed in manifests, or safely persisted as trusted
Core data. The new explicit representation makes alpha-equivalence structural
and already provides capture-safe `kernelShift`, `kernelSubstitute`, and
`kernelInstantiate`.

Therefore:

- Keep the locally nameless explicit Core.
- Do not blame De Bruijn indices for missing DTT computation. Generic β is
  nearly mechanical: instantiate a `KernelLambda` body with the first
  argument and preserve any remaining call spine.
- Restore HOAS-like ergonomics in a scoped builder layer, not by storing
  arbitrary JavaScript functions in trusted Core.

The intended TypeScript API can still look like:

```ts
pi("x", A, x => B(x))
lam("x", A, x => body(x))
let_("x", value, x => body(x))
```

The callback runs once using an opaque binder token. Lowering resolves token
identity to a De Bruijn index, after which only explicit Core remains. This
provides the old authoring convenience without its representation problems.

## Is The Architecture Settled And Scalable?

At the architectural level, yes—with this correction:

- explicit locally nameless Core is the trusted representation;
- a safe HOAS/PHOAS-style builder is the direct TypeScript surface;
- generic λΠ computation is an outer layer shared by every emdash owner;
- categorical operations remain schema-driven semantic owners, not bespoke
  AST tags;
- product manifests separately authorize signatures, runtime rules, and
  claims;
- Lambdapi remains the mathematical specification and conformance oracle.

The implementation is not yet mechanically scalable as a finished DTT product
because two large coverage gaps remain:

1. outer β/δ/ζ computation is absent;
2. only a tiny portion of the active directed-DTT owner/rule tower has been
   promoted into TypeScript.

Once outer LF computation is installed, signature/catalog expansion is
largely mechanical. Mathematical runtime semantics will never be entirely
automatic: every promoted rule still requires owner-position, authority,
subject-reduction, and interaction review. That is a feature of the trust
architecture, not an architectural failure.

The resulting policy is:

- no full restart;
- reopen the product plan;
- settle the outer LF before another broad semantic-owner tranche;
- then scale the inner directed-DTT catalog through consumer-led vertical
  slices;
- keep groupoidal closure as a separate Lambdapi-first programme.

## Objective

Implement both dependent layers of the TypeScript product:

1. a minimal Lambdapi-aligned λΠ logical framework over explicit Core;
2. a representative, scalable transfer of the active categorical/directed
   DTT.

Preserve `emdash-v3.2-mvp-1` unchanged as a historical approved profile.
Treat comprehensive groupoidal specialization/closure as a separately owned
Lambdapi-first plan.

## Architecture Decisions

The user accepted these as the direction for candidate implementation by
requesting this plan and its implementation. A later product or mathematical
trust claim still requires the corresponding human gate.

- **DTTLF-001 — Three-layer architecture.** Distinguish outer λΠ LF, inner
  categorical/directed DTT, and groupoidal/ordinary-DTT specialization. The
  product requires the first two; the third is an explicit later programme.

- **DTTLF-002 — Outer LF computation.** Add generic β-reduction, checked
  transparent definitions with δ-unfolding, and optional surface let/ζ.
  Integrate them with contextual metas and the existing checker. Eta remains
  disabled initially unless a reviewed conformance consumer requires it.

- **DTTLF-003 — Binder representation.** Retain locally nameless explicit
  Core. Add a scoped HOAS/PHOAS-style TypeScript builder whose callbacks are
  lowered once and never stored in trusted Core.

- **DTTLF-004 — Universe discipline.** Preserve `TYPE/KIND`; do not port the
  old `Type : Type` behavior. Adapt old generic LF tests to the active
  `Grpd`/`τ` and category classifier hierarchy.

- **DTTLF-005 — Profile preservation.** Do not mutate the
  H-03/H-04/H-05 `mvp-1` manifest or its termination claim. The combined
  β/δ/semantic evaluator is a new candidate profile with a fresh hash and
  later trust review.

- **DTTLF-006 — Directed-DTT transfer.** Select owner/rule slices from active
  `emdash3_2.lp` by concrete telescope consumers. Seed candidates include
  `Functord_cat`, `Transfd_cat`, `Sigma_cat`, Sigma projection/transport,
  `Pi_func`, `Pi_int_funcd`, `Sigma_catd_functord_catd`, and
  `Sigma_transfd_funcd`; the exact promoted set remains evidence-driven.

- **DTTLF-007 — Groupoidal continuation.** Open a separate Lambdapi plan to
  inventory and complete the relationship among `Grpd`, `Σ_`, `Pi_grpd`,
  equality/J, `Path_cat`, categorical groupoidality, and the directed family
  tower. Propose new primitive owners only after a failed current-owner
  consumer.

- **DTTLF-008 — Metatheory separation.** The H-04 projection-count
  termination argument applies only to its frozen three-rule runtime program.
  It must not be reused for β/δ: β can duplicate an argument, and δ introduces
  a distinct dependency/unfolding measure. The new engine remains bounded,
  traceable, and oracle-checked until separate termination, confluence, and
  subject-reduction claims are reviewed.

- **DTTLF-009 — Candidate isolation.** LF-1A starts in a new module and test
  surface. It does not change `coreRuntimeDefinitionalCompare`, the browser
  entry point, `CORE_MVP_MANIFEST`, `CORE_MVP_RELEASE_POLICY`, or any release
  completion record. Integration occurs only in the new candidate path.

- **DTTLF-010 — Separate reviewed continuation artifacts.** Preserve
  `LF-PROFILE-1` and `DIRECTED-1A` as immutable pre-review proposals. Record
  the H-DTTLF-01 and H-DTTLF-02 approvals separately, including their exact
  snapshots and non-effects. Neither approval changes the browser or deployed
  MVP profile.

- **DTTLF-011 — Isolated LF primitive catalog.** Compile each reviewed
  categorical owner signature into an ordered opaque declaration in the
  approved outer-LF environment. Candidate terms invoke those primitives
  through generic Pi calls, not by widening the frozen
  `CORE_OWNER_SCHEMAS`. A backend-only external-reference map serializes the
  same Core primitive identity to its audited Lambdapi owner without emitting
  a shadow declaration. Reject this design if the nested-telescope consumer,
  wrong-base/wrong-family negatives, non-collapse, or deterministic Lambdapi
  probe cannot pass without changing the base catalog or browser graph.

- **DTTLF-012 — Make active facade prerequisites explicit.** If a reviewed
  directed owner cannot be signature-checked without an earlier active
  computation that the frozen MVP intentionally recorded but did not grant
  to its checker, do not hide that computation in declaration validation or
  reinterpret it as structural compatibility. Inventory it as a separate
  catalog-local prerequisite, preserve stable category heads and the default
  LF/MVP runtime, and trigger H-DTTLF-02 before execution. This keeps the
  runtime/proof-time distinction observable and prevents Lambdapi's full
  imported conversion relation from masking a TypeScript dependency.

## Implementation Ledger

Only one row may be actively implemented at a time. “Pending” means scoped
but not authorized as a semantic product claim. “Deferred” means the recorded
prerequisite must be satisfied before work begins.

| Slice | State | Dependency / exit evidence |
| --- | --- | --- |
| DTTLF-PLAN-0 | **complete** | Published this correction, old-LF inventory, groupoidal boundary, routing links, recovery record, and launch prompt; documentation-proportional gates passed |
| LF-1A — generic beta | **complete** | Added isolated bounded weak-head β using `kernelInstantiate`; flat/nested spines, plicity, nested-binder capture avoidance, stuck/empty cases, budgets, deterministic traces, frozen-MVP non-beta, and bounded Lambdapi parity pass |
| LF-1B — definitions/delta | **complete** | Added a persistent candidate environment with checker-validated optional bodies, conservative explicit transparency, strictly earlier dependency ordinals, structural cycle prevention, bounded δ traces, and opaque/forward/self/ill-typed negatives |
| LF-1C — combined conversion | **complete** | Added one globally budgeted, path-traced zonk/β/δ/reviewed-runtime comparator; opt-in checker/session hooks, annotated-lambda inference, rigid-constraint/Miller-pattern revisit, candidate definition probes, and bounded Lambdapi parity pass without changing released defaults |
| LF-SURFACE-1 | **complete** | Added a one-shot scoped builder with opaque builder-local binder tokens, immediate callback lowering to de Bruijn Core, plicity/mode preservation, and dependent `let_` as annotated β sugar; alpha/beta/definition/implicit/dependent-let and foreign/escaped/open/`Type : Type` negative tests pass |
| DIRECTED-1A | **complete — H-DTTLF-01/02 approved** | Compiled the reviewed three-signature/zero-rule proposal into an isolated opaque LF primitive catalog; generic Pi application, positive nested telescope, scoped-builder lowering, wrong-base/wrong-family/non-collapse negatives, frozen catalog/browser/MVP boundaries, deterministic active-Lambdapi emission, and the full repository gate pass |
| DIRECTED-FOUNDATION-1 | **complete — H-DTTLF-02 approved** | Executes exactly the three approved decoded `Obj(Cat_cat)`, `Obj(Catd_cat)`, and `Obj(Functord_cat)` reductions as an immutable opt-in catalog runtime; five implementation tests preserve stable category heads, the default LF, and the still-unapproved decoded Cat-hom case |
| DIRECTED-FOUNDATION-2 | **proposal complete — H-DTTLF-02 pending** | Approve or reject the one decoded `Hom_Cat(A,B)` to `Functor(A,B)` runtime consequence required to use Cat-valued base-arrow action as an ordinary functor; no owner, proof-time rule, raw-classifier/category-head/default-LF/MVP/browser change, or metatheory claim |
| DIRECTED-1B | **paused — own and FOUNDATION-1 H-DTTLF-02 approved; FOUNDATION-2 pending** | After DIRECTED-FOUNDATION-2 is decided, integrate the approved five owners, one checked transparent mirror, the approved prerequisite program, and three DIRECTED-1B-owned runtime rules under the same LF budget; retain every recorded general-Sigma-hom/uncurrying/product deferral |
| DIRECTED-1C | pending | Transfer section/internal-Pi and telescope uncurrying for that consumer |
| DIRECTED-GRADUATE-1 | pending | Run the shared TypeScript/Lambdapi graduation example and review the new owner/rule/metatheory/profile boundary |
| GROUPD-PLAN-0 | **deferred** | Separate Lambdapi-first plan; begins only after directed candidate work or a concrete groupoidal consumer justifies it |

## LF-1A Detailed Contract

The first implementation slice is intentionally smaller than a new conversion
engine:

1. Introduce a candidate outer-LF module that has no production-browser
   import edge.
2. Reduce a `KernelCall` whose weak head is a `KernelLambda` by
   capture-safe `kernelInstantiate`.
3. Consume exactly the first call argument, require matching binder/argument
   plicity, and preserve the ordered residual spine.
4. Repeat only under an explicit finite step budget and return a structured
   stopped result rather than looping or throwing on budget exhaustion.
5. Record deterministic β trace entries sufficient to inspect before/after,
   binder plicity, and residual-spine size.
6. Leave non-lambda heads, empty calls, and plicity mismatches stuck. The
   checker, not an unchecked evaluator, owns ill-typedness.
7. Test nested binders and capture avoidance with explicit bound/free-variable
   assertions, not only pretty-printed equality.
8. Compare a representative well-typed β judgment with Lambdapi through a
   bounded opt-in/generated probe.

LF-1A does not yet promise congruence reduction under arbitrary constructors,
δ-unfolding, ζ, eta, conversion-checker integration, normalization, general
termination, confluence, or subject reduction. LF-1C owns combined conversion.

## LF-1B And LF-1C Safety Constraints

The initial δ fragment must be acyclic by construction:

- declarations remain immutable;
- a checked body may mention only declarations already present in its
  declaration environment;
- transparency is explicit and defaults conservatively;
- opaque definitions never unfold during conversion;
- trace and budget accounting includes every δ step;
- no global definition registry or ambient mutable rewrite set is introduced.

The combined evaluator must use a fresh candidate identity. It may reuse the
frozen semantic runtime program as a component, but it may not claim that the
old H-04 measure proves termination of the combination. A bounded engine is a
safe executable implementation, not a proof of normalization.

## LF-1A Completion Record

LF-1A added `src/v3_2/lf.ts` as a candidate-only module exported through the
development barrel but not the browser product entry point. One step:

- views nested calls as one ordered left-associated spine without counting
  flattening as computation;
- contracts only a lambda head with a matching first-argument plicity;
- uses `kernelInstantiate` for capture-safe substitution;
- preserves residual argument order, plicity, value identity, and
  provenance;
- reports neutral/empty calls, plicity-stuck terms, and budget exhaustion as
  distinct structured results;
- records deterministic β trace entries and the next-redex summary.

The implementation does not traverse semantic-owner arguments or binder
bodies, unfold declarations, integrate with the checker, or change
`coreRuntimeDefinitionalCompare`. A focused regression explicitly confirms
that the frozen MVP comparator still returns `not-equal` for the same β pair.

Validation on 2026-07-24:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw exec eslint src/v3_2/lf.ts tests/v3_2_lf_beta_tests.ts
  passed

node --require ts-node/register --test tests/v3_2_lf_beta_tests.ts
  7 tests / 1 suite: 6 passed, 1 opt-in probe skipped

timeout 60s env EMDASH_RUN_LAMBDAPI_PROBES=1 \
  node --require ts-node/register --test tests/v3_2_lf_beta_tests.ts
  7 tests / 1 suite: all passed, including the generic β oracle judgment

./scripts/pnpmw run check:ts
  workspace contract, typecheck, ESLint, and root tests passed
  259 tests / 30 suites: 238 passed, 21 opt-in probes skipped

git diff --check
  passed
```

## LF-1B Completion Record

LF-1B added `src/v3_2/lf_declarations.ts` without changing the frozen Core
declaration type. `CoreLfDeclarationEnvironment` maintains:

- the existing body-free environment consumed by the old checker;
- a parallel immutable candidate declaration record with optional checked
  body, explicit transparency, ordinal, and direct free-body dependencies.

Each extension validates its type, checks any body against that type in the
strictly preceding environment, and then inserts the declaration. Transparent
assumptions, self references, unknown/forward references, and ill-typed
bodies fail atomically. Because every stored body dependency has a smaller
ordinal, self and mutual δ cycles cannot be constructed through the API.

The bounded δ evaluator unfolds only a transparent reference weak head,
preserves any ordered call spine, distinguishes opaque/assumed/unknown/empty
or non-reference heads, and records the decreasing declaration ordinal in
each trace entry. A focused checked identity demonstrates the intended
separate `δ` then `β` layers; LF-1C owns their interleaving and Lambdapi
comparison.

Validation on 2026-07-24:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw exec eslint \
  src/v3_2/lf_declarations.ts tests/v3_2_lf_definition_tests.ts
  passed

node --require ts-node/register \
  --test tests/v3_2_lf_definition_tests.ts
  7 tests / 1 suite: all passed

./scripts/pnpmw run check:ts
  workspace contract, typecheck, ESLint, and root tests passed
  266 tests / 31 suites: 245 passed, 21 opt-in probes skipped

git diff --check
  passed
```

## LF-1C Completion Record

LF-1C added four candidate modules:

- `lf_conversion.ts` interleaves zonking, β, transparent δ, and the exact
  reviewed semantic runtime rules under one global operation budget. Its
  recursive comparator shares that budget across both sides and every
  congruence path.
- `lf_checker.ts` opts into combined comparison, annotated-lambda inference,
  and post-zonk rigid constraint conversion through protected hooks.
- `lf_probe.ts` emits checked transparent bodies to Lambdapi while emitting
  opaque definitions as body-free symbols.
- the existing checker/session received only protected default hooks. Their
  public construction, default behavior, frozen comparator, and browser
  import graph remain unchanged.

Candidate checking now accepts a direct annotated identity application,
transparent and β-convertible expected types, and a weakened contextual
Miller-pattern assignment whose later rigid constraint closes by β. Solved
meta zonking counts as an explicit combined transition when it changes the
term. Plicity mismatch remains stuck and eta remains disabled.

The shared oracle case performs, in order:

```text
transparent definition reference
  --δ--> checked identity lambda application
  --β--> reviewed full-projection redex
  --runtime--> capped projection
```

The first attempted fixture also exposed an existing presentation boundary:
the typed surface's rich direct `Hom` classifier and the generic signature
checker's `Obj(Hom_cat ...)` classifier require an active kernel comparison
outside the three-rule MVP program. LF-1C does not invent or promote that
comparison. The final fixture uses the signature-aligned classifier and
records the richer bridge as consumer evidence for a later owner/rule review.

Validation on 2026-07-24:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw exec eslint \
  src/v3_2/checker.ts src/v3_2/session.ts \
  src/v3_2/lf_conversion.ts src/v3_2/lf_checker.ts \
  src/v3_2/lf_probe.ts tests/v3_2_lf_conversion_tests.ts
  passed

node --require ts-node/register \
  --test tests/v3_2_lf_conversion_tests.ts
  8 tests / 1 suite: 7 passed, 1 opt-in probe skipped

timeout 60s env EMDASH_RUN_LAMBDAPI_PROBES=1 \
  node --require ts-node/register \
  --test tests/v3_2_lf_conversion_tests.ts
  8 tests / 1 suite: all passed, including δ-β-runtime oracle parity

./scripts/pnpmw run check:ts
  workspace contract, typecheck, ESLint, and root tests passed
  274 tests / 32 suites: 252 passed, 22 opt-in probes skipped

git diff --check
  passed
```

## LF-SURFACE-1 Completion Record

LF-SURFACE-1 added `CoreLfScopedBuilder` as an untrusted ergonomic layer over
explicit Core:

- binder callbacks run immediately and exactly once;
- opaque builder-local token identities lower to de Bruijn indices;
- no callback or JavaScript closure is stored in trusted Core;
- alpha-equivalent binder hints produce structurally equal Core;
- explicit and implicit plicity plus binder mode survive lowering;
- dependent `let_` lowers to an annotated-lambda call, so generic β owns its
  computation and no new Core node or ζ rule is added;
- foreign, escaped, open embedded, malformed-arity, and `Type : Type`
  construction paths are rejected.

The builder produces terms accepted by the candidate checker and checked
transparent-definition environment. It remains outside the production
browser entry point.

Validation on 2026-07-24:

```text
node --require ts-node/register --test tests/v3_2_lf_builder_tests.ts
  8 tests / 1 suite: all passed

./scripts/pnpmw run check:ts
  workspace contract, typecheck, ESLint, and root tests passed
  282 tests / 33 suites: 260 passed, 22 opt-in probes skipped

git diff --check
  passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  passed the root TypeScript gate, all 19 mandatory TypeScript/Lambdapi
  differential judgments, all 41 Lambdapi kernel/example metric targets,
  39 kernel-script tests, five document-registry tests, source/report/book
  checks, strict inferred-slot audit, and strict generated-catalog check
```

## Consumer-Led Directed Transfer

The directed tranche starts only after the outer candidate conversion path is
usable. Each selected owner/rule must have:

- a concrete nested-telescope consumer;
- its exact active Lambdapi owner position;
- a generated signature comparison;
- a positive computation or proof-time comparison as appropriate;
- a negative wrong-base, wrong-fibre, or non-collapse case;
- an authority classification distinguishing product computation,
  conformance-only evidence, and theorem-level equality;
- proportional warning, strict-LHS, catalog, health, example, and CI checks
  for any Lambdapi change.

Signature/catalog expansion can be schema-driven and mechanical. Runtime
semantics cannot be promoted mechanically: every rule still needs
mathematical and interaction review.

### DIRECTED-1A Authority Inventory And Exact Proposal

Experiment `DTTLF-DIRECTED-1A-E01` froze the smallest owner set that forms the
graduation example's nested Cat-valued telescope. The active declarations,
not the stale TypeScript prototype, imply:

| Candidate Core owner | Active owner position | Exact dependent signature |
| --- | --- | --- |
| `displayed-functor-category` | `Functord_cat` in “3d. Directed-family and displayed-arrow classifiers” | `{K : Cat} → (E : Catd K) → (D : Catd K) → Cat`; `K` implicit, `E` and `D` explicit |
| `sigma-category` | `Sigma_cat` in “9a. Sigma totals, Sigma homs, and projection” | `{K : Cat} → (E : Catd K) → Cat`; `K` implicit and `E` explicit |
| `sigma-telescope-family` | `Sigma_catd_functord_catd` in “9c. Families over Sigma totals and displayed-transfor uncurrying” | `{K : Cat} → {R : Catd K} → (FF : Functord R (Const_catd K Cat_cat)) → Catd (Sigma_cat R)`; `K` and `R` implicit, `FF` explicit |

In explicit Core, `Catd K` continues to mean
`τ(Obj(Catd_cat K))`, and `Functord E D` means
`τ(Obj(Functord_cat E D))`. No duplicate `Catd`, `Functord`, or `Fibre_cat`
owner is proposed. `Fibre_cat` remains the active transparent view through
generic functor-object action.

The exact proposed authority boundary is:

- add only these three declaration-backed signatures and deterministic
  Lambdapi bindings to an isolated continuation candidate catalog;
- do not add them to the frozen 16-owner `emdash-v3.2-mvp-1` manifest or its
  browser export;
- propose no TypeScript runtime or proof-time rule in DIRECTED-1A;
- preserve `Functord_cat` as a stable facade: its comparison with
  `Transf_cat K Cat_cat E D` is proof-time only and must not become a runtime
  fold;
- defer the fibre projection of `Sigma_catd_functord_catd`, dependent-pair
  construction, Sigma projection/transport, and all action rules to
  DIRECTED-1B after separate owner/rule review.

The ignored bounded probe
`emdash2/tmp/probes/typescript_dttlf_directed_1a.lp` checked:

1. all three exact declaration signatures;
2. the positive fibre computation at `(k,r)`;
3. typed `eq_refl` for the proof-time `Functord_cat`/`Transf_cat` comparison;
4. runtime non-conversion of those two stable presentations;
5. wrong-base and wrong-displayed-family rejection; and
6. non-collapse of an arbitrary induced telescope family to a constant
   family.

The probe passed in 1.75 seconds under a 30-second limit. A subsequent bounded
`make -C emdash2 check` passed. No Lambdapi source, rule, warning baseline,
catalog, or health record changed.

`src/v3_2/directed_1a_proposal.ts` now preserves this boundary as an
executable pre-review artifact. Its backend-neutral proposal records the exact
dependent signature expressions and plicities, while a separate binding
record names the three Lambdapi declarations. Its validator:

- requires dependency ordering from current Core owners through
  `displayed-functor-category` and `sigma-category` to
  `sigma-telescope-family`;
- rejects current-catalog membership, reordered or duplicated candidate
  owners, unavailable slots/owners, malformed arity, and every nonempty rule
  set;
- binds the proposal to the exact live `emdash-v3.2-mvp-1` revision, hash,
  16 owners, and three rules;
- rejects backend-binding or exact-content drift; and
- remains exported only through the development barrel, not `browser.ts`.

Eight focused tests pass, including active-source declaration relocation,
deep-freeze, browser/catalog/MVP isolation, and all named drift cases. This
artifact still grants no catalog membership or semantic rule.

### DIRECTED-1B Authority Inventory And Exact Proposal

Experiment `DTTLF-DIRECTED-1B-E01` followed the first checked telescope to the
smallest closure that can construct `(k,r)`, compute the induced fibre, project
the base object, and type and compare action along the canonical total
transport. The active owner positions imply:

| Candidate Core owner | Active owner | Exact dependent signature and candidate treatment |
| --- | --- | --- |
| `decoded-dependent-pair` | `τΣ_` in “1a. Encoded dependent pairs” | `{a : Grpd} → (P : τ a → Grpd) → TYPE`; `a` implicit and `P` explicit; opaque imported type former |
| `dependent-pair` | generated `Struct_sigma` constructor in the same inductive declaration | `{a : Grpd} → {P : τ a → Grpd} → (x : τ a) → (u : τ(P x)) → τΣ_ a P`; `a` and `P` implicit; opaque imported constructor |
| `sigma-first-projection` | `Sigma_proj1_func` in “9a. Sigma totals, Sigma homs, and projection” | `{K : Cat} → (E : Catd K) → Functor (Sigma_cat E) K`; `K` implicit and `E` explicit; opaque imported primitive |
| `sigma-transport-arrow` | `sigma_transport_arrow` in “9b. Sigma maps and canonical transport arrows” | `{K : Cat} → (E : Catd K) → {x y : Obj K} → (p : Hom K x y) → (u : Obj(E[x])) → Hom (Sigma_cat E) (x,u) (y,E[p](u))`; signature imported opaquely although the active owner is a definition |
| `sigma-telescope-transport` | `Sigma_catd_transport_func` in “9c. Families over Sigma totals” | `{K : Cat} → {R : Catd K} → (FF : Functord R (Const K Cat)) → {x y : Obj K} → (p : Hom K x y) → (r : Obj(R[x])) → Functor FF[x][r] FF[y][R[p](r)]`; exact active body mirrored as a checked transparent definition |

The groupoidal pair former is not a competing architecture. It is the active
outer/groupoidal representation through which the categorical object rule
decodes `Obj(Sigma_cat E)`. Transferring this small bridge therefore exercises
both dependent layers without claiming comprehensive groupoidal closure.

The exact runtime proposal contains these three active rules, in deterministic
catalog order:

1. `directed.sigma-object.decode`:
   `τ(Obj(Sigma_cat E)) ↪ τΣ_ k : τ(Obj K), Obj(E[k])`;
2. `directed.sigma-first-projection.evaluate`:
   `Sigma_proj1_func(E)[(k,u)] ↪ k`; and
3. `directed.sigma-telescope-fibre.evaluate`:
   `Fibre(Sigma_catd_functord_catd(FF),(k,r)) ↪ FF[k][r]`.

`sigma-telescope-transport` is not a fourth rewrite. Its checked δ-body is the
active generic `fapp1_fapp0` action of the induced family along
`sigma-transport-arrow`, so symmetric LF conversion compares the named and
generic presentations without inventing a new rule. There is no proof-time
rule in this proposal.

The new runtime rules would be an exact, immutable extension owned by the
DIRECTED catalog. They run inside the already-reviewed runtime phase before
the frozen MVP subprogram and consume the same single global LF budget. The
default `LF-PROFILE-1`, `CORE_MVP_RUNTIME_PROGRAM`, arbitrary-user-rule
exclusion, browser graph, and deployed MVP remain unchanged. Opaque imports
continue to serialize by reviewed external-reference mapping. The one checked
transparent mirror is used for TypeScript δ, but deterministic emission maps
it to the active Lambdapi definition and emits no shadow declaration.

The consumer does **not** require the general
`Hom_cat(Sigma_cat E,(x,u),(y,v))` normal form. Transferring it now would force
the unused `homd_`, `id_funcd`, and `sigma_arrow` closure. DIRECTED-1B
therefore explicitly defers that rule, `sigma_arrow` computation,
`sigma_transport_arrow` unfolding, constant-family Sigma-to-product
computation, projection pullback/section uncurrying, and groupoidal Sigma path
elimination. A later concrete consumer may reopen any of them.

The ignored bounded probe
`emdash2/tmp/probes/typescript_dttlf_directed_1b.lp` passed both quiet and
warning-enabled runs under a 30-second bound. It checked all five signatures,
categorical pair typing through the object decoder, all three runtime
computations, the transparent telescope-transport comparison, wrong-base and
wrong-family rejection, and a wrong-endpoint transport rejection. The
warning-enabled run introduced no source or warning-baseline change; it only
reported the already-known imported-kernel warnings.

`src/v3_2/directed_1b_proposal.ts` freezes this as a backend-neutral,
binder-aware review artifact. It records dependent Pi/lambda/call syntax,
exact owner plicities and dependency order, the single checked definition,
typed runtime-rule telescopes, backend evidence separately from semantic
identities, the catalog-scoped runtime policy, frozen LF/DIRECTED-1A/MVP
prerequisites, and every deferral/non-effect. Eleven focused tests pass,
including active-source relocation, deep-freeze, browser/catalog isolation,
and deliberate boundary, prerequisite, expression, definition, rule, policy,
binding, MVP, and exact-content drift.

### DIRECTED-FOUNDATION-1 Prerequisite Discovered During Integration

Experiment `DTTLF-DIRECTED-1B-E02A` attempted to compile the approved
DIRECTED-1B signatures through the TypeScript checker. The first three owners
could be formed, but validation of `sigma_transport_arrow` stopped at the
fibre occurrence `fapp0 E x`: the slot records
`E : τ(Obj(Catd_cat K))`, whereas generic functor application requires
`E : τ(Functor K Cat_cat)`. Lambdapi accepts the signature because the active
kernel already computes the former to the latter. The frozen TypeScript MVP
does not: D-021 deliberately recorded the bridge authority without granting
that runtime conversion to its structural checker.

The first dependency pass found two companion object projections on the same
path. The resulting first prerequisite is exactly:

1. `directed.category-object.decode`:
   `τ(Obj(Cat_cat)) ↪ Cat`;
2. `directed.displayed-family.decode`:
   `τ(Obj(Catd_cat K)) ↪ τ(Functor K Cat_cat)`; and
3. `directed.displayed-functor.decode`:
   `τ(Obj(Functord_cat K E D)) ↪
   τ(Transf K Cat_cat E D)`.

These are not new Lambdapi rules and do not repair the kernel. They are exact
active runtime owners from the universe-category, directed-family, and
ordinary/displayed-transfor sections. They are nevertheless new executable
rules for the TypeScript continuation and were not part of either the frozen
MVP runtime or the approved DIRECTED-1B three-rule proposal. Treating them as
an undocumented type coercion or declaration-checker exception would erase
the runtime/proof-time distinction. The integration is therefore paused at a
fresh H-DTTLF-02 instance instead.

`src/v3_2/directed_foundation_proposal.ts` freezes the exact three-rule,
zero-owner, zero-proof-rule proposal and its active bindings. If approved,
the rules remain local to the directed catalog, execute before the three
DIRECTED-1B-owned rules and then the frozen MVP subprogram, and consume the
same global LF budget. The default LF profile, deployed manifest, browser
graph, arbitrary-user-rule exclusion, stable `Catd_cat` and `Functord_cat`
category heads, approved DIRECTED-1B artifact, and all deferrals remain
unchanged.

The ignored bounded probe
`emdash2/tmp/probes/typescript_dttlf_directed_foundation_1.lp` passed quiet
and warning-enabled checks under 30 seconds. It checked all three positive
object-level conversions and two negative category-head non-conversions; the
warning run reported only the already-known imported-kernel warnings. Five
focused proposal tests pass, including exact source relocation, deep freeze,
MVP/browser isolation, preservation of the approved DIRECTED-1B owner/rule
counts, and deliberate rule/policy/binding/content drift.

The user approved this exact three-rule boundary. The executable
`CoreDirectedFoundationRuntimeProgram` now preserves its review order,
remains opt-in to directed-catalog conversion, and leaves raw/stable category
heads and every unapproved classifier conversion irreducible. Five focused
implementation tests pass all three positive rules, plicity/facade near
misses, default-LF non-conversion, deep immutability, and the exact approved
rule list.

### DIRECTED-FOUNDATION-2 Follow-Up Discovered By Deeper Checking

Experiment `DTTLF-DIRECTED-1B-E02B` reran the same declaration construction
with only the approved FOUNDATION-1 program. Validation advanced past
`fapp0 E x` and stopped at the transported endpoint:

```text
fapp1_fapp0(E,p) : τ(Hom Cat_cat E[x] E[y])
expected         : τ(Functor E[x] E[y]).
```

The active kernel supplies the missing directed-universe computation:

```text
Hom_cat Cat_cat A B ↪ Functor_cat A B.
```

The transparent `Hom` and `Functor` classifiers make its exact decoded
consequence:

```text
τ(Hom Cat_cat A B) ↪ τ(Functor A B).
```

A diagnostic-only injected version of that single decoded rule allowed all
eight DIRECTED-1A/1B declarations to validate, including the checked
transparent `Sigma_catd_transport_func` body. No further signature dependency
appeared. Because the rule was absent from the approved FOUNDATION-1
three-rule artifact, the injection was not retained as implementation.

`src/v3_2/directed_foundation_2_proposal.ts` freezes a separate one-rule,
zero-owner, zero-proof-rule proposal. Its runtime scope is deliberately
narrower than the full Lambdapi conversion: only the decoded Cat-hom form
above may execute. Raw `Hom` classifiers and `Hom_cat` category heads remain
unchanged in TypeScript. If approved, deterministic order is FOUNDATION-1,
this decoded rule, the three DIRECTED-1B-owned rules, then the frozen MVP
subprogram, all under the existing single LF budget.

The ignored bounded probe
`emdash2/tmp/probes/typescript_dttlf_directed_foundation_2.lp` passed quiet
and warning-enabled checks under 30 seconds. It contains the positive
conversion, an expected-type consumer, an opposite-ambient near miss, and an
endpoint-reversal negative. The warning run reported only the already-known
imported-kernel warnings. Five focused proposal tests pass source relocation,
approved-prerequisite preservation, exact decoded scope, MVP/browser
isolation, deep freeze, and deliberate prerequisite/rule/policy/binding/content
drift. This proposal does not execute until its fresh H-DTTLF-02 decision.

## Strong Combined Graduation Example

A suitable end-to-end example uses:

```text
K  : Cat
R  : Catd K
FF : k :^n K ; R[k] ⊢ Cat
k  : Obj K
r  : Obj(R[k])

BΣ  = Sigma_catd_functord_catd(FF)
Sec = Obj(Pi_cat(BΣ))
s   : Sec
```

The TypeScript surface then constructs:

```text
(λ t : Sec,
   piapp0(t, Struct_sigma(k,r)))
s
```

The required pipeline is:

1. the outer LF checks the dependent lambda/application;
2. generic β reduces it to `piapp0(s, Struct_sigma(k,r))`;
3. inner directed-DTT computation identifies the fibre of `BΣ` at `(k,r)`
   with `FF[k][r]`;
4. the result has the expected decoded object type;
5. deterministic Lambdapi emission accepts the same judgment.

The directed extension adds `p : k → k'` and verifies that action along

```text
sigma_transport_arrow(R,p,r)
```

reaches the reviewed `Sigma_catd_transport_func(FF,p,r)` presentation. A
wrong-fibre or wrong-base variant must be rejected by both checkers.

This exercises both required dependent layers and is substantially stronger
than either a bare lambda identity or an isolated categorical projection.

## Human Review Gates

A gate blocks only its dependent promotion or claim. Continue independent
dependency-ready work rather than guessing a mathematical rule.

| Gate | Earliest trigger | Question |
| --- | --- | --- |
| H-DTTLF-01 | LF-1C candidate and corpus complete | Approve the new outer-LF candidate profile, evaluator boundary, transparency policy, and explicitly limited metatheory for integration beyond an experimental API? |
| H-DTTLF-02 | each DIRECTED owner/rule proposal | Is the selected owner signature/rule and its authority class correct for the concrete nested-telescope consumer? |
| H-DTTLF-03 | DIRECTED-GRADUATE-1 complete | Approve the fresh combined owner/rule manifest, product boundary, oracle policy, and any newly justified termination/confluence/subject-reduction claim? |
| H-DTTLF-04 | concrete groupoidal closure consumer | Approve opening the separate Lambdapi-first groupoidal closure plan and its initial consumer/owner inventory? |

Current gate state: H-DTTLF-01 and both the DIRECTED-1A and DIRECTED-1B
instances of H-DTTLF-02 were approved as proposed on 2026-07-24.
The newly discovered
`H-DTTLF-02/DIRECTED-FOUNDATION-1` prerequisite was also approved as proposed
on 2026-07-24. Deeper executable checking then triggered the separate
`H-DTTLF-02/DIRECTED-FOUNDATION-2` instance, which is pending.
`CORE_LF_CONTINUATION_PROFILE_REVIEW` authorizes only the active continuation
checker API; `CORE_DIRECTED_1A_REVIEW` authorizes only the exact
three-signature, zero-rule isolated candidate catalog.
`CORE_DIRECTED_1B_REVIEW` separately authorizes exactly the following reviewed
proposal:

> Approve H-DTTLF-02/DIRECTED-1B as proposed: five exact active owners
> (`τΣ_`, `Struct_sigma`, `Sigma_proj1_func`, `sigma_transport_arrow`, and
> `Sigma_catd_transport_func`), the exact checked transparent body only for
> `Sigma_catd_transport_func`, three catalog-scoped runtime rules
> (`Sigma`-object decoding, first-projection beta, and induced
> telescope-fibre projection), zero proof-time rules, one shared outer-LF
> budget, no default-LF/MVP/browser change, and the recorded general-Sigma-hom,
> transport-unfolding, uncurrying, and groupoidal-closure deferrals?

The user's exact decision evidence is
`Approve H-DTTLF-02/DIRECTED-1B as proposed.` The approval does not change the
browser or deployed MVP, grant a new metatheory claim, pre-approve general
Sigma-hom computation, or pre-approve DIRECTED-1C. H-DTTLF-03 and H-DTTLF-04
remain untriggered.

The exact approved prerequisite question was:

> Approve H-DTTLF-02/DIRECTED-FOUNDATION-1 as proposed: execute exactly the
> three already-active object-level reductions for decoded `Obj(Cat_cat)`,
> `Obj(Catd_cat)`, and `Obj(Functord_cat)` in deterministic order as a
> directed-catalog-local prerequisite before the three approved
> DIRECTED-1B-owned rules and the frozen MVP program, under the same LF
> budget; add zero owners and zero proof-time rules; preserve the stable
> `Catd_cat`/`Functord_cat` category heads, default LF, MVP manifest/runtime,
> browser, arbitrary-user-rule exclusion, approved DIRECTED-1B artifact, and
> all recorded deferrals and withheld metatheory claims?

The user's exact decision evidence is
`Approve H-DTTLF-02/DIRECTED-FOUNDATION-1 as proposed.` It authorizes no
category-head rewrite, owner, proof-time rule, default-LF/MVP/browser change,
arbitrary rule registration, DIRECTED-1C work, or new metatheory claim.

The exact pending follow-up question is:

> Approve H-DTTLF-02/DIRECTED-FOUNDATION-2 as proposed: execute exactly the
> one decoded Cat-hom reduction
> `τ(Hom Cat_cat A B) ↪ τ(Functor A B)` as a
> directed-catalog-local prerequisite after the three approved
> DIRECTED-FOUNDATION-1 rules and before the three approved
> DIRECTED-1B-owned rules and frozen MVP program, under the same LF budget;
> add zero owners and zero proof-time rules; do not rewrite raw `Hom`
> classifiers or `Hom_cat` category heads in TypeScript; and preserve the
> default LF, MVP manifest/runtime, browser, arbitrary-user-rule exclusion,
> every approved proposal/review, all deferrals, and all withheld metatheory
> claims?

Approval would authorize only this exact decoded consequence of the active
`Hom_cat Cat_cat A B ↪ Functor_cat A B` computation. It would not authorize
the broader classifier/category rule, another owner, DIRECTED-1C, product
promotion, or a metatheory claim.

The exact H-DTTLF-01 proposal is to make the current outer-LF modules the
active continuation checker API used by later directed candidate slices while
retaining all of these limits:

- one explicit global budget covers solved-meta zonking, generic β,
  transparent δ, congruence, and the exact previously reviewed semantic
  runtime component;
- declaration bodies are checked only in the strictly preceding persistent
  environment; transparency is explicit, opaque definitions never unfold,
  and assumptions cannot be marked transparent;
- annotated-lambda inference and the scoped builder are enabled only through
  the continuation checker;
- eta, arbitrary user rewrite rules, unrestricted normalization, the browser
  product path, and mutation of the frozen MVP profile remain excluded;
- termination beyond budgeted stopping, confluence, and standalone
  TypeScript subject reduction remain unclaimed.

Approval of H-DTTLF-01 would authorize continuation-layer integration only.
It would not approve a new deployed manifest or browser release; that remains
H-DTTLF-03 work.

`src/v3_2/lf_profile_proposal.ts` freezes this exact review input as
`LF-PROFILE-1`. It records the implemented `zonk → β → δ → reviewed-runtime`
selection order, one 256-step global budget across both comparison sides and
all congruence paths, declaration/transparency policy, annotated-lambda and
constraint-revisit behavior, scoped-builder boundary, exact three-rule MVP
runtime component, browser exclusion, and every withheld claim. Its validator
checks the live comparison limit, frozen MVP revision/hash/runtime program,
and exact proposal content. Eight focused tests pass, including source-order
relocation, deep-freeze, browser isolation, and deliberate boundary,
conversion, declaration, surface, runtime, claim, and content drift.
The two opt-in outer-LF oracle suites also pass together under a 60-second
bound: 15 tests across generic β and combined δ/β/reviewed-runtime
conversion, with both Lambdapi judgments enabled and passing.

The first H-DTTLF-02 decision approved the three-signature, zero-rule
DIRECTED-1A candidate catalog only. The second approved the exact DIRECTED-1B
proposal above; it does not authorize DIRECTED-1C or the graduated product
profile. Neither decision implicitly authorizes the three earlier active
facade computations discovered during executable signature checking;
DIRECTED-FOUNDATION-1 was therefore reviewed and approved through a separate
H-DTTLF-02 instance. Its execution exposed the distinct decoded Cat-hom
dependency now isolated as pending DIRECTED-FOUNDATION-2.

## Experiment Record Template

```text
Experiment ID:
Date and current checkpoint:
Question/hypothesis:
Authority and owner position inspected:
Current worktree/branch and baseline relationship:
Minimal positive consumer:
Relevant negative/non-collapse consumer:
Probe command and bounded result:
Warning/audit/catalog/health effects, if any:
Decision: accept / reject / refine / defer
Plan rows changed:
Remaining prerequisite or human review:
```

Temporary Lambdapi probes belong under ignored `emdash2/tmp/probes/`. Durable
evidence belongs in focused tests, diagnostics, examples, or the relevant
report. Never promote a rule from a temporary probe alone.

## Validation Matrix

| Change | Minimum gate before handoff or an authorized checkpoint |
| --- | --- |
| Plan/docs only | `git diff --check`, relevant link/header checks, `./scripts/pnpmw run check:ts`, bounded `make -C emdash2 check` |
| Root TypeScript behavior | focused tests and `./scripts/pnpmw run check:ts` |
| Generic LF computation | focused structural/capture/budget tests and a bounded Lambdapi differential probe |
| Common Core/Lambdapi owner | owner-position evidence, generated signature probe, positive and negative comparisons, then bounded kernel check |
| Lambdapi declaration/rule | every probe, warning comparison, audit, catalog/health, example, and CI requirement in `emdash2/AGENTS.md` |
| Substantial cross-layer tranche | `EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all` |
| Candidate promotion | fresh manifest/hash, residual-risk review, human gate, and all proportional gates |

Never weaken a gate to make a slice green. Lambdapi commands remain bounded
to at most 60 seconds.

## Recovery And Baseline Record

The initial continuation audit on 2026-07-24 found:

- clean `main` at `30394f9ad7e3834e2786e1b42cc9ec396fcc2c8f`;
- clean dedicated goal worktree
  `/home/user1/emdash1-elaborator-goal` on
  `goal/typescript-elaborator-v3.2` at
  `0b585e955c5a59f87be9daf9024f37e2b3403982`;
- the goal checkpoint is a descendant of current `main`;
- unrelated detached worktrees exist and are outside this objective;
- staged and unstaged diffs were empty before DTTLF-PLAN-0;
- the shared Infinity Codex archive verified from the main worktree with 471
  responses; the goal worktree has no separate ignored archive copy.

Pre-edit bounded baselines:

```text
./scripts/pnpmw run check:ts
  passed workspace contract, typecheck, ESLint, and root tests
  252 tests / 29 suites: 232 passed, 20 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  passed the active kernel, extensions, arithmetic, walking-end,
  equality-action, evidence-property, and check corpus
```

DTTLF-PLAN-0 completion validation:

```text
python3 emdash2/scripts/lint_report_headers.py
  passed; 10 current plans

local relative-Markdown-link audit
  passed; 39 links across the six changed navigation/plan documents

git diff --check
  passed

./scripts/pnpmw run check:ts
  passed workspace contract, typecheck, ESLint, and root tests
  252 tests / 29 suites: 232 passed, 20 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  passed the active kernel, extensions, and check corpus
```

The historical `mvp-1` launch prompt authorized local commits only for its
completed objective. It is not used as implicit checkpoint authority for this
continuation.

## Current Dependency State

DTTLF-PLAN-0, LF-1A through LF-1C, LF-SURFACE-1, and DIRECTED-1A are complete.
The approved DIRECTED-1A signatures compile into an ordered opaque LF
primitive catalog without widening `CORE_OWNER_SCHEMAS`. Generic Core Pi
application checks the first nested telescope; the backend remaps only
registered external references to the audited Lambdapi owners and emits no
shadow declarations. Positive, scoped-builder, wrong-base, wrong-family,
constant-family non-collapse, frozen-catalog/browser/MVP, and deterministic
Lambdapi tests pass.

DIRECTED-FOUNDATION-1 is complete. Its reviewed immutable runtime executes
exactly the three decoded object-level facade reductions through an opt-in
catalog seam, while the default LF, stable category heads, frozen MVP runtime,
and browser graph remain unchanged. Deeper checked construction then exposed
one distinct active dependency at the transported endpoint:
`τ(Hom Cat_cat A B)` must compute to `τ(Functor A B)`. A diagnostic-only
injection of exactly that decoded consequence allowed all eight
DIRECTED-1A/1B declarations and the checked transparent transport body to
validate, with no further signature dependency.

DIRECTED-FOUNDATION-2 is therefore the sole decision-ready active row. Its
machine-readable proposal contains one decoded Cat-hom runtime rule, zero
owners, and zero proof-time rules, and explicitly excludes the broader raw
classifier and category-head computations. DIRECTED-1B retains its approved
five-owner/three-owned-runtime-rule/zero-proof-rule boundary unchanged but is
paused, not rejected or broadened, until the new H-DTTLF-02 instance is
decided. The uncommitted declaration/runtime integration experiment remains
evidence only; DIRECTED-1C is not independently dependency-ready and remains
unapproved.

LF-1B depends on LF-1A's explicit evaluator result/trace contract. LF-1C
depends on the checked declaration-body model from LF-1B. LF-SURFACE-1 depends
on stable beta/delta candidate APIs. The directed tranche depends on the
outer candidate conversion path and one recorded nested-telescope consumer.
The comprehensive groupoidal plan is deliberately deferred and is not on the
critical path.

The LF-SURFACE-1 completion gate passed `check:ts` with 282 tests across
33 suites: 260 passed and 22 opt-in probes were skipped. `git diff --check`
and the full `check:all` gate also passed. The next dependency-ready action,
after H-DTTLF-01 and H-DTTLF-02 decisions, is isolated integration of the
three reviewed DIRECTED-1A signatures and positive/wrong-base/wrong-family
TypeScript tests. No computation rule is part of that action.

Before approved integration, the latest `check:ts` passed with
298 tests across 35 suites: 276 passed and 22 opt-in probes were skipped.
The combined opt-in outer-LF run passed all 15 tests with no skips.

DIRECTED-1A completion validation:

```text
./scripts/pnpmw run check:ts
  passed workspace contract, typecheck, ESLint, and root tests
  313 tests / 37 suites: 290 passed, 23 opt-in probes skipped

EMDASH_RUN_LAMBDAPI_PROBES=1
  focused reviewed DIRECTED-1A suite passed all 9 tests, including the
  generated active-Lambdapi nested-telescope judgment

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  passed the root TypeScript gate, all 19 mandatory TypeScript/Lambdapi
  differential judgments, all 41 Lambdapi kernel/example metric targets,
  39 kernel-script tests, five document-registry tests, source/report/book
  checks, strict inferred-slot audit, and strict generated-catalog check

git diff --check
  passed
```

DIRECTED-1B proposal validation:

```text
EMDASH_TYPECHECK_TIMEOUT=30s scripts/probe.sh
  tmp/probes/typescript_dttlf_directed_1b.lp
  passed the five signatures, pair/object bridge, three computations,
  transparent transport comparison, and three negatives

EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_TYPECHECK_TIMEOUT=30s scripts/probe.sh
  tmp/probes/typescript_dttlf_directed_1b.lp
  passed; only the already-known imported-kernel warnings were reported

./scripts/pnpmw run check:ts
  passed workspace contract, typecheck, ESLint, and root tests
  324 tests / 38 suites: 301 passed, 23 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  passed the active kernel, extensions, and check corpus

python3 emdash2/scripts/lint_report_headers.py
  passed; 10 current plans

git diff --check
  passed
```

DIRECTED-1B approval-record checkpoint validation:

```text
./scripts/pnpmw run check:ts
  passed workspace contract, typecheck, ESLint, and root tests
  330 tests / 39 suites: 307 passed, 23 opt-in probes skipped

git diff --check
  passed
```

DIRECTED-FOUNDATION-1 proposal validation:

```text
node --require ts-node/register --test
  tests/v3_2_directed_foundation_proposal_tests.ts
  passed all 5 proposal/source/boundary tests

EMDASH_TYPECHECK_TIMEOUT=30s scripts/probe.sh
  tmp/probes/typescript_dttlf_directed_foundation_1.lp
  passed three positive object reductions and two stable-head negatives

EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_TYPECHECK_TIMEOUT=30s scripts/probe.sh
  tmp/probes/typescript_dttlf_directed_foundation_1.lp
  passed; only already-known imported-kernel warnings were reported

./scripts/pnpmw run typecheck
./scripts/pnpmw run lint
  passed

./scripts/pnpmw run check:ts
  passed workspace contract, typecheck, ESLint, and root tests
  335 tests / 40 suites: 312 passed, 23 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  passed the active kernel, extensions, and check corpus

git diff --check
  passed
```

DIRECTED-FOUNDATION-1 implementation validation:

```text
node --require ts-node/register --test
  tests/v3_2_directed_foundation_review_tests.ts
  tests/v3_2_directed_foundation_tests.ts
  passed 10 tests across the approval record and exact three-rule runtime

./scripts/pnpmw run typecheck
./scripts/pnpmw run lint
  passed
```

DIRECTED-FOUNDATION-2 proposal validation:

```text
node --require ts-node/register --test
  tests/v3_2_directed_foundation_2_proposal_tests.ts
  passed all 5 prerequisite/rule/policy/source/boundary tests

EMDASH_TYPECHECK_TIMEOUT=30s scripts/probe.sh
  tmp/probes/typescript_dttlf_directed_foundation_2.lp
  passed the decoded Cat-hom conversion, expected-type consumer,
  opposite-ambient near miss, and endpoint-reversal negative

EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_TYPECHECK_TIMEOUT=30s scripts/probe.sh
  tmp/probes/typescript_dttlf_directed_foundation_2.lp
  passed; only already-known imported-kernel warnings were reported

./scripts/pnpmw run check:ts
  passed workspace contract, typecheck, ESLint, and root tests
  350 tests / 43 suites: 327 passed, 23 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  passed the active kernel, extensions, and check corpus

python3 emdash2/scripts/lint_report_headers.py
  passed; 10 current plans

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  passed the root TypeScript gate, all 19 mandatory TypeScript/Lambdapi
  differential judgments, all 41 Lambdapi kernel/example metric targets,
  39 kernel-script tests, five document-registry tests, source/report/book
  checks, strict inferred-slot audit, and strict generated-catalog check

git diff --check
  passed
```

## Persistent `/goal` Launch Prompt

The following prompt is ready to use. It authorizes implementation within the
working tree and bounded temporary local checkpoint commits under the exact
2026-07-24 authorization recorded above. It authorizes no other Git mutation.

Before using it in a fresh session, start from the Git root, review and trust
the root project hook through `/hooks`, and verify the shared archive as
described in `PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`.

```text
Kick off or continue implementing
docs/TYPESCRIPT_ELABORATOR_V3_2_DTT_LF_CONTINUATION_PLAN.md.

Treat its Persistent /goal Launch Prompt as part of the objective. Recover the
actual current state from active code, checks, the plan status and ledgers,
Git worktrees and diffs, then resume the in-progress row or select the next
dependency-ready bounded slice. Read and follow the root AGENTS.md and the
repository authority order. For every emdash2 change, also follow
emdash2/AGENTS.md and the current v3.2 SOP in full. Perform implementation,
not merely another architectural review, and keep the TypeScript
kernel/elaborator, Lambdapi probes and diagnostics, plan, tests, and affected
navigation or authority records synchronized.

Preserve the completed emdash-v3.2-mvp-1 artifacts, comparator, browser entry
point, manifest, hashes, release policy, and historical decisions unchanged.
Build outer λΠ LF computation and later directed-DTT transfers through a new
candidate boundary. Keep the locally nameless explicit Core, use Lambdapi as
the mathematical authority and bounded conformance oracle, and do not promote
a signature, runtime rule, product profile, or metatheory claim without its
recorded evidence and human gate.

The plan is living rather than immutable. Correct, refine, split, reorder,
reject, or defer a slice when owner-position probes or implementation evidence
requires it. Record the concrete evidence, decision change, dependencies,
validation, human-review state, and remaining work in the plan. A need for
human review blocks only its dependent promotion; continue independent safe
work and never guess a categorical or displayed equality.

Use commit 0b585e955c5a59f87be9daf9024f37e2b3403982 as the completed-profile
comparison checkpoint, not as permission to reset a descendant. On every
continuation inspect all worktrees, staged and unstaged changes, current
authorities, and ancestry; preserve unrelated work; relocate symbols with rg;
and run bounded proportional gates. Reuse the existing dedicated clean goal
worktree when available.

The latest local implementation checkpoint is
741668201b8af1a4c3eae9a104fa952b7f2ff9e7. DIRECTED-FOUNDATION-1 is
implemented exactly as approved. The next dependent action is gated by
H-DTTLF-02/DIRECTED-FOUNDATION-2: preserve the DIRECTED-1B integration draft
but do not execute the decoded Cat-hom rule or claim the catalog complete
until the exact one-rule proposal is approved. Independent safe work may
continue without widening that boundary.

This continuation prompt authorizes temporary local checkpoint commits only
on the existing goal branch after a bounded tranche is green, its plan ledger
is synchronized, and the exact staged diff excludes unrelated work. It does
not authorize creating branches or worktrees; amending, rebasing, resetting,
or otherwise rewriting history; pushing, merging to main, publishing,
releasing, or creating a PR; or deleting branches or worktrees. Do not infer
broader authority from persistence or from the completed master plan's
historical launch prompt.

Continue making safe, plan-scoped progress until every plan row is genuinely
complete, rejected with durable evidence, or deferred behind a concrete
recorded prerequisite or human decision. If evidence invalidates a step,
record it and pursue the next independent dependency-ready row. Keep all
Lambdapi probes and checks bounded to at most 60 seconds and follow every
proportional warning, audit, catalog, health, example, and CI requirement.
```

## Change Log

- **2026-07-24 — DTTLF-PLAN-0 opened.** Recorded the corrected three-layer
  architecture, preserved the exact completed MVP boundary, established the
  outer-LF-first implementation order, deferred comprehensive groupoidal
  closure to a separate Lambdapi-first programme, recorded the clean
  worktree/baseline audit, and selected LF-1A as the next dependency-ready
  slice.
- **2026-07-24 — DTTLF-PLAN-0 completed; LF-1A opened.** Routed the handoff,
  root README, completed master plan, nested guidance, and active report
  index to this continuation. Header lint, relative-link audit,
  `git diff --check`, `check:ts`, and bounded `make -C emdash2 check` passed.
- **2026-07-24 — LF-1A completed; LF-1B opened.** Added isolated bounded
  weak-head β with structured traces/stops, capture-safe nested-binder
  substitution, flat and nested spine handling, plicity checks, budget
  behavior, frozen-MVP non-regression, and a passing bounded Lambdapi
  conversion probe.
- **2026-07-24 — LF-1B completed; LF-1C opened.** Added persistent checked
  definitions with conservative transparency, earlier-only dependency
  ordinals, construction-time cycle exclusion, bounded δ traces, and
  failure-atomic self/forward/opaque/ill-typed cases. The released declaration
  and conversion paths remain unchanged.
- **2026-07-24 — LF-1C completed; LF-SURFACE-1 opened.** Added globally
  budgeted zonk/β/δ/reviewed-runtime comparison, opt-in checker/session hooks,
  annotated-lambda application inference, candidate constraint/Miller-pattern
  revisit, definition-aware Lambdapi emission, and passing combined oracle
  parity. H-DTTLF-01 is triggered for promotion; the experimental surface
  slice remains dependency-ready.
- **2026-07-24 — LF-SURFACE-1 completed; DIRECTED-1A opened.** Added a
  one-shot scoped TypeScript builder whose opaque local tokens lower
  immediately to de Bruijn Core, preserve binder plicity and mode, and never
  retain user callbacks. Added dependent `let_` as an annotated-lambda
  application so existing β owns computation, plus alpha, explicit and
  implicit β, dependent-Pi, checked-definition, dependent-let, foreign-token,
  escaped-token, open-embed, arity, and `Type : Type` tests. The full
  TypeScript gate passed with 282 tests across 33 suites (260 passed,
  22 opt-in probes skipped), and `git diff --check` passed. DIRECTED-1A begins
  with active owner-position evidence and a frozen nested-telescope consumer;
  no categorical signature or rule is inferred from the stale TypeScript
  prototype.
- **2026-07-24 — DIRECTED-1A authority proposal completed; H-DTTLF-02
  triggered.** Identified exactly `Functord_cat`, `Sigma_cat`, and
  `Sigma_catd_functord_catd` as the declaration owners required to form the
  first nested telescope. A bounded active-kernel probe passed their exact
  signatures, the representative fibre computation, a typed proof-time
  facade comparison, runtime non-conversion, wrong-base and wrong-family
  rejection, and constant-family non-collapse. Proposed a three-signature,
  zero-rule isolated candidate extension; deferred pair, fibre, projection,
  transport, and action semantics to DIRECTED-1B. The substantial
  `check:all` gate passed.
- **2026-07-24 — DIRECTED-1A proposal made machine-readable.** Added a
  deeply frozen backend-neutral pre-review artifact plus separate active
  Lambdapi binding evidence for exactly the three proposed signatures and
  zero rules. Its validator enforces dependent owner/slot ordering, exact
  arity, active source relocation, backend separation, and the unchanged
  `emdash-v3.2-mvp-1` revision/hash/owner/rule/browser boundary. Eight focused
  tests pass and deliberately reject boundary, owner, signature, rule,
  binding, MVP-identity, and exact-content drift. Catalog integration remains
  gated by H-DTTLF-02.
- **2026-07-24 — H-DTTLF-01 profile made machine-readable.** Added a deeply
  frozen `LF-PROFILE-1` review artifact that pins the implemented transition
  order, one global 256-step budget, acyclic opaque-by-default declaration
  policy, annotated-lambda/constraint-revisit checker boundary, one-shot
  scoped builder, exact reviewed MVP runtime component, browser exclusion,
  and all withheld metatheory/performance claims. Eight focused tests pass
  and reject every relevant profile drift. Continuation-layer integration
  remains gated by H-DTTLF-01. The combined opt-in outer-LF run passed all
  15 generic-β and δ/β/reviewed-runtime tests, including both bounded
  Lambdapi judgments.
- **2026-07-24 — H-DTTLF-01 and H-DTTLF-02 approved as proposed.** Preserved
  both pre-review proposals unchanged and added separate deeply frozen review
  artifacts. H-DTTLF-01 authorizes the bounded LF as the active continuation
  checker API. H-DTTLF-02 authorizes exactly
  `displayed-functor-category`, `sigma-category`, and
  `sigma-telescope-family` in an isolated candidate catalog, with zero
  runtime or proof-time rules. Six focused review tests pass. The user’s
  persistent-goal Git-policy note was applied: all worktrees and ancestry were
  re-audited, the archive verified at 474 responses, pre-integration
  TypeScript/kernel baselines passed, and no commit authority was inferred.
- **2026-07-24 — DTTLF-DIRECTED-1A-E02 opened.** Selected an ordered opaque
  LF primitive catalog as the isolation mechanism. The experiment must
  compile the reviewed dependent signatures, use generic Pi application,
  remap only registered external references in the conformance backend, and
  pass the positive nested telescope plus wrong-base, wrong-family,
  non-collapse, frozen-catalog, browser, and Lambdapi checks. Any need to
  widen the base owner catalog or add a rule rejects the experiment.
- **2026-07-24 — DIRECTED-1A completed; DIRECTED-1B inventory opened.**
  Compiled the three reviewed signatures into persistent opaque outer-LF
  declarations while leaving the frozen base owner catalog untouched. Added
  backend-only registration of external primitive spellings, generic checked
  application and scoped-builder APIs, the positive nested telescope, exact
  wrong-base/wrong-family/non-collapse negatives, browser/MVP/rule-boundary
  checks, and deterministic serialization without shadow declarations. The
  focused opt-in suite passed all nine tests against Lambdapi; `check:ts`
  passed 313 tests across 37 suites (290 passed, 23 skipped), and the full
  cross-layer `check:all` gate passed. Opened
  `DTTLF-DIRECTED-1B-E01` for read-only owner/rule inventory and a fresh
  H-DTTLF-02 proposal; no DIRECTED-1B semantic rule is authorized yet.
- **2026-07-24 — DIRECTED-1B proposal completed; H-DTTLF-02 triggered.**
  Froze the smallest pair/fibre/projection/transport closure as five active
  owners, one exact checked transparent mirror, three catalog-scoped runtime
  rules, and zero proof-time rules. General Sigma-hom normalization,
  `sigma_arrow`, transport unfolding, constant-family totalization,
  projection-pullback/section uncurrying, and groupoidal path closure remain
  explicit consumer-led deferrals. Quiet and warning-enabled active-Lambdapi
  probes passed the signatures, positive computations and transparent action
  comparison, and wrong-base/wrong-family/wrong-endpoint negatives under a
  30-second bound. Added a deeply frozen binder-aware proposal and separate
  owner/rule binding evidence; all 11 focused tests pass. No semantic
  integration is authorized until the exact
  `Approve H-DTTLF-02/DIRECTED-1B as proposed.` decision.
- **2026-07-24 — H-DTTLF-02/DIRECTED-1B approved; local checkpoints
  authorized.** Preserved the exact approval in a separate reviewed artifact
  without rewriting the proposal. It authorizes only the five owners, one
  checked transparent mirror, three catalog-scoped runtime rules, zero
  proof-time rules, shared LF budget, and recorded non-effects/deferrals.
  Opened `DTTLF-DIRECTED-1B-E02` for isolated integration. The same user
  message authorized temporary local checkpoint commits when useful; this
  plan limits that authority to reviewed green tranches on the existing goal
  branch and excludes every remote, integration, history-rewriting, branch,
  worktree, publication, and cleanup mutation.
- **2026-07-24 — reviewed continuation tranche checkpointed.** Recorded local
  checkpoint `94b09ebb64ff3cfca7897c078532bdfeebc5df68` after the complete
  TypeScript gate passed at 330 tests / 39 suites, the plan was synchronized,
  and the exact staged diff contained only the continuation plan, outer LF,
  DIRECTED-1A implementation, and reviewed DIRECTED-1B proposal/decision
  artifacts. This is comparison/backtracking evidence, not permission to
  rewrite or discard descendants.
- **2026-07-24 — DIRECTED-1B integration exposed
  DIRECTED-FOUNDATION-1.** The first checked construction stopped at the
  active `Catd`-to-ordinary-functor object projection required to type
  `fapp0 E x`. A complete dependency trace found exactly two companion
  projections: decoded objects of `Cat_cat` and `Functord_cat`. Froze those
  three existing active runtime rules as a separate zero-owner,
  zero-proof-rule, directed-catalog-local proposal; retained the approved
  DIRECTED-1B artifact unchanged. Quiet and warning-enabled bounded Lambdapi
  probes passed three positives and two stable-category-head negatives, and
  all five proposal tests pass. Paused semantic integration at
  H-DTTLF-02/DIRECTED-FOUNDATION-1 rather than hiding the rules as checker
  coercions.
- **2026-07-24 — DIRECTED-FOUNDATION-1 proposal checkpointed.** Recorded
  local checkpoint `33001f980fcca49928fd28d8bff8f1e45b1c0809` with only the
  synchronized living plan, exact prerequisite proposal/bindings, its five
  tests, and test/index wiring staged. The unapproved runtime seam and
  DIRECTED-1B integration draft remained unstaged experiment evidence.
- **2026-07-24 — H-DTTLF-02/DIRECTED-FOUNDATION-1 approved as proposed.**
  Preserved the exact decision in a separate reviewed artifact without
  rewriting either the foundation proposal or approved DIRECTED-1B review.
  Authorized only the three ordered catalog-local prerequisite rules, zero
  owners, zero proof-time rules, the shared LF budget, and all recorded
  non-effects. Resumed combined foundation/DIRECTED-1B integration.
- **2026-07-24 — DIRECTED-FOUNDATION-1 implemented; follow-up isolated.**
  Added the immutable opt-in three-rule runtime and focused approval/runtime
  tests. The default LF remains unchanged, stable category heads and decoded
  Cat homs remain irreducible, and no browser or frozen-MVP edge was added.
  Deeper checked construction then stopped at the distinct active
  `Hom_cat Cat_cat A B ↪ Functor_cat A B` dependency. A temporary
  diagnostic injection of only its decoded consequence validated all eight
  DIRECTED-1A/1B declarations and the checked transparent transport body,
  finding no further signature prerequisite.
- **2026-07-24 — DIRECTED-FOUNDATION-2 proposed; H-DTTLF-02 triggered.**
  Froze exactly the one decoded
  `τ(Hom Cat_cat A B) ↪ τ(Functor A B)` consequence as a zero-owner,
  zero-proof-rule, directed-catalog-local proposal. Raw `Hom` classifiers,
  `Hom_cat` category heads, approved prerequisite artifacts, the default LF,
  frozen MVP, browser, deferrals, and withheld metatheory claims remain
  unchanged. Quiet and warning-enabled bounded Lambdapi probes and five
  proposal tests pass. DIRECTED-1B integration is paused at this fresh gate.
