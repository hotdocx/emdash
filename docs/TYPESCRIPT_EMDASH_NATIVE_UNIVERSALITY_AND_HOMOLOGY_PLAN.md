# Native Universality And Homology: Living Implementation Plan

Date: 2026-09-12

Plan-ID: TS-EMDASH-NATIVE-UNIVERSALITY-AND-HOMOLOGY

Depends-On: active v3.2 source and the accepted cbef77e7 review

Supersedes: earlier review execution priorities; preserves completed LES evidence and explicit deferrals

Side-Task-Ledger: TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_OWNER_LEDGER.md

Infinity-Codex-Origin: session 2026-09-12_01a096616c4a in /home/user1/emdash1/emdash2/tmp/ai-responses/sessions/

Infinity-Codex-Decision-Responses: 0003_2026-09-12T18-46-28Z_01a096e4-2f5d-7a13-a05a-165935a012d5.md and the 2026-09-12 user acceptance/goal launch

Status: NUH-4C2a checkpoint c38f6c0f; C2b native zero-column comparisons and whole factors checked; canonical Coim⇒Im next; ordinary bridge optional; Op/duality migration deferred

Branch: `goal/native-universality-homology-v3.2`

Worktree: `/home/user1/emdash1-native-universality-v1`

Comparison-baseline: `cbef77e76fc292453c8814b5ecc6d62e84132f01` (never reset to it)

## Objective And Current User Direction

Deferred terminality refinement (2026-09-13): the user accepts the current
ordinary-target normalizers for now and proposes later upgrading the
original terminal/initial interface to general categorical universality.
The categorical subplan records the distinction between contraction of a
whole Hom category and its object/core groupoid, the role of univalence,
and the proposed native whole-Hom/adjunction presentation. OneCat remains
a current qualification guard; this later refinement does not block C2c
or reopen the deferred strictness/duality migration.

Latest connecting/exactness direction (2026-09-13): use whole categorical
universality directly for the primary construction. Do not first convert
K/Q to ordinary factor/IsContr dictionaries to run the old point program.
The checked ordinary category-view prototype is retained only as optional
compatibility evidence. The
[categorical exactness and connecting subplan](TYPESCRIPT_EMDASH_CATEGORICAL_EXACTNESS_AND_CONNECTING_PLAN.md)
now owns NUH-4C: whole Coim/Im, their canonical comparison and Abelian
invertibility, canonical image-to-kernel exactness comparisons, and whole
universal descent for δ. Existing ordinary proofs remain reference consumers.

Consolidated reconstruction review (2026-09-13): the user's latest direction
allows retaining r_C:D_C∘E_C≅id for now, provided the implementation remains
computational and internal and does not require manually carried naturality
or functoriality squares. Retain the current OneCat-restricted whole DefIso
instance under this criterion. Its to/from transformations, inverse cuts,
components and further action use existing generic owners. The four new
endpoint rules compute identity components; there is no new per-map
naturality premise or construction-specific naturality rule. This remains
an explicit shape-universality primitive, not a theorem from the current
Join β rules or a proof of a general normalization result.

The ordinary faithfulness and record lemmas contain internal equality
proofs, including an application of the generic strict-component naturality
theorem. These are derived ordinary observations, not coherence parameters
to the homology program or primary definitions of K/Q/H. Keep that profile
qualification explicit; do not advertise the generic helper as a theorem
about arbitrary lax comparisons. The source/signature audit confirms that
the independent whole K/Q, mates and H sources do not import this record
proof route. The scoped review therefore creates no replacement-owner
prerequisite for NUH-4. C4 is checkpointed at `1ea98f63`; continue with NUH-4A.
The user's continuation explicitly keeps this design revisitable. If a
consumer turns naturality/functoriality squares or their equality proofs
into manually maintained primary data, revisit the construction and its
generic owner; a green checkpoint does not waive this requirement.

NativeArr(C) was only prose for the existing LaxArrow_cat C. E_C and D_C
are existing functor definitions. The inverse projected from the present
DefIso is r_C⁻¹, not D_C as an inverse of E_C. Only faithfulness of E_C is
used here, and the one-sided comparison suffices in the ordinary scope.
The earlier proposal to require a full fixed-forward E/D equivalence was
premature and is withdrawn as a current gate. If such a comparison is later
needed, reuse existing inverse machinery at its actual strength. Matching
lax transformation profiles can support the usual interval/arrow
classification, whereas strict diagram maps and genuinely lax squares
cannot be interchanged. Merely weakening the naturality equation does not
establish inverse laws. This clarification does not reopen the deferred
Op/profile migration or authorize a general higher equivalence declaration.

Implement the accepted native universality/homology redesign on the current
kernel baseline, making whole categorical universality primary in formal homology and
connecting its actual operations to a usable retained-result proof-CAS path.
The persistent goal delegates evolving implementation details, experiments,
validation and next actions to this living plan and its linked design ledger.

**Latest user reorganization, 2026-09-13:** defer the Op/duality migration
until after this goal because it may interact with strict/lax structure.
Preserve its checkpoints and partial experiments for later integration, and
start NUH-3 now. NUH-1/2 are no longer prerequisites or completion gates for
the remaining universality/homology work. This direction supersedes the
earlier execution priorities below. No deferred patch is installed in the
active nucleus. The retained work and resumption instructions are in
[the deferred experiment](../emdash2/audits/deferred_native_homd_y/README.md).
The persistent objective delegates its evolving scope here; its older
coupled-repair wording is superseded by this explicit user reorganization.

The user accepted the consolidated response archived as
`0003_2026-09-12T18-46-28Z_01a096e4-2f5d-7a13-a05a-165935a012d5.md`
in the original worktree's
`emdash2/tmp/ai-responses/sessions/2026-09-12_01a096616c4a/responses/`.
The current launch additionally authorizes a new branch/worktree, proceeding
with the plan, and starting a corresponding persistent goal. Earlier local
checkpoint authorization carries into this dedicated worktree.

**Subsequent user direction, 2026-09-12:** focus on a usual mathematical,
semantically coherent theory of Op/duality and its useful native operations.
Set handcrafted Empty proofs and this branch's prototype global strictness
rules aside. The migration in `goal/opaque-action-profile-classifiers-v3.2`
will be integrated **after this goal**, not during it and not as a
prerequisite for finishing it. Preserve existing diagnostics as historical
evidence; do not continue their investigation or use them to redirect the
current implementation queue.

**Further architectural clarification:** the implementation must remain
syntactic, computational and internal. Use the selected Op_cat,
CoAbove2_cat and required supporting native heads, their internal functors
and fapp/tapp/Hom computation. The general D_S/set-of-dimensions exposition
was semantic background, not an implemented or selected type-theoretic
API. Its arbitrary tensor/profile transport is not an implementation plan.
The internal design is not complete until its actual whole owners and
projection/action ladders are implemented.

The shared-index construction is a candidate replacement for the target
classifier of homd_int, bundling its existing y,v,a arguments. It is not a
replacement for native dependent Hom. Its necessity and scope must be
made explicit through the direct old/new owner comparison. General
functoriality in a family map G:D→D′ is auxiliary work and is parked until
an actual native action consumer needs it. Do not expand that interface
ahead of the direct homd_int adjustment.

The user subsequently confirmed that Op_catd is intended as **pointwise
opposite**, and must remain primitive. The briefly considered opposite of
the total projection is a distinct operation, owned by Op_func on that
projection. Do not substitute that interpretation for Op_catd. The
pointwise proposal under total Op has base CoAbove2_cat(K), with fibre
Op_cat(E[x]); its composite fold is not a primitive-to-defined migration.
Preserve existing native primitive heads. A semantic comparison or
constructor fold must not be described or implemented as replacing such
a primitive by a transparent definition.

For this Op migration, preserve the existing rewrite/unification
architecture by default: primitive and stable heads, runtime normal forms,
rewrite-versus-unification roles and owner placement. Adapt necessary
variance arguments and inferred-slot patterns in the existing rules first.
An additional comparison or relocation needs a concrete core consumer and
an explanation of why the existing architecture is insufficient. Auxiliary
prototype convenience or availability in a truncated prefix is not itself
a reason to change the final source organization.

**Spectra, categorical spectra, Heine generalization, dependent stabilization
and suspension research are explicitly deferred by the launch. Do not
investigate them further in this goal.** The one-fixed-endpoint brainstorm is
retained as historical context only. It creates no implementation row or
prerequisite, and no further literature review is scheduled for it.

The [accepted semantic review](TYPESCRIPT_EMDASH_HOMOLOGY_SEMANTIC_ARCHITECTURE_REVIEW.md)
supplies the architectural decisions. This plan controls execution and
supersedes its open-ended research recommendations. The
[retrospective](TYPESCRIPT_EMDASH_HOMOLOGY_RETROSPECTIVE_REVIEW.md),
[completed LES plan](TYPESCRIPT_EMDASH_BOUNDED_LONG_EXACT_HOMOLOGY_AND_BOOK_PLAN.md),
[internalization pilot](TYPESCRIPT_EMDASH_STRICT_INTERNAL_HOMOLOGY_PILOT_PLAN.md)
and [variance repair evidence](TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_REPAIR_PLAN.md)
are recovery and design evidence, not queues to resume indiscriminately.

## Fixed Architectural Decisions

1. `hom_int` and `homd_int` retain foundational syntactic ownership and their
   internalized projection/action ladders. Total-Hom projections, native
   simplicial/cubical views and other applications must be derived from or
   explicitly related to those owners. Do not replace them with an external
   relative-Hom definition or second calculus.
2. Whole K/Q, their adjunctions, units/counits and whole mate functors own
   formal universality and computation. Native H remains the whole composite
   β=K(h)∘η and H=Q∘Arr(β). Generic fapp/tapp and adjunction cuts own action,
   naturality and composition.
3. The older selected W/V families and factor/IsContr records are realization,
   verification or derived-view interfaces. Refactoring must actually remove
   their role as prerequisites driving every formal operation, rather than
   hide old selections inside mate/unmate wrappers.
4. Complex/diagram input formation must not select a kernel solely to become
   an input. Use native homd/diagram structure and its retained differential
   and zero data; then apply the universal operation.
5. Retain original native selections and computational witnesses when
   interpreting an existing result. Across different choices, use justified
   isomorphisms/equivalences or a proved stronger representation contract.
   Isomorphic raw presentations need not be equal records.
6. Equality is permitted as mathematical evidence and a derived observation.
   Do not make manual pointwise cone manipulation the primary formal program,
   erase all witness data, postulate exactness, or add object casts to conceal
   a wrong endpoint or variance.
7. Specify the globally compatible variance and transformation profiles of
   the affected owners before editing them. The preferred repair meaning is
   total Op plus the shifted homwise dual, preserving ordinary transposition
   as a derived view where required. No unrestricted same-base opposite-family
   operator or base regrading may restore the known bad reversal.
8. The ordinary Freyd target's existing local profile is a specialization,
   not a truncation of the generic directed foundations. Retained higher
   action and negative/noncollapse controls remain required.

## Scope And Deferrals

In scope: whole universality dependency refactor; native whole H and connecting/window
consumers; a scoped whole-H snake/direct/native comparison; reusable
model/reifier setup for the already supported polynomial/Freyd backend;
necessary public/private TypeScript transfer and conformance; owning
documentation, provenance and checks.

The original final symbolic endpoint-wrapper theorem remains explicitly
deferred. Do not restart private-checker patches, endpoint debug sessions,
blind record variants, or resource-limit experiments. If the new primary
interface naturally makes a required boundary comparison available, record
that specific evidence; it does not license a separate checker investigation.
Keep the working field-indexed iterator and native bounded sequence as
reference consumers throughout.

Also deferred until after this goal: the coupled op/family/Sigma/native-Hom
variance migration, with all completed and partial work retained;
prototype global strictness-rule migration and further
Empty/inconsistency audits; integration of
`goal/opaque-action-profile-classifiers-v3.2` until after this goal;
unbounded/derived-category implementation, Ext construction,
spectral algebraic geometry, general homological normalization or Adelman
theorem-proving, a new frontend/parser, unrelated strictness/profile branch
integration, and exhaustive preservation of obsolete wrappers. These are not
reasons to broaden the first homology implementation slice.

No push, merge to main, PR, publication, book/PDF promotion, release, history
rewrite, branch deletion or worktree removal is authorized by this goal.
Use ordinary correcting commits on this dedicated branch. No parallel
agents are scheduled; task delegation requires separate applicable authority.

## Authority And Recovery

Follow root `AGENTS.md`, `emdash2/AGENTS.md`, the current-status report,
Foundations, canonical syntax and report registry in their documented order.
Read the TypeScript handoff and governing transfer boundary before changing
TypeScript. Apply print/book SOP only if its owners become affected.

On continuation inspect worktrees, current branch/HEAD, baseline ancestry,
staged/unstaged/untracked state, current sources and this ledger. Use
`docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`. Work in the dedicated path
above even if the tool's default cwd remains `/home/user1/emdash1`.

The original session archive remains in `/home/user1/emdash1/emdash2/tmp/`;
it is ignored and is not copied into the new checkout. Archive responses
recover decisions but never override current user direction or active code.
The same root hook configuration is retained; no new hook is installed.

## Implementation Ledger

| Row | State | Required outcome |
| --- | --- | --- |
| NUH-0 | complete in this launch checkpoint | Dedicated bootstrapped worktree, accepted directions registered, persistent goal started and scoped launch checks passed |
| NUH-1 | user-deferred after this goal | Preserve the reviewed native duality design and checkpoints; resume only under the later strict/lax review |
| NUH-2 | user-deferred after this goal | Preserve the coupled migration prototypes and their open qualification boundaries; no active-kernel promotion now |
| NUH-3 | complete at the stated ordinary-view boundary; checkpoint 1ea98f63 | Whole K/Q universality independent of old W/V prerequisites, with computing whole/point mates and derived ordinary records; retain the explicit shape-law and profile qualifications |
| NUH-4 | active: direct inputs/maps through Freyd checked; categorical exactness/connecting owners next | Native complex input independent of kernel selection; whole H, induced maps, connecting and exactness consumers at their actual endpoints |
| NUH-5 | pending NUH-3/4 | Registered supported model/reifier preparation; retained nonsplit end-to-end consumer with explicit, accurately classified contracts |
| NUH-6 | pending NUH-4 | Whole-H snake/direct/native connecting comparison with fixed sign and original endpoint comparisons; preserve general six-term scope |
| NUH-7 | pending NUH-3–6 | Cross-layer qualification, standing-source documentation, trust/computation audit and green local integration checkpoint; retain the separate Op resumption record |

Preserved duality progress (2026-09-13): NUH-1D4 corrected the defined
HomPresheaf fibre and its two argument actions. NUH-1D5 now retains a
direct native-owner candidate with target CoAbove2(Functor(S_D(x),Cat)).
This preserves the original primitive homd_int declaration, Op_catd source
and Op_funcd composition; the x/u projections, fixed-y,v whole restriction
to homd_ and first displayed-Hom source-component fold check. The full
candidate reaches the old homd_id_tgt_func y-only evaluation. Whole-v
projection and the expanded Hom-action comparison remain pending. The
active nucleus is unchanged. The later NUH-1D6 experiment is now parked,
including its failed final fold. See the
[owner ledger](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_OWNER_LEDGER.md).

NUH-3A now implements whole K/Q structures introduced directly from whole
functors and adjunction evidence, independent of W/V. Their structural maps
and mates compute through existing native owners; old selected presentations
adapt into the new interface and reuse its structural maps. The new reviewer
and both selected-presentation regressions pass. NUH-3B now moves the whole
H-family implementation and its native zero-arrow-cone application to these
independent structures. The legacy names delegate through the presentation
adapters, preserving the whole functors and selected views. The global native
application retains its explicit OneCat profile. Focused action, whole
comparison and legacy checks pass with unchanged warning inventories.

NUH-3C1 now constructs native inputs directly from b,d,d∘b=0, and supplies
the initial dual, using the existing whole native square action with explicit
OneCat. The resulting input enters whole H before any kernel selection.

NUH-3C2 now derives k∘lift(h)=h₀ and colift(h)∘q=h₁ by whole mate
cancellation, and both structural zero equations from the unit/counit.
Independent diagram observations no longer import selected universal owners;
the old proof bodies delegate through the presentation adapters.

NUH-3C3 now has the whole native observation E_C:Arr(C)→LaxArrow(C), derived
from the existing graph of the evaluation transformation. Its arbitrary-map
components and next Hom action check. The ordinary return functor D_C is
already present; the constructor-visible E_C(D_C(edge)) round trip checks.
The second gate now adds the missing ordinary shape-universality law
explicitly: a whole natural DefIso D_C∘E_C ≅ id in End(Arr(C)), with four
computing endpoint projections. This is one new declaration-backed primitive,
not a derivation from the older join β rules. Faithfulness of E_C is derived
from that natural comparison and the existing inverse/naturality machinery.
Actual comparison maps also let raw zero tests enter the original arbitrary
diagram d, preserving their supplied arrows and future K(d)/Q(d) endpoints.

NUH-3C4 now derives native-square equality at OneCat, cancellation of both
whole structural maps, and complete ordinary kernel/cokernel records without
W/V inputs. Their centres compute to the actual mates, and their lift/colift
operations agree propositionally with the retained presentation records.
Focused reviewers and dependency/warning audits pass. No primitive or rule
was added in NUH-3C4. Whole K/Q existence and concrete model semantics remain
supplied; NUH-3 completion is not completion of the whole goal.

NUH-4A1 now supplies the independent homology-family record, preserving the
actual β=K(h)∘η factor and Q observation on its whole introduced boundary
diagram. Its cycle, boundary, H and quotient projections compute; the
original H arrow and whole Hom actions check at those record endpoints.
Legacy boundary names delegate through the structure adapter with unchanged
signatures, and the shared chain-pair observation is moved unchanged.

NUH-4A2 now forms native inputs from the original chain-pair fields before
any kernel selection and constructs HomologyRecord over that same raw pair.
The factor is the existing semantic boundary observation at the constructed
input. Original vertices/differentials, actual β/H, boundary reconstruction
and H action at two such record endpoints check. No record cast, new path
proof, primitive or rule is introduced in this tranche.

NUH-4A3 now specializes direct input formation and the new record to raw
Freyd agreements, filling the existing local categorical data. Input
formation takes no kernel presentation; H and its record use explicit whole
P/Q. The original raw classes, agreement observation and actual H endpoint
check. Existing selected wrappers and their warning inventory are preserved.

NUH-4B1/2 now constructs native maps between the direct inputs from the
original chain-map data before kernel selection. Its private comparison
uses the existing ordinary diagram comparison and keeps the represented
postcomposition endpoint required by the native Hom. Whole PathLift action
then composes with H's existing whole Hom action. Original components,
actual H/record endpoints and next Hom actions check; no new caller
coherence premise, primitive, rewrite or unifier is introduced.

NUH-4B3 now specializes these maps to the original raw Freyd map data.
The original component classes, whole action in the raw-agreement parameter,
actual H application and original record endpoints check. Existing raw
conversion and selected-map definitions remain unchanged.

NUH-4C1 follows the direct categorical subplan. The
[whole image/coimage owner](../emdash2/emdash3_2_image_coimage_adjunction_families.lp)
now defines Arr(κ), Arr(q), Coim=Q∘Arr(κ), Im=K∘Arr(q), and their structural
projection/inclusion. Six transparent definitions add no primitive, rule,
unifier or ordinary factor dictionary. Sixteen focused reviewer assertions
cover the original structural transformations, nonidentity diagram-map
components, whole Hom action, structural components, next Hom action and
noncollapse of independent selections.

NUH-4C2a now supplies [ordinary-target whole diagram transposition](../emdash2/emdash3_2_one_cat_diagram_transpose.lp)
and [the original K/Q unit/counit instances](../emdash2/emdash3_2_one_cat_kernel_cokernel_transposes.lp).
The family remains one internal functor, with columns and shape-arrow
actions as its observations. Whole evaluation through precomposition now
computes before or after Hom projection; three narrow proof-time comparisons
retain the existing evaluation and arrow-introduction owners. No new
primitive or caller square-proof input is introduced.

NUH-4C2b now adds two explicit native terminal/initial family-universality
primitives in the ordinary target, with identity endpoint computations and
existing DefIso inverse cuts. This is a recorded extension of the old
pointwise-uniqueness interface, not a derived β theorem. Their instances
at the actual ZP/ZQ columns supply whole mate inputs. The defined whole
cokernel and kernel mates then give Coim⇒ev₁ and ev₀⇒Im. Native mate
reconstruction proves their original-arrow factor equations as reviewer
observations; no ordinary dictionaries enter the primary programs.

Next NUH-4C2c constructs canonical Coim⇒Im and its coherent whole
factorization data; the two factors alone do not supply it. Then express
Abelian normality and exactness by invertibility of the actual comparison
maps, and build δ by whole universal descent. The ordinary all-arrow/category
bridge is optional compatibility work, not a primary prerequisite. Do not
infer normality from K/Q existence or postulate LES exactness. Concrete
whole models, reifier automation and snake comparison remain later.

Split these rows into bounded subrows when concrete owners and hypotheses are
known. Keep one current semantic experiment at a time. A failed candidate is
evidence to revise the design, not permission to skip an essential outcome.
Record missing prerequisites precisely and distinguish experiment rejection
from a genuinely blocked goal.

## NUH-1: Deferred Design And Resumption Evidence

This section records the parked design obligations. It is not the active
work queue and does not delay NUH-3–7 under the latest user direction.

The current native design is
[Native Duality: Syntactic Owners And Internal Computation](TYPESCRIPT_EMDASH_DUALITY_SEMANTIC_THEORY.md).
It distinguishes the unchanged active nucleus from the finite native
operator prototypes and gives their actual types and computation owners.
The earlier general external exposition does not complete the internal
design and is not the architecture being implemented. Complete the native
Homd target/module and its projection ladder using the selected owners.

Keep the artifact roles explicit:

| Artifact | Role |
| --- | --- |
| Active emdash3_2.lp and registered extension modules | The current implemented theory |
| Isolated owner-position patches and prototype files | Candidate source changes; not active library functionality |
| Reviewer/control files and typed asserts | Checks of computation, typing and proof-time unification; not primary mathematical constructions |
| Ignored tmp/probes and retained /tmp stages | Disposable experiments and their logs; not additional authorities or an implementation queue |
| Linked historical diagnostics and session archives | Recovery evidence only; current plan/user direction selects what remains in scope |

In particular, `assert ⊢ eq_refl(...) : τ(@= ...)` is the SOP's way to
exercise a unification comparison. It does not construct a family by an
equality cast. Prefer that explicit test spelling over a named `_agrees`
symbol in a temporary reviewer when the symbol has no actual consumer.

The design ledger is
[native owner and variance ledger](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_OWNER_LEDGER.md).
It must cover at least:

- Op/shifted dual/transposition, functors and the internal universe action;
- displayed families/maps/transformations, negative sections and their bases;
- mixed Hom/functor-family constructors and the presheaf/section target;
- `hom_int`, `homd_int`, the whole projection ladders and retained higher action;
- Sigma Hom, constant-family products and both whole projections;
- whole adjunction/mate owners versus selected K/Q records;
- native chain input, whole H and direct connecting dependencies; and
- the retained native-model and reification boundary.

For each owner identify current defining source, intended mathematical type,
runtime/proof-time ownership, the proposed change or preservation decision,
and a discriminating positive and negative consumer. Dimensions and
strict/lax profiles must agree throughout a connected construction. A
collection of independently typable object observations is insufficient.

Reuse the exact preserved variance experiments after auditing current-source
drift. A prefix is useful isolation evidence but not a full-kernel repair.
Do not run an old driver that bypasses the current resource guard. Do not
reset a worktree or accept an old patched binary to recover its result.

The first target review exposed both the native section-polarity defect and
the shifted-base mismatch. NUH-1B2c's strict finite coefficient models
constrain the old unrestricted y-local target. The shared native index/module
remains a possible replacement, not a selected minimal repair. The current
NUH-1D continuation first corrects the existing presheaf pipeline and reviews
the surrounding native target directly, preserving the original supplied
families and homd constructor. An arbitrary R(Z)=Z equation or new
replacement-family input still rejects a candidate. Prototyped shifted-dual
actions need their actual whole action; object formulas alone do not qualify
them. Prototype strictness migration remains deferred.

Historical NUH-1B1 records a polarity constraint: the old positive section over
the opposite target base produces a reverse Hom action and a closed Empty
witness, including a walking-arrow specialization. The
[polarity diagnostic](TYPESCRIPT_EMDASH_HOMD_TARGET_POLARITY_DIAGNOSTIC.md)
is retained as diagnostic evidence. Under the subsequent user direction,
its Empty route is not an active acceptance gate. The functional constraint
still matters: the native target must have its intended mathematical
section direction as well as its correct base. No further independence
investigation is scheduled.

Historical NUH-1B2g reproduces a separate family/section profile conflict:
unrestricted strict naturality plus the constant-section interface derives
F(x)=F(y) along every base arrow and hence Empty. Earlier routes persist
before Sigma/native-Homd, without the late theorem or its two whole
comparison unifiers.
The [profile diagnostic](TYPESCRIPT_EMDASH_FAMILY_SECTION_PROFILE_DIAGNOSTIC.md)
records the exact isolation and its limits. The user has subsequently
deferred that investigation and the associated NUH-1B2h migration. It is
historical prototype evidence, not a prerequisite for the current
mathematical duality/native-operation continuation. The mathematical
contexts remain explicit; no source comment is used as a new theorem.

## Universal Structure And First Vertical Consumer

The proposed primary K/Q structure has the existing ordinary interpretation
J(X)=(X→0), J⊣K and I(X)=(0→X), Q⊣I. Its whole arrows live in the native
diagram/Hom classifiers and its observations compute through existing
generic machinery. New stable heads are allowed only for a measured owner
need, not to duplicate semantic bodies or hide a failed comparison.

The first vertical consumer must exercise a genuine nonidentity diagram map,
whole/point mate cancellation and a nonzero retained homology/connecting
calculation. Derive the old ordinary factor view from the whole universal
comparison at the stated profile. Avoid new pointwise callback APIs as the
formal foundation. Preserve selected-algorithm witnesses at the realization
boundary and reject changed selections or missing premises.

The model/reifier work should remove repeated end-user construction of
formal coefficient names, environments, model references and observation
inventories. It must not silently relabel supplied model semantics as a
derived correctness theorem. A reusable supported backend may carry an
explicit trusted contract while certified universal-provider construction
has its own recorded obligation. A certificate of d∘G=0 alone does not
establish that G generates the entire kernel.

The completion audit must state exactly which global and per-selection
contracts are constructed, supplied or trusted. No claim for arbitrary
coefficient rings follows from the effective polynomial instance.

## Validation And Promotion

**User direction, 2026-09-12:** avoid long-running repository-wide
typechecks for this goal. Localize checks to affected aspects, features
and files wherever possible. This goal-specific direction supersedes
blanket aggregate requirements in the earlier plan/SOP workflow. Reuse
recent evidence for unchanged dependencies. Broaden only for a concrete
affected dependency or unresolved concern, with the reason and bounded
scope recorded; no automatic repository-wide gate is scheduled.

All Lambdapi experiments use `emdash2/scripts/lambdapi_resource_guard.sh`:
one checker at a time, at most 90 seconds, 2 GiB per-process address space,
64 MiB per file, no core dumps; use the existing aggregate memory scope
when available. Do not raise limits or bypass ordinary subject reduction.

Do not rerun or expand the Empty reproducers or pursue global strictness
migration as an acceptance gate for this goal. Use the affected operation's
mathematical type, whole action and ordinary nonidentity/higher-cell
consumers. Integration of the other profile branch belongs after this goal.

Documentation/design-only checkpoints need exact diff and link/Markdown,
active-reference and report-lifecycle hygiene, not repository aggregates.
Bootstrap with `./scripts/bootstrap-worktree.sh` and the pinned pnpm.

Before semantic edits, select the bounded active-kernel baseline and nearest
positive/negative consumers. Put rule changes at the intended position in a
full-source copy, compare warning families, audit inferred LHS slots and
confirm whole higher action. Negative fixtures must fail at the intended
type mismatch: syntax errors, missing imports and timeouts are not repairs.
For promoted LP changes, select the affected owner files and nearest
positive/negative and higher-action consumers. Preserve owning-position
SR/warning/LHS checks and affected catalog/health synchronization, without
automatically running all examples or full CI. A bounded check of an
affected monolithic kernel owner is a local owner check, not a reason to
expand to the repository aggregate. Record exactly what ran and its limits.

For TypeScript changes use affected typecheck/lint, focused tests and the
relevant conformance consumers. Workspace checks apply to changed workspace
configuration. Shared-boundary changes require an explicit affected-feature
selection rather than automatic check:ts/check:all. Preserve the explicit
Core/checker boundary; source-only metrics are not runtime validation.

Checkpoint only a coherent green tranche after synchronizing the ledger,
reviewing exact staged paths and `git diff --cached --check`. Research
snapshots may preserve unpromoted alternatives with their statuses, but
must not label those alternatives validated implementations.

## Decisions And Side Tasks

| ID | Decision |
| --- | --- |
| D-NUH-001 | Execute in the new dedicated worktree from cbef77e7; main and sibling worktrees are reference states |
| D-NUH-002 | Accepted native Hom ownership and whole-universality decisions govern; earlier total-Hom-first proposals stay withdrawn |
| D-NUH-003 | Spectra/Heine/dependent stabilization and beyond are brainstorming-only and receive no further investigation in this goal |
| D-NUH-004 | The coupled variance repair resumes under this new goal after the design audit; historical deferral during the finished LES goal is not a current veto |
| D-NUH-005 | Endpoint checker/debugging remains deferred; do not conflate it with the native universality refactor |
| D-NUH-006 | The mixed-functor dimension-2 action constrains its negative source variance; replacing transposition by total duality solely to fit the old E input is not a semantic repair |
| D-NUH-007 | The archived patch is zero-context and passes a matching dry-run check on the new anchor; its mechanical applicability does not qualify the 328 later added source lines or the full native Homd target |
| D-NUH-008 | The native-target positive-section polarity admits a reverse Hom functor and Empty; correct section direction together with base variance and add this route to the repair's negative controls |
| D-NUH-009 | Negative sections act through actual maps between the dual families; do not infer unrestricted covariance on old lax Catd(K) by inverting its comparison cells |
| D-NUH-010 | The full-source old-variance polarity isolation qualifies a native terminal/constant beta and direction constraint only; combine it with the preferred shifted bases and arbitrary-family profiles before proposing the final target |
| D-NUH-011 | Strict finite coefficient models refute either base-2-cell orientation of the old unrestricted y-local target; pursue the native shared triangular index/module target with original D/E inputs, preserving homd_int ownership and noncircular dependencies |
| D-NUH-012 | For the ordinary unshifted Hom target, source contravariance in u uses T and its family base is D₂(Z). D-NUH-025 uses the simultaneously homwise-dual presentation to retain the original O source over R(Z); these are distinct whole target presentations |
| D-NUH-013 | The shared-index carrier and first projection can use the corrected pre-homd_int Sigma substrate. Qualify whole x/D actions separately; do not conflate that independent carrier with the later Sigma map action's native-laxity dependency |
| D-NUH-014 | The strict-reference whole x-family computes its source-point and H-precomposition views through native Hom owners; its remaining index-arrow computation is the specific Sigma map of opposite represented precomposition. Derive that structural action without assuming inverse laxity or claiming generic-profile qualification |
| D-NUH-015 | Selected structural index action now computes complete stable/raw arrows and source-2-cell components before homd_int; classifier/profile and affected full-source qualification remain separate |
| D-NUH-016 | Follow the user's localized-validation policy for this goal: affected owners/features/files, recent unchanged evidence, and no automatic long-running repository-wide typecheck or aggregate |
| D-NUH-017 | Constant-section comparisons plus unrestricted strict naturality derive Empty; retain generic directed section action and qualify strict equality at an actual profile. Audit whole/capped/object/stable comparisons together; the four-cut diagnostic subtraction is not a repair |
| D-NUH-018 | Subsequent user direction sets Empty audits and prototype global strictness migration aside. D-NUH-017 is historical evidence, not the current work queue. Integrate goal/opaque-action-profile-classifiers-v3.2 only after this goal |
| D-NUH-019 | Use the dimension-set duality calculus, shifted universe/family actions and transported enrichment in TYPESCRIPT_EMDASH_DUALITY_SEMANTIC_THEORY.md as the coherent mathematical reference; continue native target/module construction and then the universality/homology migration |
| D-NUH-020 | User clarification supersedes D-NUH-019's architectural wording: no generic D_S API or external tensor/profile transport is being implemented. Use selected native duality heads and their internal functors/projections; the full internal design remains unfinished |
| D-NUH-021 | Prioritize the direct homd_int source/target and projection adjustment. The shared index is a target-packaging candidate; G:D→D′ module functoriality is auxiliary and parked. Mark typed equality probes as tests, not theory constructions |
| D-NUH-022 | User confirms primitive pointwise Op_catd, distinct from Op_func on a classifying functor or total projection. CoAbove2_func(E) keeps object value E[x], so the internal op composite has fibre Op_cat(E[x]), not a fibre transpose; preserve the primitive head |
| D-NUH-023 | Preserve the existing rewrite/unif architecture during the Op migration. Adapt variance within existing owners first; additions or relocations require an actual core consumer, not auxiliary-prototype or prefix-check convenience |
| D-NUH-024 | Retain the definition-only HomPresheaf correction: its fibre agrees with native homd_ and both argument actions compute through existing Hom owners. No rule is added or moved; higher-component qualification and the original-D target slot remain pending |
| D-NUH-025 | The direct Homd candidate uses the homwise-dual shared-index value category, preserving the original primitive homd_int, Op_catd source and Op_funcd composition. Fixed-y,v restriction and first source/action projections check; whole-v projection and the expanded Hom-order join remain open |
| D-NUH-026 | User defers Op/duality migration until after this goal. Preserve all checkpoints and the unfinished NUH-1D6 stage; remove NUH-1/2 from current prerequisites and completion gates; start NUH-3 on the unchanged active nucleus |
| D-NUH-027 | Whole K/Q structures and their mates now take native functors and adjunction evidence without W/V. The single whole H-family implementation takes these structures; legacy presentations delegate through one-way adapters. Ordinary records and raw input conversion must remove their remaining selected dependencies separately |
| D-NUH-028 | Raw zero-composite data now enters native zero-arrow cones via the existing whole square action, with explicit OneCat and canonical introduced diagram endpoints. Keep this as an input adapter; derive ordinary universality from the adjunction, without assuming arbitrary diagram eta or introducing factor dictionaries |
| D-NUH-029 | Reconstruction and structural annihilation now derive from whole mate cancellation and the unit/counit, independently of W/V. Full ordinary uniqueness still needs the native walking-arrow representation/faithfulness comparison; do not infer equality of arbitrary transformations from component observations alone |
| D-NUH-030 | Supply the missing ordinary walking-arrow shape-universality assembly explicitly as a whole natural DefIso D_C∘E_C ≅ id in End(Arr(C)), with OneCat and computing identity endpoint components. This is a new primitive law, not a theorem derived from existing join β rules or a judgmental equality of inverse functors. Derive map reflection from its whole inverse and naturality |
| D-NUH-031 | Use the actual reconstruction maps to form J(X)⇒d and d⇒I(X) at an arbitrary original d. Preserve d and the original supplied raw arrows; use no diagram object cast, replacement selection or per-test injectivity premise |
| D-NUH-032 | At OneCat, derive native-square equality by constructor congruence and proposition-valued fillers at the actual native Hom. This yields diagram-map equality, whole K/Q cancellation and ordinary factor contractions. New records use actual mate centres and no W/V inputs; selected-view comparisons are one-way consequences, not the source of universality |
| D-NUH-033 | Retain the ordinary whole reconstruction DefIso after the user's computational/internal review. Its inverse and naturality come from generic owners; derived equality proofs supply no caller coherence fields. A full E/D equivalence is not a current prerequisite. Keep the primitive-law, OneCat and strict-component qualifications explicit |
| D-NUH-034 | The independent homology-family record observes K, actual β=K(h)∘η and Q at the whole boundary diagram; it takes no W/V. Its arrow and Hom actions are those of the existing H. Generic boundary data and the unchanged pair observation are shared with legacy wrappers; no new primitive, rule or coherence field is introduced |
| D-NUH-035 | Original raw chain pairs form native inputs before any universal selection. Their whole-H record keeps the original pair as its literal index and reuses the existing semantic boundary factor; no reconstructed-pair transport, new equality proof or coherence field is needed |
| D-NUH-036 | Raw Freyd agreements now form native inputs without kernel presentations, with canonical local categorical data filled. Whole P/Q remain explicit for H and its record; the raw agreement is not treated as a universal provider or model. Shared raw observations and selected legacy definitions are unchanged |
| D-NUH-037 | Direct native maps derive their ordinary comparison internally from original raw-map factors and terminal-zero structure, without K/P. Preserve the native Hom's represented postcomposition head using the existing proof-time comparison as a typed view. Whole raw-map action composes with H's original Hom action; no new caller coherence fields or runtime rules |
| D-NUH-038 | Freyd raw-agreement PathMap composes with the existing direct native/H map functors. Original raw component classes and H-record endpoints remain literal observations. Whole action is in the existing agreement parameter at fixed raw morphisms; no new raw-complex category or joint directed action is claimed |
| D-NUH-039 | Connecting and exactness must use whole categorical universality directly. The ordinary category bridge stays optional. Whole Coim/Im and canonical comparison invertibility express Abelian normality/exactness; δ is to be built by whole universal descent. A whole declaration whose component invokes the old record algorithm is reference evidence, not completion of this migration |
| D-NUH-040 | Whole Coim/Im and their projection/inclusion are direct composites and whiskerings of the original K/Q and κ/q. Retain these functors and their higher action. The canonical Coim⇒Im comparison remains a separate construction; neither its implementation nor its Abelian invertibility is supplied by the six definitions |
| D-NUH-041 | Ordinary-target transposition first exchanges the original whole transformation, then forms its arrow family and exchanges the remaining arguments. Retain column observations of that single functor. Two whole evaluation projection folds and three proof-time comparisons qualify its actual κ/q endpoints. Whole zero-column universal comparisons and canonical mate assembly remain required; no pointwise cone rebuilding or new exactness axiom is admitted |
| D-NUH-042 | Terminal/initial whole family universality is now an explicit ordinary-target native presentation extension: two DefIso primitives with eight identity endpoint rules, not theorems derived from the old pointwise IsContr interface. Their actual-column instances and whole K/Q mates define Coim⇒ev₁ and ev₀⇒Im. Reconstruction is proved through native mate laws as a reviewer observation, not a new runtime cut. Canonical Coim⇒Im and exactness remain to be constructed |

Side tasks must name a concrete consumer and dependency. No speculative
spectral, normalization, parser or global profile project is admitted by
renaming it as a prerequisite.

## Launch Evidence And Next Action

2026-09-12: main was clean at `cbef77e7` with no staged or unstaged changes.
The new branch/worktree was created at that commit. Bootstrap succeeded with
Node 24.11.1 and pinned pnpm 11.16.0; all 373 packages came from the shared
store, and the workspace contract passed. The new worktree has its own
node_modules graph. No mathematical source or installed checker has changed.

The persistent goal is active and delegates to this file. NUH-1A establishes
the current native-owner/dependency inventory and source anchors. The exact
current nucleus passes its guarded focused baseline; the direct-op,
family-only and Sigma Empty fixtures all reproduce the inherited defects.
The owner ledger records their logs and the preserved patch's zero-context
format/current-source drift. Infinity Codex verification passed for 1,103
responses and identifies the accepted response 0003 as the latest archive.

Launch documentation checks pass: exact diff/whitespace, all 24 local links
in the new plan/ledger, Unicode notation/fences, active-reference lint and
report lifecycle/header registration (nine active plans). The staged launch
checkpoint contains only the new plan/ledger and their current-scope routing
in the existing reviews, repair plan, SOP and standing index/report. Main and
all sibling worktrees remain unchanged by this launch.

Next: continue NUH-1B, the joint variance design of the native Homd target,
before candidate source edits. The first dimension-2 constraint is recorded
in the owner ledger. The separate whole-universality dependency design is
inventoried in NUH-1C. No spectral or endpoint-checker research was started.

2026-09-12 continuation: the prior goal turn is classified as progress
(dedicated worktree, active plan/goal and fresh baseline at `190cd14f`). The
current worktree was clean and its nucleus hash unchanged at resumption.
NUH-1B1 now has a new closed target-polarity diagnostic, its walking-arrow
specialization and a separate lawful forward-action reviewer. All final
guarded runs pass in their recorded roles; accepting the Empty terms is
failure evidence for the encoding. The warning inventories of the core-only
diagnostic and companion agree completely at 1,144 critical pairs / 157
pattern reports. No active LP rule or installed checker was changed.

The first two raw forward-control assertion forms failed at elaboration;
the final explicitly typed reflexivity paths pass without new rules or
unifiers. Those statuses remain distinct in the diagnostic. Next is
NUH-1B2: qualify the native target's correct y-action in the terminal/constant
case, then resolve varying families and higher-base variance jointly.
Active-reference and report-lifecycle checks pass, as do exact diff and all
33 links in the affected diagnostic/plan/ledger. The three non-library LP
files pass the strict LHS audit and remain absent from positive registries.
The checkpoint adds no active-core or TypeScript change; its nucleus remains
the recorded `91f1974e` blob. The full implementation goal remains active.

The next bounded prototype derives NΠ_K(E)=O(Π_R(K)(Eᴼ)) and its whole action
on actual dual-family maps. The constant-family view recovers T(K)→C,
including nonidentity action and its next Hom. The initially attempted
unrestricted covariant constructor on Catd(K) was rejected by the laxity
direction audit; the refined input is O(Functord(Eᴼ,Dᴼ)), and an ordinary
old F:E→D is a checked wrong-input case. The guarded source-prefix driver
and exact scope/evidence are recorded in NUH-1B2a of the owner ledger.
This is an unpromoted ingredient. Full native target construction, coupled
repair and the later universality/homology consumers remain outstanding.

NUH-1B2b now completes a separate full-source polarity isolation. A private
patch changes the native target to negative sections while deliberately
retaining old op/Sigma conventions. Whole/point forward action computes to
the existing represented Hom action, including h ↦ F(p)∘h and its next Hom;
the old positive-section Empty route rejects at its intended type mismatch.
Three proof-time comparisons of strict constant constructions support one
constructor beta, with changed-parameter and runtime-noncollapse controls.
The first beta failed subject reduction before those comparisons; the
ledger preserves that failure and the exact final guarded gate.

The final copied source/reviewers and strict LHS audits pass. Warning
inventories agree with the exact baseline after source-line mapping, at
1,144 critical pairs / 157 pattern reports. The worktree's active nucleus
is unchanged. No full repair, arbitrary-family base-action theorem or
library-consumer migration is claimed. NUH-1B2 remains active: specify the
joint native variance/profile table and resolve the shifted-base input
problem before the coupled full-owner candidate. The universality/homology
refactors and model/reifier work have not started implementation.

NUH-1B2c now rules out the old local target independently of LP checking.
Two strict finite coefficient models on a walking noninvertible 2-cell force
1→0 under either attempted base-2-cell orientation. Their native Hom values
work instead on a proposed shared triangular index Sₓ(D). Its finite
semantic audit checks all index axioms, source action and native Hom
observations, including noninvertible Empty→Terminal components. The
[target design](TYPESCRIPT_EMDASH_NATIVE_HOMD_INDEX_TARGET_DESIGN.md) records
the joint direction table, original D/E inputs, actual mathematical
counterexamples, and the remaining ω/profile and native dependency gates.

The prior full-source negative-section experiment is preserved as scoped
evidence; it is not extended into the final general architecture. Next is
the complete native shared-index/module target, avoiding a definition
through Sigma/comma code that already requires the same homd action.
No active LP source or TypeScript implementation changed in this design
tranche. No spectral or endpoint-checker research was started.

NUH-1B2d now supplies a checked native shared-index ingredient on the
preferred prefix ending before homd_int. Existing Sigma, represented Hom
and duality owners define its carrier, point/arrow introductions and whole
projection, with actual arrow projection, retained triangle and further Hom
controls. No new primitive, rule or unifier is added. The guarded driver
checks the missing dependency boundary and identical complete warning
inventories (935 critical pairs / 137 pattern reports), with strict LHS
audits. This does not qualify the untested full kernel or general lax maps.

A genuine fibre 2-cell also separates the native T source from total O.
The design now records the strict higher shifts for the whole index and
target: S over D₁₂(Z), P_D and T_*(E) over D₂(Z). Those masks were
indistinguishable from the earlier shorthand in the finite ordinary-fibre
test. Next implement and qualify whole varying-x action and its actual
profiles, then the D-map/module action and full native target. The active
nucleus, ordinary homology implementation and TypeScript remain unchanged.

NUH-1B2e constructs the whole x-family in an isolated strict-reference
candidate with the further shifted-duality owners. Its S/P_D/T_*(E)
signatures, source-point action a↦a∘r and target precomposition H↦H∘S(r)
check, along with dimension-2/3 and wrong-base controls. Source action on an
index arrow stops at the recorded Sigma-map head. The guarded gate and
complete warning classification (+79 reported pairs, no new pattern reports)
are recorded in the owner ledger/design; the extra rules remain unpromoted,
and the full candidate and generic lax profiles remain unqualified.

Next is the structural represented-precomposition Sigma action and its
higher components, followed by general module/profile and full native Homd
qualification. The active mathematical sources and homology/TypeScript
implementation are unchanged; no spectral or endpoint-checker work resumed.

NUH-1B2f closes the selected structural Sigma source-action computation.
A shared defined body handles both arrow constructors and retains m and
θ⋆r; the source-2-cell component computes to (id_d,a⋆α). The ordinary
interchange comparison checks explicit side conditions, with changed-data,
missing-factorization and reversed-direction negatives. Existing full Hom
and Sigma-component rules move earlier in the copied candidate, and two
component projections expose the existing whole transformations.

The localized guarded gate passes with identical candidate/reviewer
inventories at 1,023 critical pairs / 137 pattern reports and a classified
+9 prefix delta. The full kernel and generic profiles remain unqualified;
no active mathematical or TypeScript source changed. Next settle the actual
family/section/native-Homd classifier profiles and general D-map/evaluation
interfaces before native integration. Preserve arbitrary constant-section
action; a strict-comparison comment alone cannot restrict it. The owner
ledger records source/log identities and failed intermediate forms.

The user has explicitly requested localized checks for subsequent work.
The validation section and launch prompt now carry that preference; this
tranche used only its affected owner prefixes, reviewers and document checks.

## Persistent Goal Launch Prompt

Current continuation boundary: the selected native duality owners and
their code status are specified in `TYPESCRIPT_EMDASH_DUALITY_SEMANTIC_THEORY.md`.
No generic set-indexed duality or external tensor transport is an
implementation target. Native target/module integration and the remaining
universality/homology rows are unfinished. The user's latest direction
supersedes the preceding historical profile-audit next steps. The documentation
checkpoint passes changed-link, Unicode/fence, active-reference, lifecycle
and exact-diff hygiene; it changes no active LP or TypeScript source.

Continue the native whole-universality and homology implementation in
`/home/user1/emdash1-native-universality-v1` on
`goal/native-universality-homology-v3.2`, using
`docs/TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_AND_HOMOLOGY_PLAN.md` as the living
authority for evolving scope, decisions, implementation rows, experiments,
validation and progress, under all active AGENTS/SOP instructions. Preserve
foundational hom_int/homd_int. Complete the scoped coupled variance repair,
whole-universality dependency refactor and native homology/proof-CAS consumer
work recorded there. Work autonomously through bounded reviewed tranches and
make local green checkpoint commits. Localize validation to affected owners,
features and files, reuse recent unchanged evidence, and avoid long-running
repository-wide typechecks or automatic aggregates as the user requested.
Keep the ledger current and preserve unrelated work and reference history.
Focus on the selected syntactic and internal duality/native-operation design.
Do not implement the former general D_S or external transport exposition.
Prioritize the direct homd_int declaration/target/projection adjustment;
auxiliary G:D→D′ index action is parked until an actual consumer needs it.
Empty proof audits and prototype global strictness migration are deferred. Integrate
`goal/opaque-action-profile-classifiers-v3.2` only after this goal, not as
a prerequisite for its completion.
Spectra, Heine generalization,
dependent stabilization, suspension research and beyond are deferred and
must not be investigated. Do not resume the separately deferred endpoint
checker experiments. No remote or destructive Git action is authorized.
Do not mark the goal complete until the plan's implementation and final
qualification outcomes have actually been achieved.
