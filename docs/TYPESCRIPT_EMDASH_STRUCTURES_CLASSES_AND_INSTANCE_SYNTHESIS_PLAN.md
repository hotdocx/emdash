# TypeScript/emdash Structures, Classes, And Instance Synthesis Plan

Date: 2026-08-08

Plan-ID: TS-EMDASH-CLASSES

Status: active living architecture and implementation ledger; STRUCT-PARAM-1
through ALGEBRA-GRADUATE-8 are final-green; MATH-CONSUMER-9 is retired without
implementation after its stale consumer was reconciled with the existing
acceptance evidence; remaining ergonomics, parameter-role inference, standard
library, package, and hosted rows stay separately gated

Branch: `goal/typescript-emdash-classes-v1`

Worktree: `/home/user1/emdash1-classes-v1`

Baseline: `66a61edb6299671934871ba468b4004ec077ecdf`
(`elaborator: graduate AI-native local foundation`)

## Executive Decision

The selected target is a **Lean-comparable authoring envelope over explicit
emdash Core**, not a clone of Lean's parser, kernel, tactic framework, or
inductive-declaration machinery.

Structures, classes, inheritance, instance declarations, named scopes, and
instance synthesis are direct-TypeScript management and elaboration features.
They lower to ordinary parameterized declarations, constructors, projections,
rewrite rules, and explicit dictionary arguments. They add no class,
structure, inheritance, or synthesis constructor to trusted Core. The small
TypeScript checker/evaluator remains unaware of typeclasses and checks the
fully explicit result. Deterministic Lambdapi emission remains an optional
conformance route rather than the production implementation of search.

The intended architecture is:

```text
typed *.emdash.ts declarations and proof source
                       |
        structure/class schemas + immutable scopes
                       |
        deterministic bounded evidence synthesis
                       |
             explicit, meta-free Core
                 /             \
      TypeScript checker    optional Lambdapi emitter/oracle
```

This is the practical compatibility target: an ordinary Lean development
whose organization depends on parameterized records, class hierarchies, local
instances, superclass inference, priorities, and recursive instance premises
should translate directly at the semantic level. Its declarations are written
with typed TypeScript builders rather than parsed Lean declaration text.

## Goal

Make TypeScript/emdash practical for AI-authored multi-file proof
developments by supplying:

- parameterized and dependent structures;
- stable named-field construction and projection handles;
- classes as structures plus search metadata;
- multiple inheritance with canonical shared ancestors;
- portable local, imported, global, and named instance scopes;
- deterministic recursive synthesis with complete traces;
- general call elaboration that inserts evidence at class-marked implicit
  binders; and
- publishable packages and hosted research-workspace integration after the
  local semantic boundary is qualified.

An AI agent should normally see a compact `synth(...)` request in source and
be able to inspect a stable resolution trace when it is nontrivial. The
checked artifact must contain the selected explicit dictionary term, so no
long-lived editor, MCP server, process registry, or hidden search state owns
proof meaning.

## Governing Authorities

Read and preserve these authorities in order:

1. `emdash2/emdash3_2.lp`, the active mathematical and computational
   specification;
2. the active extensions and workflow in `emdash2/AGENTS.md`;
3. `emdash2/emdash3_2_checks.lp`;
4. `emdash2/reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`;
5. `emdash2/reports/EMDASH_FOUNDATIONS.md`;
6. `emdash2/reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`;
7. `docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md` and the active plans it
   routes to;
8. `docs/TYPESCRIPT_EMDASH_AI_NATIVE_WORKSPACE_AND_PROOF_PLAN.md` for the
   explicit-Core, source/artifact, workspace, and synthesis boundaries;
9. `docs/RECORD_STRUCTURE_USABILITY_V3_2_PLAN.md` for the completed
   unparameterized dependent-structure slice; and
10. this plan for the forward structures/classes/synthesis implementation.

The stale category-specific root prototype is implementation evidence only.
It must not become a second v3.2 mathematical authority, and the retired
`D0`/`D1` compatibility API must not be recreated.

## Reviewed Baseline

### Structure macro

`src/v3_2/lf_structure_macro.ts` already provides a useful outer-LF macro:

- a callback-once direct-TypeScript field builder;
- dependent field types referencing earlier fields;
- one opaque carrier and one injective constructor;
- named projections;
- one ordered subject-reducing runtime beta per projection;
- deterministic Lambdapi fragment emission; and
- fail-closed scope, provenance, collision, forward-reference, and escaped-
  binder diagnostics.

Its carrier is currently always declared at `TYPE`. The constructor returns
the bare carrier, projections accept the bare carrier, and the runtime beta
patterns carry only field captures. Structure parameters are therefore a
real missing semantic layer, not a spelling change.

### Dictionary synthesis

`src/v3_2/lf_dictionary_synthesis.ts` deliberately implements a much smaller
contract than typeclass search:

- the caller supplies the complete finite candidate list;
- the target is closed and meta-free;
- candidates are exact installed free declarations;
- every candidate is independently checked;
- zero matches is missing, one match succeeds, and multiple matches are a
  hard ambiguity; and
- there is no discovery, recursive premise search, scope hierarchy, priority,
  backtracking, local binder evidence, or process I/O.

`src/v3_2/lf_dictionary_authoring.ts` derives and fills only the first leading
implicit binder of one global call. It is evidence that synthesis can remain
outside Core, but it is not the eventual general call elaborator.

### AI-native boundary

The completed AI-native foundation already establishes the correct product
contract:

- canonical source is a reviewable file;
- verified state is deterministic derived evidence;
- explicit Core is the semantic boundary;
- transport such as MCP, HTTP, browser, or hosted execution is optional;
- easy transitions remain compact; and
- difficult transitions expose stable diagnostics and traces.

This plan extends that boundary; it does not replace it.

### Lean reference semantics

The local Lean 4 source at `/home/user1/lean4-source-code` and the official
reference establish the user-facing comparison target:

- a class is structurally close to a structure but is registered for
  synthesis;
- class parents and method receivers use instance-implicit arguments;
- structures may be parameterized and dependent;
- inheritance separates physical parent representation, ancestral field
  identity, generated parent projections, and name-resolution order;
- overlapping diamonds share ancestor data rather than duplicating it;
- C3 linearization controls inherited name/default resolution;
- instance search is indexed, recursive, scoped, priority-aware, tabled, and
  bounded; and
- input, output, and semi-output parameter roles influence when search may
  proceed.

Relevant primary references:

- <https://lean-lang.org/doc/reference/latest/Type-Classes/Class-Declarations/>
- <https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/>
- <https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Declarations/>
- <https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/>
- <https://lean-lang.org/doc/api/Lean/Structure.html>

Lean is a behavioral comparison and acceptance-corpus source. Its parser,
implementation layout, recency tie-breaks, tactic infrastructure, and kernel
are not imported architecture.

### Lambdapi/Elpi reference

Deducteam/Lambdapi PRs
[#1378](https://github.com/Deducteam/lambdapi/pull/1378) and
[#418](https://github.com/Deducteam/lambdapi/pull/418) validate one important
partition: class and instance metadata may feed a separate proof-search
engine which fills implicit evidence, while the logical framework receives
ordinary terms. They may later inform an optional Elpi provider or
conformance experiment.

They do not supply the selected TypeScript product implementation. The
TypeScript resolver must work without Lambdapi or Elpi and must emit explicit
evidence before either backend is invoked.

## Non-Goals

This plan does not authorize or promise:

- parsing structure, class, instance, inductive, or theorem declarations;
- a Lean source parser or Lean binary/API compatibility;
- a new Core node or trusted checker branch for records or typeclasses;
- a process-global mutable instance registry;
- treating `unif_rule` as a typeclass engine;
- a general Prolog engine or unbounded theorem search;
- a general end-user `inductive` declaration frontend;
- positivity checking, generated eliminators, generated recursion, or
  automatic deriving;
- Lean tactic compatibility;
- accidental same-name field merging;
- order-sensitive silent choice between genuinely distinct equal-ranked
  solutions;
- arbitrary rewrite rules being classified as safe merely because they
  typecheck; or
- mandatory Lambdapi, MCP, network, or hosted execution.

## Mechanism Partition And Trust Boundary

Keep three mechanisms distinct:

1. **Runtime rewrite/computation** is part of the explicit checked module and
   evaluator semantics.
2. **Proof-time unification rules** influence conversion/unification at their
   reviewed owners.
3. **Instance synthesis** searches a finite immutable registry snapshot for a
   term, then submits the selected explicit term to the ordinary checker.

Instance search cannot certify a term. Registration validates provider types;
resolution constructs evidence; the Core checker remains the authority for
the result. Search traces and TypeScript types are ergonomic evidence only.

## Architecture

### A. Parameterized dependent structures

Extend the existing callback-once builder with parameters declared before
fields. A parameter has:

- a stable ordinal and binder name;
- a type which may depend only on earlier parameters;
- an explicit carrier binder mode;
- an explicit constructor binder mode; and
- an explicit projection binder mode.

The separate modes are intentional. They prevent the macro from assuming
that the carrier, constructor, and projections quantify a parameter with the
same plicity or variance. The carrier-result application always follows the
carrier binder plicity.

The generated package is:

```text
carrier    : Π carrier-parameters, TYPE
constructor:
  Π constructor-parameters, Π fields, carrier carrier-parameters
projectionᵢ:
  Π projection-parameters,
  Π record : carrier carrier-parameters,
  field-typeᵢ[parameters, earlier projections record]

projectionᵢ parameters
  (constructor parameters fields)  ↪  fieldᵢ
```

Parameter and field dependencies are lowered locally-namelessly for each
generated context. Runtime-rule variables include parameter captures followed
by field captures, with their dependent types reconstructed in source order.
Unparameterized callers remain exact.

The macro must continue to generate no eta, eliminator, recursion principle,
positivity claim, source inductive node, or hidden kernel declaration.

### B. Named construction and private layout

Add a named construction helper after parameterization is stable. It accepts
parameter applications plus a field map keyed by stable field handles, checks
that every required field appears exactly once, orders the arguments
canonically, and returns an ordinary constructor application.

Generated constructor position is not a durable public record layout. This
allows inheritance storage to evolve without breaking authoring source.

### C. Class schemas

A class is a parameterized structure plus immutable authoring metadata:

- stable class ID and generated structure handle;
- parameter roles (`input`, later `output` and `semi-output`);
- stable field/method IDs;
- direct-parent specifications and substitutions;
- canonical ancestor identities and projection terms; and
- generated superclass instance providers.

An instance-implicit source binder remains an ordinary implicit Core binder
plus metadata consumed by the call elaborator. Core plicity remains
`explicit | implicit`; no third trusted binder kind is needed.

### D. Multiple inheritance and ancestor sharing

The first representation semantically flattens an inheritance graph into one
canonical field telescope:

- each ancestral field identity has one canonical slot;
- a field identity is based on its declaring schema and stable field ID, not
  spelling alone;
- generated conversions reconstruct direct and transitive parents from those
  slots;
- every route through a diamond reconstructs a common ancestor from the same
  slots; and
- generated representation remains private.

C3-style linearization determines inherited unqualified name lookup and later
default resolution. An inconsistent hierarchy fails closed. Unrelated
same-spelled fields require qualification, renaming, or an explicit
`share`/`identify` declaration whose types are definitionally checked. A
Lean-translation helper may turn compatible same-name overlap into that
explicit mapping, but the core schema never merges by spelling accidentally.

Superclass providers are generated only for nonredundant canonical ancestor
paths. Distinct diamond paths must normalize to the same evidence or be
designated as the same canonical ancestor provider.

### E. Portable instance declarations and scopes

An instance declaration records checked immutable metadata:

- stable provider ID and provenance;
- generic ordinary parameters;
- recursively synthesized instance premises;
- result class head;
- priority;
- visibility and named scope; and
- explicit provider term or term builder.

Search receives a registry snapshot and an explicit scope. The scope contains
lexical/local evidence, explicitly opened named scopes, imported providers,
and global providers. It never discovers candidates by enumerating mutable
host state.

The initial precedence is:

```text
local > explicitly opened/named > imported/global
```

Within a tier, higher priority is considered first. A deterministic provider
ID orders diagnostics but does not silently decide between two genuinely
different equal-ranked successes.

### F. Deterministic recursive resolver

Resolution should:

1. validate the target class application and input-role readiness;
2. index candidates by exact class head;
3. unify a provider result with the requested target;
4. instantiate its ordinary parameters;
5. recursively solve its instance premises in the same immutable scope;
6. assemble an explicit provider application;
7. check the result against the target; and
8. return the term plus a complete stable trace.

The resolver is tabled by normalized goal plus scope fingerprint, detects
cycles, and enforces explicit depth/size/fuel bounds. Public outcomes are:

```text
solved | missing | stuck | ambiguous | limit-exceeded
```

Distinct equal-ranked successful evidence is ambiguous unless the terms are
definitionally equal or are canonical projections of the same shared
ancestor. Higher priority may intentionally select one provider. Explicit
arguments and explicit scope control remain the escape hatch.

Implement all-input matching first. Design parameter-role metadata from the
start, but defer output/semi-output inference and stuck/resume behavior until
an exact consumer requires them.

### G. General call elaboration

Replace the leading-only dictionary helper with a binder-walking elaborator
which:

- consumes explicit and ordinary implicit arguments;
- substitutes each accepted argument into later binder types;
- recognizes class-marked implicit binders at arbitrary positions;
- creates a source-visible synthesis request;
- resolves it under the supplied scope; and
- returns one ordinary explicit Core application plus synthesis traces.

Canonical source may retain compact `synth(...)` requests. Canonical checked
artifacts retain the selected explicit evidence. No unresolved search request
crosses the Core-checker boundary.

### H. Curated inductives and HITs

The proof assistant may expose useful inductive types and directed or
categorical HITs without implementing a general inductive declaration
frontend.

Curated standard-library packages should carry versioned declarations,
constructors, eliminators, computation rules, provenance, digests, and
available metatheoretic evidence. Natural numbers, finite families, equality,
lists/options where needed, truncations, quotients, and selected categorical
HITs are library artifacts rather than products of a universal command.

Expert users may add hand-written outer-LF declarations and rewrite rules
under an explicit `trusted-extension`/`unsafe-extension` profile. The profile
must state that successful checking does not by itself establish consistency,
confluence, normalization, positivity, or semantic justification.

### I. Package boundary

Do not publish the private repository-root workbench. The unscoped npm name
`emdash` is already occupied by an unrelated package. Subject to npm scope
ownership, the first distributable boundary should be:

- `@emdash/core`: browser-safe Core, checker/evaluator, and curated public
  subpath exports such as `./authoring` and `./workspace`;
- `@emdash/cli`: Node workspace/check/artifact commands; and
- later `@emdash/stdlib`: versioned curated inductive/HIT/algebra/category
  artifacts.

Packages contain built JavaScript and `.d.ts` files, use a strict public
export map, do not require `ts-node`, and pass a packed-install consumer test.
Publishing uses npm trusted publishing/OIDC and provenance. A git-ignored
token is neither moved nor read as part of normal publication.

### J. GetPaidX/LastRevision and Arrowgram

`emdash1` owns proof semantics, packages, and checked artifacts.
`closerfans` owns GetPaidX/LastRevision hosted files, workspace lifecycle,
runtime/build/publish operations, and additive/versioned MCP/API adapters.
`arrowgram` owns diagram and research-document rendering which consumes
emdash artifacts.

The first hosted template should be a pure-TypeScript
`emdash_research_workspace` or `emdash_proof_workspace`. The existing
GetPaidX controller images use Node 20 while this workspace requires Node
22.13 or newer; use a compatible new controller/template boundary rather than
silently breaking existing templates. A Lambdapi-equipped profile is optional
for conformance and advanced development, not required for ordinary hosted
checking.

Published or in-review MCP operations must remain compatible. Proof-oriented
operations are additive, versioned adapters over generic source read/write,
check, and artifact retrieval. Files, locks, and content-addressed artifacts
remain authoritative rather than MCP session state.

Cross-repository implementation starts only after the local package and a
packed consumer are green. Each sibling repository gets its own status/SOP
inspection and branch before edits.

## Lean-Comparable Compatibility Matrix

| Capability | Target | Boundary |
| --- | --- | --- |
| Parameterized/dependent structures | first-class | direct TS macro to ordinary LF declarations |
| Named record construction/projections | first-class | authoring helpers; private generated layout |
| Classes and methods | first-class | structure plus metadata; explicit Core evidence |
| Multiple inheritance | first-class | strict C3 lookup plus canonical flattened slots |
| Shared diamond ancestors | first-class | one ancestral identity and canonical conversions |
| Local/global/named scoped instances | first-class | immutable explicit registry snapshots |
| Recursive instance premises | first-class | bounded tabled resolver |
| Priorities | first-class | tier then numeric priority |
| Ambiguity diagnostics and traces | first-class | stable machine-readable evidence |
| Output/semi-output parameters | later | metadata now; inference after all-input search |
| Defaults and record updates | later | named-layout authoring layer |
| Default instances/coercions | later | consumer-gated separate policies |
| Declaration text parsing | non-goal | expressions/terms only may use text parsing |
| General inductive declarations | non-goal | curated stdlib plus explicit trusted extensions |
| Lean tactics/ABI/source compatibility | non-goal | semantic authoring compatibility only |

## First Acceptance Corpus

The first end-to-end hierarchy is the algebraic diamond:

```text
Mul α
One α
Semigroup α extends Mul α
MulOneClass α extends Mul α, One α
Monoid α extends Semigroup α, MulOneClass α
```

It must demonstrate:

- parameterized structures and classes;
- multiple inheritance;
- exactly one shared `Mul α` ancestor;
- named-field construction;
- generated direct and transitive parent projections;
- a local `Monoid α` dictionary synthesizing `Semigroup α`,
  `MulOneClass α`, `Mul α`, and `One α`;
- definitionally equal or canonical evidence for both diamond routes to
  `Mul α`;
- at least one generic provider with a recursive instance premise;
- stable missing, ambiguity, cycle, and bounded-search traces; and
- explicit generated Core accepted by the TypeScript checker.

Together with the two-dependent-parameter structure fixture from
STRUCT-PARAM-1, this corpus is representative enough to qualify the local
parameter, class, inheritance, scope, recursive-search, and saturated-call
mechanisms. It is not necessary to manufacture a geometry-shaped proxy before
continuing. In particular, the historical `struct_cov_sieve` spelling is not
an active v3.2 owner and is not a required consumer. Category/Functor/
Adjunction integrations remain legitimate later consumers when a real
development needs them; multiple structures on one carrier make their scope
discipline important, but they are not a prerequisite for this qualification.

## Implementation Ledger

| Row | State | Dependency-ready outcome |
| --- | --- | --- |
| ARCH-0 | complete | Architecture, comparison target, trust boundary, non-goals, and acceptance corpus recorded here. |
| STRUCT-PARAM-1 | complete | The existing macro now has dependent parameter telescopes and explicit carrier/constructor/projection modes while preserving unparameterized declarations, rules, order, and emission. |
| STRUCT-NAMED-2 | complete | Stable owner-aware handles and order-independent named parameter/field assignments now lower to one deeply frozen ordinary constructor call. |
| CLASS-SCHEMA-3 | complete | Serializable class, parameter-role, declared-method, and ordered-parent metadata is public; every parentful schema is explicitly marked unlowered. |
| CLASS-INHERIT-4A | complete | Strict C3, canonical inherited identity classes, explicit physical-slot binding/sharing, and conflict-free lookup are implemented as finite frozen metadata, without conversion terms. |
| CLASS-INHERIT-4B | complete | Transparent direct-parent reconstruction definitions are public and checked; both explicit algebraic diamond routes normalize to one canonical constructor term. |
| SYNTH-SCOPE-5 | complete | Checked providers and immutable explicit scope ranks are public, focused-green, and qualified by the complete shared TypeScript gate. |
| SYNTH-RECURSE-6 | complete | The bounded exact-head resolver is public and final-green with recursive premises, tables, explicit bounds, ambiguity, runtime-backed definitional equality, and portable traces. |
| CALL-SYNTH-7A | complete | Saturated binder walking, ordinary implicit inference, arbitrary annotated instance positions, delayed ground synthesis, stable failure data, and final explicit-Core checking are public and final-green. |
| CALL-SYNTH-7B | gated | Add partial application, named arguments, defaults, and stronger retry/postponement only after 7A and an exact ergonomic consumer. |
| ALGEBRA-GRADUATE-8 | complete | One exact local `Monoid A` scope now qualifies every direct/transitive parent, positive recursive provider expansion, coherent `Mul` diamond, and the saturated class-aware call under the same immutable artifacts. |
| MATH-CONSUMER-9 | retired without implementation | The historical `struct_cov_sieve` name was only a parameter-plicity shape inherited from the Cartier review, not an active owner or missing kernel feature. STRUCT-PARAM-1 already qualifies the distinct dependent parameter modes, and ALGEBRA-GRADUATE-8 already supplies the representative Lean-style class consumer. No replacement proxy or mathematical-source edit is justified. |
| PARAM-ROLES-10 | gated | Add output/semi-output and stuck/resume only after an exact consumer audit. |
| STDLIB-11 | gated | Define curated inductive/HIT artifact and trusted-extension profiles. |
| PACKAGE-12 | gated | Publishable `@emdash/*` package boundaries and packed-consumer evidence. |
| HOSTED-13 | gated | Add compatible GetPaidX template/API adapters and Arrowgram consumption after PACKAGE-12. |

Only one row is implemented at a time. A later row may be repartitioned by a
recorded audit, but must not silently broaden an earlier checkpoint.

## STRUCT-PARAM-1 Frozen First Tranche

The first implementation is intentionally bounded:

1. Add `parameter(...)` to the callback-once structure builder.
2. Require parameters to precede all fields.
3. Permit a parameter type to reference only earlier parameters.
4. Permit every field type to reference parameters and earlier fields.
5. Require explicit carrier, constructor, and projection binder modes.
6. Generate parameterized carrier, constructor, projections, and beta rules.
7. Expose immutable parameter handles in the expansion handle.
8. Preserve existing unparameterized declarations, rules, source order, and
   Lambdapi emission exactly; the public handle gains only an additive empty
   parameter list.
9. Add focused positive tests for dependency, mode differences, Core checking,
   subject reduction, deterministic Lambdapi emission, and caller-input
   immutability.
10. Add fail-closed tests for a parameter after a field, foreign parameter
    tokens, duplicate binder names, and invalid modes. Callback order makes a
    future-parameter token unconstructible in the first place.

This tranche adds no class metadata, inheritance, named construction,
resolver recursion, parser route, Core node, or kernel rule.

## STRUCT-PARAM-1 Completion Record

`STRUCT-PARAM-1` is final-green on 2026-08-08. The implementation:

- adds one callback-scoped `parameter(...)` declaration before fields;
- gives each parameter explicit carrier, constructor, and projection binder
  modes;
- lowers dependent parameter and field types separately in every generated
  binder context;
- applies the carrier with carrier plicity, the constructor with constructor
  plicity, and projections with projection plicity;
- includes parameter captures and their dependent types in every generated
  projection beta;
- exposes immutable parameter handles while leaving existing
  unparameterized declaration/rule/order/emission output exact;
- rejects parameters after fields, duplicate parameter binders, invalid mode
  triples, and foreign parameter expressions; and
- preserves caller-owned mode objects and freezes only returned artifacts.

The acceptance fixture deliberately uses two dependent parameters whose
plicities differ among carrier, constructor, and projection binders. Its
generated declarations and rules are checked by the ordinary TypeScript LF
compiler, its betas reduce to the selected field under the ordinary runtime,
and its deterministic emitted fragment is accepted by Lambdapi. The callback
order makes a future-parameter token unavailable by construction.

Exact validation:

- `node --require ts-node/register --test
  tests/v3_2_lf_structure_macro_tests.ts`: 13 executable tests passed, two
  opt-in Lambdapi tests skipped;
- `timeout 90s env EMDASH_RUN_LAMBDAPI_STRUCTURE_PROBES=1 node --require
  ts-node/register --test tests/v3_2_lf_structure_macro_tests.ts`: 15/15
  passed, including both unparameterized and parameterized Lambdapi
  fragments;
- `./scripts/pnpmw run typecheck`: passed;
- changed-file ESLint for the macro and focused suite: passed;
- `git diff --check`: passed; and
- the one required changed-shared-boundary `./scripts/pnpmw run check:ts`:
  1,516 tests across 228 suites, 1,462 passed, 54 intentionally skipped,
  zero failures. It took approximately 34 minutes and must be carried forward
  rather than rerun for unchanged boundaries.

No `emdash2/` source, active kernel owner, runtime rule, proof rule, Core node,
parser, browser entry, package boundary, or sibling repository changed. The
bounded generated-fragment probe was the relevant Lambdapi conformance gate;
the unchanged active-kernel aggregate was not rerun. The rollback-safe
checkpoint is the local commit containing this completion record and the
message `elaborator: add parameterized structure telescopes`.

`STRUCT-NAMED-2` followed as the next dependency-ready row. Its audit and
proposal were frozen separately before implementation so that named
construction did not absorb class metadata or inheritance.

## STRUCT-NAMED-2 Audit And Frozen Contract

The 2026-08-08 continuation audit found:

- `CoreLfStructureHandle` is consumed only by the focused structure suite;
  no production source currently relies on its exact nested shape;
- `constructorTerm` is a transfer-IR global head, while `kernelCall` operates
  only after compilation and would place this authoring helper on the wrong
  side of the explicit-Core boundary;
- named construction values may legitimately be open locally nameless
  transfer expressions, so the helper cannot require closed terms or invent
  a checking context;
- field constructor plicity is not currently retained by projection handles,
  while parameter handles already retain their three owner-specific modes;
  and
- the existing declaration compiler/checker is the right authority for value
  types after the helper has assembled an ordinary transfer expression.

The selected additive API is:

```ts
constructCoreLfNamedStructure({
  structure: expansion.handle,
  parameters: [
    { parameter: expansion.handle.parameters[0], value: A },
  ],
  fields: [
    { field: expansion.handle.projections[1], value: proof },
    { field: expansion.handle.projections[0], value: operation },
  ],
})
```

Its exact contract is:

1. Parameter and projection handles carry the stable declaring-carrier
   symbol. Projection handles additionally carry the original field binder
   mode.
2. The input contains explicit arrays of parameter and field assignments.
   Their source order is irrelevant.
3. A supplied handle is matched structurally against the selected structure's
   canonical handle at its ordinal. This accepts deterministic copied data but
   rejects a handle from another structure.
4. Every parameter and every field must occur exactly once. Missing,
   duplicate, foreign, malformed, and non-term assignments fail at stable
   source-like paths.
5. Canonical constructor argument order is all parameters by ordinal followed
   by all fields by ordinal.
6. Parameter argument plicity comes from each parameter's constructor mode;
   field argument plicity comes from the recorded field mode. The caller never
   supplies either plicity.
7. Ordinary `type`, `bound`, `global`, `call`, `pi`, and `lambda` transfer
   expressions are cloned without mutating or freezing caller data. Runtime
   `capture` and `wildcard` syntax is rejected.
8. The result is one deeply frozen ordinary `CoreLfTransferExpression` whose
   head is the generated constructor. It contains no named-construction node
   and crosses no trusted boundary.
9. Correct value types are checked only when the returned term is installed
   or checked in its actual context. The helper claims completeness and
   deterministic ordering, not independent dependent typechecking.
10. The focused corpus covers unparameterized and parameterized structures,
    deliberately reversed input order, distinct plicities, open-term cloning,
    caller immutability, ordinary LF compilation, and every fail-closed
    assignment class.

The frozen error classes are `INVALID_CONSTRUCTION`, `FOREIGN_ARGUMENT`,
`DUPLICATE_ARGUMENT`, and `MISSING_ARGUMENT`, with exact paths distinguishing
parameters from fields. This tranche adds no class/schema metadata,
inheritance, defaults, updates, synthesis, parser route, Core node, kernel
rule, browser export, or sibling-repository change.

The proposal gate `H-TS-EMDASH-CLASSES-NAMED-001` is approved under the
user-authorized unattended-review delegation, with immediate human
supersession. The proposal checkpoint records the pre-implementation
backtracking boundary. Because the exported structure authoring surface
changes, one root `check:ts` is required only after the focused tranche is
otherwise green; the resulting aggregate is then carried forward. No
repository-wide `check:all` or unchanged active-kernel aggregate is required.

## STRUCT-NAMED-2 Completion Record

`STRUCT-NAMED-2` is final-green on 2026-08-08. The implementation:

- adds stable declaring-carrier ownership to parameter and projection
  handles, while projections also retain their original constructor-field
  mode;
- adds `constructCoreLfNamedStructure(...)` as a transfer-IR authoring helper
  over explicit named parameter and field assignments;
- structurally accepts deterministic copies of canonical handles while
  rejecting malformed or foreign ownership at stable paths;
- rejects missing and duplicate assignments independently for parameters and
  fields;
- derives plicity from the selected canonical handles and emits arguments in
  parameter-then-field ordinal order, independent of caller order;
- clones ordinary open transfer terms, rejects runtime-only capture/wildcard
  syntax, preserves all caller-owned values, and deeply freezes the returned
  constructor call; and
- leaves dependent value typing to the ordinary LF compiler/checker at the
  actual installation context.

The positive corpus constructs both unparameterized and parameterized
records from deliberately reversed assignments. The parameterized fixture
uses distinct parameter and field plicities, installs the result as a
transparent ordinary LF definition, and passes normal compilation/checking.
The negative corpus fixes the public diagnostic classes and paths for missing,
duplicate, foreign, malformed, and rule-only inputs.

Exact proportional validation:

- `node --require ts-node/register --test
  tests/v3_2_lf_structure_macro_tests.ts`: 19 tests total, 17 passed and the
  two opt-in Lambdapi emission probes intentionally skipped;
- `./scripts/pnpmw run typecheck`: passed;
- changed-file ESLint for the macro and focused suite: passed; and
- `git diff --check`: passed.

The one required `./scripts/pnpmw run check:ts` was run once after those gates
were green. Its workspace check, typecheck, and complete lint phases passed;
the test phase emitted its matrix through the late workspace/scale suites
without a reported failure. The terminal transport discarded the final TAP
footer and exit packet during automatic context compaction, so this record
does not invent exact aggregate counters. The completed run was not repeated:
the focused owner suite and static gates above are the exact retained evidence,
and the preceding 1,516-test aggregate remains valid for every unchanged
consumer boundary.

No Lambdapi fragment, `emdash2/` source, active kernel owner, runtime rule,
proof rule, Core node, parser, browser entry, package boundary, or sibling
repository changed. Consequently neither a new Lambdapi probe nor an
active-kernel/repository-wide aggregate was relevant. The proposal
backtracking boundary is `e798ec0`; the rollback-safe implementation
checkpoint is the local commit with message
`elaborator: add named structure construction`.

The next dependency-ready row is `CLASS-SCHEMA-3`. Its first action is a
read-only consumer and representation audit followed by an exact frozen
metadata contract. That checkpoint must add no inheritance lowering,
instance registry, synthesis, call elaboration, parser behavior, or Core
semantics.

## CLASS-SCHEMA-3 Audit And Frozen Contract

The 2026-08-08 audit compared the completed structure expansion/handle and
dictionary seams with Lean's `StructureInfo`, `StructureParentInfo`, and
`ClassEntry` partition. It found:

- Lean likewise keeps structure layout, ordered parent metadata, class
  registration, and output-parameter positions outside its kernel terms;
- the emdash structure expansion already contains the carrier and constructor
  telescopes needed to recover declared parameter and method types without
  adding those types to trusted Core or accepting caller-supplied duplicates;
- direct-parent order must remain source-significant because the next row's
  strict C3 calculation consumes it, while argument order within one parent
  application should be canonical and handle-directed;
- a parent application is a type expression open only in the complete child
  parameter telescope, so it can be stored as ordinary locally nameless
  transfer IR and checked when inheritance is lowered in context;
- class parameter roles can be recorded now, but output/semi-output search
  scheduling and dependency restrictions remain deliberately gated by
  `PARAM-ROLES-10`; and
- an already generated child structure with declared local fields does not
  yet implement its parents. Any parentful schema must therefore say
  explicitly that its layout is unlowered rather than exposing a false
  superclass capability.

The selected additive module is `src/v3_2/lf_class_schema.ts`. Its principal
authoring shape is:

```ts
const monoid = declareCoreLfClassSchema({
  expansion: monoidStructure,
  parameterRoles: [
    { parameter: monoidStructure.handle.parameters[0], role: 'input' },
  ],
  directParents: [
    {
      parent: semigroup,
      arguments: [{
        parameter: semigroup.structure.parameters[0],
        value: coreLfClassParameterTerm(
          monoidStructure,
          monoidStructure.handle.parameters[0]
        ),
      }],
    },
  ],
})
```

Its exact contract is:

1. `declareCoreLfClassSchema(...)` accepts one complete
   `CoreLfStructureDeclarationExpansion`. The class ID is derived from its
   qualified carrier symbol; the caller cannot supply a competing ID.
2. The function validates the generated carrier/constructor telescope seam
   and copies the structure handle. It derives, rather than duplicates,
   parameter and declared-method order, binder names, modes, projection
   symbols, and locally nameless declared types.
3. A parameter identity is `(declaring class ID, parameter ordinal)`. A
   declared-method identity is `(declaring class ID, field ordinal)`. Spelling
   is descriptive and never establishes cross-class identity.
4. Parameter roles are `input | output | semi-output`. Sparse role
   assignments are order-independent and keyed by stable parameter handles;
   an unspecified parameter defaults to `input`. Duplicate, foreign, or
   malformed assignments fail closed.
5. Every declared method records its projection handle and an authoring
   receiver contract saying `class-evidence` while retaining the projection's
   ordinary explicit Core record argument. No third Core plicity is added.
6. Direct parents preserve declaration order. Each parent input carries a
   previously produced class schema and a complete order-independent named
   assignment for that parent's parameters. Self-parenting and duplicate
   direct class IDs fail closed.
7. Parent arguments are cloned at exactly the child-parameter depth, may use
   ordinary transfer term syntax, and may not use dangling indices,
   `capture`, or `wildcard`. Their plicity comes from the parent's carrier
   modes, never from the caller.
8. Each stored parent record contains only a stable parent-class reference,
   canonical arguments, and the ordinary `Parent ...` application. It does
   not recursively embed a parent schema or retain callbacks/object identity,
   keeping the result finite and JSON-serializable.
9. `coreLfClassParameterTerm(expansion, parameter)` validates a structural
   parameter handle and returns its deeply frozen bound reference in the full
   class-parameter telescope. This is the compact safe path for common
   `Parent alpha` substitutions; arbitrary ordinary terms remain possible.
10. The returned schema is a deeply frozen caller-independent snapshot with
    profile revision `emdash-lf-class-schema-v1`. Its layout status is
    `parent-free` when there are no parents and `parents-unlowered` otherwise.
11. `parents-unlowered` schemas are metadata inputs for `CLASS-INHERIT-4`, not
    superclass evidence and not candidates for instance search. The next row
    alone may add C3 order, canonical inherited-field slots, sharing,
    conversions, or superclass providers.
12. Declared types and parent applications are not independently certified by
    this metadata function. The ordinary LF compiler/checker remains the
    authority when generated inheritance declarations are installed.

The frozen diagnostic classes are `INVALID_CLASS_SCHEMA`,
`INVALID_PARAMETER_ROLE`, `FOREIGN_PARAMETER`,
`DUPLICATE_PARAMETER_ROLE`, `INVALID_PARENT`, `DUPLICATE_PARENT`,
`INVALID_PARENT_ARGUMENT`, `FOREIGN_PARENT_ARGUMENT`,
`DUPLICATE_PARENT_ARGUMENT`, and `MISSING_PARENT_ARGUMENT`. Exact paths
distinguish the expansion seam, role assignment, parent ordinal, parent
parameter handle, and argument value.

The focused corpus will cover default and explicit roles, stable declared
types and field identities, copied handles, caller immutability, deep freeze,
JSON round-trip data, ordered multiple parents, canonical parent argument
ordering/plicity, and every frozen failure class. This tranche adds no
inheritance declarations or rules, C3 algorithm, field sharing, superclass
projection, instance provider/scope/search, general call elaborator, parser,
Core/checker branch, Lambdapi emission, browser export, package split, or
sibling-repository change.

The proposal gate `H-TS-EMDASH-CLASSES-SCHEMA-002` is approved under the
user-authorized unattended-review delegation, with immediate human
supersession. The documentation-only proposal checkpoint is the backtracking
boundary. Implementation should add one isolated module and focused suite,
then wire the public v3.2 barrel and root test runner only when the bounded
surface is ready. That shared-surface checkpoint requires one final
`check:ts`; until then, no long aggregate is run. No Lambdapi or active-kernel
gate is relevant because the frozen row changes metadata only.

## CLASS-SCHEMA-3 Completion Record

`CLASS-SCHEMA-3` is final-green on 2026-08-08. The implementation adds the
public `lf_class_schema` authoring module and:

- classifies one complete generated structure expansion without changing or
  re-emitting any declaration or rule;
- derives the qualified class ID, stable parameter/method identities,
  parameter and method declared types, modes, names, and projection handles
  from the generated expansion rather than caller duplication;
- defaults sparse parameter-role metadata to `input` while preserving
  explicit `output` and `semi-output` roles for later search scheduling;
- records every method receiver as authoring-level `class-evidence` over its
  unchanged ordinary explicit Core record argument;
- validates copied class and handle data structurally, preserving
  serialization/replay rather than relying on JavaScript object identity;
- builds canonical ordered parent applications from complete named parameter
  assignments, deriving carrier plicity and validating open terms at exactly
  the child-parameter depth;
- supplies `coreLfClassParameterTerm(...)` for compact, safe child-parameter
  references in common parent substitutions;
- stores finite parent references rather than nested object graphs, so class
  schemas remain JSON-serializable; and
- distinguishes `parent-free` from `parents-unlowered`, preventing metadata
  from being mistaken for implemented superclass evidence.

The focused suite exercises copied expansion/handle data, default/input,
output, and semi-output roles, stable locally nameless declared types,
class-evidence receivers, full-telescope parameter references, ordered
multiple parents, reversed named parent arguments, canonical plicity, caller
immutability, deep freeze, JSON round trips, and all ten frozen diagnostic
classes.

Exact validation:

- `node --require ts-node/register --test
  tests/v3_2_lf_class_schema_tests.ts`: 6/6 passed;
- `./scripts/pnpmw run workspace:check`: passed;
- `./scripts/pnpmw run typecheck`: passed;
- changed-file ESLint for the module, public barrel, focused suite, and root
  test runner: passed;
- `git diff --check`: passed; and
- the one required shared-boundary `./scripts/pnpmw run check:ts`: 1,526 tests
  across 229 suites, 1,472 passed, 54 intentionally skipped, zero failures,
  exit code 0. It took approximately 25.9 minutes and must be carried forward
  rather than rerun for unchanged boundaries.

No structure declaration/rule output, dictionary resolver, Core/checker
branch, parser, browser entry, package boundary, Lambdapi fragment,
`emdash2/` source, active kernel owner, or sibling repository changed. No
Lambdapi or active-kernel aggregate was therefore relevant. The proposal
backtracking checkpoint is `388535a`; the rollback-safe implementation
checkpoint is the local commit with message
`elaborator: add class schema metadata`.

The next dependency-ready row is `CLASS-INHERIT-4`. It begins with a
read-only audit of the schema metadata, structure lowering seam, Lean's strict
C3/parent representation behavior, and the algebraic diamond. The next
proposal must decide the private flattened layout, explicit field-sharing
proof obligation, parent-conversion terms, and canonical ancestor criterion
before adding behavior. It must not begin instance registry/search or general
call elaboration.

## CLASS-INHERIT-4 Audit And Repartition

The 2026-08-08 audit inspected the completed schema boundary, the structure
macro's generated constructor/projection telescopes, and Lean's
`StructFieldKind`, copied-parent coercions, and C3 implementation. The useful
comparison is semantic rather than representational:

- Lean may embed a parent subobject when fields do not overlap and otherwise
  copies/reuses fields, while recording parent projections separately;
- Lean's C3 order is a management cache used for resolution/defaults, not a
  kernel constructor;
- Lean currently identifies repeated inherited fields primarily by field
  name and then checks definitional equality; emdash keeps the stronger plan
  decision that stable declaring-class identities come first and spelling
  alone never authorizes sharing; and
- a copied-parent projection is ultimately an ordinary function rebuilding
  the parent from child fields, which maps directly to explicit transfer IR
  and the existing checker.

The completed `CLASS-SCHEMA-3` representation deliberately classifies an
already generated child structure. Its `declaredMethods` are therefore the
physical constructor/projection slots available for a first flattened
layout. Replacing that structure under the same symbols would be unsound and
would discard a reviewed checkpoint. The selected first inheritance path is
instead:

```text
parent schemas + parent layouts
              |
      strict C3 + identity union
              |
explicit inherited identities -> existing child physical slots
              |
  finite identity-layout plan (4A)
              |
ordinary parent-conversion terms checked by LF (4B)
```

For this first path, an author declares the child's private flattened storage
fields explicitly with the existing structure macro and assigns inherited
identities to those slots. Named construction means source does not depend on
their positional order. A later ergonomic class builder may synthesize the
same private storage declaration, but no such callback/parser facade is part
of `CLASS-INHERIT-4`.

The audit partitions the row so each checkpoint has one claim:

- `CLASS-INHERIT-4A` computes and validates identity/layout metadata only;
- `CLASS-INHERIT-4B` generates direct-parent conversion types and terms,
  submits representative declarations to the ordinary LF compiler/checker,
  and qualifies the algebraic diamond.

Neither subrow creates a Core class/record node, instance registry, search
engine, or declaration parser.

## CLASS-INHERIT-4A Frozen Contract

The selected additive module is `src/v3_2/lf_class_inheritance.ts`, initially
kept off the public barrel/root runner until `4B` completes. Its principal
shape is:

```ts
planCoreLfClassInheritance({
  schema: monoidSchema,
  directParentLayouts: [semigroupLayout, mulOneLayout],
  fieldBindings: [
    {
      field: monoidSchema.declaredMethods[0].projection,
      inherited: [mulLayout.slots[0].canonicalIdentity],
    },
  ],
})
```

Its exact contract is:

1. A parent-free schema is bootstrapped with no parent layouts/bindings. A
   parentful schema requires exactly one previously planned layout for every
   direct parent, in the schema's source-significant parent order.
2. Parent layouts are matched structurally by stable class ID and parameter
   count, never JavaScript identity. Each parent resolution order must begin
   with that parent and contain no duplicate class ID.
3. The child resolution order is strict C3:
   `[child] ++ merge(L(parent_1), ..., L(parent_n), [parent_1,...,parent_n])`.
   There is no relaxed fallback. An inconsistent hierarchy fails with stable
   conflicting-head/tail evidence.
4. Every parent slot contributes its complete field-identity equivalence
   class. Classes that overlap on any stable identity are unioned, so a
   repeated ancestor in a diamond is one inherited obligation before any
   child binding is considered.
5. `fieldBindings` is a sparse, order-independent array keyed by the child's
   structural projection handles. Every unmentioned child field remains a
   local-only physical slot.
6. A binding's `inherited` entries may name any member of an inherited
   equivalence class. Naming one assigns the whole class. The same inherited
   class cannot be assigned twice, and every inherited class must be assigned
   exactly once.
7. Assigning several otherwise distinct inherited classes to one child field
   is the explicit `share`/`identify` operation. Merely repeating a binder
   spelling performs no union. Type compatibility is intentionally not
   claimed by `4A`; `4B` validates it when all generated parent conversions
   pass the ordinary dependent LF checker.
8. Every output slot contains its child physical projection, the child's
   local alias identity, every inherited identity in the assigned union, and
   one deterministic canonical identity. A slot with inherited members picks
   the lexicographically least inherited canonical representative, excluding
   the new child alias; a local-only slot uses its child identity. Adding a
   subclass therefore cannot rename an ancestor's canonical field.
9. The output carries all qualified `(declaring class, binder name)` aliases.
   An unqualified spelling is accepted only when every occurrence maps to the
   same physical slot after explicit sharing; otherwise planning fails with a
   name conflict. C3 selects the recorded provenance among aliases that do
   share a slot and remains available for later default lookup.
10. The result has profile revision
    `emdash-lf-class-inheritance-layout-v1`, status
    `identity-layout-planned`, the finite class-schema snapshot, direct-parent
    references, strict resolution order, physical slots, qualified aliases,
    and deterministic unqualified lookup. It embeds no parent layout, callback,
    checker, or process state and is deeply frozen/JSON-serializable.
11. `identity-layout-planned` is not superclass evidence. Only `4B` may add
    parent conversion plans and mark the algebraic layout usable by later
    provider/search rows.

The frozen error classes are `INVALID_INHERITANCE_LAYOUT`,
`PARENT_LAYOUT_MISMATCH`, `INCONSISTENT_C3`, `FOREIGN_FIELD`,
`DUPLICATE_FIELD_BINDING`, `FOREIGN_INHERITED_IDENTITY`,
`DUPLICATE_INHERITED_IDENTITY`, `MISSING_INHERITED_IDENTITY`, and
`FIELD_NAME_CONFLICT`, with paths distinguishing schemas, parent layout
ordinals, physical fields, and inherited identity entries.

The focused `4A` corpus will cover parent-free bootstrapping, copied/JSON
layouts, field-binding permutation determinism, the `Mul`/`One`/
`Semigroup`/`MulOneClass`/`Monoid` diamond, the exact strict C3 order, one
shared `Mul` identity class/slot, explicit unrelated-field sharing,
conflict-free qualified/unqualified lookup, caller immutability/deep freeze,
and every frozen failure family including a classic inconsistent-C3 graph.

The proposal gate `H-TS-EMDASH-CLASSES-INHERIT-4A-003` is approved under the
user-authorized unattended-review delegation, with immediate human
supersession. The documentation-only checkpoint is the backtracking boundary.
`4A` uses focused tests, typecheck, changed-file lint, and diff hygiene; it
does not enter the public barrel/root runner and therefore carries forward
the 1,526-test aggregate without another long run. `4B` will audit/freeze its
term contract after `4A` is stable and will own the single aggregate for the
complete public inheritance boundary.

## CLASS-INHERIT-4A Completion Record

`CLASS-INHERIT-4A` is final-green on 2026-08-08. The implementation adds the
isolated `lf_class_inheritance` planning module and:

- validates parent-free bootstraps and exact, structurally copied direct-parent
  layout snapshots without relying on JavaScript object identity;
- computes the strict C3 resolution order with no relaxed fallback and reports
  stable conflicting-head/tail evidence for an inconsistent hierarchy;
- unions complete inherited field-identity equivalence classes before child
  binding, so a repeated ancestor in a diamond creates one obligation;
- assigns every inherited identity class exactly once to an existing private
  physical projection while leaving unmentioned child fields local-only;
- permits unrelated inherited classes to share storage only through an
  explicit multi-identity field binding, never by repeated spelling;
- preserves ancestor canonical representatives when a subclass introduces a
  new local alias;
- emits complete qualified aliases and accepts an unqualified spelling only
  when all occurrences resolve to the same physical slot;
- returns a finite, caller-independent, deeply frozen, JSON-serializable
  `identity-layout-planned` snapshot; and
- adds no declaration, term, rule, search state, process state, or hidden
  conversion claim.

The focused algebraic corpus exercises the exact
`MonoidClass -> (SemigroupClass, MulOneClass)` diamond, obtains resolution
order `[MonoidClass, SemigroupClass, MulOneClass, MulClass, OneClass]`, and
proves at the metadata boundary that the repeated `MulClass` ancestor has one
canonical identity and one physical slot. It also covers parent-free layout,
copied JSON layouts, input permutation/caller immutability, explicit sharing
of unrelated same-named fields, same-name conflict without sharing, every
frozen validation family, and a classic inconsistent-C3 graph.

Exact validation:

- `node --require ts-node/register --test
  tests/v3_2_lf_class_inheritance_tests.ts`: 6/6 passed;
- `./scripts/pnpmw run typecheck`: passed;
- changed-file ESLint: passed;
- diff hygiene: passed; and
- the one required shared-boundary `./scripts/pnpmw run check:ts`: 1,532 tests
  across 230 suites, 1,478 passed, 54 intentionally skipped, zero failures,
  exit code 0, in `1,377,221.819576 ms` (approximately 22m57s). Its
  workspace, typecheck, and full-lint stages also passed.

The frozen proposal initially planned to keep this isolated module outside
the root runner and carry forward the preceding aggregate. Root repository
guidance instead requires every behavioral `src/` test to be registered in
`tests/main_tests.ts` and every changed shared TypeScript boundary to pass one
complete `check:ts`. The implementation follows that stronger governing rule;
the module remains absent from the public v3.2 barrel until `4B` can expose a
usable conversion boundary.

No parent-conversion term, structure declaration/rule, Core/checker branch,
instance registry/search, parser, browser entry, package boundary, Lambdapi
fragment, `emdash2/` source, active kernel owner, or sibling repository
changed. No Lambdapi or active-kernel aggregate was therefore relevant. The
proposal backtracking checkpoint is `38f39cb`; the rollback-safe
implementation checkpoint is `9764657`
(`elaborator: plan class inheritance identities`).

The next dependency-ready row is `CLASS-INHERIT-4B`. It begins with a
read-only audit and frozen proposal for direct-parent conversion types and
terms, including dependent parameter substitution, reconstruction from the
planned physical slots, ordinary LF checking, and the exact canonical
diamond criterion. It must not begin provider scopes, recursive instance
search, or general implicit-call elaboration.

## CLASS-INHERIT-4B Audit And Frozen Contract

The 2026-08-08 read-only audit inspected the completed structure expansion,
named construction, class-schema and identity-layout boundaries, the existing
mixed-phase LF compiler/checker and combined converter, and Lean's copied
parent projections. The useful conclusions are:

- an emdash parent conversion should be an ordinary transparent definition,
  not a structure field, Core constructor, runtime rule, unification hook, or
  privileged coercion;
- the child class parameter telescope uses each parameter's existing
  projection mode, while the final child-evidence receiver remains an
  ordinary explicit Core binder carrying authoring-level `class-evidence`
  metadata;
- the parent carrier application stored by `CLASS-SCHEMA-3` is already the
  exact result type open under the complete child parameter telescope;
- each parent physical field can be recovered by locating any identity in
  its parent-layout slot inside the child's 4A slot and applying that child's
  existing physical projection to the evidence;
- applying the parent's existing named constructor to its substituted
  parameters and recovered fields makes the ordinary LF checker the sole
  authority for dependent-field compatibility and explicit 4A sharing;
- transparent conversion bodies plus the existing structure projection-beta
  runtime rules are sufficient to compare two diamond paths; and
- generating only direct edges preserves a small declaration surface.
  Transitive evidence is explicit composition of those handles. Later
  synthesis may select one canonical C3 path per ancestor, while 4B checks
  that the nonselected algebraic route computes to the same evidence.

This follows the semantic content of Lean's auxiliary copied-parent
projections without copying Lean's inductive/structure environment machinery.
Lean emits a reducible definition which reconstructs a non-subobject parent;
emdash emits the corresponding backend-neutral transfer declaration and
checks it in the small TypeScript LF.

The selected additive module is
`src/v3_2/lf_class_inheritance_lowering.ts`. Its principal shape is:

```ts
const monoidInheritance = lowerCoreLfClassInheritance({
  layout: monoidLayout,
  order: monoidExpansion.nextOrder,
  directParents: [
    { layout: mulOneLayout, conversionName: 'monoid_to_mul_one' },
    { layout: semigroupLayout, conversionName: 'monoid_to_semigroup' },
  ],
  provenance,
})

const semigroupEvidence = applyCoreLfClassParentConversion({
  conversion: monoidInheritance.directParentConversions[0],
  parameters: [{
    parameter: monoidSchema.structure.parameters[0],
    value: alpha,
  }],
  evidence: monoidEvidence,
})
```

The exact contract is:

1. `lowerCoreLfClassInheritance(...)` accepts one complete 4A child layout,
   a first source order, source provenance, and one named parent-layout entry
   for every direct parent. Entries are keyed structurally by parent class ID
   and may arrive in any order; output is canonicalized to the schema's
   source-significant direct-parent order.
2. A parent-free layout accepts no entries and expands to no declarations.
   A parentful layout requires each direct parent exactly once. Each supplied
   parent layout must match the direct-parent class ID and parameter count and
   must expose every identity needed by that parent constructor.
3. Each conversion symbol is placed in the child's module under its explicit
   caller-supplied `conversionName`. Names must be valid and pairwise distinct
   and may not collide with the child's carrier, constructor, or physical
   projection symbols. The ordinary module planner remains responsible for
   collisions with other surrounding declarations.
4. For a child with parameters `p_1 ... p_n` and direct-parent application
   `P(args)`, the generated conversion type is exactly
   `Π p_1 ... p_n, Π (self : Child(p_1,...,p_n)), P(args)`. Parameter binders
   use their structure projection modes. The `self` binder is explicit and
   functorial, matching existing structure projection Core rather than adding
   a third trusted plicity.
5. Locally nameless parent arguments are shifted once beneath `self`. The
   conversion body is the corresponding sequence of lambdas followed by the
   existing parent constructor. Constructor parameter plicities come from the
   parent structure handle, not from caller array position.
6. For every parent-layout physical slot, lowering finds the unique child
   physical slot containing that inherited identity class and supplies the
   child projection applied to all child parameters and `self`. It never
   matches by field spelling. A missing or multiply mapped identity fails
   before a declaration is returned.
7. Parent construction is named-handle-directed and canonical. Consequently
   dependent parent fields and explicitly shared but differently declared
   fields are accepted only if the unchanged LF compiler/checker verifies the
   generated constructor application.
8. Every generated declaration is public, ordinary, transparent, carries an
   explicit transfer term, and is intended for the existing
   `checked-transparent-definition` policy. Lowering emits no runtime or proof
   rule. Existing structure projection-beta rules remain the only new-term
   computation used by the acceptance corpus.
9. Each direct-parent handle records its ordinal, child and parent references,
   symbol/global term, exact generated type, and the explicit class-evidence
   receiver contract. `applyCoreLfClassParentConversion(...)` accepts complete
   order-independent named child-parameter assignments plus one evidence term
   and returns the ordinary fully explicit call. The helper assembles only;
   the LF checker remains responsible for argument types.
10. The expansion has profile revision
    `emdash-lf-class-inheritance-lowering-v1`, status
    `parent-conversions-expanded`, canonical consecutive source orders,
    declarations, handles, and `nextOrder`. It is finite, caller-independent,
    deeply frozen, and JSON-serializable.
11. A lowering expansion is source IR, not a hidden certificate. It becomes
    usable superclass evidence only in an exact module whose structure
    declarations, structure runtime betas, and transparent conversion bodies
    all pass the ordinary TypeScript LF pipeline.
12. No dedicated direct-to-transitive-ancestor declaration is generated in
    4B. A transitive path is an explicit composition of direct handles. This
    prevents redundant global providers; `SYNTH-SCOPE-5` and
    `SYNTH-RECURSE-6` will separately freeze canonical provider registration
    and C3-path selection.

The canonical algebraic criterion is computational and exact. With an open
`m : MonoidClass A`, the focused test constructs:

```text
semigroup_to_mul A (monoid_to_semigroup A m)
mul_one_to_mul A (monoid_to_mul_one A m)
```

Both terms must check at `MulClass A` and normalize, using only transparent
delta, ordinary beta, and the generated structure projection betas, to the
same `MkMulClass A (monoid_mul A m)` Core expression. This witnesses diamond
sharing without proof irrelevance, an equality axiom, a special coherence
rule, or resolver heuristics.

The frozen lowering error classes are `INVALID_INHERITANCE_LOWERING`,
`LAYOUT_MISMATCH`, `PARENT_LAYOUT_MISMATCH`,
`INVALID_PARENT_CONVERSION`, `DUPLICATE_PARENT_CONVERSION`,
`MISSING_PARENT_CONVERSION`, `DUPLICATE_SYMBOL`,
`UNMAPPED_PARENT_FIELD`, `INVALID_APPLICATION`, `FOREIGN_ARGUMENT`,
`DUPLICATE_ARGUMENT`, and `MISSING_ARGUMENT`. Paths distinguish child layout,
direct-parent entry, conversion name, parent slot, named parameter, and
evidence term.

The focused corpus will cover parent-free expansion, input-order-independent
direct-parent declarations, exact parameter shifting and plicities,
copied/JSON layouts, caller immutability/deep freeze, named conversion
application, ordinary LF checking of every generated body, the exact five
direct edges of the algebraic diamond, byte-identical normalization of its
two `MulClass` routes, a definitionally compatible explicit share, rejection
of an incompatible share by the ordinary LF checker, and every frozen
lowering/application failure family.

The proposal gate `H-TS-EMDASH-CLASSES-INHERIT-4B-004` is approved under the
user-authorized unattended-review delegation, with immediate human
supersession. The documentation-only proposal checkpoint is the backtracking
boundary. Implementation first remains an isolated direct-import module and
focused suite. Root guidance requires the behavioral suite in
`tests/main_tests.ts`; once the bounded surface, public v3.2 barrel, focused
tests, typecheck, and changed-file lint are green, 4B owns exactly one final
`check:ts`. No repeated aggregate and no Lambdapi/kernel check are planned,
because the row depends only on the already-qualified TypeScript LF names and
computation.

The proposed checkpoint message is
`docs: freeze class inheritance lowering contract`. The implementation
checkpoint message is `elaborator: lower class parent conversions`.

## CLASS-INHERIT-4B Completion Record

`CLASS-INHERIT-4B` is final-green on 2026-08-08. The implementation adds the
public `lf_class_inheritance_lowering` module and:

- exposes one frozen-copy validator for completed 4A layouts so later phases
  accept structurally replayed JSON rather than JavaScript object identity;
- canonicalizes complete, order-independent direct-parent inputs back to the
  class schema's source-significant parent order;
- emits one public ordinary transparent definition per direct parent, with no
  runtime rule, proof rule, Core node, or privileged coercion;
- preserves the complete child parameter telescope and each parameter's
  projection mode, shifts parent applications exactly beneath the explicit
  `class-evidence` receiver, and records the exact generated type;
- reconstructs each parent through its existing named constructor, sourcing
  fields solely through stable inherited identities and the child's existing
  physical projections;
- leaves dependent field compatibility and explicit sharing entirely to the
  unchanged LF compiler/checker;
- exposes finite direct-parent handles and an order-independent named
  application helper which returns one ordinary fully explicit call; and
- returns caller-independent, deeply frozen, JSON-serializable
  `parent-conversions-expanded` source IR.

The focused suite contains eight executable tests. It covers parent-free
expansion, canonical direct-parent order, exact one- and two-parameter de
Bruijn shifts, mixed implicit/explicit projection modes, reversed named
parameter assignments, copied layouts/handles, caller immutability, deep
freeze, every frozen lowering/application diagnostic family, and ordinary LF
checking of generated bodies. A real explicit-share fixture succeeds when
both unrelated parent fields have type `Code` and is rejected by the ordinary
checker when the second expects `El A`.

The algebraic acceptance module contains exactly five direct edges:

```text
SemigroupClass -> MulClass
MulOneClass    -> MulClass
MulOneClass    -> OneClass
MonoidClass    -> SemigroupClass
MonoidClass    -> MulOneClass
```

With `m : MonoidClass A`, both explicit transitive terms
`semigroup_to_mul A (monoid_to_semigroup A m)` and
`mul_one_to_mul A (monoid_to_mul_one A m)` check at `MulClass A`. Under the
existing combined converter they both normalize, using only transparent
delta, ordinary beta, and structure projection betas, to the same
`MkMulClass A (monoid_mul A m)` Core expression. No proof irrelevance,
coherence axiom, resolver heuristic, or dedicated transitive declaration is
used.

Exact validation:

- `node --require ts-node/register --test
  tests/v3_2_lf_class_inheritance_lowering_tests.ts`: 8/8 passed;
- the preceding combined 4A/initial-4B focused pass was green, and the final
  4B suite subsumes its lowering coverage;
- `./scripts/pnpmw run workspace:check`: passed;
- `./scripts/pnpmw run typecheck`: passed;
- changed-file ESLint: passed;
- `git diff --check`: passed; and
- the required completed shared-boundary
  `./scripts/pnpmw run check:ts`: 1,540 tests across 231 suites, 1,486 passed,
  54 intentionally skipped, zero failures, exit code 0, in
  `1,869,668.695485 ms` (approximately 31m10s). Its workspace, typecheck, and
  full-lint stages also passed.

An initial interactive aggregate invocation passed workspace, typecheck, and
lint and entered buffered test execution, but an automatic goal continuation
terminated its tool process before any footer or exit status existed. It is
not treated as validation evidence. The one completed replacement was run
detached with a durable external log and status marker; no post-green
aggregate was or should be repeated for documentation synchronization.

The public v3.2 barrel now exports both the identity-layout and lowering
modules, and the root runner registers the focused lowering suite. The browser
surface remains unchanged. No provider registry, scope snapshot, recursive
search, call-site synthesis, parser, class/Core node, package boundary,
Lambdapi fragment, `emdash2/` source, active kernel owner, or sibling
repository changed. No Lambdapi or active-kernel gate was relevant. The
proposal backtracking checkpoint is `27f22d2`; the rollback-safe
implementation checkpoint is the local commit with message
`elaborator: lower class parent conversions`.

The next row is `SYNTH-SCOPE-5`. Its completed read-only audit and frozen
proposal below decide stable provider identity, exact class-head
representation, precedence, shadowing versus ambiguity, import provenance,
superclass-provider metadata, and serialization. Its implementation must not
begin recursive search, metavariable scheduling, general call elaboration, or
hidden process-global registration.

## SYNTH-SCOPE-5 Audit And Frozen Contract

The 2026-08-08 read-only audit inspected the final-green global dictionary
selector and leading-implicit authoring adapter, the declaration and fragment
workspace identity/snapshot machinery, completed class layouts and direct
parent conversions, and the relevant local Lean 4 implementation sources
(`Lean.Meta.Instances`, `Lean.ScopedEnvExtension`, local-instance context
management, and instance candidate collection). The selected design retains
the useful behavioral distinctions without importing Lean's environment
extension, parser, recency, or mutable metacontext architecture:

- the existing dictionary selector remains a deliberately small compatibility
  primitive over one caller-supplied list; it is not renamed into or silently
  used as recursive typeclass search;
- a provider is derived from an exact checked global declaration or an exact
  checked local binder, so registration cannot invent the provider type,
  result head, Core name, or evidence term;
- provider telescopes retain source order and explicitly classify ordinary
  binders versus later-synthesized class premises, but no premise is solved in
  this row;
- class applications record stable class identity, the checked Core head,
  parameter roles and plicities, and exact Core arguments. This makes the
  future all-input index portable without adding a class node to Core;
- direct superclass conversions are ordinary global providers with one
  explicitly classified child-evidence premise. Only the five direct edges of
  the accepted algebraic hierarchy are registered; transitive evidence still
  composes direct providers;
- local evidence is an explicit locally nameless Core reference checked in a
  supplied immutable `CoreContext`, never a name lookup or process-global
  registration;
- scopes are immutable snapshots over one immutable registry. They contain
  explicit lexical frames, opened named-scope IDs, exact imported-interface
  pins, and the current module ID; and
- canonical JSON is the fingerprint material. This browser-safe row computes
  no cryptographic digest and trusts no claimed hash beyond preserving and
  validating its portable spelling.

This is also the repeated real consumer required by the earlier
`AI-SYNTH-1B2` gate: the first consumer selected one structure capability,
while this row must represent ordinary class instances, a local class
dictionary, and generated superclass providers for the five-edge algebraic
hierarchy. It therefore graduates reusable scopes without changing canonical
workspace schemas or weakening the existing call-site-explicit helper.

The selected additive module is `src/v3_2/lf_instance_scope.ts`. Its exact
contract is:

1. `declareCoreLfGlobalInstanceProvider(...)` accepts one compiled declaration
   base, its exact `CoreLfModuleSpec`, one installed ordinary free declaration,
   one completed result-class layout, zero or more binder-ordinal/class-layout
   premise annotations, an optional nonnegative safe-integer priority, and
   either global or one qualified named-scope visibility. Provider identity is
   the declaration's exact qualified symbol; aliases cannot register the same
   declaration under a second identity.
2. Registration checks the global reference against its already compiled type
   with a fresh TypeScript LF checker, decomposes the complete Pi telescope,
   and validates the unreduced final target as an exact application of the
   supplied completed class layout. Each premise annotation must identify one
   Pi binder whose exact checked type is an application of its supplied class
   layout. All unannotated binders are ordinary parameters. Duplicate,
   out-of-range, or non-class premise annotations fail closed.
3. `declareCoreLfLocalInstanceProvider(...)` accepts the same declaration base,
   an exact `CoreContext` over that environment, module identity, a stable
   qualified provider ID, one bound-variable index, a stable lexical-frame ID,
   and result/premise class layouts. It derives both evidence and type from
   `context.lookupIndex`, checks them, and records the current ambient depth.
   Local evidence is never exportable and must later appear in its declared
   frame at exactly that resolution depth.
4. `declareCoreLfSuperclassInstanceProvider(...)` accepts one completed direct
   conversion handle plus matching child and parent layouts. It delegates to
   checked global registration, classifies the conversion's final child-
   evidence binder as the only instance premise, and records a
   `superclass-conversion` origin containing the exact direct child, parent,
   ordinal, symbol, and Core name. It rejects a transitive or mismatched
   synthetic handle.
5. Every provider snapshot has profile revision
   `emdash-lf-instance-provider-v1`, stable provider ID, exact module/fragment
   provenance, nonnegative priority (default `1000`), visibility, ambient
   depth, checked provider term and type, ordered classified telescope, exact
   result class application, and a discriminated ordinary-global,
   local-bound, or superclass source. It contains no function, callback,
   checker, declaration context, environment, unresolved metavariable, or
   search request.
6. A class application contains the stable `CoreLfClassReference`, checked
   free Core head name, complete exact type, and one ordered argument entry per
   class parameter. Each entry records ordinal, input/output/semi-output role,
   Core plicity, and exact argument. Parameter roles are data only in this row;
   output and semi-output scheduling remains `PARAM-ROLES-10`.
7. `createCoreLfInstanceRegistrySnapshot(...)` accepts a caller revision and a
   finite array of provider snapshots, revalidates replayed/JSON data, rejects
   duplicate provider IDs, canonicalizes providers by qualified ID, and
   returns a detached deeply frozen registry. It does not enumerate a
   declaration environment, class layout, module graph, filesystem, or host
   registry.
8. `createCoreLfInstanceScopeSnapshot(...)` accepts the registry, a caller
   revision, current module ID, resolution-context depth, ordered outer-to-
   inner local/section frames, an order-insensitive set of opened qualified
   named scopes, and order-insensitive pinned imports. Each import explicitly
   records module ID, interface revision, `sha256:` interface pin, and the
   complete available provider-ID list. Import order and provider-list order
   are canonicalized; no provider is inferred from workspace externals,
   dependency declarations, or an environment scan.
9. A provider is eligible in exactly one activation class: a declared local
   provider in its exact frame; a named provider from the current module or an
   explicitly pinned import when its exact scope is opened; a current-module
   global; or a pinned imported global. Unknown, repeated, wrong-module,
   local-in-import, wrong-frame, wrong-depth, unopened, or otherwise
   ineligible references fail closed. Registry entries not activated by the
   snapshot remain inert.
10. Candidate precedence is frozen as explicit ranks, not implied array
    order. Inner lexical frames precede outer frames; each lexical frame is a
    separate rank. All opened named scopes share the next rank. Current and
    imported globals share the final ambient rank. Within one rank, higher
    provider priority sorts first; equal-priority provider IDs sort only for
    stable diagnostics. Distinct equal-ranked providers are retained, never
    shadowed by ID or declaration recency. `SYNTH-RECURSE-6` will test actual
    success and ambiguity.
11. Local-frame order is semantically significant and preserved. Provider
    arrays, opened named scopes, imports, and import provider lists are
    semantically unordered and canonicalized. Reversing those inputs must
    produce byte-identical registry/scope serialization; reversing nested
    local frames must deliberately change ranks.
12. `serializeCoreLfInstanceRegistrySnapshot(...)` and
    `serializeCoreLfInstanceScopeSnapshot(...)` reuse the qualified browser-
    safe canonical workspace JSON encoder. The scope records the exact
    registry revision and provider-ID inventory so the future resolver can
    reject a mismatched registry. The serialized registry plus scope are the
    future table-key fingerprint material; no collision-prone ad hoc hash is
    introduced.
13. This module performs no goal matching, candidate selection, recursive
    premise resolution, unification/metavariable assignment, cycle detection,
    fuel accounting, ambiguity decision, call elaboration, or Core checking of
    a newly assembled application. Those all remain `SYNTH-RECURSE-6` or
    `CALL-SYNTH-7`.

The frozen provider/scope error families are `INVALID_PROVIDER`,
`UNAVAILABLE_PROVIDER`, `UNSUPPORTED_PROVIDER`, `INVALID_PROVIDER_TYPE`,
`INVALID_CLASS_HEAD`, `INVALID_PREMISE`, `DUPLICATE_PREMISE`,
`INVALID_SUPERCLASS_PROVIDER`, `INVALID_REGISTRY`, `DUPLICATE_PROVIDER`,
`INVALID_SCOPE`, `UNKNOWN_PROVIDER`, `INVALID_LOCAL_FRAME`,
`DUPLICATE_LOCAL_FRAME`, `INVALID_NAMED_SCOPE`, `DUPLICATE_NAMED_SCOPE`,
`INVALID_IMPORT`, `DUPLICATE_IMPORT`, `INELIGIBLE_PROVIDER`, and
`NON_PORTABLE_DATA`. Structured paths distinguish the provider declaration,
Pi binder, class argument, registry entry, local frame, named opening, import,
and derived candidate.

The focused corpus will cover checked opaque and transparent global
providers, a checked local binder, generic ordinary parameters, one explicit
instance premise, exact input/output/semi-output role retention, all five
direct algebraic superclass providers, replay from JSON, input immutability
and deep freeze, canonical provider/import/named permutations, significant
lexical-frame nesting, the exact local/named/imported/global rank matrix,
equal-ranked retention, canonical serialization, and every frozen failure
family. It will explicitly show that no synthesis result or selected evidence
is produced.

The proposal gate `H-TS-EMDASH-CLASSES-SYNTH-SCOPE-5-005` is approved under
the user-authorized unattended-review delegation, with immediate human
supersession. The documentation-only proposal checkpoint is the backtracking
boundary. Implementation begins as a direct-import module and focused suite,
then enters the public v3.2 barrel and root runner only with its final bounded
surface. Workspace check, focused tests, TypeScript typecheck, changed-file
lint, canonical diff hygiene, and one final `check:ts` are required because
the public barrel and runner are shared boundaries. The final aggregate must
not be repeated for unchanged documentation, and no Lambdapi/kernel check is
planned because this row derives only already-checked TypeScript Core names
and types.

The proposed checkpoint message is
`docs: freeze instance provider scope contract`. The implementation checkpoint
message is `elaborator: add immutable instance scopes`.

## SYNTH-SCOPE-5 Implementation And Qualification Record

Implementation and final qualification are complete on 2026-08-09. The
additive public module `src/v3_2/lf_instance_scope.ts` now:

- derives ordinary global providers from exact installed declarations and
  checks their references against the compiled type with a fresh LF checker;
- derives local providers from exact `CoreContext` bound-variable lookups at a
  recorded ambient depth and rechecks the evidence against its derived type;
- decomposes complete Pi telescopes, classifies explicit premise annotations,
  rejects Core metavariables, and records exact unreduced class heads,
  parameter roles, plicities, and arguments;
- turns each completed direct-parent conversion into an ordinary superclass
  provider with exactly one child-evidence premise, while retaining direct
  child/parent/ordinal provenance;
- revalidates JSON-replayed provider data into a canonical deeply frozen
  registry ordered only by stable qualified provider ID;
- builds immutable scopes from source-significant outer-to-inner lexical
  frames plus order-insensitive named openings and exact imported-interface
  pins, activating no provider outside those explicit inputs;
- ranks inner lexical frames before outer frames, opened named scopes next,
  and imported/current globals together last, sorting priority then stable ID
  inside a rank without selecting or discarding equal-ranked evidence; and
- serializes registry and scope artifacts through the existing browser-safe
  canonical workspace JSON encoder without hashing, I/O, callbacks, or hidden
  process state.

The v3.2 barrel exports the module, the root runner registers its focused
suite, and the source-visible AI-native capability record now reports
`instance-provider-scope@emdash-lf-instance-scope-v1`. The earlier
AI-SYNTH-1B2 row is correspondingly partitioned: artifact-only 1B2A is this
result, while canonical-workspace persistence remains 1B2B and recursive
resolution remains AI-SYNTH-2/SYNTH-RECURSE-6.

Qualification records:

- the dedicated provider/scope suite: 6/6 passed;
- the combined class schema, identity layout, parent lowering, provider/scope,
  and AI-native capability matrix: 41 tests across seven suites, all passed;
- `./scripts/pnpmw run workspace:check`: passed;
- `./scripts/pnpmw run typecheck`: passed;
- changed-file ESLint: passed;
- direct capability text rendering and the browser-safety/forbidden-effect
  scan: passed; and
- `git diff --check`: passed.

The one required `./scripts/pnpmw run check:ts` passed against the unchanged
final TypeScript boundary: workspace validation, full typecheck, full ESLint,
and 1,546 tests across 232 suites completed with 1,492 active passes, 54
intentional skips, and zero failures. The directly observed root-test duration
was 2,939,372.205378 ms. Its durable log and exit markers are
`/tmp/emdash-classes-v1-check-ts-scope5-run1.{log,status}`. No second aggregate
was run for documentation synchronization. `SYNTH-RECURSE-6` is now
dependency-ready and begins with a read-only audit and frozen proposal, not
recursive implementation by analogy.

No parser, transfer-expression variant, Core/checker branch, runtime/proof
rule, recursive resolver, metavariable scheduler, synthesis result, call-site
elaborator, workspace schema, package boundary, browser command, Lambdapi
fragment, `emdash2/` source, active kernel owner, or sibling repository
changed. No Lambdapi or active-kernel gate is relevant. The immutable proposal
checkpoint is `1a6d591`; the qualified implementation checkpoint uses the
frozen message `elaborator: add immutable instance scopes`.

## SYNTH-RECURSE-6 Audit And Frozen Contract

The read-only audit began from qualified scope checkpoint `e8d38be` on
2026-08-09. It compared the completed provider/scope artifacts with the
existing finite selector in `lf_dictionary_synthesis.ts`, contextual
metavariables and transactions in `session.ts`, the public
`CoreChecker.checkRefinement(...)` boundary used by proof application, the
combined LF normalization/comparison engine, and Lean's local
`Meta/SynthInstance.lean` and `Meta/Instances.lean` implementations.

Lean confirms the useful architectural shape: index by class head, instantiate
one provider telescope with fresh metavariables, unify its result with the
goal, recursively discharge instance binders, table normalized goals, and use
explicit resource bounds. Emdash deliberately does not copy Lean's mutable
environment extension, heartbeat counter, continuation/waiter scheduler,
metavariable-bearing root goals, output-parameter heuristics, or
"morally canonical" first-answer optimization. The first emdash resolver has
ground goals and immutable inputs, so a deterministic depth-first table is
sufficient, and distinct evidence remains ambiguous unless checked
definitionally equal.

The selected additive implementation module is
`src/v3_2/lf_instance_synthesis.ts`. Its exact contract is:

1. `synthesizeCoreLfInstance(...)` accepts one checked mixed-declaration base,
   an exact `CoreContext` over that base, an optional exact reviewed catalog
   runtime used by ordinary LF conversion, one completed target-class layout,
   one target Core type, one immutable provider registry, its exact immutable
   scope snapshot, and optional explicit limits. There is no environment
   enumeration, process registry, search callback, filesystem read, network
   request, parser case, workspace mutation, or Lambdapi execution.
2. The resolver reconstructs the registry and scope through their public
   validators and requires byte-identical canonical serialization, exact
   registry revision/provider inventory, and `scope.contextDepth ===
   context.depth`. It rejects a context from another Core declaration
   environment. Every activated provider term is rechecked against its stored
   type in that exact context before search; local evidence therefore cannot
   be replayed merely because another context has the same depth.
3. The root target is checked as a meta-free type in the supplied context.
   Its completed layout supplies the stable class identity, parameter count,
   roles, and expected carrier declaration. Recursive goals use the already
   checked premise-class metadata. Every goal must have the exact installed
   free Core head linked to its stable class ID and the exact parameter count
   and plicities. A transparent alias is not silently treated as a second
   class identity.
4. This is the all-arguments-ground profile. Input, output, and semi-output
   role labels remain in goal/provider evidence, but every goal argument must
   already be meta-free. The resolver assigns no caller metavariable and does
   not interpret output or semi-output scheduling; that remains
   `PARAM-ROLES-10`.
5. Scope candidates are indexed only by the exact stable result-class
   reference and checked Core head. The existing scope order remains
   authoritative: ascending lexical/named/ambient rank, then descending
   numeric priority, then stable provider ID for deterministic traversal and
   diagnostics. Provider ID never resolves an ambiguity.
6. Each candidate attempt gets a fresh `CoreLfChecker` and session with the
   requested comparison limit and exact supplied catalog runtime. The resolver
   creates one contextual meta for every provider Pi binder, builds one
   ordinary explicit Core application, and calls the existing public
   `checkRefinement(...)` boundary to constrain the provider result against
   the ground goal while retaining premise metas. No generic checker/session
   API or trusted Core rule changes.
7. After result matching, every ordinary-parameter meta must already be
   solved by the ground goal. Instance-premise metas must remain unsolved, and
   the provider result class application must not depend on instance-evidence
   binders. A premise is then resolved in its recorded telescope order after
   zonking prior ordinary and premise solutions. An underconstrained ordinary
   parameter, a premise target that is not ground when scheduled, or a result
   that depends on premise evidence is a stable `stuck` candidate, not a
   heuristic assignment.
8. Provider binders may be interleaved: later ordinary parameters are allowed
   when the result match already determines them. This row does not infer an
   ordinary parameter from a recursively synthesized premise and does not
   reorder premises using output/semi-output roles. Those stronger Lean-style
   scheduling cases remain consumer-gated with `PARAM-ROLES-10`.
9. A recursively solved premise is checked against its exact zonked meta type
   before assignment. Once every premise is filled, the candidate application
   is zonked to meta-free explicit Core and passes an ordinary final
   `checker.check(context, term, goal)` boundary. A term that cannot pass this
   boundary is invalid provider evidence and never becomes a synthesis
   answer.
10. The table key is the stable class reference plus canonical serialization
    of the fully combined-normalized, meta-free goal, exact canonical
    registry/scope serialization, and supplied runtime revision/rule
    inventory. No collision-prone ad hoc or caller-asserted hash is used. Goal
    records receive stable first-discovery ordinals, and table hits and
    active-stack cycle edges are explicit in the trace.
11. A cycle is finite failure for that candidate edge, not coinductive
    evidence and not a process exception. Alternative acyclic candidates at
    the same or later precedence groups are still explored. A goal with only
    finitely failed/cyclic branches is `missing`; its trace retains every
    cycle edge.
12. Candidate decisions are made by exact `(rank, priority)` groups. A group
    is examined completely before a success is accepted. Finite failures
    permit the next group. A stuck, nested-ambiguous, or limit-exceeded branch
    in a group that could still affect the choice blocks all lower-precedence
    groups; limit-exceeded takes precedence over ambiguity, which takes
    precedence over stuck.
13. Multiple successful terms in the first decisive group are compared with
    the same bounded combined LF definitional equality and supplied reviewed
    runtime. Definitionally equal answers form one evidence class; this is
    how the already qualified algebraic diamond collapses through its ordinary
    structure-projection betas. Stable provider order chooses only the
    representative of that equal class. Two non-definitionally-equal classes
    are `ambiguous`. A comparison that exhausts its bound is
    `limit-exceeded`, never a silent choice.
14. Normal successful results are tabled with their explicit term and
    provider-application size. The default complete limits are `maxDepth: 32`,
    `maxTableEntries: 256`, `maxResultSize: 128`, `maxFuel: 4096`, and the
    existing LF comparison limit `256`. All are caller-overridable
    nonnegative safe integers. Root depth is zero; each recursive premise adds
    one. Result size counts provider applications, and one fuel unit is spent
    per candidate attempt. There is no wall-clock or host-heartbeat oracle.
15. Public search is a deeply frozen discriminated outcome:
    `solved | missing | stuck | ambiguous | limit-exceeded`. `solved` carries
    the meta-free checked term, exact target type, selected provider, result
    size, and report. Expected search failure is data rather than an exception.
    Invalid inputs and broken checked-artifact invariants throw
    `CoreLfInstanceSynthesisError` with one of `INVALID_INPUT`,
    `INVALID_CONTEXT`, `INVALID_TARGET`, `INVALID_LIMITS`, `INVALID_REGISTRY`,
    `INVALID_SCOPE`, `INVALID_PROVIDER`, `INVALID_CLASS_HEAD`,
    `NON_PORTABLE_DATA`, or `INTERNAL_INVARIANT`.
16. The report contains the normalized target, complete limits and usage,
    exact registry/scope fingerprint material, supplied runtime revision/rule
    inventory, stable goal-table records, every exact-head candidate attempt,
    ordinary-argument solutions, premise edges with expanded/table-hit/cycle
    disposition, rank/priority decisions, equivalent-success classes, skipped
    lower groups, and the final outcome.
    `serializeCoreLfInstanceSynthesisReport(...)` uses the existing canonical
    browser-safe JSON encoder. The report contains strings and immutable data,
    never live checker/session/table/metavariable objects.
17. The existing `synthesizeCoreLfGlobalDictionary(...)` remains unchanged as
    the qualified finite exact-global helper. The new resolver does not yet
    walk arbitrary call binders, persist synthesis requests in workspace
    source, synthesize omitted arguments from text syntax, expose an external
    Elpi engine, or change Core, runtime/proof rules, class layouts,
    Lambdapi/emdash, `emdash2/`, or sibling repositories. Those remain
    `CALL-SYNTH-7`, AI-SYNTH-1B2B, later optional adapters, or explicit
    cross-repository rows. The optional catalog runtime reuses an already
    reviewed conversion artifact; this row adds or changes no runtime rule.

The focused corpus will use the checked algebraic fixture and cover direct
local/global selection, exact rank and priority preemption, recursive direct-
superclass search, table reuse, both `Monoid -> Mul` diamond routes collapsing
by definitional equality, genuinely distinct same-group ambiguity, missing
evidence, self/mutual cycles with and without an acyclic base, underconstrained
ordinary parameters, interleaved but goal-determined ordinary binders, nested
ambiguity/stuck propagation, every independent limit, JSON-replayed registry
and scope determinism, final explicit-Core rechecking, input immutability, deep
freeze, canonical report serialization, and every frozen invalid-input family.

The proposal gate `H-TS-EMDASH-CLASSES-SYNTH-RECURSE-6-006` is approved under
the user-authorized unattended-review delegation, with immediate human
supersession. Implementation begins only after a documentation-only proposal
checkpoint. The new module and focused suite enter the public v3.2 barrel and
root runner only with their final bounded surface. Proportional qualification
is the dedicated suite, the nearest class/scope/dictionary/capability matrix,
workspace check, TypeScript typecheck, changed-file lint, canonical diff and
forbidden-effect checks, plus one final `check:ts` because the public barrel and
runner are shared boundaries. The 1,546-test SYNTH-SCOPE-5 aggregate is not
rerun during implementation; another complete run occurs only once against
the final recursive-synthesis boundary.

The proposed checkpoint message is
`docs: freeze bounded instance resolver contract`. The implementation
checkpoint message is `elaborator: add bounded recursive instance synthesis`.

## SYNTH-RECURSE-6 Implementation And Qualification Record

Implementation began from proposal checkpoint `e63c555` and preserves the
frozen search boundary. The additive
`src/v3_2/lf_instance_synthesis.ts` module now:

- reconstructs and byte-compares canonical registry/scope snapshots, checks
  the exact Core context, rechecks every activated provider, and rejects a
  non-ground root target;
- indexes exact checked class heads, creates one isolated LF checker session
  per candidate, constrains its full Pi telescope with public
  `checkRefinement(...)`, and recursively fills only recorded instance
  premises before an ordinary final `check(...)`;
- tables combined-normalized goals, exposes cycle and table-hit edges, honors
  independent depth/table/result-size/fuel/conversion bounds, and preserves
  rank/priority decision groups without ID-based choice;
- compares every successful term in the first decisive group by bounded LF
  definitional equality, collapsing the algebraic superclass diamond only
  through its exact compiled projection runtime while retaining genuine
  ambiguity; and
- returns deeply frozen solved/missing/stuck/ambiguous/limit data with
  canonical browser-safe reports, including exact registry, scope, and
  runtime revision/rule fingerprint material.

The runtime input is a measured correction to the proposal rather than a new
semantic rule. The two qualified `MonoidClass -> MulClass` conversion terms
require the already compiled structure-projection betas to reach their shared
constructor normal form. Omitting that exact catalog artifact caused a real
same-group ambiguity; threading it through the ordinary checker,
normalization, recursive premise checks, and equality comparison recovered the
previously proved definitional equality. No diamond special case, mutable
registration surface, or new runtime rule was introduced.

The public v3.2 barrel exports the resolver. The source-visible AI-native
capability record now reports
`recursive-instance-synthesis@emdash-lf-instance-synthesis-v1` and no longer
lists reusable recursive dictionary search as deferred. The existing finite
global dictionary selector remains independently public and unchanged.

Final proportional qualification evidence:

- the combined provider/scope/synthesis suite: 12/12 passed;
- the structure, class-schema, inheritance-layout, parent-lowering,
  provider/synthesis, and AI-native capability matrix: 64 active passes and
  two intentional Lambdapi skips across 66 tests and nine suites;
- `./scripts/pnpmw run workspace:check`: passed;
- `./scripts/pnpmw run typecheck`: passed;
- changed-file ESLint: passed; and
- forbidden-effect and `git diff --check` scans: passed.

The one required `./scripts/pnpmw run check:ts` passed against the stabilized
public TypeScript boundary: workspace validation, full typecheck, full ESLint,
and 1,552 tests across 233 suites completed with 1,498 active passes, 54
intentional skips, and zero failures. The directly observed root-test duration
was 2,497,864.674849 ms. Its durable log and exit markers are
`/tmp/emdash-classes-v1-check-ts-synth-recurse6-run1.{log,status}`. No second
aggregate was run for documentation synchronization. No Lambdapi/emdash
source, active owner, Core/checker/session API, runtime/proof rule, parser,
workspace schema, sibling repository, package, hosted service, or deployment
changed.

## CALL-SYNTH-7 Audit, Repartition, And Frozen 7A Contract

The read-only audit began from final-green resolver checkpoint `168b751` on
2026-08-09. It compared the leading-only
`lf_dictionary_authoring.ts` adapter, generic Core call inference in
`checker.ts`, public meta-retaining `checkRefinement(...)`, proof application,
the completed class/provider/scope/resolver artifacts, and Lean's
`Elab/App.lean`, `Term/TermElabM.lean`, and `SyntheticMVars.lean` scheduling.

The existing Core checker already supplies the essential mechanism: while
walking a generic Pi type it inserts fresh ordinary implicit metas, checks
later explicit arguments against substituted binder types, and can solve
those metas through ordinary constraints. What it intentionally cannot know
is whether an implicit Pi binder is an instance request, because Core plicity
does not encode Lean's separate `instImplicit` management annotation. Lean's
useful lesson is correspondingly outside its kernel: application elaboration
records instance-implicit metavariables, processes later arguments and the
expected result, and repeatedly attempts only requests no longer blocked by
ordinary metavariables.

Emdash should reuse that schedule without importing Lean's syntax object,
global environment extensions, coercion/default machinery, opaque synthetic
metavariable kinds, error-recovery heuristics, or process-local queue. One
direct-TypeScript call artifact can carry exact binder annotations and stable
request IDs, use one isolated checker session for ordinary inference, invoke
the already qualified immutable resolver only on ground class targets, and
then erase to a fully explicit checked Core call.

The row is repartitioned because saturated semantic calls and all of Lean's
application ergonomics are different claims:

- `CALL-SYNTH-7A` handles one completely saturated dependent call, arbitrary
  instance-binder positions, omitted ordinary implicits, supplied implicit or
  explicit arguments, an optional expected type, and stable search traces;
- `CALL-SYNTH-7B` later covers partial application/eta expansion, named
  arguments, defaults, and stronger postponement/retry behavior after an exact
  consumer demonstrates which of those features is necessary.

A Lean term using a partial application can be eta-expanded for the 7A
semantic envelope. This is an explicit temporary authoring limitation, not a
Core limitation or a claim that partial applications are unnecessary.

The selected additive implementation module is
`src/v3_2/lf_class_call_elaboration.ts`. Its exact 7A contract is:

1. `elaborateCoreLfSaturatedClassCall(...)` accepts one checked mixed-
   declaration base, exact `CoreContext`, optional reviewed catalog runtime,
   one inferable Core callee, a finite plicity-tagged stream of source-supplied
   Core arguments, a finite set of instance-binder annotations, optional
   meta-free expected result type, exact immutable registry/scope snapshots,
   resolver limits, one explicit call provenance, and an optional nonnegative
   safe `maxBinders` limit (default 128).
2. A class-call instance annotation contains a nonnegative Pi-binder ordinal,
   unique stable source request ID, and one completed class-inheritance
   layout. The annotation is management metadata only. It neither changes
   `BinderMode` nor adds a third Core plicity; the annotated binder must be an
   existing implicit Pi whose instantiated type has the exact installed class
   head, parameter count, and plicities supplied by that layout.
3. The callee may be a global, local, or compound inferable Core term in the
   exact context. A fresh `CoreLfChecker`/session with the requested conversion
   limit and runtime infers it. The elaborator does not enumerate declarations
   or infer annotations by class-shaped spelling.
4. 7A walks the complete Pi telescope in order and produces a saturated call.
   A matching supplied implicit or explicit argument is checked with public
   `checkRefinement(...)` and substituted into every later binder. An omitted
   ordinary implicit binder receives a fresh ordinary meta. A missing explicit
   binder, extra source argument, plicity mismatch, or annotation beyond the
   finite telescope is a stable malformed-call error.
5. An omitted annotated instance binder receives a separate fresh instance
   meta and source-visible request record. Explicitly supplying an argument at
   that binder checks and substitutes the evidence normally and records a
   `provided` disposition; it does not run search merely because the binder is
   annotated.
6. Pending instance requests are kept in binder order. Before and after each
   supplied argument, and after optional expected-result refinement, the
   elaborator retries pending requests whose zonked class target is meta-free.
   A request blocked by an ordinary meta remains pending. Solving one request
   may make a later request ready, so the finite queue is revisited until no
   further progress occurs.
7. The optional expected type is itself checked as a meta-free type in the
   exact context. `checkRefinement(...)` against that result may determine
   ordinary implicits before the final synthesis pass. A stuck constraint is
   retried only when a ground instance request was actually solved; there is
   no unbounded generic retry loop.
8. Every ready request invokes `synthesizeCoreLfInstance(...)` with the exact
   same declarations, context, reviewed runtime, registry, scope, class
   layout, and caller limits. A solved term is rechecked against the exact
   zonked request type in the call's checker session before its meta is solved.
   Resolver assignments never leak between requests or into failed calls.
9. Synthesis is not allowed to guess an ordinary implicit. After all supplied
   arguments and expected-type constraints, any unresolved ordinary meta or
   non-ground instance target yields a stable call-level `stuck` outcome.
   Output/semi-output parameter scheduling and inference from premise evidence
   remain `PARAM-ROLES-10`.
10. The first unsolved ready request in binder order determines the call-level
    `missing | stuck | ambiguous | limit-exceeded` outcome. Later requests are
    retained as `pending`/`skipped` trace records rather than searched under a
    branch whose call cannot become explicit. Expected search failure is data;
    malformed input, argument/type errors, and violated checked-artifact
    invariants throw `CoreLfClassCallElaborationError` with a stable code/path.
11. A successful result is `status: 'elaborated'` and carries the meta-free
    explicit Core call, its inferred exact result type, optional checked
    expected type, ordered request reports, and a deeply frozen portable call
    report. No synthesis request or session-owned meta crosses the ordinary
    final `checker.infer(...)` and optional `checker.check(...)` boundary.
12. The portable report records the callee, supplied-argument count, expected
    type when present, every walked binder's ordinal/name/mode/type,
    `provided | inferred-implicit | synthesized | pending | skipped`
    disposition, stable request IDs, nested synthesis reports, final status,
    and explicit checked term/type only on success. It contains no live
    context, checker, session, runtime, table, symbol identity, or meta object.
13. `core_serialization.ts` gains one additive ambient-depth serializer used
    by both call reports and the completed resolver. The existing closed
    `serializeCoreExpression(...)` behavior remains byte-identical as its
    depth-zero wrapper. This is inspection-only plumbing, not a Core/checker
    semantic change.
14. The API performs no parser action, declaration/workspace mutation,
    provider discovery, process registration, filesystem/network I/O,
    Lambdapi execution, or callback-driven search. It changes no transfer
    expression variant, Core node, checker/session API, runtime/proof rule,
    class layout, provider/scope artifact, or resolver choice rule.
15. The first corpus extends the checked five-class algebraic fixture with one
    opaque callee whose telescope interleaves an ordinary implicit parameter,
    explicit values, `Monoid` evidence, and later `Mul` evidence. Its expected
    result determines the ordinary implicit; local `Monoid` evidence and the
    runtime-coherent superclass diamond fill both instance slots.

Focused qualification will cover ordinary inference from an expected type,
two arbitrary instance positions, explicit evidence bypass, later-request
readiness after earlier synthesis, exact argument plicity/order, recursive
scope resolution, missing/ambiguity/limit propagation, underconstrained
ordinary and class targets, malformed annotations and calls, canonical replay,
input immutability, deep freeze, ambient-depth serialization, final explicit
Core rechecking, the neighboring class/scope/resolver/capability matrix,
typecheck, changed-file lint, workspace check, forbidden-effect/diff scans,
and one final `check:ts` because the Core serializer and public v3.2 barrel are
shared boundaries.

The proposal gate `H-TS-EMDASH-CLASSES-CALL-SYNTH-7A-007` is approved under
the user-authorized unattended-review delegation, with immediate human
supersession. Implementation begins only after a documentation-only proposal
checkpoint. The frozen proposal message is
`docs: freeze class-call elaboration contract`; the implementation checkpoint
message is `elaborator: add saturated class-call synthesis`.

## CALL-SYNTH-7A Implementation And Qualification Record

Implementation began from proposal checkpoint `c3c6beb` and preserves the
frozen saturated-call boundary. The additive
`src/v3_2/lf_class_call_elaboration.ts` module now:

- reconstructs and byte-compares the exact immutable registry/scope
  snapshots, checks their exact contextual depth and declaration environment,
  and fingerprints the explicit reviewed runtime used by nested synthesis;
- validates stable instance-request IDs and arbitrary Pi-binder ordinals
  against completed class layouts and exact installed class heads, without a
  class node or third Core plicity;
- walks one complete dependent Pi telescope, checks supplied arguments in
  order, inserts isolated ordinary or instance metas for omitted implicits,
  and rejects missing explicit, extra, plicity-mismatched, or malformed calls
  with stable code/path diagnostics;
- lets later supplied evidence or an optional expected result constrain
  ordinary implicits, then invokes the completed immutable resolver only for
  binder-ordered meta-free class targets and rechecks every synthesized term
  against its exact request type;
- propagates the first ready `missing | stuck | ambiguous | limit-exceeded`
  search result as deeply frozen call data while retaining later pending or
  skipped request traces; and
- zonks to one saturated, meta-free, fully explicit call and sends it through
  an ordinary final Core infer/check boundary before returning a portable
  canonical report.

`core_serialization.ts` now exposes the additive
`serializeCoreExpressionAtDepth(...)` inspection helper. The previous
`serializeCoreExpression(...)` is its depth-zero wrapper and retains its
closed-term behavior. The recursive resolver now reuses that shared utility
instead of carrying a private duplicate; its search and choice rules are
unchanged.

The public v3.2 barrel exports the call elaborator. The source-visible
AI-native capability record reports
`class-call-elaboration@emdash-lf-class-call-elaboration-v1`. The checked
algebraic fixture has one opaque five-binder callee interleaving an ordinary
implicit carrier, two explicit values, `Monoid` evidence, and later `Mul`
evidence. It demonstrates inference both from a supplied later dictionary and
from an expected result, explicit-evidence bypass, local recursive search, and
the runtime-coherent `Monoid -> Mul` diamond.

Final proportional qualification evidence:

- the combined provider/scope/resolver/call suite: 18/18 passed, including six
  saturated-call cases;
- the serializer, structure, class-schema, inheritance-layout,
  parent-lowering, provider/resolver/call, and AI-native capability matrix:
  76 active passes and two intentional Lambdapi skips across 78 tests and 11
  suites;
- `./scripts/pnpmw run workspace:check`: passed;
- `./scripts/pnpmw run typecheck`: passed;
- changed-file ESLint: passed; and
- forbidden-effect, tracked/untracked whitespace, and canonical diff scans:
  passed.

The one required `./scripts/pnpmw run check:ts` passed against the stabilized
shared TypeScript boundary: workspace validation, full typecheck, full ESLint,
and 1,559 tests across 234 suites completed with 1,505 active passes, 54
intentional skips, and zero failures. The directly observed root-test duration
was 2,715,709.559982 ms. Its durable log and exit markers are
`/tmp/emdash-classes-v1-check-ts-call-synth7a-run1.{log,status}`. No second
aggregate was run for documentation synchronization. No Lambdapi/emdash
source, active owner, Core node, checker/session API, runtime/proof rule,
parser, workspace schema, sibling repository, package, hosted service, or
deployment changed.

## ALGEBRA-GRADUATE-8 Audit And Frozen Qualification Contract

The 2026-08-09 read-only audit began from final-green CALL-SYNTH-7A
checkpoint `d329497`. It compared the first acceptance corpus with the exact
checked algebraic fixture and all focused evidence accumulated through rows
1--7A.

There is no remaining algebraic implementation gap:

- all five classes are parameterized structures with completed schemas,
  strict-C3 layouts, canonical shared identities, and checked parent
  lowerings;
- the five direct superclass conversions are checked generic providers with
  explicit class premises, while transitive evidence is ordinary recursive
  composition;
- local `Monoid A` evidence already solves representative `Mul A` and `One A`
  goals, the two `Mul` routes compare definitionally equal through the exact
  reviewed runtime, and missing/ambiguity/cycle/stuck/limit behavior is
  qualified separately; and
- the final-green saturated-call fixture already consumes both `Monoid A` and
  later `Mul A` evidence and ends at independently checked explicit Core.

The residual gap is evidence aggregation, not a new mechanism: no single test
currently states that one exact immutable registry/scope/runtime and one local
`Monoid A` derive **all** of `Semigroup A`, `MulOneClass A`, `Mul A`, and
`One A`, expose a successful recursive-premise trace, retain the coherent
diamond, and complete the class-aware call.

`ALGEBRA-GRADUATE-8` is therefore frozen as a test-and-ledger tranche:

1. Extend only the existing checked algebraic fixture in
   `tests/v3_2_lf_instance_scope_tests.ts`; do not create a second fixture,
   demo-only semantic path, or public graduation wrapper.
2. Build one registry and one scope containing the inner local `Monoid`
   provider and exactly the five generated direct-superclass providers.
3. Synthesize the four parent targets in canonical acceptance order
   `Semigroup`, `MulOneClass`, `Mul`, `One`. Every result must be solved,
   meta-free, deeply frozen, and independently checked at its exact target by
   an ordinary LF checker using the same reviewed runtime.
4. Require the direct targets to select the exact generated conversion IDs,
   require at least one positive expanded recursive premise ending at the
   local provider, and require the `Mul` root to retain both definitionally
   equivalent routes rather than selecting by declaration order.
5. Reuse the same registry/scope/runtime in one
   `elaborateCoreLfSaturatedClassCall(...)` invocation. Its five explicit Core
   arguments must contain the local `Monoid` evidence and synthesized `Mul`
   evidence and must pass the ordinary final check already owned by 7A.
6. Treat the existing named construction, provider diagnostics, search
   failures/bounds, canonical replay, immutability, and malformed-call cases
   as carried-forward neighboring evidence. Do not duplicate them in the
   graduation assertion.
7. Add no source module, profile revision, capability entry, public barrel or
   runner edit, parser production, Core/checker/runtime rule, registry/scope
   format, workspace schema, or Lambdapi dependency.

Proportional qualification is the focused provider/resolver/call file,
TypeScript typecheck, changed-test ESLint, exact diff/whitespace review, and
the living-ledger update. The 1,559-test/234-suite CALL-SYNTH-7A aggregate is
recent green evidence for every unchanged shared boundary and must not be
rerun for this test-only row. No active-kernel check is relevant.

The proposal gate `H-TS-EMDASH-CLASSES-ALGEBRA-GRADUATE-8-008` is approved
under the user-authorized unattended-review delegation, with immediate human
supersession. The documentation-only checkpoint message is
`docs: freeze algebraic class graduation contract`; the qualification
checkpoint message is `tests: graduate algebraic class foundation`.

## ALGEBRA-GRADUATE-8 Completion Record

Qualification began from proposal checkpoint `3c64193` and added only one
end-to-end assertion to the existing checked algebraic fixture. The assertion:

- constructs one immutable six-provider registry from the inner local
  `Monoid` evidence and exactly the five generated direct-parent conversions;
- solves `Semigroup`, `MulOneClass`, `Mul`, and `One` in the frozen acceptance
  order and independently checks each meta-free term against its exact target
  using the same reviewed runtime;
- observes the positive expanded `monoid_to_semigroup` premise ending at the
  exact local provider, the exact direct conversion IDs, and both equivalent
  `Monoid -> Mul` routes;
- reuses the same registry/scope/runtime for the saturated class-aware call,
  confirms its explicit local `Monoid` and resolver-equal `Mul` arguments,
  and rechecks the complete result at `Monoid A`; and
- compares the call report's canonical registry/scope material with the exact
  supplied snapshots and verifies deep immutability throughout.

Final proportional qualification evidence:

- `tests/v3_2_lf_instance_scope_tests.ts`: 19/19 passed across four suites;
- `./scripts/pnpmw run typecheck`: passed;
- changed-test ESLint: passed; and
- exact diff and whitespace review: passed.

No source, profile, capability, barrel, runner, package, workspace, kernel, or
sibling-repository boundary changed. The recent CALL-SYNTH-7A aggregate of
1,559 tests across 234 suites, with 1,505 active passes, 54 intentional skips,
and zero failures, therefore remains the governing shared-boundary evidence;
it was not rerun for this test-only graduation row. No Lambdapi or active-
kernel check was relevant.

## MATH-CONSUMER-9 Audit And Retirement Record

The 2026-08-09 authority audit corrected a stale handoff assumption before it
could turn into duplicate mathematics. The historical declaration recovered
from `cartierSolution16.lp.txt` had the outer-LF shape

```text
struct_cov_sieve [Ml_cat] (Ml_site) : TYPE
Struct_cov_sieve [Ml_cat] (Ml_site) [Cs_cat] [Cs_func] (Cs_hom)
  : struct_cov_sieve Ml_site
```

with projections for `Cs_cat`, `Cs_func`, and `Cs_hom`. Its review value was
the parameter surface: `Ml_cat` was implicit throughout, while `Ml_site` was
explicit at the carrier and constructor but inferred by projections. The
August 1 record-usability plan therefore retained it as evidence that carrier,
constructor, and projection parameter modes cannot be conflated. It did not
select the old declaration as a current v3.2 mathematical owner.

The later class plan accidentally promoted that review mnemonic into a future
"mathematical consumer" even though the needed mechanism had already been
qualified and the active mathematical organization had moved on. Current
presheaf/site/scheme sources own their explicit Sigma presentations under
names including `GrothTopology`, `ReflectiveCommRingedSpaceCover`, and
`BinarySiteRelativeSchemePresentation`; this audit makes no claim that those
developments are absent. It also establishes no one-for-one replacement or
compatibility alias for the historical structure. Their mathematical design
and the TypeScript class-usability qualification are independent boundaries.

No replacement fixture is needed:

- STRUCT-PARAM-1 already has two dependent parameters whose carrier,
  constructor, and projection modes differ independently, plus named
  construction, checked projection betas, explicit-Core compilation, and an
  opt-in live Lambdapi conformance consumer; and
- ALGEBRA-GRADUATE-8 already has the representative Lean-style development:
  parameterized classes, multiple inheritance, one shared diamond ancestor,
  generated superclass evidence, recursive search, lexical selection, hard
  ambiguity elsewhere, and a final saturated checked call.

Accordingly MATH-CONSUMER-9 is **retired without implementation**. No
presheaf, sieve, site, sheafification, affine-scheme, scheme, projective-space,
or other mathematical source may be edited merely to satisfy this row. No
geometry-shaped, category-shaped, or adjunction-shaped proxy is added for
coverage volume. A real later development may introduce such a consumer when
it exercises a mechanism not covered by the existing corpus.

This retirement changes only the living plan and handoff. It introduces no
source, test, profile, capability, parser, Core/checker/runtime, workspace,
package, kernel, sibling-repository, or publication boundary and therefore
requires only exact documentation diff/whitespace review. The recent
CALL-SYNTH-7A shared aggregate and ALGEBRA-GRADUATE-8 focused evidence carry
forward unchanged. The initial authority hypothesis did trigger the single
root-mandated bounded baseline
`EMDASH_TYPECHECK_TIMEOUT=90s make -C emdash2 check`; it completed with exit
zero through the current site-relative scheme and projective-line modules.
That read-only evidence is not a dependency of this documentation row and
must not be rerun. The next implementation must be chosen by auditing a
genuine remaining usability or distribution gap, not by replacing this stale
example automatically.

## Decision Ledger

| ID | Decision | Rationale |
| --- | --- | --- |
| C-001 | Target Lean-comparable semantics, not a Lean clone. | Preserves direct translation of ordinary developments without inheriting parser/kernel/tactic complexity. |
| C-002 | Classes and synthesis erase before Core checking. | Keeps one explicit trusted semantic boundary and portable backends. |
| C-003 | Typeclass synthesis is distinct from runtime rewriting and `unif_rule`. | Search needs scopes, recursion, priorities, bounds, ambiguity, and provenance. |
| C-004 | Parameter modes are explicit for carrier, constructor, and projections. | Mathematical consumers may require different quantification behavior. |
| C-005 | Initial inheritance uses canonical flattened field identities and generated parent reconstruction. | Delivers ancestor sharing with a private, replaceable layout. |
| C-006 | C3-style lookup is strict and deterministic. | Inconsistent hierarchies should require explicit repair rather than heuristic order. |
| C-007 | Same spelling never establishes field identity by itself. | Avoids accidental mathematical identification; translation sugar may emit explicit sharing. |
| C-008 | Search takes an immutable registry and scope snapshot. | Makes source/artifacts reproducible locally, in browsers, and remotely. |
| C-009 | Equal-ranked distinct successes are ambiguous. | Avoids invisible declaration-recency semantics in AI-authored workspaces. |
| C-010 | Implement all-input search before output/semi-output inference. | Establishes a useful bounded resolver without premature metavariable scheduling. |
| C-011 | No general inductive declaration frontend. | Curated inductives/HITs plus explicit trusted extensions better fit the directed-HIT objective. |
| C-012 | TypeScript backend is the initial production focus. | Lambdapi remains specification/conformance evidence, not a runtime dependency. |
| C-013 | Publish curated packages, not the private root workbench. | Provides stable consumer contracts and avoids exposing internal development barrels. |
| C-014 | GetPaidX integration is additive and follows local package qualification. | Protects the published/in-review plugin and keeps platform state non-authoritative. |
| C-015 | Parentful class schemas are explicitly unlowered until inheritance qualification. | Prevents metadata from claiming superclass evidence before C3, sharing, layout, and conversion checks exist. |
| C-016 | Class roles default to input; output and semi-output are recorded but not interpreted yet. | Keeps ordinary declarations compact while deferring metavariable scheduling to its consumer-gated row. |
| C-017 | Direct parent conversions are ordinary transparent definitions; transitive evidence composes direct handles. | Gives computational diamond coherence without extra Core semantics or redundant global providers. |
| C-018 | Parent-conversion receivers are authoring-level class evidence over explicit Core binders. | Preserves one trusted plicity model while allowing later synthesis to insert dictionaries. |
| C-019 | Provider registration derives exact telescopes and class heads from checked globals or checked local binders. | Prevents metadata from asserting evidence or types that the explicit-Core checker has not established. |
| C-020 | Lexical frames are explicit precedence ranks; opened named scopes share one rank; imported and current globals share one ambient rank. | Preserves meaningful lexical shadowing while rejecting hidden import/open/declaration-recency choice. |
| C-021 | Equal-priority candidates at one rank remain distinct and visible. | Stable IDs order evidence and diagnostics but never turn a real ambiguity into an implicit choice. |
| C-022 | Provider registries and scopes use canonical JSON as fingerprint material and preserve exact import pins without computing hashes. | Keeps the first scope layer browser-safe, portable, and honest about its acquisition boundary. |
| C-023 | Recursive candidate matching reuses fresh isolated LF checker sessions and public `checkRefinement`, then ends at ordinary `check`. | Reuses qualified generic metavariable machinery without changing the trusted checker or leaking branch assignments. |
| C-024 | Search receives and validates the exact Core context, registry, and scope; depth alone never authorizes local evidence. | Makes local dictionaries replay-safe and keeps all accepted evidence independently checkable. |
| C-025 | Rank and priority form explicit decision groups; all successes in the first decisive group are checked for definitional equivalence. | Provides intentional precedence while retaining strict ambiguity rather than Lean's morally-canonical first-answer heuristic. |
| C-026 | Ground normalized goals are tabled against exact canonical registry/scope material under depth, table, result-size, fuel, and conversion bounds. | Gives deterministic termination and portable recovery without process heartbeats or fake hashes. |
| C-027 | The first resolver requires goal-determined ordinary parameters and premise-independent results; output/semi-output scheduling remains later. | Delivers useful recursive synthesis while making every unsupported inference dependency an explicit stuck state. |
| C-028 | Expected search outcomes are frozen data; only malformed inputs or violated checked-artifact invariants throw. | AI agents can inspect and revise stable proof-state evidence without parsing exception text. |
| C-029 | Resolver conversion accepts and fingerprints one explicit reviewed catalog runtime. | Definitional equality of inherited record evidence depends on already checked projection betas; explicit runtime identity keeps this computational evidence reproducible without special cases or hidden global state. |
| C-030 | Instance-implicit status is explicit binder metadata outside Core plicity. | The checker must preserve one explicit/implicit semantic plicity while management distinguishes ordinary inference from class search. |
| C-031 | CALL-SYNTH-7A saturates the whole telescope; partial/named/default application is a separate 7B row. | Arbitrary-position evidence insertion and application ergonomics can be reviewed independently, while eta expansion preserves the first semantic envelope. |
| C-032 | One isolated call session infers ordinary implicits before invoking isolated ground-goal resolvers. | Matches the useful Lean scheduling shape without a hidden mutable synthetic-metavariable service. |
| C-033 | Explicit evidence at an annotated binder bypasses synthesis. | Preserves the standard escape hatch and makes translation/debugging predictable. |
| C-034 | Expected result refinement may determine ordinary implicits, but synthesis never does. | Supports the common `{A} -> [C A] -> ...` call while retaining the all-arguments-ground resolver boundary. |
| C-035 | Call-level search failure is frozen data; malformed application data still throws stable diagnostics. | AI agents need inspectable proof-state transitions without concealing actual source/type errors. |
| C-036 | Ambient-depth Core serialization is one additive shared inspection utility. | Resolver and call traces need canonical open contextual terms without duplicating the closed serializer or weakening scope validation. |
| C-037 | Algebraic graduation is an end-to-end assertion over the exact checked fixture, not another runtime wrapper or profile. | The implementation mechanisms were already qualified; one integrated acceptance witness closes the evidence gap without expanding the public or trusted boundary. |
| C-038 | Retire `struct_cov_sieve` as a stale consumer mnemonic; do not replace it with a proxy or edit active mathematics. | STRUCT-PARAM-1 already proves the parameter-mode mechanism and ALGEBRA-GRADUATE-8 already proves the representative Lean-style class workflow. The historical Cartier record and current site/scheme Sigma owners are separate designs, so another example would not qualify a new boundary. |

## Validation And Checkpoint Policy

Before each bounded semantic checkpoint:

- inspect branch/worktree status and staged/unstaged diffs separately;
- run `./scripts/pnpmw run workspace:check` when workspace/package boundaries
  are affected;
- run the nearest focused tests directly;
- run TypeScript typecheck and changed-file lint as relevant;
- run one `./scripts/pnpmw run check:ts` only when a shared TypeScript boundary
  actually changed and the bounded tranche is otherwise green;
- run a bounded active-kernel check only when current kernel names or
  computation are newly depended upon; and
- run `check:all` only at an actual cross-layer/release boundary.

Recent green aggregate evidence is carried forward when its boundary did not
change. Long repository-wide aggregates must not be rerun for reassurance.
Every Lambdapi command remains bounded to at most 90 seconds.

Local checkpoint commits are authorized on this dedicated goal branch after:

- the tranche is coherent and green;
- this ledger and decision record are synchronized;
- exact staged paths contain no unrelated work;
- `git diff --cached` and `git diff --cached --check` are reviewed; and
- the checkpoint message names the completed plan row.

Do not amend, rebase, reset, force-push, or erase failed evidence. Use a new
correcting commit or a separate experiment branch. Preserve all existing
worktrees. Push, merge, release, publication, deployment, and cleanup occur
only at their recorded readiness boundary and under the applicable repository
SOP; no hosted operation may break an existing public contract.

## Baseline Evidence

At `66a61ed` in the new worktree on 2026-08-08:

- `./scripts/bootstrap-worktree.sh` passed and created the worktree-local pnpm
  link graph using the shared store;
- `./scripts/pnpmw run workspace:check` passed;
- `./scripts/pnpmw run typecheck` passed; and
- `node --require ts-node/register --test
  tests/v3_2_lf_structure_macro_tests.ts` passed 10/10 executable tests with
  the opt-in Lambdapi probe skipped.

No repository-wide aggregate was run for this baseline.

## Persistent `/goal` Objective

Use this objective after the first implementation checkpoint is synchronized:

> Continue the long-running TypeScript/emdash structures, classes, and
> instance-synthesis goal from the dedicated
> `/home/user1/emdash1-classes-v1` worktree on branch
> `goal/typescript-emdash-classes-v1`. Treat
> `docs/TYPESCRIPT_EMDASH_STRUCTURES_CLASSES_AND_INSTANCE_SYNTHESIS_PLAN.md`
> as the living governing plan, together with the authority chain and SOPs it
> names. On every continuation inspect all worktrees, current branch ancestry,
> staged and unstaged changes, the governing authorities, and the plan ledger;
> preserve unrelated work. Select only the next dependency-ready bounded row,
> keep structures/classes/synthesis as direct-TypeScript management which
> elaborates to explicit checked Core, focus the production implementation on
> TypeScript/emdash, and retain Lambdapi only as an optional bounded
> conformance route. Do not add declaration text parsing, a general inductive
> frontend, a class/Core node, or hidden process-global proof state. Run
> focused proportional checks and avoid long aggregate/repository-wide tests
> unless an actually changed shared or release boundary strictly requires one.
> Local rollback-safe checkpoint commits on the dedicated goal branch are
> authorized only after the bounded tranche is green, the living plan is
> synchronized, and the exact staged diff is reviewed under
> `docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`. When a recorded internal
> proposal gate awaits review and no immediate human response arrives, the
> goal may approve the bounded proposal itself under that checkpoint SOP;
> later human direction supersedes it immediately. Cross-repository package,
> GetPaidX/LastRevision, Arrowgram, publication, and deployment work must wait
> for the plan's prerequisites, follow each repository's SOP, use isolated
> branches, remain backward-compatible/additive where public contracts exist,
> and record exact evidence before mutation. Continue until every scoped row
> is implemented, rejected with durable evidence, or explicitly deferred
> behind a concrete prerequisite or human decision.

## Recovery Checklist

On every continuation:

1. read root `AGENTS.md` and any closer instructions;
2. inspect `git worktree list`, branch/HEAD ancestry, and status;
3. inspect staged and unstaged diffs separately;
4. read this plan's status, ledger, decisions, and latest completion record;
5. locate exact definitions and consumers with `rg`;
6. carry forward valid recent green evidence for unchanged boundaries;
7. implement one dependency-ready bounded row;
8. run proportional checks;
9. synchronize this plan before staging;
10. review exact staged content and checkpoint only when authorized and green;
11. never rewrite or discard checkpoints to hide a failed experiment; and
12. report branch, HEAD, changed plan row, exact validation, worktree state,
    and next dependency-ready row.
