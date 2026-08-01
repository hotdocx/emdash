# Emdash v3.2 Record/Structure Declaration Usability Plan

Date: 2026-08-01 (America/Toronto)

Status: implemented, validated, and locally checkpointed

Plan-ID: `RECORD-STRUCTURE-USABILITY-V3.2`

Parent checkpoint:
`dd8a82e77ef68960a1ba44e98c6235a9c5a3f3ff`
(`feat: add outer LF adjunction declarations`)

Parent main checkpoint:
`cea2605ca4fe6a3023b46c26c5997956cc4e9f03`
(`docs: record recursive Hom Pages deployment`)

Branch: `goal/record-structure-usability-v3.2`

Worktree: `/home/user1/emdash1-record-structure-usability`

Persistent-goal objective: implement the smallest backend-neutral
direct-TypeScript outer-LF declaration facility for a nonrecursive dependent
single-constructor structure with named primitive projections and
subject-reducing projection beta rules. Keep the macro outside explicit Core
and string parsing. Separately classify parameterized/decoded record
conventions and general inductive declarations; do not claim recursion,
positivity, eliminator generation, or Lambdapi-kernel semantics that the
selected slice does not implement.

Git authorization: the user authorized and the prior worktree completed the
adjunction checkpoint `dd8a82e`, authorized this dedicated branch/worktree
fork, and then explicitly authorized the reviewed eight-file structure result
to be committed as a local checkpoint. No push, merge, publication, history
rewrite, branch/worktree removal, or cleanup is authorized.

## 1. Purpose And Selected Outcome

Several prospective sheaf/scheme consumers need finite packages whose later
fields depend on earlier fields. Hand-writing the carrier, constructor,
projection signatures, and one beta rule per projection is both repetitive
and error-prone. The explicitly authorized historical Cartier prototype
contains the representative five-field package:

```lambdapi
constant symbol struct_mod_loc : TYPE;
constant symbol Struct_mod_loc :
  Π [Ml_cat : cat]
    [Ml_site : site Ml_cat]
    [Ml_smod : smod Ml_site Terminal_cat]
    [Ml_mod_ring : mod_ring (smod_mod Ml_smod)]
    (Ml_mod_loc : mod_loc Ml_mod_ring),
    struct_mod_loc;

symbol mod_loc_cat (Ml : struct_mod_loc) : cat;
symbol mod_loc_site (Ml : struct_mod_loc) : site (mod_loc_cat Ml);
// ...three more projections...

rule mod_loc_cat
  (@Struct_mod_loc $Ml_cat $Ml_site $Ml_smod $Ml_mod_ring $Ml_mod_loc)
  ↪ $Ml_cat;
// ...four more projection betas...
```

The first deliverable is a direct-TypeScript outer declaration comparable to:

```ts
scope.declareStructure({
    order: 10,
    carrierName: 'struct_mod_loc',
    constructorName: 'Struct_mod_loc',
    fields: record => {
        const category = record.field({
            binderName: 'Ml_cat',
            projectionName: 'mod_loc_cat',
            mode: binderMode('implicit', 'functorial'),
            type: record.global(scope.resolve(cat))
        });
        const siteValue = record.field({
            binderName: 'Ml_site',
            projectionName: 'mod_loc_site',
            mode: binderMode('implicit', 'functorial'),
            type: record.apply(
                record.global(scope.resolve(site)),
                category
            )
        });
        // Later field types may use category, siteValue, and other
        // already-created field handles.
    },
    provenance
});
```

This is a TypeScript host API. It is not an emdash-term string production,
not a Lambdapi parser extension, and not a new trusted explicit-Core node.

## 2. Authority And Reviewed Evidence

Use this order on every continuation:

1. `emdash2/emdash3_2.lp` for active mathematical declarations and
   computation;
2. the active one-way extension modules and workflow in
   `emdash2/AGENTS.md`;
3. `emdash2/emdash3_2_checks.lp`;
4. `emdash2/reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`;
5. `emdash2/reports/EMDASH_FOUNDATIONS.md`;
6. `emdash2/reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`;
7. `docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md` and the active transfer
   plans it names;
8. this plan for this side goal's exact scope and evidence;
9. the explicitly authorized historical Cartier file only as consumer
   evidence, never as active mathematical authority; and
10. `/home/user1/lambdapi-source-code` as implementation reference for the
    installed Lambdapi command, not emdash design authority.

### 2.1 Recent adjunction macro

`src/v3_2/lf_adjunction_macro.ts` establishes the correct outer-LF pattern:

```text
typed host declaration
  -> branded resolution of prior globals
  -> deterministic atomic expansion
  -> ordinary CoreLfTransferDeclaration / rule values
  -> existing generic module/checker/runtime engines
  -> bounded deterministic Lambdapi conformance emission
```

The macro object and callbacks disappear before `CoreLfModuleSpec` and
explicit Core. Source order, output collisions, provenance, foreign scopes,
and forward references fail closed. The record facility reuses this
architecture, but its generated rules are runtime projection betas rather
than proof-time agreements.

### 2.2 Active kernel record convention

The active v3.2 representative is `PathRecordData` /
`PathRecord_grpd`. It uses:

- a parameterized one-constructor native inductive carrier;
- a decoded `*_grpd` public classifier;
- named manual projections with constructor beta rules;
- a reviewed facade over the generated dependent eliminator; and
- deliberately no runtime record eta.

This richer convention is a composition of several mechanisms. The first
TypeScript usability slice implements only the primitive carrier /
constructor / named-projection / beta package needed by the Cartier consumer.
It does not claim to generate a decoded classifier, native inductive command,
equality view, eliminator, or public v3.2 mathematical record convention.

A later API may factor a lower-level “attach named primitive projections to
an existing carrier and constructor” operation so native inductive carriers
can reuse the projection machinery. That mode remains consumer-gated.

### 2.3 Existing TypeScript inductive boundary

The current transfer layer already has two deliberately narrower abilities:

1. `CoreLfTransferInductiveBlock` plus
   `lowerCoreLfInductiveSignatures` mechanically lowers an explicitly
   represented head and constructors to ordinary signatures; and
2. explicit generated recursor declarations and beta rules already accepted
   by Lambdapi can be transferred through the ordinary declaration/runtime
   engines.

The SCALE-INDUCTIVE evidence explicitly withholds an end-user inductive
declaration facade, source-level recursor synthesis, TypeScript positivity,
and mutual/higher-order inductives. `generatedBy` is provenance, not a trusted
semantic shortcut. The record macro must not reopen or silently supersede
that boundary.

### 2.4 Lambdapi native inductive implementation

The copied Lambdapi source confirms that `inductive` is a real outer command,
not a core term. The parser records one or mutually linked blocks;
`src/handle/command.ml` adds heads, makes fixed parameters implicit in
constructors, adds constructors, generates one `ind_NAME` owner per type,
subject-checks generated rules, and records the inductive metadata.
`src/handle/inductive.ml` traverses supported dependent constructor shapes to
generate motives, induction hypotheses, recursor types, and rules.

The manual advertises parameterized, mutually defined, dependent,
strictly-positive data and includes higher-order strictly-positive examples.
The reviewed source contains shape-directed recursive-occurrence handling but
no separately exposed general polarity/positivity checker that emdash could
safely reuse as a TypeScript trust boundary. Consequently, “similar to
Lambdapi inductive” is not a sufficiently precise specification for a new
emdash API.

The user subsequently clarified that even a precisely delimited ordinary
inductive facade is not the desired next feature. The intended consumers are
*higher inductive categories/types*, such as the walking endomorphism. The
active `emdash3_2_walking_end_hit.lp` demonstrates the materially richer
boundary: opaque category formation, an object introduction, a directed loop
introduction, explicit truncation evidence, a contextual `Functord`
eliminator, and separate base/loop computation owners. An ordinary
head/constructor/recursor generator would therefore solve the wrong next
problem. It is explicitly postponed; any future declaration facility must be
a separately reviewed higher-inductive design that states its cell
dimensions, endpoints, eliminators, computation rules, truncation/coherence
data, and trust boundary.

### 2.5 Cartier consumer inventory

The authorized file contains two useful shapes:

- unparameterized `struct_mod_loc`, with five dependent stored fields; and
- parameterized `struct_cov_sieve Ml_site`, whose carrier parameters have
  different explicitness at the carrier, constructor, and projection
  surfaces.

The first is the selected vertical slice. The second proves that general
parameter support cannot be added casually: carrier parameters, constructor
parameters, inferred projection parameters, and stored fields are distinct
roles. Parameterization is a separate tranche after the unparameterized
field-telescope contract is green.

## 3. Mechanism Partition

The following three facilities must remain distinct:

| Facility | Generated artifacts | Recursion/positivity | Selected now |
| --- | --- | --- | --- |
| Primitive dependent structure | one opaque carrier, one constructor, named projections, projection betas | none | yes, unparameterized first slice |
| One-constructor inductive record | inductive carrier, constructor, generated dependent eliminator/beta, optional named projections | recursive occurrence policy still matters | no; active kernel may consume a later projection adapter |
| Ordinary general inductive declaration | one/mutual heads, multiple constructors, generated recursors and all betas | requires an explicit recursion/positivity contract | no; explicitly postponed because it is not the intended next abstraction |
| Higher inductive category/type declaration | object/point, arrow/path, and possibly higher-cell constructors; endpoint data; dimensional eliminators and computation/coherence laws | requires a dimension-, endpoint-, truncation-, and coherence-aware contract | no; separate future design goal, informed by the walking-endomorphism HIT |

A record macro is not merely a one-constructor spelling of the current
inductive transfer IR. Its practical value is the dependent named projection
telescope, and it intentionally does not generate induction semantics.

## 4. Selected First-Slice Semantics

### 4.1 Exact generated package

For `n >= 1` fields, one command occupies exactly `2 + 2n` source ordinals:

1. one public opaque `constant` carrier of type `TYPE`;
2. one public opaque `injective` constructor with the dependent field
   telescope and carrier result;
3. `n` public ordinary opaque projection declarations, in field order; and
4. `n` runtime projection beta rules, in the same field order.

The constructor is injective because this API promises a genuine free
constructor rather than an arbitrary opaque packing operation. Projections
are ordinary symbols: declaring a projection itself injective would be false
for ordinary records. If an exact legacy consumer later needs a non-injective
packing constant, that is a named semantic option or different API, not an
ambiguous default.

The macro emits no:

- record eta;
- eliminator or recursor;
- equality principle;
- induction hypothesis;
- recursive or self-referential field;
- positivity or coverage judgment;
- decoded `Grpd` classifier;
- parser production;
- browser/deployed profile registration; or
- Lambdapi kernel declaration.

### 4.2 Dependent field elaboration

A field type may reference only already-created field handles. The host
builder retains those references in a macro-private expression tree and
lowers the same tree in three environments:

```text
constructor type: prior field handle -> prior constructor binder
projection type:  prior field handle -> prior projection(record)
beta rule:        prior field handle -> earlier rule capture
```

Internal `Pi`/lambda binders remain locally nameless and must shift field
references correctly beneath nested binders. The public callback and every
binder callback execute exactly once. No callback, field placeholder, or
macro-only expression enters `CoreLfTransferExpression`.

For fields `a : A`, `b : B(a)`, and `c : C(a,b)`, the result is:

```text
Mk : (a : A) -> (b : B(a)) -> (c : C(a,b)) -> Record
get_a : Record -> A
get_b : (r : Record) -> B(get_a(r))
get_c : (r : Record) -> C(get_a(r),get_b(r)).
```

### 4.3 Subject reduction and rule order

The beta for a later projection may type-check only after earlier projection
betas reduce its dependent result type. Rules are therefore generated and
compiled in field order. This is semantic ordering, not cosmetic emission.

The acceptance boundary is stronger than “Lambdapi accepts the text”:

- every rule must pass the generic TypeScript runtime subject checker without
  an external oracle;
- the mixed-phase compiler must expose the prior generated beta to each later
  beta;
- a live Lambdapi consumer must accept the same fragment with subject
  reduction enabled; and
- the last dependent projection must reduce to its constructor argument.

### 4.4 Resolved-global and naming boundary

All non-field globals in field types are branded handles resolved from one
immutable macro scope. Dependency-module, existing-Core, and same-module
earlier-fragment availability are accepted; unavailable, foreign, or forward
handles fail closed. The carrier, constructor, and every projection name must
be unique against both the scope and each other.

The first slice deliberately supports no carrier parameters. This makes
`struct_mod_loc` a complete realistic consumer while keeping the more subtle
`struct_cov_sieve` mode distinctions explicit future work.

## 5. API And Integration Architecture

The implementation is the root-only module
`src/v3_2/lf_structure_macro.ts`, exported through `src/v3_2/index.ts` and
covered by `tests/v3_2_lf_structure_macro_tests.ts`.

The public concepts are:

- `CoreLfStructureMacroScope`;
- branded `CoreLfResolvedStructureGlobal` handles;
- a callback-once `CoreLfStructureFieldBuilder`;
- `structure-declaration` host command and `declareStructure` facade;
- a frozen expansion containing ordinary declarations/runtime rules and a
  canonical handle; and
- deterministic `emitCoreLfStructureLambdapiFragment` conformance output.

The expansion is supplied to `createCoreLfModuleSpec`, policy construction,
the mixed planner, and existing declaration/runtime compilers exactly like
hand-authored entries. `CoreLfModuleSpec`, explicit emdash Core, and the
generic checker gain no structure-specific node or case.

## 6. Why Ordinary Inductives Are Explicitly Postponed

Adding a general `inductive` facade simultaneously would combine a small
ergonomic macro with a much larger trusted-source-language decision. Before
such an API is credible, the project must choose at least:

1. trusted already-expanded artifacts versus untrusted source declarations;
2. parameters versus indices and constructor-local plicity;
3. zero/one/multiple and mutual constructors;
4. direct, nested, and higher-order recursive occurrences;
5. the exact strict-positivity algorithm and diagnostics;
6. generated recursor motive and induction-hypothesis shape;
7. generated symbol naming/collision rules;
8. subject reduction, termination, and computation-rule ordering; and
9. whether Lambdapi is merely a conformance oracle or the generator.

The existing expanded-symbol path already handles the immediate transfer
need. More importantly, the intended new-language consumer is not an
ordinary datatype: it is a higher inductive category/type such as the
walking endomorphism. Such a declaration must coordinate at least:

1. formation of the ambient type/category;
2. object/point constructors;
3. arrow/path constructors with typed source and target endpoints;
4. optional higher-cell constructors and boundary equations;
5. dimensional or contextual eliminators;
6. computation at every constructor dimension;
7. truncation and coherence evidence; and
8. the division between definitional computation and proof-only laws.

`emdash3_2_walking_end_hit.lp` already makes this distinction concrete: its
base and directed loop are not two homogeneous constructors of an ordinary
inductive carrier, and its contextual eliminator has separate base and loop
observations. Building an ordinary Lambdapi-like inductive macro first would
create a competing outer-language abstraction without advancing that target.
Therefore ordinary inductive declaration work is not queued after this plan.
Any renewed effort begins with a dedicated higher-inductive declaration plan
and a genuine consumer corpus; it does not grow out of the structure macro by
feature accretion.

## 7. Kernel And Standard-Library Boundary

No Lambdapi source edit or new `emdash3_2_*` standard-library module is
selected. The generated carrier, constructor, projections, and betas belong
to the consuming LF module just as the historical boilerplate did.

The active kernel's decoded/native-inductive convention remains authoritative
for new mathematical records promoted into `emdash3_2.lp`. If a future
sheaf/scheme implementation needs that exact convention, first compose the
record projection generator with an existing native inductive carrier or add
a separately reviewed parameterized/classifier wrapper. Do not insert a raw
`TYPE` package into the kernel merely because the TypeScript macro can emit
one.

## 8. Plan Ledger

| Row | Status | Dependency | Deliverable and exit evidence |
| --- | --- | --- | --- |
| RECORD-PLAN-0 | complete | user request, `dd8a82e` | Dedicated worktree/goal, authority review, Cartier and active-record inventories, Lambdapi-inductive source audit, mechanism partition, first-slice contract, validation plan, and routing links. |
| RECORD-PROBE-0A | complete | RECORD-PLAN-0 review | Ignored active-kernel probe with four dependent mixed-plicity fields, an injective constructor, four projection betas, last-field computation, explicit no-eta assertion, SR enabled, and zero warnings. |
| RECORD-TS-1A | complete | RECORD-PLAN-0, RECORD-PROBE-0A | `lf_structure_macro.ts` adds branded prior-global resolution, callback-once private field expressions, earlier-field handles, and a frozen `2 + 2n` expansion into ordinary declarations and field-ordered runtime betas. |
| RECORD-TS-1B | complete | RECORD-TS-1A | The four-field dependent fixture compiles through ordinary module/policy/mixed engines; all four rules report `typescript-checked`, see exactly the earlier beta prefix, and reduce to their selected constructor fields. |
| RECORD-TS-1C | complete | RECORD-TS-1B | Deterministic Lambdapi emission covers mixed plicity and nested dependent field types. The generated active-kernel consumer checks all four betas plus explicit no-eta evidence. Independent repeated expansions are deterministic and carry no builder identity. |
| RECORD-TS-1D | complete | RECORD-TS-1C | Root barrel and test runner are wired; focused boundary/negative tests, typecheck, lint, live conformance, the complete aggregate, and the bounded kernel check have run. The sole aggregate failure is the unchanged independently recorded `79 !== 68` categorical-text inventory defect. |
| RECORD-PARAM-2 | deferred | concrete parameterized consumer after 1D | Separate carrier/constructor/projection parameter modes, dependent parameters, result application, and `struct_cov_sieve`-shaped evidence. |
| RECORD-EXISTING-CTOR-2B | deferred | active decoded/native-inductive consumer | Attach named primitive projections to a resolved existing carrier/constructor without regenerating induction semantics. |
| RECORD-INDUCTIVE-3 | postponed, not queued | user clarification after RECORD-TS-1D | Do not build an ordinary general/mutual inductive facade as the next declaration feature; it is not the intended higher-inductive abstraction. Existing expanded-artifact transfer remains available. |
| RECORD-HIT-3B | deferred separate design goal | genuine higher-inductive consumer and authority review | Design higher inductive category/type declarations around dimensional constructors, endpoints, contextual eliminators, computation, truncation, and coherence; use `emdash3_2_walking_end_hit.lp` as active evidence rather than treating it as an ordinary inductive. |
| RECORD-KERNEL-4 | no change selected | concrete active mathematical consumer | Any classifier, eliminator, equality view, or kernel record convention change follows the complete nested Lambdapi SOP. |
| RECORD-FINAL-5 | complete | all nondeferred rows | Plan/handoff/index include the higher-inductive clarification; exact whitespace/file scope and all worktrees were inspected; the superseded ignored probe was removed; validation and Git boundaries are recorded for handoff. |

Only one implementation row may be active. Failed hypotheses update this
ledger and the decision table rather than being silently bypassed.

## 9. Decision Ledger

| Decision | Status | Rationale and consequence |
| --- | --- | --- |
| D-RECORD-001 | accepted | Implement primitive dependent structure usability before considering general inductives. |
| D-RECORD-002 | accepted | The declaration is a direct-TypeScript host macro erased before `CoreLfModuleSpec`/explicit Core; add no string parser. |
| D-RECORD-003 | accepted | The first slice is unparameterized, nonrecursive, and has at least one stored field. It completely covers `struct_mod_loc`; parameter roles remain a separate tranche. |
| D-RECORD-004 | accepted | Field handles are scope-branded and can reference only earlier fields; macro-private lowering interprets them as constructor binders, prior projections, or rule captures. |
| D-RECORD-005 | accepted | Generate a constant carrier, injective constructor, ordinary projections, and one runtime beta per field. Generate no eta or eliminator. |
| D-RECORD-006 | accepted | Projection rules are ordered by field dependency and must pass native TypeScript subject checking without an oracle plus live Lambdapi SR. |
| D-RECORD-007 | accepted | The recent adjunction macro is the outer-command/resolution/atomicity/emission template; record-specific dependency lowering is a separate private builder, not an extension of trusted Core. |
| D-RECORD-008 | accepted | Existing TypeScript inductive transfer remains an expanded-artifact path. Do not infer a source-level inductive generator or positivity guarantee from it. |
| D-RECORD-009 | accepted | No Lambdapi kernel or standard-library file is needed for the selected consumer-layer macro. Active decoded/native-inductive record conventions remain separate. |
| D-RECORD-010 | superseded Git boundary | Work was isolated on `goal/record-structure-usability-v3.2` without checkpoint authority through final handoff. D-RECORD-016 records the user's subsequent explicit local-commit authorization. |
| D-RECORD-011 | accepted user clarification | An ordinary Lambdapi-like inductive declaration macro is explicitly postponed. The intended future facility is for higher inductive categories/types such as the walking endomorphism, whose dimensional constructors, endpoints, eliminators, computation, truncation, and coherence require a separate design goal. |
| D-RECORD-012 | accepted implementation | The implemented public host API is `CoreLfStructureMacroScope` plus branded resolved globals and a callback-once field builder. It erases to six ordinary declarations and four field-ordered runtime rules for the four-field conformance fixture; no parser, Core case, eta, eliminator, recursion, or kernel source was added. |
| D-RECORD-013 | accepted validation exception | The complete `check:ts` passed workspace validation, typecheck, and lint, then ran 1,292 tests in about 38.2 minutes: 1,238 passed, 53 intentionally skipped, and only the untouched categorical-text graduation audit failed at the same `79 !== 68` baseline defect. Relative to the parent adjunction checkpoint, the exact delta is eight new passes and one new opt-in skip; no structure test failed. |
| D-RECORD-014 | accepted cross-layer evidence | The opt-in generated Lambdapi structure consumer passed all four projection betas and the explicit no-eta assertion. `EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check` also passed with no Lambdapi source change. |
| D-RECORD-015 | completed handoff | The dedicated worktree remains at parent HEAD `dd8a82e` with only the reviewed unstaged/untracked eight-file task result and an empty index. The task-owned ignored design probe was removed after its generated test replacement passed. The concurrent elaborator worktree has its own unrelated edits and was preserved. No commit, push, merge, kernel source change, publication, or worktree cleanup was performed for this tranche. |
| D-RECORD-016 | completed checkpoint | After D-RECORD-015, the user explicitly authorized an immediate local checkpoint. The exact reviewed eight-file result, including this ledger synchronization, is committed at the branch tip with message `feat: add outer LF structure declarations`. No push, merge, publication, history rewrite, kernel source change, or worktree cleanup is included. |

## 10. Acceptance Corpus

### Positive structural and runtime cases

1. exact `2 + 2n` source-order expansion and `nextOrder`;
2. deterministic, deeply frozen output and callback-once execution;
3. a Cartier-shaped five-field dependent telescope;
4. mixed implicit/explicit constructor arguments;
5. a field whose type contains an internal dependent `Pi` binder;
6. correct constructor-side bound indices;
7. correct projection-side replacement by prior projections on the same
   record;
8. correct capture-side replacement in beta variable types;
9. field-ordered subject-reducing beta compilation with no oracle;
10. TypeScript runtime reduction for every projection, especially the last;
11. same-module earlier and dependency-module resolved globals;
12. two structures in one scope without generated-name or rule leakage;
13. deterministic Lambdapi source and a live active-kernel consumer; and
14. explicit runtime no-eta evidence.

### Negative and fail-closed cases

1. empty field list in the first slice;
2. duplicate carrier, constructor, projection, or binder/capture names;
3. collisions with prior globals;
4. unavailable, foreign, or forward globals;
5. a field handle from another declaration builder;
6. an escaped internal binder token;
7. self/future-field reference attempts;
8. invalid plicity/mode, source order, name, or provenance;
9. open rule syntax or unbound macro placeholders reaching explicit LF;
10. a wrong-sorted field type rejected by the existing generic checker;
11. caller-owned inputs remain unmutated; and
12. no browser/deployed profile or parser export.

## 11. Baseline And Validation Matrix

Fresh-worktree baseline at `dd8a82e`:

```text
./scripts/pnpmw run workspace:check
  passed (pnpm 11.16.0, Node 24.11.1)

focused adjunction/inductive/inductive-contract/mixed suites
  44 tests: 42 passed, 2 intentional live skips, zero failures

./scripts/pnpmw run typecheck
./scripts/pnpmw run lint
  passed

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  passed
```

The ignored design probe
`emdash2/tmp/probes/record_structure_primitive.lp` passes through
`emdash2/scripts/probe.sh` with subject reduction enabled and zero warnings.

Implemented focused evidence:

```text
structure-only suite
  ordinary run: 8 passed, 1 intentional live skip, zero failures
  opt-in Lambdapi run: 9 passed, zero failures

structure + adjunction + runtime + mixed suites
  51 tests: 48 passed, 3 intentional live skips, zero failures

generated mixed compilation
  four projection betas: all typescript-checked, no subject oracle
  each later rule records the exact earlier-beta prefix
  all four instantiated redexes reduce to the selected constructor field

generated Lambdapi consumer
  all four mixed-plicity dependent projection betas accepted
  reconstructed-record eta remains non-convertible
```

Implementation inner loop:

```bash
node --require ts-node/register --test \
  tests/v3_2_lf_structure_macro_tests.ts

node --require ts-node/register --test --test-concurrency=1 \
  tests/v3_2_lf_structure_macro_tests.ts \
  tests/v3_2_lf_adjunction_macro_tests.ts \
  tests/v3_2_lf_transfer_runtime_tests.ts \
  tests/v3_2_lf_transfer_mixed_tests.ts

./scripts/pnpmw run typecheck
./scripts/pnpmw run lint
```

Because the public barrel, test runner, and shared outer-LF behavior change,
run one complete gate after the bounded tranche is green:

```bash
./scripts/pnpmw run check:ts
EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
```

The live generated conformance test remains opt-in in the ordinary focused
suite and was run explicitly with
`EMDASH_RUN_LAMBDAPI_STRUCTURE_PROBES=1` before final handoff. All Lambdapi
calls are bounded to at most 60 seconds.

Final aggregate evidence:

```text
./scripts/pnpmw run check:ts
  workspace contract: passed
  TypeScript typecheck: passed
  repository ESLint: passed
  node:test: 1,292 total in about 38.2 minutes
    1,238 passed
    53 intentionally skipped
    1 failed: unchanged categorical-text audit, actual 79 vs expected 68

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  passed
```

The parent adjunction checkpoint recorded 1,283 aggregate tests with 1,230
passes, 52 skips, and the same single `79 !== 68` failure. The exact arithmetic
delta is this tranche's eight ordinary passes plus one opt-in skip; no new or
existing structure/adjunction/runtime/mixed test failed.

Documentation checks:

```bash
git diff --check
git diff -- \
  docs/RECORD_STRUCTURE_USABILITY_V3_2_PLAN.md \
  docs/ADJUNCTION_USABILITY_V3_2_PLAN.md \
  docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md \
  emdash2/reports/INDEX.md
```

## 12. Recovery Prompt

Continue only in `/home/user1/emdash1-record-structure-usability` on
`goal/record-structure-usability-v3.2`. Re-read root and nested `AGENTS.md`,
this plan, the handoff, the active kernel record representative, and relevant
SOP sections. Inspect every worktree plus staged/unstaged diffs; preserve the
separate `goal/typescript-elaborator-v3.2` worktree. Confirm ancestry from
`dd8a82e` and recover the active persistent goal.

The implemented tranche is handoff-ready but uncommitted. First inspect the
exact diff and current Git authorization; do not checkpoint unless the user
separately authorizes it. Keep the macro outside explicit Core and parsing.
Do not expand the first slice to carrier parameters, existing
native-inductive attachment, decoded classifiers, eta, eliminators,
recursion, kernel changes, browser promotion, or wider Git operations without
the corresponding recorded dependency and authority. In particular, do not
resume an ordinary general-inductive macro as the next row: D-RECORD-011
postpones it in favor of a separately planned higher-inductive category/type
facility grounded in a genuine consumer such as the walking endomorphism.
