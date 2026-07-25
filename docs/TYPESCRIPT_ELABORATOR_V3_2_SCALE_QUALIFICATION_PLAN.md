# TypeScript Elaborator v3.2 — Systematic Transfer Scale Qualification

Date: 2026-07-24
Plan-ID: TS-ELAB-V3.2-SCALE-QUALIFICATION
Depends-On: the reviewed TypeScript DTT/LF continuation, completed MVP plan,
and active emdash v3.2 mathematical authorities, with implementation history
in
[`TYPESCRIPT_ELABORATOR_V3_2_DTT_LF_CONTINUATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_DTT_LF_CONTINUATION_PLAN.md),
and the completed profile in
[`TYPESCRIPT_ELABORATOR_V3_2_MASTER_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_MASTER_PLAN.md).
Supersedes: no completed profile, approval, implementation record, or
mathematical authority; this is the active forward plan for qualifying a
systematic Lambdapi-to-TypeScript transfer architecture
Side-Task-Ledger: source acquisition, canonical grammar, module IR, generic
compilers, representative stress corpus, validation, and human gates in this
file
Infinity-Codex-Origin: the post-H-DTTLF-03 architecture clarification and
scale audit in session
`infinity-codex:019f9243-9fba-7c73-861b-ff4eacf0c56c:019f9686-d7a3-7030-ba41-92e1e69b97fd`
Infinity-Codex-Decision-Responses: direct user scale-qualification direction
on 2026-07-24; active code, authorities, and this plan outrank the archive
Human-Direction: after approving H-DTTLF-03/D-DTTLF-001, the user requested a
careful clarification of whether the final architecture was already settled.
On 2026-07-24 the user then directed that we gather a varied set of
representative ingredients from the remaining Lambdapi development in order
to prove and stress-test whether the remaining transfer can be performed at
scale, systematically, and mechanically. After clarifying that this direction
did not require a full Lambdapi term parser as the architectural starting
point, the user approved revised H-DTTLF-SCALE-01 on 2026-07-24.
Status: active living plan; SCALE-PLAN-0 and SCALE-0A are complete; revised
H-DTTLF-SCALE-01/D-DTTLF-SCALE-001R is approved; SCALE-0B through SCALE-0E
are complete; SCALE-RUNTIME-DEPS-1 is next and remains a required
pre-stress/batch mechanism
Completed-profile comparison checkpoint:
`0b585e955c5a59f87be9daf9024f37e2b3403982`
Reviewed directed-continuation implementation checkpoint:
`71f46f66aba45d1b79a4c93746970b5d79e42fca`
Pre-plan documentation checkpoint:
`29976248189a8caa9797cced533ae11559dbe95c`
SCALE-0A implementation checkpoint:
`920c0d41b547edf41d8095ea02834abab6585657`
SCALE-0B implementation checkpoint:
`2fd69f55ca8e5576fd91cf41990870bf16e1bb5f`
SCALE-0C implementation checkpoint:
`197e80deb80f30ff964ffc876773d823dd51a402`
SCALE-0D implementation checkpoint:
`3461c2e32f26869099060667e63ce2e65336cb32`
SCALE-0E implementation checkpoint:
`ac8c8887d21c5dc2eeb14c9d3ec3ec4e96cd3ed3`

## Purpose

The exact `emdash-v3.2-dttlf-directed-1` continuation proves that the
foundational direction works:

- an explicit locally nameless, backend-neutral Core;
- a one-shot scoped TypeScript builder with HOAS-like ergonomics;
- generic outer λΠ beta and transparent-definition delta computation;
- bidirectional checking and contextual metavariables;
- catalog-owned categorical computation;
- immutable profile/review artifacts; and
- deterministic Lambdapi conformance emission without a production
  Lambdapi dependency.

It does **not** yet prove that the remainder of `emdash3_2.lp` and its active
extensions can be transferred mechanically. The reviewed continuation
contains only 29 signatures, ten runtime rules, and no proof-time
unification rules. Much of that slice is expressed through hand-authored,
owner-specific proposal, catalog, runtime, and validation code.

This plan establishes the missing qualification evidence. It selects a
structurally and mathematically diverse corpus, defines one generic immutable
module/fragment IR plus declaration/runtime/proof engines, and requires
successive corpus additions to be data and policy changes rather than new
owner-specific materializers, checker exceptions, or evaluator branches.
Audited typed TypeScript construction is the initial mandatory producer of
that IR. Canonical-export term parsing is a possible later acquisition
adapter, not the semantic architecture or an immediate prerequisite.

## Authority And Trust Boundary

The authority order remains:

1. `../emdash2/emdash3_2.lp`;
2. the four active one-way extension modules named in
   `../emdash2/AGENTS.md`;
3. `../emdash2/emdash3_2_checks.lp`;
4. the current v3.2 SOP and status report;
5. `../emdash2/reports/EMDASH_FOUNDATIONS.md`;
6. the canonical-surface-syntax report;
7. the active plans selected through `../emdash2/reports/INDEX.md`;
8. this scale-qualification plan;
9. the DTT/LF continuation and completed TypeScript master plan as
   implementation and historical evidence.

The handwritten Lambdapi sources remain the mathematical authority. A
canonical export, parser, generated module IR, or TypeScript catalog is a
checked derivative and cannot change the meaning or ownership of the active
source.

Import is distinct from semantic promotion. Successfully parsing a
declaration or rule does not authorize it in a TypeScript product profile.
Every executable owner/rule set still needs exact owner-position evidence,
subject-reduction and interaction checks, an immutable policy overlay, and
the applicable human decision.

This plan authorizes no Lambdapi semantic change. Existing active declarations
and rules may be used as conformance and importer stress cases. A genuinely
missing owner or new mathematical rule returns to the complete nested
Lambdapi SOP before any TypeScript transfer.

## Corrected Scalability Verdict

The answer is deliberately split in two:

- **The foundational spine is settled enough to retain.** There is no reason
  to restart the outer LF, explicit Core, scoped builder, catalog/profile
  boundary, or Lambdapi-oracle design.
- **The whole-development transfer architecture is not yet qualified.** We
  have not yet demonstrated one generic representation and engine path for
  definitions, inductives, grouped rewrite rules, proof-time unification
  rules, protected declarations, or deep dependency closure.

The next claim to earn is therefore not “the whole kernel has been ported.”
It is:

> A representative corpus covering every materially distinct active
> declaration and computation mechanism can pass through one generic,
> fail-closed transfer IR and engine architecture, after which adding another
> instance of an already-qualified mechanism is a mechanical data/policy
> operation.

The claim is falsified if a representative case requires an owner-named term
node, materializer, checker exception, or evaluator branch that does not
generalize to the mechanism it represents.

## Three Distinct Kinds Of Genericity

The scale clarification distinguishes three independent concerns:

1. **A generic term/pattern representation is mandatory.** Qualified global
   references, locally nameless binders, applications, runtime match
   variables, proof-time problems, and provenance must not be redefined for
   each semantic owner tranche.
2. **Generic declaration, runtime-rule, and proof-time-unification engines are
   mandatory.** The current successful continuation still duplicates
   expression materialization across DIRECTED-1A, DIRECTED-1B, and
   DIRECTED-1C, while its Foundation runtime contains owner-specific rewrite
   functions. Removing those tranche-specific compilers is the immediate
   scalability problem.
3. **Generic parsing of canonical Lambdapi terms is optional acquisition
   automation.** It is likely useful if most of the hundreds of active
   declarations and clauses are eventually imported, but it is not required
   to settle or stress-test the TypeScript checker architecture.

The successful method remains valid:

```text
audit selected active Lambdapi owners/rules
        │ exact source/export evidence and human semantic policy
        ▼
encode an immutable backend-neutral TypeScript transfer specification
        ▼
compile it into explicit Core declarations/runtime/proof programs
        ▼
run TypeScript checking plus bounded Lambdapi differential evidence
```

The required change is that the specification language and its compilers
become shared and mechanism-generic. Direct typed construction is not an
owner-specific shortcut: adding `Pi_grpd`, `nat_add`, or `WalkingEnd_cat`
must add specification data and policy rather than a `PiGrpd` Core node,
`NatAdd` matcher, or `WalkingEnd` evaluator.

The original `main` worktree is relevant implementation evidence. Its
`src/types.ts`, `src/pattern.ts`, `src/unification.ts`, `src/globals.ts`, and
rewrite/higher-order test suites already explore:

- separate raw and elaborated rewrite-rule records;
- structural pattern matching followed by capture-aware substitution;
- scope-restricted pattern variables and higher-order flex-rigid abstraction;
- occurs checks and deterministic constraint revisiting; and
- symmetric proof-time unification-rule matching that emits new constraints.

Those algorithms should be audited and adapted where they remain generic.
Their named-HOAS closures, mutable global registries, category-specific term
cases, untyped unification-rule registration, and fail-soft logging are not
the new trusted architecture. The current locally nameless Core, contextual
metavariables, immutable profiles, structured failures, and shared operation
budget remain authoritative implementation boundaries.

## Executable Source-Landscape Evidence

With installed Lambdapi `3.0.0-90-gdb4f780`, the checked command
`lambdapi export -o lp FILE` emits deterministic canonical Lambdapi source.
Two exports of the core module produced the same SHA-256 digest.

The initial read-only inventory found:

| Active module | Imports | Symbols | Inductives | Runtime rule commands | Unification rules | Other top-level commands |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| `emdash3_2.lp` | 0 | 757 | 11 | 597 | 61 | 5 flags, 6 builtins, 3 notations, 1 opacity directive |
| `emdash3_2_nat_arithmetic.lp` | 1 | 8 | 0 | 1 | 0 | none |
| `emdash3_2_eq1_hom_action.lp` | 1 | 77 | 0 | 0 | 0 | none |
| `emdash3_2_eq1_evidence_property.lp` | 2 | 60 | 0 | 0 | 0 | none |
| `emdash3_2_walking_end_hit.lp` | 2 | 81 | 0 | 8 | 1 | none |

One `rule` command may contain several `with` clauses, so rule-command counts
are intentionally distinct from clause counts. The active health/status
audit's 602 rewrite rules count source `rule` commands rather than grouped
clauses; its 61 unification rules remain the source authority. Canonical
export is a different, normalized command presentation and its counts must
not be substituted into the source health ledger.

The canonical form adds another useful structural view:

| Active module | Definitions with bodies | Body-free symbols | Protected definitions | Tactic bodies | Canonical runtime clauses | Inductive constructors |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `emdash3_2.lp` | 479 | 278 | 0 | 0 | 633 | 14 |
| `emdash3_2_nat_arithmetic.lp` | 7 | 1 | 0 | 0 | 3 | 0 |
| `emdash3_2_eq1_hom_action.lp` | 77 | 0 | 56 | 2 | 0 | 0 |
| `emdash3_2_eq1_evidence_property.lp` | 60 | 0 | 0 | 0 | 0 | 0 |
| `emdash3_2_walking_end_hit.lp` | 75 | 6 | 0 | 0 | 10 | 0 |

The 633 canonical core clauses are the 597 exported `rule` commands after
expanding their grouped `with` clauses. That number is not directly
comparable to the health report's source-command count. Inductive constructors
and any generated owners still need explicit provenance in module IR; a
canonical presentation cannot be mistaken for a product-policy decision.

The initial canonical-export digests are:

| Active module | SHA-256 of canonical `lp` export |
| --- | --- |
| `emdash3_2.lp` | `355bd868c33553e0c7488a181d7c58661471fc2c878e63d5ceba296d26c056a0` |
| `emdash3_2_nat_arithmetic.lp` | `2fc300997b2de8d53f3cbf7822aff5dedf50edd4167d28c0f12fccc006dcf354` |
| `emdash3_2_eq1_hom_action.lp` | `a1d73d0aac76ca1c5b57c6dd1e9407b3f3eb431839d88484f278fc0ac109c0e2` |
| `emdash3_2_eq1_evidence_property.lp` | `83075b38429baee5b03c7829b2d82f908a04b374cdb839249a54dda72835f4ee` |
| `emdash3_2_walking_end_hit.lp` | `6b7f2d63fe9490a01d5c96726673bb1070400a154e2287fb36cc1486734dfbda` |

These hashes are drift detectors for the pinned exporter and current source,
not new mathematical identities. A deliberate Lambdapi or exporter upgrade
must regenerate and review them.

## Approved Transfer And Acquisition Boundary

Revised H-DTTLF-SCALE-01 approves this development/build architecture:

```text
active handwritten .lp source
        │ Lambdapi checks with normal subject-reduction policy
        ├───────────────┐
        │               │ pinned canonical export
        │               │ inventory, hashes, drift, normalized evidence
        ▼               ▼
exact audited selection and immutable semantic policy
        │
        ▼
typed TypeScript CoreLfModuleSpec/module-fragment builder
        │
        ▼
shared backend-neutral transfer IR
        │
        ├── generic declaration compiler
        ├── generic runtime-rule compiler/matcher
        ├── separate generic proof-time unification compiler/engine
        ├── deterministic Lambdapi conformance emitter
        └── committed reviewed product artifacts

optional later bulk adapter:
pinned canonical export ── fail-closed parser/generator ──► same transfer IR
```

The mandatory boundary is the shared transfer IR and engines, not a textual
parser. Initially, an audited typed TypeScript builder constructs exact
module or dependency-closed fragment specifications. Each specification is
anchored to qualified active owners, source/export hashes or exact relocatable
source evidence, and a separate immutable authority/policy decision.

Canonical export remains valuable because Lambdapi has already parsed,
scoped, elaborated, and checked the active module; the output is deterministic
and normalized enough for inventory, drift detection, exact extraction, and
future generation. SCALE-0A therefore remains permanent evidence rather than
discarded parser work.

A complete canonical term/pattern parser is probably feasible and could
eventually make bulk transfer economical. It is not yet known to be the
shortest path: canonical output still contains binder shorthand, pattern
variables, wildcards, grouped rules, binder-producing right-hand sides,
`let` expressions, inductive blocks, unification constraint lists, and
retained tactic bodies. Parsing those forms proves acquisition coverage, not
that the TypeScript runtime or proof-time engine implements them correctly.
The target IR and engines are stabilized against the representative corpus
before H-DTTLF-SCALE-02 decides whether the optional parser/generator has
sufficient value.

Any later importer must feed exactly the same reviewed transfer IR, reject
unknown canonical commands and grammar, and remain a developer/build tool.
Assertions omitted by canonical export remain a separate conformance corpus;
they are not product declarations. `raw_dk` remains unselected because it
loses relevant Lambdapi-level structure and the active development does not
export cleanly through that route.

## Proposed Backend-Neutral Module IR

`CoreLfModuleSpec` and dependency-closed module fragments should represent the
following without Lambdapi-specific runtime objects, regardless of whether
they were built directly or by a later acquisition adapter:

| IR component | Required information |
| --- | --- |
| Module identity | qualified module ID, source path, dependency IDs, source hash, canonical-export hash, exporter version |
| Declaration | qualified stable identity, binders/plicity, type, optional body, declaration order, direct dependencies |
| Body representation | explicit term body, checked tactic-source body, or absent; only explicit term bodies are candidates for generic delta compilation |
| Modifiers | public/protected/private visibility, constant/injective/opaque status, generated ownership |
| Inductive block | parameters, indices, constructors, generated eliminator references, declaration order |
| Runtime program | grouped typed patterns and right-hand sides, source owner, clause order |
| Proof-time program | typed `unif_rule` left/right problems and generated constraints, source owner, order |
| Presentation metadata | canonical text/span and enough provenance for exact diagnostics and deterministic emission |

The IR is explicit and locally nameless after typed-builder lowering.
Qualified symbol identities and a module dependency graph prevent accidental
name collisions. Dependency closure and hashes are deterministic. A future
parser must produce the same representation rather than introduce a second
semantic AST.

Runtime rewrite rules and proof-time unification rules remain separate
programs. The current continuation has no proof-time rules, but the active
kernel has 61; treating them as runtime equality would be mathematically and
operationally incorrect.

The live inventory shows that `export -o lp` does not erase every tactic:
two protected definitions retain checked `begin`/`end` bodies. The transfer
IR must preserve that distinction instead of pretending tactic source is a
Core term.
The default scalable treatment is to import such theorem/proof owners
opaquely after Lambdapi has checked them, while retaining their canonical body
for provenance and conformance. If a product consumer requires delta
computation through a tactic-backed body, the importer must fail closed and
open an explicit term-reification or tactic-compilation decision; it may not
silently install an unverified body or owner-specific evaluator.

## Proposed Authority/Policy Overlay

Canonical ingestion records what exists. A separate immutable policy records
what a candidate TypeScript profile may do with it:

| Policy class | TypeScript treatment |
| --- | --- |
| `opaque-signature` | type-check applications; do not unfold |
| `checked-transparent-definition` | validate and permit bounded delta unfolding |
| `runtime-rewrite` | compile a reviewed active rule into the bounded evaluator |
| `proof-unification` | compile a reviewed active `unif_rule` only into proof-time comparison |
| `theorem-body` | retain and TypeScript-check an explicit term proof body without treating it as product computation; retain tactic-backed checked source as non-delta provenance |
| `conformance-only` | parse and round-trip/check, but exclude from the product profile |
| `excluded` | record a deliberate unsupported boundary and fail if transitively required |

Generated IR and policy should be committed only after review so production
does not invoke Lambdapi. The generator and oracle remain developer/CI tools.

## Representative Stress Corpus

The corpus is selected by mechanism, not by convenience or symbol count.
Existing active owners can exercise import machinery without claiming any new
groupoidal theorem or closure.

| Mechanism to qualify | Representative active ingredient | Why it is diagnostic |
| --- | --- | --- |
| Outer dependent elimination and nonlinear guarded matching | `ind_eqr` and its reflexivity rule | Dependent motive, repeated endpoints, subject-reduction-sensitive matching |
| Binder-producing groupoidal decoding | `Pi_grpd` and `τ(Pi_grpd A B) ↪ Π x, τ(B x)` | A runtime right-hand side that introduces an outer dependent binder |
| Dependent inductive/record encoding | `τΣ_`, generated `Struct_sigma`, and Sigma elimination beta | Inductive blocks, constructors, dependent projections/elimination |
| Imported grouped recursion | `nat_add` in `emdash3_2_nat_arithmetic.lp` | Module dependency, injective defined head, ordered `with` clauses, recursion |
| Higher-cell action with binder construction | a representative `fapp1_func`/path-action rule | Deep owner telescope and a lambda-bearing right-hand side |
| Proof-time comparison | the active `Pi_cat`/`Functord_cat` comparison family | Proves the runtime/proof-program separation and typed unification compilation |
| Internal/pullback dependent Pi | `Pi_int_funcd` and `Pi_pullback_funcd` | Varying bases, reindexing, dependent section action |
| Sigma telescope uncurrying | `Sigma_catd_functord_catd` and `Sigma_transfd_funcd` | Genuinely dependent nested telescope and component computation |
| Opaque/transparent profunctor boundary | `ProfComparison` and `Prof_tensor` | Deep dependency closure, definitions versus opaque primitives, action rules |
| Protected one-way extension | `groupoidal_core_homwise` and its protected closure | Visibility, module ownership, non-exported implementation dependencies |
| Proof-heavy extension | `omega_equiv_along_evidence_is_prop` family | Large transparent theorem bodies with no runtime-rule promotion |
| Multi-module directed HIT | `WalkingEnd_cat`, `walking_end_ind_funcd`, its beta rules, and `BNat_cat` | Opaque constructors, dependent eliminator, higher action, imported Nat rules, runtime/proof split |

The set may be refined when direct typed encoding or a later acquisition
adapter exposes a genuinely distinct active syntax or rule shape. It must not
be narrowed merely to make the current hand-authored implementation pass.

## Mechanical-Scale Acceptance Criteria

The architecture qualifies only when all of the following hold:

1. Every selected module or dependency-closed fragment is represented in one
   deterministic immutable transfer IR, initially through the shared typed
   builder and optionally through a later parser/generator.
2. Every selected declaration, runtime clause, and unification rule is either
   represented or rejected with an explicit reviewed reason; nothing in the
   claimed transfer envelope is silently ignored. SCALE-0A continues to
   inventory every top-level command of all five active modules.
3. The representative corpus covers imports/visibility, opaque and
   transparent declarations, inductives, grouped runtime rules, binder RHSs,
   nonlinear patterns, and proof-time unification.
4. Adding a second instance of a qualified mechanism changes generated
   data/policy and focused fixtures, not owner-named materializer, checker, or
   evaluator code.
5. The existing 29-signature/ten-rule directed continuation can be regenerated
   or compiled through the generic path with equivalent manifest content and
   conformance outcomes.
6. Runtime and proof-time programs have independent typed validation,
   deterministic ordering, and bounded execution.
7. TypeScript/Lambdapi positive, negative, conversion, and subject-reduction
   witnesses pass for every semantically promoted stress slice.
8. Unsupported higher-order pattern features fail closed with the exact
   source owner and pattern; no fallback silently treats them as opaque
   equality.
9. Generated product artifacts have no Lambdapi runtime dependency and are
   reproducible from pinned source/export evidence, typed specification,
   generic compilers, and policy hashes. If a parser/generator is later used,
   its version and hash join that reproducibility record.
10. A final review can state a precise envelope: which future additions are
    mechanical, which require only semantic policy review, which require new
    engine or mathematical work, and whether bulk acquisition is direct,
    semi-generated, or fully parsed.
11. A larger dependency-closed batch passes without compiler changes after
    its constituent mechanisms have been qualified; representative examples
    alone do not justify a throughput claim.

## Implementation Ledger

| Row | Status | Depends on | Deliverable |
| --- | --- | --- | --- |
| SCALE-PLAN-0 | complete | reviewed directed continuation | This living plan, corrected verdict, source inventory, representative matrix, gates, and launch prompt |
| SCALE-0A | complete | SCALE-PLAN-0 | Pure TypeScript top-level canonical-export parser/inventory; fixture tests; opt-in live export/version/hash/count gate over all five active modules |
| SCALE-0B | complete | revised H-DTTLF-SCALE-01, SCALE-0A | Shared immutable typed transfer IR and scoped builder for qualified declarations, explicit/tactic/absent bodies, runtime patterns, and separate proof problems; no parser or semantic promotion |
| SCALE-0C | complete | SCALE-0B | Generic declaration compiler plus policy overlay; reproduce the reviewed 29-signature continuation without owner-specific catalog construction |
| SCALE-0D | complete | SCALE-0C | Generic typed runtime-rule compiler/matcher; migrate the ten reviewed rules equivalently before adding stress semantics |
| SCALE-0E | complete | SCALE-0C | Separate typed proof-time `unif_rule` compiler and bounded comparison engine, informed by reusable generic algorithms on `main` |
| SCALE-RUNTIME-DEPS-1 | pending | SCALE-0D | Compose immutable generic runtime fragments through explicit module/prior-fragment dependencies; qualify the mechanism without silently promoting the active `Const_catd` fibre rule or any other new semantic rule |
| SCALE-ACQUIRE-1 | deferred decision | SCALE-0C through SCALE-0E and representative encoding evidence | Decide whether bulk acquisition warrants a fail-closed canonical term/pattern parser/generator or a lighter checked extraction adapter; any adapter targets the same IR |
| SCALE-STRESS-1 | pending | SCALE-0D, SCALE-RUNTIME-DEPS-1, applicable semantic review | Outer J, groupoidal Pi/Sigma, and imported Nat grouped-recursion cases |
| SCALE-STRESS-2 | pending | SCALE-0D, SCALE-0E, SCALE-RUNTIME-DEPS-1, applicable semantic review | Internal/pullback Pi and Sigma telescope uncurrying cases |
| SCALE-STRESS-3 | pending | SCALE-0D, SCALE-0E, applicable semantic review | Profunctor, protected/evidence extension, and WalkingEnd/HIT cases |
| SCALE-BATCH-1 | pending | SCALE-RUNTIME-DEPS-1 and required stress mechanisms | Larger dependency-closed data/policy-only transfer batch with no engine changes |
| SCALE-GRADUATE-1 | pending | all required stress rows | Exact mechanical-transfer envelope, residual risks, generated-artifact policy, final qualification proposal |

Rows may be split when implementation reveals an independently reviewable
mechanism. A failed experiment records its exact unsupported syntax or
semantic dependency and opens the smallest correcting row; it does not
authorize a feature-specific shortcut.

## SCALE-0A Exact Contract

SCALE-0A is deliberately non-semantic. It will:

- split canonical `lp` text into semicolon-terminated top-level commands
  while respecting strings, comments, nested `()`, `[]`, and `{}`, and
  semicolon-bearing `begin`/`end` tactic bodies;
- classify `require`, `flag`, `symbol`, `inductive`, `rule`, `unif_rule`,
  `builtin`, `notation`, and standalone opacity directives;
- retain canonical command text and deterministic source order;
- record imported module IDs;
- record declaration modifiers, names, and whether a body is present;
- count constructor declarations in an inductive block;
- count grouped runtime clauses without splitting a rule command;
- reject unknown commands, mismatched delimiters, unterminated strings or
  comments, and trailing unterminated input;
- expose immutable, Node-independent inventory data through the root
  development barrel only; and
- add a separate bounded live gate that runs the pinned exporter on all five
  active modules and verifies exporter version, SHA-256, and exact command
  counts.

It will not parse terms, build a TypeScript semantic catalog, install a
runtime or proof rule, change the frozen MVP or reviewed continuation,
enter the browser barrel, modify Lambdapi source, or grant H-DTTLF-SCALE-01.

## SCALE-0A Completion Record

SCALE-0A added
`src/v3_2/lambdapi_export_inventory.ts` as a pure, Node-independent,
fail-closed top-level parser. It returns deeply immutable ordered commands,
imports, symbol modifiers/body presence, inductive constructor counts, grouped
runtime clause counts, opacity directives, and exact kind totals. It is
exported only by the root development barrel; `browser.ts` remains unchanged.

The first live run usefully rejected three assumptions in the paper
inventory:

- the canonical printer can put inductive parameters before the
  keyword, for example `(A : Grpd)inductive PathRecordData`;
- protected transparent proofs may retain `begin`/`end` tactic bodies whose
  internal semicolons are not top-level command terminators; and
- opacity may be applied by a standalone `opaque owner;` directive after a
  definition.

The splitter and classifier were generalized for those mechanisms, focused
fixtures were added, and the next live run accepted every command of all five
active modules. No command was ignored to make the inventory pass.

`tests/v3_2_lambdapi_export_inventory_tests.ts` now checks:

- every supported command kind and deterministic ordinal;
- semicolons inside strings, comments, brackets, and tactic bodies;
- nested delimiters/comments and parameter-prefixed inductives;
- opaque assumptions versus definitions and later opacity directives;
- grouped-clause and inductive-constructor counts;
- recursive immutability;
- exact fail-closed errors for unknown commands and malformed framing; and
- the pinned exporter version, five export hashes, module dependency graph,
  exact command counts, body/assumption/protected/tactic splits, runtime
  clause counts, constructors, and repeat-export determinism.

Validation on 2026-07-24:

```text
node --require ts-node/register \
  --test tests/v3_2_lambdapi_export_inventory_tests.ts
  7 tests / 1 suite: 6 passed, 1 live probe skipped

./scripts/pnpmw run check:scale-inventory
  7 tests / 1 suite: all passed against Lambdapi 3.0.0-90-gdb4f780

./scripts/pnpmw run check:ts
  workspace contract, typecheck, ESLint, and root tests passed
  423 tests / 52 suites: 396 passed, 27 process probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active core, all four extensions, and checks passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:scale
  passed the complete TypeScript gate, all 19 frozen MVP differential
  judgments, 41 kernel/example metric targets, 39 kernel-script tests,
  five document-registry tests, source/report/book checks, strict LHS and
  generated-catalog audits, all 11 directed-continuation judgments, and all
  seven live scale-inventory tests

python3 emdash2/scripts/lint_report_headers.py
git diff --check
  passed
```

This completes source-landscape acquisition evidence only. It supplied the
evidence for revised H-DTTLF-SCALE-01 and grants no term parser, module
compiler, semantic owner, runtime rule, proof-time rule, profile, product, or
metatheory authority by itself.

## SCALE-0B Completion Record

SCALE-0B adds `src/v3_2/scale_architecture_review.ts` as the separate frozen
record of approved H-DTTLF-SCALE-01/D-DTTLF-SCALE-001R and
`src/v3_2/lf_transfer.ts` as the first shared transfer boundary. The latter
contains no categorical-owner switch and exposes:

- qualified module-owned symbols and exact source/export hashes;
- one explicit locally nameless expression language for terms, patterns, and
  templates, with context-specific rejection of captures and wildcards;
- a one-shot scoped TypeScript builder whose callbacks are lowered immediately
  and never retained in the IR;
- absent, explicit-term, and checked-tactic-source declaration bodies;
- ordered declarations, inductive blocks and generated symbols, grouped
  runtime clauses, and separate proof-time problems/constraint templates;
- explicit matched versus fresh-constraint proof variables and restricted
  higher-order capture scopes;
- dependency/external-symbol inventories, provenance, modifiers, and a
  deterministic referenced-symbol closure; and
- a separately constructed immutable authority/policy overlay.

`createCoreLfModuleSpec()` validates identifiers, hashes, normalized authority
paths, dependencies, uniqueness/order, local binder scope, capture roles,
nonlinear pattern bindings, higher-order scope restrictions, rigid runtime
heads, fresh proof-constraint use, global availability, and all three body
kinds. It clones before freezing, so validation has no ambient registry and
does not freeze caller-owned input. It performs representation validation
only: it does not type-check or install a declaration or rule.

`tests/v3_2_lf_transfer_tests.ts` supplies ten focused tests. In addition to a
synthetic declaration/inductive/runtime/proof module, it directly represents
two active, structurally different mechanisms against the exact
`emdash3_2.lp` source and canonical-export hashes:

- the nonlinear `ind_eqr` reflexivity runtime clause, including repeated
  captures and a wildcard; and
- the `Obj(Hom_cat ...)` proof-time injectivity problem, including three
  generated equality constraints.

Both witnesses use only shared symbol, call, capture, wildcard, variable, and
constraint data. There is no `ind_eqr`, `Hom_cat`, or other owner-named
materializer/checker/evaluator branch. Their policy remains
`conformance-only`; this completion installs neither active rule. Negative
tests fail closed on escaping indices, unresolved globals, duplicate source
orders, undeclared captures, a variable mentioned only by another variable's
dependent type, malformed higher-order scopes, fresh variables in match
problems, incompatible policy classes, foreign builder terms, and decision
drift. The frozen 16-owner/three-rule MVP, reviewed
29-signature/ten-rule continuation, and browser barrel remain exact.

Validation on 2026-07-24:

```text
node --require ts-node/register \
  --test tests/v3_2_lf_transfer_tests.ts
  10 tests / 1 suite: all passed

./scripts/pnpmw run check:ts
  workspace contract, typecheck, ESLint, and root tests passed
  433 tests / 53 suites: 406 passed, 27 process probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active core, all four extensions, and checks passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:scale
  passed the complete TypeScript gate, all 19 frozen MVP differential
  judgments, 41 kernel/example metric targets, 39 kernel-script tests,
  five document-registry tests, source/report/book checks, strict LHS and
  generated-catalog audits, all 11 directed-continuation judgments, and all
  seven live scale-inventory tests

python3 emdash2/scripts/lint_report_headers.py
git diff --check
  passed
```

SCALE-0B therefore establishes the shared acquisition/representation seam,
not the claimed systematic-transfer result. It grants no term parser,
declaration compiler, executable runtime matcher, proof-time comparison
engine, semantic import, product promotion, browser API, or mechanical-scale
qualification. SCALE-0C must consume this IR generically and reproduce the
already reviewed 29-signature continuation without owner-specific catalog
construction.

## SCALE-0C Completion Record

SCALE-0C adds `src/v3_2/lf_transfer_compiler.ts` as one owner-agnostic
declaration compiler over the SCALE-0B IR. Its inputs are the immutable module
specification, the independent semantic policy overlay, and a new independent
immutable symbol-linkage table. The linkage maps authoritative qualified
symbols either to an existing intrinsic `CoreOwnerId` or to a safe Core free
name plus backend spelling; it does not grant semantic policy.

The compiler:

- requires exact policy and linkage coverage and rejects unknown, duplicate,
  missing, forward, self, or excluded dependencies;
- lowers `type`, locally nameless `bound`, qualified `global`, generic `call`,
  dependent `pi`, and `lambda` nodes without an owner-named branch;
- checks conformance-only intrinsic declarations against
  `coreOwnerSignatureType()` and does not install a duplicate free
  declaration for them;
- installs opaque signatures, checked transparent definitions, and checked
  opaque theorem bodies in one persistent `CoreLfDeclarationEnvironment`;
- gives body checking access to only the earlier checked delta environment,
  generic beta, and an optional injected closed runtime component, without a
  global rule/declaration registry;
- validates exact intrinsic arity and plicity, declaration scope, earlier-only
  bodies, transparency/body policy, and the resulting environment; and
- refuses inductives, runtime rules, proof rules, checked tactic execution, or
  unsupported declaration policy rather than silently ignoring another
  compiler phase.

`src/v3_2/directed_continuation_transfer.ts` is the reviewed migration data
edge, not another semantic compiler. It adapts the already approved
`CORE_DIRECTED_GRADUATION_MANIFEST` snapshots through the shared scoped
builder into one `CoreLfModuleSpec`, with exact active qualified symbols,
source fragments, source SHA-256, and canonical-export SHA-256. Separate
policy and linkage artifacts then classify the same ordered 29 declarations:

- 20 base owner signatures are intrinsic `conformance-only` checks;
- eight reviewed candidate declarations are body-free opaque signatures; and
- `Sigma_catd_transport_func` is the one checked transparent definition.

Compiling those three data artifacts installs exactly the existing nine
candidate declarations. The executable equivalence validator checks every
signature, body, transparency decision, Core name, backend mapping, and
environment order against `CoreDirected1cCatalog.create()`. The result remains
eight opaque backend references plus one transparent backend definition. The
existing continuation factory, frozen MVP, browser graph, Lambdapi source,
reviewed runtime programs, and all authority/profile records are unchanged.
The seven-rule directed runtime is injected only while checking the already
reviewed transparent body; its generic IR compilation is SCALE-0D.

`tests/v3_2_lf_transfer_compiler_tests.ts` supplies eleven focused tests. An
unrelated fixture proves the same compiler handles intrinsic, opaque,
transparent, theorem-body, and prior-delta declaration cases without a
registry. Negative cases reject missing linkage, incomplete policy, a forward
reference, intrinsic signature drift, and an unsupported tactic body. The
reviewed migration tests prove the exact 20 + 9 split, recursive immutability,
live-source fragment/hash relocation, expression-for-expression legacy
equivalence, owner-agnostic compiler source, and continued browser exclusion.

Validation on 2026-07-24:

```text
node --require ts-node/register \
  --test tests/v3_2_lf_transfer_compiler_tests.ts
  11 tests / 2 suites: all passed

./scripts/pnpmw run check:ts
  workspace contract, typecheck, ESLint, and root tests passed
  444 tests / 55 suites: 417 passed, 27 process probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active core, all four extensions, and checks passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:scale
  passed the complete TypeScript gate, all 19 frozen MVP differential
  judgments, 41 kernel/example metric targets, 39 kernel-script tests,
  five document-registry tests, source/report/book checks, strict LHS and
  generated-catalog audits, all 11 directed-continuation judgments, and all
  seven live scale-inventory tests

python3 emdash2/scripts/lint_report_headers.py
git diff --check
  passed
```

SCALE-0C establishes generic declaration migration equivalence only. It
grants no new declaration, runtime or proof rule, semantic profile, parser,
product promotion, theorem claim, or systematic whole-development
qualification. SCALE-0D is the next ledger row; SCALE-0E is independently
dependency-ready from this checkpoint.

## SCALE-0D Completion Record

SCALE-0D adds `src/v3_2/lf_transfer_runtime.ts` as one owner-agnostic
runtime-rule compiler and immutable matcher over the SCALE-0B IR. It consumes
one runtime-only `CoreLfModuleSpec`, the separate exact policy overlay, and an
already compiled qualified declaration context. The generic engine:

- resolves every qualified rigid head through declaration linkage, validates
  exact intrinsic/free arity and plicity, requires complete runtime policy,
  contiguous ordered rule groups, and an exact source-owner head;
- compiles typed dependent rule-variable telescopes in order and validates
  each new variable type against only the already compiled rule prefix,
  without revalidating a trusted declaration context under an artificially
  smaller runtime;
- checks rule subject reduction against the same earlier prefix by default;
- compiles one immutable slot-based structural matcher with deterministic
  source order, repeated-capture equality, exact plicity, capture-safe
  template instantiation, and bounded weak-head execution;
- separates the ambient De Bruijn depth of an open checker subterm from
  binders written inside a rule pattern or template, so a first-order
  binder-independent capture is canonicalized and shifted without capture;
- rejects wildcards and genuinely higher-order binder-dependent captures at
  this row rather than treating them as unconstrained equality; and
- permits an exact external subject-reduction-oracle exception only when its
  authority path, ordered rule IDs, and evidence are supplied. Every listed
  exception must actually fail the current TypeScript subject check; an
  unknown, reordered, foreign, duplicate, or newly stale exception fails
  compilation.

`src/v3_2/directed_continuation_runtime_transfer.ts` is the reviewed
migration-data edge, not an owner-specific evaluator. It adapts the exact
four Foundation and three DIRECTED-1B typed rule snapshots plus the three
frozen MVP snapshots into the shared rule IR. The latter variables are
assigned dependent types mechanically from their left-pattern owner slots.
All ten entries retain manifest order, active source fragments, the pinned
source/export hashes, separate runtime policy, and the existing 7-directed
then 3-MVP execution boundary.

The migration bootstraps declaration signatures with the already reviewed
legacy runtime only as a construction oracle, compiles the generic ten-rule
runtime, recompiles all 29 declarations with that generic runtime, recompiles
the runtime against those generic declarations, and rejects any difference
between the two compiled rule sets. The returned fixed-point pair owns only
generic declaration/runtime artifacts. Its equivalence validator exercises
every exact left side with deterministic bindings, compares the result and
binding order against the legacy 7+3 programs, compares an exact plicity near
miss for every rule, checks the zero-step boundary, and revalidates the old
catalog only as an oracle.

Six rules pass standalone TypeScript subject checking against their compiled
prefix. Four preserve their previously approved external-oracle boundary:

1. `directed.sigma-telescope-fibre.evaluate`;
2. `projection.functor-hom.evaluate`;
3. `projection.transfor-component.evaluate`; and
4. `projection.transfor-hom.evaluate`.

The first diagnostic is concrete: typing its reduct needs the active
`@fapp0 $K Cat_cat (@Const_catd $K $A) $_ ↪ $A` computation, which is not in
the reviewed ten-rule profile. The final three retain the checker limitation
already recorded by D-028 for the frozen MVP evaluator. H-DTTLF-03 explicitly
requires the Lambdapi subject-reduction oracle and withholds standalone
TypeScript subject reduction, so SCALE-0D records these four exact,
self-invalidating exceptions instead of silently installing an eleventh
rule, adding a checker coercion, or strengthening the profile claim.

This dependency finding opens `SCALE-RUNTIME-DEPS-1`: generic immutable
composition of prior runtime fragments must be qualified before imported
grouped recursion and the larger batch. That mechanism can be implemented
with representation-only fixtures; importing the active `Const_catd` fibre
rule or any other new executable semantic content still requires its exact
evidence and human gate.

`tests/v3_2_lf_transfer_runtime_tests.ts` supplies eleven focused tests. An
unrelated opaque `Nat` fixture proves strict checking and execution of two
free-declaration-headed rules, including a capture below a lambda and an open
ambient redex. Negative cases reject missing policy, plicity drift, a foreign
source owner, malformed grouped order, a non-preserving rule, wildcard and
higher-order patterns, and stale or foreign oracle exceptions. The reviewed
tests prove the 29+10 fixed point, exact subject-validation split, all ten
legacy rewrites and near misses, immutable source/policy evidence,
owner-agnostic compiler source, and continued browser exclusion.

Validation on 2026-07-24:

```text
node --require ts-node/register \
  --test tests/v3_2_lf_transfer_runtime_tests.ts
  11 tests / 2 suites: all passed

./scripts/pnpmw run check:ts
  workspace contract, typecheck, ESLint, and root tests passed
  455 tests / 57 suites: 428 passed, 27 process probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active core, all four extensions, and checks passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:scale
  complete TypeScript gate passed
  all 19 frozen MVP differential judgments passed
  41 kernel/example metric targets passed
  39 kernel-script tests and five registry tests passed
  source/report/book/audit gates passed
  all 11 directed conformance probes passed
  all seven live canonical-export inventory probes passed
```

SCALE-0D establishes generic runtime compilation and exact migration
equivalence only. It adds no new semantic rule, profile, browser API,
standalone subject-reduction claim, parser, or whole-development mechanical
qualification. SCALE-RUNTIME-DEPS-1 is independently dependency-ready and is
required before the applicable stress/batch rows.

## SCALE-0E Completion Record

SCALE-0E adds `src/v3_2/lf_transfer_proof.ts` as one owner-agnostic,
proof-only compiler and bounded comparison engine over the SCALE-0B IR. It
accepts a proof-only `CoreLfModuleSpec`, an exact separate
`proof-unification` policy overlay, an already compiled qualified declaration
context, and an optional immutable runtime-conversion dependency. It exposes
no evaluator or `rewriteHead` interface.

The compiler:

- resolves every qualified symbol through the compiled declaration context,
  checks exact intrinsic/free arity and plicity, rejects excluded owners, and
  requires one policy entry for every proof rule;
- compiles each dependent matched/fresh variable telescope in order, allowing
  a variable type to depend only on the already compiled prefix;
- validates both sides of the source problem and every generated constraint
  with the current TypeScript LF checker;
- records source order and the exact earlier proof-rule prefix without using
  a mutable registration table; and
- supports an exact, ordered, self-invalidating Lambdapi typing-oracle
  exception for a future reviewed dependent rule that the current standalone
  checker cannot validate. No SCALE-0E fixture needs that exception; unknown,
  foreign, reordered, duplicate, or stale exceptions fail compilation.

The comparison engine first runs the existing bounded β/δ/runtime
definitional comparison. If conversion does not close the problem, it tries
proof rules in immutable source order, forward and then symmetrically per
rule. A successful match accumulates one substitution across both problem
sides, allocates `fresh-constraint` metavariables in telescope order, and
places the generated problems on an ordered worklist. Direct canonical
meta/rigid problems delegate to the existing session, retaining its
scope/occurs/Miller-pattern assignment checks. Conversion reductions,
meta assignments, and proof-rule applications consume one shared explicit
budget and produce an immutable trace, rule-application list, resolution
order, and metavariable snapshot. Cyclic rule application therefore returns
a structured next step at the exact bound rather than looping.

First-order captures below binders use the same locally nameless discipline
as the runtime matcher: a candidate independent of rule-local binders is
canonicalized at the ambient comparison depth and reinserted capture-safely.
Wildcards and genuinely higher-order `allowedBoundIndices` captures remain
fail-closed boundaries in this row. The engine also deliberately makes no
claim of complete Lambdapi-unifier parity, arbitrary rigid decomposition,
flex-flex search, or coverage of the active 61-rule inventory.

The old-main audit was performed against
`30394f9ad7e3834e2786e1b42cc9ec396fcc2c8f`, specifically
`src/types.ts`, `src/pattern.ts`, `src/unification.ts`, `src/state.ts`, and
`src/globals.ts`. SCALE-0E retained only the generic operational lessons:

- symmetric matching of an equality pair with one accumulated substitution;
- ordered replacement of one problem by generated constraints;
- fresh metavariables for variables used only by generated constraints; and
- Miller-style scope, occurs, and bounded-worklist discipline.

It did not copy the mutable process-global `userUnificationRules` array,
untyped `addUnificationRule`, named-HOAS storage, category-specific term
switches, undefined-argument-to-fresh-hole behavior, heuristic global
iteration bound, or console/fail-soft error handling. Current explicit Core,
immutable policy, qualified declarations, and session-local metavariables own
those responsibilities instead.

`tests/v3_2_lf_transfer_proof_tests.ts` supplies nine focused tests over an
unrelated opaque `Nat`/`Code` declaration fixture. Two executable
representation-only rules prove strict typing, deterministic prefix order,
forward/symmetric matching, direct generated-meta solving, RHS-only fresh
metas, ordered multi-constraint success and stuck evidence, and bounded
cyclic application. Negative cases reject incomplete policy, plicity drift,
ill-typed constraints, wildcard/higher-order patterns, and stale/foreign
typing-oracle exceptions. Source/API tests prove that the compiler contains
no active category owner, old global-registry path, runtime interface, or
browser export.

Validation on 2026-07-24:

```text
node --require ts-node/register \
  --test tests/v3_2_lf_transfer_proof_tests.ts
  9 tests / 1 suite: all passed

./scripts/pnpmw run check:ts
  workspace contract, typecheck, ESLint, and root tests passed
  464 tests / 58 suites: 437 passed, 27 process probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active core, all four extensions, and checks passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:scale
  complete TypeScript gate passed
  all 19 frozen MVP differential judgments passed
  41 kernel/example metric targets passed
  39 kernel-script tests and five registry tests passed
  source/report/book/audit gates passed
  all 11 directed conformance probes passed
  all seven live canonical-export inventory probes passed
```

SCALE-0E completes the three generic local compiler/engine foundations only.
Its rules are synthetic representation fixtures. The active
`Obj(Hom_cat ...)` witness remains `conformance-only`; no active proof rule,
runtime rule, profile, product API, parser, or all-61-rule claim was promoted.
SCALE-RUNTIME-DEPS-1 is next. Once generic prior-runtime composition is
qualified, H-DTTLF-SCALE-02 reviews this engine boundary before any semantic
stress import.

## Human Review Gates

### H-DTTLF-SCALE-01 — Transfer IR And Acquisition Architecture

SCALE-0A triggered the initial acquisition proposal. The user clarified that
“systematic” meant making the successful reviewed transfer method reusable
across a mechanism-diverse corpus, not requiring a complete parser for
`emdash3_2.lp` as the architectural starting point. The initial unapproved
D-DTTLF-SCALE-001 text is therefore superseded by this approved revision:

> **D-DTTLF-SCALE-001R — approved 2026-07-24:** make the generic immutable
> module/fragment IR and generic declaration, runtime-rule, and separate
> proof-time-unification engines mandatory; initially construct reviewed
> transfer specifications with a shared typed TypeScript builder anchored to
> exact Lambdapi source/export evidence; retain checked, version/hash-pinned
> canonical export for inventory, drift detection, extraction, conformance,
> and an optional later bulk parser/generator; preserve a separate immutable
> authority/policy overlay and the explicit-term, checked-tactic-source, and
> absent-body distinction; and commit reviewed product artifacts so Lambdapi
> is never a production runtime dependency.

This approval authorizes SCALE-0B implementation, including a separate frozen
decision record and representation-only witnesses. It does not authorize
semantic promotion of any new declaration or rule, a canonical term parser,
or any product/profile expansion.

### H-DTTLF-SCALE-02 — Generic Engine Boundary

Triggered after SCALE-0C through SCALE-0E and SCALE-RUNTIME-DEPS-1
demonstrate declaration, local runtime, composed prior-runtime, and proof-time
compilation. It reviews the generic engine, migration equivalence for the
existing continuation, fail-closed unsupported boundary, generated-artifact
policy, and whether SCALE-ACQUIRE-1 should use a canonical parser/generator
or lighter checked extraction before broad stress imports.

### Existing Semantic And Mathematical Gates

- A new TypeScript signature/runtime/proof profile still requires an exact
  H-DTTLF-02-style proposal and decision, or a successor gate explicitly
  defined before promotion.
- H-DTTLF-03 remains the authority only for
  `emdash-v3.2-dttlf-directed-1`; it does not authorize this larger corpus.
- H-DTTLF-04 is required for new groupoidal-closure mathematics. Merely
  importing or conformance-testing already-active groupoidal owners does not
  assert new closure and does not trigger that gate.
- A Lambdapi source change follows the complete owner-position and nested SOP
  workflow regardless of any TypeScript plan approval.

### H-DTTLF-SCALE-03 — Mechanical-Transfer Qualification

Triggered by SCALE-GRADUATE-1. It may authorize only the exact supported
mechanism envelope demonstrated by the corpus. It must list residual
non-mechanical cases and cannot infer full mathematical correctness,
termination, confluence, unrestricted normalization, performance, release,
or groupoidal closure.

## Validation Policy

The frozen `check:all`, `check:conformance`, browser profile, and deployed MVP
remain unchanged.

SCALE-0A adds:

```text
./scripts/pnpmw run check:scale-inventory
```

This bounded opt-in lane invokes the installed exporter and is mandatory for
changes to canonical acquisition, parser classification, pinned version,
counts, or hashes. The ordinary `check:ts` lane runs all pure fixture and
failure tests while skipping live exporter processes.

The aggregate forward gate is:

```text
./scripts/pnpmw run check:scale
```

It preserves the complete reviewed continuation gate and then runs the live
scale inventory. Later rows must extend this gate without mutating the frozen
MVP policy.

All Lambdapi invocations remain bounded to at most 60 seconds and retain
subject-reduction checking.

## Git And Persistent-Goal Boundary

This plan inherits
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md)
and the exact local-checkpoint authorization already recorded in the DTT/LF
continuation.

Temporary local checkpoint commits are authorized only on the existing
`goal/typescript-elaborator-v3.2` branch/worktree, after a bounded tranche is
green, this ledger and affected navigation are synchronized, and the exact
staged diff excludes unrelated work.

No push, merge, PR, publication, release, new branch/worktree, rebase, amend,
reset, history rewrite, branch/worktree deletion, or unrelated cleanup is
authorized.

## Persistent `/goal` Launch Prompt

```text
Kick off or continue implementing
docs/TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md.

Treat its Persistent /goal Launch Prompt as part of the objective. Recover
actual state from active code, checks, the plan and its ledgers, all Git
worktrees and staged/unstaged diffs, and the active authority order. Follow
the root AGENTS.md and, for every emdash2 action, emdash2/AGENTS.md and the
current v3.2 SOP. Resume the in-progress row or select the next
dependency-ready bounded slice, and implement executable evidence rather than
only extending the architectural prose.

Preserve the completed emdash-v3.2-mvp-1 profile and the reviewed root-only
emdash-v3.2-dttlf-directed-1 continuation unchanged. Keep the explicit
locally nameless Core, scoped builder, outer lambda-Pi LF, immutable
catalog/profile boundary, and Lambdapi conformance role. Do not claim that the
whole-development transfer architecture is settled until the representative
mechanism corpus passes the plan's mechanical-scale acceptance criteria.

Follow approved D-DTTLF-SCALE-001R. Build one immutable backend-neutral
module/fragment IR and generic declaration, runtime-rule, and separate
proof-time-unification engines. Initially construct exact reviewed transfer
specifications through a shared typed TypeScript builder anchored to active
source/export evidence. Use checked bounded canonical export for inventory,
drift detection, extraction, conformance, and a possible later bulk
parser/generator; do not make full term parsing an immediate prerequisite.
Handwritten active Lambdapi remains mathematical authority and production
must not invoke Lambdapi.

Separate acquisition from semantic policy and runtime rewrites from
proof-time unification. Fail closed on unsupported terms, patterns,
dependencies, or proof problems. Never add an owner-named term node,
materializer, checker exception, or evaluator shortcut to make one stress
case pass. Audit the old generic rewrite, pattern, and unification algorithms
on `main` as implementation evidence, but do not reintroduce their mutable
global state, category-specific AST, named-HOAS storage, or fail-soft
behavior.

Do not promote a declaration, definition, runtime rule, proof-time rule,
product profile, or metatheory claim without its exact recorded evidence and
human gate. Existing active owners may be inventoried and conformance-tested
without changing Lambdapi. Any proposed Lambdapi semantic change returns to
owner position and follows the nested SOP in full.

Use commit 0b585e955c5a59f87be9daf9024f37e2b3403982 as the completed-profile
comparison checkpoint, 71f46f66aba45d1b79a4c93746970b5d79e42fca as the
reviewed continuation implementation checkpoint, and recover the actual
descendant HEAD. These are comparison/backtracking evidence, never
permission to reset or rewrite descendants.

The existing authorization permits temporary local checkpoint commits only
on the existing goal branch after a bounded green tranche, synchronized
ledger/navigation, and exact staged-diff review. It authorizes no other Git
mutation, integration, remote operation, publication, release, or cleanup.

Continue safe independent work around a pending human gate. Keep every
Lambdapi process bounded to at most 60 seconds and preserve subject-reduction,
warning, audit, catalog, health, examples, and CI obligations whenever their
scope is affected.
```

## Change Log

- **2026-07-24 — SCALE-PLAN-0 opened.** Corrected the scalability verdict:
  the foundational spine is retained, but a systematic full-development
  transfer is not yet qualified. Recorded canonical-export evidence across
  all five active modules, proposed the backend-neutral module IR and
  authority overlay, selected a mechanism-diverse stress corpus, defined
  mechanical acceptance criteria and review gates, and selected SCALE-0A as
  the first non-semantic implementation slice.
- **2026-07-24 — SCALE-PLAN-0 and SCALE-0A completed;
  H-DTTLF-SCALE-01 triggered.** Added a pure immutable canonical-export
  inventory parser, focused fail-closed fixtures, and a separate bounded live
  gate over all five active modules. Live evidence corrected the inventory for
  parameter-prefixed inductives, semicolon-bearing tactic bodies,
  standalone opacity, 11 core inductive blocks, 633 canonical core runtime
  clauses, and 14 inductive constructors. The full scale gate passed while
  preserving both reviewed TypeScript profiles and all Lambdapi sources.
- **2026-07-24 — SCALE-0A checkpointed.** Recorded local checkpoint
  `920c0d41b547edf41d8095ea02834abab6585657` after the exact staged diff,
  focused and live inventory suites, 423-test TypeScript gate, all 19 frozen
  MVP differentials, all 41 kernel/example targets, all 11 directed
  continuation judgments, report/link/whitespace audits, and the complete
  scale gate passed. The checkpoint grants no H-DTTLF-SCALE-01 decision,
  semantic import, product promotion, or broader Git authority.
- **2026-07-24 — Revised H-DTTLF-SCALE-01 approved; SCALE-0B opened.**
  Clarified that generic transfer representation and engines are mandatory
  while a complete canonical term/pattern parser is optional acquisition
  automation. Recorded approved D-DTTLF-SCALE-001R, retained SCALE-0A as
  inventory/drift evidence, added direct typed construction as the initial IR
  producer, separated later bulk-acquisition qualification, and recorded the
  reusable and rejected boundaries of the older generic rewrite/unification
  implementation on `main`. No new semantic owner, runtime rule, proof-time
  rule, profile, or product authority was granted.
- **2026-07-24 — SCALE-0B completed.** Added the frozen reviewed architecture
  artifact, shared immutable module/fragment IR, one-shot scoped builder,
  distinct term/pattern/template and body classes, separate runtime/proof
  programs, and separate policy overlay. Ten focused tests represent a
  nonlinear active runtime rule and a constraint-producing active proof rule
  without installing either or adding an owner-specific code path. The
  433-test TypeScript gate passed with both reviewed profiles and the browser
  boundary unchanged. SCALE-0C is now dependency-ready.
- **2026-07-24 — SCALE-0B checkpointed.** Recorded local checkpoint
  `2fd69f55ca8e5576fd91cf41990870bf16e1bb5f` after exact staged-diff
  review, ten focused transfer tests, the 433-test TypeScript gate, bounded
  active kernel check, complete scale gate, header lint, and whitespace audit
  passed. The checkpoint grants no parser, semantic promotion, product
  expansion, mechanical-transfer qualification, or broader Git authority.
- **2026-07-24 — SCALE-0C completed.** Added one generic declaration
  compiler, separate immutable symbol linkage, and an exact typed 29-signature
  migration specification. Twenty base signatures validate against intrinsic
  Core schemas and the nine reviewed candidate declarations reproduce the
  legacy reviewed catalog expression-for-expression, including its 8 opaque
  + 1 transparent boundary and backend mappings. Eleven focused tests and the
  444-test TypeScript gate passed; no runtime/proof compiler, semantic
  promotion, browser API, or mechanical-scale claim was added. SCALE-0D is
  next and SCALE-0E is dependency-ready.
- **2026-07-24 — SCALE-0C checkpointed.** Recorded local checkpoint
  `197e80deb80f30ff964ffc876773d823dd51a402` after exact staged-diff
  review, eleven focused compiler/migration tests, the 444-test TypeScript
  gate, bounded active kernel check, complete scale gate, header lint, and
  whitespace audit passed. The checkpoint grants no runtime/proof compiler,
  semantic promotion, parser, product expansion, mechanical-transfer
  qualification, or broader Git authority.
- **2026-07-24 — SCALE-0D completed.** Added one generic typed runtime
  compiler/matcher and an exact ten-rule migration adapter. The 29-declaration
  and ten-rule compilers reach a stable generic fixed point, and all ten
  positive rewrites, binding orders, plicity near misses, and the zero-step
  boundary agree with the reviewed 7+3 legacy programs. Six rules pass strict
  TypeScript subject checking. The nested Sigma-fibre rule and three frozen
  MVP rules retain exact self-invalidating Lambdapi-oracle obligations under
  the already approved standalone-subject-reduction non-claim. No missing
  `Const_catd` computation or other semantic rule was silently promoted.
  Eleven focused tests and the 455-test TypeScript gate passed; SCALE-0E is
  next, and SCALE-RUNTIME-DEPS-1 records the generic prior-fragment
  composition prerequisite exposed by this tranche.
- **2026-07-24 — SCALE-0D checkpointed.** Recorded local checkpoint
  `3461c2e32f26869099060667e63ce2e65336cb32` after exact staged-diff
  review, eleven focused runtime/migration tests, the 455-test TypeScript
  gate, bounded active kernel check, complete scale gate, header lint, and
  whitespace audit passed. The checkpoint adds no semantic rule, standalone
  subject-reduction claim, parser, product/profile expansion,
  whole-development mechanical-transfer qualification, or broader Git
  authority.
- **2026-07-24 — SCALE-0E completed.** Added one generic proof-only compiler
  and bounded symmetric constraint engine after auditing the reusable and
  rejected parts of the old-main pattern/unification implementation. Two
  unrelated typed fixture rules exercise accumulated pair matching,
  RHS-only fresh metas, ordered generated constraints, direct session
  assignments, and exact cyclic-budget exhaustion. Nine focused tests and
  the 464-test TypeScript gate passed. No active `unif_rule`, runtime
  conversion, browser API, semantic profile, parser, all-61-rule coverage, or
  whole-development qualification was added. SCALE-RUNTIME-DEPS-1 is next
  before H-DTTLF-SCALE-02.
- **2026-07-24 — SCALE-0E checkpointed.** Recorded local checkpoint
  `ac8c8887d21c5dc2eeb14c9d3ec3ec4e96cd3ed3` after exact staged-diff
  review, nine focused proof-engine tests, the 464-test TypeScript gate,
  bounded active kernel check, complete scale gate, header lint, and
  whitespace audit passed. The checkpoint adds no active proof rule,
  runtime conversion, parser, product/profile expansion, all-61-rule or
  whole-development qualification, or broader Git authority.
