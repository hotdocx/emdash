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
scale, systematically, and mechanically.
Status: active living plan; SCALE-PLAN-0 and SCALE-0A are complete;
H-DTTLF-SCALE-01/D-DTTLF-SCALE-001 is triggered, and SCALE-0B is gated on
that acquisition/interchange-architecture decision
Completed-profile comparison checkpoint:
`0b585e955c5a59f87be9daf9024f37e2b3403982`
Reviewed directed-continuation implementation checkpoint:
`71f46f66aba45d1b79a4c93746970b5d79e42fca`
Pre-plan documentation checkpoint:
`29976248189a8caa9797cced533ae11559dbe95c`
SCALE-0A implementation checkpoint:
`920c0d41b547edf41d8095ea02834abab6585657`

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
structurally and mathematically diverse corpus, defines one generic
source-to-module-IR pipeline, and requires successive corpus additions to be
data and policy changes rather than new owner-specific parser, checker, or
evaluator branches.

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
  have not yet demonstrated generic ingestion of modules, definitions,
  inductives, grouped rewrite rules, proof-time unification rules, protected
  declarations, or deep dependency closure.

The next claim to earn is therefore not “the whole kernel has been ported.”
It is:

> A representative corpus covering every materially distinct active
> declaration and computation mechanism can pass through one generic,
> fail-closed interchange architecture, after which adding another instance
> of an already-qualified mechanism is a mechanical data/policy operation.

The claim is falsified if a representative case requires an owner-named term
node, parser production, checker exception, or evaluator branch that does not
generalize to the mechanism it represents.

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

## Proposed Acquisition Boundary

The proposed development/build pipeline is:

```text
active handwritten .lp source
        │ Lambdapi checks with normal subject-reduction policy
        ▼
pinned `lambdapi export -o lp`
        │ deterministic canonical interchange text
        ▼
small fail-closed TypeScript canonical parser
        ▼
backend-neutral CoreLfModuleSpec
        │
        ├── declaration compiler
        ├── runtime-rule compiler
        ├── proof-time unification compiler
        ├── deterministic Lambdapi round-trip/conformance emitter
        └── committed generated product artifacts
```

Reasons for using the canonical export boundary:

- Lambdapi has already parsed, scoped, elaborated, and checked the active
  module before export.
- The exporter makes implicit structure, plicity, applications, modifiers,
  grouped rules, and unification commands explicit and regular.
- The TypeScript parser can target a smaller pinned grammar than the complete
  handwritten surface language.
- The boundary is reproducible and can be hash-pinned.
- Lambdapi remains a development/build oracle rather than a deployed runtime
  dependency.

The parser must reject unknown canonical commands and grammar rather than
silently discard them. Assertions omitted by canonical export remain a
separate conformance corpus; they are not product declarations.

`raw_dk` is not selected: it loses relevant Lambdapi-level structure and the
active development does not export cleanly through that route.

## Proposed Backend-Neutral Module IR

`CoreLfModuleSpec` should represent the following without Lambdapi-specific
runtime objects:

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

The IR is explicit and locally nameless after term parsing. Qualified symbol
identities and a module dependency graph prevent accidental name collisions.
Dependency closure and hashes are deterministic.

Runtime rewrite rules and proof-time unification rules remain separate
programs. The current continuation has no proof-time rules, but the active
kernel has 61; treating them as runtime equality would be mathematically and
operationally incorrect.

The live inventory shows that `export -o lp` does not erase every tactic:
two protected definitions retain checked `begin`/`end` bodies. SCALE-0B must
preserve that distinction instead of pretending tactic source is a Core term.
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

The set may be refined when the canonical parser exposes a genuinely distinct
active syntax or rule shape. It must not be narrowed merely to make the
current hand-authored implementation pass.

## Mechanical-Scale Acceptance Criteria

The architecture qualifies only when all of the following hold:

1. All five active modules parse into deterministic module IR under one
   pinned canonical grammar.
2. Every command, declaration, runtime clause, and unification rule is either
   represented or rejected with an explicit reviewed reason; nothing is
   silently ignored.
3. The representative corpus covers imports/visibility, opaque and
   transparent declarations, inductives, grouped runtime rules, binder RHSs,
   nonlinear patterns, and proof-time unification.
4. Adding a second instance of a qualified mechanism changes generated
   data/policy and focused fixtures, not owner-named parser/checker/evaluator
   code.
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
   reproducible from pinned source, exporter, parser, compiler, and policy
   hashes.
10. A final review can state a precise envelope: which future additions are
    mechanical, which require only semantic policy review, and which require
    new engine or mathematical work.

## Implementation Ledger

| Row | Status | Depends on | Deliverable |
| --- | --- | --- | --- |
| SCALE-PLAN-0 | complete | reviewed directed continuation | This living plan, corrected verdict, source inventory, representative matrix, gates, and launch prompt |
| SCALE-0A | complete | SCALE-PLAN-0 | Pure TypeScript top-level canonical-export parser/inventory; fixture tests; opt-in live export/version/hash/count gate over all five active modules |
| SCALE-0B | pending | H-DTTLF-SCALE-01, SCALE-0A | Canonical term/pattern parser and immutable module IR with qualified identities, binders, dependencies, inductive blocks, runtime clauses, and proof rules |
| SCALE-0C | pending | SCALE-0B | Generic declaration compiler plus policy overlay; reproduce the reviewed 29-signature continuation without owner-specific catalog construction |
| SCALE-0D | pending | SCALE-0C | Generic typed runtime-rule compiler/matcher; migrate the ten reviewed rules equivalently before adding stress semantics |
| SCALE-0E | pending | SCALE-0C | Separate typed proof-time `unif_rule` compiler and bounded comparison engine |
| SCALE-STRESS-1 | pending | SCALE-0D, applicable semantic review | Outer J, groupoidal Pi/Sigma, and imported Nat grouped-recursion cases |
| SCALE-STRESS-2 | pending | SCALE-0D, SCALE-0E, applicable semantic review | Internal/pullback Pi and Sigma telescope uncurrying cases |
| SCALE-STRESS-3 | pending | SCALE-0D, SCALE-0E, applicable semantic review | Profunctor, protected/evidence extension, and WalkingEnd/HIT cases |
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

This completes source-landscape acquisition evidence only. It triggers
H-DTTLF-SCALE-01 and grants no term parser, module compiler, semantic owner,
runtime rule, proof-time rule, profile, product, or metatheory authority.

## Human Review Gates

### H-DTTLF-SCALE-01 — Acquisition And Interchange Architecture

Triggered after SCALE-0A. The exact proposed decision is:

> **D-DTTLF-SCALE-001:** use checked, version/hash-pinned
> `lambdapi export -o lp` as the development/build acquisition boundary;
> implement the fail-closed canonical parser and backend-neutral
> `CoreLfModuleSpec`; preserve separate runtime and proof-time programs and a
> separate immutable authority/policy overlay; distinguish explicit term
> bodies from checked tactic-source bodies, importing the latter opaquely
> unless a separately reviewed reification/compiler is required; and commit
> reviewed generated product artifacts so Lambdapi is never a production
> runtime dependency.

Approval authorizes SCALE-0B implementation, not semantic promotion of any
new declaration or rule.

### H-DTTLF-SCALE-02 — Generic Engine Boundary

Triggered after SCALE-0C through SCALE-0E demonstrate declaration, runtime,
and proof-time compilation. It reviews the generic engine, migration
equivalence for the existing continuation, fail-closed unsupported boundary,
and generated-artifact policy before broad stress imports.

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

Use checked, bounded canonical export only as the proposed development/build
interchange boundary; handwritten active Lambdapi remains mathematical
authority and production must not invoke Lambdapi. Separate source ingestion
from semantic policy, and separate runtime rewrites from proof-time
unification. Fail closed on unsupported commands, terms, patterns, or
dependencies. Never add an owner-named parser, checker, or evaluator shortcut
to make one stress case pass.

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
