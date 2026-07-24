# TypeScript Elaborator/Kernel For emdash v3.2 — Living Master Plan

Date: 2026-07-23
Plan-ID: TS-ELAB-V3.2
Depends-On: active emdash v3.2 authorities and the completed ELAB-0 wiring
slice
Supersedes: forward architecture and growth guidance in the ELAB-0 RFC and
handoff; preserves their historical evidence
Side-Task-Ledger: coverage, implementation, experiment, and human-review
ledgers in this file
Infinity-Codex-Origin: none; user-directed post-ELAB-0 review on 2026-07-23
Infinity-Codex-Decision-Responses: none; decisions are recorded inline
Status: active living master plan; ELAB-0 is complete and the first
post-ELAB-0 implementation slice is dependency-ready
Pre-implementation baseline:
`a06433e57cba95e7d35f8577b7c71912862c3d25`

## Purpose And Operating Contract

This is the master implementation plan and decision ledger for replacing the
stale root TypeScript category layer with a TypeScript elaborator and candidate
product kernel aligned with the active emdash v3.2 design.

It is deliberately revisable. Each continuation must recover the actual state
from active code, checks, this ledger, and Git rather than treating prose or a
previous conversation as current fact. An owner-position probe or
implementation result may correct, refine, reorder, split, or reject a planned
slice. Record the evidence and changed decision here before or with the code
that depends on it.

This plan does not outrank the active mathematical authorities under
`../emdash2/`. A TypeScript implementation can become the deployed MVP kernel
only after the explicitly recorded graduation boundary below. Until then,
Lambdapi remains the executable specification and differential oracle for the
common implemented fragment.

The Git and checkpoint discipline for a persistent Codex `/goal` run is
defined in
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md).
The ready-to-use launch prompt appears at the end of this plan.

## Authority And Recovery Order

Before starting or resuming a slice, read and inspect in this order:

1. root `AGENTS.md` and, for any `emdash2/` change, `emdash2/AGENTS.md`;
2. `emdash2/emdash3_2.lp` and its active one-way extensions;
3. `emdash2/emdash3_2_checks.lp`;
4. the current v3.2 SOP, Foundations, and canonical-syntax report named in
   `TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md`;
5. this plan and its decision/experiment ledgers;
6. the current implementation and tests, relocated with `rg`;
7. staged and unstaged Git state, worktree state, and bounded baselines.

The baseline commit above is a comparison and possible design-backtracking
anchor. It is not an instruction to reset a descendant worktree. Verify the
relationship with:

```bash
git merge-base --is-ancestor \
  a06433e57cba95e7d35f8577b7c71912862c3d25 HEAD
```

If the current work is not a descendant, document why and recover the relevant
ledger and code state before continuing.

## Current Evidence

At the baseline:

- the Git worktree is clean;
- `./scripts/pnpmw run check:ts` passes 159 tests in 44 suites, with 157
  passing and two opt-in Lambdapi probe tests skipped;
- `EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check` passes the active
  kernel, extensions, and diagnostics;
- ELAB-0 implements an isolated direct-TypeScript surface AST to explicit
  target AST to deterministic Lambdapi-probe path under `src/v3_2/`;
- ELAB-0 covers only `fapp0`, `fapp1_fapp0`, and `tapp1_fapp0`;
- the old root category-specific term union and standard library remain
  present, non-authoritative, and coupled to otherwise reusable generic
  elaboration mechanisms.

The active kernel contains the projection ladder that ELAB-0 does not yet
model:

| Role | Full owner | Capped/application owner |
| --- | --- | --- |
| Functor object action | — | `fapp0` |
| Functor hom action | `fapp1_func` | `fapp1_fapp0` |
| Transfor diagonal component | `tapp0_func` | `tapp0_fapp0` |
| Transfor off-diagonal action | `tapp1_func` | `tapp1_fapp0` |
| Source-varying internal Hom | `hom_int` | projected through the common ladder |
| Target-varying internal Hom | `hom_con_int` | projected through the common ladder |

The kernel also has ordinary functor-category weakening, exchange, and
contraction owners (`Const_func_func`, `sym_func_func`, and
`diag_func_func`), displayed categories and functors, pullback
(`Pullback_catd`), constant displayed families (`Const_catd`), and sections
(`Pi_cat`). The current SOP still lists displayed structural logic as a
deferred boundary. Therefore a uniform dependent elaborator is a concrete
consumer to investigate, not evidence that unspecified displayed structural
rules are already sound or should be added wholesale.

## Intended End State

The intended product architecture is:

```text
TypeScript expressions / optional parser
                 |
                 v
surface AST and typed macros
                 |
        scope, constraints, metas,
        binder roles, implicit recovery
                 |
                 v
backend-neutral explicit emdash Core IR
                 |
        +--------+--------------------+
        |                             |
        v                             v
small TypeScript checker/       deterministic Lambdapi
evaluator/rewrite-unifier       conformance emitter
        |                             |
        v                             v
candidate deployed MVP          bounded differential probes/CI
kernel                          against active v3.2 owners
```

The TypeScript surface and macro layer may offer customized constructions that
would be awkward without direct access to Lambdapi internals. Those macros
must elaborate to explicit Core terms and remain outside the small trusted
checker/evaluator.

The final deployed product need not invoke Lambdapi. Lambdapi is retained as:

- the current mathematical and computational specification;
- a rapid experimental workbench for kernel design;
- a differential oracle for the common frozen fragment;
- an optional diagnostic/reviewer backend.

The old TypeScript category theory is not a compatibility target. Its
category-specific nodes, reductions, setup, and tests should ultimately be
deleted and replaced. The sequencing constraint in `AGENTS.md` exists only to
preserve useful generic evidence long enough to extract or reimplement it
cleanly.

## Design Decisions

| ID | Status | Decision | Evidence or review condition |
| --- | --- | --- | --- |
| D-001 | accepted | Replace and eventually delete the old TypeScript category-specific layer; preserve no old category API merely for compatibility. | The old theory predates v3.2 and is entangled with the generic term union. Inventory generic invariants before deletion. |
| D-002 | accepted | Reimplement a clean generic core where extraction would preserve global mutation or stale semantic coupling. | Holes, rule registries, and traversals currently depend on the old union and global state. |
| D-003 | accepted | Use a backend-neutral explicit Core IR. Do not make Lambdapi text the semantic IR. | The product kernel and Lambdapi emitter need one shared elaboration result. |
| D-004 | accepted | Make the TypeScript checker/evaluator the intended product path; keep Lambdapi optional at runtime and mandatory as a conformance oracle until graduation. | ELAB-0 proves integration, not TypeScript parity. |
| D-005 | accepted | Describe families of owners with recursive classifier/projection schemas rather than adding one surface tag per Lambdapi symbol. | Full/capped projections and higher cells repeat the same owner pattern recursively. |
| D-006 | accepted | There is no special `fapp2`: a 2-cell is acted on by applying the ordinary `fapp1_func` schema to the hom functor obtained from the preceding `fapp1_func`. | This preserves the active iterated-hom architecture. |
| D-007 | experimental | Start the context/type/term design from displayed/dependent structure, then recover ordinary structure as a constant-family specialization where justified. | TypeScript elaboration is intrinsically contextual, but the exact uniform representation and reductions require probes. |
| D-008 | accepted | Separate four notions of structural action: meta-level telescope operations, internal ordinary structural functors, displayed structural owners, and shape reindexing. | Naive exchange or contraction is not generally valid in a dependent telescope. |
| D-009 | accepted | Every displayed-to-ordinary comparison must be classified as runtime reduction, proof-time unification, explicit theorem/path, or intentional non-collapse. | Existing bridges do not justify blanket definitional equality. |
| D-010 | accepted | Kernel additions are consumer-led. Missing displayed operations are first recorded as failed owner-position probes; only the smallest coherent owner package may be promoted. | Required by the active v3.2 SOP and warning/subject-reduction discipline. |
| D-011 | accepted | Direct TypeScript AST construction remains the first surface; a string parser is optional and deferred. | Parsing does not test the elaboration or trusted-core boundary. |
| D-012 | accepted | Persistent implementation uses bounded experiments and, only when the launch prompt authorizes them, a dedicated local goal branch/worktree and validated checkpoint commits. | See the Git protocol linked above. |

“Accepted” records the current engineering direction, not a theorem about the
mathematics. Entries marked experimental must be resolved by the named
evidence before they can constrain the trusted core.

## Core Architecture Requirements

### 1. Separate layers

The implementation must keep these layers distinct:

1. **Surface and macros:** source spans, omitted arguments, convenient
   TypeScript constructors, and later optional parsing.
2. **Elaboration state:** scopes, telescopes, metavariables, constraints,
   expected types, and diagnostics.
3. **Explicit Core:** binders, variables, applications, classifiers, and
   declared rule heads with all semantically relevant arguments represented.
4. **Trusted TypeScript kernel:** scope/type checking, capture-safe
   substitution, weak-head evaluation, rule validation/application, and
   definitional comparison for a frozen fragment.
5. **Backends:** Lambdapi serialization, diagnostics/source-map adaptation,
   debug printers, and future persistence formats.

Surface macros may call elaborator services. They may not mutate trusted rule
tables or bypass Core checking.

### 2. Schema catalogs, not a flat symbol grammar

The first schema catalog should represent:

- classifier formation and its parameter telescope;
- projection families and their full/capped relation;
- endpoint recovery constraints;
- plicity separately from binder variation;
- internalization constructors such as `hom_int` and `hom_con_int`;
- degeneration/comparison routes, with an explicit authority class;
- backend capability and active-source provenance.

An owner schema may name a Lambdapi symbol for conformance, but the surface
grammar should express the mathematical operation. Adding an active symbol to
a catalog is not sufficient: at least one positive consumer, one relevant
negative boundary, and its expected type/normal form are required.

### 3. Recursive higher-cell stress test

Suppose:

```text
F : Functor(A,B)
x,y : Obj(A)
f,g : Hom_A(x,y)
alpha : Hom_(Hom_A(x,y))(f,g)
```

The functor's action on `alpha` should be represented by recursively applying
the same hom-action schema:

```text
fapp1_func (fapp1_func F x y) f g
```

and then applying that resulting functor to `alpha`. This must elaborate
without inventing `fapp2` or falling back to a one-category-only AST case.
A mismatch at either hom level must be rejected at the originating source
span.

### 4. Dependent-first hypothesis

The initial encoding hypothesis to test is:

```text
context Γ               ↦ category interpreting Γ
type A over Γ           ↦ A : Catd Γ
term of A               ↦ section/object associated with Pi_cat A
substitution σ : Δ → Γ  ↦ functor
A substituted along σ   ↦ Pullback_catd A σ
ordinary type B         ↦ Const_catd Γ B, when the comparison is justified
```

This is a design experiment, not yet a selected universal encoding. It must be
tested against:

- dependent extension and lookup;
- weakening by an unused variable;
- substitution and composition;
- exchange only where dependency permits it;
- contraction only with the required diagonal/reindexing data;
- an effectively nondependent family;
- at least one case that must remain displayed rather than collapse.

The experiment must say whether a result is judgmental in the active kernel,
proof-time comparable, available by an explicit theorem/path, or unavailable.

### 5. Ordinary/displayed bridge matrix

Maintain a matrix with at least these columns for every proposed bridge:

| Consumer | Uniform displayed route | Optimized ordinary route | Authority class | Positive evidence | Required non-collapse |
| --- | --- | --- | --- | --- | --- |
| To be filled by the first dependent slice | owner sequence | owner sequence | runtime / unification / theorem / distinct | probe/test | negative probe/test |

Do not optimize a constant family to an ordinary term until both routes have
a recorded comparison. “TypeScript can detect nondependence” is not itself a
kernel equality.

## Reusable Generic Machinery Inventory

Each legacy mechanism must receive one of four dispositions before the old
category layer is removed: **port**, **reimplement**, **retain temporarily as
oracle**, or **delete**.

| Mechanism | Initial disposition | Required evidence |
| --- | --- | --- |
| Bidirectional `infer`/`check` organization | reimplement from the pattern | Expected-type and inferred-type tests over the new Core |
| Holes/metavariables and occurs check | reimplement behind per-session state | Scope escape, occurs, solution determinism, and error-location tests |
| Higher-order pattern unification | port only after Core binder representation stabilizes | Positive pattern cases and negative non-pattern boundary |
| Rewrite versus unification-rule separation | reimplement as explicit rule classes | Rule validation plus runtime/proof-time differential cases |
| Capture-avoiding substitution and shifting | audit, then port or replace | Binder, shadowing, and substitution composition tests |
| Proof-state traversal | retain as evidence, then reimplement generically | No dependency on old category node tags |
| Direct TypeScript constructors | port | Source-location and macro-expansion tests |
| Existing category constructors/rules | delete after replacement coverage is recorded | No compatibility requirement; retain only independently generic tests |
| Global mutable standard-library/rule setup | delete | New session-owned rule manifest and deterministic reset-free tests |
| Legacy parser | defer/delete | Revisit only after surface/core contracts stabilize |

The inventory is not an instruction to mechanically extract old files. Clean
reimplementation is preferred whenever extraction would preserve the stale
union, ambient global state, or old mathematical assumptions.

## Coverage And Stress Corpus

The coverage ledger is about semantic capabilities, not merely exported names.

| ID | Capability | Current status | Minimum positive/negative evidence |
| --- | --- | --- | --- |
| C-00 | Plicity independent of binder variation | complete in ELAB-0 | Metadata round trip |
| C-01 | `fapp0` implicit category recovery | complete in ELAB-0 | Exact explicit target and wrong functor/object category |
| C-02 | `fapp1_fapp0` capped arrow action | complete in ELAB-0 | Exact target and wrong source category |
| C-03 | `tapp1_fapp0` capped off-diagonal action | complete in ELAB-0 | Exact target and Lambdapi acceptance |
| C-04 | `tapp0_fapp0` diagonal component | missing | Exact owner slots and wrong component object |
| C-05 | `fapp1_func` full hom functor | missing | Returned functor usable at the next hom dimension |
| C-06 | `tapp0_func` full component functor | missing | Projection to `tapp0_fapp0` |
| C-07 | `tapp1_func` full off-diagonal functor | missing | Projection to `tapp1_fapp0` |
| C-08 | Recursive action on a 2-cell | missing | Two hom levels; wrong inner endpoint rejected |
| C-09 | Partially applied `hom_int` | missing | Object projection followed by later action |
| C-10 | Partially applied `hom_con_int` | missing | Variance-correct target action and reversal negative |
| C-11 | Metavariable/implicit solving over Core | missing | Occurs/scope/ambiguity negatives |
| C-12 | Context extension and displayed type | missing | Dependent lookup and substitution |
| C-13 | Constant displayed family comparison | missing | Both routes plus a deliberate non-collapse |
| C-14 | Dependent weakening | missing/inventory required | Concrete elaboration consumer |
| C-15 | Dependency-respecting exchange | missing/inventory required | Permitted and forbidden telescope swaps |
| C-16 | Dependent contraction/diagonal | missing/inventory required | Reindexing data and invalid contraction negative |
| C-17 | TypeScript rule manifest/checker | missing | Valid/malformed rules and differential normal forms |
| C-18 | Source-mapped backend diagnostics | partial | Generated map exists; diagnostic remapping missing |
| C-19 | Legacy category-layer removal | blocked by replacement | Generic inventory and replacement gates green |

The first higher-dimensional corpus must exercise C-05 through C-10 before
declaring the grammar representative of v3.2.

## Implementation Ledger

Only one row should be marked **in progress** at a time in a single worktree.
Parallel alternatives belong on explicit experiment branches/worktrees and
must identify their common baseline.

| Slice | Status | Dependencies | Deliverable and exit criterion |
| --- | --- | --- | --- |
| PLAN-0 | complete | — | This living plan, Git protocol, synchronized handoff/SOP/index, and a green preparation validation. |
| ELAB-0 | complete wiring spike | — | Three capped/object owners lower to explicit target terms; TypeScript and opt-in Lambdapi positive/negative probes pass. |
| ELAB-1A | next / dependency-ready | ELAB-0 | Introduce backend-neutral owner/classifier schema interfaces and a catalog; migrate the three ELAB-0 forms without changing behavior; add `tapp0_fapp0`; focused exact-target and negative tests pass. This slice must change implementation, not only produce another inventory report. |
| ELAB-1B | pending | ELAB-1A | Add generic full/capped projection elaboration for `fapp1_func`, `tapp0_func`, and `tapp1_func`; pass the recursive 2-cell stress case and a wrong-inner-hom negative. |
| ELAB-1C | pending | ELAB-1B | Add partial internalization cases for `hom_int` and `hom_con_int`; prove the grammar can retain an unapplied Hom-valued functor and later project it with correct variance. |
| ELAB-2A | pending | ELAB-1A, Core binder decision | Reimplement session-owned scopes, binders, metavariables, constraints, substitution, occurs checking, and bidirectional checking over Core. |
| ELAB-2B | pending | ELAB-2A | Implement the bounded dependent-first context experiment using `Catd`, `Pullback_catd`, `Const_catd`, and `Pi_cat`; populate the bridge matrix. |
| ELAB-2C | pending | ELAB-2B | Exercise weakening, permitted/forbidden exchange, and contraction. Record missing displayed owners with consumer probes; do not yet assume kernel promotion. |
| KERNEL-DISPLAYED-1 | conditional | ELAB-2C failure evidence | If a concrete uniform elaboration consumer cannot be expressed, design and probe the smallest displayed structural owner package under the v3.2 SOP, including degeneration/comparison and non-collapse cases. Human review is required before promotion. |
| KERNEL-DISPLAYED-2 | conditional | reviewed KERNEL-DISPLAYED-1 | Promote only reviewed kernel changes with diagnostics, warning comparison, audits, catalogs, health, examples, and CI synchronized. |
| TSK-1 | pending | ELAB-1 schema stability, ELAB-2A | Define a frozen TypeScript MVP signature/rule manifest and small trusted-core boundary. |
| TSK-2 | pending | TSK-1 | Implement rule validation, weak-head evaluation, rewriting, proof-time unification/comparison classes, and deterministic diagnostics for the frozen fragment. |
| TSK-3 | pending | TSK-2 | Build positive, negative, conversion, malformed-rule, and higher-cell differential tests against Lambdapi for every common owner/rule. |
| MIGRATE-1 | pending | replacement inventory, TSK-2 | Port/reimplement still-useful generic proof/unification facilities and classify every legacy test. |
| MIGRATE-2 | pending | MIGRATE-1, replacement tests | Delete the old category-specific nodes, standard library, reductions, and obsolete category tests; retain no D0/D1 or legacy category compatibility API. |
| GRADUATE-1 | human gate | TSK-3, MIGRATE-2 | Review parity evidence, trust assumptions, subject reduction, termination/confluence scope, performance, and maintenance cost. Decide whether TypeScript is the authoritative deployed MVP kernel. |
| RELEASE-READY | pending | GRADUATE-1 | Documentation, manifests, examples, diagnostics, full repository checks, and explicit residual Lambdapi-conformance policy are synchronized. |

If a slice grows beyond one reviewable semantic claim, split it in this table
before continuing. Do not mark a row complete merely because its code compiles:
its tests, evidence, ledger entry, and proportional gates must all be current.

## Immediate Slice: ELAB-1A

The next run should begin with implementation of ELAB-1A:

1. inventory the current `src/v3_2` switches and active signatures at their
   current locations;
2. define the smallest backend-neutral schema interface needed to express the
   existing three operations and `tapp0_fapp0`;
3. keep active owner names/provenance in a catalog/backend layer rather than
   in a growing surface-term union;
4. migrate existing elaboration through that schema without changing the
   deterministic ELAB-0 output;
5. add a direct TypeScript surface constructor or generic application form for
   a transfor component;
6. add an exact explicit-target positive and a wrong-object/endpoint negative;
7. run the focused TypeScript test, the opt-in positive/negative Lambdapi
   probes, `check:ts`, and the bounded kernel check;
8. update this ledger with the actual result and refine ELAB-1B if the schema
   evidence changes its shape.

It must not add a broad parser, migrate the legacy union, or promote a
displayed kernel rule.

## Human Review Gates

Record a concrete recommendation and evidence before requesting review:

| Gate | Earliest trigger | Question |
| --- | --- | --- |
| H-01 | ELAB-2B | Does the dependent-first encoding produce a simpler uniform elaborator than an ordinary-first Core with displayed forms only where needed? |
| H-02 | KERNEL-DISPLAYED-1 probe complete | What are the mathematically correct displayed weakening, exchange, and contraction owners, and which degenerations should compute, unify, or remain theorem-level? |
| H-03 | TSK-1 | What exact owner/rule fragment is frozen as the MVP TypeScript kernel? |
| H-04 | TSK-2 | What termination, confluence, subject-reduction, and trusted-rule assumptions may the MVP claim? |
| H-05 | GRADUATE-1 | Is Lambdapi retained only as CI/reviewer oracle, or as an ongoing acceptance authority for selected declarations? |
| H-06 | after measured need | Is a textual grammar stable and valuable enough to support? |

A human gate blocks only the dependent slice. Record the prerequisite and
continue any independent dependency-ready work instead of guessing the
decision.

## Experiment Record Template

Append or link one record for an experiment that changes architecture:

```text
Experiment ID:
Date and checkpoint:
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

Temporary probes belong under ignored `emdash2/tmp/probes/` or another
explicit temporary location. Durable evidence belongs in focused tests,
diagnostics, examples, or the appropriate report.

## Validation Matrix

| Change | Minimum gate before checkpoint/handoff |
| --- | --- |
| Plan/docs only | `git diff --check`, relevant link/header checks, `check:ts`, bounded `make -C emdash2 check` |
| Root TypeScript behavior | focused tests, `./scripts/pnpmw run check:ts` |
| Common Core/Lambdapi owner | focused opt-in generated probes with timeout at most 60 seconds, then bounded kernel check |
| Root package/setup | `workspace:check`, root typecheck/tests, affected print checks |
| Lambdapi declaration/rule | owner-position probe; diagnostics; warning comparison; LHS/rule audits; catalog/health refresh; examples and full `make ci` as required by `emdash2/AGENTS.md` |
| Substantial cross-layer tranche | `./scripts/pnpmw run check:all` |
| Legacy deletion | all replacement-focused gates plus full repository check and explicit test-disposition ledger |

Record exact commands and outcomes in the completed slice or checkpoint
message. Never weaken a gate to make a checkpoint green.

### PLAN-0 preparation validation

Validated from the Git root on 2026-07-23:

```text
python3 emdash2/scripts/lint_report_headers.py
  passed; 10 active plan headers

local relative-Markdown-link audit
  passed; 30 links across the seven changed navigation/plan documents

git diff --check
  passed

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, and root tests passed
  159 tests / 44 suites: 157 passed, 2 opt-in probes skipped

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, extensions, and diagnostics passed

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  root TypeScript gate passed
  41 active Lambdapi kernel/example files passed
  39 formal infrastructure tests and 5 print registry tests passed
  active-reference/report-header/book/evidence/typography/KaTeX checks passed
  strict rule-LHS audit and generated catalog freshness passed
```

No TypeScript source, test behavior, package/lockfile, Lambdapi declaration,
kernel rule, generated authority, branch, worktree, or commit was changed by
PLAN-0.

## Persistent `/goal` Launch Prompt

The following prompt is ready to use. It explicitly authorizes creating or
reusing one dedicated local goal branch/worktree and making local validated
checkpoint commits there; it does not authorize pushing, merging, publishing,
rewriting history, or deleting worktrees.

Before pasting it, start a new Codex session from the Git root, review and
trust the root project hook through `/hooks`, and verify the shared archive as
described in `PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`.

```text
Kick off or continue implementing
docs/TYPESCRIPT_ELABORATOR_V3_2_MASTER_PLAN.md.

Treat it as the living master plan and decision ledger: determine the actual
current state from the active code, checks, plan status/ledger, and Git
worktree; then resume the in-progress slice or select the next
dependency-ready bounded slice according to the plan. Read and follow the root
AGENTS.md, the repository authority order, and, for every emdash2 change,
emdash2/AGENTS.md and the current v3.2 SOP. Perform the implementation—not
merely another general review—and keep the TypeScript kernel/elaborator,
Lambdapi diagnostics and probes, plan, and other affected authorities
synchronized.

The plan is revisable rather than immutable: correct, refine, split, reorder,
reject, or extend a slice when owner-position probes or implementation
evidence reveal a better architecture. Record the concrete evidence, changed
decision, dependencies, human-review status, and remaining work in the plan.
Preserve the distinction between the active Lambdapi mathematical
specification, the backend-neutral explicit Core, the candidate TypeScript
product kernel, and the optional Lambdapi conformance backend.

Commit a06433e57cba95e7d35f8577b7c71912862c3d25 is the
pre-implementation baseline for comparison and possible design backtracking
only. Work from the current state when it is that commit or a descendant,
including a temporary checkpoint descendant; do not reset to the baseline.
On every continuation, inspect staged and unstaged changes and
git worktree list, verify the baseline relationship, preserve unrelated work,
relocate symbols rather than relying on remembered lines, and run bounded
probes/checks and the proportional warning, audit, catalog, health, example,
and CI gates required by the SOP.

Use docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md. Local checkpoint commits on
the dedicated goal branch are authorized for this objective after each
bounded tranche has passed its proportional gates and the living plan ledger
is synchronized. Inspect the exact staged diff and do not include unrelated
pre-existing work. Creating or reusing one dedicated local goal branch and
worktree is also authorized: first inspect existing names and worktrees; if
this worktree contains only plan-scoped preparation changes, create the goal
branch in place so those changes are preserved; if it is clean, a sibling
goal worktree may be created at the current descendant and bootstrapped.
Never move, stash, copy, or commit unrelated dirty work to establish the goal
worktree. Use new commits or explicitly recorded experiment branches for
backtracking; do not amend, rebase, reset away, or otherwise rewrite
checkpoints. Do not push, merge to main, publish, release, create a PR, delete
branches, or remove worktrees unless separately requested by the user.

Continue making safe, plan-scoped progress until every plan row is genuinely
complete, rejected with durable evidence, or deferred behind a concrete
recorded prerequisite or human decision. If evidence exposes a blocker or
invalidates a planned step, document the result and pursue any independent
dependency-ready work that remains in scope. A need for human mathematical
review blocks only the affected slice; never guess a rule or a
displayed-to-ordinary equality.
```
