# ELAB-0: TypeScript Elaboration Boundary For emdash v3.2

Date: 2026-07-23
Status: implemented ELAB-0 draft; architecture and trust choices await human
review

## Question

What is the smallest useful TypeScript implementation that compiles a direct
surface AST into the active emdash v3.2 owner calculus, and should the MVP call
Lambdapi its kernel or replace Lambdapi with the existing TypeScript
rewrite/unification engine?

This RFC answers only the first vertical slice. It does not select a parser,
port the whole v3.2 signature, change a Lambdapi rule, or delete the older
TypeScript prototype.

## Evidence Baseline

The evidence was recovered in the authority order required by `AGENTS.md` and
`emdash2/AGENTS.md`:

1. `emdash2/emdash3_2.lp` owns the active definitions, rewrites, and
   proof-time comparisons.
2. `emdash2/emdash3_2_eq1_hom_action.lp`,
   `emdash2/emdash3_2_eq1_evidence_property.lp`,
   `emdash2/emdash3_2_nat_arithmetic.lp`, and
   `emdash2/emdash3_2_walking_end_hit.lp` are one-way extensions. None changes
   the ordinary application signatures selected below.
3. `emdash2/emdash3_2_checks.lp` exercises the explicit applications and their
   positive and negative boundaries.
4. The current SOP says that the global `fapp*`/`tapp*` calculus solely owns
   ordinary functoriality and naturality.
5. Foundations maps `F[x]`, `F[f]`, and `eta[f]` to `fapp0`,
   `fapp1_fapp0`, and `tapp1_fapp0`.
6. The canonical-syntax report is authoritative for mathematical notation but
   explicitly is not yet a parser grammar.
7. Appendix G of the checked book records the intended optional elaboration
   stage and classifies the parent TypeScript implementation as feasibility
   evidence, not a current compiler.

At repository commit `3965df1d221ff14ee93e2496aaece010b685b708`,
the worktree had empty staged and unstaged diffs. The following pre-edit
baselines passed:

```text
./scripts/pnpmw run check:ts
  workspace contract, TypeScript, ESLint, 152 tests / 43 suites

EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check
  active kernel, Nat, WalkingEnd, hom-action, evidence-property, diagnostics
```

The current status report records a substantially larger active formal
surface than the parent prototype: 758 kernel symbols, 602 rewrite rules, and
61 proof-time unification rules. Matching a few familiar operation names is
therefore not evidence that the old TypeScript engine implements v3.2.

## Active Owner Signatures Selected For ELAB-0

The selected slice copies no mathematical law. It lowers against these
existing signatures:

```text
fapp0 :
  [A B : Cat] -> F : Functor(A,B) -> X : Obj(A) -> Obj(B)

fapp1_fapp0 :
  [A B : Cat] -> F : Functor(A,B) ->
  [X Y : Obj(A)] -> f : Hom_A(X,Y) -> Hom_B(F[X],F[Y])

tapp1_fapp0 :
  [A B : Cat] -> [F G : Functor(A,B)] ->
  [X Y : Obj(A)] -> eta : Transf(F,G) -> f : Hom_A(X,Y) ->
  Hom_B(F[X],G[Y])
```

The literal serialized targets are:

```lambdapi
@fapp0 A B F X
@fapp1_fapp0 A B F X Y f
@tapp1_fapp0 A B F G X Y eta f
```

`tapp1_fapp0` is an active typed owner and naturality target, while its source
comment still describes the general external ordinary-naturality API as
reserved. ELAB-0 may construct the typed application; it must not invent a new
reduction for it.

## Inventory Of The Parent TypeScript Prototype

### Reusable now as implementation patterns

| Mechanism | Evidence | ELAB-0 treatment |
| --- | --- | --- |
| Direct TypeScript AST construction | `src/types.ts` constructors and the current tests | retained as the surface entry point; no string parser is required |
| Explicit versus implicit application | `Icit`, `App`, `Pi`, and implicit-argument tests | retained as a distinct plicity axis |
| Binder variation metadata | `BinderMode` and mode-aware context tests | represented independently from plicity; no broad old mode law is imported |
| Bidirectional organization | `infer`, `check`, and typed constraint generation in `src/elaboration.ts` | retained as the intended growth pattern after the first schema-directed slice |
| Holes, occurs check, and higher-order pattern unification | `src/state.ts`, `src/unification.ts`, and focused tests | candidate for later extraction behind a generic AST interface |
| Rewrite/unification separation | stored rewrite rules versus `UnificationRule` and the active Lambdapi SOP | retained as a design distinction, not as v3.2 rule authority |
| Proof-state traversal | `src/proof.ts` | candidate for later reuse after traversal is decoupled from the stale term union |
| Test harness | `node:test` suites wired through `tests/main_tests.ts` | reused directly |

### Not reusable as v3.2 authority

- `FunctorTypeTerm`, `MkFunctorTerm`, `NatTransTypeTerm`, `SetTerm`,
  `HomCovFunctorIdentity`, and the old implicit-slot table encode an earlier
  categorical API.
- The old `Term` union mixes generic lambda-calculus nodes with stale
  category-specific nodes. Every generic traversal switches over the entire
  union.
- Holes are solved by mutating `ref` fields, constraints and rule registries
  are global, and standard-library reset functions install the old theory.
  This is useful executable evidence but not yet a small reviewable trusted
  kernel.
- The old normalizer and coherence check know only the rules installed by the
  parent standard library. They do not mirror the current 19,201-line v3.2
  source or its one-way module graph.
- The old parser covers a small lambda/Pi/let language and is not the
  canonical categorical surface.

ELAB-0 therefore lives beside the prototype under `src/v3_2/`. It neither
imports the old category nodes nor deletes them.

## Selected Architecture

```text
direct TypeScript surface AST
        |
        | scope lookup and owner-schema constraint recovery
        v
typed ELAB-0 result
        |
        | owner-directed lowering
        v
explicit v3.2 kernel-target AST
        |
        +----> deterministic Lambdapi serialization + source map
        |                         |
        |                         v
        |                  bounded Lambdapi check
        |
        `----> candidate TypeScript MVP kernel
               (conformance-limited until its graduation criteria pass)
```

The successful API returns the explicit term, its explicit target type, and a
serializable checked-probe representation. The target AST contains:

- local or active-symbol references;
- applications whose complete argument list records the declared plicity of
  every slot;
- Pi and lambda binders for the next slices;
- source/provenance metadata distinguishing written and recovered arguments.

The first surface AST contains references and the three selected application
forms. A context binding records its type and binder metadata. Parsing strings
is deliberately out of scope.

### Binder model

Plicity and variation are separate:

```text
plicity   = explicit | implicit
variation = functorial | natural | object-only
```

This models all five concepts named in the handoff without incorrectly making
them mutually exclusive. The v3.2 book settles `k :^n K` for the natural/index
role, but a full user grammar for additional mode annotations remains
unsettled. ELAB-0 retains variation as typed metadata and does not serialize
it as invented Lambdapi syntax.

### Normalization policy

ELAB-0 performs no categorical normalization. It compares only the rigid
symbolic categories and endpoints present in the typed surface context. All
v3.2 conversion, rewrite, and proof-time comparison behavior remains with
Lambdapi.

### Diagnostic policy

TypeScript reports unbound names, unexpected operand kinds, and rigid
category/endpoint mismatches at source spans before serialization. The
serializer emits a generated-line-to-source map. Parsing arbitrary Lambdapi
diagnostic formats back through that map is a later tranche.

## Do We Need Lambdapi For The MVP?

There are three different questions behind the word *need*:

1. **Must the deployed TypeScript product invoke Lambdapi on its request
   path?** No. TypeScript is the better implementation language for surface
   syntax, typed macros, source maps, incremental state, customized
   automation, and a responsive product kernel.
2. **Should Lambdapi remain an executable specification and differential
   oracle while that kernel is built?** Yes. It already contains the settled
   owner calculus and is the only current implementation against which a new
   mirror can measure acceptance and conversion.
3. **Can the parent TypeScript engine simply be relabelled the v3.2 kernel?**
   No. Its generic mechanisms are useful, but its categorical theory and
   trusted boundary have not been brought into parity with v3.2.

In particular, it is premature for the existing TypeScript prototype to serve
directly as the trusted emdash v3.2 kernel:

1. it implements an older and much smaller categorical signature;
2. its generic algorithms are coupled to stale semantic nodes and global
   mutable state;
3. it has no current rule manifest corresponding to the active owners,
   runtime rewrites, proof-time comparisons, or one-way module boundary;
4. its tests establish selected behavior, not parity with the active
   Lambdapi acceptance and conversion relation;
5. no independent TypeScript trusted core, subject-reduction story,
   differential corpus, or frozen MVP fragment has been selected.

The recommended route is therefore a **TypeScript-native MVP with a
conformance phase**, not a permanent Lambdapi runtime dependency:

- TypeScript owns elaboration, macros, diagnostics, and the candidate product
  evaluator/checker, with surface macros kept outside its small trusted core.
- Lambdapi remains the reference acceptance oracle while the TypeScript core
  is incomplete or has not met the graduation criteria below.
- Lambdapi checks belong in differential tests, CI, and selected development
  milestones. They may be batched and cached; the design does not require
  spawning Lambdapi after every keystroke or in the eventual deployed path.
- `emdash3_2.lp` can continue as the rapid executable specification and
  experimental design workbench. A later TypeScript product kernel can mirror
  a deliberately frozen, minimized fragment rather than the whole historical
  development.

Thus “go through Lambdapi” is required for ELAB-0 conformance evidence, not as
the final product architecture. The old rewrite/unification implementation is
raw material for the candidate TypeScript core; reusing it should mean
extracting the generic algorithms behind the new explicit IR, not extending
its stale category nodes.

Treating the TypeScript implementation as the authoritative MVP kernel becomes
defensible only after a separate RFC and implementation supply at least:

1. a frozen MVP signature and owner/rule manifest;
2. a small trusted core isolated from surface macros and metavariable state;
3. capture-safe substitution and deterministic scope/metavariable handling;
4. an explicit classification of runtime rules versus proof-time comparison
   authority;
5. positive, negative, conversion, and malformed-rule differential tests
   against Lambdapi over the frozen fragment;
6. stated subject-reduction, termination/confluence, and trust assumptions
   proportionate to the claims made;
7. a human decision that the measured parity and maintenance tradeoff justify
   changing the acceptance authority.

This keeps the TypeScript-kernel option open. ELAB-0 does not make that
product/trust decision accidentally.

## ELAB-0 Acceptance Tests

The focused tests must establish:

1. plicity and variation are represented independently;
2. `fapp0(F,x)` recovers `A` and `B`;
3. `fapp1_fapp0(F,f)` recovers `A`, `B`, `X`, and `Y`;
4. `tapp1_fapp0(eta,f)` recovers `A`, `B`, `F`, `G`, `X`, and `Y`;
5. a wrong source category is rejected with a source-located TypeScript
   diagnostic;
6. serialization contains all explicit v3.2 arguments and a source map;
7. one generated positive consumer containing all three heads is accepted by
   Lambdapi;
8. a deliberately corrupted explicit target with a wrong-endpoint arrow is
   rejected by Lambdapi, demonstrating the trust boundary.

The Lambdapi integration tests are focused and opt-in for the TypeScript-only
gate. The documented focused command runs them with a timeout no greater than
60 seconds. The repository-wide gate separately checks every active formal
module while leaving these two generated-probe tests skipped.

## Human Review Points

These choices are recorded rather than inferred as mathematics:

1. **Acceptance authority:** approve the staged TypeScript-native kernel with
   Lambdapi conformance, or retain Lambdapi as the ongoing acceptance
   authority.
2. **Binder surface:** decide which functorial/object-only annotations, if any,
   join the settled `:^n` notation as user syntax.
3. **Trusted-core boundary:** decide whether a future TypeScript mirror shares
   the elaborator's AST or consumes only the explicit target AST. This RFC
   recommends the latter.
4. **Check cadence:** choose interactive per-declaration, batched, cached, or
   CI-only Lambdapi confirmation based on measured latency.
5. **Next vertical slice:** choose a current consumer before adding displayed
   action, metavariables, or normalization. No kernel rewrite follows merely
   from the existence of the TypeScript layer.

No mathematical design choice above changes an active v3.2 declaration or
normal form.

## Implementation Record

The implementation is isolated from the parent `Term` union:

- `src/v3_2/kernel.ts` defines the explicit target IR, the audited plicity
  manifest for the selected active symbols, provenance, structural comparison,
  and deterministic Lambdapi serialization.
- `src/v3_2/surface.ts` defines the direct source-located surface AST, ordered
  typed context, orthogonal binder metadata, and rigid dependency validation.
- `src/v3_2/elaborator.ts` recovers the implicit owner slots, produces the
  explicit target applications and types, and reports source-located surface
  errors.
- `src/v3_2/probe.ts` constructs declarations/assertions, emits a generated
  line source map, and runs a checker in a unique temporary directory with a
  hard timeout of at most 60 seconds.
- `src/v3_2/index.ts` exposes the boundary without changing the legacy root
  exports.
- `tests/v3_2_elab0_tests.ts`, wired through `tests/main_tests.ts`, covers the
  five pure TypeScript properties and two opt-in Lambdapi boundary checks.

Validation on 2026-07-23:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw exec node --require ts-node/register \
  --test tests/v3_2_elab0_tests.ts
  5 passed; 2 opt-in checks skipped

EMDASH_RUN_LAMBDAPI_PROBES=1 ./scripts/pnpmw exec node \
  --require ts-node/register --test tests/v3_2_elab0_tests.ts
  7 passed; generated positive consumer accepted; corrupted target rejected

EMDASH_PROBE_TIMEOUT=30s emdash2/scripts/probe.sh <positive consumer>
  exit 0

EMDASH_PROBE_TIMEOUT=30s emdash2/scripts/probe.sh <wrong-endpoint consumer>
  exit 1 as required; assertion failed at the generated assertion

EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all
  workspace contract, TypeScript, ESLint
  159 tests / 44 suites: 157 passed, 2 opt-in checks skipped
  41 active Lambdapi kernel/example files passed
  formal diagnostics, audits, catalogs, and book checks passed
```

The temporary probe consumers were removed after the bounded checks. No
package manifest, lockfile, active Lambdapi source, or parent category node was
changed.
