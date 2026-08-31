# TypeScript/emdash Formal Presented Modules And CAS Delegation Plan

Date: 2026-08-31

Plan-ID: `TS-EMDASH-FORMAL-PRESENTED-MODULES-CAS`

Status: active living plan on a dedicated branch/worktree; architecture
reviewed, exact formal owner audit and implementation pending.

Baseline: `e665301bf40a68f136833ba2b7e9416ace55c79e`

Branch: `goal/formal-presented-modules-cas-v3.2`

Worktree: `/home/user1/emdash1-formal-presented-modules-cas-v1`

Decision-Response-Evidence:

- `infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a05916-1430-7761-ad91-c0944eec23eb`
- `infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a05925-b359-77c1-8140-f0b1c9fa788a`

## Purpose

This plan governs the first formal computational presentation spine shared by
the proof assistant and the matrix/module CAS:

```text
finite free vectors
  -> column-oriented matrices and matrix action
  -> explicit presentation-agreement witnesses
  -> parent-aware formal reification
  -> module-membership delegation
  -> syzygy and bounded-resolution equations
  -> concrete category/operation reinterpretation
  -> formal adoption and backend conformance.
```

The goal is deliberately below a quotient-module or Abelian-category claim.
It supplies the concrete representation needed by the existing CAP-like
doctrine/tower/compiler layer and by future formal complexes, Čech
differentials, and homology.

## CAP/homalg Architectural Contract

Direct vectors and matrices are the concrete backend model, not the public
limit of the architecture. The selected layering is:

```text
exact ring/matrix algorithms
  -> computational presentations
  -> typed AlgebraOperation / graph
  -> computable category instance
  -> doctrine and derived operations
  -> constructor towers / reinterpretations
  -> categorical compiler
  -> explicit Core realization and adoption.
```

This mirrors the successful CAP/homalg separation among computable ring and
matrix primitives, module presentations, concrete categories, categorical
doctrines, generic algorithms, Freyd/category-constructor towers, and
specialization. Emdash additionally retains exact formal goal identity,
realizations, computation artifacts, and checked/trusted adoption.

The goal targets architectural subsumption of selected CAP/homalg workflows,
not API compatibility or equal package breadth. GAP filters, globals, dynamic
dispatch, and arbitrary host-AST recovery are not the public design.

## Authority And Existing Substrate

Formal authority remains active Lambdapi v3.2 under `emdash2`, especially:

- `FiniteFamily`, Nat recursion, Sigma, equality, and truncation owners;
- commutative-ring carriers and element operations;
- finite sum/dot-product constructions; and
- the generic category/functor/transfor nucleus.

There is currently no active Lambdapi matrix, module, presentation, complex,
or homology owner. Any new one-way module follows `emdash2/AGENTS.md`, the
current status/Foundation/canonical-syntax authorities, owner-position
probing, warning comparison, LHS audit, checks/catalog/health synchronization,
and bounded formal CI.

Computational authorities already include:

- exact coefficient domains and matrix spaces;
- row-major `AlgebraMatrix` with multiplication and kernel bases;
- field-linear presented modules, morphisms, relation witnesses, kernels, and
  cokernels;
- polynomial free modules, Gröbner bases, membership, Schreyer syzygies, and
  resolutions;
- presented-algebra modules `R^n/(IR^n+N)` and semilinear maps;
- categorical doctrines, constructor towers, Freyd/CoFreyd models,
  reinterpretations, and program lowering; and
- the completed proof–CAS request/adoption and classified assumption-source
  infrastructure.

The root guidance and persistent-goal Git workflow remain mandatory. `main`
was fast-forwarded only to the completed affine-localization/Čech baseline;
orthogonal path-cubical/strictness work remains excluded.

## Formal Representation

### Vectors

Use the existing finite-family representation:

```text
CommRingVector(R,n) := FiniteFamily(|R|,n).
```

Implement transparent Nat-recursive zero, addition, negation, subtraction,
and scalar multiplication. No `Fin`, list, array, second tuple encoding, or
new inductive declaration is selected.

### Matrices

Use columns as finite vectors:

```text
CommRingMatrix(R,rows,columns)
  := FiniteFamily(CommRingVector(R,rows),columns).
```

A `rows x columns` matrix therefore represents:

```text
R^columns -> R^rows.
```

Matrix application is the linear combination of columns. Composition maps
the left matrix action over the columns of the right matrix:

```text
A : rows x middle
B : middle x columns
A o B : rows x columns.
```

This orientation matches the existing CAS relation-matrix convention, where
columns are relations in the free generator space, and avoids transpose or
indexed lookup in the foundational calculus.

### Presentations Without Quotient Overclaim

A presentation is retained as ranks plus a relation matrix:

```text
A : Matrix(R,generators,relations).
```

For raw vectors `v,w : Vector(R,generators)`, define explicit agreement data:

```text
PresentationAgreement(A,v,w)
  := Sigma c : Vector(R,relations), A*c = v-w.
```

This is computational relation evidence. It is not judgmental equality, a
path in a quotient module, or an inhabitant of a not-yet-selected cokernel
type. Names, documentation, and tests must preserve that distinction.

A later presentation morphism may retain matrices `F,W` and the law:

```text
F o R_source = R_target o W.
```

This matches the existing CAS `relationWitness` structure and prepares a
Freyd-style category, but the exact categorical tranche remains audit-gated.

## Formal Computation Policy

Vector and matrix operations should be transparent definitions over existing
Nat/finite-family recursion. Ring reassociation, commutation, and
distributivity remain theorem-level paths. No rewrite or unification rule is
presumed.

If a projected consumer fails to compute, first inspect transparent
definitions and existing finite-family projections. Any proposed rule requires
the full nested SOP, positive typed consumer, relevant noncollapse case,
warning comparison, and subject-reduction evidence.

## Formal Reification

Define a parent-aware realization binding:

- one computational coefficient/presented algebra to one formal ring;
- exact rank and row/column orientation;
- canonical coefficient/quotient-element reification;
- vectors to ordered `FiniteFamily` terms;
- row-major CAS matrices to column-oriented formal matrices;
- relation matrices and candidate coefficient vectors; and
- exact formal equation targets.

Reification must be deterministic, reject foreign parents/dimensions/order,
and retain whole computational source data. Equivalent normalized inputs emit
the same explicit Core.

## First Consumer: Module Membership

Use a whole membership/normalization result, not the projected Boolean zero
decision. Retain tested vector, original generators, basis,
transformation/combination coefficients, remainder, and reduction counts.

For a selected positive coefficient vector, target:

```text
linearCombination(generators,coefficients) = vector.
```

Negative membership retains the canonical nonzero remainder and leaves the
goal open. For modules over a presented algebra, the realization must
explicitly classify any trusted algebra-relation semantics; it may not assume
that an arbitrary formal ring realizes `R/I`.

## Second Consumer: Syzygies

For each selected Schreyer generator `s`, target:

```text
G*s = 0-vector.
```

The CAS whole syzygy result and every selected coefficient vector remain
available. A classified assumption source may batch the equations, but every
opaque claim retains an independent decision and exact computation artifact.

## Third Consumer: Resolution Equations

Reify matrices in a bounded Schreyer resolution and target every adjacent
equation:

```text
d_i o d_(i+1) = 0-matrix.
```

This establishes a formal chain-shaped presentation. It does not yet claim a
chain-complex category, exactness, freeness/projectivity universality,
homology, or a resolution theorem.

## Categorical Compatibility

The goal must not terminate with a category-blind matrix API. At least one
representative consumer must connect the new representation to the existing
categorical engine:

- ranks as free-module objects;
- matrices as morphisms;
- matrix multiplication as composition;
- presentation matrices as Freyd-style objects;
- relation witnesses as morphism well-definedness data; and
- one generic categorical operation/program lowering to the direct algebra
  graph with structural agreement.

Generic kernel/cokernel/homology algorithms should continue depending on
categorical roles rather than matrix internals. A full formal Abelian-category
claim remains later work.

## Proposed Implementation Sequence

1. Exact formal/CAS orientation and owner audit.
2. Formal finite-vector definitions and focused computation.
3. Formal column matrices, action, zero, and composition.
4. Presentation-agreement and syzygy equation classifiers.
5. TypeScript signature mirrors and parent-aware reifiers.
6. Positive/negative polynomial-module membership delegation.
7. Schreyer syzygy equation delegation and classified batch source.
8. Bounded resolution matrices and adjacent-zero equations.
9. Concrete categorical reinterpretation/program-lowering consumer.
10. Portable artifacts, direct/graph agreement, and focused live Lambdapi
    conformance.

## Implementation Ledger

| Row | Status | Dependency | Deliverable and acceptance boundary |
| --- | --- | --- | --- |
| `FPM-PLAN-0` | complete; checkpoint `67bb128` | completed affine formal bridge at `e665301` and reviewed CAP/homalg continuation | living plan, isolated branch/worktree, exact baseline, layering, representation, validation, Git limits |
| `FPM-AUDIT-1A` | complete; checkpoint `877823b` | `FPM-PLAN-0` | exact formal owner gap, matrix orientation, CAS consumer map, smallest Lambdapi module, categorical acceptance target |
| `FPM-VECTOR-2A` | complete; checkpoint `877823b` | audit | formal vectors and transparent zero/add/neg/subtract/scale computation |
| `FPM-MATRIX-3A` | complete; checkpoint `877823b` | vector | formal column matrices, action, zero, composition, typed positive/noncollapse consumers |
| `FPM-PRESENTATION-4A` | complete; checkpoint `877823b` | matrix | presentation/agreement and syzygy/composite-zero classifiers without quotient overclaim |
| `FPM-REIFY-5A` | in progress; Core reifier checkpoint pending | formal owners | exact signature mirrors, vector/matrix/presentation reification, dimension/parent/order diagnostics |
| `FPM-MEMBERSHIP-6A` | pending | reifier | whole positive/negative module-membership delegation and formal selected equation |
| `FPM-SYZYGY-7A` | pending | membership | Schreyer syzygy equations and classified finite adoption source |
| `FPM-RESOLUTION-8A` | pending | syzygy | bounded resolution matrix terms and all adjacent-zero equations |
| `FPM-CATEGORY-9A` | pending | matrix/presentation | representative concrete-category/reinterpretation/compiler lowering with direct structural agreement |
| `FPM-CONFORMANCE-10A` | pending | all active rows | portable artifacts, focused formal checks, live Lambdapi acceptance, proportional final audit |

Rows may be split, rejected, or deferred only with durable evidence and an
updated plan. Every completed row requires focused positive/negative tests,
proportional validation, synchronized decisions/results, and a local
checkpoint.

## Initial Decisions

| Decision | Status | Rationale |
| --- | --- | --- |
| `D-FPM-001` | accepted | Direct vectors/matrices are the concrete computable model beneath, not instead of, CAP-like categorical abstraction. |
| `D-FPM-002` | accepted | The formal API is ring-generic; field and polynomial-module computations are concrete instances. |
| `D-FPM-003` | accepted | Vectors reuse `FiniteFamily`; matrices are finite families of columns. |
| `D-FPM-004` | accepted | CAS row-major matrices reify by explicit transpose into the formal column representation while preserving dimensions. |
| `D-FPM-005` | accepted | Presentation agreement is explicit coefficient/equation data, not quotient-module equality. |
| `D-FPM-006` | accepted | Whole membership, syzygy, and resolution computations remain primary; Boolean/projection facades are derived. |
| `D-FPM-007` | accepted | Generic categorical algorithms depend on roles/doctrines, not matrix representation internals. |
| `D-FPM-008` | accepted | One categorical lowering/direct-agreement consumer is part of this goal's completion boundary. |
| `D-FPM-009` | accepted | Classified exact-Core assumption sources handle selected equations; no certificate framework is required. |
| `D-FPM-010` | accepted | Abstract semantic modules, quotient types, full Freyd/Abelian formalization, chain-complex categories, exactness, homology, and Čech cohomology remain later layers. |
| `D-FPM-011` | accepted | New Lambdapi mathematics follows the complete nested SOP; no rule is assumed necessary. |
| `D-FPM-012` | accepted | Local validated checkpoint commits are authorized on this branch; push, merge, publication, release, history rewriting, and cleanup are not. |
| `D-FPM-013` | accepted | `main` was fast-forwarded only through `e665301`; orthogonal path-cubical/strictness work remains excluded. |
| `D-FPM-014` | accepted after audit | Formal matrices are columns; CAS row-major storage is an implementation detail handled by reification. |
| `D-FPM-015` | accepted after audit | Transparent Nat/finite-family definitions suffice for vector arithmetic, matrix action/composition, presentation agreement, syzygy, and adjacent-zero classifiers; no rewrite/unification rule is added. |
| `D-FPM-016` | accepted after audit | The initial formal module is a presentation calculus, not an abstract semantic module or quotient construction. |
| `D-FPM-017` | accepted during reification | Whole polynomial-module membership reifies original generator vectors as formal matrix columns and selected coefficients as the formal input vector; the target is the exact matrix-action equation. |

## Initial Reifier Result

`src/v3_2/algebra_formal_finite_module.ts` now constructs explicit Core for
polynomial-module vectors, column matrices, selected membership coefficients,
and the matrix-action equality target. It preserves the CAS component order
and transposes only the conceptual row-major/column-family boundary.

The first native membership operation retains the whole coefficient and
remainder result rather than projecting a Boolean. A focused one-generator
positive case reifies and recomputes successfully, while the corresponding
constant vector has a nonzero remainder. Root typecheck and the focused test
pass. Exact LF signature mirrors, proof-goal adoption, broader dimension
negatives, syzygies, and resolution artifacts remain in the active row.

## Formal Spine Result

The audited rule-free one-way module
`emdash2/emdash3_2_commutative_algebra_finite_modules.lp` now defines finite
vectors, componentwise operations, column matrices, matrix application, zero
matrices, composition, explicit presentation agreement, syzygy equations, and
adjacent composite-zero equations over an arbitrary formal commutative ring.

The reviewer example checks visible two-column action and explicit agreement
construction, and rejects collapse of a visible column to the zero matrix.
Both owner and example pass bounded Lambdapi checking. No new rule, warning
family, Core owner, quotient module, or categorical overclaim is introduced.
The exact audit is recorded in
`docs/TYPESCRIPT_EMDASH_FORMAL_PRESENTED_MODULES_CAS_OWNER_AUDIT.md`.

## Validation

- Documentation-only rows: exact diff/link hygiene.
- TypeScript rows: workspace check, focused affected tests, typecheck, and
  affected lint.
- Lambdapi rows: owner-position probe, positive/noncollapse consumer, warning
  comparison, strict LHS audit if rules exist, checks/catalog/health updates,
  and bounded target/CI gates required by `emdash2/AGENTS.md`.
- Every Lambdapi target remains bounded to 90 seconds.
- Final bridge artifacts receive focused live Lambdapi checks.
- Avoid `check:all`, book/print/package/release gates, and repeated full
  TypeScript aggregates outside a genuinely affected boundary.
- Carry forward the known unrelated stale source-pin failures from the recent
  full TypeScript run rather than absorbing them into this goal.

## Git Authorization

The user authorizes this dedicated branch/worktree and local validated
checkpoint commits according to the living plan. This does not authorize
push, merge, rebase, amend, reset, history rewriting, publication, release,
PR creation, branch deletion, worktree removal, or orthogonal integration.

## Non-Goals

- proving the CAS correct or centering proof certificates;
- a semantic quotient module or arbitrary quotient/HIT decision;
- calling presentation agreement “module equality”;
- hard-coding categorical algorithms against matrices;
- full formal Abelian/Freyd/complex/homology theory;
- formal Čech differentials or cohomology;
- GAP/CAP API compatibility or dynamic filter emulation;
- arbitrary AST recovery, parser, hosted service, or publication; or
- push, merge, release, or worktree cleanup.

## Completion Boundary

The goal completes when every active row is implemented, audit-rejected, or
explicitly deferred behind a concrete prerequisite; formal vector/matrix/
presentation operations compute and pass focused formal checks; membership,
syzygy, and bounded-resolution equations flow through the proof–CAS bridge;
at least one categorical program structurally agrees with the direct backend;
all artifacts and assumptions are deterministic and classified; required live
conformance passes; and every bounded tranche is checkpointed.

## Persistent `/goal` Launch Prompt

Work in `/home/user1/emdash1-formal-presented-modules-cas-v1` on
`goal/formal-presented-modules-cas-v3.2`. Implement the formal finite-vector,
column-matrix, presentation-agreement, module-membership, syzygy, resolution,
and categorical-compatibility objective with every evolving owner,
orientation, formal equation, bridge adapter, trust classification,
categorical reinterpretation, validation result, checkpoint, and completion
condition delegated to this plan. Preserve baseline `e665301`, exclude
orthogonal path-cubical/strictness work, and re-read current source/SOP/plan on
every continuation. Treat direct matrices as the concrete implementation
beneath the existing CAP-like doctrine/tower/compiler layer; do not claim a
quotient module or full Abelian category. Add formal mathematics only under
the nested Lambdapi SOP, use proportional affected checks, make only local
validated checkpoint commits, and do not push, merge, publish, release,
rewrite history, remove worktrees, or broaden unrelated formal/kernel theory.
