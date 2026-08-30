# TypeScript/emdash Affine Formal-Computational Bridge Plan

Date: 2026-08-30

Plan-ID: `TS-EMDASH-AFFINE-FORMAL-BRIDGE`

Status: living architecture and implementation ledger; dedicated branch and
worktree created; formal-owner audit is the first dependency-ready row.

Baseline: `5df79d356d003d3c1831ff1b93a2c593f299f75b`

Branch: `goal/affine-formal-computational-bridge-v3.2`

Worktree: `/home/user1/emdash1-affine-formal-bridge-v1`

## Purpose

This plan governs the now-consumer-backed bridge between the completed focused
TypeScript affine CAS and the active Lambdapi/emdash v3.2 formal structures.
The finite affine-cover and Cech implementation has removed the earlier design
ambiguity: the concrete computational data that may need formal realization is
now known.

The target path is:

```text
AlgebraPresentedAlgebra and quotient elements
                  |
                  v
selected formal commutative-ring/algebra owner
                  |
                  v
unimodular affine cover realization
                  |
                  v
principal-localization charts and overlap maps
                  |
                  v
ordered signed Cech diagram
                  |
                  v
backend-neutral explicit Core
                  |
                  v
deterministic Lambdapi emission / conformance
```

This is concrete implementation work, not a general proof-certificate project.
The CAS remains independently useful and the native TypeScript engine remains
the computational default.

## Authority And Prerequisites

The computational input is the completed affine plan
`docs/TYPESCRIPT_EMDASH_AFFINE_ALGEBRAIC_GEOMETRY_PLAN.md` at the baseline
above. In particular, the bridge consumes:

- canonical polynomial quotient rings and elements;
- relation-checked presented algebra maps;
- principal localizations and basic-open charts;
- affine schemes and morphisms;
- presented tensor products and affine fiber products;
- finite affine covers and ordered signed Cech data; and
- backend-neutral computation graphs and staged categorical lowering.

The formal mathematical authority is the active Lambdapi v3.2 development
under `emdash2`, in the order and workflow required by `emdash2/AGENTS.md`.
The bridge must inspect current owners and consumers before naming or extending
them. Historical responses and plans are recovery evidence, not authority over
active code.

For TypeScript LF work, follow
`docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md` and the active explicit-Core,
checker, transfer, and scale authorities it names. Build backend-neutral Core
first. Lambdapi emission is a conformance backend, not the semantic source of
the TypeScript architecture.

## Governing Principles

1. Reuse current formal owners. Do not invent a parallel formal commutative
   algebra, Zariski cover, localization, or Cech API from memory.
2. Separate computational realization from mathematical proof. A bridge may
   carry explicit data or a clearly named trusted-computation status without
   pretending to be a kernel-checked certificate.
3. Do not add opaque propositional-equality bridges or new kernel primitives as
   a workaround. Any formal equality path must derive from existing
   computation, existing proof structure, or a separately reviewed trust
   boundary outside ordinary kernel claims.
4. Reification is explicit and parent-aware. A CAS quotient element may be
   realized only after selecting the formal ring/algebra object and the map
   from computational generators to formal terms.
5. Preserve whole data. Cover elements, coefficients, combination, localized
   charts, canonical maps, overlap maps, simplex indices, and face signs remain
   available after translation.
6. Deterministic explicit Core is the primary interchange. Direct Lambdapi
   strings are not the architectural starting point.
7. The first bridge consumer is the actual finite basic-open cover, not an
   abstract universal adapter with no execution path.
8. No CAS correctness certificate is required. Optional checked reconstruction
   may be added only where it improves a concrete consumer.
9. Validation is proportional and owner-focused. `check:ts` and repository-wide
   aggregates remain explicitly deferred.
10. Local checkpoints are permitted on this isolated branch; push, merge,
    publication, and history rewriting are not.

## Concrete Bridge Data

The completed affine consumer exposes exactly these candidate inputs:

1. `AlgebraPresentedAlgebra`
   - canonical quotient parent;
   - polynomial generators and relation ideal;
   - reduced Gröbner owner; and
   - exact quotient-element remainders.
2. `AlgebraAffineCover`
   - ambient coordinate algebra;
   - ordered quotient cover elements;
   - quotient coefficients whose combination is canonical one;
   - retained whole unimodular computation; and
   - actual localized charts.
3. `AlgebraPrincipalLocalization`
   - adjoined-inverse presentation;
   - canonical source map;
   - distinguished inverse; and
   - checked inverse equation.
4. `AlgebraCechSimplex` and `AlgebraCechFace`
   - strictly increasing chart indices;
   - product localization;
   - removed index and sign; and
   - validated restriction algebra map.

The bridge must not silently discard this data to a Boolean theorem flag.

## Proposed Implementation Sequence

### 1. Audit current formal owners

Inspect the actual Lambdapi and TypeScript declarations for:

- commutative rings and algebras;
- polynomial or quotient presentations, if present;
- `CommRingUnimodularPresentation` or its current replacement;
- Zariski/basic-open cover structures;
- principal localizations and localization maps;
- internal diagrams, simplicial/Cech structures, signs, and chain data;
- computational/trusted realization markers already in use; and
- current TypeScript LF realization, class-instance, explicit-Core, and
  deterministic-emission mechanisms.

Produce an exact owner/consumer map and a gap classification. This audit is a
design input, not a substitute for implementation.

### 2. Backend-neutral computational realization

Define an explicit association conceptually shaped like:

```text
AffineFormalRealization {
  computationalAlgebra: AlgebraPresentedAlgebra
  formalAlgebra: explicit Core term / selected formal owner
  generatorRealizations: ordered explicit Core terms
  elementReifier: canonical quotient element -> explicit Core term
  status: explicit-data | trusted-computation | checked
}
```

The exact type and naming follow the audit. The realization must validate
parent identity and generator arity. It must not globally register a formal
term for a structurally unrelated quotient parent.

### 3. Quotient-element and polynomial reification

Reify canonical sparse representatives using the selected formal coefficient,
addition, multiplication, negation, power, and generator owners. Reification
is deterministic and normal-form-driven. Equivalent computational
representatives must emit the same explicit Core term after quotient
normalization.

If the active formal development already owns polynomial or quotient
presentations, reuse those constructors. Otherwise, initially realize elements
into a separately supplied formal algebra through generator terms; do not
postulate a formal quotient-ring implementation merely to finish the adapter.

### 4. Unimodular-cover adapter

Translate:

- ordered cover elements;
- ordered quotient coefficients;
- their canonical combination equal to one; and
- the selected ambient formal algebra

into the existing formal unimodular/Zariski owner. Prefer definitional or
existing proof reconstruction when the formal ring computation supports it.
If not, stop at an explicit computational/trusted realization boundary rather
than inserting an opaque equality constant into the kernel theory.

### 5. Localization and chart realization

Relate the computational adjoined-inverse presentation, canonical map,
distinguished inverse, and inverse equation to current formal localization or
basic-open structures. Retain chart identity and the map from the ambient
formal algebra.

### 6. Cech realization

Translate ordered simplex indices, product localizations, restriction maps,
removed positions, and signs into the closest existing internal diagram,
simplicial, or cochain representation. This row realizes the finite cover
diagram; it does not claim sheaf cohomology or exactness.

### 7. Deterministic Core and Lambdapi emission

Construct explicit backend-neutral Core through existing LF builders and
declaration/workspace APIs. Lambdapi emission must be deterministic and use
current symbol ownership/visibility. Do not recover semantics from TypeScript
function ASTs or rely on handwritten string templates as the main path.

### 8. Focused conformance examples

Start with:

```text
D(x), D(1-x) covering A^1
```

Then cover affine two-space by:

```text
D(x), D(y), D(1-x-y).
```

Check canonical quotient reification, the unimodular coefficients, chart
localizations, overlap restrictions, signs, emitted Core, deterministic
Lambdapi text, and focused Lambdapi checking.

## Implementation Ledger

| Row | Status | Dependency | Deliverable and acceptance boundary |
| --- | --- | --- | --- |
| `BRIDGE-PLAN-0` | complete | completed affine goal and reviewed recommendation | this living plan, dedicated branch/worktree, architecture, staged rows, validation policy, and Git limits |
| `BRIDGE-AUDIT-1A` | pending; next selected row | active TypeScript/Lambdapi authorities | exact formal owner/consumer map, current symbol inventory, trust/equality options, gap classification, and selected first consumer |
| `BRIDGE-CONTRACT-1B` | pending | `BRIDGE-AUDIT-1A` | backend-neutral parent-aware realization contract, status boundary, deterministic generator/element reification interfaces, and negative diagnostics |
| `BRIDGE-REIFY-2A` | pending | `BRIDGE-CONTRACT-1B` | canonical polynomial/quotient-element reifier into explicit Core with representative invariance and coefficient/generator coverage |
| `BRIDGE-COVER-3A` | pending | `BRIDGE-REIFY-2A`, current formal unimodular owner | concrete affine-cover adapter carrying ordered elements, coefficients, combination, and selected formal ring/algebra realization |
| `BRIDGE-LOCALIZATION-4A` | pending | `BRIDGE-COVER-3A`, current formal localization owner | chart/localization realization, ambient maps, distinguished inverses, and overlap product localizations |
| `BRIDGE-CECH-5A` | pending | `BRIDGE-LOCALIZATION-4A`, current diagram/Cech owner | ordered simplex and signed restriction realization into existing formal diagram/cochain structures |
| `BRIDGE-EMISSION-6A` | pending | representative bridge consumer | deterministic explicit-Core declarations/workspaces and Lambdapi emission without handwritten semantic templates |
| `BRIDGE-CONFORMANCE-7A` | pending | all preceding active rows | two concrete cover examples, focused TypeScript tests, deterministic snapshots, bounded Lambdapi checks, warning comparison, and final boundary audit |

Rows may be split into lettered subtranches. A row completes only after
implementation, focused positive and negative tests, proportional validation,
synchronized decisions/results, and a local checkpoint.

## Initial `BRIDGE-AUDIT-1A` Tranche

The first bounded tranche is read-mostly and owns:

- complete reading of `emdash2/AGENTS.md` and the formal report authority map;
- exact `rg`-based inventory of candidate Lambdapi symbols and their owning
  modules;
- exact inventory of TypeScript LF/Core realization and emission APIs;
- direct consumer tracing for current unimodular, Zariski, localization,
  diagram, simplicial, and Cech structures;
- classification of which affine data already has a formal owner;
- a decision on the first realizable vertical slice;
- owner-position probes only if static inspection leaves an actual reduction
  or visibility question; and
- a synchronized audit result in this plan or a directly linked report.

No formal symbol, rewrite/unification rule, or bridge API is added until this
audit selects its owner and equality/trust boundary.

## Validation Policy

Use proportional checks only:

- focused TypeScript tests and root typecheck for bridge files;
- affected-file ESLint and workspace check at checkpoints;
- exact diff and staged-diff hygiene;
- for Lambdapi changes, the owner-position probe, warning comparison, catalog
  or health updates, and bounded target required by `emdash2/AGENTS.md`;
- every Lambdapi command bounded to at most 90 seconds;
- deterministic Core/Lambdapi snapshots for concrete examples; and
- no `check:ts`, `check:all`, print, book, browser, package-release, or
  repository-wide aggregate unless a later explicit integration request
  changes the boundary.

Wiring focused tests into `tests/main_tests.ts` does not justify the aggregate
runner.

## Git Authorization And Checkpoints

The user authorizes local checkpoint commits on this dedicated branch as work
progresses. Each checkpoint requires a bounded green tranche, synchronized
living plan, and an exact staged diff without unrelated work.

This authorization does not include pushing, merging, rebasing, amending,
history rewriting, publication, release, PR creation, branch deletion, or
worktree removal. Formal/kernel experimentation must use new commits and
isolated probes rather than destructive backtracking.

## Non-Goals

- proving the native CAS implementation correct;
- introducing a general certificate framework;
- adding formal quotient rings, localizations, or schemes without a current
  owner and concrete need;
- adding opaque equality axioms to make an adapter typecheck;
- treating trusted computation as definitional or checked proof;
- redesigning the completed affine CAS object model without counterevidence;
- publishing the contributor APIs; or
- integrating the branch into `main`.

## Completion Boundary

This goal is complete when every bridge ledger row is implemented, validated,
documented, and checkpointed; both concrete covers realize deterministically
through explicit Core and bounded Lambdapi conformance; trust or checked status
is explicit; no parallel formal geometry API or opaque equality workaround was
introduced; and the native CAS remains independent of the bridge. It is not
complete merely because one formal term can be emitted.
