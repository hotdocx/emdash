# Emdash v3.2 Coherent Nerve And Dependent-Simplex Bridge Plan

Date: 2026-08-19 (America/Toronto)

Plan-ID: `COHERENT-NERVE-DEPENDENT-SIMPLEX-V3.2`

Status: **active bounded implementation plan**. The architecture and baseline
reuse audit are complete; `CNB-LEVEL-2` is the first implementation row.

Branch: `goal/coherent-nerve-bridge-v3.2`

Worktree: `/home/user1/emdash1-coherent-nerve-v1`

Baseline: completed simplicial-substrate checkpoint
`e31a812850561f9a6717f11354fd512eaed17671`

Depends-On:

- `emdash3_2.lp`, especially `Functor_cat`, whole precomposition,
  `homd_`, `homd_int`, dependent Sigma, the ordinary/displayed internal
  action, `fapp1_compositor`, and the recursive second action;
- `emdash3_2_simplex_shapes.lp` for Nat-indexed join-built ordinal shapes,
  `join_map_func`, strict face dictionaries, and the selected cofaces through
  dimension two;
- `emdash3_2_semisimplicial_face_codes.lp`,
  `emdash3_2_semisimplicial_index.lp`, and
  `emdash3_2_semisimplicial_diagrams.lp` for the global combinatorial index,
  representable standard semisimplices, and category/groupoid-valued diagrams;
- the completed internal-laxity/groupoidal-realization plan for the
  no-associativity dependent tetrahedron and Path-realized pseudo
  specialization; and
- current Foundations, canonical notation, current SOP, and the persistent
  Git experimentation workflow.

Side-Task-Ledger: `CNB-00`, `CNB-BASE-1`, `CNB-LEVEL-2`,
`CNB-TETRA-FACE-3`, `CNB-JOIN-REC-4`, `CNB-FACE-GEN-5`, `CNB-NERVE-6`,
`CNB-CELL-7`, `CNB-BRIDGE-8`, `CNB-PROFILE-9`, `CNB-GENERIC-10`,
`CNB-DOC-11`, and `CNB-CLOSE-12`.

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`, especially archived decisions
`0060_2026-08-19T02-13-50Z_01a017c3-1ce8-7232-b9ca-a48584117ad9.md`
and
`0061_2026-08-19T03-03-43Z_01a017f5-0de5-7cc3-887e-90e254494f7f.md`.
Those responses are recovery evidence only. Active code/SOP and this evolving
ledger are authoritative.

## 1. Objective

Construct and validate the missing computational bridge between:

1. the combinatorial standard simplex represented by the internal
   semisimplicial index;
2. the ordinal mapping category `Functor_cat([n],C)`; and
3. the recursive base-cell-plus-dependent-cell presentation already computed
   by `homd_`, dependent Sigma, and the internal action.

The intended whole comparison is

```text
Hom(Delta[n],CoherentNerve(C))
  ~= CoherentNerve(C)[n]
  ~= RecursiveSimplex(C,n).
```

The first equivalence should be existing Yoneda after the nerve is assembled.
The second is the new mathematical content. It must preserve face action and
retain higher hom action, not merely compare object carriers.

The architecture is generic in `n`. Dimension three is the first decisive
acceptance test, because it forces an explicit base associator and a dependent
tetrahedral filler over that associator. It is not the permanent definition of
the generic construction.

## 2. The Four Distinct Current Presentations

Keep these meanings separate:

| Presentation | Current expression | Meaning |
| --- | --- | --- |
| ordinal shape | `DirectedSimplex_cat(n)` | the ordinary category `[n]` with `n+1` vertices |
| representable semisimplex | `StandardSimplex(succ n)` | Yoneda `Delta[n] = Hom(-,[n])` over the injective simplex index |
| category of coherent maps | `Functor_cat(DirectedSimplex_cat(n),C)` | candidate category of `n`-simplices in `C` and transfors between them |
| dependent cell presentation | second and later `homd_`/Sigma iterations | a base cell with a dependent cell above it, recursively |

`Sigma_cat(StandardSimplex(succ n))` is an already-expressible category of
faces and face factorizations, subject to the current Grothendieck orientation.
Because representable fibres are path-discrete, it captures combinatorial
incidence rather than the target-dependent nontrivial higher filler.

The bridge must relate the latter two presentations without identifying
either with the face-incidence total by a broad rewrite.

## 3. Intended Generic Nerve

In ordinary dimension notation, the level classifier is

```text
CoherentNerveLevel(C,n)
  := Functor_cat(DirectedSimplex_cat(n),C).
```

For an injective face code

```text
alpha : FaceCode(succ p,succ n),
```

the intended action is precomposition by a strict realization:

```text
realize_face(alpha)
  : DirectedSimplex_cat(p) -> DirectedSimplex_cat(n)

alpha^*
  : CoherentNerveLevel(C,n) -> CoherentNerveLevel(C,p).
```

When generic face realization and its composition computation exist, these
levels should assemble into

```text
CoherentNerveRaw(C)
  : Functor(Op_cat(SemiDeltaPlus_cat),Cat_cat).
```

The augmented object zero needs an honest empty ordinal shape. This is now a
concrete consumer for the previously deferred augmented-empty endpoint.
Before adding a new shape owner, audit `Path_cat(Empty_grpd)`, functors out of
it, and any existing initial-category facade. If the empty boundary cannot yet
retain the required whole action, a positive-dimension nerve facade may be
used temporarily, but it must not be mislabeled as a functor on all of
`SemiDeltaPlus_cat`.

The public Cat-valued presheaf facade remains distinct from the raw whole
functor-category owner, following the existing semisimplicial realization
policy.

## 4. Join Mapping Data Is The Recursive Step

The shape recursion is already

```text
[0]     = Terminal_cat
[n + 1] = [n] star Terminal_cat.
```

The current `join_elim_func` constructs a functor from `A star B` from:

```text
first  : Functor(A,C)
second : Functor(B,C)
cross  : one whole internally natural cross-cell first ==> second.
```

For `B = Terminal_cat`, this is precisely a cone over the old simplex. Define
or expose a reusable whole classifier schematically as

```text
JoinMapData(A,C)
  = (F : Functor(A,C),
     x : Functor(Terminal_cat,C),
     cross : WholeCross(F,x)).
```

The candidate recursion theorem is

```text
Functor_cat(Join_cat(A,Terminal_cat),C)
  ~= JoinMapData(A,C).
```

Construction from right to left is the existing join eliminator. The missing
left-to-right observation restricts a functor to both join branches and acts
on `join_cross_transf`. Beta/eta and retained hom action determine whether the
comparison is a transparent `DefIso`, an `OmegaEquivAlong Cat_cat`, or a
weaker first-stage observation interface.

Do not postulate a tuple of pointwise cross arrows or an external naturality
family. The cross datum must remain at the existing whole profunctor/transfor
owner.

## 5. Relation Of Join Data To `homd_`

For a fixed new vertex `x`, the whole cross-cell is a coherent family of
arrows from every point of the old simplex to `x`. Its component over an old
base arrow is exactly the kind of cell classified by `homd_`.

The recursive bridge should therefore factor as

```text
map out of [n+1]
  -> whole join-cone data
  -> base simplex plus internally represented dependent hom data.
```

At dimensions two and three, the observations must reduce to the already
selected owners:

```text
n = 2  -> fapp1_compositor
n = 3  -> explicit base associator
          plus the next fdapp1_int_hom_fapp0 dependent filler.
```

The completed no-associativity probe is the semantic and computational
baseline. Do not promote its diagnostic capped pre/post rules, a standalone
tetrahedron constant, or a manual pentagon record.

## 6. Why Dimension Three Is The Acceptance Test

The bounded observations are:

```text
n = 0  vertex
n = 1  arrow
n = 2  compositor triangle
n = 3  coherence between two triangle pastings.
```

The tetrahedron must expose all four triangle faces by restriction. Its top
cell must retain:

```text
kappa_assoc
  : h o (g o f) = (h o g) o f

Lambda
  : transport(kappa_assoc,right_pasting) -> left_pasting.
```

The dependent component must be the existing recursive internal-action
projection. Global proof-time associativity may remain installed for the
prototype, but the acceptance probe must not rely on it; use the established
no-associativity comparison technique when the endpoint distinction matters.

Passing dimension three demonstrates one genuinely recursive step. It does
not alone establish a variable-`n` theorem. The variable-`n` row opens only
after the dimension-three data comes from the same join/cone owners intended
for induction.

## 7. Strict, Lax, And Path Profiles

The same bridge should have three readings:

```text
general target Hom   -> directed lax simplex
selected strict map  -> ordinary commuting simplex
Path_cat target      -> invertible pseudo simplex.
```

The selected face realizations themselves are strict-profile maps. The target
simplex classifier should reuse the ambient functor/transfor tower; do not
duplicate it for each profile.

The current kernel remains a documented prototype in which historical global
strict functoriality/naturality endpoint comparisons coexist with nonidentity
laxity cells. This plan does not perform the large profile-aware migration.
Every promoted claim must distinguish endpoint conversion from collapse of
the laxity cell itself.

## 8. Lean/Mathlib Baseline And Adaptation Boundary

Lean/Mathlib already provides:

- the full simplex category as finite monotone maps;
- face and degeneracy generators, normal forms, and epi-mono factorization;
- the semisimplex inclusion;
- the ordinary nerve `N_C[n] = Functor([n],C)`;
- strict Segal and quasicategory results for that nerve; and
- a homotopy-coherent nerve of simplicial categories via enriched functors
  from simplicial thickenings.

These are reference semantics and engineering baselines, not evidence that
emdash should copy their proof-record architecture. The intended emdash
contribution is computational ownership:

```text
one whole internal action
  -> compositor
  -> next coherence
  -> later coherence,
```

with groupoidal specialization obtained by landing in `Path_cat`.

Do not claim that Lean cannot formalize the mathematics. The narrower claim to
test is whether emdash can make the nerve and its coherent-cell reading
compute through one recursively iterable functorial-type-theory mechanism,
where ordinary Lean normally uses structures, propositional laws, and
proof-producing simplification.

Useful primary/current references include:

- Mathlib `SimplexCategory.Basic`, `GeneratorsRelations.NormalForms`, and
  `SemiSimplexCategory`;
- Mathlib ordinary `Nerve`, `StrictSegal`, and `Quasicategory.Nerve`;
- Mathlib `SimplicialNerve` for the enriched homotopy-coherent nerve;
- Street and Johnson--Walters on orientals and the higher nerve;
- Riehl--Shulman on directed shapes, Segal types, and Rezk types; and
- Kolomatskaia--Shulman on display/cone presentations of semisimplicial
  types.

No Lean source is copied into the active kernel. If the ordinary ordinal plus
internal-action approach fails at dimension three, document the exact failure
before considering an emdash oriental or simplicial thickening.

## 9. Explicit Nonclaims

This plan does not initially construct or claim:

- the full simplex category or degeneracies;
- a generic boundary, horn, spine, Segal, Rezk, Kan, or complicial interface;
- a Street oriental or a simplicial thickening;
- a coinductive `SST` facade;
- a complete omega-coherence theorem;
- a broad join eta rewrite or category-head identification;
- a migration of the historical global strict endpoint rules;
- a TypeScript or text-parser surface; or
- integration, publication, or deployment.

Degeneracies are not fundamentally blocked. They are postponed because the
current bridge needs only injective face restriction, and because unitors add
a separate normal-lax/strict-profile question. A later full-simplex plan
should prefer normalized finite monotone maps or another computational normal
form over an unnormalized quotient of face/degeneracy words.

## 10. Proposed Module Strategy

Do not place this bridge in `emdash3_2.lp` unless a focused probe proves a
genuinely missing generic owner.

Candidate one-way modules are:

```text
emdash3_2_coherent_nerve_levels.lp
  variable-n ordinal mapping-category facade and augmented-shape audit

emdash3_2_tetrahedron_faces.lp
  four selected triangle cofaces and their join-built realization

emdash3_2_join_mapping_recursion.lp
  whole restriction/extension interface for maps out of A star 1

emdash3_2_coherent_nerve.lp
  raw semisimplicial nerve, only after generic face realization

emdash3_2_dependent_simplex_bridge.lp
  recursive cell observation and dimension-three comparison.
```

Names may be consolidated after probes show the actual dependency boundary.
Keep examples one-way and reviewer-facing. Do not create a public module for a
failed candidate or a facade whose claimed whole action is absent.

## 11. Validation Policy

Follow the nested Lambdapi SOP:

- inspect staged and unstaged changes separately at every continuation;
- use ignored owner-position probes before active rules;
- keep every Lambdapi target under 90 seconds;
- write inferred rule slots as `_` unless a measured subject-reduction guard
  requires a rigid term, then add the adjacent `lhs-audit` annotation;
- compare quiet and warning-enabled runs for each candidate rewrite family;
- exercise every unifier with typed `eq_refl` and both-order probes;
- pair positive computations with direction/index/non-collapse negatives;
- retain at least one next hom action for every claimed whole owner;
- run source/reviewer checks and the strict LHS audit before each checkpoint;
- update check registries, current status, source inventories, and this ledger
  only for promoted owners; and
- avoid long aggregate checks unless omitting one would genuinely block
  trustworthy promotion.

The focused baseline on 2026-08-19 is green for
`emdash3_2_simplex_shapes.lp`, `emdash3_2_semisimplicial_diagrams.lp`, and
`examples/dependent_hom_laxity.lp`. No aggregate baseline was run.

## 12. Git And Authorization Boundary

The user authorized this dedicated branch/worktree, implementation,
persistent goal, and SOP-compliant local checkpoints. Every checkpoint must:

- contain one bounded green tranche;
- synchronize this ledger and affected active authorities;
- stage only reviewed plan-owned paths; and
- preserve all other branches and worktrees.

No push, merge, PR, tag, npm/Zenodo publication, deployment, history rewrite,
branch/worktree deletion, or unrelated repository mutation is authorized.

## 13. Execution Ledger

| Row | Status | Deliverable and acceptance boundary |
| --- | --- | --- |
| `CNB-00` | complete | Promoted the generic architecture, dimension-three acceptance boundary, Lean comparison, nonclaims, module order, validation policy, and Git boundary into this living plan. |
| `CNB-BASE-1` | complete | Dedicated worktree forked from clean `e31a812`; workspace bootstrap and focused shape/diagram/dependent-hom baselines are green. |
| `CNB-LEVEL-2` | active | Promote a variable-`n` `CoherentNerveLevel_cat(C,n)` facade and audit the augmented-empty shape without claiming a whole semisimplicial nerve. Check dimensions 0--3 and retained Functor-category hom action. |
| `CNB-TETRA-FACE-3` | pending | Construct the four strict-profile triangle cofaces `Delta[2] -> Delta[3]` from join maps, with code/functor agreement and selected face-of-face equations. No generic decoder claim. |
| `CNB-JOIN-REC-4` | pending | Probe and, if supported, promote whole observation/extension for maps out of `A star Terminal`; reuse the existing cross transfor and retain one hom action. Do not add a broad join eta rewrite. |
| `CNB-FACE-GEN-5` | pending decision gate | Decide whether raw face-code recursion plus join maps can construct `realize_face` for variable dimensions with identity/composition computation. If not, record the exact prerequisite and keep the tetrahedral bridge bounded. |
| `CNB-NERVE-6` | pending on generic face realization | Assemble `CoherentNerveRaw(C)` by precomposition and cross the public Psh facade only through existing projections. Retain whole face and next action. |
| `CNB-CELL-7` | pending | Define the recursive join-cone/dependent-cell observation through dimensions 0--3. Triangle must be `fapp1_compositor`; tetrahedron must reuse the established second `homd_`/Sigma action. |
| `CNB-BRIDGE-8` | pending | Compare the ordinal mapping-category and recursive-cell presentations wholely at the strongest justified level. Require all four tetrahedral faces and the top dependent filler; reject an object-only coincidence as final completion. |
| `CNB-PROFILE-9` | pending | Validate general directed-lax, selected strict, and `Path_cat` pseudo readings without duplicating classifiers or collapsing the generic laxity cell. |
| `CNB-GENERIC-10` | pending decision gate | If rows 4--9 use one stable recursive owner, formulate/prove the variable-`n` induction. Otherwise record whether the missing ingredient is join uniqueness, generic face realization, recursive boundary formation, or a richer oriented simplex shape. |
| `CNB-DOC-11` | pending | Synchronize Foundations, canonical notation, status/source inventories, reviewer examples, and report index only for checked promoted results. |
| `CNB-CLOSE-12` | pending | Record exact checkpoints, focused evidence, warning deltas, deferred prerequisites, clean state, and safe continuation. No integration/publication. |

## 14. Completion Definition

This goal is complete when every row is complete or explicitly deferred
behind a named, evidence-backed prerequisite; the variable-`n` interface has
not been replaced by a hard-coded tetrahedron API; every promoted whole owner
retains the action it claims; dimension three either computes the four faces
and dependent top filler from generic owners or records a precise architectural
failure; strict and Path specializations state their exact scope; the living
ledger and active documentation agree; the worktree is clean at green local
checkpoints; and no excluded Git/publication/aggregate operation has occurred.
