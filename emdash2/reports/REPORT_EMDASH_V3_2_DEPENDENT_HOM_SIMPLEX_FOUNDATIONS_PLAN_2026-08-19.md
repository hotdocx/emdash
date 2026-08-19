# Emdash v3.2 Dependent-Hom Simplex Foundations Plan

Date: 2026-08-19 (America/Toronto)

Plan-ID: `DEPENDENT-HOM-SIMPLEX-FOUNDATIONS-V3.2`

Status: **active implementation plan**. The completed coherent-nerve bridge
supplies the baseline. This continuation refocuses the open work on the
mathematical capability: a computational internal presentation of finite
simplices whose recursive structure is owned by `Hom_cat`, `Sigma_cat`,
`homd_`, and their whole internal actions. An internal code algebra is a later
enabling layer derived from the checked native dimensions; it is not the
definition of simplex semantics by itself.

Branch: `goal/dependent-hom-simplex-foundations-v3.2`

Worktree: `/home/user1/emdash1-dependent-simplex-v1`

Baseline: completed coherent-nerve checkpoint
`087e7080ddce308f932760c1403d4289f0d6535c`

Parent-Plan:
`REPORT_EMDASH_V3_2_COHERENT_NERVE_AND_DEPENDENT_SIMPLEX_BRIDGE_PLAN_2026-08-19.md`

Depends-On:

- `emdash3_2.lp`, especially equality/J, `Path_cat`, categorical
  composition, `Hom_cat(Sigma_cat(...))`, `homd_`, `homd_int`, Sigma maps,
  whole ordinary/displayed action, and represented composition;
- `emdash3_2_dependent_simplex_bridge.lp` for the native local triangle and
  iterable tetrahedron action;
- `emdash3_2_path_pseudo_laxity.lp` and
  `emdash3_2_path_groupoid_2horn_fillers.lp` for the groupoidal profile,
  retained higher Path action, and the bounded algebraic two-simplex;
- `emdash3_2_semisimplicial_face_codes.lp`,
  `emdash3_2_semisimplicial_index.lp`, `emdash3_2_simplex_shapes.lp`, and
  `emdash3_2_face_realization.lp` for the already-computing combinatorial and
  ordinal presentations; and
- active Foundations, canonical notation, current SOP, report index, and the
  persistent-goal Git workflow.

Side-Task-Ledger: `DHSF-00`, `DHSF-BASE-1`, `DHSF-NATIVE-2`,
`DHSF-PATH-3`, `DHSF-DIM4-4`, `DHSF-CODE-5`, `DHSF-DECODE-6`,
`DHSF-FACE-7`, `DHSF-ADEQUACY-8`, `DHSF-JOIN-9`, `DHSF-DOC-10`, and
`DHSF-CLOSE-11`.

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`; selected clarification response
`0067_2026-08-19T08-58-28Z_01a0193c-59a7-7b10-9ba5-e125a649ff37.md`.
That response and earlier archived discussion are recovery evidence only.
Active code/SOP and this evolving ledger are authoritative.

## 1. Objective

Establish the first internally computational foundations for simplicial
methods in functorial type theory by making the dependent-hom interpretation
precise and executable.

The conventional ordinal level is already available:

```text
OrdinalSimplex_cat(C,n)
  := Functor_cat(DirectedSimplex_cat(n),C).
```

The missing target is a native recursively dependent presentation, written
provisionally as

```text
DependentSimplex_cat(C,n),
```

whose formation, face observations, map action, and higher action compute
through the existing categorical owners:

```text
Hom_cat
Sigma_cat
homd_
homd_int
fdapp1_int_*
fapp1_func.
```

The intended long-range adequacy statement is

```text
OrdinalSimplex_cat(C,n)
  ~= DependentSimplex_cat(C,n),
```

with the exact strict/lax/groupoidal profile stated explicitly. This plan
does not assume that the same unqualified equivalence is correct for every
profile. Dimensions zero through four must determine the stable statement
before a uniform theorem or code decoder is promoted.

## 2. Refocused Mathematical Boundary

Keep four notions distinct:

| Layer | Meaning | Active boundary |
| --- | --- | --- |
| ordinal simplex shape | `[n] = DirectedSimplex_cat(n)` | active for every Nat `n` |
| ordinal mapping category | `Functor_cat([n],C)` | active for every `n`, with current prototype profile caveats |
| semisimplicial object | contravariant action of all injective faces | ingredients active; whole shape functor gated by join normal forms |
| dependent-hom simplex | a base cell plus a dependent cell above it, recursively | local triangle/tetrahedron active; complete dimensions and uniform internal code absent |

`DependentSimplex_cat(C,n)` is not a fifth unrelated definition. It is the
native dependent normal form whose relationship with the ordinal mapping
category is to be tested and then proved at the appropriate profile.

The code layer must remain subordinate to this objective. Its purpose is to
make a changing native boundary internally recursive in `n`; it must not
become a generic syntax for arbitrary emdash types or replace the semantic
owners above.

## 3. Canonical Native Decoder Principle

The active kernel already owns the decisive computation:

```text
Hom_{Sigma(E)}((x,u),(y,v))
  -->
Op(Sigma(
  p : Hom_K(x,y)^op,
  homd_(id_E,x,u,y,v)[p])).
```

Accordingly:

1. native dimensional presentations should be written first with canonical
   `Hom_cat` and `Sigma_cat` owners;
2. the existing `Hom_cat(Sigma_cat(...))` rule should expose the `homd_`
   layer;
3. a future code interpreter should decode to those canonical owners rather
   than duplicate the expanded Sigma/homd body;
4. action decoding should reuse `sigma_map_func`,
   `fdapp1_int_presheaf_arrow`, and `fapp1_func`; and
5. every claimed whole map must retain at least one next hom action.

This is a shallow Tarski-style code direction: codes describe only the finite
dependency/face recipe, while their interpretation is the active emdash
calculus itself.

## 4. Native Dimensions Before Codes

The first implementation tranche must specify and validate the intended
native forms through dimension four.

### Dimension zero

Identify the object-level presentation and the comparison with
`Functor_cat(Terminal_cat,C)`. Preserve the whole category and higher action;
do not replace it by a pointwise object equivalence only.

### Dimension one

Identify the total arrow presentation built from objects and `Hom_cat`, and
compare it with maps out of the join-built walking arrow. State whether the
comparison is strict-profile, general-lax, or both with different data.

### Dimensions two and three

Reuse, rather than duplicate:

```text
DependentTriangle_catd
DependentTriangle_cat
dependent_triangle_map
dependent_tetrahedron_map.
```

Place those local fixed-endpoint classifiers inside the complete boundary
telescope for a two- and three-simplex. Account for every face projection,
not only the top action.

### Dimension four

Construct the next complete source boundary and feed it through the retained
next action. This dimension is the decision gate for the eventual code
constructor: the code grammar must be extracted from a successful native
construction, not guessed before the boundary is understood.

## 5. Groupoidal Source-Coherence Bootstrap

The completed no-associativity tetrahedron probe established that the second
`homd_`/Sigma action maps an explicitly supplied associator and its dependent
filler. It did not construct that associator.

For a literal `Path_cat(A)`, the source associator must instead arise from
the groupoidal equality layer and be presented through the categorical API:

```text
J-derived path transitivity coherence
  -> categorical Path composition presentation
  -> whole represented-composition owner when non-circular
  -> dependent-hom tetrahedron source
  -> retained next action.
```

The bounded bootstrap audit is:

1. derive associativity of `eq_trans` by `ind_eqr`, without `comp_assoc`;
2. transport it to `comp_fapp0(Path_cat(A),...)` using the existing
   `path_comp_eq_trans` comparisons;
3. inspect `Rep_catd_func`, `path_comp_sec`, `path_comp_func`, and their
   generic compositor with the global associativity unifier disabled;
4. reject any represented owner that obtains its claimed associator
   circularly from `comp_assoc`;
5. compare a surviving whole represented component with the J-derived path;
6. feed the selected groupoidal source cell into the native dependent
   tetrahedron; and
7. retain the next action needed for the four-arrow boundary.

The J theorem may serve as the non-circular seed. A capped J theorem alone is
not the final recursive owner if a whole represented-composition action can
be recovered safely.

For arbitrary directed `C`, groupoidality alone cannot generate an
associator. The generic source must eventually be supplied by or projected
from a coherent directed composition structure. The Path adapter is the
first computational specialization and bootstrap test, not an illicit
definition of every category through equality.

## 6. Emdash-Specific Internal Codes

Only after Sections 4 and 5 determine the native successor pattern should a
curated internal code algebra be promoted.

The existing `FaceCode(p,n)` remains the combinatorial language answering
which face is selected. Do not duplicate it. The new layer should answer how
the data on that face is formed through dependent hom.

Provisional roles—not yet final Lambdapi signatures—are:

```text
DependentSimplexCode(n)           finite dependent-frame recipe
DependentBoundaryRef(c)           face/boundary references, reusing FaceCode
DependentBoundary_cat(C,c)        category of admissible boundary data
DependentFiller_catd(C,c)         native family of possible top fillers
decodeDependentSimplex(C,c)       Sigma total of boundary and filler
dependentSimplexNext(c,s,t)       next dependent-hom frame
dependentSimplexFace(alpha,c)     decoded face projection
dependentSimplexAction(F,c)       whole map and retained higher action.
```

The likely structural grammar is deliberately small:

```text
vertex
dependent-step(previous-code,source-reference,target-reference,orientation).
```

Actual vertices, arrows, and cells belong to decoded environments, not to an
untyped syntax tree. Strict/lax/Path profiles parameterize interpretation;
they should not multiply the code grammar.

The central decoder law should have the canonical orientation:

```text
decode(next(c,s,t))
  --> Hom_cat(decode(c),decodeRef(s),decodeRef(t))
  --> Op_cat(Sigma_cat(...,homd_(...))).
```

The second step is the existing kernel computation, not a duplicate code rule.

## 7. Relative Adequacy And Completeness

The first completeness claim is deliberately relative to the native finite
dependent-simplex grammar:

> Every finite nondegenerate simplex frame generated by the selected
> `Hom_cat(Sigma_cat(...))`/`homd_` recursion has a code, and decoding every
> code yields a native expression in that grammar.

This may initially be a metatheoretical induction documented and validated by
checked dimensions rather than one internal theorem. Record both directions:

```text
reify  : native dependent-simplex expression -> code
decode : code -> native dependent-simplex expression.
```

The stronger ordinal adequacy comparison is staged:

1. dimensions zero and one;
2. dimensions two and three at explicitly selected profiles;
3. dimension four as the recursive acceptance case; and
4. only then a variable-`n` comparison.

If the ordinary ordinal source is insufficient for a lax/coherent profile,
record the exact low-dimensional failure before introducing an oriental,
Gray-thickened source, or another shape. Such alternatives are consumer-led,
not assumed by this plan.

## 8. Face Action And Simplicial Consumers

The foundational dependent interface must support a whole face operation
whose intended form is

```text
dependentSimplexFace(alpha)
  : DependentSimplex_cat(C,n) -> DependentSimplex_cat(C,p)
```

for `alpha : FaceCode(succ p,succ n)`. It must reuse native projections and
retain higher action. `FaceCode` composition should own coface identities;
do not add an external family of simplicial equations.

After this foundation is active, later consumer plans may add:

- full simplex maps and degeneracies;
- generic boundaries, horns, and spines;
- algebraic Kan filler structures;
- Segal composition and completeness conditions;
- groupoidal/Kan and directed/Gray-oriented profiles; and
- a curated coinductive facade if a concrete consumer then needs it.

Those are not acceptance requirements for this bounded foundational plan.

## 9. Explicit Nonclaims

This plan does not initially claim:

- a complete simplicial, Segal, Rezk, Kan, complicial, or omega-coherence
  metatheory;
- degeneracies or the full simplex category;
- a general user-defined inductive/coinductive declaration mechanism;
- a deep syntax for arbitrary `Cat`, `Catd`, `Grpd`, or emdash expressions;
- that `Functor_cat([n],C)` has the same dependent presentation for every
  strict/lax/oplax profile;
- that a generic directed associator follows from the groupoidal Path API;
- that the active global strict functoriality/naturality or associativity
  prototype equations have been migrated; or
- a broad rewrite, unifier, Sigma eta, functor extensionality axiom, or
  independent coherence record.

## 10. Implementation Order

The dependency-respecting order is:

```text
owner/reuse audit and focused baseline
  -> non-circular Path associator seed
  -> represented-composition bootstrap audit
  -> complete native dimensions 0--3
  -> dimension-four boundary and retained action
  -> derive the minimal internal code grammar
  -> implement code decoder through native owners
  -> decoded face projections
  -> low-dimensional ordinal/dependent adequacy
  -> join-normal-form handoff or bounded implementation if still required
  -> authority synchronization and closeout.
```

Failed architectural probes remain ignored evidence. Promote only a stable
owner with a positive consumer, relevant negative/non-collapse case, and
proportional validation.

## 11. Validation Policy

Follow `emdash2/AGENTS.md` exactly:

- keep every Lambdapi invocation within 90 seconds;
- begin semantic changes with the smallest owner-position full-file probe;
- use `_` for inferred LHS slots unless a measured guard is documented by an
  adjacent `lhs-audit` comment;
- exercise every unifier with typed `eq_refl` and both reduction orders;
- compare quiet and warning-enabled runs for every rule/unifier candidate;
- treat warnings as diagnostic evidence rather than an automatic veto;
- pair positive computations with endpoint/index/non-collapse negatives;
- retain at least one next hom action for every whole claim;
- run focused source/reviewer checks, strict LHS audit, and affected catalog
  or health refreshes before a checkpoint; and
- eagerly avoid long aggregate checks unless their omission would block a
  trustworthy promotion or final integration boundary.

Documentation-only changes require exact diff, link/reference, and report
hygiene rather than unrelated kernel, TypeScript, browser, print, or
repository aggregates.

## 12. Git And Authorization Boundary

The user's instruction to proceed and start the corresponding persistent
goal is interpreted consistently with the completed parent goal as
authorization for:

- this one dedicated local child branch/worktree;
- implementation within this plan's scope; and
- SOP-compliant local checkpoint commits after bounded green tranches.

Every checkpoint must synchronize this ledger, stage only reviewed
plan-owned paths, and preserve every other worktree and branch.

No push, merge, PR, tag, npm/Zenodo publication, deployment, history rewrite,
branch deletion, worktree removal, or unrelated repository mutation is
authorized.

## 13. Execution Ledger

| Row | Status | Deliverable and acceptance boundary |
| --- | --- | --- |
| `DHSF-00` | complete | This refocused child plan is linked from the completed parent and report index. Recovery, Git, nonclaim, owner, and proportional-validation boundaries are frozen; the first non-circular Path seed is green quietly and warning-enabled. |
| `DHSF-BASE-1` | complete | The clean descendant worktree, bootstrap, relevant owner inventory, focused path/dependent source and profile reviewer baselines, archive verification, and exact current-source no-associativity copy are green. Quiet/warning runs of the copy and first consumer have zero delta at `1112/159`. No long aggregate baseline was run. |
| `DHSF-NATIVE-2` | pending | Specify complete native dependent presentations in dimensions 0--3, distinguishing global boundary totals from existing fixed-endpoint local triangle/tetrahedron classifiers. Retain whole and next-hom action. |
| `DHSF-PATH-3` | in progress; first public source slice promoted | `emdash3_2_dependent_simplex_path_associator.lp` materializes the two Path endpoint comparisons without a rule/unifier, exposes the whole represented compositor and readable invertible associator, preserves distinct J provenance, and retains one next action. Feed that selected owner into the native dependent tetrahedron/dimension-four source before closing the row. |
| `DHSF-DIM4-4` | pending | Construct the full next source boundary from the selected lower groupoidal/native owners, apply the retained dependent action, inspect all required faces, and reject any hidden reliance on the global associativity unifier. |
| `DHSF-CODE-5` | pending | Derive the smallest intrinsically indexed `DependentSimplexCode` grammar from dimensions 0--4; reuse `FaceCode`; record reification/decoding scope and profile parameters. No generic type syntax. |
| `DHSF-DECODE-6` | pending | Implement code decoding to canonical `Hom_cat`/`Sigma_cat` owners so existing rules expose `homd_`; reproduce the checked triangle/tetrahedron and dimension-four action with no duplicate semantic normal form. |
| `DHSF-FACE-7` | pending | Implement decoded face projections indexed by existing `FaceCode`, preserve composition through its owner, and retain higher action. Defer degeneracies. |
| `DHSF-ADEQUACY-8` | pending | Establish the strongest honest ordinal/dependent comparison through dimensions 0--3 and use dimension four as the recursion test; state exact strict/lax/Path scope and any shape/profile obstruction. |
| `DHSF-JOIN-9` | pending | Reassess `CNB-JOIN-NORMALFORM` only when the whole face/nerve consumer reaches it. Implement narrowly if dependency-ready; otherwise hand off with exact owner and consumer evidence. |
| `DHSF-DOC-10` | pending | Synchronize Foundations, canonical notation, current status, README/source inventories, report index, diagnostics/examples, and generated evidence only for promoted boundaries. |
| `DHSF-CLOSE-11` | pending | Complete every scoped row by implementation, evidence-backed rejection, or concrete deferral; run proportional final gates, record checkpoints and exact dirty state, and leave remote/integration/cleanup operations excluded. |

At most one row may be `in progress`. Architectural discovery may revise later
rows, but each revision must preserve the mathematical objective and record
why the former route was rejected or narrowed.

### 13.1 Launch And First Path Seed — 2026-08-19

The dedicated child worktree was forked from clean checkpoint `087e708` and
bootstrapped with the pinned pnpm workspace. The root Infinity Codex archive
verifies from its owning original worktree; the ignored archive is correctly
absent from a fresh Git worktree and was not copied or symlinked.

Focused baselines are green for:

```text
emdash3_2_path_pseudo_laxity.lp
emdash3_2_dependent_simplex_bridge.lp
examples/dependent_simplex_profiles.lp.
```

Report-header, active-reference, and source-TOC checks are also green. No
repository, kernel, example, print, browser, or TypeScript aggregate was run.

The ignored probe

```text
tmp/probes/dependent_simplex_path_assoc_seed.lp
```

derives

```text
eq_trans(f,eq_trans(g,h))
  = eq_trans(eq_trans(f,g),h)
```

by one right-based equality induction on `f`. Its reflexive case reduces to
`eq_refl(eq_trans(g,h))`. Quiet and warning-enabled runs are green:

```text
logs/probes/dependent_simplex_path_assoc_seed-20260819-052850.log
logs/probes/dependent_simplex_path_assoc_seed-20260819-052911.log.
```

The probe contains neither an `@comp_assoc` term nor a `unif_rule`. This
establishes the non-circular groupoidal seed only. It does not yet compare
the two categorical `comp_fapp0(Path_cat(A),...)` bracketings, recover a whole
represented-composition owner, feed the seed into the dependent tetrahedron,
or construct dimension four.

### 13.2 Exact No-Associativity And Represented-Owner Audit — 2026-08-19

The ignored current-source copy

```text
tmp/probes/dependent_simplex_no_assoc_full.lp
```

differs from `emdash3_2.lp` only at the generic associativity owner: it removes
the proof-time composition-associativity `unif_rule` and leaves `comp_assoc`
opaque instead of defining it by `eq_refl`. The paired consumer

```text
tmp/probes/dependent_simplex_path_assoc_no_assoc.lp
```

imports only that copy. Quiet runs pass, and the warning-enabled copy and
consumer each report exactly 1,112 critical-pair diagnostics and 159
replaceable-variable advisories:

```text
logs/probes/dependent_simplex_no_assoc_full-20260819-053501.log
logs/probes/dependent_simplex_path_assoc_no_assoc-20260819-053501.log
logs/probes/dependent_simplex_no_assoc_full-20260819-053525.log
logs/probes/dependent_simplex_path_assoc_no_assoc-20260819-053525.log.
```

The consumer derives two non-circular seeds by one `ind_eqr` on the first
path:

```text
eq_trans(f,eq_trans(g,h))
  = eq_trans(eq_trans(f,g),h)

h o (g o f)
  = (h o g) o f
  in Path_cat(A).
```

Both reduce to reflexivity when `f` is reflexive. The second theorem uses the
selected categorical Path unit rules directly and neither unfolds through
the first theorem nor references `comp_assoc`.

The same no-associativity consumer also forms the generic compositor of

```text
Rep_catd_func(Z) : Op_cat(Z) -> Catd_cat(Z)
```

and projects its displayed component at `h`. Thus the whole represented owner
is not bootstrapped from generic associativity merely to exist. Its exact
formal type is retained at the `functord_transport_lhs_func` and
`functord_transport_rhs_func` endpoints:

```text
logs/probes/dependent_simplex_path_assoc_no_assoc-20260819-053858.log.
```

The first attempted direct ascription to the readable orientation

```text
(h o g) o f -> h o (g o f)
```

fails with exactly two obligations: one formal source comparison and one
formal target comparison, both involving stable represented pre/postcomposition
heads. Evidence:

```text
logs/probes/dependent_simplex_path_assoc_no_assoc-20260819-054021.log.
```

This is not evidence that the whole owner is circular or unavailable. It is
the known non-transitive-unification boundary: the next probe must materialize
typed comparisons through rigid intermediate heads, following the existing
Path pseudo-laxity pattern. Do not add a runtime fold, reassociation rule, or
new unifier merely to make the readable ascription elaborate.

### 13.3 Represented Path Associator — 2026-08-19

The endpoint obstruction is resolved propositionally rather than by changing
normal forms. At a reflexive first path, the existing generic
`fapp1_id_path` compares `Rep_catd_func` action with displayed identity. The
already-selected postcomposition/raw-composition equality and one new
protected precomposition/raw-composition equality then expose the common
`h o g` component. Right-based path induction transports those two endpoint
comparisons to arbitrary `f`.

The promoted rule-free module

```text
emdash3_2_dependent_simplex_path_associator.lp
```

therefore retains the following ownership ladder:

```text
represented_assoc_transfd(f,g)
  : represented_assoc_lhs_funcd(f,g)
      => represented_assoc_rhs_funcd(f,g)

represented_assoc_cell(f,g,h)
  : represented_assoc_lhs(f,g,h)
      -> represented_assoc_rhs(f,g,h)

represented_assoc_higher_func(f,g,h0,h1)
  : Hom(h0,h1)
      -> Hom(represented_lhs(h0),represented_rhs(h1)).
```

For `Z = Path_cat(A)`, the formal endpoints compare propositionally with

```text
(h o g) o f
h o (g o f),
```

and `path_represented_assoc` is the resulting invertible equality in the
forward orientation. `path_cat_assoc_J` independently derives the reverse
orientation by J and `path_assoc_J_forward` reverses it; the reviewer checks
that this proof term is not definitionally the represented one. A wrong final
arrow is rejected at the retained formal target.

The general typed postcomposition comparison formerly marked `protected` in
`emdash3_2_path_pseudo_laxity.lp` is now public because this is its second
independent source module consumer; its body and computational behavior are
unchanged.

The final no-associativity probe passes quietly and warning-enabled with the
same `1112/159` diagnostics as its full-file comparison baseline:

```text
logs/probes/dependent_simplex_path_assoc_no_assoc-20260819-055955.log
logs/probes/dependent_simplex_path_assoc_no_assoc-20260819-060015.log.
```

The final promoted source, reviewer, and unchanged Path-pseudo-laxity warning
baseline pass at the same minimal active import-closure inventory of
`1112/159`:

```text
logs/probes/emdash3_2_dependent_simplex_path_associator-20260819-062349.log
logs/probes/dependent_simplex_path_associator-20260819-062349.log
logs/probes/emdash3_2_path_pseudo_laxity-20260819-062434.log.
```

The module and reviewer add no rule or `unif_rule`, so no new LHS or critical
pair is owned by the tranche. The remaining `DHSF-PATH-3` obligation is a
native dependent-simplex consumer of this selected source coherence; merely
having two readable associator proofs is not yet dimension four.

## 14. Completion Definition

This goal is complete when:

1. the native dimensions 0--4 are specified and checked to the strongest
   feasible whole-action boundary;
2. the groupoidal source-coherence bootstrap is either non-circular and
   active or blocked behind one precisely demonstrated owner gap;
3. the internal dependent-simplex code grammar and native decoder are
   implemented through the validated dimensions, or rejected with evidence
   identifying a smaller necessary foundation;
4. face action and low-dimensional ordinal adequacy are implemented to their
   honest profile boundary or deferred behind named, concrete prerequisites;
5. no code layer duplicates the active `Hom_cat`/`Sigma_cat`/`homd_`
   semantics;
6. affected authorities and focused evidence are synchronized; and
7. the worktree is reviewable with no unauthorized integration, publication,
   history rewrite, or cleanup.

Nearness to a context, token, or elapsed-time limit is not completion.
