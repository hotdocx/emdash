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
| `DHSF-NATIVE-2` | complete | `emdash3_2_dependent_simplex_native_dimensions.lp` defines the honest flagged tower `C`, `PathOut_C(x0)`, `PathOut(e01)`, and `PathOut(t012)` through dimension three. Derived whole map functors iterate the existing displayed hom/Sigma/pullback-total action and retain another hom action. Visible constructors expose all lower faces; a typed represented-source conjugation exposes face 123 and the top filler. A single global mixed-variance all-simplex total is explicitly not claimed. |
| `DHSF-PATH-3` | complete | `emdash3_2_dependent_simplex_path_associator.lp` materializes both generic raw-bracketing endpoint comparisons without a rule/unifier, exposes the whole and raw-endpoint represented associators, specializes invertibly to Path while preserving distinct J provenance, and retains one next action. `emdash3_2_dependent_simplex_represented_source.lp` then projects that selected cell at a constructor-visible Sigma spine to the native `(kappa,lambda)` tetrahedron, maps it through the existing whole next action with both component betas, and retains another hom action. |
| `DHSF-DIM4-4` | complete at the honest recursive boundary | `emdash3_2_dependent_simplex_dimension4.lp` adds one more flagged PathOut classifier and whole map action. Visible data expose faces 0123/0124/0134; the typed readable Hom(Sigma) split exposes face 0234 and retains the 1234/top-filler frame. A full-constructor negative proves that this residual requires recursively carried readable lower endpoints rather than a dimension-specific eta or rewrite. Another hom action remains available. |
| `DHSF-CODE-5` | complete | `emdash3_2_dependent_simplex_codes.lp` defines `RawDependentSimplexCode(C,n,K)` intrinsically indexed by its decoded category: zero has `K=C`, and successor at `x:Obj(K)` has `K=PathOut_K(x)`. The public dependent Sigma hides `K`; existing `FaceCode(succ p,succ n)` supplies boundary references; `DependentSimplexEndpointView` retains typed formal/readable endpoints. No arbitrary Cat syntax or second semantic grammar is introduced. |
| `DHSF-DECODE-6` | complete | `emdash3_2_dependent_simplex_code_map.lp` recursively maps a raw code along `F:C->D`, returning a target code and whole decoded functor. Zero returns `F`; successor maps the stored flag and reuses `pathout_map_func`. Selected codes recover native maps through dimension four, endpoint views map by `eq_ap`, and another hom action remains iterable without duplicate native-map rules. |
| `DHSF-FACE-7` | complete at the whole-action boundary | `emdash3_2_dependent_simplex_faces.lp` recursively interprets existing nonempty `FaceCode`s against intrinsic codes. Skip gives fixed-flag constant action, `keep(skip ...)` uses target projection, and `keep(keep ...)` reuses `pathout_map_func`. Visible triangle faces and selected public composition compute, higher action is retained, and opaque direct/sequential whole-functor equality is precisely left unforced. |
| `DHSF-ADEQUACY-8` | in progress | Establish the strongest honest ordinal/dependent comparison through dimensions 0--3 and use dimension four as the recursion test; state exact strict/lax/Path scope and any shape/profile obstruction. |
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
normal forms. The generic typed postcomposition/raw-composition comparison
first identifies the whole represented source with composition of the two
represented precomposition functors. Existing fibre projection and one new
protected precomposition/raw-composition equality then expose
`(h o g) o f`. The opposite base-composition comparison similarly exposes
`h o (g o f)` on the target side. These paths work for arbitrary directed
`Z`; no Path induction or categorical associativity is needed for them.

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

The subsequent generic refinement adds
`represented_assoc_lhs_agrees_raw`, `represented_assoc_rhs_agrees_raw`, and
`represented_assoc_readable_cell`. Equality-induced arrows conjugate the
formal whole component to a directed cell

```text
(h o g) o f -> h o (g o f)
```

for arbitrary `Z`. In a Sigma total whose three input edges are kept in their
native `Struct_sigma(p,alpha)` presentation, the existing `Hom(Sigma)` rule
reduces both raw composites and the readable cell projects directly as the
second dependent-Sigma pair `(kappa,lambda)`. The focused constructor-visible
probe is green:

```text
logs/probes/dependent_simplex_represented_assoc_components-20260819-064903.log.
```

If the three total edges are first hidden behind arbitrary opaque arrow
variables or named non-constructor endpoints, the projection intentionally
stops because the kernel has no Sigma eta. This is positive evidence for the
planned intrinsic dependent-simplex code: its decoder must retain native
constructor visibility rather than request a broad projection rule.

### 13.4 Constructor-Visible Represented Source — 2026-08-19

The promoted rule-free module

```text
emdash3_2_dependent_simplex_represented_source.lp
```

turns the successful probe into one reusable source boundary. For four Sigma
vertices and three native `dependent_triangle` arrows it exposes:

```text
dependent_spine3_left_triangle
dependent_spine3_right_triangle
dependent_spine3_assoc_cell
dependent_spine3_assoc_tetrahedron
dependent_spine3_assoc_map.
```

The first two terms are the raw bracketings of the three-edge spine. The
third is the generic represented directed cell at those literal endpoints.
The fourth supplies its `sigma_Fst` and `sigma_Snd` projections to the
existing `dependent_tetrahedron` constructor, rather than postulating a
parallel coherence record. The final term is the existing
`dependent_tetrahedron_map` specialized to those endpoints.

The focused reviewer checks that the two bracketings do not collapse by
runtime conversion, that applying the whole map preserves the represented
base cell, and that its dependent component computes through
`fdapp1_int_hom_fapp0`. A further `fapp1_func` of that same map also
typechecks. Thus the selected non-circular source coherence has now been fed
through the recursive dependent action; `DHSF-PATH-3` is complete. The next
row returns to the original global/local distinction: dimensions zero through
three still need complete boundary telescopes rather than only fixed-endpoint
triangle/tetrahedron and three-edge-spine slices.

No rule or `unif_rule` is present in either new source slice. The durable
negative remains the opaque-edge probe: without visible Sigma constructors,
projection stops and no eta is synthesized.

Focused quiet checks are green:

```text
logs/probes/emdash3_2_dependent_simplex_path_associator-20260819-073248.log
logs/probes/dependent_simplex_path_associator-20260819-073253.log
logs/probes/emdash3_2_dependent_simplex_represented_source-20260819-073251.log
logs/probes/dependent_simplex_represented_source-20260819-073256.log.
```

Warning-enabled checks are also green. The path-associator source/reviewer
retain the `1112/159` import-closure inventory. The represented-source
source/reviewer report `1150/159`, exactly matching the unchanged
`emdash3_2_dependent_simplex_bridge.lp` import-closure baseline rather than
adding a diagnostic family:

```text
logs/probes/emdash3_2_dependent_simplex_path_associator-20260819-073043.log
logs/probes/dependent_simplex_path_associator-20260819-073049.log
logs/probes/dependent_simplex_path_assoc_no_assoc-20260819-074718.log
logs/probes/dependent_simplex_path_assoc_no_assoc-20260819-074720.log
logs/probes/emdash3_2_dependent_simplex_bridge-20260819-073143.log
logs/probes/emdash3_2_dependent_simplex_represented_source-20260819-073046.log
logs/probes/dependent_simplex_represented_source-20260819-073051.log.
```

The strict LHS audit, source TOC, active-reference lint, report-header lint,
catalog regeneration/strict check, and exact diff hygiene are green. Health
was refreshed in source-only mode and records 237 tracked Lambdapi
source/reviewer files. An attempted resumable health check invalidated its
cache because `check_metrics.py` itself gained the new source entry and began
rechecking the unchanged repository; it was interrupted rather than allowed
to become an unnecessary long aggregate. The focused source/reviewer checks
above are the semantic evidence for this tranche; no `make check`,
`make examples`, `make ci`, or repository aggregate is claimed.

### 13.5 Flagged Native Dimensions Zero Through Three — 2026-08-19

The successful native-dimensions probe identifies the recursion that the
earlier provisional code sketches were trying to describe. It is not a new
deep syntax. After fixing the initial lower face, the next classifier is the
already-active outgoing-path category:

```text
DependentSimplex0_cat(C)                 = C
DependentSimplex1_cat(C,x0)              = PathOut_C(x0)
DependentSimplex2_cat(C,x0,e01)          = PathOut_{S1}(e01)
DependentSimplex3_cat(C,x0,e01,t012)     = PathOut_{S2}(t012).
```

The promoted rule-free source is

```text
emdash3_2_dependent_simplex_native_dimensions.lp.
```

Because `PathOut_Z(x) = Sigma_y Hom_Z(x,y)`, every successor is exactly the
canonical `Hom_cat`/`Sigma_cat`/`homd_` recursion selected by this plan.
`dependent_simplex2_visible` projects to edges 02 and 12 and its dependent
triangle filler; edge 01 is the classifier flag. A visible
`dependent_simplex3` projects immediately to faces 013 and 023, with face 012
as its flag. Its remaining component is initially based at the stable
represented postcomposition owner. The generic
`dependent_simplex3_readable_cell` conjugates along the existing typed
postcomposition/raw-composition path. At fully constructor-visible lower
faces, `dependent_simplex3_visible_readable_cell` then projects by Hom(Sigma)
to face 123 and the top dependent filler.

Whole map action is also derived rather than postulated:

```text
pathout_map_func(F,x)
  = sigma_pullback_total_func(F,Rep_D(Fx))
      o sigma_map_func(fapp1_at_transf(F,x)).
```

Iterating it supplies `dependent_simplex1_map` through
`dependent_simplex3_map`; the reviewer checks a visible edge image and retains
the next `fapp1_func` in dimension three. No recursive action record, rule,
unifier, or Sigma eta is introduced.

This resolves the global/local distinction honestly. The active
computational presentation is **flagged**: its category changes after choosing
the initial vertex, edge, and triangle. Naively totalizing over all flags would
ask a Cat-valued family to transport a represented hom covariantly in its
contravariant endpoint; that is the earlier mixed-variance comma/coherent-
square gap. This row therefore does not claim a single category of all native
`n`-simplices. Low-dimensional comparison with `Functor([n],C)` remains the
profile-sensitive adequacy row, not a prerequisite for using the checked
flagged tower.

Focused source/reviewer checks are green quietly and warning-enabled. Both
warning runs retain the unchanged dependent-bridge import-closure inventory
of `1150/159`:

```text
logs/probes/emdash3_2_dependent_simplex_native_dimensions-20260819-082712.log
logs/probes/dependent_simplex_native_dimensions-20260819-082714.log
logs/probes/emdash3_2_dependent_simplex_native_dimensions-20260819-082717.log
logs/probes/dependent_simplex_native_dimensions-20260819-082720.log.
```

The durable negative from the probe is architectural rather than a failing
promoted term: directly projecting the final component before endpoint
conjugation does not elaborate. The promoted readable-cell adapter is the
narrow typed repair; no global postcomposition fold or Sigma eta was added.
The strict LHS audit, source TOC, active-reference and report-header lints,
focused metrics/source-TOC tests, catalog regeneration/strict check, and exact
diff hygiene are green. The source-only health snapshot now records 239 files;
no long aggregate was rerun.

### 13.6 Dimension-Four Acceptance Boundary — 2026-08-19

The fourth native level is structurally uniform:

```text
DependentSimplex4_cat(C,x0,e01,t012,s0123)
  = PathOut_{DependentSimplex3_cat(C,x0,e01,t012)}(s0123).
```

`dependent_simplex4_map` is the corresponding next `pathout_map_func`, and
its reviewer retains another `fapp1_func`. The visible constructor packages a
target tetrahedron and an arrow out of the flagged tetrahedron. Its immediate
projections give faces 0124 and 0134, while face 0123 is the classifier flag.

The generic `dependent_simplex4_readable_cell` reuses the dimension-three
typed endpoint conjugation at the `DependentSimplex2_cat` level. When the
three lower tetrahedra remain constructor-visible,
`dependent_simplex4_visible_readable_cell` becomes a Hom(Sigma) pair. Its
first component is face 0234. Its second component is the remaining dependent
frame containing face 1234 and the top filler.

The ignored full-constructor probe deliberately attempts

```text
sigma_Fst(sigma_Snd(dependent_simplex4_visible_readable_cell(...))).
```

and fails to infer a type even when all C-level vertices, edges, triangles,
and lower tetrahedra are visible:

```text
logs/probes/dependent_simplex_dimension4-20260819-083935.log.
```

The failure is not missing Sigma eta at the outer level—the first pair already
projects. The residual lower tetrahedra still carry the formal represented
postcomposition endpoints of their own dependent cells. The restored probe,
which stops at that exact recursive frame, is green:

```text
logs/probes/dependent_simplex_dimension4-20260819-084304.log.
```

This is the dimension-four decision requested by the plan. A viable internal
code cannot store only a flat list of faces, nor may it decode by rewriting
all formal endpoints. Each successor frame must retain:

```text
formal native owner
typed readable endpoint view
recursive residual frame.
```

Accordingly `DHSF-DIM4-4` is complete at the strongest honest computational
boundary and `DHSF-CODE-5` becomes active. The direct-final-projection gap is
not silently reclassified as a completed face computation.

Focused source/reviewer checks are green quietly and warning-enabled. Both
warning runs retain the unchanged `1150/159` import-closure inventory:

```text
logs/probes/emdash3_2_dependent_simplex_dimension4-20260819-085216.log
logs/probes/dependent_simplex_dimension4-20260819-085219.log
logs/probes/emdash3_2_dependent_simplex_dimension4-20260819-085221.log
logs/probes/dependent_simplex_dimension4-20260819-085224.log.
```

The strict LHS audit, source TOC, active-reference and report-header lints,
focused tooling tests, catalog regeneration/strict check, and exact diff
hygiene are green. The source-only health snapshot records 241 files; no long
aggregate was run.

### 13.7 Intrinsically Indexed Flag Codes — 2026-08-19

The dimension-four result rules out both earlier extremes: external source
generation is unnecessary, while a deep code for arbitrary categories would
duplicate the kernel. The promoted middle ground is:

```text
RawDependentSimplexCode(C,0,C)
RawDependentSimplexCode(C,n,K), x : Obj(K)
  -> RawDependentSimplexCode(C,n+1,PathOut_K(x)).
```

The public `DependentSimplexCode(C,n)` packages the decoded `K` in a dependent
Sigma. `dependent_simplex_code_decode_cat` is simply `sigma_Fst`; the raw code
at that index is `sigma_Snd`. Thus decoding never interprets arbitrary `Cat`
syntax and cannot create a second Hom/Sigma/homd normal form.

The source

```text
emdash3_2_dependent_simplex_codes.lp
```

also provides selected codes through dimension four. Their decoded categories
are judgmentally the already-promoted `DependentSimplex1_cat` through
`DependentSimplex4_cat`. `DependentSimplexFaceRef(p,n)` is a transparent alias
for the existing `FaceCode(succ p,succ n)`, not another face syntax.
`DependentSimplexEndpointView` packages formal and readable objects in the
decoded category together with their typed equality, carrying the recursive
view demanded by the dimension-four residual.

The raw-wrapper rule has one rigid `RawDependentSimplexCode` owner and no
compound inferred LHS slot. The focused strict rule audit is green. Quiet and
warning-enabled source/reviewer checks are green with no diagnostic delta:

```text
logs/probes/emdash3_2_dependent_simplex_codes-20260819-090640.log
logs/probes/dependent_simplex_codes-20260819-090642.log
logs/probes/emdash3_2_dependent_simplex_codes-20260819-090645.log
logs/probes/dependent_simplex_codes-20260819-090648.log.
```

The warning inventory remains `1150/159`. `DHSF-CODE-5` is complete. The
remaining decoder work is specifically functorial: recursively map the hidden
flag code along `F:C->D` and return the existing native whole functor between
the two decoded category indices.
The source TOC, active-reference/report-header lints, focused tooling tests,
catalog regeneration/strict check, and exact diff hygiene are green. The
source-only health snapshot records 243 files; no long aggregate was run.

### 13.8 Functorial Mapped Decoding — 2026-08-19

The mapped decoder follows the intrinsic code index instead of introducing a
parallel recursive action record. Its structural result is

```text
DependentSimplexCodeMapResult(D,n,K)
  = Sigma target : DependentSimplexCode(D,n),
      Functor(K,decode(target)).
```

The stable recursive owner `raw_dependent_simplex_code_map(F,c)` has exactly
two runtime clauses. Zero returns `(code0(D),F)`. At a successor flag `x`, it
recursively obtains `(c',F_c)`, stores `F_c(x)` in `step(c',F_c(x))`, and
returns `pathout_map_func(F_c,x)`. The public projections are
`dependent_simplex_code_map_target` and
`dependent_simplex_code_map_func`. The selected codes compute to
`dependent_simplex1_map` through `dependent_simplex4_map`; no
dimension-specific map rule is added. A generic `fapp1_func` remains
available at dimension four.

`dependent_simplex_endpoint_view_map` applies the decoded whole functor to
both the formal and readable endpoints and carries their comparison by
`eq_ap` of its object function. Thus recursive readable views survive mapped
decoding without a new equality or endpoint normal form.

The two raw-code clauses share one rigid stable owner, and the strict LHS
audit reports no unreviewed reconstructible compound slot. Quiet and
warning-enabled source/reviewer checks are green:

```text
logs/probes/emdash3_2_dependent_simplex_code_map-20260819-092925.log
logs/probes/dependent_simplex_code_map-20260819-092928.log
logs/probes/emdash3_2_dependent_simplex_code_map-20260819-092930.log
logs/probes/dependent_simplex_code_map-20260819-092933.log.
```

The warning inventory remains `1150/159`. Focused source registration,
reviewer assertions, source TOC, active-reference/report-header lints,
tooling tests, strict core/new-source audits, catalog regeneration/strict
check, exact diff hygiene, and source-only health are green. The health
snapshot records 245 files; no long aggregate was run. `DHSF-DECODE-6` is
complete and decoded face projection is now the sole active row.

### 13.9 Recursive Whole Face Action — 2026-08-19

The successful face probe shows why neither a naive `pathout_map_func` fold
nor a separate family of coface projections is appropriate. For a successor
flag code, raw skip/keep syntax has three geometric cases:

```text
skip alpha       -> constant(recursiveFace(alpha)[flag])
keep(skip alpha) -> recursiveFace(keep alpha) o Sigma_proj1_func
keep(keep alpha) -> pathout_map_func(recursiveFace(keep alpha),flag).
```

The middle clause is essential. In a triangle it sends face 02 to the target
edge; a naive outgoing-path map of the vertex-0 face would instead produce a
constant reflexive edge. The final clause sends face 12 through the base-arrow
projection of the outgoing path. These clauses and the vertex base case form
the stable `raw_dependent_simplex_face` owner in

```text
emdash3_2_dependent_simplex_faces.lp.
```

`DependentSimplexFaceResult(C,p,K)` packages the target intrinsic code and a
whole `Functor(K,decode(target))`. Public `dependent_simplex_face` reuses
`face_code_raw` on the existing `DependentSimplexFaceRef = FaceCode`; its two
projections are `dependent_simplex_face_target` and
`dependent_simplex_face_func`. The reviewer computes both edge vertices and
all three triangle edges, and retains the generic next `fapp1_func`.

One selected public `face_comp` consumer distinguishes computation from
extensionality. Direct and sequential routes compute to the same target code
and to the same final vertex on a constructor-visible triangle. For an opaque
simplex object, however, both their object actions and whole functors retain
different recursive-composition normal forms. This is a durable non-collapse
result, not a reason for a broad rewrite: no functor extensionality,
PathOut-map composition law, or external family of simplicial equations is
added. A later adequacy/whole-nerve consumer may request the narrow comparison.

The four recursive clauses have one stable owner, disjoint raw constructors,
and no unreviewed inferred LHS slot. Quiet and warning-enabled source/reviewer
checks are green:

```text
logs/probes/emdash3_2_dependent_simplex_faces-20260819-100111.log
logs/probes/dependent_simplex_faces-20260819-100116.log
logs/probes/emdash3_2_dependent_simplex_faces-20260819-100122.log
logs/probes/dependent_simplex_faces-20260819-100128.log.
```

The warning inventory remains `1150/159`. Registration, authority and
notation updates, strict audits, source TOC/reference/report lints, catalog,
focused tooling tests, exact diff hygiene, and the 247-file source-only health
snapshot are green; no long aggregate was run. `DHSF-FACE-7` is complete at
the honest whole-action boundary, and low-dimensional adequacy is now active.

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
