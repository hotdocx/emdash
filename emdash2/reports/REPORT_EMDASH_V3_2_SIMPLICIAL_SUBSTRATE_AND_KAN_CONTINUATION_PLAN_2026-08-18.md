# Emdash v3.2 Simplicial Substrate And Kan Continuation Plan

Date: 2026-08-18 (America/Toronto)

Plan-ID: `SIMPLICIAL-SUBSTRATE-KAN-V3.2`

Status: **active bounded implementation plan**. `SIMP-00`, the Cat-valued
Nat/join feasibility row `SIMP-PROBE-1`, the set-classified face-code row
`SIMP-CODE-2`, and the internal index-category row `SIMP-INDEX-3` are
complete. The join-shape/selected-realization row `SIMP-SHAPE-4` is also
complete. The representable/diagram row `SIMP-YONEDA-5` is complete;
the dimension-two boundary/horn row `SIMP-SIEVE-6` is complete;
the bounded algebraic filler row `SIMP-FILL-7` is complete. The promoted
decalage slice `SIMP-DEC-8` is complete at its checked levelwise boundary;
the whole varying-fibre comparison is deferred behind the named
`SIMP-DEC-HFIBRE-TODO` prerequisite. The codata gate `SIMP-CODATA-9` is
therefore deferred, `SIMP-DOC-10` is complete, and `SIMP-CLOSE-11` is the
active row. Later work remains ordered rather than simultaneous scope.

Branch: `goal/simplicial-substrate-v3.2`

Worktree: `/home/user1/emdash1-simplicial-v1`

Baseline: published clean `main` checkpoint
`e1dc41484e4b906cadf094dc63fc7bddba526a41`

Depends-On:

- active `emdash3_2.lp`, especially Nat elimination, `Join_cat`, whole
  functor/transfor action, `Catd`, `homd_`, `homd_int`, dependent Sigma, and
  the extracted laxity tower;
- `emdash3_2_presheaves.lp`, `emdash3_2_sieves.lp`, and
  `emdash3_2_sieve_extensions.lp` for Yoneda, ordinary sieves, and their
  whole inclusions into representables;
- `emdash3_2_walking_arrow.lp`, path pseudo-laxity, generic
  groupoidification, and the selected Gray profile as concrete low-dimensional
  evidence;
- `EMDASH_FOUNDATIONS.md`, current SOP, canonical syntax, and the completed
  internal-laxity/groupoidal-realization decision record; and
- `PERSISTENT_GOAL_GIT_EXPERIMENTATION.md` for resumable Git discipline.

Side-Task-Ledger: `SIMP-00`, `SIMP-PROBE-1`, `SIMP-CODE-2`,
`SIMP-INDEX-3`, `SIMP-SHAPE-4`, `SIMP-YONEDA-5`, `SIMP-SIEVE-6`,
`SIMP-FILL-7`, `SIMP-DEC-8`, `SIMP-DEC-HFIBRE-TODO`, `SIMP-CODATA-9`,
`SIMP-DOC-10`, and `SIMP-CLOSE-11`

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`. The principal design response was
manually preserved after an interrupted hook turn at
`/home/user1/emdash1/emdash2/.scratchpad/tmp-ai-responses-simplicial.md`.
That ignored file is recovery evidence only. Active code/SOP and this plan
outrank it.

## 1. Objective

Build the first reusable computational substrate for simplicial methods in
emdash without importing a second foundational type theory. The selected
architecture treats the simplex index, standard simplices, boundaries,
horns, and diagrams as internal categorical objects. The existing
functorial/dependent action owns their substitution and higher coherence.

The intended path is:

```text
computing face-map codes
          |
          +-- SemiDeltaPlus_cat
          |       |
          |       +-- Yoneda standard simplices
          |       +-- boundary / horn / spine sieves
          |       +-- semisimplicial diagrams
          |       `-- categorical decalage
          |                 |
          |                 `-- displayed cone slice
          |                          |
          |                          `-- homd_/Sigma iteration
          |
          `-- realization as join-built directed simplex shapes.
```

A later curated coinductive `SST` facade may expose the cone observation
interface. It is not the foundational first owner and is not a prerequisite
for standard simplices or Kan fillers.

## 2. Scope And Explicit Nonclaims

This plan includes:

1. a computational code for augmented semi-simplex face maps;
2. an internal augmented semi-simplex category;
3. Nat-indexed directed simplex shapes by iterated join;
4. a whole realization from face codes to those shapes;
5. standard representables, selected boundaries, and selected horns;
6. groupoid-valued semisimplicial diagrams and their Cat-valued realization;
7. one algebraic low-dimensional Kan consumer; and
8. a bounded decalage/slice comparison with the existing dependent-hom tower.

It does not initially claim:

- the full simplex category with degeneracies;
- every boundary, horn, or spine in one first tranche;
- a complete Reedy model structure or classifier theorem;
- a type-theoretic display translation on arbitrary syntax;
- a general positivity, guardedness, or productivity checker;
- judgmental codata eta or equality of coinductive presentations;
- a complete simplicial, Segal, Rezk, Kan, or omega-coherence metatheory;
- global normalization, canonicity, confluence, or semantic soundness of the
  combined calculus; or
- a migration of the historical global strict functoriality/naturality cuts.

Full simplicial maps, degeneracies, Segal/Rezk conditions, geometric
realization, skeleton/coskeleton, and generic shape-category abstractions are
future consumers of the substrate, not prerequisites for its first vertical
slice.

## 3. Terminology And Ownership

Three objects must remain distinct:

| Name | Meaning | Selected owner |
| --- | --- | --- |
| `DirectedSimplex_cat(n)` | finite ordinal category `[n]`, geometrically an `(n+1)`-vertex directed simplex shape | Nat-recursive iterated `Join_cat` |
| `StandardSimplex(m)` | representable presheaf of the `m`-vertex ordinal; conventional `Delta[n]` is `StandardSimplex(succ n)` | existing `yoneda_psh` over `SemiDeltaPlus_cat` |
| semisimplicial diagram `X` | coherent diagram on the opposite semi-simplex category | `Functor(Op_cat(SemiDeltaPlus_cat),Grpd_cat)` or its Cat-valued realization |

The earlier `homd_`/Sigma result is a local cell-iteration mechanism. It
packages a base cell with a dependent cell above it, and recursively repeats
that pattern. It does not alone define the category of all simplex shapes or
the standard representable simplex.

The earlier explicit groupoidal `Delta2_grpd` proposal is also distinct. It
is the groupoidal realization/free inversion of a selected directed
2-simplex-shaped source, not the representable semisimplicial set
`StandardSimplex(3)`.

## 4. Reference Audit And Adaptation Boundary

External material was reviewed in an isolated temporary corpus and is not a
repository dependency:

```text
/tmp/emdash-sst-review.KehjPC
```

The reviewed snapshots are:

- Kolomatskaia--Shulman, *Displayed Type Theory and Semi-Simplicial Types*,
  arXiv:2311.18781v2;
- `FrozenWinters/Kan` at `1a6d523`, including the compact Narya definitions
  of `SST`, boundaries, horns, and chosen Kan fillers;
- `FrozenWinters/SSTs` at `52c35d4`, including the earlier Agda syntax and
  dependency-list construction;
- Narya at `7bf7fb8`, especially its observation-driven codata and displayed
  coinductive documentation;
- Herbelin--Ramachandra,
  *A parametricity-based formalization of semi-simplicial and semi-cubical
  sets*, arXiv:2401.00512v2;
- Herbelin--Ramachandra,
  *The very dependent recursive structure of iterated parametricity in
  indexed form*, arXiv:2602.12689v1; and
- Bonak at `0f0f239`, including the published set-level construction, the
  current groupoid-level experiment, and the indexed--presheaf
  correspondence.

These references guide tests and distinctions rather than dictate the
foundation:

- displayed type theory shows that a coinductive cone interface can expose
  all dimensions, but it depends on a primitive guarded display operation;
- Narya shows demand-driven codata and a compact algebraic Kan API, while its
  implementation and mode theory are not emdash authorities;
- Herbelin's indexed construction exposes the exact frame/restriction/
  coherence dependency graph, but remains an explicit combinatorial
  reconstruction; and
- Bonak's growth from sets to groupoids demonstrates why emdash should not
  duplicate a new coherence record at every truncation level. Its current
  presheaf/indexed comparison also uses an explicit coinductive-extensionality
  axiom at the final equality boundary, supporting an emdash `OmegaEquiv`
  comparison rather than judgmental codata eta.

## 5. Computational Face Codes

Use the augmented cardinal convention: object `n : Nat` represents the
finite ordinal with `n` vertices, so object zero is the augmentation object,
object one represents the ordinary 0-simplex, object two the directed edge,
and object three the directed 2-simplex.

The selected raw indexed code is structurally the binary skip/keep word:

```text
FaceCode(0,0)

face_skip : FaceCode(p,n) -> FaceCode(p,n+1)
face_keep : FaceCode(p,n) -> FaceCode(p+1,n+1).
```

`FaceCode(p,n)` represents an injective monotone map from the `p`-vertex
ordinal to the `n`-vertex ordinal. Identity is the all-keep word. Composition
substitutes the source word into the retained positions of the target word.

The promoted representation separates computation from public discreteness:

```text
RawFaceCodeData(p,n)                 indexed skip/keep syntax
RawFaceCode(p,n)                     Grpd wrapper for raw recursion
FaceCode(p,n) := ||RawFaceCode(p,n)||_0
```

`raw_face_comp` owns the four structural substitution clauses. Public
`face_skip`, `face_keep`, and `face_comp` use `trunc_map` and nested restricted
recursion, so visible constructors still compute. `face_code_is_set` is the
existing truncation reflector's classified evidence rather than a new axiom
or observational-equality theory.

The code owner provides:

- a native decoded classifier and constructor eliminator sufficient for
  structural identity/composition;
- runtime computation on visible constructors;
- sethood/discreteness evidence at the public category boundary;
- positive zero/skip/keep and composition cases;
- negative index-mismatch cases; and
- no broad proof-time clause merely to hide a failed composition definition.

The curated native indexed inductive is standard-library infrastructure, not
a general user-facing inductive-declaration facility. Its generated dependent
eliminator was inspected in the ignored owner probe before promotion.

## 6. The Internal Semi-Simplex Category

The target facade is:

```text
Obj(SemiDeltaPlus_cat) = Nat_grpd

Hom_cat(SemiDeltaPlus_cat,p,n)
  = Path_cat(FaceCode(p,n)).
```

Identity and composition delegate to the computing face-code operations.
The hom categories are path-discrete once `FaceCode` sethood is established.

The promoted composition boundary is intentionally narrower than a catch-all
category fold. At visible public `trunc_intro` points it reduces through
`face_comp`; arbitrary composition remains at the generic `comp_fapp0` head.
An unconstrained category fold was rejected after bounded quiet and warning
probes both timed out. The visible-point LHS uses the constructor normal form
of `trunc_zero`, because that transparent alias normalizes before rule
selection.

The category must retain category-level identity/composition at the generic
owners. Constructor computation belongs at face-code identity/composition;
do not add duplicate `fapp*` or `tapp*` rules.

## 7. Directed Simplex Shapes And Join Realization

The first probe tests whether current Nat elimination can return an object of
`Cat_cat` directly:

```text
DirectedSimplex_cat(0)     = Terminal_cat
DirectedSimplex_cat(n + 1) =
  Join_cat(DirectedSimplex_cat(n),Terminal_cat).
```

Expected low-dimensional observations are:

```text
DirectedSimplex_cat(0) = Terminal_cat
DirectedSimplex_cat(1) = WalkingArrow_cat
DirectedSimplex_cat(2) = Join_cat(WalkingArrow_cat,Terminal_cat).
```

The augmented empty shape can be added as a separately named
`Path_cat(Empty_grpd)` endpoint if a concrete decalage or Yoneda consumer
needs it; it should not complicate the first Nat recursion unnecessarily.

The missing reusable geometric operation is:

```text
join_map(F,G) : Join_cat(A,B) -> Join_cat(A',B').
```

It should be defined through `join_elim_func`, with the target's existing
`join_cross_transf` supplying the internally natural cross cell. A separate
pointwise naturality family is forbidden.

Face codes then receive a whole realization into strict-profile functors
between the appropriate directed simplex shapes. Face-code composition owns
normalization; join realization owns geometric meaning. Neither presentation
should be rewritten globally into the other.

The conventions are related by successor rather than identified: index
object `m` counts vertices (and permits `m=0`), while ordinary
`DirectedSimplex_cat(n)` has `n+1` vertices. The first selected dictionary
therefore pairs `FaceCode(succ p,succ n)` with a strict-profile functor
`DirectedSimplex_cat(p) -> DirectedSimplex_cat(n)`. A generic realization of
the augmented-empty code remains deferred until an empty-join comparison is a
real consumer.

## 8. Standard Simplices, Boundaries, Horns, And Spines

Once `SemiDeltaPlus_cat` exists:

```text
StandardSimplex(n)
  := yoneda_psh(SemiDeltaPlus_cat,n).
```

The active `hom_con_int`/Yoneda owner supplies every restriction and higher
action. No standalone record of face maps or external simplicial identities
is added.

Boundaries and horns are ordinary sieves on `n`:

```text
Boundary(n) : Sieve(SemiDeltaPlus_cat,n)
Horn(n,k)   : Sieve(SemiDeltaPlus_cat,n).
```

Their computing membership should use the code:

```text
f in Boundary(n)  iff f omits a vertex;
f in Horn(n,k)    iff f omits a vertex distinct from k.
```

Precomposition preserves omission structurally. Existing ordinary-sieve
extension then produces whole inclusions

```text
partial-Delta[n] -> Delta[n]
Lambda^k[n]      -> Delta[n].
```

The first implementation is explicitly bounded to dimension two. Generic
Nat-indexed boundary/horn families follow only after those literal cases
compute without duplicating the sieve action.

The promoted finite presentation computes three omission bits on raw
skip/keep codes and descends them through `FaceCode` by restricted recursion
into the internally proved set `Bool_grpd`. One kind-indexed higher-sieve owner
exposes proposition-valued fibres; generic `Catd` action owns naturality.
Generic sieve pullback retains the canonical represented-postcomposition
head. A direct runtime bridge from that head to `face_comp` is intentionally
absent; structural `face_comp` computation is checked separately.

A later spine sieve can express the Segal comparison through the existing
Hom-locality interface. It is not part of the first horn tranche.

## 9. Groupoid-Valued Diagrams

The first direct classifier is:

```text
SemiSimplicialGrpd
  := Functor(Op_cat(SemiDeltaPlus_cat),Grpd_cat).
```

Since `Hom_cat Grpd_cat A B` is a path category of ordinary functions, its
generic compositor is invertible for structural reasons. A groupoid-valued
semisimplicial diagram is therefore pseudo/coherently functorial without a
second Gray-profile classifier.

Postcomposition with

```text
Path_cat_func : Grpd_cat -> Cat_cat
```

gives the Cat-valued presheaf realization consumed by the existing Yoneda and
sieve modules. A thin rigid facade may be added if it preserves the generic
composition owner; it must not duplicate `Psh_cat` or its action.

The promoted boundary keeps whole postcomposition in
`Functor_cat(Op(SemiDeltaPlus_cat),Cat_cat)`. `Psh_cat(SemiDeltaPlus_cat)` is a
deliberately distinct runtime head, so realized objects and maps cross only
through its existing object/Hom projections. No new rigid whole functor into
`Psh_cat` is postulated merely to make the two category heads definitionally
equal.

Levelwise sethood gives the semisimplicial-set specialization. Generic
Cat-valued presheaves remain available for higher-categorical consumers.

## 10. Algebraic Horn Filling

For a realized diagram `X`, define mapping categories and restriction by
precomposition:

```text
SimplexMaps(X,n) = Hom(Delta[n],X)
HornMaps(X,n,k)  = Hom(Lambda^k[n],X)

horn_restrict(X,n,k)
  : SimplexMaps(X,n) -> HornMaps(X,n,k).
```

The first computational Kan interface is algebraic: it selects a whole
section of each restriction. This is stronger and more executable than mere
truncated filler existence and corresponds to Narya's `Kan` consumer.

The first nontrivial consumer is the 2-dimensional nerve of a path groupoid:

- the inner horn computes by path composition;
- the two outer horns compute using path inverses; and
- retained higher action reuses the existing path pseudo-laxity tower.

The promoted slice separates two boundaries. For arbitrary Cat-valued `X`,
horn restriction is exactly existing whole precomposition by the selected
sieve inclusion. For a path groupoid `G`, one explicit algebraic strict
2-nerve carrier and three horn carriers provide computational filler functions
and whole Path-map lifts. The algebraic carriers are not yet identified with
the full presheaf mapping categories; that comparison is not required for the
bounded filler computation.

Mere Kan, inner-Kan/quasicategory, and all-dimensional fillers remain later
interfaces. A successful 2-horn consumer is not a complete Kan theorem.

## 11. Categorical Decalage And The Cone Interface

The emdash-native alternative to a primitive theory-wide display translation
is categorical decalage.

Adding a distinguished initial or final vertex gives a shift functor on the
semi-simplex category. Precomposition defines:

```text
Dec(X)[n] = X[n+1].
```

The shifted simplex has two relevant whole observations:

- its added cone vertex; and
- its opposite base simplex.

Fixing `x : X[0]` in the first observation gives a fibre `S(X,x)` displayed
over `X` by the base observation. Its first dimensions must recover edges
from `x`, triangles over base edges, and tetrahedral fillers. Those are the
same base-plus-dependent-cell layers already computed by `homd_`, dependent
Sigma, and the recursive internal action.

The acceptance test for calling this fibre *the* derived emdash display is a
whole comparison for the first three dimensions, not a pointwise analogy.
The bounded probe established the shift, both whole observations, presheaf
decalage, levelwise fixed-tip fibres, and one iterable whole base Path-map. It
also isolated the missing prerequisite: a varying-`HFiber` Catd, or
equivalently a whole total Path-family over the shifted diagram, from which
`FibrewiseSigma_catd` can assemble one displayed semisimplicial object.

That prerequisite is recorded as `SIMP-DEC-HFIBRE-TODO`. Until it is met,
public documentation may describe the active construction as categorical
decalage with selected levelwise cone fibres, but not as a whole
`homd_`/dependent-Sigma realization. This is a genuine boundary, not a reason
to replace the missing whole owner with an external naturality record.

## 12. Curated Coinduction Policy

A later user-facing observation facade may expose:

```text
SST.z : SST -> Grpd
SST.s : (X : SST) -> SST.z(X) -> DisplayedSST(X).
```

For a curated logical-framework codata signature, computation must be
observation-driven:

```text
head(corec(seed,...)) -> ...
tail(corec(seed,...)) -> corec(next(seed),...).
```

The policy is:

- only destructor-headed rules unfold;
- the corecursive object does not unfold eagerly;
- no judgmental codata eta;
- bisimulation/extensionality is an explicit path or `OmegaEquiv`;
- every declaration receives owner-position, subject-reduction, termination,
  warning, and both-order audits; and
- no claim is made that Lambdapi checks general positivity/productivity.

A TypeScript management builder may eventually generate these curated symbol
and rule skeletons. Such generation is an authoring convenience, not a new
kernel trust theorem.

For `SST`, the preferred comparison is an `OmegaEquiv` between the presheaf
presentation and the cone-observation presentation. Judgmental equality of
the two representations is explicitly excluded.

## 13. Module And Dependency Strategy

Do not put the whole development into `emdash3_2.lp`.

1. Probe the Nat/join expression in ignored temporary space.
2. If it is transparent and owner-aligned, place the public shape facade in a
   narrow downstream module such as `emdash3_2_simplex_shapes.lp`.
3. Put face codes and `SemiDeltaPlus_cat` in a dedicated downstream module
   after their representation stabilizes.
4. Put representables/sieves and Kan consumers in later one-way modules.
5. Add decalage only after the index category and first horn consumer are
   stable.

The core `emdash3_2.lp` changes only if a probe proves a genuinely missing
generic owner. A missing public alias or literal code constructor is not such
evidence.

## 14. Validation Policy

The inner loop is proportional:

- inspect staged and unstaged diffs separately;
- use ignored focused probes before active edits;
- keep every Lambdapi invocation under 90 seconds;
- run the nearest source and reviewer target after each bounded change;
- compare quiet and warning-enabled runs for every new rewrite family;
- use typed `eq_refl` to exercise any `unif_rule`;
- audit inferred LHS slots and both reduction orders;
- add positive, negative, and retained-higher-action checks; and
- update catalog/health only when a public source/check boundary changes.

Do not rerun `make ci`, repository-wide TypeScript checks, book rendering, or
other long aggregates after each row. Carry forward exact unchanged evidence.
Run a larger gate only at a real affected integration/checkpoint boundary and
only when omitting it would block trustworthy promotion.

## 15. Git And Authorization Boundary

The user authorized the dedicated worktree/branch, implementation,
persistent goal, and SOP-compliant local checkpoints. Each checkpoint must:

- contain one bounded green tranche;
- synchronize this ledger and any affected active authority;
- stage only reviewed plan-owned paths; and
- preserve unrelated work and all other worktrees.

No push, merge, PR, tag, npm/Zenodo publication, history rewrite, branch or
worktree removal, or deployment is authorized by this plan.

## 16. Execution Ledger

| Row | Status | Deliverable and acceptance boundary |
| --- | --- | --- |
| `SIMP-00` | complete | Promoted the reviewed categorical-first architecture, reference adaptation boundary, terminology, trust policy, module order, validation policy, and Git boundary into this living plan. |
| `SIMP-PROBE-1` | complete | The ignored quiet and warning-enabled probe proves that active `nat_elim` computes a Cat-valued iterated join with `0`, `1`, and `2` observations and no new kernel rule. The augmented-empty endpoint remains a separately consumer-gated choice. |
| `SIMP-CODE-2` | complete | Promoted raw indexed skip/keep syntax with four structural composition clauses and the public set-truncated `FaceCode`; sethood, constructors, identity, composition, both identity directions, a mixed composition branch, and index mismatch are checked without a unifier. |
| `SIMP-INDEX-3` | complete | Promoted `SemiDeltaPlus_cat` with Nat objects, locally discrete face-code Homs, all-keep identity, visible-point category composition through `face_comp`, the three dimension-two coface relations, and a direction/index negative. The rejected catch-all composition fold timed out; the selected narrow rule adds no warning or unifier. |
| `SIMP-SHAPE-4` | complete | Promoted ordinary Nat-indexed join shapes, a whole `join_map_func` whose cross cell is reindexed from the target join, strict-profile join closure, and paired code/functor realizations for the two vertices of `Delta[1]` and three edges of `Delta[2]`; all three functorial coface equations compute. |
| `SIMP-YONEDA-5` | complete | Promoted standard Yoneda semisimplices, the groupoid-valued diagram classifier, generic raw whole postcomposition by `Path_cat_func`, public realized objects/maps through `Psh_cat`, level/face computation, and retained higher action without a rule or unifier. |
| `SIMP-SIEVE-6` | complete | Promoted three omission bits, a four-kind boundary/horn membership family, one whole higher-sieve owner, four ordinary sieves, generic pullback, whole extensions/inclusions, the complete codimension-one membership matrix, and structural precomposition checks without a represented-composition bridge. |
| `SIMP-FILL-7` | complete | Promoted generic whole partial-simplex restriction plus an algebraic path-groupoid strict 2-nerve with three restrictions/fillers, inner composition, outer inverses, right-J comparison, derived cancellation, whole function section paths, whole Path-map lifts, and retained next action. |
| `SIMP-DEC-8` | complete at bounded boundary | Promoted the vertex-appending shift, whole base and cone-tip transformations, presheaf decalage, fixed-tip levelwise fibres through the first three selected levels, and an iterable whole base Path-map. The intended whole displayed comparison did not typecheck because no varying-`HFiber` Catd/total Path-family owner exists; it is split into the named deferred prerequisite below rather than approximated pointwise. |
| `SIMP-DEC-HFIBRE-TODO` | deferred prerequisite | Introduce one reusable varying-`HFiber` Catd or total Path-family owner, assemble it through existing `FibrewiseSigma_catd`, and only then compare its first three whole layers with `homd_`/Sigma action. Reopen only for a concrete displayed-fibre consumer. |
| `SIMP-CODATA-9` | deferred; gate not met | The categorical/decalage interface did not yet produce the required whole displayed comparison, so no curated observation-driven `SST` codata facade, generic codata mechanism, or judgmental eta is promoted. Reconsider after `SIMP-DEC-HFIBRE-TODO`, not merely because an external reference uses codata. |
| `SIMP-DOC-10` | complete | Synchronized Foundations, canonical cardinal-versus-dimension notation, both READMEs, SOP/source inventories, focused examples, and the report index for the promoted substrate and its exact nonclaims. No generated book/article artifact was edited. |
| `SIMP-CLOSE-11` | active | Record checkpoints, exact focused evidence, warning deltas, clean state, remaining rows, and a safe continuation prompt. No integration or publication. |

### 16.1 Initial Nat/Join Probe — 2026-08-18

The ignored probe `tmp/probes/simplicial_nat_join_shape.lp` imports the active
walking-arrow owner and defines only the transparent candidate

```text
directed_simplex_probe_cat(0)     = Terminal_cat
directed_simplex_probe_cat(n + 1) =
  Join_cat(directed_simplex_probe_cat(n),Terminal_cat)
```

by applying existing `nat_elim` with constant motive `Obj Cat_cat`. Both runs
pass under the uniform 90-second ceiling:

```text
logs/probes/simplicial_nat_join_shape-20260818-131735.log  quiet
logs/probes/simplicial_nat_join_shape-20260818-131753.log  warnings enabled
```

The assertions compute the zero case to `Terminal_cat`, the one case to the
active `WalkingArrow_cat`, and the two case to
`Join_cat(WalkingArrow_cat,Terminal_cat)`. An open dimension remains a
well-typed single Cat-valued family. No new runtime rule, proof-time unifier,
primitive recursor, or active source symbol is needed. This establishes the
shape-family feasibility but deliberately does not yet promote its readable
alias ahead of the computing face-code/index owner.

### 16.2 Set-Classified Face Codes — 2026-08-18

The promoted source
`emdash3_2_semisimplicial_face_codes.lp` uses the stronger of the two green
representation probes. `RawFaceCodeData(p,n)` is the native dependent
skip/keep family and `raw_face_comp` owns its four constructor-headed
substitution clauses. The public boundary is

```text
FaceCode(p,n) := Trunc_grpd(0,RawFaceCode(p,n)).
```

Consequently `face_code_is_set` is inherited from the classified truncation
reflector. `face_skip` and `face_keep` are truncation maps; public composition
is nested restricted recursion into a set-valued function space. There is no
new proof-time unifier, proof-erasure rule, observational equality, or
category-level generic-action clause.

The focused reviewer `examples/semisimplicial_face_codes.lp` checks public
sethood, skip/keep point computation, the empty and successor identities,
both closed identity directions, the keep/skip composition branch, both
association orders of a closed three-map chain, and a source-index mismatch.
The exact focused gates are green:

```text
scripts/check.sh emdash3_2_semisimplicial_face_codes.lp
scripts/check.sh examples/semisimplicial_face_codes.lp
EMDASH_LAMBDAPI_WARNINGS=1 scripts/check.sh \
  emdash3_2_semisimplicial_face_codes.lp
EMDASH_LAMBDAPI_WARNINGS=1 scripts/check.sh \
  examples/semisimplicial_face_codes.lp
python3 scripts/audit_rule_lhs.py --strict \
  emdash3_2_semisimplicial_face_codes.lp
```

The warning-enabled predecessor and promoted-source streams each contain
1,297 inherited warning headers; the promoted stream contains no warning
owned by the new module. The strict inferred-slot audit reports zero
unreviewed or annotated candidates. The generated dependent eliminator was
also inspected in the ignored probe and retains the full `(p,n,code)` motive.

A resumable health refresh was attempted after source registration. Because
this fresh worktree had no ignored health cache, it began a repository-wide
rerun; it was deliberately interrupted after 17 green targets under the
standing no-long-aggregate policy. No tracked health report was rewritten.
The focused evidence above is the acceptance boundary for this row; one
health refresh is deferred to a later genuine integration/closure boundary
instead of being repeated after each simplicial tranche.

### 16.3 Internal Augmented Semi-Simplex Category — 2026-08-18

`emdash3_2_semisimplicial_index.lp` promotes the category
`SemiDeltaPlus_cat`. Its objects compute to `Nat_grpd`, its Homs compute to
`Path_cat(FaceCode(p,n))`, and `semi_delta_plus_hom_is_discrete` packages the
existing face-code sethood with canonical path-category groupoidality.
Identity computes to the all-keep code.

The first obvious composition rule

```text
comp_SemiDelta(g,f) -> face_comp(g,f)
```

for arbitrary `g` and `f` timed out at the uniform 90-second boundary in both
the full coface probe and a minimal owner-only probe. The selected replacement
matches only visible public truncation points and routes its RHS through the
existing `face_comp` owner. A normal-form query established that
`trunc_zero` expands before matching, so the LHS deliberately uses
`trunc_succ(trunc_succ(trunc_minus_two))`; the readable alias remains on the
RHS. Open visible-point comparison verifies both reduction orders.

The focused reviewer `examples/semisimplicial_index_category.lp` checks
formation, Hom presentation, identity, locally discrete Hom evidence, the
next generic Path-Hom layer, all three literal 2-simplex coface relations, and
rejection of a reversed vertex arrow. The active source and reviewer are green
quietly and with warnings. Each warning stream retains the same 1,297
predecessor warning headers and contains no new-module warning. The strict LHS
audit reports zero reconstructible compound candidates; no proof-time unifier
or generic `fapp*`/`tapp*` clause was added.

Relevant ignored evidence includes:

```text
logs/probes/semisimplicial_index_category-20260818-135142.log
logs/probes/semisimplicial_index_category_min-20260818-135405.log
  rejected catch-all composition: bounded timeouts

logs/probes/semisimplicial_index_category_min-20260818-141645.log
logs/probes/semisimplicial_index_category_min-20260818-141121.log
  selected visible-point owner and three coface relations: green
```

Per the recorded aggregate policy, the deferred health refresh is not rerun
for this immediately subsequent tranche.

### 16.4 Join Shapes And Selected Face Realization — 2026-08-18

The ignored `simplicial_join_map.lp` probe established the generic whole
construction before promotion. For `F : A -> A2` and `G : B -> B2`,
`join_map_cross_transf(F,G)` is obtained by applying
`Prof_reindex_transf(F,G)` to `join_cross_transf(A2,B2)`. Existing
constant-profunctor and nested-reindex rules make its source and target
exactly the cross datum expected by `join_elim_func`. Both restrictions of
the resulting `join_map_func(F,G)` compute through the existing join betas.

`emdash3_2_simplex_shapes.lp` additionally introduces strict codes for both
join inclusions and the join of two strict codes. Their carrier rules expose
only the already-derived whole functors. `DirectedSimplex_cat(n)` is the
right-iterated join of `n+1` terminal vertices. The transparent
`SelectedFaceRealization(p,n)` dictionary pairs a
`FaceCode(succ p,succ n)` with a strict code between those ordinary shapes.
The promoted instances are the two vertices of `Delta[1]` and the three edges
of `Delta[2]`.

`examples/simplex_shapes.lp` checks the first three shapes, both generic join
restrictions, the whole cross-cell type, all selected code/functor
projections, profile-local strict compositor computation, one code-level
coface relation, all three functor-level coface relations, and the
vertex-count/augmented-empty negative boundary. Source and reviewer checks
are green quietly and with warnings. The exact import-closure baseline and
candidate each contain 1,315 warning headers; no warning is owned by the new
module. The strict LHS audit reports zero reconstructible compound slots, and
no unifier or external naturality record was added.

Relevant ignored probe evidence is:

```text
logs/probes/simplicial_join_map-20260818-142719.log  quiet
logs/probes/simplicial_join_map-20260818-142740.log  warnings enabled
logs/probes/simplicial_join_map_warning_baseline-20260818-142838.log
```

The augmented-empty shape and a decoder for arbitrary `FaceCode` remain
explicitly deferred. They are not prerequisites for standard representables,
which live directly in the internal augmented index category. The health
aggregate remains deferred to the later closure boundary.

### 16.5 Standard Semisimplices And Groupoid-Valued Diagrams — 2026-08-18

`emdash3_2_semisimplicial_diagrams.lp` defines
`StandardSimplex(n)` transparently as
`yoneda_psh(SemiDeltaPlus_cat,n)`. Its level at `p` therefore computes to
`Hom_cat(SemiDeltaPlus_cat,p,n)`, with restriction and every higher action
owned by the existing contravariant internal-hom/Yoneda tower.

`SemiSimplicialGrpd_cat` is the ordinary functor category from the opposite
internal index into `Grpd_cat`. The whole realization owner is exactly
`comp_cat_cov_func(Path_cat_func)` and deliberately targets the raw
Cat-valued functor category. An initial probe attempting to assign that owner
directly to rigid `Psh_cat` failed at the intended category-head boundary. The
accepted design exposes its object and map actions through existing `Psh_cat`
projections while retaining the raw whole functor for hom and later-cell
action.

The focused reviewer `examples/semisimplicial_diagrams.lp` checks the three
classifier presentations and their non-collapse, Yoneda level computation,
levelwise Path realization, realized face action as `path_map_func`, public
map typing, one retained whole next action, and non-representability of an
arbitrary diagram. Source and reviewer are green quietly and with warnings;
both warning streams contain 1,297 inherited headers and no new-module
warning. The module is rule-free, its strict LHS audit is empty, and no
unifier or naturality record was added.

Ignored probe evidence:

```text
logs/probes/semisimplicial_yoneda_facade-20260818-143849.log
  rejected direct rigid-Psh whole-functor target
logs/probes/semisimplicial_yoneda_facade-20260818-144231.log
  accepted raw whole owner with level/face realization
```

The health aggregate remains deferred to the later closure boundary.

### 16.6 Boundary And Horn Sieves Of The Two-Simplex — 2026-08-18

`emdash3_2_simplex2_sieves.lp` computes omission of each of the three target
vertices on raw skip/keep words. A local Boolean-set proof permits all three
observations to descend through public `FaceCode` by the existing restricted
truncation recursor. Boundary membership is the disjunction of all omission
bits; horn `k` membership is the disjunction of the two bits distinct from
`k`. Literal truth values are the actual proposition classifiers
`Unit_grpd` and `Empty_grpd`.

`Simplex2SieveKind` indexes one whole `simplex2_higher_sieve` owner. Its fibre
projection is `Path_cat(Simplex2SieveMember(kind,f))`; generic Catd action
retains restriction and naturality. Proposition evidence packages the four
ordinary sieves. Existing `sieve_pullback`, `ordinary_sieve_extension_psh`,
and `ordinary_sieve_extension_inclusion` supply pullback stability, extensions,
and whole inclusions into `StandardSimplex(3)`.

The focused reviewer `examples/simplex2_boundary_horns.lp` checks that the
identity face lies in no proper sieve, every edge lies in the boundary, and
edge `ij` is excluded exactly from the horn missing the opposite vertex. It
also checks public `SieveMembership`, proposition evidence, one retained
higher action, generic pullback at canonical represented postcomposition,
structural `face_comp` precomposition, and every whole inclusion. A trial
direct equality from generic pullback membership to literal `face_comp` was
rejected because the active slice owner intentionally retains
`hom_postcomp_fapp0`; no new bridge was installed.

Source and reviewer are green quietly and with warnings. The exact
import-closure baseline and promoted candidate each contain 1,315 warning
headers; no warning is owned by the new module. The two initial unused raw
constructor payloads were replaced by `_` before promotion. The strict LHS
audit reports zero candidates, and no unifier or external naturality record
was added.

Ignored probe evidence:

```text
logs/probes/simplex2_sieves-20260818-150523.log
logs/probes/simplex2_sieves_warning_baseline-20260818-150026.log
logs/probes/simplex2_sieves-20260818-150212.log
```

The health aggregate remains deferred to the later closure boundary.

### 16.7 Algebraic Path-Groupoid Horn Fillers — 2026-08-18

`emdash3_2_path_groupoid_2horn_fillers.lp` keeps generic presheaf-facing
partial-simplex restriction at `ordinary_sieve_local_precomp`. Its selected
consumer is a transparent algebraic strict 2-nerve of a groupoid `G`: a
triangle stores three vertices and composable paths `p01,p12`, while the three
horn carriers retain the appropriate two edges.

The inner filler computes edge `p02` as `eq_trans(p01,p12)`. Horn 0 computes
the missing edge as `p01^-1 ; p02`. Horn 2 computes it as
`p02 ; p12^-1` using `eq_trans_right`, a right-J operation whose conventional
agreement with `eq_trans` is proved propositionally. The dual J orientation
makes the horn-2 endpoint computational without a new rewrite rule.

Both outer cancellation laws are derived by J. Horn-specific nested-Sigma
eliminators lift them to pointwise record section paths; `PiFunext` packages
all three as whole function section laws. Every restriction and filler is
lifted by `path_map_func`, so equality and all later action remain at the
generic Path owner. No solver, tactic, primitive filler, rewrite, or unifier is
introduced.

The reviewer `examples/path_groupoid_2horn_fillers.lp` checks generic mapping-
category restriction, right-J agreement, all three object computations, both
outer cancellation proofs, all three section paths, whole restriction/filler
types, one retained next action, and the all-dimensional-presheaf nonclaim.
Source and reviewer are green quietly and with warnings; both contain the
same 1,315 inherited warning headers and no new-module warning. The strict LHS
audit is empty because the module is rule-free.

Ignored probe evidence:

```text
logs/probes/path_groupoid_2horn_fillers-20260818-152536.log
logs/probes/path_groupoid_2horn_fillers-20260818-152557.log
```

This is not yet an all-dimensional nerve object, a comparison with every
presheaf mapping category, a mere-Kan theorem, or an inner-Kan/quasicategory
interface. The health aggregate remains deferred to the later closure
boundary.

### 16.8 Categorical Decalage And The Levelwise Cone Boundary — 2026-08-18

`emdash3_2_semisimplicial_decalage.lp` appends one final vertex by the whole
endofunctor `semi_delta_shift_func`; its arrow action keeps that new vertex in
every face code. The base inclusion and cone-tip inclusion are components of
the whole transformations `semi_delta_base_transf` and
`semi_delta_cone_transf`, so their off-diagonal action remains at the existing
generic `tapp1_func` owner. Restriction along the shift defines presheaf
decalage and computes fibrewise as `Dec(X)[n] = X[n+1]`.

For a groupoid-valued semisimplicial diagram and fixed cone tip `x`,
`SemisimplicialConeFibre(X,x,n)` is the levelwise `HFiber` of the cone-tip
observation. Forgetting the tip is lifted by `path_map_func` to one whole
functor from that fibre to the opposite base simplex, retaining the generic
next Path action. The reviewer `examples/semisimplicial_decalage.lp` checks
the shift on objects and arrows, both low face codes, both transformation
components, retained transformation action, the decalage fibre equation, the
first three selected cone-fibre levels, the whole base Path-map, its next
action, and the pointwise non-collapse boundary.

Source and reviewer are green quietly and with warnings. Both warning-enabled
runs contain the same 1,297 inherited warning headers and no source- or
reviewer-owned diagnostic. The strict LHS audit reports no unreviewed slot;
the shift action's two rigid category positions are documented subject-
reduction guards. No unifier or external naturality/coherence record is
added.

The probe did not find an active varying-`HFiber` Catd or total Path-family
owner. `FibrewiseSigma_catd` can assemble the desired varying fibres only
after that generic owner exists. Consequently `SIMP-DEC-HFIBRE-TODO` records
the exact deferred prerequisite, and the codata gate remains closed. This
tranche does not claim a whole displayed semisimplicial fibre, comparison
with `homd_`, or a coinductive `SST` presentation. The health aggregate
remains deferred to the closure decision under the standing no-long-
aggregate policy.

### 16.9 Documentation And Notation Consolidation — 2026-08-18

The Foundations guide now separates the local simplicial reading of
dependent homs from the global internal semisimplicial index, then follows one
coherent route through face codes, join shapes, Yoneda representables,
two-dimensional sieves/fillers, and decalage. Its deferred inventory names
generic dimensions, degeneracies, all-dimensional Kan filling, and the whole
varying-fibre comparison without weakening the promoted claims.

The canonical-syntax authority records the critical index convention:
internal object `m` counts vertices, whereas conventional `Delta[n]` is
`StandardSimplex(succ n)`. The same convention corrects the earlier
representable two-simplex reference from `StandardSimplex(2)` to
`StandardSimplex(3)`. It also records comment notation for face codes,
diagrams, the four selected sieves, algebraic fillers, and decalage, while
making clear that no corresponding parser extension, generic `Kan` syntax,
whole cone-display equation, or codata declaration syntax is active.

The root and kernel READMEs, current-status report, nested repository guide,
check registries, examples, and report index now describe the same promoted
boundary. Active-reference lint, report-header lint, source-TOC validation,
shell parsing, Python compilation, and exact diff whitespace checks pass. The
assembled book and overview article are generated/released editorial
artifacts and were not silently changed by this implementation plan; a future
reader-facing simplicial chapter should receive its own evidence-backed
editorial plan.

## 17. Completion Definition

This persistent goal is complete when every row is either complete or
explicitly deferred behind a named prerequisite, the active public owners
compute at their stated boundary, positive and negative examples agree with
the plan, whole higher action is retained where claimed, documentation states
all nonclaims, the dedicated worktree is clean at a green local checkpoint,
and no excluded Git/publication/aggregate operation has occurred.
