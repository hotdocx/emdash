# Emdash v3.2 Cubical Arrow And Semicubical Codes Plan

Date: 2026-08-23 (America/Toronto)

Plan-ID: `CUBICAL-ARROW-SEMICUBICAL-CODES-V3.2`

Status: **completed implementation plan**.

Property-profile supersession (2026-08-27): historical rows below use the
profile names active at their checkpoints. Current recursive face actions and
frames carry the transparent property `IsPseudoFunctor`, not an abstract
`ReadablePseudoFunctorProfile`; see
`REPORT_EMDASH_V3_2_FUNCTOR_PROPERTY_PROFILE_MIGRATION_PLAN_2026-08-27.md`.

Corrective-Continuation:
`REPORT_EMDASH_V3_2_CUBICAL_INTERNALIZATION_AND_SIGMA_DERIVATION_PLAN_2026-08-24.md`.
The completed rows remain evidence for the specialized square orientation,
arbitrary-dimensional `{L,R,*}` action, and recursive frames. They do not
establish generic `homdc_int`, a Sigma-derived lax-arrow category, or full
cubical combinatorial adequacy.

Supersedes: no completed plan. This is the implementation child of the
completed cubical-dependent-hom plan. It reopens only the fully varying
endpoint, iterated cubical-arrow, and semicubical-code continuations deferred
there.

Depends-On: `emdash3_2.lp`; `emdash3_2_cubical_dependent_hom.lp`;
`emdash3_2_cubical_square_total.lp`; the active Sigma/Pi, ordinary/displayed
hom-action, strict-profile, truncation, and Nat infrastructure; the completed
semisimplicial face-code/index/realization modules as an implementation
pattern; and the current Foundations, canonical syntax, SOP, report index,
and persistent-goal Git workflow.

Infinity-Codex-Origin: session `019ffe39-2eb9-7080-88e3-06b77d69b8d1`;
definitive archived response
`0121_2026-08-23T16-59-58Z_01a02f8c-dfcf-7ad2-bc49-bfefdfcd0bef.md`.

Infinity-Codex-Decision-Responses: `infinity-codex:019ffe39-2eb9-7080-88e3-06b77d69b8d1:01a02f8c-dfcf-7ad2-bc49-bfefdfcd0bef`.

Side-Task-Ledger: `CASC-00`, `CASC-ARROW-1`, `CASC-COMP-2`, `CASC-FACES-3`,
`CASC-MAP-4`, `CASC-CUBE-5`, `CASC-CODE-6`, `CASC-INDEX-7`, `CASC-LEVEL-8`,
`CASC-ACTION-9`, `CASC-LAWS-10`, `CASC-FRAME-11`, `CASC-COMPARE-12`,
`CASC-EXTRA-13`, `CASC-DOC-14`, and `CASC-CLOSE-15`.

Branch: `goal/cubical-arrow-v3.2`

Worktree: `/home/user1/emdash1-cubical-arrow-v1`

Baseline: completed cubical-dependent-hom checkpoint
`c1f423c9116dc3fdece63ff9389d84fb6f005cfa`.

Parent plan:
`REPORT_EMDASH_V3_2_CUBICAL_DEPENDENT_HOM_PLAN_2026-08-23.md`.

Active code and this evolving ledger outrank archived conversation.

## 1. Objective

Turn the checked fixed-endpoint two-sided dependent hom into a genuinely
variable-boundary, recursively iterable cubical layer, then connect that layer
directly to the standard variable-dimensional semicubical word combinatorics.

The foundational dependency path is:

```text
homdc_
  -> CubicalArrow_cat
  -> CubicalArrow_func
  -> CubicalLevel(C,n)
  -> CubeFaceCode {L,R,*}
  -> whole semicubical face action.
```

The implementation must make an arbitrary square an object at the next arrow
level, so a cube can have six independently varying square faces. Merely
taking another hom between fixed-boundary squares does not satisfy the goal.

The following are comparison layers, not foundations:

```text
CubicalArrow_cat(C) ~= GrayHom_lax(WalkingArrow_cat,C)

homdc_[a] ~= homd_(E[a^op],...).
```

No Gray code, tensor, or `homd_parameter_func` may become a prerequisite of
the native cubical face-code interpreter.

## 2. Mathematical Core

### 2.1 Two-sided local hom

For

```text
E : K1^op -> Catd(K2)
u : E[x1][x2]
v : E[y1][y2],
```

the checked classifier is

```text
homdc_E(u,v)[a,b]
  = Hom_{E[x1][y2]}
      (E[x1][b](u),E[a^op][y2](v)),
```

covariant in `a : Hom_K1(x1,y1)` and contravariant in
`b : Hom_K2(x2,y2)`.

For `E=hom_int(id_C)`, an object is the square filler

```text
alpha : b o u ==> v o a.
```

### 2.2 Specialized intrinsic arrow category

The first implementation deliberately specializes the general two-sided
Grothendieck idea to the identity-Hom family:

```text
CubicalArrow_cat(C) : Cat.
```

Its constructor-visible objects are arrows:

```text
cubical_edge(x,y,u),
u : Hom_C(x,y).
```

Its Hom category is the existing nested-Sigma square total:

```text
Hom_{CubicalArrow(C)}
  (cubical_edge(x1,x2,u),cubical_edge(y1,y2,v))
  --> homdc_square_cat(hom_int(id_C),x1,y1,x2,y2,u,v).
```

Thus an arrow is the native term

```text
cubical_square(a,b,alpha) = (a,(b,alpha)).
```

The general `TwoSidedSigma_cat(E)` is a later abstraction. It must not be
postulated before the identity-Hom specialization reveals the exact
composition/interchange profile required of arbitrary `E`.

### 2.3 Arrow identities and composition

The identity square on `u : x -> y` has side identities and the identity
filler at `u`, modulo the current selected unit computations:

```text
id_square(u) = (id_x,(id_y,id_u)).
```

For

```text
alpha : b o u ==> v o a
beta  : d o v ==> w o c,
```

composition must expose the usual pasted cell

```text
(d o b) o u ==> w o (c o a),
```

obtained by whiskering `alpha` by `d`, whiskering `beta` by `a`, and composing
with the existing associativity/compositor comparisons. The current prototype
may use its tracked strict endpoint cuts, but the source and plan must record
which computation relies on them. No cubical-specific associativity equation
is permitted.

### 2.4 Whole endpoint faces

The arrow category owns whole functors

```text
cubical_src_func(C), cubical_tgt_func(C)
  : CubicalArrow_cat(C) -> C,
```

with computations

```text
src(x,y,u) = x              tgt(x,y,u) = y
src(a,b,alpha) = a          tgt(a,b,alpha) = b.
```

Arrow-level betas must project the nested Sigma square; point-only formulas
are insufficient because the later face-code action consumes whole functors.

### 2.5 Profiled functorial lifting

Every selected readable pseudofunctor carrier must lift:

```text
P : ReadablePseudoFunctorProfile(F)

CubicalArrow_func(F,P)
  : CubicalArrow_cat(C) -> CubicalArrow_cat(D).
```

An arbitrary normal-lax functor is insufficient: mapping the selected square
orientation requires the compositor forward at the source and inverse at the
target. The subsequent intrinsic-profile redesign reframes the existing
internal-action compositor to one readable post cell, supplies fixed-forward
`OmegaEquivAlong` for that cell, and derives the pre/right reverse adjustment
from a selected native inverse through the existing endpoint comparison. That
comparison is a documented adapter for the temporary global strict cut, not a
noncollapse theorem. The
mapped filler is

```text
post_compositor.to ; F_1[alpha] ; pre_compositor.from.
```

The lift maps an edge to `F[u]`, retains another hom action, and satisfies
whole source/target comparisons:

```text
src_D o CubicalArrow_func(F) ~= F o src_C
tgt_D o CubicalArrow_func(F) ~= F o tgt_C.
```

Runtime equality is not assumed if the active owners naturally provide typed
paths or transformations.

## 3. Recursive Cubical Levels

Define fixed dimensions first:

```text
CubicalLevel(C,0)       = C
CubicalLevel(C,succ n)  = CubicalArrow_cat(CubicalLevel(C,n)).
```

The intended readings are:

```text
Obj(CubicalLevel(C,1)) = edges
Obj(CubicalLevel(C,2)) = squares
Obj(CubicalLevel(C,3)) = cubes.
```

At dimension two, four edge-face functors are

```text
src_{Cub1}, tgt_{Cub1},
CubicalArrow_func(src_C), CubicalArrow_func(tgt_C).
```

An arrow in `CubicalLevel(C,2)` then has two ordinary endpoint squares plus
the actions of those four face functors: six square faces, with no face forced
degenerate by the classifier.

The generic Nat recursion must be attempted only after dimensions one and two
compute through the same constructors. A code-only facade that hides a
dimension-specific implementation does not satisfy this row.

## 4. Semicubical Word Codes

### 4.1 Raw and public codes

The standard semi-cube category has morphisms represented by words in
`{L,R,*}`. Introduce a curated indexed raw syntax parallel to the active
semisimplicial skip/keep syntax:

```text
raw_cube_nil

raw_cube_left(f)
  : RawCubeFaceCode(p,succ n)

raw_cube_right(f)
  : RawCubeFaceCode(p,succ n)

raw_cube_keep(f)
  : RawCubeFaceCode(succ p,succ n).
```

Equivalently, a code `p -> n` is a length-`n` word with exactly `p` stars.
Raw syntax owns structural substitution. Public `CubeFaceCode(p,n)` should
reuse the existing 0-truncation pattern so the resulting hom categories are
locally discrete while visible constructors continue to compute.

Identity is the all-star word. Composition substitutes an inner word into
the star positions of an outer word. The clauses must be structural and
exhaustive; no list equality, extensional function code, or ad hoc face-law
family is introduced.

### 4.2 Semicube category

Define the internal augmented semicube category:

```text
SemiCubePlus_cat : Cat

Obj(SemiCubePlus_cat) = Nat
Hom(p,n) = Path_cat(CubeFaceCode(p,n)).
```

Identity and composition delegate to the code owners. As with
`SemiDeltaPlus_cat`, arbitrary composition may remain at the generic category
owner while visible public codes compute through the raw structural
substitution.

### 4.3 Native code action

For a code `f : CubeFaceCode(p,n)`, construct a whole restriction functor

```text
cube_face_action(C,f)
  : CubicalLevel(C,n) -> CubicalLevel(C,p).
```

The raw recursion is the decisive architectural test:

```text
action(left f)
  = action(f) o cubical_src

action(right f)
  = action(f) o cubical_tgt

action(keep f)
  = CubicalArrow_func(action(f)).
```

The first two constructors fix the new coordinate; the star constructor
preserves it. No Gray equivalence or triangular `homd_int` comparison may be
used to define these clauses.

The whole laws are contravariant:

```text
action(id_n) ~= id_{CubicalLevel(C,n)}

action(g o f)
  ~= action(f) o action(g).
```

The comparison may initially be typed equality/path evidence if a runtime
fold would compete with stable owners. Face-specific rewrites are forbidden.

## 5. Comparison With Indexed Semicubical Frames

The usual presheaf presentation and the native cell tower remain distinct:

```text
semicubical diagram:
  SemiCubePlus_cat^op -> Cat/Grpd/Set

native cubical nerve level:
  n |-> CubicalLevel(C,n).
```

The goal is to assemble the code action into a whole category-valued or
groupoid-valued semicubical nerve once the identity/composition laws are
available.

The indexed-frame comparison must be recursive rather than a dimensionwise
record. At successor dimension, an object of `CubicalArrow_cat(Cub_n)` has:

- an `L` endpoint `n`-cube;
- an `R` endpoint `n`-cube;
- the preserved/cylindrical higher cell;
- inherited lower faces obtained by `CubicalArrow_func`.

This matches the left/right/star layers of the indexed semicubical frame. The
bounded acceptance boundary is:

1. generic `{L,R,*}` code action in variable dimension;
2. all `2n` face observations available through codes;
3. explicit dimensions zero through three;
4. dimension-two square boundary and dimension-three six-face cube agree with
   the native `CubicalArrow` projections;
5. a whole semicubical diagram if the code-action laws close; otherwise the
   exact whole-functor coherence prerequisite is recorded.

A theorem identifying every arbitrary semicubical set with a cubical nerve is
not intended; the native construction produces a canonical semicubical nerve
of an emdash category.

## 6. Derived Comparison Rows

After the native code action is green, separate rows may establish:

```text
CubicalArrow_cat(C)
  ~= GrayHom_lax(WalkingArrow_cat,C)

homdc_[a]
  ~= homd_(E[a^op],...).
```

The first requires a generic strict walking-arrow code and profile-aware Hom
comparison. The second may use a future `homd_parameter_func`. Failure or
deferral of either comparison cannot block the native semicubical code layer.

## 7. Explicit Nonclaims

This plan initially claims none of the following:

- a complete cubical type theory;
- Kan composition/filling;
- degeneracies, connections, reversals, or coordinate permutations;
- a symmetric monoidal or full Crans--Gray structure;
- general `TwoSidedSigma_cat(E)` composition for every arbitrary lax family;
- equivalence of every semicubical set with a nerve of one category;
- automatic positivity/productivity checking or user-defined inductives;
- removal of the historical global strict endpoint cuts;
- a global consistency, normalization, or confluence theorem.

Degeneracies and connections are later native operations:

```text
degeneracy: insert an identity arrow
connection: compose/merge adjacent arrow coordinates.
```

They must extend the same `CubicalArrow` tower and code category rather than
introduce a competing cubical representation.

## 8. Execution Ledger

| Row | State | Deliverable and acceptance boundary |
| --- | --- | --- |
| `CASC-00` | complete | Audited the clean parent and all worktrees; created `goal/cubical-arrow-v3.2` at exact checkpoint `c1f423c` in `/home/user1/emdash1-cubical-arrow-v1`; bootstrapped its own pnpm link graph; promoted the definitive `{L,R,*}`-driven architecture into this indexed plan; selected focused-only validation and local-checkpoint policy. |
| `CASC-ARROW-1` | complete for the constructor-visible vertical slice | `emdash3_2_cubical_arrow.lp` adds the stable `CubicalArrow_cat(C)`, nested dependent-Sigma arrow objects, transparent `cubical_edge`, transparent nested-Sigma `cubical_square`, and a Hom rule to the existing `homdc_square_cat`. The focused source/reviewer and owner probe are green; the extension LHS audit reports zero candidates. Malformed endpoints remain rejected by dependent constructor typing without a coercion or eta rule. |
| `CASC-COMP-2` | complete | `emdash3_2_cubical_arrow_composition.lp` defines post-whiskering of `alpha` by `d`, pre-whiskering of `beta` by `a`, their ordinary Hom-category composite, visible identity squares, and visible category composition. The desired filler at `(d o b) o u` and `w o (c o a)` typechecks without a cubical equation or unifier. The only strict-prototype reliance is the already-tracked identity/associativity endpoint conversion used to align bracketings; the cell term itself is generic action and composition. Focused source/reviewer, warning-enabled owner probe, and zero-candidate LHS audit are green. |
| `CASC-FACES-3` | complete | Whole source and target functors compute on arrow objects and square arrows. Their retained `fapp1_func` actions consume a visible square and recover `a` and `b`; after visible square pasting they recover `c o a` and `d o b`. Identity/composition agree with generic functoriality, so no duplicate whole-action owner or face equation is introduced. The first iterated-arrow use now depends only on `CubicalArrow_func`. |
| `CASC-MAP-4` | complete historical boundary; evidence shape superseded by the 2026-08-26/27 intrinsic-profile plan | `CubicalArrow_func(F,P)` remains the whole profiled lift, but its profile no longer supplies independent unit/post/pre arrows. The active redesign derives one readable cell from `fapp1_compositor`, supplies fixed-forward `OmegaEquivAlong` for it, and derives the pre/right reverse adjustment from a selected native inverse plus endpoint reframing. The reframe is explicitly a temporary strict-prototype adapter; edge/square action and retained higher action are unchanged. |
| `CASC-CUBE-5` | complete | `emdash3_2_cubical_square_level.lp` defines `CubicalSquare_cat(C)` as the first recursive arrow level. Outer source/target and `CubicalArrow_func` applied to inner source/target give four whole, independently noncollapsed edge-face functors; an arbitrary next arrow has its source and target square objects plus the four corresponding side-square actions. A visible square recovers all four independently supplied edges, every face retains a readable pseudo profile for another lift, and the focused source/reviewer plus zero-candidate LHS audit are green. No cube filler, face equation, rule, unifier, Gray comparison, or code syntax is added. |
| `CASC-CODE-6` | complete | `emdash3_2_semicubical_face_codes.lp` adds intrinsically indexed raw `{L,R,*}` words: a code `p -> n` has length `n` and exactly `p` stars. Six exhaustive structural clauses substitute the inner word only at outer stars. The public `CubeFaceCode` reuses the classified 0-truncation pattern; visible endpoint/keep constructors, all-star identity, and public composition compute. The reviewer checks both endpoint constructors, star consumption, a closed associative three-map chain, constructor noncollapse, and wrong-index rejection. The warning-enabled owner probe has exactly the inherited truncation warning count (`1151` versus baseline `1151`), and the strict LHS audit reports zero candidates. No list syntax, extensional function code, face-law family, or unifier is added. |
| `CASC-INDEX-7` | complete | `emdash3_2_semicubical_index.lp` adds `SemiCubePlus_cat`: objects compute to Nat dimensions, Homs to `Path_cat(CubeFaceCode(p,n))`, identity to the all-star code, and constructor-visible composition to the existing public substitution owner. Arbitrary composition remains at the generic category head. The reviewer checks distinct `L/R` cofaces, visible identity/composition, local discreteness, and wrong-dimension rejection. Its owner-position warning probe has the same inherited count as the code-only baseline (`1151`), and the strict LHS audit reports zero candidates with the three code indices documented as subject-reduction guards. No action, degeneracy, connection, broad fold, or unifier is added. |
| `CASC-LEVEL-8` | complete | `emdash3_2_cubical_levels.lp` defines `CubicalLevel_cat(C,n)` by genuine `nat_elim`: zero is `C`, and successor is `CubicalArrow_cat` of the previous level. Focused checks validate the generic successor equation and dimensions zero through three, with level two definitionally recovering `CubicalSquare_cat(C)`. The successor does not collapse back to `C`. This is a native recursive category classifier, not a code decoder; it adds no rule, action, profile, or unifier. |
| `CASC-ACTION-9` | complete | `emdash3_2_semicubical_face_action.lp` interprets every raw `{L,R,*}` code as dependent data pairing a whole restriction functor with its readable pseudo profile. `L/R` compose the recursive action after source/target; star applies `CubicalArrow_func` using the recursively retained profile. Public set-truncated codes decode through curated raw sethood and retain visible computation. The reviewer validates dimension-one source/target, the all-star lift, both dimension-two inner-face recursions, the deliberately retained outer identity-action factor, generic profile availability, wrong-index rejection, and another hom action. The owner-position warning probe matches its dependency baseline exactly (`1151`), and the strict LHS audit reports zero candidates. Recursive profile histories are intentionally not collapsed to independently selected face profiles; that coherence belongs to `CASC-LAWS-10`. No face-specific equation, Gray comparison, parameterized triangular hom, degeneracy, connection, or unifier is added. |
| `CASC-LAWS-10` | complete | `emdash3_2_semicubical_nerve.lp` assembles `semicubical_nerve_func(C) : SemiCubePlus_cat^op -> Cat_cat`. Its object action judgmentally returns `CubicalLevel_cat(C,n)`. Its generic arrow action is related propositionally to the computing, profile-retaining `cube_face_action_func`; a direct runtime arrow beta was probed and rejected because it added 16 unjoinable overlaps with generic strict identity/composition cuts. Nested restricted truncation induction instead proves named public substitution equal to arbitrary `SemiCubePlus_cat` composition. Transporting the nerve's generic `fapp1_id_path` and `fapp1_comp_path` across the arrow observation derives whole all-star identity and contravariant public composition. The final warning probe returns exactly to the dependency baseline (`1151`), the strict LHS audit reports zero candidates, and the reviewer retains the whole next action. No face-specific rewrite, broad category fold, or unifier is added. |
| `CASC-FRAME-11` | complete | `emdash3_2_semicubical_frames.lp` constructs the immediate boundary as an existing `FiniteFamily`: its count adds two at every successor, its first pair is the new coordinate's `L/R`, and removing that pair leaves definitionally the star-map of the preceding family. Thus all `2n` faces are exposed without a new `Fin`/list grammar. Because public truncation recursors do not fuse at arbitrary inputs, restricted induction first derives raw-decoder paths for public `L/R/star`; ordinary path action then gives whole action-constructor paths. The new pair compares to native source/target through the all-star identity law, while inherited faces compare to profiled `CubicalArrow_func`; object-level projections carry the same recursion. The reviewer checks counts `0,2,4,6`, generic family observations, all four independent edges of a visible square, and the two-new-plus-four-inherited six-face shape of a visible cube. Focused source/reviewer and strict zero-candidate LHS audit are green; the warning probe remains at the exact nerve baseline (`1151`). No dimension-specific record, filler, face equation, rewrite, or unifier is added. |
| `CASC-COMPARE-12` | deferred | Gray/walking-arrow and `homd_parameter_func` comparisons are semantic tests after the native action; neither blocks `CASC-ACTION-9`. |
| `CASC-EXTRA-13` | deferred | Degeneracies, connections, reversals, permutations, general `TwoSidedSigma(E)`, and Kan operations require their own selected consumers after the semicubical face layer. |
| `CASC-DOC-14` | complete | Synchronized the mathematician-facing Foundations, current status/SOP, canonical notation, `emdash2/README.md`, both AGENTS authority inventories, source/metrics registries, report index, focused reviewer examples, and strict check catalog. The stale claim that nondegenerate cubical variation was blocked by `homd_parameter_func` is replaced by the active intrinsic-arrow/semicubical-nerve path; the general parameter action remains a comparison row. The notation authority explicitly distinguishes judgmental level/object computation from propositional public-constructor and whole nerve-arrow comparisons. Proportional health evidence consists of each promoted owning source and reviewer checking below 90 seconds, exact warning baselines on every rule-bearing tranche, zero-candidate strict LHS audits, source-TOC, report-header, catalog-strict, and diff hygiene. Per the plan's explicit policy, the unchanged broad health/registered/example/repository aggregates were not rerun. |
| `CASC-CLOSE-15` | complete | Audited every row: foundational rows `CASC-00` through `CASC-FRAME-11` and documentation row `CASC-DOC-14` are complete; `CASC-COMPARE-12` and `CASC-EXTRA-13` are explicitly deferred behind named future consumers rather than blockers. The final focused source/reviewer, report-header, catalog-strict, source-TOC, strict LHS, and diff gates are green; exact warning comparisons remain at their recorded baselines. The branch contains eleven bounded implementation checkpoints after baseline `c1f423c` plus this documentation/closure checkpoint. Broad health/registered/example/repository aggregates were deliberately omitted under the plan's proportional policy. No push, merge, tag, publication, PR, history rewrite, branch deletion, or worktree removal was performed. |

## 9. Validation And Git Policy

- Keep every Lambdapi invocation bounded to 90 seconds.
- Use ignored focused probes before promoting stable heads, rules, or
  unifiers.
- Run only the owning source/reviewer and nearest static audits during an
  implementation tranche.
- Eagerly avoid full registered, example, health, repository, TypeScript, or
  print aggregates unless omission blocks classification of a genuinely
  changed boundary.
- Do not rerun `make health` merely because source registries change. Record
  focused evidence and defer the report unless a later explicit release
  boundary authorizes the known broad rebuild.
- Treat warnings as diagnostics, not automatic vetoes. Compare the owning
  warning surface for every new rule.
- Follow LHS minimality, owner-position, subject-reduction, and typed
  `eq_refl` SOP for every unifier. Prefer no unifier.
- Preserve one wrong-orientation/wrong-dimension negative near every new
  projection family.
- The user authorizes this dedicated branch/worktree and SOP-compliant local
  checkpoint commits after bounded green tranches and synchronized ledger.
- Do not push, merge, publish, tag, create a PR, amend/rebase/reset, delete a
  branch, or remove a worktree without separate explicit authorization.

## 10. Persistent-Goal Launch Prompt

> Continue the emdash v3.2 intrinsic cubical-arrow and semicubical-code
> implementation in `/home/user1/emdash1-cubical-arrow-v1` on branch
> `goal/cubical-arrow-v3.2`, delegating the exact mathematics, sequencing,
> evidence, exclusions, validation, Git discipline, and completion boundary
> to
> `emdash2/reports/REPORT_EMDASH_V3_2_CUBICAL_ARROW_AND_SEMICUBICAL_CODES_PLAN_2026-08-23.md`
> and its active authority chain. Begin from baseline
> `c1f423c9116dc3fdece63ff9389d84fb6f005cfa`. Work one dependency-ready row
> at a time, starting with `CASC-ARROW-1`; keep `homdc_`, intrinsic
> `CubicalArrow_cat`, functorial lifting, and `{L,R,*}` face action on the
> foundational path. Gray/walking-arrow and `homd_parameter_func` are
> comparison rows only. Keep every Lambdapi invocation bounded to 90 seconds
> and eagerly avoid broad registered/example/health/repository aggregates
> unless omission blocks classification of genuinely changed behavior. The
> user authorizes SOP-compliant local checkpoint commits on this dedicated
> branch after each bounded green tranche and synchronized ledger. Do not
> push, merge, publish, tag, create a PR, rewrite history, delete branches, or
> remove worktrees. Do not mark the goal complete until every scoped row is
> implemented, rejected with durable evidence, or explicitly deferred behind
> a concrete prerequisite and all affected authorities and proportional gates
> are synchronized.

## 11. Completion Definition

The bounded goal is complete when:

1. `CubicalArrow_cat(C)` has computing arrow objects and square Homs;
2. identity, composition, source, and target are whole and computational at
   the promoted constructor surface;
3. `CubicalArrow_func` maps edges and squares and retains another action;
4. a dimension-two arrow exposes six independently varying square faces;
5. raw/public `{L,R,*}` codes, structural composition, and the internal
   semicube category are active;
6. `CubicalLevel(C,n)` and code-selected face action work in variable
   dimension and at least through dimension three;
7. identity/composition of face action are whole or have one exact recorded
   coherence prerequisite;
8. the native boundary is compared with indexed semicubical frames without
   claiming every presheaf is a nerve;
9. Gray and triangular comparisons remain derived and cannot silently become
   foundations;
10. all nonclaims and deferred extensions remain accurate;
11. required documentation, examples, catalogs, and proportional evidence are
    synchronized without an unnecessary aggregate; and
12. the dedicated branch is clean at reviewed local checkpoints.
