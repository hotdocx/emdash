# Emdash v3.2 Cubical Yoneda And Gray-Cube Adequacy Plan

Date: 2026-08-25 (America/Toronto)

Plan-ID: `CUBICAL-YONEDA-GRAY-CUBE-ADEQUACY-V3.2`

Status: **completed implementation plan**.

Supersedes: no completed plan. It is the semantic-adequacy continuation of
`REPORT_EMDASH_V3_2_CUBICAL_INTERNALIZATION_AND_SIGMA_DERIVATION_PLAN_2026-08-24.md`
and a consumer of the completed selected right-Gray closure in
`REPORT_EMDASH_V3_2_PROFILED_GRAY_HOM_AND_I_TENSOR_I_PLAN_2026-08-17.md`.

Depends-On: `emdash3_2_cubical.lp`, especially `StandardSemicube`,
`semicubical_nerve_func`, `CubicalLevel_cat`, `LaxArrow_cat`, and the whole
`{L,R,*}` action; the generic `fib_cov_transf`, displayed component, and
presheaf owners in `emdash3_2.lp` and `emdash3_2_presheaves.lp`; and
`emdash3_2_gray_profiles.lp`, `emdash3_2_gray_right_closure.lp`,
`emdash3_2_gray_walking_square.lp`, `emdash3_2_gray_interchanger.lp`, and
`emdash3_2_walking_arrow.lp`.

Side-Task-Ledger: `CGCA-00`, `CGCA-AUDIT-1`, `CGCA-YONEDA-2`,
`CGCA-YONEDA-BETA-3`, `CGCA-GRAY-ORIENT-4`, `CGCA-WALKING-BRIDGE-5`,
`CGCA-GRAYCUBE-6`, `CGCA-GRAY-DECODE-7`, `CGCA-DIM-8`,
`CGCA-SIMPLICIAL-DEFER-9`, `CGCA-DOC-10`, and `CGCA-CLOSE-11`.

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`; decisive responses
`0129_2026-08-25T05-20-17Z_01a03758-e44b-7961-be86-97ec28ed39f8.md`
and
`0130_2026-08-25T06-12-19Z_01a03786-90f3-7331-b29f-75e812c512e9.md`.

Infinity-Codex-Decision-Responses: `infinity-codex:019ffe39-2eb9-7080-88e3-06b77d69b8d1:01a03758-e44b-7961-be86-97ec28ed39f8`, `infinity-codex:019ffe39-2eb9-7080-88e3-06b77d69b8d1:01a03786-90f3-7331-b29f-75e812c512e9`.

Branch: `goal/gray-cube-adequacy-v3.2`

Worktree: `/home/user1/emdash1-gray-cube-adequacy-v1`

Baseline: completed cubical declaration-clarification checkpoint
`ce9da4210218c7330dc0a4aa0304568db776c7a8`.

Active code, this plan, and measured owner-position probes outrank archived
conversation and literature-derived expectations.

## 1. Objective

Establish two complementary object-level readings of the native cubical
levels:

```text
representable/Yoneda realization
  StandardSemicube(n) -> N_cube(C)
    <-> native n-cube,

geometric Gray-cube observation
  strict realization GrayCube_mu(n) -> C
    -> native n-cube.
```

The first demonstrates coherent internal computation of ordinary
`{L,R,*}` face combinatorics. The second demonstrates that an external
mathematician's visual lax cube—vertices, coordinate arrows, directed
interchanger, and higher fillers—has the same object-level meaning as an
emdash native iterated-lax-arrow cell.

The public claims remain object-level during this plan. Whole functorial
machinery may still be required internally to make the variable-dimensional
construction recurse; no inverse functor or mapping-category equivalence is
claimed until those object computations are stable.

## 2. Two Adequacy Questions Must Remain Distinct

### 2.1 Representable/Yoneda realization

The existing objects are

```text
N_cube(C) := semicubical_nerve_func(C)

N_cube(C)[n] = CubicalLevel_cat(C,n)

StandardSemicube(n)[p]
  = Hom_{SemiCubePlus}(p,n)
  = Path_cat(CubeFaceCode(p,n)).
```

A map

```text
eta : Hom_Psh(StandardSemicube(n),N_cube(C))
```

assigns a native `p`-cell to every face code `f:p->n`, coherently under face
substitution. Evaluation at the identity face gives

```text
eta |-> eta[n](cube_face_identity(n))
  : Obj(CubicalLevel_cat(C,n)).
```

Conversely, a native cube `X` gives its Yoneda section

```text
X |-> (f |-> cube_face_action_func(f)[X]).
```

This is a coherent re-presentation of an already-native cube. It validates the
internal index, face action, and naturality, but is not an independent
geometric model.

### 2.2 Geometric/computadic Gray-cube observation

The independent comparison has the form

```text
H : StrictFunctor(GrayCube_mu(n),C)
  |-> gray_cube_observation(H)
      : Obj(CubicalLevel_cat(C,n)).
```

Here `GrayCube_mu(n)` contains the vertices, coordinate arrows, directed
interchangers, and higher cubical fillers as generators and relations before
the map to `C` is chosen. This comparison is the stronger semantic statement
for an external audience's usual visual lax cubes.

The two claims coincide only after an independent theorem identifies the
native nerve level with maps from the chosen Gray cube. Yoneda alone cannot
establish that identification because `N_cube(C)[n]` is already defined to be
the native level.

## 3. Why `GrayHom_lax` Alone Does Not Repair A Cartesian Cube

In the active profile:

```text
Obj(GrayHom_lax(A,C))
  = StrictFunctorData(A,C)

Hom_{GrayHom_lax(A,C)}(F,G)
  = Transf_cat(carrier(F),carrier(G)).
```

Thus `GrayHom_lax` changes arrows and higher cells between strict functors. It
does not change the relations already imposed in the source category. An
object of `GrayHom_lax([1]^n,C)` is still a strict realization of a Cartesian
cube; strict equalities in `[1]^n` remain strict in `C`.

The laxity of one cube must instead live in the shape:

```text
GrayCube_mu(n) = [1] tensor_mu ... tensor_mu [1].
```

Then a strict functor out of that shape maps its tensor-generated
interchangers to selected directed cells in `C`. `GrayHom_lax` is relevant
through the biclosed comparison

```text
GrayHom_mu(A tensor_mu B,C)
  ~= GrayHom_mu(A,GrayHom_mu(B,C)),
```

not as a way of weakening the objects of a mapping category with unchanged
Cartesian source.

## 4. Literature Boundary

The proposed geometric shape is established mathematics, not an emdash-only
invention:

- Gurski's review gives the generators-and-relations Gray tensor of strict
  2-categories, including its interchanger, and the universal property
  classifying cubical functors:
  <https://emis.de/ft/8985>.
- Campion--Maehara call `[1]^{tensor n}` the Gray cubes, describe them as lax
  `n`-dimensional cubes, and characterize the lax Gray tensor by a monoidal
  biclosed universal property:
  <https://arxiv.org/abs/2304.05965>.
- Campion proves that Gray tensor powers of the arrow category form a dense
  cube category for weak `(infinity,infinity)`-categories:
  <https://arxiv.org/abs/2209.09376>.
- Ara--Lucas establish the monoidal Gray tensor setting for strict
  omega-categories:
  <https://arxiv.org/abs/1909.13564>.

These sources do not settle the project's notation `R` versus the literature's
left/right lax/oplax conventions. They establish the family of candidate
shapes; emdash must still check its selected direction computationally.

## 5. Orientation And Low-Dimensional Acceptance

There are lax, oplax, and pseudo variants. The native emdash square is

```text
alpha : b o u ==> v o a.
```

The chosen Gray interchanger must have this direction. Depending on convention
the correct source may be `A tensor B`, `B tensor A`, a left/right internal
hom, or an opposite. No terminology-only verdict is accepted.

The decisive dimension-two probe must compare:

```text
GrayWalkingSquare_cat
  = GrayTensor_R(WalkingArrow,WalkingArrow)
```

with the visible native square in

```text
LaxArrow_cat(GrayWalkingSquare_cat).
```

It must identify the four derived vertices, the four coordinate arrows, the
two composite routes, and the actual `gray_interchanger` source and target. If
the current interchanger has the reverse direction, the plan must select a
factor swap/opposite or rename the profile; it must not add an endpoint rewrite
or silently call the reverse cell "lax".

The checked verdict is now precise. The selected right-Gray cell has readable
direction

```text
v o a ==> b o u,
```

where `u,v` are the inner-coordinate arrows and `a,b` are the outer-coordinate
arrows. A generic missing projection beta was promoted at its true
`tapp1_at_transf` owner:

```text
tapp1_at_transf(epsilon,X)[g][f] = epsilon[g o f].
```

It exposes the already-existing ordinary off-diagonal action, retains
represented composition on the right, and is warning-neutral (`1290 =
1131 + 159`) against the unchanged baseline. Whole strict paths, stable
postcomposition, and the existing pre/right PathOut reframe then give
first-class comparisons from the formal endpoints to both raw composites.

No directed cell is inverted. Instead the coordinate-swapped assignment

```text
native source/target edges := a,b
native side arrows         := u,v
```

turns the same cell into the native boundary

```text
v o a ==> b o u.
```

`gray_interchanger_swapped_square` checks this as an actual arrow of
`CubicalArrow_cat(GrayWalkingSquare_cat)`, while the unswapped
`cubical_square` application is rejected.

## 6. Cubical Yoneda Object Slice

The first implementation tranche should use existing generic owners.

### 6.1 Section from a native cube

For `X : Obj(CubicalLevel_cat(C,n))`, the expected whole map is

```text
cubical_yoneda_section(C,n,X)
  : Hom_Psh(StandardSemicube(n),N_cube(C)).
```

The semantic body should be the existing represented covariance section:

```text
fib_cov_transf(
  Op_cat(SemiCubePlus_cat),
  semicubical_nerve_func(C),
  n,
  X).
```

The proof-time Yoneda/represented-source comparison may be used if the public
`StandardSemicube` and `FibCov_source_catd` heads remain distinct. No new
presheaf naturality family is permitted.

### 6.2 Evaluation at the identity face

For

```text
eta : Hom_Psh(StandardSemicube(n),N_cube(C)),
```

the expected object is

```text
cubical_yoneda_eval(C,n,eta)
  := Fibre_func(eta,n)[cube_face_identity(n)].
```

This uses the existing displayed-functor component evaluator. It must not
introduce a pointwise natural-transformation record.

### 6.3 First beta

The selected first computation is

```text
cubical_yoneda_eval(cubical_yoneda_section(X)) = X.
```

Probe judgmental equality first. If the generic represented and public
presheaf heads retain different stable histories, derive a typed path through
their existing comparison. Do not add a broad Yoneda fold or claim the full
eta law.

## 7. Transformation-Graph Bridge

The orientation audit rejects the previously proposed whole functor

```text
GrayHom_lax(WalkingArrow,C) -> LaxArrow_cat(C).
```

Its object map would send a strict walking map `F` to the edge `F[g]`, but an
arrow `epsilon:F=>G` has the selected right-Gray cell in the reverse direction
from the square between those two edges. The dimension-one object observation
remains valid; it simply does not extend to that whole functor for this
profile.

The coordinate-swapped result identifies the scalable bridge instead. Every
ordinary transformation

```text
epsilon : F => G,       F,G : B -> C,
```

should induce its whole **transformation graph**

```text
gray_transf_lax_arrow_func(epsilon)
  : B -> LaxArrow_cat(C)

y |-> (F[y] -> G[y], epsilon[y])

g |-> square(
       epsilon[y], epsilon[z],
       F[g], graph_target_side(g),
       graph_target_side(g) o epsilon[y]
         ==> epsilon[z] o F[g]).
```

The square filler is the existing post/left internal-action cell with the
typed endpoint reframe established by `CGCA-GRAY-ORIENT-4`. Thus this is not a
new naturality record. The implementation should derive the whole functor
through the existing hom/Sigma totalization and retained `tapp*` action; an
opaque object-and-arrow constructor is not acceptable.

The completed implementation sharpens the generic-lax reading. The retained
target side has the correct type

```text
graph_target_side(g) : Hom_C(G[x],G[y]),
```

but remains the family-natural total-base-change/internal-action projection;
it is not judgmentally or propositionally identified here with the separately
named term `G[g]`. That stronger reading belongs at the selected strict
profile required by the Gray decoder, not in the generic ambient graph. The
source side does compute to `F[g]`, and the remaining nested-Sigma projection
is already a cell with the displayed native lax-square boundary above.

`emdash3_2_gray_transformation_graph.lp` now constructs the whole graph without
a graph primitive. Its source section is the new generic ordinary represented
identity section `(y,id_y)`—the covariant mirror of the pre-existing
self-comma section. Family-natural `sigma_pullback_total_transf`, represented
Sigma reindex accumulation, and proof-time opposite/reindex comparison remove
the former equality-transport scaffolding while preserving each whole action.
Objects have a typed path to the visible edge `epsilon[y]`; arrows expose the
source side, retained target side, directed filler, and another whole hom
action. No Sigma eta, pointwise naturality record, endpoint collapse, or
graph-specific rule is added.

For

```text
H : StrictFunctorData(GrayTensor_R(WalkingArrow,B),C),
```

right curry produces a strict walking map into `GrayHom_lax(B,C)`. Its action
on the walking generator is a transformation between two `B`-diagrams, and
the graph above is therefore a strict candidate `B -> LaxArrow_cat(C)`. This
is the recursive successor input required by the Gray-cube decoder.

## 8. Fixed-Bracketing Gray Cubes

The selected tensor has no unit comparison, so the implemented recursion uses
the predecessor of the positive geometric dimension:

```text
GrayCubePos_R(0)       = WalkingArrow_cat
GrayCubePos_R(succ n)  = GrayTensor_R(WalkingArrow_cat,GrayCubePos_R(n)).
```

Thus index `n` denotes the `(n+1)`-dimensional cube. The first three values are
judgmentally `I`, `I tensor_R I`, and `I tensor_R (I tensor_R I)`. This avoids
inventing a dimension-zero unit for a tensor whose unit law is outside the
selected right-closure boundary.

This prepends the new coordinate and matches the selected right-closure
currying order

```text
GrayHom_lax(GrayTensor_R(WalkingArrow,GrayCubePos_R(n)),C)
  ~= GrayHom_lax(WalkingArrow,GrayHom_lax(GrayCubePos_R(n),C)).
```

Fixed bracketing is sufficient for an object-level first theorem. The plan
does not claim tensor parameter functoriality, a unit comparison at dimension
zero, associativity between alternate bracketings, coordinate permutations,
or full Crans--Gray monoidality.

## 9. Gray-Cube Decoder

The implemented scalable object owner uses the predecessor index:

```text
gray_cube_observation(C,n)
  : StrictFunctorData(GrayCubePos_R(n),C)
    -> Obj(CubicalLevel_cat(C,succ n)).
```

Its induction hypothesis is uniform in the target category:

```text
Pi C,
  StrictFunctorData(GrayCubePos_R(n),C)
    -> Obj(CubicalLevel_cat(C,succ n)).
```

The checked recursion reads schematically

```text
decode_1(H)
  = (H[src],H[tgt],H[generator])

decode_(n+1)(H)
  = shift_n(
      decode_n(
        LaxArrow_cat(C),
        strict_graph_data(
          gray_curry_R(H)[walking_generator]))).
```

`strict_gray_transf_graph_data` is selected only when the transformation's two
endpoint diagrams already carry strict codes. Its decoder head remains stable
so the profile-local compositor computes; a whole carrier path supplies the
transparent graph reading without a competing runtime fold. The canonical
`cubical_level_shift_path` is proved by Nat induction and turns the recursive
cell over `LaxArrow(C)` into the next cubical level over `C`.

Acceptance is checked both at selected low dimensions and at variable `n`.
At dimension two, `emdash3_2_gray_cube_dimension2.lp` exposes the actual
internal-action cell selected by the graph, in the same coordinate-swapped
native direction as the earlier interchanger. Its target side retains the
total-base-change history; `gray_interchanger_readable` has additionally
reframed that side, so a direct equality would be the wrong acceptance test.
At dimension three, the existing variable-dimensional immediate frame applied
to the decoded object gives six square faces, while the graph itself retains
another whole hom action. No hand-written six-face record is used.

## 10. Simplicial Analogue

The existing substantive simplicial object operation is

```text
H : Functor(DirectedSimplex_cat(n),C)
  |-> ordinal_dependent_simplex_observation(H).
```

A symmetric Yoneda operation would require a whole native dependent-simplex
semisimplicial nerve `N_delta(C)` with a uniform level classifier. That level
is not yet settled: the current code has coherent mapping levels, intrinsic
dependent codes, mapped observations, and faces, but not one whole native
level category at every `n`.

This plan therefore records but does not implement the simplicial Yoneda
analogue. It is a later organization/coherence task, not a prerequisite for
the existing ordinal decoder or the cubical adequacy results.

The closing audit identifies the exact missing object rather than a missing
face algorithm. `CoherentNerveLevel(C,n)=Functor(DirectedSimplex_cat(n),C)` is
the geometric mapping side and cannot also serve as the independent native
level without making the comparison circular. The intrinsic dependent-simplex
codes, mapped decoder, nonempty-face action, and canonical ordinal-source
recursion already work at arbitrary variable dimension, but their decoded
categories vary with the stored flag; they do not yet assemble into one
category `DependentSimplexLevel_cat(C,n)` at each `n`.

A later simplicial Yoneda tranche should therefore construct one whole native
semisimplicial nerve

```text
N_delta(C) : SemiDeltaPlus_cat^op -> Cat_cat
N_delta(C)[n] = DependentSimplexLevel_cat(C,n),
```

whose object/face action factors the existing intrinsic code machinery. Only
then should it add the representable section/evaluation and compare the
independent ordinal operation
`Functor(DirectedSimplex_cat(n),C) -> DependentSimplexLevel_cat(C,n)`. Join
identity/composition uniqueness and the changing-boundary classifier remain
the named prerequisites. No part of that assembly is required by the now
complete cubical object decoder.

## 11. Explicit Nonclaims

This plan does not initially claim:

- a full Yoneda equivalence or eta law;
- an inverse geometric decoder;
- equivalence of Gray mapping categories and native cubical levels;
- tensor parameter functoriality, mirror closure, associators, unitors, or
  coordinate symmetries;
- equality of all lax/oplax/pseudo conventions;
- degeneracies, connections, reversals, or Kan filling;
- a whole native dependent-simplex semisimplicial nerve;
- global normalization, confluence, canonicity, or consistency.

## 12. Execution Ledger

| Row | State | Deliverable and acceptance boundary |
| --- | --- | --- |
| `CGCA-00` | complete | Created `goal/gray-cube-adequacy-v3.2` at exact checkpoint `ce9da42` in `/home/user1/emdash1-gray-cube-adequacy-v1`; bootstrapped its own pnpm link graph and promoted this living plan. |
| `CGCA-AUDIT-1` | complete | Re-audited the generic represented covariance/component ladder, public Yoneda facade, native nerve/action, strict-code Gray profile, selected right closure, walking-square/interchanger, derived lax-arrow total, and recursive cubical levels. The literature establishes Gray tensor powers of the arrow as the geometric shapes but does not settle the project's `R`/lax naming; the exact dimension-two orientation remains isolated in `CGCA-GRAY-ORIENT-4`. The first concrete missing API was only the named cubical Yoneda section/evaluation, not a new naturality owner. |
| `CGCA-YONEDA-2` | complete | `emdash3_2_cubical_yoneda.lp` transparently defines `cubical_yoneda_section` by `fib_cov_transf` and `cubical_yoneda_eval` by the existing fibre functor at `cube_face_identity(n)`. The arbitrary-`C,n` source and reviewer are green; no pointwise naturality family, rule, or unifier is added, and the section retains the generic displayed/face-code action. |
| `CGCA-YONEDA-BETA-3` | complete | Evaluation of the selected section computes to `semicubical_nerve_action_func(C,n,n,id_n)[X]`, not judgmentally to `X`. `cubical_yoneda_beta` is therefore derived by applying object evaluation to the nerve's existing whole `fapp1_id_path`; it adds no equality axiom and claims no eta law. The rule-free source has zero LHS candidates and exactly the dependency warning count (`1310`). |
| `CGCA-GRAY-ORIENT-4` | complete | Checkpoint `d288339`. Promoted the generic third projection `tapp1_at_transf(epsilon,X)[g][f] -> epsilon[g o f]` at the represented-composition owner. Kernel, central diagnostics, typed endpoint probe, dedicated positive/negative reviewer, strict LHS audit, strict catalog, and exact warning comparison are green; warnings remain `1290 = 1131 + 159`. `emdash3_2_gray_interchanger_orientation.lp` derives first-class stable-to-readable paths and a capped `v o a ==> b o u` cell without endpoint collapse. Swapping coordinate roles constructs `gray_interchanger_swapped_square` in the native `CubicalArrow_cat`, while the unswapped application is rejected. |
| `CGCA-WALKING-BRIDGE-5` | complete, checkpoint `6a9d54b` | `emdash3_2_gray_transformation_graph.lp` transparently constructs `epsilon:F=>G |-> (B -> LaxArrow_cat(C))` from the whole internal action, the new generic ordinary represented identity section, family-natural Sigma base change, and opposites. Objects read as native component edges; arrow projections expose `F[g]`, a retained target side in `Hom(G[x],G[y])`, the coordinate-swapped native filler, and another hom action. The generic lax target side is deliberately not equated with the separate term `G[g]`; strict-profile packaging is the next decoder prerequisite. No graph primitive, Sigma eta, pointwise naturality record, graph-specific rule, or new warning is added. The earlier whole `GrayHom_lax(WalkingArrow,C) -> LaxArrow_cat(C)` proposal remains rejected. |
| `CGCA-GRAYCUBE-6` | complete, checkpoint `5871e30` | `emdash3_2_gray_cubes.lp` defines `GrayCubePos_R(n)` by genuine Nat recursion, with predecessor index `n` denoting geometric dimension `n+1`. The dedicated reviewer checks dimensions one through three as `I`, `I tensor_R I`, and `I tensor_R (I tensor_R I)`. The rule-free module claims no tensor unit, alternate bracketing, associator, coordinate permutation, or full monoidal structure. |
| `CGCA-GRAY-DECODE-7` | complete, checkpoint `79a8250` | `emdash3_2_gray_transformation_graph_profile.lp` adds the selected strict-code closure for graphs of transformations between strict-coded endpoint diagrams, retaining a stable strict carrier plus a whole path to the transparent graph. `emdash3_2_gray_cube_decoder.lp` defines `gray_cube_observation(C,n)` by one internal Nat recursion uniform in `C`: dimension one evaluates the walking map, and each successor curries, takes the generator, packages its graph, recurses in `LaxArrow(C)`, and applies the proved cubical-level shift. The rule-free decoder is arbitrary in variable `n`; its reviewer checks the zero/successor computations, dimensions one through three, the recursive carrier path, and recovery of the existing walking-square coevaluation inputs. No source generation, dimension-specific filler, inverse, or mapping-category equivalence is added. |
| `CGCA-DIM-8` | complete, checkpoint `cd23484` | Dimensions one through three and the arbitrary-`n` recursion are checked. The identity realization of `I tensor_R I` recovers the exact existing coevaluation source/target strict codes and outer transformation; `emdash3_2_gray_cube_dimension2.lp` names the actual retained target side, coordinate-swapped internal-action interchanger, and next whole action. A direct equality with `gray_interchanger_readable` is intentionally rejected as the wrong boundary because that older name has additionally reframed the target side. `gray_cube_immediate_faces` applies the existing variable-dimensional frame to every decoded cube, yielding four edges in dimension two and six square faces in dimension three without a bespoke record. |
| `CGCA-SIMPLICIAL-DEFER-9` | complete, documented deferral at `0835e22` | The existing ordinal observation, intrinsic dependent codes, mapped decoder, faces, and variable-dimensional canonical source are sufficient object algorithms but do not yet form one native category `DependentSimplexLevel_cat(C,n)` or one whole nerve `N_delta(C)`. `CoherentNerveLevel(C,n)` is the independent geometric mapping side and cannot be reused without circularity. A later tranche must assemble the changing-boundary native levels and whole face action before adding a simplicial Yoneda section/evaluation; join uniqueness and the changing-boundary classifier are the exact prerequisites. No implementation is needed for cubical adequacy. |
| `CGCA-DOC-10` | complete, checkpoint `0835e22` | Synchronized the living plan, Foundations, current status/SOP, canonical notation, root and `emdash2` READMEs, report index, `AGENTS.md`, source/metrics registries, focused reviewers, and generated check catalog. The exact proportional validation and the stopped long aggregate/health attempts are recorded rather than overstated; the health report remains intentionally deferred because the changed core hash would force a long repository-wide refresh that is not needed to classify this branch. |
| `CGCA-CLOSE-11` | complete, closure checkpoint pending | Every scoped row is implemented or explicitly deferred behind a named prerequisite. The exact checkpoint chain is recorded below; the dedicated branch is clean before this final ledger edit. No push, merge, publication, tag, PR, history rewrite, branch deletion, or worktree removal was performed. |

### 12.1 `CGCA-WALKING-BRIDGE-5` validation boundary

The promoted source, dedicated reviewer, and central diagnostics check under
the uniform 90-second ceiling. The strict LHS audit reports zero unreviewed
candidates, and warning diagnostics remain exactly the pre-tranche baseline
`1290 = 1131 critical pairs + 159 replaceable variables`. Source TOC,
catalog strictness, report headers, active references, Python syntax, shell
syntax, and `git diff --check` are green.

The full registered-source `make check` and the health refresh were stopped
after they expanded into long aggregates over unchanged mathematics. Their
partial results are not claimed as gates. This is the plan-authorized
proportional-validation boundary: the changed kernel, central diagnostics,
new source, and new reviewer have each checked directly; health/report-wide
refresh remains for `CGCA-DOC-10` or the eventual close boundary if it is then
needed to classify the release.

`CGCA-GRAYCUBE-6` adds only one transparent Nat-recursive source and a focused
reviewer. Both direct checks are green; it changes no rule, unifier, warning
family, or central diagnostic, so the preceding warning/LHS evidence carries
forward unchanged.

`CGCA-GRAY-DECODE-7` adds a selected strict code and carrier path, followed by
one rule-free decoder and focused reviewers. Direct source/reviewer checks are
green. The attempted runtime carrier fold was rejected during probing because
it erased the strict-code discriminator before compositor reduction; no such
rule was promoted. The stable-carrier/path design adds no rewrite, unifier, or
warning family, so the `1290 = 1131 + 159` kernel evidence again carries
forward.

`CGCA-DIM-8` adds only transparent selected observations and reuses the
existing variable-dimensional frame. The dimension-two source/reviewer and
the updated decoder/reviewer are green. No rule, unifier, endpoint equality,
Sigma eta, or warning family is added; the prior focused evidence remains the
applicable kernel boundary.

## 13. Completion Verdict

The plan's two object-level adequacy questions are answered within their stated
boundaries:

1. the Yoneda section/evaluation coherently re-presents every native cube by
   its internal `{L,R,*}` faces and returns it at the identity face; and
2. strict realizations of fixed-bracketing positive right-Gray cubes decode by
   one internal Nat recursion to native cubical levels.

The second construction is variable-dimensional, not a dimension-three macro.
It uses the checked coordinate swap, whole transformation graphs, a selected
strict graph code with stable carrier path, right curry, and a proved
cubical-level shift. Dimensions one through three, the `I tensor_R I`
interchanger direction, four square edges, six cube faces, and another whole
action are checked. The direct equality between the retained graph cell and
the separately reframed readable interchanger is intentionally not claimed.

Checkpoint chain:

```text
69fb447  plan cubical semantic adequacy
0be1813  realize native cubes by Yoneda
d288339  align Gray interchanger with native cubes
6a9d54b  construct Gray transformation graphs
5871e30  define fixed-bracketing Gray cubes
79a8250  decode variable-dimensional Gray cubes
cd23484  validate Gray cube dimensions
0835e22  synchronize mathematical and public documentation
```

The remaining inverse/equivalence, tensor-coherence, and simplicial-native-
nerve work is precisely documented, not silently folded into this result.
Long registered-source and health aggregates were deliberately not completion
gates under the plan's proportional-validation policy; all changed semantic
owners, central diagnostics, new sources, and focused reviewers were checked
directly under the 90-second per-target ceiling.

## 14. Validation And Git Policy

- Keep every Lambdapi command bounded to 90 seconds.
- Use ignored focused probes before promoting semantic rules or stable heads.
- Put every candidate rule at its true owner for final warning and critical-
  pair comparison; follow inferred-slot/LHS SOP and test proof-time rules with
  typed `eq_refl`.
- Warnings are diagnostic, not an automatic veto.
- Carry forward recent green evidence for unchanged sources. Eagerly avoid
  registered/example/health/repository aggregates unless their omission blocks
  classification of changed behavior.
- Preserve staged, unstaged, and unrelated work in every worktree.
- SOP-compliant local checkpoint commits are authorized on this dedicated
  branch after bounded green tranches and synchronized ledger.
- Do not push, merge, publish, tag, create a PR, amend/rebase/reset, delete a
  branch, or remove a worktree without separate explicit authority.

## 15. Persistent-Goal Launch Prompt

> Continue the emdash v3.2 cubical Yoneda and Gray-cube adequacy work in
> `/home/user1/emdash1-gray-cube-adequacy-v1` on branch
> `goal/gray-cube-adequacy-v3.2`, delegating exact mathematics, sequencing,
> acceptance, exclusions, proportional validation, documentation, and Git
> discipline to
> `emdash2/reports/REPORT_EMDASH_V3_2_CUBICAL_YONEDA_AND_GRAY_CUBE_ADEQUACY_PLAN_2026-08-25.md`
> and its authority chain. Begin at `ce9da42`. Implement the cubical Yoneda
> object maps and selected identity-face beta first. Then determine the actual
> lax/oplax direction of the selected Gray walking square before defining a
> fixed-bracketing Gray-cube recursion or geometric decoder. Treat Gray tensor
> powers of the walking arrow as the literature-backed geometric shapes, but
> do not confuse `GrayHom_lax` with a weakening of Cartesian cube objects.
> Public claims may remain object-level; retain whole action internally where
> variable-dimensional recursion needs it. Keep all Lambdapi commands within
> 90 seconds and eagerly avoid broad aggregates. SOP-compliant local checkpoint
> commits are authorized after bounded green tranches and synchronized ledger.
> Do not push, merge, publish, tag, create a PR, rewrite history, delete
> branches, or remove worktrees. Complete only when every scoped row is
> implemented, rejected with durable evidence, or explicitly deferred behind
> a concrete prerequisite and all affected authorities are synchronized.
