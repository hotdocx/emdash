# Emdash v3.2 Cubical Yoneda And Gray-Cube Adequacy Plan

Date: 2026-08-25 (America/Toronto)

Plan-ID: `CUBICAL-YONEDA-GRAY-CUBE-ADEQUACY-V3.2`

Status: **active implementation plan**.

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

## 7. Walking-Arrow Bridge

The central geometric comparison begins at dimension one:

```text
gray_walking_to_lax_obj
  : Obj(GrayHom_mu(WalkingArrow,C))
    -> Obj(LaxArrow_cat(C)).
```

For a strict code `S`, decode its carrier `F : WalkingArrow -> C` and form the
native edge

```text
(F[src],F[tgt],F[generator]).
```

For variable-dimensional recursion, an object-only function may be
insufficient internally. A curried successor cube is a transformation between
two lower-dimensional realizations; mapping it to a native square requires
the lower decoder's arrow action. The scalable target is therefore likely a
whole functor

```text
gray_walking_to_lax_func(C)
  : GrayHom_mu(WalkingArrow,C) -> LaxArrow_cat(C),
```

while this plan initially advertises only its object projection. The functor's
arrow action must be the transformation's two endpoint components plus its
selected lax/oplax naturality cell, extracted through existing `tapp*` owners.

The inverse edge-to-strict-code constructor is not required for the first
observation. If later needed, it requires a curated strict walking-arrow code
whose carrier is the existing join extension; it must not postulate an opaque
functor unrelated to `Join_cat(1,1)`.

## 8. Fixed-Bracketing Gray Cubes

After the orientation verdict, define one chosen recursion:

```text
GrayCube_mu(1)       = WalkingArrow_cat
GrayCube_mu(n+1)     = GrayTensor_mu(WalkingArrow_cat,GrayCube_mu(n)).
```

This prepends the new coordinate and matches the selected right-closure
currying order

```text
GrayHom_mu(WalkingArrow tensor GrayCube_mu(n),C)
  ~= GrayHom_mu(WalkingArrow,GrayHom_mu(GrayCube_mu(n),C)).
```

Fixed bracketing is sufficient for an object-level first theorem. The plan
does not claim tensor parameter functoriality, a unit comparison at dimension
zero, associativity between alternate bracketings, coordinate permutations,
or full Crans--Gray monoidality.

## 9. Gray-Cube Decoder

The desired scalable owner is

```text
gray_cube_decode_func(C,n)
  : GrayHom_mu(GrayCube_mu(n),C)
    -> CubicalLevel_cat(C,n).
```

The public first result is its object action:

```text
H |-> gray_cube_observation(H).
```

The successor should use selected Gray curry, the walking-arrow bridge, and
the recursively retained decoder action. If current `GrayTensor_R` lacks a
parameter action needed to map the inner target of curry, record the exact
consumer-gated prerequisite rather than postulating a dimension-specific
cube decoder.

Acceptance proceeds through dimensions one, two, and three before claiming
variable `n`. At dimension two, the decoded top filler must be the actual
mapped Gray interchanger in the same direction as the native square. At
dimension three, another hom action must remain; a hand-written six-face
record is not an acceptable replacement.

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
| `CGCA-GRAY-ORIENT-4` | in progress | Direct typing of `gray_interchanger` as either `b o u ==> v o a` or `v o a ==> b o u` fails, and typed `eq_refl` cannot identify either stable endpoint with the corresponding readable composite. This is not an orientation verdict: the interchanger retains `functord_transport_lhs/rhs` endpoints. Its `tapp1_post_laxity_transf` provenance reads schematically `G[g] o epsilon[-] ==> epsilon[g o -]`, predicting visible `v o a ==> b o u`. Derive the two endpoint readings through existing whole internal-action paths before selecting factor swap/opposite/profile naming; add no endpoint rewrite. |
| `CGCA-WALKING-BRIDGE-5` | pending | Construct the strict-walking-map to native-edge object operation and, if required for recursion, its whole functorial arrow action from transformation components and internal naturality. Do not require the inverse code constructor initially. |
| `CGCA-GRAYCUBE-6` | pending | Define a fixed-bracketing positive-dimensional Gray-cube recursion after the orientation verdict; validate dimensions one through three without claiming unit/associativity/symmetry. |
| `CGCA-GRAY-DECODE-7` | pending | Construct the Gray-cube-to-native decoder using selected curry and the walking bridge. Publicize object action first; promote a whole functor only where recursion genuinely requires it. |
| `CGCA-DIM-8` | pending | Validate dimensions one, two, and three: endpoints/generator; four edges and directed interchanger; six faces and retained next action. State the exact boundary to arbitrary variable `n`. |
| `CGCA-SIMPLICIAL-DEFER-9` | pending | Audit and document the distinct later simplicial Yoneda prerequisite without constructing an unsettled native semisimplicial level facade. |
| `CGCA-DOC-10` | pending | Synchronize the living plan, Foundations, status/SOP, canonical syntax, READMEs, AGENTS/source registries, examples, catalog, and proportional health evidence. |
| `CGCA-CLOSE-11` | pending | Audit every scoped row, checkpoint implemented/deferred evidence, and hand off exact commits/prerequisites. No push, merge, publication, tag, PR, history rewrite, branch deletion, or worktree removal without separate authority. |

## 13. Validation And Git Policy

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

## 14. Persistent-Goal Launch Prompt

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
