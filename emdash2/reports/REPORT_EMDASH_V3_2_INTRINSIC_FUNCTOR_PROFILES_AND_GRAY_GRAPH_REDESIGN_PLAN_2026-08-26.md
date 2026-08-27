# Emdash v3.2 Intrinsic Functor Profiles And Gray-Graph Redesign Plan

Date: 2026-08-27 (America/Toronto)

Plan-ID: `INTRINSIC-FUNCTOR-PROFILES-GRAY-GRAPH-V3.2`

Status: **active corrective continuation**. The 2026-08-26 graph/profile
tranche remains historical green evidence; rows `IFPG-OMEGA-AUDIT-11`
through `IFPG-OMEGA-CLOSE-15` correct its fixed-forward equivalence boundary
without launching the deferred global strict/lax migration.

Supersedes: no completed plan. It is a corrective continuation of
`REPORT_EMDASH_V3_2_CUBICAL_YONEDA_AND_GRAY_CUBE_ADEQUACY_PLAN_2026-08-25.md`.

Depends-On: `emdash3_2_gray_transformation_graph.lp`,
`emdash3_2_gray_transformation_graph_profile.lp`,
`emdash3_2_gray_cube_decoder.lp`, `emdash3_2_readable_pseudofunctors.lp`,
`emdash3_2_cubical_arrow_functor.lp`, `emdash3_2_cubical_square_level.lp`,
`emdash3_2_semicubical_face_action.lp`, and the completed internal-laxity
continuation plan.

Branch: `goal/gray-cube-adequacy-v3.2`

Worktree: `/home/user1/emdash1-gray-cube-adequacy-v1`

Baseline: `c4df575` (`clarify Gray graph object computation`).

Continues:
`REPORT_EMDASH_V3_2_CUBICAL_YONEDA_AND_GRAY_CUBE_ADEQUACY_PLAN_2026-08-25.md`.

Authority chain: active `emdash3_2*.lp` source; `emdash2/AGENTS.md`;
`EMDASH_FOUNDATIONS.md`; the current status/SOP and canonical-syntax reports;
the completed internal-laxity continuation plan; this living plan; linked
decision responses; raw session archive.

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`, response
`0140_2026-08-26T14-14-01Z_01a03e68-460a-7230-bd89-cf70c34a00ea.md`.

Infinity-Codex-Decision-Responses: `infinity-codex:019ffe39-2eb9-7080-88e3-06b77d69b8d1:01a03e68-460a-7230-bd89-cf70c34a00ea`.

Corrective-Decision-Response:
`infinity-codex:019ffe39-2eb9-7080-88e3-06b77d69b8d1:01a03eee-6d6f-7d83-9189-1602dd992e45`.

Side-Task-Ledger: `IFPG-00`, `IFPG-AUDIT-1`, `IFPG-GRAPH-CARRIER-2`,
`IFPG-GRAPH-STRICTNESS-3`, `IFPG-GRAPH-MIGRATE-4`,
`IFPG-PSEUDO-EVIDENCE-5`, `IFPG-CUBICAL-MIGRATE-6`,
`IFPG-HIERARCHY-7`, `IFPG-FACADE-8`, `IFPG-DOC-9`, `IFPG-CLOSE-10`,
`IFPG-OMEGA-AUDIT-11`, `IFPG-OMEGA-EVIDENCE-12`,
`IFPG-OMEGA-CUBICAL-13`, `IFPG-OMEGA-DOC-14`, and
`IFPG-OMEGA-CLOSE-15`.

## 1. Objective

Replace two expedient Gray/cubical profile facades with a computational and
internally derived architecture:

1. determine whether the transformation graph of a selected lax transfor is
   genuinely a computationally strict functor;
2. if it is, decode its strict code directly to the public graph and make only
   its already-extracted unit/compositor cells compute to identity;
3. if it is not, remove the false strict code and generalize the recursive Gray
   decoder to the appropriate coherent-map profile;
4. replace `ReadablePseudoFunctorProfile`'s independent compositor evidence by
   fixed-forward invertibility evidence for the existing internal-action cells;
5. preserve whole and iterated action throughout the cubical lifting and
   variable-dimensional face recursion; and
6. establish a reusable hierarchical profile design suitable for later
   AI-native structure/typeclass resolution.
7. replace the temporary single-inverse `IsoCellEvidence` vocabulary by the
   active fixed-arrow `OmegaEquivAlong` owner, while retaining the existing
   strict-prototype endpoint reframe only as an explicitly bounded
   presentation adapter.

The plan is a redesign of profile evidence, not a new category theory encoded
beside the active functorial type theory.

## 2. Governing Invariant

> Profiles never invent coherence cells. They classify, constrain, invert, or
> make judgmental the cells already extracted from the internal-action tower.

The active owners are:

```text
functord_laxity_transf
fdapp1_int_cell
tapp1_post_laxity_transf
tapp1_pre_laxity_transf
tapp1_post_laxity_cell
tapp1_pre_laxity_cell
fapp1_compositor
the retained next internal action.
```

A profile may provide an inverse or cancellation evidence for one of these
specific cells. It may not provide another unconstrained arrow with the same
endpoints and call that arrow the compositor.

This invariant applies independently of management-layer typeclass inference.
Resolution may locate evidence; it must not manufacture an unrelated
mathematical coherence.

## 3. Current Architecture And Findings

### 3.1 Intrinsic cubical core is retained

The following are transparent and already match the desired architecture:

```text
LaxArrow_cat(C)
  := homdc_total_cat(C,C,hom_int(id_C))

lax_edge(x,y,u)
  := homdc_total_obj(...,x,y,u)

lax_square(a,b,alpha)
  := (a,(b,alpha)).
```

Thus edges and squares are dependent-Sigma observations of `homdc_int`; no
primitive square or independent square axiom exists.

### 3.2 Public transformation graph is retained

The public stable graph has the selected intended computation:

```text
Graph(epsilon) : B -> LaxArrow_cat(C)
Graph(epsilon)[x]  --> epsilon[x]
Graph(epsilon)[g]  --> standardSquare(epsilon,g),
```

where

```text
standardCell(epsilon,g)
  := tapp1_post_laxity_cell(epsilon,g,id_x).
```

Its overlap with historical global strict cuts remains an accepted prototype
diagnostic pending the separate global cut migration.

### 3.3 Strict graph code is unresolved

The current decoder requires an inhabitant of

```text
StrictFunctorData(B,LaxArrow_cat(C)).
```

It obtains one through `strict_gray_transf_graph_data`, then postulates
`strict_gray_transf_graph_carrier_path` and derives object/arrow observations
by `eq_ap`/`eq_apd`.

The path is mathematically typed but opaque. It is not the preferred
computational realization. Existing strict join constructors demonstrate the
better owner pattern:

```text
strict_functor_carrier(strict_join_map_data(F,G))
  --> join_map_func(strict_functor_carrier(F),
                    strict_functor_carrier(G)).
```

### 3.4 Existing pseudo capability is wrong-shaped

`ReadablePseudoFunctorProfile(F)` is evidence over an already-existing
intrinsic functor, not a concrete functor record. Its current post/pre
compositor accessors nevertheless return complete `IsoEvidence` packages whose
forward arrows are not constrained to be the existing extracted laxity cells.

Its substantive consumers are:

- `emdash3_2_cubical_arrow_functor.lp`;
- `emdash3_2_cubical_square_level.lp`; and
- `emdash3_2_semicubical_face_action.lp`.

The graph does not computationally consume this profile.

## 4. Intended Profile Hierarchy

```text
ambient intrinsic Functor F
  |
  +-- generic lax structure
  |     extracted unitor/action/compositor/higher action
  |
  +-- pseudo evidence
  |     inverses for those exact extracted cells
  |
  +-- strict evidence
  |     those exact cells are propositionally identities
  |
  `-- strict computational code
        selected extracted cells reduce judgmentally to identities.
```

The semantic evidence layer and the computational code layer must remain
distinguished. A proof that a cell is an identity does not automatically
install a rewrite; a stable strict code must declare which constructor owns
that computation.

The management/typeclass layer may later resolve instances such as identity,
composition and cubical lifting. The internal term remains explicit and can be
checked independently of resolution.

## 5. First Decision Probe: Whole Strict Carrier

Test at the true decoder owner:

```lambdapi
rule @strict_functor_carrier _ _
      (@strict_gray_transf_graph_data $B $C $SF $SG $epsilon)
  ↪ @gray_transf_graph_func
      $B $C
      (@strict_functor_carrier $B $C $SF)
      (@strict_functor_carrier $B $C $SG)
      $epsilon;
```

This is distinct from the rejected capped `fapp0`/`fapp1_fapp0` projection
folds. Probe it in an owner-position full copy with:

- whole carrier conversion;
- object and capped arrow computation;
- subject reduction;
- identity and composition overlaps;
- selected strict compositor observation;
- the recursive decoder step;
- strict LHS audit; and
- exact warning comparison.

If the whole rule fails subject reduction, do not replace it by another opaque
path. Reassess the `StrictFunctorData` target or the graph endpoints.

## 6. Second Decision Probe: Is The Graph Actually Strict?

The whole carrier rule erases the syntactic
`strict_functor_carrier(strict_gray_transf_graph_data(...))` discriminator.
Before restoring any computation, inspect the existing graph unit and binary
compositor cells.

The binary candidate is not a new symbol. It is exactly:

```text
fapp1_compositor(Graph(epsilon),g,f)
  := tapp1_post_laxity_cell(id_Graph,g,f)
  ≡ fdapp1_int_cell(...Graph(epsilon)...).
```

There are two outcomes.

### Outcome A: genuinely strict graph

If both the unit and binary compositor are semantically the identity for the
selected transformation profile, install narrowly scoped computations on
their actual internal-action owners. The binary rule will recognize the
`gray_transf_graph_func` head with strict-coded endpoint functors. It must not
declare a second graph compositor.

Then remove:

```text
strict_gray_transf_graph_carrier_path
strict_gray_transf_graph_obj_path
strict_gray_transf_graph_arrow_pathover.
```

### Outcome B: coherent but non-strict graph

If either extracted cell remains nonidentity, the graph must not inhabit
`StrictFunctorData`. Remove `strict_gray_transf_graph_data` and generalize the
Gray-cube recursion to a profile that accepts the actual coherent graph while
retaining its next action.

Do not let the historical global strict cuts decide this semantic question.

## 7. Fixed-Forward Pseudo Evidence

The replacement must fix the forward cell as an input. The repository already
owns exactly this native boundary:

```text
OmegaEquivAlong(C,x,y,c).
```

It decodes to separate selected left and right inverse arrows with
equality-valued cancellation in the two endomorphism hom-categories. This is
the active recursive omega-equivalence vocabulary. A second single-inverse
`IsoCellEvidence` duplicates that vocabulary and is therefore retired by the
corrective continuation.

The pseudo profile should constrain the already-extracted cells:

```text
PseudoFunctorEvidence(F)
  := Pi X Y Z g f,
       OmegaEquivAlong(
         Hom_cat(B,F[X],F[Z]),
         source(F,g,f),
         target(F,g,f),
         fapp1_compositor(F,g,f)).
```

The public field is indexed by the already-fixed forward cell; it must not use
`OmegaEquiv`, which would package and reselect a forward arrow. If an endpoint
path is desired, package the fixed cell and its `OmegaEquivAlong` evidence into
`OmegaEquiv` and use the active univalence bridge as a derived observation.

The current readable post cell remains a prototype presentation of that
intrinsic cell. Its source reframe deliberately uses the historical global
strict-functoriality path to recover the surface spelling
`F[g] o F[f]` after that temporary cut has selected `F[g o f]`. This does not
construct the cell: `fapp1_compositor` is already independently projected from
the whole internal action and retains its next action. The reframe is therefore
accepted only as a documented adapter under the existing prototype policy. It
does **not** establish noncollapsed lax endpoint semantics, and the eventual
profile-local strict-cut migration must replace it by direct left/right
internal-action observations.

The pre/right presentation must either constrain
`tapp1_pre_laxity_cell(id_F,...)` directly or be derived from the post/left
owner through a checked whole comparison. It must not be an independently
supplied forward cell. For the current cubical consumer, select one reverse
arrow from `OmegaEquivAlong` and follow it by the existing post/pre
presentation reframe. The reverse arrow is the final pseudofunctor adjustment
in `phi ; F_1[alpha] ; phi^-1`; it is not another compositor.

An arbitrary non-normal unit profile is deferred until the corresponding
unitor has itself been extracted from internal action. Do not retain a
primitive unitor merely because the old capability exposed one.

Higher coherence comes from the next internal action. Do not add primitive
pentagon or triangle fields.

## 8. Cubical Consumer Migration

The current mapped filler is schematically:

```text
old-profile-post.to ; F_1[alpha] ; old-profile-pre.from.
```

The corrected implementation must be:

```text
existing post/left extracted cell
  ; F_1[alpha]
  ; inverse evidence for the existing pre/right extracted cell.
```

Migrate in this order:

1. `cubical_arrow_map_cell` and `CubicalArrow_func`;
2. source, target and lifted profile instances;
3. four face profiles in `cubical_square_level`;
4. `CubeFaceActionResult` and `{L,R,*}` recursion; and
5. variable-dimensional face-action reviewers and negatives.

Every result must remain a whole functor with generic next action. Do not turn
the recursion into capped record data.

Opaque identity/composition/source/target/lifted profile constants should be
replaced by transparent derived evidence wherever the active internal action
supports construction. A remaining supplied capability must be named and
documented honestly.

## 9. Structure And Typeclass Architecture

This work establishes a reusable pattern rather than a classical concrete
functor record:

```text
FunctorProfile(F)
PseudoProfile(F) extends FunctorProfile(F)
StrictProfile(F) extends FunctorProfile(F).
```

The carrier and all iterated action belong to intrinsic `Functor`. Profiles
only refine those actions. Later TypeScript management/typeclass resolution
may search for instances, share ancestors, and cache derived evidence, while
the Lambdapi/Core term records the explicit mathematical result.

Do not introduce more unrelated primitive field families before this
hierarchical boundary is tested by the cubical consumers.

## 10. Cubical Readability Facade

The aliases

```text
CubicalArrow_cat = LaxArrow_cat
cubical_edge     = lax_edge
cubical_square   = lax_square
```

own no competing semantics. They may temporarily remain as domain-readable
notation. Do not describe them as compatibility obligations.

After the profile redesign is green, audit whether one vocabulary is enough.
Deletion is a broad mechanical migration across cubical levels, frames and
face actions; it must be a separate bounded row and must not obscure the
semantic profile diff.

## 11. Explicit Nonclaims

This plan does not initially claim:

- completion of the global strict-cut migration;
- a general concrete category/functor/transfor declaration compiler;
- automatic Lambdapi typeclass resolution;
- a complete lax/pseudo/strict omega-map hierarchy in one tranche;
- new primitive coherence cells;
- a full Crans--Gray monoidal structure;
- inverse Gray-cube decoding;
- degeneracies, connections or Kan structure; or
- deletion of every historical readability alias.

## 12. Execution Ledger

| Row | State | Deliverable and acceptance boundary |
| --- | --- | --- |
| `IFPG-00` | complete | Reused the clean dedicated worktree `/home/user1/emdash1-gray-cube-adequacy-v1` on `goal/gray-cube-adequacy-v3.2` at baseline `c4df575`; no branch, worktree, push, merge or publication mutation was needed. |
| `IFPG-AUDIT-1` | complete | Re-audited `LaxArrow_cat`, `lax_edge`, `lax_square`, the public/protected graph, `StrictFunctorData`, strict join precedents, the Gray decoder, `ReadablePseudoFunctorProfile`, `cubical_arrow_map_cell`, square-level profiles and recursive face action. The intrinsic cubical core is retained; the opaque strict graph path and independent-forward pseudo evidence are the exact redesign targets. |
| `IFPG-GRAPH-CARRIER-2` | complete, checkpoint `2b80b66` | The whole `strict_functor_carrier(strict_gray_transf_graph_data(...))` rule checks at the true owner and computes to the public graph, unlike the rejected late projection folds. Direct whole, object and arrow conversions are green, as is the recursive decoder consumer; no carrier path is needed. The profile source remains exactly at its graph dependency warning inventory `1311 = 1152 + 159`, and its strict LHS audit has zero unreviewed candidates. |
| `IFPG-GRAPH-STRICTNESS-3` | complete selected boundary, checkpoint `a07f8d0` | A minimal graph-head rule on the existing `fdapp1_int_cell` makes `fapp1_compositor(Graph(epsilon),g,f)` compute to identity for strict-coded endpoint diagrams. A second narrow rule makes the already-extracted identity filler `tapp1_post_laxity_cell(epsilon,id,id)` compute to identity; neither rule introduces a cell. The resulting readable `lax_square(id,id,id)` still does not judgmentally equal the canonical nested-Sigma identity of `LaxArrow_cat`, matching the existing cubical-library boundary. A generic `lax_square_id`/Sigma-identity reconstruction path—not a graph-specific unit axiom—is the exact prerequisite for a whole-arrow equality and is deferred until a concrete non-graph consumer requests it. The profile remains warning-neutral at `1311 = 1152 + 159`. |
| `IFPG-GRAPH-MIGRATE-4` | complete selected boundary, checkpoint `a07f8d0` | Retired `strict_gray_transf_graph_carrier_path`, `strict_gray_transf_graph_obj_path`, and `strict_gray_transf_graph_arrow_pathover`; profile and decoder reviewers use direct whole/object/arrow computation. The strict graph code is retained because its intrinsic identity filler and binary compositor now compute at their actual owners. The remaining readable-square/canonical-identity comparison is generic derived-total presentation, not evidence that the decoder needs a parallel coherent-map carrier. |
| `IFPG-PSEUDO-EVIDENCE-5` | complete, checkpoint `396ecc2` | Added transparent fixed-forward `IsoCellEvidence(cell)` containing only inverse/cancellation data. Four explicit endpoint-path rungs reframe the existing `fapp1_compositor` to one readable post cell; the profile constrains exactly that cell. Removed the independent primitive unitor and post/pre `IsoEvidence` arrows. The pre/right inverse is derived from the same inverse plus the existing post/pre endpoint path; no second compositor or inverse field remains. Source and strict LHS audit are green with exact dependency inventory `1308 = 1149 + 159`. |
| `IFPG-CUBICAL-MIGRATE-6` | complete semantic migration, checkpoint `396ecc2` | `cubical_arrow_map_cell` now composes the existing readable compositor, generic `F_1[alpha]`, and its derived pre-readable inverse. Cubical lift, square-level and recursive face-action reviewers are green; source/target and next-hom behavior remain unchanged. The cubical source remains warning-neutral at `1308 = 1149 + 159`, and its strict LHS audit has zero candidates. The remaining opaque identity/composition/source/target/lifted profile inhabitants are owned by the hierarchy/instance row rather than this cell migration. |
| `IFPG-HIERARCHY-7` | complete selected boundary, checkpoint `89ea513` | `readable_pseudo_profile_intro` constructs a profile from one explicit dependent family of fixed-forward evidence and its projection computes. This realizes the intrinsic-map/pseudo-evidence layer without rebuilding object or arrow maps. Identity/composition and cubical source/target/lifted instances are now documented as supplied capabilities; deriving them is precisely gated by an extracted unit interface and next-action composite-profile coherence rather than hidden behind independent cells. Typeclass search remains a future management-layer consumer. |
| `IFPG-FACADE-8` | complete decision, recorded at `89ea513` | Retain `CubicalArrow_cat`, `cubical_edge`, and `cubical_square` as intentional domain-readable transparent aliases for now, not compatibility obligations. They own no rules or competing semantics; deleting them would be broad low-value mechanical churn and is not required by the profile redesign. |
| `IFPG-DOC-9` | complete, closeout checkpoint `02675f4` | Synchronized Foundations, current SOP/status, canonical syntax, AGENTS, `emdash2/README`, report map, superseded cubical-plan descriptions, focused reviewers, and the generated catalog. The `cubical_*` vocabulary is explicitly readability rather than compatibility, fixed-forward evidence and supplied-instance boundaries are stated consistently, and retired graph-path/independent-compositor names have no active source consumer. |
| `IFPG-CLOSE-10` | complete, closeout checkpoint `02675f4` | Every scoped row is implemented or precisely deferred behind a named generic prerequisite. Graph profile/decoder/dimension-two, fixed-forward profile, cubical lift, square-level and recursive face-action sources/reviewers are green under the 90-second ceiling. Exact inventories are `1311 = 1152 + 159` for the graph profile and `1308 = 1149 + 159` for readable/cubical profile consumers; strict LHS audits report zero candidates. Catalog, report headers, active references, TOC and diff hygiene are green. Long registered-source, examples, health and repository aggregates remain intentionally omitted because unchanged boundaries and focused evidence suffice. |
| `IFPG-OMEGA-AUDIT-11` | complete design correction | Re-audited the fixed-forward field and endpoint ladder. `IsoCellEvidence` is a duplicate single-inverse vocabulary; `OmegaEquivAlong` is the active native fixed-arrow owner. A focused no-adapter diagnostic confirms that the historical whole strict cut normalizes the formal source to `F[hom_postcomp(id,g,f)]`, so the existing `fapp1_comp_path` rung is retained only as an explicit prototype presentation adapter. It does not construct the independently extracted cell and does not claim noncollapsed lax endpoints. The large global strict/lax migration remains out of scope. |
| `IFPG-OMEGA-EVIDENCE-12` | complete, checkpoint pending | Removed the duplicate transparent `IsoCellEvidence` Sigma and all three projections. `readable_pseudo_profile_intro` and its computing field projection now use `OmegaEquivAlong` over the exact existing `readable_pseudo_post_cell`, adding no cell, rule, unifier, or facade. The explicit-constructor reviewer computes to the supplied native evidence family. |
| `IFPG-OMEGA-CUBICAL-13` | complete, checkpoint pending | `readable_pseudo_pre_inverse` now selects `omega_equiv_along_left_inv` and follows it by the existing post/pre presentation reframe. The intrinsic square map remains exactly `phi(b,u) ; F_1[alpha] ; phi(v,a)^-1`; edge/square computation, next action, square level, and variable-dimensional `{L,R,*}` recursion are green. The five identity/composition/source/target/lifted profile constants remain explicitly supplied. |
| `IFPG-OMEGA-DOC-14` | complete, checkpoint pending | Synchronized the active plan, AGENTS, Foundations, status/SOP, canonical syntax, README/report map, predecessor cubical/Gray ledgers, graph comments, and focused reviewer. Every active claim now names fixed-forward `OmegaEquivAlong`; the endpoint ladder is consistently documented as a temporary strict-prototype adapter validating cell provenance/iteration rather than noncollapsed lax endpoints. Historical ledger mentions of the retired name remain only as dated evidence. |
| `IFPG-OMEGA-CLOSE-15` | complete pending exact checkpoint | Focused profile/cubical sources and reviewers, square level and recursive face action are green under the 90-second ceiling. Warning inventories remain exactly `1308 = 1149 critical + 159 replaceable`; strict LHS audits report zero candidates. Catalog, source TOC and diff hygiene are green. No active source/reviewer retains `IsoCellEvidence`; only its explicit historical/retirement mentions remain. Long registered-source, examples, health and repository aggregates were intentionally omitted because no changed boundary requires them. |

### 12.1 Historical 2026-08-26 Completion Verdict

The redesign satisfies the governing invariant. The strict graph code decodes
computationally to the public graph; its existing identity filler and binary
compositor compute at their internal-action owners; and no opaque carrier path
or parallel coherence cell remains. Pseudo evidence fixes the forward readable
cell derived from `fapp1_compositor`, supplies only inverse/cancellation data,
and derives its pre/right inverse by endpoint reframing. Cubical lifting and
variable-dimensional face action retain their whole higher action.

The remaining supplied profile instances are explicit assumptions rather than
hidden independent cells. Their construction is gated by an extracted unitor
and next-action composite-profile coherence. The readable
`lax_square(id,id,id)` versus canonical nested-Sigma identity comparison is a
generic derived-total path and is not made a graph-specific axiom. These are
precise future prerequisites, not missing requirements of this bounded plan.

The corrective continuation does not invalidate that graph/cubical execution
evidence. It narrows the semantic claim: the endpoint reframe is a temporary
strict-prototype adapter, and the native pseudo field is
`OmegaEquivAlong(readable_pseudo_post_cell)`. Rows 11--15 supersede the
single-inverse vocabulary and the earlier unqualified phrase "semantic
migration complete."

Checkpoint chain:

```text
2b80b66  decode strict Gray graphs computationally
396ecc2  constrain pseudo profiles to intrinsic compositors
89ea513  add explicit intrinsic pseudo profile constructor
a07f8d0  constrain Gray graph unit at intrinsic cell
02675f4  close intrinsic functor profile redesign
```

## 13. Validation Policy

- Every Lambdapi invocation is bounded to 90 seconds.
- Use owner-position full-copy probes before promoting rules.
- Validate proof-time comparisons with typed `eq_refl`; use `assertnot` for
  intended noncollapse.
- Follow inferred-slot/LHS SOP for every rewrite and unification rule.
- Treat warnings as diagnostics, including known overlaps with temporary global
  strict cuts; do not ignore subject-reduction failures.
- Run focused sources/reviewers, affected central diagnostics, exact warning
  comparisons, strict LHS audit, catalog/TOC and document hygiene.
- Eagerly avoid long registered-source, examples, health and repository
  aggregates unless their omission blocks classification.
- Carry forward recent green evidence for unchanged boundaries.

## 14. Git Policy

The user authorizes SOP-compliant local checkpoint commits on this dedicated
branch after each bounded green tranche and synchronized ledger. Preserve
unrelated work and inspect the exact staged diff before committing.

Do not push, merge, publish, tag, create a PR, rewrite history, delete branches,
or remove worktrees without separate explicit authorization.

## 15. Persistent-Goal Launch Prompt

> Continue the emdash v3.2 intrinsic functor-profile corrective continuation in
> `/home/user1/emdash1-gray-cube-adequacy-v1` on branch
> `goal/gray-cube-adequacy-v3.2`, delegating exact design, sequencing,
> acceptance, exclusions, proportional validation, documentation and Git
> discipline to
> `emdash2/reports/REPORT_EMDASH_V3_2_INTRINSIC_FUNCTOR_PROFILES_AND_GRAY_GRAPH_REDESIGN_PLAN_2026-08-26.md`
> and its authority chain. Resume from the validated 2026-08-26 closeout at
> `7454a65`. Profiles must never invent
> coherence cells: they may only classify, constrain, invert or make
> judgmental the cells already extracted from the internal-action tower.
> Execute rows `IFPG-OMEGA-EVIDENCE-12` through `IFPG-OMEGA-CLOSE-15`: replace
> the duplicate `IsoCellEvidence` field by fixed-forward `OmegaEquivAlong`,
> derive the reverse cubical adjustment from its selected inverse, preserve
> whole higher action, and synchronize every affected authority. Retain the
> current endpoint path ladder only as a documented adapter for the temporary
> global strict-functoriality prototype; do not claim noncollapsed lax endpoint
> semantics and do not launch the large global strict/lax migration in this
> tranche. Keep the five closure profiles explicitly supplied. Keep every
> Lambdapi command within 90 seconds and avoid long aggregates unless omission blocks
> classification. Local checkpoint commits are authorized after bounded green
> tranches and ledger synchronization. Do not push, merge, publish, tag, create
> a PR, rewrite history, delete branches or remove worktrees. Complete only
> when every scoped row is implemented, rejected with durable evidence or
> precisely deferred and all affected authorities are synchronized.
