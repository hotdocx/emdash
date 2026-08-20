# Emdash v3.2 Ordinal Dependent Simplex Dimension-Three Plan

Date: 2026-08-19 (America/Toronto)

Plan-ID: `ORDINAL-DEPENDENT-SIMPLEX-DIMENSION-THREE-V3.2`

Status: **active implementation plan**. The completed join-cross plan
constructs the canonical dimension-two ordinal dependent simplex and retains
the next whole hom action. This child plan uses that boundary to construct the
corresponding ordinal tetrahedron, without reopening dimension two or silently
expanding to dimension four.

Branch: `goal/ordinal-dependent-simplex3-v3.2`

Worktree: `/home/user1/emdash1-ordinal-simplex3-v1`

Baseline: completed join-cross dependent-simplex checkpoint
`e157b37c2cf359a114fff65786e62e2ae6d18fe0`.

Parent-Plan:
`REPORT_EMDASH_V3_2_JOIN_CROSS_DEPENDENT_SIMPLEX_PLAN_2026-08-19.md`

Depends-On:

- `emdash3_2_dependent_simplex_ordinal_filler.lp` for the constructed native
  ordinal triangle, its arbitrary-target image, its unconditional observation,
  and `ordinal_dependent_simplex2_next_func`;
- `emdash3_2_dependent_simplex_native_dimensions.lp` for
  `DependentSimplex3_cat`, `dependent_simplex3_visible`, its readable final
  cell, and `dependent_simplex3_map`;
- `emdash3_2_tetrahedron_faces.lp` for the four selected ordinal triangle
  cofaces 012, 013, 023, and 123;
- `emdash3_2_join_cross_compatibility.lp` and
  `emdash3_2_join_generator_compatibility.lp` for whole join-cross comparison,
  generator observation, and retained higher action; and
- active Foundations, canonical notation, current SOP, report index, and the
  persistent-goal Git workflow.

Side-Task-Ledger: `ODS3-00`, `ODS3-BASE-1`, `ODS3-OWNER-2`,
`ODS3-FACES-3`, `ODS3-SOURCE-4`, `ODS3-MAP-5`, `ODS3-OBSERVE-6`,
`ODS3-PROFILE-7`, `ODS3-NEXT-8`, `ODS3-DOC-9`, and `ODS3-CLOSE-10`.

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`; launch recommendation response
`0073_2026-08-19T18-35-16Z_5f1c11a1-d49b-4824-ada0-ece9484feb94.md`.
That response is recovery evidence only. Active code/SOP and this evolving
ledger are authoritative.

## 1. Objective

Construct the intrinsic dimension-three dependent-simplex observation of every
ordinal tetrahedron functor

```text
H : Functor(DirectedSimplex_cat(3), C)
```

from the existing join, face, `homd_`/Sigma, and whole internal-action owners.
The intended public boundary is schematically

```text
ordinal_dependent_simplex3_observe_canonical(H)
  : DependentSimplexObservation(C,3).
```

Its underlying object must be a genuine inhabitant of the existing flagged
classifier

```text
DependentSimplex3_cat(C,x0,e01,t012),
```

whose lower data are the four ordinal triangle restrictions and whose top
dependent cell comes from the retained recursive action. A primitive
tetrahedron filler, an unrelated coherence record, or an ordinary
associativity proof does not satisfy the goal.

## 2. Exact Dimension-Three Boundary

For `H : Functor(Delta[3],C)`, let

```text
H012, H013, H023, H123 : Functor(Delta[2],C)
```

be composition with the four already-selected cofaces. Each restriction has
the constructed dimension-two observation. Dimension-three adequacy must show
that these observations form one native tetrahedron:

```text
flag       = triangle 012
target     = triangle 013
base face  = triangle 023
far face   = triangle 123
top cell   = dependent cell over those four faces.
```

The native classifier represents this recursively rather than as a flat
four-face record. Face 123 and the readable top endpoint must therefore be
obtained through the existing `dependent_simplex3_readable_cell` projection
and typed endpoint transport, not by duplicating the recursive semantics.

The first owner audit must distinguish three questions:

1. which source object of `DependentSimplex3_cat(Delta[3],...)` is canonical;
2. which whole hom action supplies its arrow from face 012 to face 013; and
3. which existing comparison identifies the projected faces with 023 and 123.

## 3. Meaning Of The Retained Dimension-Two Action

`ordinal_dependent_simplex2_next_func(H)` is positive evidence that the mapped
native triangle remains iterable. Its current public type fixes both endpoints
to the canonical source triangle, so it must not be assumed without checking
to be the distinct-face tetrahedral action.

If dimension three needs two different source triangles, expose a transparent
between-objects projection of the already existing whole owner:

```text
fapp1_func(dependent_simplex2_map(...), t0, t1).
```

Such a projection is an API refinement, not a second action semantics. Add no
new primitive head merely to avoid writing the existing generic action. If the
required source higher cell is instead the next projection of whole
join-cross compatibility, recover it there and record the exact projection
ladder.

The required ownership ladder is:

```text
whole join/internal action
  -> source tetrahedral hom
  -> native source DependentSimplex3 object
  -> dependent_simplex3_map(H)
  -> arbitrary-target ordinal observation
  -> one retained next hom action.
```

## 4. Canonical Source Tetrahedron

Use the recursive presentation

```text
Delta[3] = Join_cat(Delta[2], Terminal_cat)
```

and the existing four coface functors. First construct the canonical native
tetrahedron for the identity functor on `Delta[3]`. Its three immediately
visible lower triangles and residual dependent cell must arise from:

- the already-constructed canonical dimension-two source triangle;
- source join-cross action at the new vertex;
- the next `homd_`/Sigma action retained by that construction; and
- only the endpoint paths projected from whole face/join comparisons.

Do not postulate a source top filler. If direct construction fails, the owner
probe must name the smallest missing whole higher join-cross comparison and
show why the current retained action cannot project it. A face-specific
conversion rule, broad join eta, or opaque tetrahedron constant is not an
acceptable repair.

## 5. Mapping Under An Arbitrary Ordinal Tetrahedron

Once the source native object exists, map it under arbitrary `H` through the
existing

```text
dependent_simplex3_map(Delta[3],C,H,...).
```

The resulting object, rather than a separately assembled flat record, is the
canonical target tetrahedron. Public readable projections may expose its
vertices, six edges, four triangle faces, and top dependent cell, but they
must remain observations of this one mapped native object.

Acceptance requires that the four face observations agree with

```text
ordinal_dependent_simplex2_observe_canonical(H012)
ordinal_dependent_simplex2_observe_canonical(H013)
ordinal_dependent_simplex2_observe_canonical(H023)
ordinal_dependent_simplex2_observe_canonical(H123)
```

at the strongest form justified by the current owners. Definitional
conversion is not required where the existing face/join comparisons are
propositional, but each comparison must be projected from a whole owner and
must retain its next action when the source does.

## 6. Profiles And Negative Evidence

The same construction must support three readings:

```text
general C       directed/lax tetrahedron;
strict profile  the same object with only selected profile-local collapses;
Path_cat(A)     an equality-valued, reversibly oriented top cell.
```

Historical global proof-time strict endpoint comparisons may remain installed
as the documented prototype boundary. They must not be used as evidence that
the extracted top cell is an identity. The no-associativity/path-transport
technique from the dependent-simplex foundations remains the reference when
endpoint bracketing matters.

Focused reviewers must include:

1. all four face restrictions and their shared lower faces;
2. the native top dependent component;
3. one wrong face or wrong top endpoint rejected;
4. direct noncollapse of the generic top cell where meaningful;
5. the Path inverse supplied by `eq_sym`; and
6. one further whole hom action.

## 7. Dimension-Four Handoff

Dimension four is not implemented by this plan. Closeout must expose the
literal next whole action of the completed dimension-three map and record
whether it is sufficient input for a later dimension-four child plan. Do not
add the dimension-four ordinal comparison, a uniform `RecursiveSimplex(C,n)`,
or a mapping-category equivalence here.

## 8. Escalation Ladder

Use the smallest architecture that constructs the objective:

1. transparent composition and projection from active owners;
2. one named whole projection facade if the current public endpoint is too
   specialized;
3. one propositional whole comparison at the join/internal-action semantic
   owner if the two existing whole constructions are not definitionally equal;
4. only after a variance audit, one missing covariant/contravariant displayed
   owner required by a concrete face; and
5. only if the ordinary source provably cannot express the oriented boundary,
   a separately planned richer source such as an oriental.

Every escalation needs a positive consumer, a negative/noncollapse consumer,
and retained higher action. Do not introduce a capped square or tetrahedron
axiom.

## 9. Explicit Nonclaims

This plan does not claim or construct:

- dimension-four ordinal adequacy or a general all-`n` theorem;
- a whole semisimplicial nerve or mapping-category equivalence;
- degeneracies, horns, Kan, Segal, Rezk, complicial, or oriental structure;
- a broad join eta or general join mapping equivalence;
- a manual associator, pentagon, or flat coherence record;
- a migration of historical global strict endpoint rules;
- a duplicate `FaceCode`, dependent-simplex code, `homd_`, or Sigma theory;
- TypeScript/parser work; or
- integration, publication, deployment, or cleanup.

## 10. Module Strategy

The expected first module is:

```text
emdash3_2_dependent_simplex_ordinal_dimension3.lp
  canonical source tetrahedron, arbitrary-H native image, face observations,
  unconditional dimension-three observation, and retained next action.
```

If the owner audit proves that one generic higher join-cross comparison is
missing, place it in a preceding narrowly named module and keep the ordinal
consumer separate. Edit `emdash3_2.lp` only if an owner-position full-file
probe proves that a generic computation belongs beside the primitive owner.

Add one focused reviewer for each promoted source. Update registries and
authority documents only after the source boundary is stable.

## 11. Implementation Order

```text
baseline and exact owner inventory
  -> four-face restriction/endpoint audit
  -> canonical source tetrahedral hom
  -> native source DependentSimplex3 object
  -> arbitrary-H whole map
  -> unconditional observation and readable faces
  -> strict/Path/noncollapse review
  -> retained dimension-four handoff
  -> authority synchronization and closeout.
```

At most one ledger row may be `in progress`.

## 12. Validation Policy

Follow `emdash2/AGENTS.md` exactly:

- keep every Lambdapi target within 90 seconds;
- use owner-position full-file probes for any rule or unifier candidate;
- minimize inferred LHS slots and annotate every measured guard;
- compare quiet and warning-enabled runs for promoted source/reviewer files;
- exercise every proposed unifier with typed `eq_refl`;
- test both projection orders for a commuting bridge;
- pair positive computation with wrong-endpoint/noncollapse evidence;
- run affected source/reviewer checks, strict LHS audit, catalog, and
  source-only health before implementation checkpoints; and
- eagerly avoid long aggregate checks unless omitting one would block
  trustworthy promotion or final closeout.

Warnings are diagnostic evidence, not an automatic veto. No promoted code may
use `--no-sr-check`.

## 13. Git And Authorization Boundary

The user's instruction to proceed with the recommended child goal authorizes:

- this dedicated local branch/worktree;
- implementation within this plan's scope; and
- SOP-compliant local checkpoint commits after bounded green tranches.

No push, merge, PR, tag, release, npm/Zenodo publication, deployment, history
rewrite, branch/worktree deletion, or unrelated mutation is authorized.

## 14. Execution Ledger

| Row | Status | Deliverable and acceptance boundary |
| --- | --- | --- |
| `ODS3-00` | complete | Created the dedicated child branch/worktree from clean checkpoint `e157b37`; recorded the exact objective, nonclaims, validation policy, and Git boundary in this linked living plan; and indexed it for a clean launch checkpoint. |
| `ODS3-BASE-1` | complete | Bootstrapped the worktree. Focused quiet checks of the ordinal filler, native dimension-three classifier, tetrahedron faces, and their three reviewers are green. Unchanged aggregate evidence is carried forward; no long aggregate was run. |
| `ODS3-OWNER-2` | complete | Audited the fixed next-action facade against its distinct-endpoint owner, constructed the source join-cross section and all three new-vertex triangle actions uniformly, applied the recursive section action to the lifted 012 filler, and recovered the missing section-composition route from transparent section totalization plus the generic extracted `fapp1_compositor`. The resulting whole tetrahedral cell and both recursive Sigma projections typecheck without a primitive, rewrite, or unifier. Naive direct packaging is rejected because it confuses the join presentation, whose outer base cell is face 012, with the flagged `DependentSimplex3_cat` presentation, whose outer base cell is face 123. |
| `ODS3-FACES-3` | in progress | Define the four arbitrary-`H` triangle restrictions and establish their six shared edge/vertex comparisons through existing whole face/join owners, without face-specific rewrite rules. The source audit constructs faces 013, 023, and 123 from one generic cross-action projection and retains face 012 as the existing canonical filler. The generic terminal-right module exposes a computational directed source component and whole displayed normalizer with retained laxity action. Separate green compositor and action projections establish the formal-alpha architecture: the forward section compositor supplies the sequential-013/123 factor and the 012 action supplies the following factor; their already-green whole composite uses all four faces without an inverse compositor. The compositor has been conjugated to readable endpoints, whiskered by face 013, and related to the native `homd_` source through the generic higher precomposition/product-composition bridge. A promoted generic `section_postcomp_sec` owner makes `Pi_func` postcomposition computational: its point components are the normalized successor faces and its base-arrow action is the existing `fdapp1_int_hom_fapp0`, including displayed laxity. The terminal-normalization module now also retains `p |-> g o F[p]` as a whole map-then-postcompose functor and exposes a generic expected-to-constructor-visible displayed reflag. Applying that reflag to the normalized Pi section is green: face 023 computes to the existing visible filler and its 012 base-arrow action remains whole. This closes both the former Pi projection gap and the pointwise-visible coherence gap; final native `DependentSimplex3_cat` endpoint packaging and arbitrary-`H` face comparison remain. |
| `ODS3-SOURCE-4` | pending | Construct the identity-`Delta[3]` native source tetrahedron, including its dependent top cell, from the retained recursive action. No primitive or opaque tetrahedron filler is permitted. |
| `ODS3-MAP-5` | pending | Map the one source native tetrahedron under arbitrary `H` through `dependent_simplex3_map`; retain the whole map rather than only its top component. |
| `ODS3-OBSERVE-6` | pending | Expose the unconditional `DependentSimplexObservation(C,3)` and readable projections agreeing with all four canonical dimension-two face observations. |
| `ODS3-PROFILE-7` | pending | Validate general directed, selected strict, and Path-valued readings; reject a wrong endpoint and verify that endpoint conversion does not imply top-cell collapse. |
| `ODS3-NEXT-8` | pending | Expose one further whole hom action for a later dimension-four child and record its exact source/target boundary without implementing dimension four. |
| `ODS3-DOC-9` | pending | Synchronize focused reviewers, source/check registries, Foundations, syntax/SOP status, READMEs/AGENTS where affected, report index, catalog, and source-only health. |
| `ODS3-CLOSE-10` | pending | Review the exact diff and evidence, create clean implementation and closeout checkpoints, and state the precise achieved boundary. No long aggregate or unauthorized integration/publication/cleanup. |

## 15. Completion Definition

This goal is complete only when the canonical native source tetrahedron and
its arbitrary-`H` dimension-three observation are constructed from existing or
properly promoted whole owners; all four ordinal faces are accounted for; the
top component is not an opaque filler; general/strict/Path and negative
reviewers pass; one next action remains available; affected authorities and
evidence are synchronized; and the worktree is clean at green local
checkpoints.

Merely observing that the fixed public next-action facade is too narrow, or
naming a possible future higher comparison, does not satisfy this completion
definition. If a genuine foundational prerequisite blocks construction, keep
the goal active while safe in-scope alternatives remain; report it as blocked
only under the persistent-goal blocked-status rules.

## 16. Launch And Baseline — 2026-08-19

The dedicated branch and worktree were created from clean completed checkpoint
`e157b37` and bootstrapped with the pinned pnpm workspace. The launch plan and
report-index routing pass report-header, source-TOC, and active-reference
checks. The ignored Infinity Codex archive is not replicated into a fresh
worktree; the archive in `/home/user1/emdash1` remains the linked recovery
evidence.

Focused quiet Lambdapi baselines are green for:

```text
emdash3_2_dependent_simplex_ordinal_filler.lp
emdash3_2_dependent_simplex_native_dimensions.lp
emdash3_2_tetrahedron_faces.lp
examples/dependent_simplex_ordinal_filler.lp
examples/dependent_simplex_native_dimensions.lp
examples/tetrahedron_faces.lp
```

The first material owner fact is already visible in the checked public type:
`ordinal_dependent_simplex2_next_func(H)` fixes both hom endpoints to the one
canonical source triangle. It proves iterability but is not by itself the
distinct-face arrow needed for a tetrahedron. `ODS3-OWNER-2` therefore starts
at the underlying `dependent_simplex2_map`/`fapp1_func` owner and the retained
join-cross action; no new action primitive is presumed.

The clean launch checkpoint is `10cca62`.

### 16.1 First Higher Owner Audit

The ignored owner-position probe

```text
tmp/probes/ordinal_simplex3_owner.lp
```

constructs the dimension-three source profile without a new kernel symbol:

```text
base    = Product_cat(Op_cat(Delta[2]),Terminal_cat)
family  = reindexed Unit_prof(Delta[3])
section = join_map_cross_transf(id_Delta[2],id_Terminal).
```

For an arbitrary old edge `p : x -> y`, one generic projection of this
section supplies the cross-triangle filler on `(x,y,3)`. The raw source keeps
the terminal-coordinate functor action. The existing `fapp1_id_path`, rigid
`Hom_fapp0` to precomposition bridge, and pre/post proof-time bridge move it
to the native stable `hom_postcomp_fapp0` endpoint. The same construction
therefore gives faces 013, 023, and 123; no three face-specific fillers or
rules are needed.

The canonical 012 filler lifts through the product/opposite base as a higher
arrow from its stable represented postcomposition endpoint to its direct
endpoint. Applying the section action once more succeeds and normalizes to
the expected recursive `fdapp1_int_cell`. This establishes the whole
dimension-three source of the top component and is stronger than the fixed
endomorphism-shaped public handoff.

The first attempted native packaging also rejects one overly short route:
the raw second action is not by itself the whole native `alpha0123` pair.
Face 123 is its first Sigma component, while the raw top still targets the
section action on the stable composite old arrow. The exact remaining join is
the generic section-composition comparison from that stable action to the
`(face123,face013)` pasting. It is not a missing tetrahedron filler, variance
mirror, or associativity axiom. The next probe must derive it from the
section/internal-action compositor and the existing stable-to-readable
postcomposition path before considering any new owner.

### 16.2 Whole Section Composition And Flagging Audit

The same ignored probe now closes the section-composition part of the owner
audit. A section `s : Pi_cat(E)` totalizes transparently as

```text
K -> Sigma_K(Const_K(1)) -> Sigma_K(E),
```

using the terminal total functor followed by `sigma_map_func(s)`. Applying the
already extracted ordinary `fapp1_compositor` to that whole functor gives the
missing comparison from the composite of the two section actions to the
section action on the formal composite base arrow. The formal composite is
moved to the named stable 012 base arrow by the existing
`hom_postcomp_fapp0`/raw-composition path and `eq_ap` of the whole section
action. Composing this comparison with the section's action on the lifted 012
filler constructs a whole tetrahedral cell.

Constructor-visible total objects and `sigma_arrow` actions expose that cell
in the existing recursive `DependentTriangle` presentation. Both projections
typecheck:

```text
whole section tetrahedron
  -> lifted face-012 base cell
  -> internal-action-derived dependent top cell.
```

No primitive symbol, rewrite rule, proof-time unifier, Sigma eta, join eta, or
associativity assumption was added. The generic compositor remains the owner,
and its ordinary next hom action remains available.

The probe also rejects a materially different shortcut. Pairing the projected
top cell directly with the native face-123 component generates incompatible
dependent-family obligations. This is not merely a stable endpoint mismatch:
the join-cross construction presents the tetrahedron with face 012 as its
outer base cell, whereas `DependentSimplex3_cat(C,x0,e01,t012)` presents the
same boundary with face 123 as the outer base cell. The dependent top is real,
but moving it between these two nested Hom/Sigma flaggings requires a whole
dependent rebracketing/exchange comparison. Pointwise coercions, an opaque top
filler, and a face-specific conversion rule are rejected.

The next source tranche must therefore derive the smallest whole comparison
from the existing Hom/Sigma, profunctor interchange, and join owners, or—only
if that derivation is demonstrably unavailable—promote one generic
higher-constructor comparison at that semantic owner. It must map the already
extracted top cell, retain a next action, and then construct the genuine
flagged source object; naming this prerequisite alone does not complete the
goal.

### 16.3 Reflagging And Endpoint-Conjugation Audit

The ignored owner probe now also establishes the reflagging boundary without
using the historical global associativity comparison.  The two one-arrow
bracketings

```text
(p23 o p12) o p01
p23 o (p12 o p01)
```

are connected by `represented_assoc_readable_cell`, and the existing
`Hom_func` plus represented precomposition owners assemble a whole functor
from the join presentation's top hom-category into the native flagged top
ambient category.  Applying it to the recursively extracted top cell succeeds.
Thus neither an associativity axiom nor a new base-cell constructor is the
remaining issue.

A second, more direct route applies the same whole rebracketing to the raw
second section action on the lifted 012 filler.  Its source, target, and mapped
top all typecheck.  This confirms that the top cell itself is present at the
generic `piapp1_func`/`fdapp1_int_cell` owner and is not manufactured by the
later readable section-compositor presentation.

Three tempting shortcuts are now rejected with typed negative evidence:

1. the mapped raw endpoints are not definitionally equal to the canonical
   readable endpoints, because the latter explicitly conjugate the raw face
   actions along equality-induced arrows;
2. applying the ordinary compositor to `Op_func(F)` does not create a generic
   reverse compositor—`Op_cat` reverses 1-arrow endpoints, not all higher hom
   directions; and
3. packaging the raw 013 and 023 components directly as native Sigma arrows
   fails because their rigid `Hom_fapp0` sources have not yet passed through
   the canonical whole endpoint conjugation.

The remaining construction is therefore sharply identified.  It must compare
the following two whole procedures by a higher cell:

```text
raw join-section action -> apply recursive next action -> reframe endpoints
raw join-section action -> conjugate canonical face endpoints -> compose faces.
```

Direct equality of their component proof terms is neither expected nor
required.  The next probe first tests the existing ordinary/displayed
post/pre-laxity and rigid-Hom interchange owners.  If those do not expose the
needed whole comparison, escalation row 3 permits one generic propositional
comparison at this join/internal-action boundary, provided it maps the already
extracted top and retains a next hom action.  A face-specific coercion or an
opaque tetrahedron filler remains excluded.

This audit also distinguishes the current result from the existing code
decoder.  `dependent_simplex_code_map` recursively maps an already chosen
intrinsic flag code and its decoded `PathOut` classifier along a functor.  It
does not select, for arbitrary `n`, the ordinal flag object carried by
`H : Functor(Delta[n],C)`.  The present dimension-three construction is the
first nontrivial term-level instance of that still-missing uniform ordinal
realization, rather than a duplicate classifier decoder.

### 16.4 Generic Terminal-Right Normalization

The next focused probes separate three issues which had previously appeared
as one large endpoint mismatch.

First, a terminal-source specialization of the historical global strict
functor identity rule does normalize the concrete arrow
`G[Terminal_obj]` to an identity.  It does not identify the whole retained
action, because the latter remains under the generic ladder

```text
Prof_reindex_fapp1_func
  -> evaluation at the retained cross object
  -> product-pair embedding p |-> (p,id_*).
```

The temporary runtime rule was therefore removed rather than promoted.  A
direct primitive presentation of `Delta[n]` would have the same whole-action
obligation and would duplicate the reusable join cross; it is not a repair
for this boundary.

Second, the rule-free focused probe

```text
tmp/probes/prof_reindex_terminal_native_normalization.lp
```

establishes the smallest dimension-independent interface.  For arbitrary
`F : A -> B`, `G : 1 -> B`, endpoints `W,X : A`, and retained arrows
`g,h`, it names:

```text
native action:
  pull back homd_(id, (X,g), (W,h)) along p |-> (p,id_*)

expected action:
  p |-> Hom_B(g o F[p], h).
```

One supplied normality witness `G[id_*] = id` supports one propositional path
between those **whole Cat-valued families**.  Equality-to-arrow conversion,
generic `Pi_func`, and ordinary hom action then derive a displayed map, a
whole section-normalization functor, and another iterable hom action.  The
normality argument is intentional: today's global strict prototype supplies
it via `fapp1_id_path`, while a later lax migration can require it from the
selected strict profile instead of silently assuming it for every functor.

Third, the ordinal specialization is now green in

```text
tmp/probes/join_cross_whole_action_compare.lp.
```

The existing restricted recursive second section is definitionally the
generic native family.  Applying the generic whole section normalizer and
then its `piapp1_fapp0` action to
`ordinal_simplex2_source_canonical_filler` constructs a genuine next higher
cell in the canonical precomposition family.  No pointwise tetrahedron
constant, face-specific rule, proof-time unifier, terminal eta, or direct
ordinal category is used.

The promoted boundary is
`emdash3_2_prof_reindex_terminal_normalization.lp`, with focused reviewer
`examples/prof_reindex_terminal_normalization.lp`.  It is generic in `A` and
therefore reusable at every successor presentation
`Delta[n+1] = Join_cat(Delta[n],Terminal_cat)`.  It does not by itself assert
the all-`n` ordinal/dependent equivalence: the immediate remaining task is to
project and package its dimension-three cell in the existing flagged
`DependentSimplex3_cat` presentation, then verify the four selected faces.

Fourth, the endpoint audit required a computational refinement of that
rule-free family comparison. The same generic module now exposes
`prof_terminal_expected_retained_source_transf`, whose component is the
equality-induced arrow from the readable source action to the retained native
source, and `prof_terminal_explicit_normalization_funcd`, whose fibre
projection is the corresponding rigid `Hom_func`. Both are whole owners, so
`tapp1_func` and `functord_laxity_transf` retain the higher comparison needed
by the tetrahedral consumer. Their two narrowly guarded projection rules pass
the strict LHS audit and introduce no warning delta.

The same audit settled the packaging order. The normal-lax section compositor
points from the sequential 013/123 pasting to the stable composite action and
is not invertible in a general directed target. The action of
`ordinal_simplex2_source_canonical_filler` then points from that stable middle
boundary to the 012/023 boundary. Both factors and their whole forward
composite typecheck through the explicit normalizer and retain higher action;
the composite, not either factor alone, is the candidate formal alpha.
At checkpoint `03d51c8`, canonical endpoint pasting, source packaging, and
arbitrary-`H` face comparison still remained.

The next endpoint audit closes the source half constructively. The ordinary
compositor's formal source is compared with its sequential-action reading by
the existing base postcomposition path, `eq_ap`, and `fapp1_comp_path`; its
formal target is compared with the canonical pair action. `Hom_func` then
conjugates the existing nonidentity compositor rather than replacing it by an
equality. Whiskering that cell by face 013 yields the expected source-pasting
comparison.

The native `homd_` transport retains a different but equivalent projection
order: represented fibre covariance followed by precomposition. The missing
higher rung is now the generic proof-time comparison
`hom_precomp_along_fapp1_comp_prod_path` in `emdash3_2.lp`. It compares capped
precomposition hom action with product-composition whose first higher input is
identity, while retaining both runtime owners. Generic point and hom-action
probes, the concrete native-source path, and the 013-whiskered comparison are
green. Direct kernel checking is green; the warning inventory remains exactly
`1271` (`1112` unjoinable critical pairs and `159` replaceable variables), and
the strict LHS audit reports no unreviewed compound slots. A broad source sweep
was deliberately stopped after many downstream modules passed, in accordance
with the explicit no-long-aggregate policy. The remaining source task is to
assemble the retained 012 action at the native target without inverting the
directed normalizer laxity, then package the resulting tetrahedron.

Focused quiet source and reviewer checks pass. Warning-enabled checks are also
green: both inherit exactly `1271` diagnostics (`1112` unjoinable critical
pairs and `159` replaceable pattern variables), so the explicit projection
rules add no warning delta. The strict LHS audit reports zero unreviewed
compound slots, and the reviewer covers both component betas, retained higher
action, wrong-normality rejection, and direct noncollapse. Source-TOC,
active-reference, report-header, catalog, and diff hygiene checks pass. The
long repository-wide health refresh remains waived under the user's explicit
aggregate policy; focused exact-content evidence is the proportional
checkpoint gate.

### 16.5 Computational Pi Postcomposition

The action-target audit isolated one general LF interface rather than a
simplex-specific missing cell.  Mapping a section through the explicit
terminal normalizer was available as the hom action of `Pi_func`, but its
object and base-arrow projections had no stable computational owner.  As a
result, the normalized face components and the mapped 012 action were
mathematically the same whole section while appearing through unrelated
projection orders.

The promoted `section_postcomp_sec(FF,s)` is the object action of `Pi_func` on
`FF : Functord(E,D)`.  Its component computes to `FF[k](s[k])`, and its action
over `p` computes through

```text
fdapp1_int_hom_fapp0(FF,p,s[x],s[y],s[p]).
```

The latter includes the outer displayed laxity and the image of the inner
section cell in one existing internal-action projection.  It neither assumes
strictness nor postulates a naturality square.  A first probe using a rule on
all displayed composites was green but added 17 critical-pair diagnostics;
it was rejected.  The stable section-specific owner is the narrower semantic
boundary and leaves unrelated displayed composites untouched.

Tracked generic assertions in `emdash3_2_checks.lp` cover the Pi object
action, point component, and base-arrow component.  The core, tracked checks,
and focused normalized-section/face/action probes are green.  The strict LHS
audit reports zero unreviewed compound slots.  The warning inventory is now
`1279` (`1120` unjoinable critical pairs and `159` replaceable variables), an
eight-diagnostic increase localized to the intentionally overlapping Pi
identity, constant-section, and higher-component projection routes.  A typed
identity join and the concrete owner consumer are green.  Per repository SOP,
the warnings are recorded diagnostic evidence rather than an automatic veto;
no broad or face-specific join was added merely to suppress them.

This closes the general LF/foundational prerequisite.  The remaining work is
the dimension-three flagged packaging itself: project the now-coherent
normalized section's forward compositor/action composite into the native
`DependentSimplex3_cat` flag, then map that one source object under arbitrary
`H` and expose its four face comparisons.

This concrete consumer does **not** trigger the deferred redesign of
`piapp0`, `piapp1_func`, or `piapp1_fapp0` into primitive heads.  Their current
definitions successfully project through the stable `tapp0_fapp0` and
`fdapp1_int_*` owners once `Pi_func`'s object action has the single stable
`section_postcomp_sec` boundary.  Reconsider primitive Pi eliminators only if
a later arbitrary-dimensional consumer cannot retain a required whole action
or if independent projection bridges begin to proliferate again.

### 16.6 Whole Constructor-Visible Reflag

The next endpoint audit found that the normalized Pi section was coherent but
its fibres still used the precomposition presentation of
`p |-> g o F[p]`. Reflagging each point independently produced the correct
faces but discarded the base-arrow action needed by the tetrahedral cell.
The missing boundary is dimension-independent and now lives in
`emdash3_2_prof_reindex_terminal_normalization.lp`.

`prof_terminal_visible_source_func` presents the same object formula as one
whole semantic composite:

```text
Hom_A(W,X)
  -> Hom_B(FW,FX)
  -> Hom_B(FW,G*).
```

The first arrow is `F`'s whole hom action and the second is stable
postcomposition by `g`. It is intentionally not definitionally equal to
`prof_terminal_expected_source_func`. Their object actions meet at the raw
composite, yielding `prof_terminal_expected_visible_source_fapp0_path`.
The stable displayed owner `prof_terminal_expected_visible_funcd` uses the
reverse equality-induced source arrow inside one rigid `Hom_func`; its sole
component beta is `prof_terminal_expected_visible_fibre_func`, while generic
`Functord` action owns all higher coherence.

Focused generic source and reviewer checks are green. Warning-enabled runs
inherit exactly `1279` diagnostics (`1120` unjoinable critical pairs and `159`
replaceable pattern variables), so the new rule adds no warning delta. The
strict LHS audit reports zero unreviewed compound slots. A negative reviewer
keeps the expected and visible whole source functors distinct. The concrete
ordinal application is also green: mapping the computational normalized
section through the new owner makes its `p02` component exactly the existing
constructor-visible face-023 filler, and its action on
`ordinal_simplex2_source_canonical_filler` remains available at the generic
`piapp1_fapp0`/`fdapp1_int_hom_fapp0` ladder.

A resumable repository-health refresh was stopped under the goal's explicit
long-aggregate policy after more than two minutes and 34 additional registered
targets had passed; it reported no failure and wrote no health snapshot. The
source-health report remains a single closeout gate rather than a per-tranche
rerun.

This does not yet complete `ODS3-FACES-3`. After represented-associator and
native endpoint reframing, the two final alpha endpoints remain
propositionally rather than definitionally presented. The next probe must
project those comparisons from the same whole visible section action and then
pair its face-123 base component with its dependent top through the existing
`dependent_tetrahedron` constructor. No direct `eq_refl`, face-specific rule,
whole-source equality, or primitive Pi eliminator is justified.

### 16.7 Whole Four-Face Total And Normalized Source Factor

Two subsequent ignored probes narrow that last packaging step further. In
`tmp/probes/ordinal_simplex3_visible_total.lp`, the already-composed
section-compositor-plus-012 action maps through the whole visible reflag as one
arrow of `Op(Sigma(base,visibleAction))`. Both outer base projections compute
to the expected composite and direct ordinal edges; the dependent top and its
exchange through the represented associator typecheck as whole actions. This
uses all four faces in one term rather than attempting to compose capped
pointwise coercions.

The companion
`tmp/probes/ordinal_simplex3_normalized_source_comparison.lp` rebuilds the
forward source compositor exclusively from the normalized
constructor-visible faces. Generic compositor endpoint paths, represented
fibre-covariance/precomposition comparison, and postcomposition whiskering
derive a directed cell from the sequential 013/123 pasting to the native
face-123 transport source. The probe is green and introduces no rule,
unifier, or old/new-face equality.

The negative endpoint tests are informative: the exchanged whole-total
endpoint is not definitionally equal to that normalized stable source, just as
the 012/023 endpoint is not definitionally equal to the corresponding Sigma
projection. These are the two directed factors carried by the whole reflag
and its displayed laxity, not missing object equalities. The remaining
consumer step is therefore to project the forward 012/023 factor from that
whole laxity and compose it with the green normalized source comparison,
yielding the native top without inverting either factor.

This architecture remains dimension-independent up to the final flag: the
Pi postcomposition owner, terminal normalization, visible reflag, compositor,
and retained next actions contain no dimension-three data. The checked
dimension-three packaging is still required before claiming a uniform
variable-`n` ordinal-adequacy theorem; a later recursive owner over the
existing intrinsic dependent-simplex codes must package the same iterable
pattern at arbitrary dimension.

### 16.8 Base-Change Audit And Whole-Projection Correction

A later owner audit corrects one over-optimistic sentence in section 16.7.
The final consumer is not obtained by simply ascribing the reconstructed
source comparison to the exchanged action endpoint.  The attempted term is
rejected, and direct equalities between the capped endpoints are also
rejected.  They retain different whole-action and endpoint-transport
histories; treating that as a missing `eq_refl` would be precisely the
face-specific normalization prohibited by this plan.

One apparent prerequisite is now closed constructively.  For
`F : A -> B`, `E : B -> Cat`, and `u : E[F x]`, `v : E[F y]`, dependent hom
after pullback is definitionally the pullback of dependent hom along the
whole hom action:

```text
homd_(id_(F^*E),x,u,y,v)
  =
(Op(F_1))^* homd_(id_E,Fx,u,Fy,v).
```

The generic probe
`tmp/probes/homd_pullback_compatibility_refl.lp` proves the Catd equality by
`eq_refl`; replacing the earlier probe-only opaque path by that transparent
term leaves the normalized total and action-total probes green.  Therefore
no Beck--Chevalley axiom, rewrite, unifier, or primitive `piapp*` redesign is
needed.

The source and target whole carriers also have the same *kind* of recursive
shape:

```text
join carrier   = Op(Sigma(Op(Hom(base)), secondAction))
native carrier = Op(Sigma(nativeTopBase, nativeTopFamily)).
```

Both equalities are judgmental in
`tmp/probes/ordinal_simplex3_whole_category_shapes.lp`.  Consequently the
ordinary total-category Fubini law
`Sigma_k Sigma_e D(k,e) ~= Sigma_(k,e) D(k,e)` is mathematically natural but
is not, by itself, the missing comparison here: the two totals have different
base/family owners rather than merely different parenthesization.  Promoting
Fubini without an exact instantiation would be scope drift.

The remaining bounded prerequisite is therefore one **whole** comparison
between those already-existing join/internal-action and native
`homd_`/Sigma presentations.  It must map the retained higher cell before
projecting its dependent endpoint, expose the four selected face readings,
and retain another hom action.  The next probe follows escalation rows 2--3:

1. first attempt a transparent whole base/family reindexing from the active
   terminal comparison, visible reflag, and Sigma-total owners;
2. if no such composite elaborates, introduce one named whole projection
   facade at that semantic owner; and
3. use one propositional whole join/internal-action comparison only if the two
   existing whole maps are not definitionally equal.

No capped endpoint equality, arbitrary bracketing normalizer, generic reverse
compositor, face-specific rule, or opaque tetrahedron filler is admitted.
The green `os3ff_native_to_stable` factor remains useful evidence: its
orientation comes from the existing typed strict functor-composition path,
not inversion of a directed lax compositor.  It is not yet the final native
top until the whole carrier comparison above is checked.

### 16.9 Parameter-Natural Join-Beta Action

The next owner probe rules out both the ordinary Fubini detour and a merely
fixed-generator higher projection.  Converting the existing
`join_map_generator_beta(F,G)` to an equality-induced transformation and
retaining its `tapp1_func` action is well typed, but its indexing category is
`Terminal_cat`; it records higher action at one fixed walking generator and
does not vary that generator along an old-base arrow of `Delta[2]`.

The relevant generic owner is already stronger.  Package the identity
successor presentation

```text
Delta[3] = Join_cat(Delta[2],Terminal_cat)
```

as `JoinMapObjectData` with the existing left inclusion, terminal right
branch, and primitive `join_map_cross_transf`.  Then
`join_map_extend_cross_cell` is the equality-induced **whole displayed
transformation** from the action-observed cross to that primitive cross.  Its
existing arbitrary-displayed-action ladder supplies:

```text
tdapp1_int_cell(...,r01,*)
```

for every old-base arrow, and, for the lifted 012 filler,

```text
tdapp1_int_presheaf_arrow(...)
  -> tapp1_fapp0(...,kappa012)
```

as a whole functor between the corresponding higher hom categories.  The
focused probe
`tmp/probes/ordinal_simplex3_join_cross_beta_action.lp` checks this entire
ladder.  It also checks judgmentally that the target profunctor and primitive
cross are exactly the existing `os3_source_prof` and `os3_source_cross` owners.
No new join cell, rule, unifier, `piapp*` primitive, or Fubini comparison is
needed to obtain this parameter-natural action.

The final target is intentionally not definitionally
`Fibre_cat(os3_second_action_catd,r012)`.  The arbitrary-transfor action has a
mixed endpoint: its source retains the action-observed cross while its target
retains the primitive cross.  This is the ordinary naturality boundary of the
whole equality-induced beta, not a bracketing defect.  The next probe must use
the two endpoint components of the same equality-induced cross cell to
conjugate that mixed-endpoint action into the native primitive presentation.
Those components are invertible because the owner comes from equality; this
does not license inversion of a generic directed compositor.  Only after that
whole conjugation is green should its component be compared with
`os3nna_source` and used in the final native top.

### 16.10 Whole Conjugation And The Deferred Pi Interface

The required whole conjugation is now green in
`tmp/probes/ordinal_simplex3_join_cross_beta_conjugation.lp`.  For an arbitrary
observed cross section `O` and equality `O = os3_source_cross`, equality
induction supplies forward and reverse displayed cells, retains the whole
`tdapp1_int_presheaf_arrow`, maps its mixed second-action category into the
primitive second-action owner, and derives typed source, target, and whole-top
comparisons.  In the reflexive case all three comparisons compute to the
existing `os3_raw_top` presentation.  The independent
`tmp/probes/ordinal_simplex3_join_cross_reflexive_action.lp` check confirms the
same direct top from the ordinary internal-action owner.  Thus the
parameter-natural join comparison has reached the exact primitive recursive
second action; no fixed-face endpoint rule is needed.

A separate fixed-right-pair probe provides useful corroborating evidence.
`tmp/probes/section_pullback_stable_pair_consumer.lp` maps `p02`, `p012`, the
canonical filler, and its whole section action through one recursively acting
pair functor; all four observations compute, and the mapped action is
`os3_raw_top` by typed `eq_refl`.  This does not justify promoting that helper:
the parameter-natural join-beta owner above is stronger and already owns the
relevant higher action.

This consumer therefore does **not** require a primitive-`piapp*` migration.
The audit distinguishes three facts:

1. the generic public `piapp1_fapp0` view and its underlying
   `fdapp1_int_cell` view can be compared in isolation;
2. changing `piapp1_fapp0` into a stable head and adding a runtime fold to
   `fdapp1_int_cell` fails subject reduction, so that candidate is rejected;
3. a proof-time stable-head comparison can be made to typecheck in a full-file
   experiment, but neither the dimension-three construction nor the stronger
   whole join action needs it.

No `piapp*` rule, unifier, or primitive change is promoted.  Stable Pi
eliminator heads remain a legitimate future interface/consolidation topic if
another consumer needs readable projection normal forms, but they are not a
mathematical or computational prerequisite for this goal.

The remaining native step is narrower than the former Pi detour.  Map and
reframe the now-conjugated `os3_raw_top` through the existing represented
associator/native exchange, then compose the resulting directed endpoint
factors.  Direct `eq_refl` between the stable, action, and native capped
endpoints remains deliberately rejected: those terms retain different
projection histories, while the whole comparison already carries the needed
directed information.  `ODS3-FACES-3` remains in progress until that arrow is
packaged with the four faces and checked under arbitrary `H`.

### 16.11 Pulled-Section Endpoints And Whole Sigma Transport

The next audit identifies and closes the actual Pi interface requirement.
The generic action theorem could already be instantiated, but its dependent
source endpoint was hidden inside the theorem-selected Hom carrier.  Two
rule-free projection theorems are now promoted at the existing
`section_pullback_sec` owner in `emdash3_2.lp`:

```text
section_pullback_piapp1_src_path
section_pullback_piapp0_path
```

They state, respectively, that the transported source of a pulled section
action is the original transported source along `F[p]`, and that evaluation
of the pulled section at `y` is evaluation of the original section at `F[y]`.
Both generic declarations, their actual dimension-three specialization, and
the active kernel check are green.  They add no rule, unifier, primitive
`piapp*` head, or Pi eta principle.  This is the reusable interface the
consumer needed; the broader primitive-Pi experiment remains rejected.
The warning inventory remains exactly `1279` diagnostics (`1120` unjoinable
critical pairs and `159` replaceable pattern variables), and the strict LHS
audit still reports zero unreviewed compound slots.  A repository-wide
`make check` continuation was stopped after the edited kernel and its first
downstream targets had passed, under the standing no-long-aggregate policy;
the direct kernel target and focused consumer are the tranche gates.

The semantic reversed-base hom functor, without the diagnostic fixed-right
replacement, computes on all three data required by the top cell:

```text
p02       |-> r02
p012      |-> r012
kappa012  |-> kappa012.
```

All three comparisons are typed `eq_refl` in
`tmp/probes/section_pullback_actual_base_paths.lp`.  Reframing the pulled
native action through the two promoted endpoint paths is green in
`tmp/probes/section_pullback_actual_action_reframe.lp`.

The decisive correction is to stop moving the resulting dependent source
pointwise.  The active `sigma_pullback_total_func` maps the complete
`(kappa,lambda)` arrow from `Sigma(F^*D)` to `Sigma(D)`, preserving its
dependent endpoints in one whole action.  The focused sequence

```text
section_pullback_actual_total_map.lp
section_pullback_actual_total_projections.lp
section_pullback_actual_total_kappa.lp
section_pullback_actual_total_raw_lambda.lp
```

is green.  It maps the native total, projects its computed base, composes that
base path with `mapped kappa012 = kappa012`, and uses equality induction only
inside the existing `homd_` fibre.  Lambdapi then accepts the transported
fibre directly at

```text
Hom(raw_top_source, raw_top_target).
```

This is the constructive canonical raw top needed by the continuation.  An
optional judgmental equality with the older `os3_raw_top` is rejected and is
not required: the two cells retain different derivation histories.  The next
step is now precisely to carry this canonical cell through the existing
represented-associator/native exchange as a whole and package the resulting
visible tetrahedron.  No capped source equality, endpoint normalizer, Fubini
axiom, or `piapp*` redesign remains on that path.
