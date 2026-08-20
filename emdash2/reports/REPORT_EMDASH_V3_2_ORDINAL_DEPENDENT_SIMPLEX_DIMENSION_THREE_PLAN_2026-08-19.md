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
| `ODS3-FACES-3` | in progress | Define the four arbitrary-`H` triangle restrictions and establish their six shared edge/vertex comparisons through existing whole face/join owners, without face-specific rewrite rules. The source audit constructs faces 013, 023, and 123 from one generic cross-action projection and retains face 012 as the existing canonical filler. The generic terminal-right module now also exposes a computational directed source component and whole displayed normalizer with retained laxity action. Separate green compositor and action projections establish the formal-alpha architecture: the forward section compositor supplies the sequential-013/123 factor and the 012 action supplies the following factor; their already-green whole composite uses all four faces without an inverse compositor. The compositor has now been conjugated to its readable endpoints, whiskered by face 013, and related to the native `homd_` source through a generic higher precomposition/product-composition bridge. Native action-target packaging and arbitrary-`H` face comparison remain. |
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
