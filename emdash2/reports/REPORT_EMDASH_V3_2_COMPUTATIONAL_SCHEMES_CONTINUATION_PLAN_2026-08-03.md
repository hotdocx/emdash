# EMDASH v3.2 Computational Schemes Continuation Plan

Date: 2026-08-03

Status: living design, decision, implementation, and validation ledger

Baseline: local checkpoint `4427b99` (`docs: record computational affine-scheme checkpoint`)

Parent plan:
`REPORT_EMDASH_V3_2_PRESHEAVES_SITES_SCHEMES_PRELIMINARY_PLAN_2026-08-01.md`

Recovery evidence:

- `infinity-codex:019fbb03-cc64-7cf2-be18-24c35b0dfab0:1c14d3ed-a654-4efd-b2e0-6d8409c80648`
  records the completed affine-MVP checkpoint and initial feasibility split;
- `infinity-codex:019fbb03-cc64-7cf2-be18-24c35b0dfab0:019fc5ce-9958-7be2-8ece-26a2a3894fe4`
  records the subsequent mathematical and architectural correction concerning
  locality, overlap/cocycle data, gluing effectivity, sites, and scheme
  presentations.

This file is the active continuation plan after the affine computational MVP.
It is intentionally living: implementation probes, concrete consumers, and
mathematical comparison results may refine its proposed interfaces. The active
kernel and one-way library sources remain authoritative over this plan. The
parent PSSS ledger remains the detailed history and dependency map; where its
PSSS-D-117 wording conflicts with this plan, the decisions below supersede it.

## 1. Objective

Continue from the checkpointed affine package toward a computational,
non-affine, finite-qcqs scheme interface while preserving the emdash SOP:

1. keep whole functorial action, restriction, and naturality at their existing
   internal owners;
2. make concrete chart values, localizations, restrictions, overlaps, and glue
   compute whenever the selected data make this meaningful;
3. distinguish semantic schemes from their chosen computational
   presentations;
4. derive overlap and cocycle structure from an existing global object rather
   than asking ordinary scheme users to duplicate it componentwise;
5. keep atlas-first gluing as a separate construction interface;
6. retain all supplied assumptions visibly, especially sheafification,
   coordinate-localization locality, locally-ringed support, and any chart
   realization not yet internally constructed; and
7. avoid allowing general sheafification, arbitrary descent, stalk theory, or
   a complete category of schemes to block the next bounded computational
   consumer.

The intended result is not merely a proposition that a textbook scheme exists.
It is a semantic object equipped, where chosen, with presentations that expose
executable coordinate rings, restriction maps, localization comparisons, and
overlap computations.

## 2. Completed Affine Baseline

The baseline module
`emdash3_2_commutative_algebra_affine_schemes.lp` defines the transparent
package

```text
AffineSchemePresentation(R)
  = Sigma P : AffineStructureSheafPresentation(R),
      AffineCoordinateLocalizationLocality(R).
```

The first field supplies:

- the exact internally generated big-affine Zariski topology;
- a supplied reflective CommRing-valued sheafification capability;
- one selected structure-sheaf object; and
- a whole `DefIso` from its included presheaf to the computing coordinate
  presheaf `affine_spec_coordinate_psh(R)`.

The second field supplies, for every chart, section, and selected
universal-property localization, a fixed-forward whole
`OmegaEquivAlong Cat_cat`. Its forward functor is the existing restriction
from the localization carrier to coherent matching families on `D(s)`; its
selected inverse is a whole glue functor and both cancellation laws are paths
of whole composite functors.

The closed `F2 x F2` reviewer additionally computes:

- the complementary-idempotent finite Zariski presentation;
- its two selected localization charts;
- the whole structured restriction maps;
- their orthogonal product generator; and
- the resulting zero-ring overlap.

This is a nontrivial atlas of an affine scheme. It is not yet a non-affine
scheme, a universal gluing construction, a locally-ringed comparison theorem,
or a category of schemes.

The checkpoint consists of:

- `68578be` — `feat: add thin computational affine schemes`; and
- `4427b99` — `docs: record computational affine-scheme checkpoint`.

The worktree was clean at the continuation boundary. No merge, push, history
rewrite, publication, branch deletion, or worktree cleanup is part of this
plan.

## 3. Historical Cartier/Zeuner Mapping

The v3.2 affine package is a selective modernization of the experimental
`cartierSolution16.lp.txt`, not a declaration that the historical experiment
was mathematically complete.

| Historical intention | v3.2 owner | Reading |
| --- | --- | --- |
| `site`, `smod`, `mod_smod`, unit, and glue | `GrothTopology`, `Sheaf_cat`, supplied `SheafificationCapability`, whole adjunction and glue owners | The useful assumption-explicit reflector boundary is retained, but action and cancellation are whole internal data. |
| `struct_mod_loc` | `ReflectiveCommRingedSite` and `AffineStructureSheafPresentation` | This currently gives a reflective ringed site and computing sheaf presentation; its old name must not be read as a proved local-ring condition. |
| invertibility support and `mod_loc_elim` | `comm_ring_psh_invertibility_sieve` and `CommRingPshLocalizationLocality` | This recovers the computational basic-open localization assertion using universal-property localizations and coherent internal matching families. |
| `ascheme_*` basic opens and restrictions | `AffineSpecBigSlice_cat`, the coordinate presheaf, structured localization arrows, and overlap comparisons | Object values and arrow action compute through existing Sigma, functor, and CommRing owners. |
| finite joins/unimodular covers | finite families, unimodular presentations, selected localization families, and generated big-affine topology | The cover/topology boundary is now explicit and internally generated by an impredicative least-topology construction. |
| `scheme_slice_ascheme` | future affine realization of a restriction/slice chart of a global ringed object | Still open; it requires an honest whole comparison between the ambient chart restriction and an affine presentation. |

The current fixed-forward equivalence corresponds to the basic-open/qcqs
formula

```text
O(D(s)) ~= O(U)[1/s].
```

It is the computational center of the old `mod_loc_elim` idea and corresponds
to Zeuner's qcqs localization lemma. It is not, by itself, the definition that
all stalks are local rings.

## 4. Three Locality Notions

The word *locality* must remain qualified because three distinct interfaces
are in play.

| Name in this plan | Content | Current status |
| --- | --- | --- |
| Zariski sheaf locality | Compatible sections over a covering sieve glue uniquely. | Matching/descent infrastructure exists in pieces; no general theorem should be inferred from coordinate-localization locality. |
| Locally-ringed support locality | The invertibility-locus operation `D` is a support; in the ordinary spatial setting this is equivalent to local stalk rings. | The invertibility sieve exists, but its full support laws and comparison theorem are not yet assembled. |
| Basic-open coordinate-localization locality | On an appropriate affine/qcqs chart, coherent sections over `D(s)` are equivalent to `O(U)[1/s]`. | Implemented assumption-explicitly by `CommRingPshLocalizationLocality` and its affine specialization. |

Max Zeuner uses all three ideas in distinct roles: a local Z-functor is a
Zariski sheaf, a locally ringed lattice has an invertibility map satisfying
support laws, and the qcqs lemma computes sections on `D(s)` by localization.
For ordinary ringed spaces, the support formulation is compared with local
stalk rings. These facts justify a future bridge but do not collapse the three
classifiers into one.

Consequences for v3.2:

1. retain the current public name only with the full qualifier *coordinate
   localization locality*;
2. do not advertise `CommRingPshLocalizationLocality` as covering-sieve
   sheafhood or a stalk-local-ring predicate;
3. audit and, when a consumer requires it, assemble a separate point-free
   invertibility-support capability;
4. prefer that support capability as the computational locally-ringed
   interface; and
5. treat a stalk-local-ring theorem as a mathematical comparison layer rather
   than forcing stalk construction into the kernel-facing MVP.

The support and localization interfaces may eventually reinforce one another
under affine/qcqs hypotheses, but no naked equivalence between them is assumed
by this plan.

## 5. Global-First And Atlas-First Interfaces

Two constructions must not be conflated.

### 5.1 Global-first presentation

Given an already existing global ringed object `X`, choose a covering atlas
and affine presentations of its chart restrictions. Pairwise overlaps are
pullbacks/restrictions inside `X`; transition maps and triple compatibility
are consequences of the global structure, chart comparisons, and generic
composition. They may have named derived observations, but they are not
independent user-supplied objectwise squares.

This is the intended normal `SchemePresentation(X)` direction and the closest
continuation of the historical Cartier experiment.

### 5.2 Atlas-first construction

Given independent affine objects before a global `X` exists, one must supply
open overlap pieces, whole overlap isomorphisms, and appropriate cocycle data.
A gluing constructor then realizes them as a global object and proves the
restriction comparisons and universal property.

Those witnesses are legitimate inputs to a *constructor*. They should not be
duplicated as fields of every global-first scheme presentation.

### 5.3 SOP consequence

For either direction, whole functors, transformations, structured maps,
`DefIso`, and `OmegaEquivAlong` remain the owners. External component-only
naturality or commutative-square families are not acceptable substitutes.
When a concrete constructed functor initially requires laws, those laws should
be consumed once by its whole constructor and then propagated internally.

## 6. Two-Chart Gluing And Effectivity

Gluing two affine charts means starting from

```text
Spec(A), Spec(B), U subset Spec(A), V subset Spec(B), and U ~= V,
```

then constructing a global scheme that identifies the chosen opens. The
standard non-affine test is the projective line, obtained from two affine
lines by identifying their nonzero principal opens via inversion.

This is useful because it simultaneously consumes localization, open-chart
restriction, whole transition isomorphisms, and global realization. It is not
required to define or recognize every scheme, and it is not a complete test
of triple-overlap coherence.

The word *effective* is reserved for a separate property: compatible local
data are realized by a global object with the expected restriction
identifications and universal property. It does not merely mean replacing two
charts by many charts.

The arity ladder is:

1. two selected charts;
2. a selected finite atlas, sufficient for the present qcqs direction; and
3. an unrestricted indexed atlas, which is outside the near-term MVP.

The near-term milestone is therefore:

> derive the internal overlap/Čech restriction diagram of a selected finite
> affine cover; later construct a realization interface for compatible finite
> open-gluing data.

This plan does not claim arbitrary fpqc descent or unrestricted atlas
effectivity.

## 7. Small, Big, And Affine Site Comparisons

The existing `AffineSpecBigSlice_cat(R)` is a big-affine presentation: its
objects range over affine schemes over `Spec(R)`, equivalently appropriately
oriented `R`-algebras.

Four distinctions must remain explicit:

- the small Zariski site uses open subschemes of a fixed base;
- the big Zariski site uses all schemes over the base;
- the small affine site is an affine basis for the small site; and
- the big affine site is an affine basis for the big site.

The affine/full comparisons within the same small or big scope may induce
topos equivalences. The small and big Zariski topoi are not generally
equivalent. Accordingly, the old phrase *small/big-site equivalence* is
superseded by the following narrower tasks:

1. construct/restrict to basic or affine opens when a concrete consumer needs
   the small site;
2. show that coordinate values and restrictions agree under that restriction;
3. compare a principal-open basis with the full small Zariski site where the
   required basis theorem is available; and
4. keep the functorial/geometric equivalence of qcqs schemes distinct from any
   equivalence of sites or topoi.

No small-site construction is required for the first global-cover substrate.

## 8. Semantic Schemes And Computational Presentations

The intended eventual layering is:

```text
PresentedScheme
  = a semantic scheme X
  + a selected computational presentation of X

PresentedScheme  --realize/forget-->  Scheme_cat.
```

More explicitly:

- `Scheme_cat` should be representation-independent and carry whole scheme
  morphisms;
- `Spec_func : Op(CommRing_cat) -> Scheme_cat` should expose the affine
  computation on ring maps;
- `SchemePresentation(X)` should be a certificate over `X`, retaining a
  selected finite affine atlas and computing comparisons;
- a total `PresentedScheme_cat` may package `(X,presentation)` when a category
  of presented objects is useful; and
- chartwise/presentation-preserving maps may be compilation witnesses, but
  ordinary scheme morphisms should not be required to preserve a chosen
  atlas.

This separation permits multiple presentations of the same scheme. Do not
quotient them prematurely. Whole `DefIso`/`OmegaEquiv` comparisons can relate
computing representations while preserving visible ownership.

The semantic category enables composition, base change, functor of points,
and gluing universal properties. The presentation layer supplies executable
normal forms. Neither replaces the other.

## 9. Staged Proposed Architecture

### CS-01 — Global reflective ringed object with a selected cover

Before naming a scheme, introduce a thin global-first substrate of the form

```text
ReflectiveCommRingedSpaceCover(K)
  = Sigma A : ReflectiveCommRingedSite(K),
    Sigma X : Obj(K),
    Sigma R : Sieve_K(X),
      Covers(topology(A),R).
```

This package has no affine-chart claim. It should expose only transparent
projections plus the covering-sieve pullback supplied by
`groth_topology_pullback`. For a chart arrow `f : U -> X`, the internally
derived overlap cover is `f^*R`; pairwise overlap candidates are members of
that pulled-back sieve. Repeated pullback is the future Čech direction.

This first source must:

- be rule-free;
- reuse `ReflectiveCommRingedSite`, `Sieve`, `Covers`, and
  `groth_topology_pullback`;
- add no external naturality or cocycle field;
- not call the result a scheme or an affine atlas;
- not claim finiteness merely because a cover is selected; and
- include a focused reviewer showing constructor/projection computation and
  pulled-back coverhood.

### CS-02 — Finite selected-cover presentation

Audit whether `FiniteFamily` plus a supplied covering sieve can express a
finite subcover without inventing a second sieve-generation calculus. The
current affine consumer should continue to use
`CommRingZariskiCoverFamily` as its source of truth. A generic finite cover
interface is promoted only with a non-affine consumer and a precise statement
that the selected finite family generates or covers, not merely that its
members lie in a covering sieve.

### CS-03 — Affine chart realization owner probe

For an actual member `f : U -> X`, determine the correct whole comparison
between the ambient restriction/slice at `U` and an affine presentation
associated to a ring `R_U`. Required questions include:

1. whether `Slice_cat(K,U)` and the existing pullback owners supply the right
   ambient restriction category;
2. how the topology and reflective structure sheaf restrict;
3. whether a reusable pullback of `ReflectiveCommRingedSite` is needed;
4. whether chart affineness should be a whole `DefIso`, a category-level
   `OmegaEquivAlong`, or a structured bundle of both; and
5. which small/big-site comparison is genuinely consumed.

Do not promote a chart record that merely labels `U` with an unrelated ring
and `AffineSchemePresentation(R_U)`. The comparison with the ambient
restriction is the semantic content of affineness.

### CS-04 — Global-first finite-qcqs `SchemePresentation`

After CS-02/CS-03 are concrete, package an existing global object with:

- a reflective CommRinged global presentation;
- the narrow point-free locally-ringed/support capability actually required;
- a selected finite covering atlas; and
- an affine realization for every selected chart.

Overlap restrictions and cocycle laws are derived from the global object,
pullback/restriction, whole chart comparisons, and generic composition. Named
adapters may expose them for consumers, but the record must not store a second
componentwise coherence calculus.

### CS-05 — First non-affine computational consumer

Two possible consumers are deliberately separated:

1. a global object supplied with two affine charts, testing the global-first
   presentation without constructing the object; and
2. an atlas-first gluing constructor, eventually testing a projective-line
   style example.

The first is the nearer MVP. The second requires a realization/universal
property and should not block the first.

### CS-06 — Later semantic comparisons

Later, independently gated work includes:

- point-free invertibility-support versus ordinary local-stalk comparison;
- small-site restriction and principal-open basis comparison;
- a representation-independent `Scheme_cat` and `Spec_func`;
- realization/forgetful comparison for presented schemes;
- finite open-gluing effectivity; and
- a Zeuner-style equivalence between suitable geometric and functorial qcqs
  scheme categories.

Constructed double-plus or categorical-HIT sheafification remains a separate
research program and is not an MVP prerequisite because the current reflector
interface keeps the assumption explicit.

## 10. Feasibility Assessment

| Boundary | Feasibility | Principal uncertainty |
| --- | --- | --- |
| Global ringed object plus selected covering sieve and pulled-back covers | High | Only exact ergonomic shape and naming. |
| Global-first assumption-explicit affine atlas | Good | Honest whole restriction/pullback comparison to each affine chart. |
| Finite-qcqs presentation | Good with a consumer | Generic finite-cover generation must not duplicate the existing algebraic family owner. |
| Supplied global non-affine example | Good | Selecting a mathematically meaningful ambient object before `Scheme_cat` exists. |
| Constructive two-affine gluing | Moderate | Global realization and universal property, not overlap algebra itself. |
| Point-free locally-ringed support interface | Good | Correct support laws in the present ordinary-sieve/site representation. |
| Stalk-local-ring comparison | Moderate/research | Stalk/point infrastructure and constructive hypotheses. |
| Small-site restriction/basis comparison | Moderate | Exact basis and topology transport owners. |
| Representation-independent category of schemes | Research-grade but plausible | Morphism representation, locally-ringed structure, and comparison with presentations. |
| Unrestricted atlas effectivity or general sheafification construction | Research-grade | Descent/localization/HIT infrastructure and scope. |

The original computational-schemes direction remains feasible. The main risk
is no longer basic opens, localization, topology, or affine glue; those have
working internal owners. The immediate architectural risk is attaching an
affine presentation to an ambient chart without losing the whole
restriction/sheaf comparison or smuggling it into an opaque name.

## 11. Decision Ledger

- **CS-D-001 — Living authority:** this continuation plan is updated as probes
  change the design. Active source remains authoritative. The parent PSSS
  plan retains history.
- **CS-D-002 — Locality split:** sheaf descent, locally-ringed support, and
  basic-open coordinate-localization locality remain separate classifiers and
  claims.
- **CS-D-003 — Global-first default:** an ordinary scheme presentation starts
  from a global object; overlaps and cocycles are derived. Atlas-first gluing
  is a separate constructor boundary.
- **CS-D-004 — Whole internal coherence:** no external object-only naturality,
  restriction-square, or cocycle family may replace existing whole owners.
- **CS-D-005 — Effectivity terminology:** effectivity means global
  realization of descent data; it is not synonymous with increasing atlas
  arity.
- **CS-D-006 — Finite qcqs scope:** finite selected affine covers are the
  near-term scope. Unrestricted atlases are not a hidden requirement.
- **CS-D-007 — Site correction:** replace *small/big-site equivalence* with
  scoped restriction, affine-basis, and representation-comparison tasks.
- **CS-D-008 — Presentation separation:** `SchemePresentation(X)` is a
  certificate over a semantic object; a later `PresentedScheme_cat` may total
  those fibres without forcing scheme morphisms to preserve atlases.
- **CS-D-009 — First promoted substrate:** implement the rule-free global
  reflective ringed-space cover package and derived pullback coverage before
  fixing any public non-affine scheme record.
- **CS-D-010 — No unrelated affine labels:** a chart is not affine merely
  because it is paired with an `AffineSchemePresentation`; an honest whole
  comparison with the ambient restriction is mandatory.
- **CS-D-011 — Historical scope:** `cartierSolution16.lp.txt` is design
  evidence and computational motivation, not a mathematical authority.
- **CS-D-012 — Git boundary:** local green checkpoint commits are allowed on
  the dedicated goal branch after proportional SOP validation and ledger
  synchronization. Push, merge, rebase, amend, reset, publication, cleanup,
  branch deletion, and worktree removal are not authorized.

These decisions supersede the conflicting portions of PSSS-D-117, especially
its proposal to store whole overlap/cocycle witnesses in the ordinary
global-first record and its phrase *small/big-site equivalence*.

## 12. Side-Task Ledger

| ID | Task | Status | Gate |
| --- | --- | --- | --- |
| CS-00 | Consolidate affine checkpoint and corrected architecture | Complete; dedicated plan, parent supersession note, and index route added | This report and index routing |
| CS-01 | Global reflective ringed object, covering sieve, and internally derived pullback cover | Implementation complete and proportionally green; local checkpoint pending | Checkpointed PSSS-11c and existing site pullback owner |
| CS-02 | Point-free invertibility-support/local-ring capability audit | Proposed | Concrete scheme consumer or theorem statement |
| CS-03 | Generic finite-cover presentation audit | Proposed | Non-affine finite-atlas consumer |
| CS-04 | Pullback/restriction of reflective ringed sites | Required owner probe | CS-01 plus existing slice, pullback, topology, and sheaf owners |
| CS-05 | Honest affine chart realization over an ambient restriction | Blocked on design probe, not implementation difficulty | CS-04 and affine checkpoint |
| CS-06 | Global-first finite-qcqs `SchemePresentation(X)` | Proposed | CS-02/CS-03/CS-05 contracts |
| CS-07 | Supplied global two-chart non-affine reviewer | Proposed first non-affine consumer | CS-06 |
| CS-08 | Atlas-first two-affine gluing constructor | Later | Whole open-overlap input plus realization/universal property |
| CS-09 | Small-site restriction and affine/principal-open basis comparison | Later | Concrete small-site consumer |
| CS-10 | Semantic `Scheme_cat`, `Spec_func`, and presented-scheme realization | Research continuation | Stable object/morphism interfaces and CS-06 |
| CS-11 | Point-free support versus stalk-local-ring comparison | Later theorem | Support capability and suitable point/stalk infrastructure |
| CS-12 | Constructed categorical-HIT/double-plus sheafification | Independent research | Local-object classifier, categorical localization, and left-exactness hypotheses |

## 13. CS-01 Success Criteria

CS-01 is green when:

1. one rule-free standard-library module defines the transparent global
   reflective ringed-space cover package;
2. its constructor and projections compute through existing Sigma owners;
3. the selected covering evidence uses exactly the topology projected from
   the retained `ReflectiveCommRingedSite`;
4. pullback of the selected covering sieve along any arrow is proved covering
   solely by `groth_topology_pullback`;
5. a chart/member view, if promoted, reuses the existing restriction-total and
   sieve-membership owners;
6. no affine, finite, locally-ringed, scheme, gluing-effectivity, or cocycle
   claim is made;
7. no rewrite, unification rule, external naturality field, topology law, or
   duplicate pullback owner is added;
8. focused source/reviewer checks and exact warning comparison are green;
9. strict rule audit, catalog/health routing, report index, Foundations, SOP,
   and syntax are updated only in proportion to the promoted surface; and
10. the exact staged diff contains no concurrent-worktree or unrelated user
    changes before a local checkpoint.

### 13.1 CS-01 implementation and validation record — 2026-08-03

The promoted rule-free module
`emdash3_2_commutative_algebra_ringed_space_covers.lp` is 240 lines and
declares 17 symbols, zero rewrite rules, and zero unification rules. It imports
only `emdash3_2_ringed_sites` and adds the transparent package
`ReflectiveCommRingedSpaceCover(K)` with:

- one retained `ReflectiveCommRingedSite(K)`;
- one distinguished whole object of `K`;
- one selected sieve on that object;
- covering evidence in exactly the retained topology;
- the underlying included CommRing-valued presheaf as a derived projection;
- pullback of the selected sieve along an arbitrary arrow; and
- covering of that pullback derived solely by the existing
  `groth_topology_pullback` owner.

The companion chart view is the restriction-total member of the selected
sieve. Its domain, arrow, membership witness, and pulled-back-cover
observation are projections or existing generic consequences, not duplicated
atlas data. In particular, CS-01 adds no affine label, scheme classifier,
local-ring assertion, gluing/effectivity claim, overlap field, cocycle field,
external naturality equation, topology law, or new computation rule.

The reviewer `examples/commutative_ring_ringed_space_covers.lp` is 114 lines
with eight typed assertions. It checks constructor/projection beta reduction,
the underlying-presheaf route, pullback coverhood, and literal chart domain,
arrow, membership, and chart-pullback computations.

Focused validation is green:

- the source and reviewer pass quiet checks at 6.292 seconds and 6.220
  seconds respectively in the recorded health run;
- their warning-enabled checks inherit exactly the existing 1,179 warnings
  (1,020 unjoinable-rule and 159 pattern warnings), with no warning owned by
  either changed file;
- strict rule-LHS audit reports zero unreviewed rules and 52 annotations over
  32 intentional rule groups;
- catalog generation/checking, health-report validation, report-header and
  active-reference lint, source-TOC validation, check-metrics unit tests, and
  whitespace checks pass; and
- the 60-second health integration gate is green for all 110 registered
  targets. It reused 109 exact-snapshot successes and reran only the unchanged
  central `emdash3_2_checks.lp`, which passed in 58.519 seconds. The recorded
  source-metrics snapshot is
  `sha256:d20e1a986f3903490706b5a655d0cb651ff78309155d749dd11018e20589e7df`
  and the check-content snapshot is
  `sha256:36bd77af8a5f61b6004b7d01f9b6f1a77bc16b9e5aa5e08bf4b0ef06e7eacdf9`.

No full CI or duplicate aggregate was run: registering a new checked source
and reviewer required one health-snapshot integration boundary, and its saved
resume state prevented replay of the 109 unchanged successful targets after
the central diagnostics target first narrowly exceeded its fixed timeout.

## 14. Validation And Checkpoint Contract

For every bounded source tranche:

1. inspect all worktrees and exact staged/unstaged state;
2. relocate owners and consumers with `rg`;
3. state the mathematical normal form and non-claims in the living plan;
4. probe the candidate under the 60-second Lambdapi limit;
5. use typed assertions for every new public projection/comparison;
6. compare warning output exactly for changed targets;
7. run strict rule audit for any source change, even when the intended module
   is rule-free;
8. synchronize the source registry, reviewer, catalog, health snapshot, and
   affected authority prose;
9. avoid a long aggregate when focused and recent unchanged evidence provides
   the same boundary; and
10. checkpoint locally only after the bounded tranche and its ledger are
    green.

Recent aggregate evidence for the unchanged affine baseline should be carried
forward. A full repository or kernel aggregate is reserved for a genuine
integration boundary rather than rerun for reassurance.

## 15. Persistent Goal Launch Objective

The successor persistent goal should use an objective at this level of
specificity:

> In the dedicated
> `/home/user1/emdash1-presheaves-sites-schemes` worktree on
> `goal/presheaves-sites-schemes-v3.2`, continue the computational-schemes
> program from clean checkpoint `4427b99` by treating
> `REPORT_EMDASH_V3_2_COMPUTATIONAL_SCHEMES_CONTINUATION_PLAN_2026-08-03.md`
> as the living implementation, decision, validation, and recovery ledger.
> Execute its next ready bounded tranche under the active nested Lambdapi SOP,
> beginning with the global-first rule-free selected-cover substrate and its
> internally derived pullback coverage. Update the plan whenever probes or
> consumers refine the architecture; preserve the separation of the three
> locality notions, global-first presentation from atlas-first gluing,
> semantic schemes from computational presentations, and small/big site
> restriction from affine-basis equivalence. Keep all functoriality,
> naturality, overlap, and cocycle propagation at whole internal owners; do
> not promote unrelated affine labels, opaque theorem names, external
> component coherence, or overclaimed scheme/local-ring interfaces. Reuse
> recent green evidence for unchanged boundaries and avoid long aggregates
> unless a real integration gate requires one. Create only authorized local
> green checkpoint commits after synchronized proportional validation. Do not
> push, merge, publish, rebase, amend, reset, rewrite history, clean up
> worktrees, or interfere with concurrent branches.

The plan, not the launch sentence, owns the evolving task order and detailed
acceptance gates.
