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
| `scheme_slice_ascheme` | future affine realization of a restriction/slice chart of a global ringed object | Still open. The historical term itself assumed `slice_site`, a continuous adjoint site-morphism package, pullback of sheaves, and compatibility of that pullback with sheafification/glue; it did not construct those capabilities. The v3.2 successor requires an honest whole comparison between the ambient chart restriction and an affine presentation without hiding those assumptions. |

The current fixed-forward equivalence corresponds to the basic-open/qcqs
formula

```text
O(D(s)) ~= O(U)[1/s].
```

It is the computational center of the old `mod_loc_elim` idea and corresponds
to Zeuner's qcqs localization lemma. It is not, by itself, the definition that
all stalks are local rings.

### 3.1 Historical slice/glue factorization

The historical experiment did address its own question *how does glue in a
slice relate to glue in the base?*, but not by deriving everything from its
primitive `glue`. It assumed four distinct layers:

1. `slice_site(S_site,U)` supplied a site on the slice category;
2. `site_morph` retained a left/right adjoint pair between the slice and base
   categories together with continuity data in both relevant directions;
3. `site_morph_pullback_smod` supplied pullback of sheaf objects, with rules
   exposing its underlying presheaf and comparing pullback of a sheafification
   with sheafification after presheaf pullback; and
4. `site_morph_mod_adjL`/`site_morph_mod_adjR` related adjunction transposition
   and `glue` across that site morphism.

`ascheme_slice_ascheme` and `scheme_slice_ascheme` then assembled the slice
affine interface from that supplied slice site, pulled-back structure sheaf,
pulled-back ring structure, and pulled-back localization interface. Thus the
historical file contains a useful architectural factorization, but its
`slice_site`, site-morphism evidence, and sheaf transport are opaque
capabilities marked for review. It is not a construction or proof of the
induced slice topology.

The current CS-04 package intentionally implements only the part that is
already canonical in v3.2: the whole slice-domain functor, whole presheaf
restriction, and an explicit supplied reflective-slice presentation with a
whole `DefIso`. It is therefore more honest about assumptions and stronger
about internal functorial ownership, but it does **not** yet recover the full
relation asserted by the historical site-morphism package. In particular, a
whole topology/base-change relation is still absent.

The Stacks Project result cited by the historical source compares
sheafification before and after presheaf pullback under the appropriate
cocontinuity/adjoint hypotheses. Its v3.2 analogue should be a whole
functorial comparison or mate/Beck--Chevalley capability, not a global rewrite
between opaque sheaf objects. The precise `DefIso` versus
`OmegaEquivAlong`/whole-transformation representation remains consumer- and
normal-form-gated. *Locally exact square* is a semantic criterion for proving
that this whole mate is invertible; it is not a proposal to store explicit
commutative-square equations in a scheme or site record.

### 3.2 What a categorical-HIT sheafification would and would not solve

The phrase *categorical HIT* in this plan has the precise research meaning
recorded by PSSS-05d and PSSS-D-114.  For a site `(K,T)`, select a whole class
`W_T` of covering-sieve, Cech, or higher-descent maps in the whole presheaf
category and freely localize that category at `W_T`.  The categorical
construction adds the required fillers, equalities, and higher coherences and
has an internal eliminator/universal property against local targets.  Its
whole reflector, object and arrow action, unit, and naturality are then owned
by existing categorical owners.  It does **not** mean a direct transcription
of a HoTT HIT into Lambdapi, nor does it commit the stable consumer interface
to external point/path constructors or naturality equations.

Three notions must therefore remain distinct:

| Phrase | Role in this program | Non-claim |
| --- | --- | --- |
| HoTT HIT | General object/type presentation by point, path, and higher constructors. | It is not by itself a sheafification construction or the selected emdash interface. |
| Tabareau's `OT` HIT | One auxiliary higher-inductive coequalizer used inside the iterated-kernel-pair proof of separated reflection. | It is neither the whole Tabareau sheafification nor a declaration template for v3.2. |
| Emdash categorical HIT | Free localization of the **whole presheaf category** at selected descent maps, characterized by an internal eliminator/universal property into local targets. | It does not expose object-level point/path constructors, external naturality fields, or component coherence to scheme consumers. |

The adjective *categorical* thus names the level and universal property of the
construction, not a direct categorical spelling of Tabareau's `OT`. The
PSSS-05d observation is specifically that functorial type theory may formulate
the desired localization directly at whole category/functor owners. The
existing `WalkingEnd_cat` demonstrates one contextual categorical eliminator,
but it is not yet generic localization, coequalizer, telescope-colimit, or
higher-coherence infrastructure.

Quirin--Tabareau construct Lawvere--Tierney sheafification from a left-exact
modality on propositions by an h-level induction. Their construction has two
steps:

1. a separated reflection, whose universality uses an image, iterated kernel
   pairs, a mapping telescope, and the higher-inductive `OT` coequalizer; and
2. closure of that separated object to obtain a sheaf, followed by proofs of
   reflective universality, modal closure, compatibility across h-levels, and
   left exactness.

Tabareau's HIT is therefore an auxiliary higher-inductive coequalizer inside
the separated-reflection proof, not one monolithic *sheafification HIT* and
not the proposed emdash categorical localization.  This is important design
evidence: a genuine constructed sheafification is
not merely a primitive object former with one beta rule. Its public contract
includes a local/sheaf classifier, a whole reflector and unit, a universal
mapping property, functoriality, idempotence/reflection, and the finite-limit
or left-exactness structure consumed by geometric base change.

It is not, however, a drop-in implementation of the current library. The paper
starts from a Lawvere--Tierney modality on `HProp`; v3.2 starts from an
ordinary-sieve `GrothTopology(K)` and currently wants CommRing-valued
presheaves. A usable construction therefore also needs:

- a bridge from covering sieves to local equivalences/dense maps or an
  equivalent internal sheaf predicate;
- a categorical localization/HIT whose local objects form a whole sheaf
  category, or a proved comparison with the existing rigid `Sheaf_cat`;
- a lift from the set/type-valued reflector to CommRing-valued objects that
  preserves their operations and laws; and
- a separate base-change theorem for the slice projection and its induced
  topology.

Accordingly, the PSSS-05d free categorical-localization construction can
eventually *instantiate* and strengthen `SheafificationCapability` for a fixed
selected site. It does not by itself select the slice topology, establish
continuity of the slice/base functors, or prove the required sheafification
base-change comparison. Those remain separate
geometric-morphism/Beck--Chevalley obligations even when the reflector is
constructed. Tabareau's `OT`, h-level induction, and modal-closure staging
remain semantic comparison points, not the chosen emdash syntax or reduction
architecture.

The historical comment that the Lawvere--Tierney development is merely
semantic, or that its density definition is flawed, is not adopted as a v3.2
decision. The paper supplies an actual HIT-based reflective construction, but
its propositional computation and its Lawvere--Tierney/h-level scope differ
from the definitional and category-valued computation sought here. Any
relative-density refinement must be justified by a concrete v3.2 consumer
rather than inherited from the historical comment.

### 3.3 Site-morphism literature route

The following literature is routed by the contract it may clarify rather than
treated as one undifferentiated prerequisite list:

| Reference | Relevance to this plan | Priority |
| --- | --- | --- |
| Caramello--Osmond, *Morphisms and comorphisms of sites I -- Double categories of sites* (`arXiv:2505.08766`) | Separates morphisms and comorphisms of sites, packages sheafification as a double functor, and characterizes *locally exact* squares whose Beck--Chevalley cell becomes invertible after sheafification. This is the closest modern semantic guide to the historical `site_morph_mod_adjL`/glue interaction. | Primary bounded CS-05a audit. |
| Osmond--Caramello, *Morphisms and comorphisms of sites II -- Distributors of sites* (`arXiv:2507.20932`) | Generalizes strict site functors to distributors and relates continuous distributors to geometric morphisms. Emdash's profunctor infrastructure makes this architecturally plausible if an affine chart comparison is genuinely relational rather than functorial. | Consumer-gated fallback; do not replace an adequate whole functor by a distributor merely for generality. |
| Caramello, *Fibred sites and existential toposes* (`arXiv:2212.11693`) | Provides a relative/fibred setting potentially suited to a family of slices and relative schemes. | Later CS-06/CS-10 comparison, after one chart works. |
| Bartoli--Caramello, *On morphisms of relative toposes* (`arXiv:2310.20691`) | Studies site functors inducing relative geometric morphisms and a relative Diaconescu theorem. | Later relative/family semantics; not needed for the immediate whole restriction. |
| Caramello--Zanfa, *On the dependent product in toposes* (`arXiv:1908.08488`) | Gives an explicit and site-theoretic dependent product. It may inform future right-adjoint/`Pi` and dependent slice infrastructure. | Separate dependent-product task unless CS-05 produces a concrete right-adjoint consumer. |

The initial inspection of the first paper changes one architectural emphasis:
the sought comparison should not be called generic *naturality of glue*.
It is more precisely a sheafified Beck--Chevalley or locally-exact-square
condition between extension/restriction operations. The semantic development
may formulate and prove local exactness of a site square, but the computational
interface should expose the resulting whole sheaf-restriction functor and
invertible whole mate. A natural transformation is already a whole internal
emdash object, so its naturality and all evaluated component squares remain at
the generic transformation owners. Neither the site record nor each scheme
presentation should carry a family of external component equations.

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

### CS-02 — Point-free locally-ringed-support audit

Audit the exact support laws needed beyond the existing proposition-valued
invertibility sieve. This remains consumer-gated: coordinate-localization
locality is already implemented but is not silently reclassified as a
locally-ringed condition, and stalk construction remains a later comparison
layer. Promote only the narrow internal support capability consumed by the
first scheme presentation.

### CS-03 — Finite selected-cover presentation

Audit whether `FiniteFamily` plus a supplied covering sieve can express a
finite subcover without inventing a second sieve-generation calculus. The
current affine consumer should continue to use
`CommRingZariskiCoverFamily` as its source of truth. A generic finite cover
interface is promoted only with a non-affine consumer and a precise statement
that the selected finite family generates or covers, not merely that its
members lie in a covering sieve.

### CS-04 — Whole ambient chart-slice restriction

For an actual member `f : U -> X`, the owner probe separates three layers
that the earlier wording had conflated:

1. the conventional whole domain functor `Slice_cat(K,U) -> K`;
2. the whole ambient structure presheaf restricted along that functor; and
3. transport or supply of topology, sheaf category, reflector, and selected
   sheaf object on the slice.

The first two layers are constructible now. `Into_restr_cat(K,U)` is the Sigma
total over `K^op`, so `Sigma_proj1_func` supplies its whole projection and
opposite gives the conventional slice-domain functor. Ordinary whole functor
composition then constructs

```text
O_X|_U = O_X o Op(slice_domain_U)
        : CommRingPsh(Slice_cat(K,U)).
```

Generic composition owns both object and arrow action. At an arbitrary
encoded-Sigma object, the stable endpoint remains evaluation of the whole
domain functor; at a literal `(V -> U)` it computes to `V`. No global Sigma
eta/projection rewrite is justified merely to identify those presentations.

The third layer is not constructible from the current public owners:
`GrothTopology(K)` has no site-functor transport operation, and `Sheaf_cat`
is intentionally opaque with no pullback theorem for its supplied reflector.
The bounded assumption-explicit interface therefore retains a supplied
`ReflectiveCommRingedSite(Slice_cat(K,U))` and one whole `DefIso` from its
included structure presheaf to `O_X|_U`. This is a computational presentation
of a reflective slice, not a theorem that its topology or reflector was
induced from the ambient site. A future induced-topology/continuous-site
capability must state that relation honestly if a consumer requires it.

### CS-05 — Honest affine chart realization

With the actual ambient slice presheaf available, determine the remaining
whole comparison with an affine presentation associated to a ring `R_U`.
Required questions now sharpen to:

1. which base-category/site functor or equivalence compares
   `Slice_cat(K,U)` with `AffineSpecBigSlice_cat(R_U)`;
2. which topology-compatibility contract is genuinely needed;
3. whether affineness should combine a base/site equivalence with a whole
   `DefIso`, a category-level `OmegaEquivAlong`, or a structured bundle of
   both; and
4. which small/big-site comparison is actually consumed.

The first bounded substep, CS-05a, audits the historical four-layer package
against the morphism/comorphism distinction and locally exact squares. It
must determine whether the slice projection and its right adjoint form:

- an ordinary site morphism/comorphism pair sufficient for the consumer;
- a whole sheafified Beck--Chevalley/mate capability, semantically justified
  by a locally exact site square, that supplies the required glue/base-change
  law without storing component square equations; or
- only in a genuinely nonrepresentable case, a distributor of sites.

CS-05a is a contract and owner-position audit, not authorization to port the
historical rewrite rules. CS-05b may promote the smallest whole capability
selected by an actual affine-chart assertion. Construction of a general HIT
reflector is brought forward only if that consumer is blocked specifically by
the absence of a constructed fixed-site `SheafificationCapability`; it is not
used to bypass the topology or base-change questions.

Do not promote a chart record that merely labels `U` with an unrelated ring
and `AffineSchemePresentation(R_U)`. The comparison with the actual ambient
restriction is the semantic content of affineness.

### CS-06 — Global-first finite-qcqs `SchemePresentation`

After CS-02/CS-03/CS-05 are concrete, package an existing global object with:

- a reflective CommRinged global presentation;
- the narrow point-free locally-ringed/support capability actually required;
- a selected finite covering atlas; and
- an affine realization for every selected chart.

Overlap restrictions and cocycle laws are derived from the global object,
pullback/restriction, whole chart comparisons, and generic composition. Named
adapters may expose them for consumers, but the record must not store a second
componentwise coherence calculus.

### CS-07 — First non-affine computational consumer

Two possible consumers are deliberately separated:

1. a global object supplied with two affine charts, testing the global-first
   presentation without constructing the object; and
2. an atlas-first gluing constructor, eventually testing a projective-line
   style example.

The first is the nearer MVP. The second requires a realization/universal
property and should not block the first.

### CS-08 and later — Construction and semantic comparisons

Later, independently gated work includes:

- atlas-first two-affine gluing and its realization/universal property;
- point-free invertibility-support versus ordinary local-stalk comparison;
- small-site restriction and principal-open basis comparison;
- a representation-independent `Scheme_cat` and `Spec_func`;
- realization/forgetful comparison for presented schemes;
- finite open-gluing effectivity; and
- a Zeuner-style equivalence between suitable geometric and functorial qcqs
  scheme categories.

Constructed double-plus or categorical-HIT sheafification remains a separable
research program and is not presently an MVP prerequisite because the current
reflector interface keeps the assumption explicit. Its contract audit may be
brought forward during CS-05, but implementation is split into: topology to
local-object data, a left-exact reflective localization, realization of the
current sheaf/capability facade, a CommRing-valued lift, and an independent
slice/base-change theorem. Completing only the HIT object former would not
close CS-05.

## 10. Feasibility Assessment

| Boundary | Feasibility | Principal uncertainty |
| --- | --- | --- |
| Global ringed object plus selected covering sieve and pulled-back covers | High | Only exact ergonomic shape and naming. |
| Whole ambient presheaf on the actual chart slice | Implemented | No remaining object/arrow-action gap; arbitrary Sigma endpoints stay at the whole domain functor. |
| Supplied reflective slice with a computing ambient comparison | Implemented assumption-explicitly | It deliberately supplies, rather than derives, slice topology and reflection. |
| Induced slice topology and reflective-sheaf transport | Moderate and consumer-gated | Honest site-functor/topology compatibility and a sheaf/reflector transport theorem are absent; the historical file supplied both. |
| Whole sheafified Beck--Chevalley/locally-exact comparison | Moderate, with strong semantic guidance | Exact v3.2 owner and orientation must be selected by the affine-chart consumer; no component-square encoding is acceptable. |
| Global-first assumption-explicit affine atlas | Good | Honest whole restriction/pullback comparison to each affine chart. |
| Finite-qcqs presentation | Good with a consumer | Generic finite-cover generation must not duplicate the existing algebraic family owner. |
| Supplied global non-affine example | Good | Selecting a mathematically meaningful ambient object before `Scheme_cat` exists. |
| Constructive two-affine gluing | Moderate | Global realization and universal property, not overlap algebra itself. |
| Point-free locally-ringed support interface | Good | Correct support laws in the present ordinary-sieve/site representation. |
| Stalk-local-ring comparison | Moderate/research | Stalk/point infrastructure and constructive hypotheses. |
| Small-site restriction/basis comparison | Moderate | Exact basis and topology transport owners. |
| Representation-independent category of schemes | Research-grade but plausible | Morphism representation, locally-ringed structure, and comparison with presentations. |
| Fixed-site categorical-HIT sheafification construction | Research-grade but factorable | Topology-to-local-equivalence bridge, categorical localization/HIT, rigid `Sheaf_cat` realization, CommRing lift, and left exactness. |
| Unrestricted atlas effectivity | Research-grade | Descent/localization infrastructure and scope. |

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
- **CS-D-013 — Restriction split:** the whole slice-domain functor and ambient
  CommRing-presheaf restriction are internally constructible and should
  compute through generic Sigma/functor owners. Topology and reflective-sheaf
  transport are separate capabilities; until they are constructed, a
  `SuppliedReflectiveCommRingedSlicePresentation` visibly supplies one slice
  site and a whole computational `DefIso` without claiming induced topology.
  Arbitrary encoded-Sigma objects remain aligned with whole functor
  evaluation; only literal restriction arrows are promised to reduce to
  their first projection.
- **CS-D-014 — Historical slice/glue factorization:** the old
  `scheme_slice_ascheme` is evidence for four separate capabilities--slice
  topology, adjoint site morphism/comorphism, sheaf pullback, and a
  sheafification/glue base-change comparison--not evidence that primitive
  `glue` constructs a slice theory. A v3.2 successor must retain this
  separation and express the comparison at whole owners rather than porting
  its rewrites.
- **CS-D-015 — Native categorical-HIT sequencing:** a native emdash
  categorical HIT means the PSSS-05d/PSSS-D-114 free localization of the
  whole presheaf category at a selected class of covering-sieve, Cech, or
  higher-descent maps, with an internal eliminator into local targets.  Such a
  construction may instantiate a fixed-site `SheafificationCapability`,
  preferably with a separately stated left-exact localization contract. Its
  whole object action, arrow action, eliminator, and computation belong to
  categorical owners. Tabareau's HoTT HIT is an auxiliary coequalizer in one
  separated-reflection proof and is semantic evidence rather than an
  implementation template or a monolithic sheafification HIT. The categorical
  localization neither chooses the induced slice topology nor proves the
  sheafified Beck--Chevalley law. Bring its implementation forward only when a
  concrete CS-05/CS-07 consumer is blocked specifically on reflector
  construction.
- **CS-D-016 — Site-comparison vocabulary:** use
  morphism/comorphism/locally-exact-square language during CS-05a. A
  distributor is consumer-gated for a comparison that cannot be represented
  adequately by whole functors. No new external component naturality or
  commutative-square family follows from adopting the double-categorical
  view.
- **CS-D-017 — Semantic criterion versus computational interface:** local
  exactness is a metatheoretic or construction-time condition showing that a
  sheafified mate is invertible. The public kernel capability retains the
  selected whole functors and that one whole invertible transformation or
  comparison. Generic transfor action owns its naturality; ordinary scheme
  records do not retain local-exactness derivations or component equations.
- **CS-D-018 — First affine-basis consumer strength:** CS-05b selects a whole
  sheaf-restriction functor whose inclusion comparison is one whole
  `IsoEvidence`, a category-level `OmegaEquivAlong Cat_cat` witnessing the
  basis comparison, and one direct whole presheaf `DefIso` joining the actual
  ambient restriction to the existing computing affine presentation.  The
  sheafification/glue Beck--Chevalley mate from the CS-05a probe remains a
  separate later capability because no first chart consumer transports
  generic glue through it.  Local exactness may prove such a mate later, but
  neither it nor component square equations are fields of CS-05b.

These decisions supersede the conflicting portions of PSSS-D-117, especially
its proposal to store whole overlap/cocycle witnesses in the ordinary
global-first record and its phrase *small/big-site equivalence*.

## 12. Side-Task Ledger

| ID | Task | Status | Gate |
| --- | --- | --- | --- |
| CS-00 | Consolidate affine checkpoint and corrected architecture | Complete; dedicated plan, parent supersession note, and index route added | This report and index routing |
| CS-01 | Global reflective ringed object, covering sieve, and internally derived pullback cover | Complete and locally checkpointed at `a5aebcf` | Checkpointed PSSS-11c and existing site pullback owner |
| CS-02 | Point-free invertibility-support/local-ring capability audit | Proposed | Concrete scheme consumer or theorem statement |
| CS-03 | Generic finite-cover presentation audit | Proposed | Non-affine finite-atlas consumer |
| CS-04 | Whole ambient chart-slice restriction and supplied reflective-slice presentation | Complete and locally checkpointed at `7d63a90`; induced topology/reflector transport remains a separate CS-05 input question | CS-01 plus existing Sigma, opposite, functor-composition, and reflective-site owners |
| CS-05 | Honest affine chart realization over an ambient restriction | Complete through CS-05b's whole semantic/computational package; locally checkpointed at `b4fca9c`; stronger sheafification base change remains separately consumer-gated | CS-04 and affine checkpoint |
| CS-05a | Historical site-morphism and modern morphism/comorphism/locally-exact contract audit | Complete as a contract audit; stronger sheafification base change remains separately consumer-gated | CS-04 plus a concrete affine-chart target |
| CS-05b | Whole sheaf-basis comparison plus computational ambient-affine realization | Promoted as two transparent rule-free modules; focused/exact-warning/audit/catalog green, 115/116 exact-content health targets current-green, unchanged central aggregate carried forward under the proportional-validation policy; local checkpoint `b4fca9c` | CS-D-018 and CS-04 |
| CS-06 | Global-first finite-qcqs `SchemePresentation(X)` | Proposed | CS-02/CS-03/CS-05 contracts |
| CS-07 | Supplied global two-chart non-affine reviewer | Proposed first non-affine consumer | CS-06 |
| CS-08 | Atlas-first two-affine gluing constructor | Later | Whole open-overlap input plus realization/universal property |
| CS-09 | Small-site restriction and affine/principal-open basis comparison | Later | Concrete small-site consumer |
| CS-10 | Semantic `Scheme_cat`, `Spec_func`, and presented-scheme realization | Research continuation | Stable object/morphism interfaces and CS-06 |
| CS-11 | Point-free support versus stalk-local-ring comparison | Later theorem | Support capability and suitable point/stalk infrastructure |
| CS-12 | Constructed native categorical-HIT/localization sheafification | Factorized PSSS-05d/PSSS-D-114 research; free localization at whole descent maps is the emdash candidate, while Tabareau's auxiliary HoTT HIT is semantic evidence and implementation remains consumer-gated | Topology-to-local-object bridge, categorical localization, rigid-facade realization, CommRing lift, and left-exactness |
| CS-12b | Slice/base-change and sheafified Beck--Chevalley theorem | Separate from constructing the reflector | Induced slice topology plus selected site morphism/comorphism or locally exact square |

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
The complete bounded source, reviewer, authority, registry, health, and plan
boundary is locally checkpointed as `a5aebcf` (`feat: add global ringed-space
covers`). No push, merge, history rewrite, publication, or worktree cleanup
was performed.

### 13.2 CS-04a implementation and validation record — 2026-08-03

The owner-position probe first established that the whole restriction total
projects by `Sigma_proj1_func` and its opposite is a well-typed conventional
slice-domain functor. It also measured two normal-form boundaries:

1. the object action of the functor-between-functor-categories
   `comp_cat_con_func` deliberately retains its stable
   `hom_precomp_along_fapp0` cut, so it is not the selected runtime endpoint
   for computing values of one concrete restricted presheaf; and
2. at an arbitrary encoded-Sigma object, whole `slice_domain_func` evaluation
   does not reduce to the separately defined `sigma_Fst` observation because
   the kernel intentionally has no global package eta. At a literal
   `Struct_sigma(V,f)`, both presentations compute to `V`.

The promoted design therefore defines `comm_ring_psh_pullback(F,O)` as the
whole ordinary composite `O o Op(F)`. This remains a full functor—generic
composition owns its values, structured arrow action, functoriality, and
naturality—while exposing the computational endpoint required by chart
consumers without a new rule or a duplicate component calculus.

The rule-free module
`emdash3_2_commutative_algebra_ringed_space_restrictions.lp` is 225 lines and
declares 13 symbols, zero rewrite rules, and zero unification rules. It adds:

- `into_restr_domain_func` and its opposite `slice_domain_func`;
- generic whole `comm_ring_psh_pullback`;
- the actual ambient structure presheaf on `Slice_cat(K,U)` and its selected
  cover-chart specialization; and
- `SuppliedReflectiveCommRingedSlicePresentation(A,U)`, retaining one supplied
  reflective CommRinged site on the actual slice and a whole `DefIso` from
  its included structure presheaf to the computing ambient restriction.

The last classifier is explicitly a computational presentation. It does not
assert that its selected topology, sheaf category, reflector, or sheaf object
was induced from the ambient site. The source adds no site continuity law,
topology transport, sheaf pullback theorem, affine label, locally-ringed
support, overlap/cocycle field, scheme record, or gluing constructor.

The reviewer `examples/commutative_ring_ringed_space_restrictions.lp` is 155
lines with 11 typed assertions. It checks literal restriction-total and slice
domain beta, whole CommRing-presheaf value and arrow action, the ambient-slice
value route, cover-chart specialization, supplied-package projections, and
both readable components of the whole `DefIso`.

The final owner probe is
`logs/probes/cs04_slice_ambient_psh-20260803-015049.log`. Quiet promoted
source/reviewer evidence is recorded at timestamp `20260803-015357`, and the
warning-enabled pair at `20260803-015437`.

Focused and proportional validation is green:

- quiet source and reviewer probes pass;
- warning-enabled source and reviewer probes inherit exactly the unchanged
  1,179 warnings (1,020 unjoinable-rule and 159 pattern warnings), with no
  warning location in either new file;
- strict rule-LHS audit reports zero unreviewed rules and 52 annotations over
  32 intentional rule groups;
- strict catalog generation/checking, report-header and active-reference
  lint, source-TOC validation, check-metrics unit tests, and whitespace checks
  pass; and
- the fresh 60-second health integration snapshot passes all 112 registered
  targets. The new source takes 9.336 seconds, its reviewer 12.255 seconds,
  and central `emdash3_2_checks.lp` 35.961 seconds. The recorded source-metrics
  snapshot is
  `sha256:dd89720090fd2867b550478b293fc27ee04d78c7715f3d94622addfac86137af`
  and the check-content snapshot is
  `sha256:4bd2f81e0d775e44b99f31cb97e37c0f8571279c95ece9c106a231679bd85631`.

No full CI or duplicate aggregate was run. The fresh health snapshot was the
single integration boundary required by registering one new source and one
new reviewer; subsequent work should carry it forward while those checked
contents remain unchanged.
The complete bounded source, reviewer, authority, registry, health, and plan
boundary is locally checkpointed as `7d63a90` (`feat: add whole ringed-space
slice restrictions`). No push, merge, history rewrite, publication, or
worktree cleanup was performed.

### 13.3 Post-checkpoint slice/glue and HIT sequencing audit — 2026-08-03

The explicit historical recovery requested by the user confirms that
`cartierSolution16.lp.txt` did not ask its generic `glue` primitive to invent
the slice semantics. Its `scheme_slice_ascheme` route depends on separately
declared `slice_site`, `site_morph`, `site_morph_pullback_smod`, and
sheafification/adjunction interaction rules. The same file marks the slice
site/morphism formulation for careful review. CS-04 therefore remains the
correct honest checkpoint: it computes the whole ambient presheaf restriction
and exposes a supplied reflective presentation, while making no false claim
that the supplied topology or reflector is induced.

The Quirin--Tabareau PDF and its layout extraction were checked together.
Section 5.2 defines sheafification in two stages; the higher-inductive `OT`
construction appears in the separated-reflection stage, while later
propositions establish the reflective subuniverse, modality, compatibility,
and left exactness. The visually inspected section boundaries and formulae on
PDF pages 20, 22, 26, and 27 agree with the extraction. This supports a future
categorical-HIT program but also shows why one primitive HIT declaration is
not an adequate sheafification contract.

An initial primary-source audit of Caramello--Osmond I and II identifies
locally exact squares and the sheafification double functor as the closest
modern formulation of the historical glue/base-change interaction.
Distributors of sites are a plausible later generalization because emdash
already has first-class profunctors, but no current consumer shows that the
strict functorial slice comparison is insufficient. Fibred/relative-site and
dependent-product references are routed to later family, relative-topos, or
`Pi` consumers rather than placed on the immediate critical path.

The resulting order is:

1. finish CS-05a by stating one concrete affine-chart comparison and selecting
   the minimal morphism/comorphism/locally-exact whole contract;
2. promote that contract only after an owner-position normal-form probe;
3. continue the assumption-explicit computational scheme MVP if that
   suffices; and
4. bring forward the categorical-HIT reflector construction only if the
   concrete consumer is blocked specifically on constructing the fixed-site
   reflector.

Even in the fourth case, induced slice topology and the sheafified
Beck--Chevalley/base-change theorem remain independent obligations. This audit
changes plan architecture and literature routing only; it adds no Lambdapi
symbol, rule, unifier, external naturality field, or new semantic claim.

### 13.4 CS-05a whole-interface probe — 2026-08-03

The focused probe `tmp/probes/cs05a_site_basis_contract.lp` passes under the
ordinary 60-second limit; its recorded log is
`logs/probes/cs05a_site_basis_contract-20260803-023839.log`. It establishes the
following typed architecture without promoting source:

1. the honest general orientation is a selected whole affine-basis functor
   `i : AffineSpecBigSlice_cat(R) -> Slice_cat(K,U)`, not an asserted
   equivalence of those underlying categories;
2. ordinary opposite-precomposition supplies a whole presheaf restriction
   functor between the corresponding functor categories;
3. a supplied sheaf-restriction functor can be related to presheaf
   restriction by one `IsoEvidence` between **whole composite functors**;
4. the historical sheafification-pullback rule has a well-typed successor as
   one `IsoEvidence` between the two whole sheafification/base-change
   composites;
5. comparison-lemma strength, when justified, is separately expressible as
   `OmegaEquivAlong Cat_cat` for the selected whole sheaf-restriction functor;
   and
6. independently of those semantic strengths, the actual ambient structure
   presheaf restricted along `i` keeps computing values and can be joined by
   one whole `DefIso` to an existing `AffineSchemePresentation(R)`. Composing
   with the affine scheme's existing `DefIso` yields a whole computational
   comparison directly to `affine_spec_coordinate_psh(R)`.

Items 3 and 4 contain transformations and inverse laws at the functor-category
owner. They are not a list of objectwise commutative squares. Evaluating them
at an object is a derived observation, while naturality and higher action stay
inside the generic emdash calculus. The phrase *locally exact square* remains
the semantic theorem that can construct item 4 for a concrete site square; it
is not a proposed field family in the computational interface.

The probe also reveals why an equivalence of the raw slice category with the
big affine slice would overstate the general case. For a site of all schemes
over `U`, the affine objects form a basis or dense subsite rather than every
object. A strict category equivalence is available only in specially chosen
ambient affine-only presentations. The future interface should support the
basis functor plus a sheaf/topos comparison and allow the identity/equivalence
special case to reduce through it.

No public symbol was promoted from that first probe. Its remaining
semantic-strength choice is resolved by CS-D-018 and the second probe below.

### 13.5 CS-05b affine-basis realization selection — 2026-08-03

The first concrete consumer does not yet transport generic glue or
sheafification across the chart comparison.  Its smallest honest contract is
therefore the conjunction of two complementary whole statements:

1. semantic basis comparison: a selected sheaf-restriction functor is
   compatible with ordinary presheaf restriction by one whole
   `IsoEvidence`, and that functor carries `OmegaEquivAlong Cat_cat`; and
2. computational realization: the actual ambient structure presheaf,
   restricted along the selected affine-basis functor, has one whole
   `DefIso` to the existing affine scheme's computing underlying presheaf.

The first statement prevents an unrelated affine label: it ties the selected
base functor to the two sheaf theories and asserts comparison-lemma strength.
The second preserves the desired executable coordinate normal forms. They do
not duplicate naturality: both comparisons live at whole functor-category
owners, and readable components remain derived observations.

The focused candidate
`tmp/probes/cs05b_affine_basis_realization.lp` passed under the 60-second limit
with zero warnings. It is now split into the promoted generic rule-free
`emdash3_2_site_basis.lp` and the CommRing-specific rule-free
`emdash3_2_commutative_algebra_affine_basis.lp`, with focused reviewers
`examples/site_basis.lp` and `examples/commutative_ring_affine_basis.lp`.
The promoted sources contain no rewrite rule, unification rule, continuity
field, induced topology, constructed reflector, locally-exactness derivation,
component square family, or sheafification/glue Beck--Chevalley mate.

The normal-form audit found one deliberate distinction. Generic
`fapp0(psh_restriction_func(i),P)` retains the generic precomposition owner's
stable cut-oriented runtime form; it is not judgmentally folded to the direct
`comp_cat_fapp0(P,Op(i))` spelling. Existing Cat-specialized unification does,
however, prove that comparison by `eq_refl`. The generic module therefore
exposes `psh_restriction_value_path` and the derived
`psh_restriction_value_iso` as proof-time presentation bridges. It adds no
runtime rule and does not duplicate generic functor action. The
CommRing-specific ambient restriction is written directly by composition, so
its scheme-facing value computation remains judgmental.

A larger ignored experiment attempted to derive immediately an isomorphism
between the restricted selected sheaf object and the affine selected sheaf
object. Its helper endpoints check, but the assembled candidate did not finish
under the unchanged 60-second import budget on the loaded host. Nothing from
that experiment is promoted or claimed. CS-05b therefore remains honest: it
retains a whole sheaf-category equivalence and a whole underlying-presheaf
`DefIso`, not a new sheaf-object comparison.

The stronger mate from CS-05a remains a valid later capability if a concrete
CS-07/CS-08 consumer must transport generic glue. At that later boundary,
local exactness is a mathematical route for constructing the one whole
invertible mate; it is not additional runtime record payload. Likewise, the
PSSS-05d free categorical localization may construct the fixed-site reflector
through emdash-owned whole action and its eliminator into local targets, but
Tabareau's auxiliary HoTT coequalizer does not prescribe its declarations or
reductions.

### 13.6 CS-05b promotion evidence — 2026-08-03

The promoted source and reviewer quartet is focused-green under the mandatory
60-second bound. Warning-enabled checks of all four targets report exactly the
inherited 1,179 warnings: 1,020 unjoinable-critical-pair diagnostics and 159
replaceable-pattern-variable diagnostics, with no warning at either new
source. The strict inferred-slot audit reports zero rules and zero candidates
in both new modules; the unchanged kernel audit remains zero unreviewed
candidates with 52 annotated slots across 32 intentional clauses. The strict
check catalog, report-header lint, active-reference lint, source TOC,
shell/Python syntax checks, and diff hygiene are green.

The exact-content health identity is
`sha256:45836a25af8bced8ed321a708026feb79bc8fc686995b573743fa1551580cfb5`
with source-metrics identity
`sha256:6565c58890f8556f2f745ef843fabffa13f824e42285e782a9bc52e6e4ff2a10`.
The resumable pass has persisted 115 of 116 targets green, including both new
sources, both new reviewers, the affine-glue source, and its reviewer. The
sole remaining target is unchanged `emdash3_2_checks.lp`. It imports neither
new module and the current tracked health report records recent green
58.519-second evidence for that exact unchanged central target. Repeated
bounded runs under concurrent load, after the load ended, and with only the
validator pinned to performance CPUs all reached the fixed 60-second cap
between 60.24 and 60.76 seconds; none emitted an assertion, rule, or source
error before interruption.

Under this plan's proportional-validation rule and the root SOP's explicit
instruction to carry forward recent green aggregate evidence for unchanged
boundaries, the central result is carried forward rather than rerun again.
The generated health report therefore remains at its previous exact snapshot;
the current 115-target resumable state plus that tracked central evidence is
the recorded combined boundary. This is not claimed as a fresh 116-target
generated report. No full CI, weakened timeout, modified central assertion,
or redundant repository aggregate is scheduled. The bounded CS-05b tranche
is included in authorized local checkpoint `b4fca9c`.

### 13.7 Validation timeout recalibration — 2026-08-03

The former 60-second ceiling was adopted as an early-development hang guard
before the current diagnostic and computational-schemes layers existed. At
the `cea2605c` comparison checkpoint, `emdash3_2_checks.lp` had 19,425 lines;
it now has 22,265. More importantly, recent exact green health observations
for the central target include 54.033, 57.730, 57.890, and 58.519 seconds,
while repeated checks of the same unchanged target reached the old cutoff
between 60.24 and 60.76 seconds without emitting a semantic error. Current
focused affine-basis and affine-glue targets also have valid observations near
55 and 56 seconds. The old split between a 30-second probe, 60-second focused
check, and 60-second registered check therefore classified the same valid
dependency path differently according to its wrapper and ordinary host load.

The active SOP and all emdash2 Lambdapi wrappers now use one uniform
90-second per-target ceiling. This is a ceiling, not an expected duration and
not authorization for a broad aggregate: a successful focused check still
returns immediately, owner-position probes remain the first validation step,
and recent exact aggregate evidence is still carried forward whenever the
checked boundary is unchanged. The unrelated TypeScript test watchdogs are
outside this kernel-policy change.

For the one-time local timeout migration, a focused uncommitted helper reused
the 115 exact-current exit-zero observations obtained under 60 seconds and
executed only the missing central target under 90 seconds. That target passed
in 67.884 seconds, directly confirming that the previous limit was rejecting
a valid check. The helper and its migration-only tests were then removed
before checkpointing. Durable resumable-health behavior remains strict in
checked file paths and bytes, Lambdapi version, warning mode, extra flags, and
timeout. The refreshed tracked health report is exact-current for all 116
targets, records 115 resumed observations and the one current central
observation, and has source-metrics snapshot
`sha256:6565c58890f8556f2f745ef843fabffa13f824e42285e782a9bc52e6e4ff2a10`
and check-content snapshot
`sha256:45836a25af8bced8ed321a708026feb79bc8fc686995b573743fa1551580cfb5`.

## 14. Validation And Checkpoint Contract

For every bounded source tranche:

1. inspect all worktrees and exact staged/unstaged state;
2. relocate owners and consumers with `rg`;
3. state the mathematical normal form and non-claims in the living plan;
4. probe the candidate under the uniform 90-second per-target Lambdapi
   ceiling; this larger ceiling does not authorize a broad or aggregate rerun;
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

The successor persistent goal was started on 2026-08-03 with this objective
and remains active after the CS-01 checkpoint. The plan, not the launch
sentence, owns the evolving task order and detailed acceptance gates.
