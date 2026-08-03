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
5. keep atlas-first gluing outside the active goal as a separate future
   construction problem, rather than making it part of scheme data;
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
| Locally-ringed support locality | The invertibility-locus operation `D` is a support; in the ordinary spatial setting this is equivalent to local stalk rings. | A witness-rich topology-local presentation is implemented: invertible zero forces the empty sieve to cover, and an invertible sum selects a covering sieve with executable unit branches. Raw distributive-lattice support laws and the stalk comparison remain later theorems. |
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
3. use the separate topology-local computational local-ring presentation for
   the first whole-object consumer, while retaining raw support-lattice and
   stalk comparisons as later theorems;
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

The CS-06 owner audit sharpens this gate. The existing
`comm_ring_psh_invertibility_sieve(O,U,s)` already constructs the whole
ordinary sieve `D_U(s)` and its restriction action. Max Zeuner's support
condition, however, is not merely the pointwise predicate that a restricted
section is a unit. It requires `D(0)=bottom`, `D(1)=top`,
`D(st)=D(s) meet D(t)`, and `D(s+t) <= D(s) join D(t)` in the relevant
point-free open algebra, or an equivalent topology-local forcing statement
for a local ring object. The active site library has ordinary sieves and
pullback but no selected bottom/finite-join algebra or internal local-ring
forcing interface. Replacing the join law by a pointwise choice of one unit
branch would be too strong, while objectwise nontriviality would mishandle the
empty-open stage. Therefore CS-02 is a genuine later prerequisite for the
public name `SchemePresentation`, not a field to guess during the atlas
tranche. The binary affine-cover substrate below is intentionally not called a
scheme.

The subsequent owner probe resolves the computational prerequisite without
postulating a raw join. `empty_sieve(U)` is the constant `Path(Empty)` family,
so literal membership reduces to `Empty`. A selected topology-local local-ring
presentation supplies:

```text
Unit_O(U)(0) -> Covers_T(empty_sieve(U))

Unit_O(U)(s+t) ->
  Sigma R : Sieve(U), Covers_T(R) *
    Pi q in R, Sigma b : Bool, Unit_O(domain(q))(s|q or t|q).
```

This is the computational Kripke--Joyal alternative already allowed by the
audit: it retains an actual covering refinement and executable branch instead
of truncating existence or choosing one branch globally. The laws for one and
products are algebraically automatic and remain derived comparison work. The
selected presentation is not asserted proposition-valued, and the raw
distributive lattice of opens and stalk-local-ring equivalence remain CS-11.

### CS-03 — Finite selected-cover presentation

Audit whether `FiniteFamily` plus a supplied covering sieve can express a
finite subcover without inventing a second sieve-generation calculus. The
current affine consumer should continue to use
`CommRingZariskiCoverFamily` as its source of truth. A generic finite cover
interface is promoted only with a non-affine consumer and a precise statement
that the selected finite family generates or covers, not merely that its
members lie in a covering sieve.

The first consumer resolves the immediate binary case without a second sieve
constructor. For selected covering sieve `R` and charts `c0,c1 : R`, define

```text
CoverChartFactorization(c,q)
  = Sigma h : Hom(domain(q),domain(c)), q = c o h

BinarySelectedCoverGeneration(R,c0,c1)
  = Pi q, q in R ->
      Sigma b : Bool,
        if b=false then CoverChartFactorization(c0,q)
        else CoverChartFactorization(c1,q).
```

Together with retained coverhood of `R`, this is constructive evidence that
the two selected arrows generate `R`: their retained membership makes their
generated branches a subsieve of `R`, while the displayed factorization gives
the reverse inclusion. It is strictly stronger than listing two members and
retains executable chart selection and factor maps. Closure under further
restriction is derived by composition and is not stored as an external
naturality field. The first tranche need not construct or name the generated
sieve itself. A generic
Nat-indexed finite choice/factorization family remains consumer-gated until a
consumer needs arity beyond two; the existing algebraic
`CommRingZariskiCoverFamily` remains unchanged.

The two selected arrows are the affine **generators** of the atlas. The
covering sieve also contains all their precompositions, and those arbitrary
refinements are not required or claimed to be affine. This matches the usual
finite affine-cover condition: the selected domains are affine and their
generated sieve covers. It would be unnecessarily strong to equip every
member of that sieve with a separate affine realization. The later semantic
`Scheme_cat` remains presentation-independent; only a chosen computational
`SchemePresentation(X)` carries such generators and their realizations.

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

The audit splits this phase rather than overclaiming the first promoted type:

- **CS-06a — binary affine-cover presentation:** package two selected charts,
  the explicit generation witness above, and for each chart the already
  supplied reflective slice, coordinate ring, affine presentation, affine
  basis functor, and whole `AffineBasisRealizationAlong`. This is an honest
  global-first computational atlas over an existing ringed object, but it is
  named `BinaryAffineCoverPresentation`, not `SchemePresentation`;
- **CS-06b — locally-ringed scheme certificate:** after CS-02 supplies the
  correct point-free support/local-ring capability, combine it with CS-06a
  and generalize the binary choice to a finite atlas only when an arity-generic
  consumer requires it.

The first CS-06b consumer is now promoted conservatively. Locality for the
distinguished object belongs on its actual slice `K/X`, not on every unrelated
ambient object. A supplied reflective slice retains topology, sheaf semantics,
and one whole `DefIso` to the computing ambient restriction; the topology-
local presentation runs on that target. Pairing it with CS-06a yields
`BinaryLocallyRingedAffineCoverPresentation`. It is deliberately not yet
renamed `SchemePresentation`: a covering-sieve member in an arbitrary site is
not automatically an open immersion. An admissible-open or relative-geometry
contract is therefore the next semantic naming gate.

The CS-06c audit resolves that gate by separating two meanings that the word
*scheme* had conflated. Max Zeuner's functor-of-points definition requires a
local Z-functor together with an affine **compact-open** cover; compact opens
are classified by transformations into the Zariski-lattice functor. A bare
Grothendieck-cover member is not that classifier data. By contrast, the
historical Cartier experiment defines a scheme **relative to a ringed site**:
the selected site coverage is already the chart geometry, and chosen slice
charts are required to satisfy the affine interface. It has no independent
open-immersion field.

The current v3.2 package is an honest computational implementation of the
second, site-relative boundary. Its descriptive name should remain
`BinaryLocallyRingedAffineCoverPresentation`; adding a transparent
`SchemePresentation` alias or an unstructured `IsOpen` predicate would add no
semantics. It must not be advertised as Zeuner's functorial qcqs-scheme, a
classical locally-ringed-space scheme, or a representation-independent
semantic scheme. Conversely, construction of a compact-open classifier must
not block the intended Cartier-style non-affine computational consumer. The
functor-of-points/open-classifier comparison is routed to CS-10, while CS-06d
totals the completed site-relative package without adding overlap data.

This relative reading agrees with the Stacks Project's site distinctions. A
big Zariski covering is specifically a jointly covering family of open
immersions (Tags `020N` and `020T`); objects of the small Zariski site are
themselves open immersions into the base. By contrast, the small and big
étale sites select étale objects/covering maps (Tag `03PF`). Thus
*admissibility* belongs to the chosen site or coverage and is not universally
synonymous with monomorphism. A later claim of classical Zariski semantics
must specialize or compare the current supplied topology with that coverage,
but the generic Cartier-style ringed-site presentation should not duplicate
the coverage by carrying an additional `open` field.

This sequencing preserves the computational center while preventing either a
mere cover-member list or coordinate-localization locality from masquerading
as a semantic scheme condition.

### CS-06d — Total binary site-relative scheme presentation

The global-first scheme interface does **not** require overlap isomorphisms or
gluing data as additional inputs. The global reflective CommRinged object and
its whole structure sheaf already own restriction and compatibility. A
selected covering family then supplies affine realizations of its selected
generators; repeated restriction, overlap maps, and cocycle behavior are
derived from the global object and generic whole composition.

The current implementation has this information in fibrewise form:

```text
P : ReflectiveCommRingedSpaceCover(K)
Q : BinaryLocallyRingedAffineCoverPresentation(P).
```

Their dependent total is

```text
BinarySiteRelativeSchemePresentation(K)
  = Sigma P : ReflectiveCommRingedSpaceCover(K),
      BinaryLocallyRingedAffineCoverPresentation(P).
```

This is not a notation-only alias: it packages the actual global object,
structure sheaf, selected covering sieve, topology-local local-ring
capability, constructive binary generation, and both whole affine chart
realizations as one end-user presentation. Its projections route to the
existing owners and introduce no overlap, transition, cocycle, or gluing
field. The qualifier *site-relative* remains essential: the supplied site
determines its admissible covering maps. A later classical Zariski or Zeuner
comparison must still identify the appropriate open/compact-open semantics.

The two selected generators are the affine cover charts. Arbitrary arrows of
the sieve they generate are refinements and need not themselves have affine
domains in a general ambient site; their restrictions and compatibility still
come from the global object. This is the ordinary distinction between an
affine covering family and every arrow in its generated covering sieve.

Atlas-first two-affine gluing remains an out-of-scope CS-08 possibility for
the different situation in which no global object exists yet. It is not a
prerequisite for the site-relative scheme presentation, projective-space
presentation, or any supplied non-affine computational example.

This is the direct v3.2 successor of the historical declaration
`scheme Ml Cs` and its operation `scheme_slice_ascheme`. In the old file,
`Ml` retained the ringed/local ambient data, `Cs` retained a chosen covering
diagram, and `scheme_slice_ascheme` supplied an affine structure for each
chosen chart in that diagram. The v3.2 total makes the corresponding global
and chart data explicit, specializes the first executable interface to two
constructively generating charts, and replaces ad hoc component rules by
whole restriction, `DefIso`, and affine-realization owners. It does not claim
that the experimental declaration was mathematically complete or that every
refinement arrow in the generated sieve is another chosen affine chart.

### CS-07 — First non-affine computational consumer

The selected consumer is a global object supplied with two affine charts,
testing the global-first presentation without constructing the object. An
atlas-first constructor from independent affine pieces is not required for
the Cartier-style computational goal and is outside the active path. A later
projective-line example may likewise supply its global object, structure
sheaf, local-ring capability, and affine cover rather than first proving a
general gluing/effectivity theorem.

The parameterized first consumer is now concrete. Given a supplied
`Q : BinaryAffineCoverPresentation(P)`, an arbitrary retained sieve member
`q`, and its membership witness, evaluate
`binary_affine_cover_refinement_at(Q,q,member)`. The result is the existing
Boolean-selected `BinaryCoverChartFactorization`; its side derives the
selected chart generator, that generator's already-owned whole affine
realization, and its coordinate ring. No new Sigma package stores those
derived values. For an open Boolean side, the realization deliberately stays
in the canonical branch-indexed family instead of adding a dependent fusion
rule through the readable selected-chart observation.

This closes the supplied computational consumer: every retained arrow is
constructively routed through one of the two affine generators. It still does
not provide a closed genuinely non-affine global object, assert that an
arbitrary refinement is itself affine, supply the missing locally-ringed
support condition, or perform atlas-first gluing.

The post-CS-06d consumer audit sharpens what a first projective-line-style
example must establish.  Merely supplying two polynomial coordinate rings and
whole chart-coordinate `DefIso`s would be useful affine-chart data, but it
would not distinguish the projective line from an arbitrary global object
with two affine-line charts.  The familiar inversion comparison on the two
localized coordinate rings is computationally meaningful only when it is
connected to the **actual inherited intersection** of the two selected global
charts.  That connection is consumer data or a derived adapter for the
example; it is not a new overlap/coherence field in the general scheme
presentation.

No active v3.2 module currently supplies a projective/graded/`Proj` object, a
principal-sieve facade for an arbitrary chart arrow, or a ready ordinary
categorical-pullback object.  `Pullback_catd` is family reindexing, explicitly
not a pullback constructor.  General weighted-limit infrastructure may later
present a pullback, but no such finite diagram/weight consumer has yet been
selected.  The next bounded probe must therefore test the smallest honest
selected-overlap contract in the slice category before promoting a named
projective-line presentation.  It must not attach a disconnected localization
isomorphism to an opaque `P1` label, store external component naturality, or
move atlas-first gluing back into the active path.

### CS-08 and later — Out-of-scope construction and semantic comparisons

Possible later research, explicitly outside the current computational-scheme
MVP, includes:

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
| Binary global-first affine-cover presentation | Implemented, exact-current through the bounded 122-target health boundary, and locally checkpointed at `0f3b379` | Retain constructive generation of the covering sieve by the two charts; mere sieve membership is insufficient. |
| General finite-qcqs presentation | Good after the binary consumer | Generalize the Boolean choice to Nat-indexed finite factorization without duplicating the algebraic family owner. |
| Supplied global two-chart refinement consumer | Implemented, exact-current through the bounded 124-target health boundary, and locally checkpointed at `4892c33` | It consumes an assumption-explicit global presentation and does not construct a closed non-affine object. |
| Closed global non-affine example | Good but separate | Selecting or constructing a mathematically meaningful ambient object before `Scheme_cat` exists. |
| Constructive two-affine gluing | Out of current scope | It is needed only to construct a global object from independent charts, not to present or compute with an already supplied scheme. |
| Topology-local locally-ringed presentation | Implemented assumption-explicitly, exact-current through the bounded 128-target health boundary, and locally checkpointed at `c2b53bf` | It avoids raw joins: invertible zero yields empty coverhood, while an invertible sum returns a selected cover and memberwise Boolean unit branches. Raw support-lattice comparison remains later. |
| Total site-relative scheme presentation | Implemented, exact-current through the bounded 130-target health boundary | The rule-free dependent total retains the global cover and its binary locally-ringed affine certificate; the base site supplies relative chart geometry. |
| Functor-of-points compact-open classifier | Moderate/research and separately routed | A generic Grothendieck cover does not classify Zeuner compact opens. This is required for comparison with functorial qcqs-schemes, not for the Cartier-style site-relative computational consumer. |
| Stalk-local-ring comparison | Moderate/research | Stalk/point infrastructure and constructive hypotheses. |
| Small-site restriction/basis comparison | Moderate | Exact basis and topology transport owners. |
| Representation-independent category of schemes | Research-grade but plausible | Morphism representation, locally-ringed structure, and comparison with presentations. |
| Fixed-site categorical-HIT sheafification construction | Research-grade but factorable | Topology-to-local-equivalence bridge, categorical localization/HIT, rigid `Sheaf_cat` realization, CommRing lift, and left exactness. |
| Unrestricted atlas effectivity | Research-grade | Descent/localization infrastructure and scope. |

The original computational-schemes direction remains feasible. The main risk
is no longer basic opens, localization, topology, affine glue, the whole
ambient-to-affine chart comparison, the constructively generated two-chart
atlas, or the topology-local local-ring presentation; those now have working
internal owners. CS-06c now makes the semantic scope explicit: this is a
Cartier-style site-relative presentation, while a Zeuner compact-open or
classical open-immersion comparison remains separate. CS-06d now supplies the
total global package. The next direct computational-scheme consumer is a
supplied, genuinely non-affine global presentation with a mathematically
meaningful structure sheaf and selected affine cover. It does not require a
gluing/effectivity construction.

A native categorical-HIT experiment is also ready as an independent research
tranche, but not as the next dependency of that consumer. Its first honest
probe is Set/path-valued on a small explicit site: select whole descent maps,
define their local objects, and test whether free categorical localization
produces a whole reflector and unit that instantiate
`SheafificationCapability`. A CommRing-valued lift, left exactness, and slice
base change remain separate later gates. Raw support-lattice, compact-open,
and stalk comparisons likewise remain later theorems rather than hidden
prerequisites.

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
- **CS-D-019 — Uniform bounded validation:** all emdash2 Lambdapi wrappers use
  a 90-second per-target ceiling. A measured unchanged central check passed at
  67.884 seconds after repeatedly crossing the former 60-second ceiling.
  Proportional validation and carry-forward of exact unchanged evidence still
  prohibit broad aggregate reruns for reassurance.
- **CS-D-020 — Binary cover generation first:** two selected members of a
  covering sieve do not constitute a binary cover. The first honest atlas
  retains, for every arrow in the selected covering sieve, a Boolean-selected
  chart, an actual factor arrow, and its triangle path. This witness-rich
  generation contract precedes any generic Nat-indexed generated-sieve API.
- **CS-D-021 — Scheme naming is scope-explicit:** the whole
  invertibility sieve is not by itself Max Zeuner's support law, and
  coordinate-localization locality is not reused as a substitute. The
  topology-local internal local-ring condition is now implemented. A
  site-relative computational scheme presentation may use the selected site's
  own admissible chart geometry, while an unqualified classical/Zeuner
  `SchemePresentation` or semantic `Scheme_cat` still requires the appropriate
  open/compact-open comparison and morphism semantics.
- **CS-D-022 — Generators are not arbitrary sieve members:** the two affine
  charts are distinguished arrows in one selected covering sieve and the
  constructive factorization capability says that they generate it. Other
  members are refinements/precompositions of those generators; the package
  does not attach a separate affine realization to every such refinement.
  This is the binary instance of the intended chosen computational
  `SchemePresentation(X)`, while a later semantic `Scheme_cat` remains
  independent of any selected cover.
- **CS-D-023 — Canonical dependent package endpoints:** readable projection
  aliases remain available as observations, but types of later dependent
  projections use the literal nested-`Sigma` endpoints retained by the
  package. Restating those endpoints through readable aliases caused the
  affine-chart probe to exceed both 90 and 120 seconds; the canonical form
  passes without package eta, a rewrite, or a unification rule. This measured
  elaboration boundary is not evidence for increasing the timeout.
- **CS-D-024 — Refinement observations are derived, not stored:** a
  `BinaryCoverChartFactorization` already owns the executable side and factor
  map, while `BinaryAffineCoverPresentation` already owns both whole affine
  realizations. CS-07 therefore adds no second refinement Sigma. It evaluates
  generation once and derives the selected generator, branch-indexed whole
  realization, and coordinate ring by Boolean elimination. The open-side
  realization is not forced through a new dependent fusion rule, and the
  arbitrary refinement is not reclassified as affine.
- **CS-D-025 — Topology-local support avoids raw joins:** local
  nontriviality sends unit evidence for zero to coverhood of the literal empty
  sieve. Local unit splitting sends unit evidence for `s+t` to a selected
  covering sieve whose members carry executable Boolean unit branches. This
  is witness-rich computational presentation data, not a pointwise global
  disjunction, raw sieve union, propositional truncation, or claim that the
  presentation type is a property.
- **CS-D-026 — Whole-object locality lives on `K/X`:** the distinguished
  object's local-ring presentation retains a supplied reflective slice. Its
  topology owns the forcing relation, its whole `DefIso` owns sheaf/computing
  comparison, and the local computation runs on the whole ambient restriction
  target rather than an opaque or unrelated presheaf.
- **CS-D-027 — Locally-ringed atlas is the fibrewise certificate:**
  `BinaryLocallyRingedAffineCoverPresentation` combines CS-D-025/026 with the
  existing generated binary affine atlas over one retained global cover. Its
  dependent total is a site-relative computational scheme presentation. It
  does not thereby become an unqualified classical/Zeuner scheme or a
  representation-independent semantic scheme object.
- **CS-D-028 — Site-relative and functorial schemes are separate:** the
  historical Cartier interface treats its selected ringed-site coverage as
  the chart geometry and asks chosen slices to be affine. At that explicit
  site-relative boundary, `BinaryLocallyRingedAffineCoverPresentation` is the
  completed binary computational presentation and no additional open label is
  stored. Zeuner's functorial qcqs-scheme instead requires compact-open
  classifier data; that future comparison must not be simulated by a generic
  cover member, a transparent alias, or an opaque `IsOpen` witness.
- **CS-D-029 — Global-first schemes do not store gluing data:** once a global
  ringed object and its structure sheaf are already retained, restriction,
  overlap compatibility, and cocycle propagation belong to that whole object
  and generic composition. The first site-relative scheme presentation totals
  the existing global cover plus its locally-ringed affine-atlas certificate.
  Coordinate transition isomorphisms are inputs only to the separate
  atlas-first construction in which the global object does not yet exist.
- **CS-D-030 — The binary total recovers the historical scheme declaration:**
  the old `scheme Ml Cs` plus `scheme_slice_ascheme` represented a global
  ringed/local ambient object, a chosen cover diagram, and affine chosen
  slices. `BinarySiteRelativeSchemePresentation(K)` is the current explicit,
  rule-free binary successor. The historical primitive `mod_smod` remains the
  separately supplied `SheafificationCapability`; constructing it by native
  categorical localization is CS-12 and does not block this declaration.
- **CS-D-031 — A non-affine example must connect coordinates to its inherited
  overlap:** two affine-line chart labels alone do not characterize a
  projective-line-style consumer.  Any selected localization/inversion
  comparison must be related to an actual common chart restriction, using a
  reusable slice-overlap or pullback contract if one is needed.  This adapter
  remains outside `BinarySiteRelativeSchemePresentation`: the global object
  continues to own restriction and compatibility, and the example merely
  identifies the derived overlap with its chosen computing presentation.

These decisions supersede the conflicting portions of PSSS-D-117, especially
its proposal to store whole overlap/cocycle witnesses in the ordinary
global-first record and its phrase *small/big-site equivalence*.

## 12. Side-Task Ledger

| ID | Task | Status | Gate |
| --- | --- | --- | --- |
| CS-00 | Consolidate affine checkpoint and corrected architecture | Complete; dedicated plan, parent supersession note, and index route added | This report and index routing |
| CS-01 | Global reflective ringed object, covering sieve, and internally derived pullback cover | Complete and locally checkpointed at `a5aebcf` | Checkpointed PSSS-11c and existing site pullback owner |
| CS-02 | Point-free invertibility-support/local-ring capability audit | Topology-local computational alternative promoted: empty-cover nontriviality plus selected covering unit splitting; raw support-lattice and stalk comparisons remain later | CS-D-025 and whole-object consumer |
| CS-03 | Generic finite-cover presentation audit | Binary contract selected: explicit witness that two charts generate the retained covering sieve; generic Nat arity remains consumer-gated | CS-06a first two-chart consumer |
| CS-04 | Whole ambient chart-slice restriction and supplied reflective-slice presentation | Complete and locally checkpointed at `7d63a90`; induced topology/reflector transport remains a separate CS-05 input question | CS-01 plus existing Sigma, opposite, functor-composition, and reflective-site owners |
| CS-05 | Honest affine chart realization over an ambient restriction | Complete through CS-05b's whole semantic/computational package; locally checkpointed at `b4fca9c`; stronger sheafification base change remains separately consumer-gated | CS-04 and affine checkpoint |
| CS-05a | Historical site-morphism and modern morphism/comorphism/locally-exact contract audit | Complete as a contract audit; stronger sheafification base change remains separately consumer-gated | CS-04 plus a concrete affine-chart target |
| CS-05b | Whole sheaf-basis comparison plus computational ambient-affine realization | Promoted as two transparent rule-free modules; focused/exact-warning/audit/catalog green; exact-current 116-target health completed under the uniform timeout policy; local checkpoints `b4fca9c`, `82d93b5`, and validation-policy checkpoint `023ffbf` | CS-D-018 and CS-04 |
| CS-06 | Global-first finite-qcqs site-relative scheme presentation | Complete at the binary chosen-cover boundary through CS-06d; generic finite arity remains consumer-gated | CS-02/CS-03/CS-05 contracts |
| CS-06a | Global-first `BinaryAffineCoverPresentation` with constructive cover generation and whole affine realizations | Complete and locally checkpointed at `0f3b379`: three rule-free source layers, three reviewers, exact warning comparison, audit/catalog/authority synchronization, and 122-target resumable health are green | CS-03 binary contract plus CS-05b |
| CS-06b | Add correct locally-ringed support and, when consumed, generic finite arity | Binary whole-object locally-ringed atlas complete and locally checkpointed at `c2b53bf`: two rule-free sources, two reviewers, exact warning comparison, audit/catalog/authority synchronization, and 128-target resumable health are green. Generic finite arity remains consumer-gated; CS-06c resolved the scheme-name scope | CS-D-025/026 plus CS-06a |
| CS-06c | Separate site-relative presentation from functor-of-points compact-open semantics | Complete as an architecture audit: retain the descriptive site-relative name, add no empty open label/alias, and route compact-open comparison to CS-10 | CS-D-028 |
| CS-06d | Total binary site-relative scheme presentation | Complete and locally checkpointed at `4b178ee`: a 141-line/14-symbol rule-free source, 107-line/12-assertion reviewer, exact warnings, audit, registries, authority prose, and 130-target resumable health are green | CS-D-028/029/030 plus CS-06b |
| CS-07 | Supplied global two-chart selected-refinement consumer | Complete and locally checkpointed at `4892c33`: rule-free source, focused reviewer, exact warning comparison, registry/authority/catalog synchronization, and 124-target resumable health are green. A closed genuinely non-affine realization remains separate | CS-06a |
| CS-07b | First supplied genuinely non-affine global consumer | Contract audit in progress: no active projective/graded object exists, and a projective-line-style presentation must connect its localization transition to the actual inherited chart intersection rather than merely label two chart rings | CS-D-031; smallest honest selected-overlap/pullback probe |
| CS-08 | Atlas-first two-affine gluing constructor | Out of current scope, not part of the global-first scheme interface | Reconsider only for a future consumer explicitly constructing a global object from independent affine pieces |
| CS-09 | Small-site restriction and affine/principal-open basis comparison | Later | Concrete small-site consumer |
| CS-10 | Semantic `Scheme_cat`, `Spec_func`, functor-of-points compact opens, and presented-scheme realization | Research continuation | Stable object/morphism interfaces, CS-06, and a genuine open classifier/comparison |
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

### 13.8 CS-06a binary affine-cover presentation — 2026-08-03

The promoted design distinguishes a selected affine generating family from
the full covering sieve it generates. For one retained global object `X` and
one retained covering sieve `R` on `X`, the two selected chart arrows
`c0 : U0 -> X` and `c1 : U1 -> X` are members of `R`. For every other member
`q : V -> X`, `BinarySelectedCoverGeneration` returns an executable Boolean,
a factor map from `V` to the selected chart domain, and the path identifying
`q` with the corresponding composite. Membership plus sieve closure gives
the generated subsieve's inclusion in `R`; factorization gives the reverse
inclusion. Arbitrary members of `R` are refinements, not additional selected
affine charts, and no affine realization is required for every refinement.

Three transparent rule-free modules implement that boundary:

- `emdash3_2_commutative_algebra_binary_covers.lp` has 275 lines and 11
  symbols. It defines one-chart factorization, the witness-rich Boolean
  choice, and generation of the retained sieve without constructing a second
  generated-sieve object or using propositional truncation.
- `emdash3_2_commutative_algebra_affine_cover_charts.lp` has 199 lines and 10
  symbols. It packages the actual supplied reflective chart slice, a
  coordinate ring and existing `AffineSchemePresentation`, a whole affine
  basis functor, and the existing whole `AffineBasisRealizationAlong`; its
  coordinate `DefIso` is derived from that owner.
- `emdash3_2_commutative_algebra_affine_cover_presentations.lp` has 112 lines
  and seven symbols. It combines two selected charts, their constructive
  generation capability, and their two whole affine realizations as
  `BinaryAffineCoverPresentation`.

All three modules contain zero rewrite rules and zero unification rules.
Generic composition, restriction, functor action, transformation naturality,
and the retained whole `DefIso`/`OmegaEquivAlong` owners continue to propagate
the internal structure. No external restriction square, overlap comparison,
or cocycle family is stored. The package is deliberately not named
`SchemePresentation`: the correct point-free locally-ringed support condition
remains CS-06b, and an atlas-first gluing constructor remains CS-08.

The focused reviewers are
`examples/commutative_ring_binary_covers.lp` (138 lines, six assertions),
`examples/commutative_ring_affine_cover_charts.lp` (85 lines, six assertions),
and `examples/commutative_ring_affine_cover_presentations.lp` (61 lines, four
assertions). They check the factor triangle and both Boolean branches,
generation application, constructor/projection computation, both whole affine
realizations, and the derived coordinate `DefIso`.

The normal-form probe rejected one superficially readable dependent-package
spelling. Restating later projection types through
`affine_cover_chart_ring(Q)` caused the chart candidate to exceed both the
90-second registered ceiling and a diagnostic 120-second run. Keeping the
literal nested `sigma_Fst`/`sigma_Snd` endpoints selected by the package made
the same whole interface pass. The promoted API therefore exposes readable
aliases for ordinary observations while using canonical nested-Sigma
endpoints in dependent types. It adds no package eta, rewrite, unifier, or
timeout increase.

Proportional validation is green:

- quiet health timings for the three sources are 3.429, 16.615, and 16.373
  seconds; the three reviewers take 9.831, 31.085, and 41.287 seconds;
- warning-enabled checks of all six targets inherit exactly 1,179 warnings
  (1,020 unjoinable critical pairs and 159 replaceable pattern variables),
  with no warning located in a new source or reviewer;
- the strict rule-LHS audit remains at zero unreviewed rules with 52
  annotations across 32 intentional clauses;
- strict catalog generation/checking, source TOC, report-header and active
  reference lint, check-metrics tests, Python/shell syntax, and whitespace
  hygiene pass; and
- the exact-current health report contains 122 successful targets. A
  one-time ignored-cache migration first proved that the previous 116 files
  still reproduced their exact recorded content hash and that their
  Lambdapi/environment identity was unchanged. The health refresh then reused
  those 116 successes and executed only the six new targets. Its
  source-metrics snapshot is
  `sha256:723fdd5ce992da7d8f6f53ce12c072452ede915d75947fb779d483b04c7c1fd1`
  and its check-content snapshot is
  `sha256:ef903fa031ffeaa6a541ff48abe6e013244ff9c027bc2b1a093b9e0c461a4605`.

No full CI, kernel-wide replay, root aggregate, push, merge, history rewrite,
publication, or worktree cleanup was performed. The complete CS-06a boundary
is locally checkpointed as `0f3b379` (`feat: add binary affine-cover
presentations`). CS-07 may now consume the package as a supplied global
two-chart computational atlas; a closed non-affine construction and the
semantic locally-ringed scheme classifier remain separately gated.

### 13.9 CS-07 selected-generator refinement consumer — 2026-08-03

The first parameterized consumer begins with a supplied
`Q : BinaryAffineCoverPresentation(P)` and an arbitrary member `q` of its
retained covering sieve. Evaluating
`binary_affine_cover_refinement_at(Q,q,member)` reuses the presentation's
constructive generation function and returns its existing
`BinaryCoverChartFactorization`. The factorization's Boolean side then
computes the selected generator, its retained whole affine realization, and
its coordinate ring.

The first owner probe packaged the factorization and selected realization in
a new dependent Sigma and passed. Retrospective SOP review rejected that
shape because it duplicated data: the factorization already owns its side and
the presentation already owns both realizations. The promoted module instead
contains only six transparent derived observations:

- `binary_affine_cover_chart_at_side` and
  `binary_affine_cover_realization_at_side` perform literal Boolean selection;
- `binary_affine_cover_refinement_at` evaluates the retained generation
  function at a membership witness; and
- `binary_affine_cover_refinement_chart`,
  `binary_affine_cover_refinement_realization`, and
  `binary_affine_cover_refinement_ring` derive the selected public data from
  the computed factorization.

The source
`emdash3_2_commutative_algebra_affine_cover_refinements.lp` is 157 lines with
six symbols, zero rewrite rules, and zero unification rules. Its realization
observation deliberately keeps the canonical branch-indexed `bool_elim`
family for an open side; it does not add a dependent fusion between that
family and the readable selected-chart observation. The 98-line reviewer
`examples/commutative_ring_affine_cover_refinements.lp` has six assertions
covering both literal branches, generation evaluation, selected chart,
selected whole realization, and selected coordinate ring.

Proportional validation is green:

- focused health timings are 56.557 seconds for the source and 38.288 seconds
  for the reviewer under the uniform 90-second ceiling;
- warning-enabled checks of both targets inherit exactly 1,179 warnings
  (1,020 unjoinable critical pairs and 159 replaceable pattern variables),
  with no warning located in either new file;
- the strict rule audit remains at zero unreviewed clauses with 52 annotated
  slots across 32 intentional clauses;
- strict catalog, source-TOC, report-header, active-reference, check-metrics,
  Python/shell syntax, health-staleness, and whitespace checks pass; and
- the exact-current health report contains 124 successful targets. A
  one-time ignored-cache migration proved that all 122 previous files still
  reproduced their exact content hash under the unchanged environment, then
  executed only the two new targets. Its source-metrics snapshot is
  `sha256:e2822b73c06bc463b8a182195ac885346178d708c4dc62c00f0aaa5fadbeca4d`
  and its check-content snapshot is
  `sha256:82a4a49e1ccd8f53e53944a600a1acce9c5fb115ab0000850db9730140e62ede`.

No full CI, kernel-wide replay, root aggregate, push, merge, history rewrite,
publication, or worktree cleanup was performed. The complete CS-07 boundary
is locally checkpointed as `4892c33` (`feat: add affine-cover refinement
consumers`). It completes the supplied global two-chart refinement consumer,
not a closed non-affine example, locally-ringed scheme certificate, or
atlas-first gluing construction.

### 13.10 CS-06b topology-local whole-object presentation — 2026-08-03

The local-ring audit selected the witness-rich Kripke--Joyal formulation rather
than introducing a raw join of sieves. The 401-line rule-free source
`emdash3_2_commutative_algebra_local_ringed_sites.lp` adds 23 transparent
symbols. Its literal `empty_sieve(U)` has `Empty`-valued membership. A local
nontriviality witness sends unit evidence for zero to coverhood of that empty
sieve; a local unit-splitting witness sends unit evidence for `s+t` to an
actual covering sieve whose every retained member carries a Boolean-selected
unit witness for the restriction of `s` or `t`. The 167-line reviewer contains
11 assertions covering literal empty membership, both branches, all selected-
cover projections, local-ring application, and the closed chaotic degeneracy
model.

The first whole consumer is the 211-line rule-free source
`emdash3_2_commutative_algebra_locally_ringed_space_presentations.lp`, with 11
transparent symbols. `ReflectiveCommRingedWholeObjectLocalPresentation(P)`
retains a supplied reflective presentation on the actual slice `K/X`, uses
that presentation's topology for local forcing, exposes its existing whole
`DefIso`, and runs unit computation on the whole ambient restriction. Pairing
it with `BinaryAffineCoverPresentation(P)` yields the deliberately conservative
`BinaryLocallyRingedAffineCoverPresentation(P)`. The 113-line reviewer has
eight assertions covering both fields and the slice, topology, computing
presheaf, and whole-`DefIso` observations.

The tranche adds 892 lines, 34 symbols, 19 assertions, zero rewrite rules, and
zero unification rules. It does not add a pointwise disjunction, raw sieve
union, truncation, external naturality/coherence field, duplicated overlap or
cocycle payload, induced-slice-topology claim, stalk comparison, open-
immersion classifier, gluing constructor, semantic `SchemePresentation`, or
category of schemes.

Proportional validation is green:

- exact-current quiet timings are 3.383 and 16.283 seconds for the two sources
  and 3.893 and 38.327 seconds for their reviewers under the uniform
  90-second ceiling;
- warning-enabled checks of all four targets inherit exactly 1,179 warnings
  (1,020 unjoinable critical pairs and 159 replaceable pattern variables),
  with no warning located in a new source or reviewer;
- the strict rule-LHS audit remains at zero unreviewed rules with 52 annotated
  slots across 32 intentional clauses;
- strict catalog generation/checking, source TOC, report-header and active-
  reference lint, check-metrics tests, Python/shell syntax, and whitespace
  hygiene pass; and
- the exact-current health report contains 128 successful targets. A one-time
  ignored-cache migration first proved that all 124 prior files reproduced
  their recorded exact content hash under the unchanged Lambdapi/environment
  identity, then executed only the four new targets. The source-metrics
  snapshot is
  `sha256:fe9cc65e750c7b89c08efb7178ebcd920ebee26d98178178be6db65fca52ef2c`
  and the check-content snapshot is
  `sha256:3e8439ad51f06ecfb0490b9eb0dd4b9afadf412d99c7ea1186079131139e292e`.

No full CI, kernel-wide replay, root aggregate, push, merge, history rewrite,
publication, or worktree cleanup was performed. This completes the bounded
CS-06b promotion and makes CS-06c's admissible-open or relative-geometry
contract the next semantic audit. The complete feature boundary is locally
checkpointed as `c2b53bf` (`feat: add topology-local ringed affine covers`).

### 13.11 CS-06c/06d semantic audit and total scheme presentation — 2026-08-03

The semantic audit separated three claims that earlier wording had conflated.
The supplied site's coverage determines admissible chart geometry for the
Cartier-style relative interface. Classical Zariski schemes additionally need
comparison with open-immersion coverage, while Zeuner's functor-of-points
schemes use compact-open classifier data. The first claim is sufficient for
the current computational consumer; the latter two remain explicit later
comparison theorems rather than empty record fields.

The 141-line rule-free source
`emdash3_2_commutative_algebra_site_relative_schemes.lp` adds 14 transparent
symbols. Its normal form is

```text
BinarySiteRelativeSchemePresentation(K)
  = Sigma P : ReflectiveCommRingedSpaceCover(K),
      BinaryLocallyRingedAffineCoverPresentation(P).
```

The constructor retains the global cover and dependent certificate exactly
once. Twelve observations expose the global ringed site, distinguished object,
whole structure presheaf, selected covering sieve, topology-local capability,
binary atlas, both selected charts, and both whole affine realizations through
their existing owners. No rewrite rule, unification rule, external naturality
field, overlap/transition/cocycle payload, gluing constructor, classical-open
claim, or semantic `Scheme_cat` is added.

The 107-line reviewer
`examples/commutative_ring_site_relative_schemes.lp` contains 12 assertions,
one for every public projection/comparison. It checks both dependent-Sigma
betas, the inherited global observations, both halves of the fibrewise
certificate, and the exact types of both selected charts and both affine
realizations.

This is the current binary v3.2 successor of the historical
`scheme Ml Cs`/`scheme_slice_ascheme` interface. It retains an already-global
ringed object and a chosen cover whose selected chart slices are affine. The
old primitive `mod_smod` assumption is represented separately and more
honestly by `SheafificationCapability`; CS-12 may later construct that
capability through whole categorical localization without changing this
consumer boundary.

Proportional validation is green:

- exact-current health timings are 16.193 seconds for the new source and
  31.254 seconds for its reviewer; the comment-only corrected fibrewise source
  and its direct reviewer pass in 15.611 and 22.351 seconds;
- warning-enabled checks of the new source and reviewer each inherit exactly
  1,179 warnings (1,020 unjoinable critical pairs and 159 replaceable pattern
  variables), with no warning located in either new file;
- the strict rule-LHS audit remains at zero unreviewed clauses with 52
  annotated slots across 32 intentional clauses;
- strict catalog generation/checking, source TOC, report-header and active-
  reference lint, check-metrics tests, Python/shell syntax, and whitespace
  hygiene pass; and
- the exact-current health report contains 130 successful targets. A one-time
  ignored-cache migration verified 126 prior targets byte-for-byte against the
  checkpoint and preserved the unchanged Lambdapi/environment identity, then
  executed only the two new targets, the comment-only corrected source, and
  its direct reviewer. The source-metrics snapshot is
  `sha256:97554f1f0d17a93e26515071dc57c47bf2766b12bcd3a04d5c907763cf9f628a`
  and the check-content snapshot is
  `sha256:34b7318f842b5e8c76a08ac3ab1aacbf866b97a5b330e0b804606d993231590b`.

No full CI, kernel-wide replay, root aggregate, push, merge, history rewrite,
publication, atlas-first gluing, or worktree cleanup was performed. The
bounded CS-06c/06d feature boundary is locally checkpointed as `4b178ee`
(`feat: add site-relative scheme presentations`). The next direct
computational consumer is a supplied genuinely non-affine global presentation;
the first small-site categorical-HIT localization probe is an independent
CS-12 research option, not its blocker.

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
