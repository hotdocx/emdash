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
recorded by PSSS-05d and PSSS-D-114.  For a site `(K,T)` and one presheaf
`P`, the primary construction sought is a new object `sheafify_T(P)`,
presented by a categorical HIT that freely adjoins the selected descent
fillers, equalities, and higher coherences required to make `P` local.  Its
internal eliminator expresses the objectwise universal property

```text
Hom(sheafify_T(P), X) ~= Hom(P, X)    for every T-local X.
```

Choosing the covering-sieve, Cech, or higher-descent maps `W_T` uniformly and
making this construction functorial in `P` then assembles the objectwise HITs
into the whole reflector `sheafify_T`.  Equivalently, that assembled result is
the reflective/free localization of the whole presheaf category at `W_T`.
Thus *whole-category localization* describes the uniform semantics and
functorial packaging of the per-presheaf construction; it is not a proposal
to replace `sheafify_T(P)` by one unrelated category-level object.  Object and
arrow action, unit, naturality, and the eliminator must remain at whole
categorical owners.  This does **not** mean a direct transcription of a HoTT
HIT into Lambdapi, nor does it commit the stable consumer interface to
external point/path constructors or naturality equations.

The first CS-12 implementation tranche now makes the ordinary-covering-sieve
choice of `W_T` literal.  `FibrewiseSigma_catd(E,D)` composes a family
`E : K -> Cat` with a family over `Sigma(E)`.  Consequently an ordinary sieve
`R` on `U`, natively stored over `K/U`, extends to the ambient presheaf

```text
R_hat[V] = Sigma(f : Hom_K(V,U)), R(f),
i_R       : R_hat -> y(U).
```

The fibres and components of the whole first projection `i_R` compute.  Its
base-arrow action and naturality are carried internally by one displayed
functor; the first boundary deliberately adds no external equations or
separate action fields.  `IsTopologyLocalPsh(T,X)` now quantifies, for every
covering `R`, the exact whole equivalence induced by precomposition with
`i_R`.  This closes the topology-to-local-object *interface* for Cat-valued
ordinary-sieve descent.  It does not yet construct a local replacement,
prove equivalence with the PSSS-05a weighted-limit presentation, or select the
Cech/hypercover maps needed by stronger higher-descent semantics.

Three notions must therefore remain distinct:

| Phrase | Role in this program | Non-claim |
| --- | --- | --- |
| HoTT HIT | General object/type presentation by point, path, and higher constructors. | It is not by itself a sheafification construction or the selected emdash interface. |
| Tabareau's `OT` HIT | One auxiliary higher-inductive coequalizer used inside the iterated-kernel-pair proof of separated reflection. | It is neither the whole Tabareau sheafification nor a declaration template for v3.2. |
| Emdash categorical HIT | For each presheaf `P`, construct `sheafify_T(P)` by freely adjoining categorical descent data, with an eliminator into local targets; uniformly these objects and maps assemble the reflective localization of the whole presheaf category. | The whole-category formulation does not erase the per-presheaf constructor, nor expose external naturality fields or component coherence to scheme consumers. |

The adjective *categorical* thus names the constructors, coherence, and
eliminator used to build each localized presheaf, not a direct categorical
spelling of Tabareau's `OT`.  The PSSS-05d observation is that functorial type
theory may make that objectwise construction uniform at whole functor owners,
rather than asking every consumer to carry its action and naturality.  The
existing `WalkingEnd_cat` demonstrates one contextual categorical eliminator,
but it is not yet a generic local-object constructor, localization,
coequalizer, telescope-colimit, or higher-coherence infrastructure.

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

#### Direct free-sheaf correction: return, cover branching, and silent quotient

A subsequent review of Pierre-Marie Pédrot's *Pursuing Shtuck* and the earlier
*Debunking Sheaves* changes the active CS-12 sequencing.  The relevant PDF
pages were visually inspected alongside the supplied layout extractions:

- *Pursuing Shtuck*, PDF pages 5--7 and 10, for `isSh`, the free `X(A)`
  quotient-inductive construction, its recursor, and the computational
  dialogue-tree reading; and
- *Debunking Sheaves*, PDF pages 3, 13--14, and 21, for the `S_J(A)`
  return/ask/silent signature, the identification of compatible matching
  families with whole internal maps, and the distinction between dialogue
  algebras and their sheaf quotient.

For a proposition-valued modality represented by questions `I` and
proof-irrelevant answers `O:I->Prop`, Pédrot's direct free sheaf has the
generator-and-relation shape

```text
X(A)
  eta    : A -> X(A)
  ask    : Pi i:I. (O(i) -> X(A)) -> X(A)
  silent : Pi i x. ask(i, constant(x)) = x.
```

The family in `ask` is recursive in `X(A)`, not merely a family in the input
`A`; otherwise the constructor performs only one round of gluing.  The
`silent` equation is also not an arbitrary quotient.  It says that gluing the
restrictions of an already global element returns that element.  Together
with function/whole-map extensionality, it derives separatedness: if `x` and
`y` have the same restrictions on a cover, then both are equal to the glue of
that common matching family.

The direct external-site translation should use the whole ordinary-sieve
extension already implemented by CS-12a.  For a site `(K,T)`, input presheaf
`P`, object `U`, covering sieve `R`, and

```text
i_R : R_hat -> y(U),
```

the candidate is one whole presheaf `FreeSheaf_T(P)` with

```text
eta_P : P -> FreeSheaf_T(P),

glue(U,R,cover,m) : Hom_Psh(y(U), FreeSheaf_T(P))
  where m : Hom_Psh(R_hat, FreeSheaf_T(P)),

silent(U,R,cover,x) :
  glue(U,R,cover,x o i_R) = x.
```

The argument `m` is already an internally compatible matching family: its
action and naturality are those of one whole presheaf morphism.  No family of
componentwise equations is to be added.  In the intended fully internal
formulation, restriction of `glue` along `f:V->U` must be carried by the
pulled-back-cover/question action and the reindexed matching map at whole
presheaf owners.  It must not be retained as an external componentwise
naturality square.  The first external-site signature quantifies over
`(U,R,covers)` by dependent Pi, however, so its whole glue functor is internal
only in matching-family arrows; it does not yet own reindexing in the
object/cover indices.  CS-D-048 records this boundary and prevents the
missing action from being silently assumed.  The eliminator into a
`T`-local target `Y` should extend a
whole map `P->Y`, compute on `eta` and `glue`, respect `silent`, and derive

```text
Hom(FreeSheaf_T(P),Y) ~= Hom(P,Y).
```

Only after that per-input construction is uniform on presheaf arrows should
it be assembled into the whole reflector and compared with the rigid
`Sheaf_cat` facade and supplied `SheafificationCapability`.  A first bounded
implementation may expose the whole formation, unit, recursive cover-glue,
and silent quotient before claiming the eliminator or sheafification theorem,
but its name and comments must say that it is a direct free-cover HIT
boundary rather than a completed reflector.

The underlying formation initially lands in `Psh(K)` deliberately.  This is
not a decision that the final object is merely a presheaf.  Pédrot likewise
first forms `X(A):Type`, proves that `X(A)` is a sheaf, and can then package
the type with that evidence.  In v3.2 the corresponding staged endpoint is

```text
DirectCoverCompletionPsh(T,P) : Psh(K),

direct_cover_completion_is_local :
  IsTopologyLocalPsh(T,DirectCoverCompletionPsh(T,P)),

ConstructedSheaf(T,P)
  := (DirectCoverCompletionPsh(T,P),is_local).
```

Directly declaring the first primitive as an object of the existing rigid
`Sheaf_cat(K,T,Cat)` would be circular: that facade presently acquires its
underlying-presheaf interpretation only through the supplied inclusion and
reflector capability which this program is intended eventually to construct.
The local-target eliminator should derive `is_local`; a constructed local-
object category can then package the result syntactically as a sheaf and be
related to the rigid facade by a scoped whole realization/equivalence, never
by a broad definitional identification.

The earlier supplied `SheafificationCapability` is the integration contract
for this construction, not an obsolete parallel API.  Integration proceeds
in explicit grades:

1. derive the local-target eliminator, including its `eta`, `glue`, and
   `silent` computation/coherence laws;
2. derive `IsTopologyLocalPsh` for every completed presheaf and package the
   result in the constructed local-object/sheaf category;
3. derive the fixed-forward whole universal property
   `Hom(completion(P),X) ~= Hom(P,X)` for every local target `X`;
4. assemble formation and unit functorially on presheaf morphisms and obtain
   the whole left-adjoint/inclusion pair;
5. instantiate the existing `SheafificationCapability`, including its
   fixed-counit `OmegaEquivAlong` reflector evidence; and
6. compare that constructed capability scopefully with any independently
   supplied reflector and prove, propositionally/wholly where appropriate,
   that its derived `sheafification_glue` mate agrees with the direct
   recursive construction on their common interface.

The fixed-site Cat-valued HIT is considered integrated with the existing core
at step 5 because existing consumers can then switch from supplied to
constructed evidence without an API rewrite.  CommRing lifting, left
exactness, induced-slice topology, and base-change are later integration
grades required before assumption-explicit ringed-site and scheme clients can
be reconstructed from it.  They do not block validation of the core
reflector.  No step installs a conversion rule between constructed and
supplied reflectors or conflates direct HIT glue with the adjunction mate.

The post-checkpoint eliminator audit exposes one necessary internality
correction to the first signature.  Pédrot's oracle is an internal operation,
not merely an object-level function on matching families.  For each covering
`R` and presheaf `X`, write

```text
Match_R(X) = Hom_Psh(R_hat,X),
Sect_U(X)  = Hom_Psh(y(U),X).
```

The computational algebra at that cover must be

```text
DirectCoverAt(R,X)
  = Sigma (glue : Functor(Match_R(X),Sect_U(X))),
      glue o restrict_R = id_Sect_U(X).
```

Thus glue carries its action on arrows between matching families internally,
and silent is one whole equality of endofunctors.  The previous pointwise
`glue(m)` and `silent(x)` remain useful projections, but they must be derived
from this whole algebra rather than serve as its primitive representation.
This is the external-site form of Pédrot's internal oracle and constant-family
law.  It also answers the SOP concern: no family of component naturality or
silent equations is stored.

Every `IsTopologyLocalPsh(T,X)` canonically forgets to such a direct-cover
algebra by selecting the left inverse of each restriction equivalence and its
whole left-cancellation law.  The converse is deliberately **not** installed
as a primitive right-cancellation axiom.  In Pédrot's internal presentation,
existence on arbitrary matching families follows from internal naturality,
proof-irrelevance of answers, and pullback of questions.  Externally, the
corresponding v3.2 proof needs the whole pulled-cover action and the fact that
pullback along a sieve member is maximal.  Until that comparison is derived,
`DirectCoverAlgebra(T,X)` is the computational oracle view and
`IsTopologyLocalPsh(T,X)` is the full restriction-equivalence view; neither is
silently identified with the other.

An honest nondependent eliminator must consequently do more than return an
opaque map.  It consumes a target direct-cover algebra (with topology-local
targets supplying one canonically), extends `P->Y`, preserves the whole glue
functors, and maps the source silent path to the selected target silent path.
The unit, glue, and silent/path beta data are the three recursor obligations
visible in Pédrot's Figure 2.  A selected map lacking the whole glue law or
path-constructor coherence is only an extension candidate and must not be
promoted as the CS-12 eliminator.

Pédrot also clarifies a meaningful intermediate *lax/effectful* notion.  If
the recursive cover operation is retained without the silent quotient, one
gets a dialogue/free-effect algebra rather than an ordinary sheaf.  Replacing
the equality by a merely directed arrow similarly suggests a lax completion.
This may be useful for Cat-valued lax descent or a future higher/stack-like
theory, but it does not by itself enforce ordinary separatedness.  The active
first construction therefore uses an internal path (or invertible groupoid
cell).  A directed `LaxCoverCompletion` may be probed separately and must not
be named `Sheafification` until an appropriate lax universal property and
consumer justify that terminology.  For higher-valued descent, invertible
cells and their higher coherences may replace literal set-level proof
irrelevance; a one-way cell changes the semantics and is not a cosmetic
presentation choice.

This direct constructor must also remain distinct from two existing uses of
the word *glue*:

1. `sheafification_glue` in `emdash3_2_ringed_sites.lp` is an adjunction-mate
   operation derived from an already supplied whole reflector.  A successful
   direct HIT may eventually construct the capability from which this mate is
   derived; the mate is not one of the HIT constructors.
2. `comm_ring_psh_localization_glue` and its affine Cartier specialization
   map coherent matching data on one basic open `D(s)` to the selected
   localization carrier `O(U)[1/s]`.  They are computing local-algebraic
   consumers/models of sheaf-like amalgamation.  Since `D(s)` need not cover
   `U`, they are neither general covering-sieve descent nor the recursive
   constructor of a reflector.  After a constructed structure sheaf exists,
   a scoped comparison may show that Cartier glue is the corresponding
   algebra/computation on principal opens; no global rewrite should identify
   the two operations.

Thus the historical `cartierSolution16.lp.txt` glue intuition and the direct
HIT constructor are related by *consumer versus constructor*: the former
expresses computational amalgamation for already selected local algebra and
the latter freely constructs an object supporting amalgamation over every
selected cover.  This distinction preserves the computational motivation of
the historical experiment without claiming that its primitive glue already
constructed sheafification.

#### Completed independent model: successor localization

The first concrete CS-12 model is the one-object free-monoid category
`BNat_cat` and the principal higher sieve generated by `bnat_generator`.  The
sieve is not supplied componentwise: it is the existing representable family
on the restriction slice at the generator.  Its fibre over an arrow `n` is
the category of factorizations of `n` through the generator.  Those fibres do
not definitionally collapse to literal `Empty`/`Unit`; subterminality and the
ordinary-sieve comparison must be proved from uniqueness of natural-number
factorization.  No rewrite is to be added merely to force that semantic fact
into a preferred fibre normal form.

For a Set/path-valued presheaf whose generator acts by `s:A->A`, localization
at that principal successor sieve has the sequential-telescope normal form

```text
inc(n,x)                         : Tel(A,s)
step(n,x) : inc(n+1,s(x)) = inc(n,x).
```

The promoted `emdash3_2_telescope_localization_hit.lp` selects this as the
first genuine per-object categorical-HIT boundary.  Its primitive signature
is limited to formation, point/path constructors, set-truncation evidence,
the dependent eliminator into set-valued fibres, and point-constructor beta.
The path beta is derived by proof uniqueness in the set target.  More
importantly, both whole inverse laws for

```text
Function(Tel(A,s),B) -> TelescopeCocone(A,s,B)
```

are derived internally by dependent induction, `PiFunext`, Sigma path
induction, and proposition-valued coherence; they are not opaque universal-
property axioms.  The original endomap acts on the telescope by
`inc(n,x) |-> inc(n,s(x))`, its inverse computes by the index shift
`inc(n,x) |-> inc(n+1,x)`, and the HIT step derives both pointwise
cancellations.  These assemble at the existing proof-time `Grpd_cat`
composition/identity views into a whole `OmegaEquivAlong Grpd_cat` without a
new composition rewrite or external naturality field.

This closes one reusable *per-object one-map localization* experiment, not the
whole sheafification goal.  The telescope is retained as valid categorical-HIT
infrastructure and evidence about eliminators and internally derived whole
universal properties.  It is no longer the active route to direct
sheafification.  The ignored principal-BNat ordinary-sieve/factorization probe
is frozen and must not be promoted merely to connect this special model to a
Grothendieck topology.  Such a bridge remains legitimate deferred generic-
localization research if a later consumer specifically needs it.

The active scheme lane returns to a selected projective-line/projective-space
consumer.  The independent constructed-sheaf lane starts from the direct
`eta/glue/silent` cover-indexed signature above.  Neither lane is blocked by
the BNat factor predicate.  Arbitrary higher descent, comparison with rigid
`Sheaf_cat`, CommRing lift, left exactness, and slice base change remain later
gates after the direct per-presheaf eliminator exists.

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

The bounded CS-07b/07c implementation now supplies that honest connection.
A selected Boolean weighted-limit comparison presents the two chart objects'
product in the conventional slice; whole slice-domain and structure-presheaf
action derive the actual overlap ring and its two restrictions.  The generic
Laurent layer then makes each literal restriction map a one-variable
localization and derives both coordinate-inversion maps by polynomial and
localization universality.  A thin dependent adapter applies that package to
the actual rings and maps.  No disconnected localization `DefIso`, external
component naturality, or atlas-first gluing is introduced.

No active v3.2 module yet constructs a projective/graded/`Proj` object or a
closed `P1` term, and `Pullback_catd` remains family reindexing rather than a
categorical pullback constructor.  The completed adapter is therefore an
assumption-explicit projective-line-style computational presentation of a
supplied global object, not a construction or non-affineness theorem for that
object.

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
| Selected actual intersection of two retained charts | Implemented and locally checkpointed at `d9e036f` after focused checks, exact warnings, strict audit/catalog, and 134-target exact-current resumable health | The intersection is a selected binary product in the conventional slice, not an atlas-first gluing payload. |
| Projective-line-style actual-overlap coordinates | Implemented, proportional validation green, and locally checkpointed at `5118fb1` | Both chart rings and the actual structure-sheaf restrictions are the polynomial/localization inputs; both Laurent maps are internally constructed and compared wholly with identity on the literal overlap. |
| Closed global non-affine object | Good but separate | Supply or later construct a genuine global `P1`/`Proj` object instantiating the now-available site-relative and Laurent-overlap presentations; this tranche does not prove non-affineness. |
| Constructive two-affine gluing | Out of current scope | It is needed only to construct a global object from independent charts, not to present or compute with an already supplied scheme. |
| Topology-local locally-ringed presentation | Implemented assumption-explicitly, exact-current through the bounded 128-target health boundary, and locally checkpointed at `c2b53bf` | It avoids raw joins: invertible zero yields empty coverhood, while an invertible sum returns a selected cover and memberwise Boolean unit branches. Raw support-lattice comparison remains later. |
| Total site-relative scheme presentation | Implemented, exact-current through the bounded 130-target health boundary | The rule-free dependent total retains the global cover and its binary locally-ringed affine certificate; the base site supplies relative chart geometry. |
| Functor-of-points compact-open classifier | Moderate/research and separately routed | A generic Grothendieck cover does not classify Zeuner compact opens. This is required for comparison with functorial qcqs-schemes, not for the Cartier-style site-relative computational consumer. |
| Stalk-local-ring comparison | Moderate/research | Stalk/point infrastructure and constructive hypotheses. |
| Small-site restriction/basis comparison | Moderate | Exact basis and topology transport owners. |
| Representation-independent category of schemes | Research-grade but plausible | Morphism representation, locally-ringed structure, and comparison with presentations. |
| Ordinary-sieve extension and topology-local-object classifier | Implemented at the whole Cat-valued boundary | Fibrewise dependent-Sigma values and inclusion components compute; explicit base-arrow beta and equivalence with the separate weighted-limit descent presentation remain consumer-gated. |
| Fixed-site categorical-HIT sheafification construction | Whole constructor, recursor, eligible-question, varying-family, canonical-pullback, strict-substitution, and syntactic internal-sheaf boundaries implemented; the remaining reflector is research-grade but factorable | Formation/unit/glue/silent and the nondependent recursor are checkpointed. Whole strict glue substitution is derived internally at generic `tapp1_func`; one whole displayed glue plus one whole silent path now form `DirectCoverSheafStructure`, and the completion inhabits the total `DirectCoverSheaf`. Generic record-style functor extensionality is no longer an active prerequisite. Remaining gates are whole Hom universality, functorial reflector assembly, scoped comparison with conventional two-sided `IsTopologyLocalPsh` and the rigid `Sheaf_cat` facade, then CommRing lift and left exactness. |
| Unrestricted atlas effectivity | Research-grade | Descent/localization infrastructure and scope. |

The original computational-schemes direction remains feasible. The main risk
is no longer basic opens, localization, topology, affine glue, the whole
ambient-to-affine chart comparison, the constructively generated two-chart
atlas, or the topology-local local-ring presentation; those now have working
internal owners. CS-06c now makes the semantic scope explicit: this is a
Cartier-style site-relative presentation, while a Zeuner compact-open or
classical open-immersion comparison remains separate. CS-06d supplies the
total global package, and CS-07b/07c now supply its selected actual overlap
and a direct polynomial/localization coordinate presentation there. A closed
global `P1` term remains separate because no projective/graded object is
currently available; it may instantiate the presentation as supplied data
without requiring a gluing/effectivity construction.

A native categorical-HIT experiment is also ready as an independent research
tranche, but not as the next dependency of that consumer. Its topology-local
target predicate is now concrete: ordinary covering sieves extend to whole
maps into Yoneda and induce fixed-forward Hom equivalences. The next honest
probe is Set/path-valued on a small explicit site: for one selected presheaf
`P`, construct `sheafify_T(P)` by adjoining the chosen descent fillers and
test its internal eliminator against those local targets. Only after that
objectwise probe should the construction be made uniform on presheaf objects
and arrows to produce a whole reflector and unit instantiating
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
  categorical HIT first constructs `sheafify_T(P)` from each presheaf `P` by
  freely adjoining descent fillers and coherences, with an internal eliminator
  into local targets.  Uniformity in `P` assembles those objectwise HITs into
  the PSSS-05d/PSSS-D-114 reflective localization of the whole presheaf
  category at the selected covering-sieve, Cech, or higher-descent maps. Such
  a construction may instantiate a fixed-site `SheafificationCapability`,
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
- **CS-D-032 — Chart intersections are selected slice products:** the
  smallest honest inherited overlap is a supplied binary product of the two
  chart arrows in the conventional slice over the global object. The generic
  product contract is the existing whole terminal-weighted limit comparison
  for the Boolean path-discrete diagram. Its universal cone derives both
  projections internally; applying the existing slice-domain functor and
  structure-presheaf action derives the base arrows and restriction maps. No
  primitive pullback rule, componentwise cone/naturality fields, overlap or
  cocycle field on a scheme, or atlas-first gluing constructor is added.
  `Pullback_catd` remains family reindexing and is not reused as a categorical
  pullback object.
- **CS-D-033 — Laurent coordinates use the actual restriction maps:** the
  first projective-line-style adapter does not identify an unrelated Laurent
  ring with the inherited overlap by a disconnected `DefIso`.  Each literal
  chart structure ring is instead supplied as a one-variable polynomial
  algebra over one common base, and its already-derived structure-sheaf map
  into the literal overlap ring is supplied as localization at that
  coordinate. Polynomial universality constructs the map sending `t` to
  `u^{-1}`; localization universality extends it to the whole Laurent map.
  The shared-overlap presentation retains one whole identity path for each of
  the two constructed overlap endomorphisms. These paths are concrete
  coordinate-presentation evidence, not componentwise restriction squares,
  generic naturality fields, or transition/cocycle fields on
  `BinarySiteRelativeSchemePresentation`. The thin scheme adapter adds only
  the common base ring around that generic package. It neither constructs the
  supplied global object nor proves that it is non-affine or projective line.
- **CS-D-034 — Objectwise localization is a whole-Hom contract:** for one
  localizing arrow `w:A->B` in an ambient category, `X` is local when
  precomposition `Hom(B,X)->Hom(A,X)` is an `OmegaEquivAlong Cat_cat`. A
  proposed unit `eta:P->L` is an objectwise localization when `L` is local and
  precomposition `Hom(L,X)->Hom(P,X)` is the same fixed-forward whole
  equivalence for every local `X`. The selected left inverse is the internal
  eliminator; existing equality-valued owners derive both whole beta/eta
  composite-functor paths. The green ignored identity model validates this
  output contract but is not a nontrivial sheafification construction.
- **CS-D-035 — Ordinary sieves localize through fibrewise dependent Sigma:**
  an ordinary sieve over `K/U` is extended to `K` as
  `V |-> Sigma(f:V->U),R(f)`. The generic whole first projection is its exact
  inclusion into `y(U)`, so topology-locality can quantify whole Hom
  equivalences without an external cone, component naturality, or a supplied
  unrelated presheaf map. This construction, rather than a propositional
  truncation, is the missing bridge found by the first CS-12 audit.
- **CS-D-036 — Fibrewise Sigma is the only new primitive boundary:**
  `FibrewiseSigma_catd` and its whole displayed first projection are stable
  constructor owners with computing fibres/components. The ordinary-sieve
  extension and local-object classifier are transparent specializations.
  Explicit base-arrow beta, total-category Fubini, weighted-descent
  comparison, and categorical-HIT localization remain separate gates; no
  sieve-specific opaque action or external coherence package is promoted.
- **CS-D-037 — Successor localization is retained but no longer the active
  sheafification model:** the principal higher sieve generated by
  `bnat_generator` and its Nat-factorization semantics remain a legitimate
  one-map localization example.  The checkpointed telescope is reusable
  categorical-HIT evidence.  The ignored ordinary/subterminal bridge is
  frozen: do not install fibre rewrites to literal `Empty`/`Unit`, pretend the
  higher sieve is already an ordinary covering sieve, or let this special
  representation theorem block direct cover-indexed sheafification or the
  projective consumer.
- **CS-D-038 — Minimal sequential-HIT primitive boundary:** the telescope
  localization primitive signature contains formation, point/path
  constructors, set truncation, dependent induction into set-valued fibres,
  and point beta.  Path beta, the whole maps-to-cocones equivalence, and its
  two inverse laws are derived internally; no generic `eq_ap` rewrite,
  component coherence package, or opaque universal-property axiom is added.
- **CS-D-039 — Executable localized transition:** the original endomap on the
  telescope and its successor-index shift inverse both compute on point
  constructors.  Dependent induction derives their two cancellations, which
  are packaged through the existing `Grpd_cat` proof-time comparison heads as
  one whole `OmegaEquivAlong Grpd_cat`.  This proves one-map localization, not
  yet whole-presheaf sheafification.
- **CS-D-040 — Direct Shtuck/free-sheaf route:** for one `(K,T,P)`, construct
  a whole recursive cover completion with a whole unit `P->X`, a cover-indexed
  constructor from matching maps `R_hat->X` to sections `y(U)->X`, and an
  internal silent path saying that gluing the restriction of a section returns
  it.  Matching compatibility and restriction action remain at whole
  presheaf owners.  An eliminator into topology-local targets and its whole
  Hom equivalence are required before calling the object a constructed
  sheafification; functorial reflector assembly comes afterwards.
- **CS-D-041 — Lax completion is a distinct intermediate:** recursive cover
  branching without the silent quotient is a dialogue/effect completion.  A
  directed rather than invertible silent cell may support a future lax or
  higher descent semantics, but it does not establish ordinary separatedness.
  Probe it under an explicitly lax name only after a concrete consumer; the
  first ordinary Set/discrete-groupoid route retains an internal path.
- **CS-D-042 — Three glue owners remain distinct:** the direct HIT glue is a
  recursive constructor; `sheafification_glue` is an adjunction mate derived
  from a supplied or later constructed reflector; Cartier localization glue
  is a computing algebraic amalgamation on one principal open.  Later scoped
  comparison may relate their computations, but no rewrite or public alias
  identifies them.
- **CS-D-043 — Projective consumers return to the active scheme lane:** the
  current library already owns a supplied global scheme presentation, two
  affine realizations, their actual inherited overlap, and the Laurent
  inversion computation.  The next bounded projective consumer should first
  select an assumption-explicit global `P1` capability over a base ring and
  instantiate those owners; it must state whether the global object is a
  primitive/supplied presentation rather than claim atlas-first construction.
  Generalize next to the finite standard cover of `P^n`, with polynomial chart
  rings and computing pairwise localizations.  A genuine `Proj(S)` constructor
  is a subsequent algebraic tranche requiring graded commutative rings,
  homogeneous localizations, degree-zero parts `(S_f)_0`, and the irrelevant-
  ideal cover.  Neither direct sheafification nor BNat is a prerequisite for
  the assumption-explicit `P1` consumer; constructed `Proj` remains a larger
  but now explicitly active standard-library direction.  Mathematically a
  sufficiently computational `Proj` subsumes the standard examples through
  `P^n_R = Proj(R[x_0,...,x_n])`; the explicit `P1`-first order is therefore a
  validation strategy, not three independent definitions.  Once the graded
  infrastructure exists, standard `P^n` should be derived by instantiating
  `Proj`, and the earlier explicit `P1` capability should receive a whole
  comparison rather than remain a competing public construction.
- **CS-D-044 — Direct-cover glue is a whole functor:** at each cover, package
  the oracle as a functor from the matching hom-category to the section
  hom-category and package silent as the whole equality
  `glue o restriction = id`.  Pointwise glue and silent observations are
  projections.  The checkpointed object-only primitive is migrated before an
  eliminator is claimed; no external matching-arrow naturality fields are
  added.
- **CS-D-045 — Oracle structure and restriction equivalence remain distinct
  until proved equivalent:** topology-locality supplies a direct-cover algebra
  through its selected left inverse.  Do not add the other inverse law as an
  opaque constructor.  Deriving it from whole pulled-cover action, ordinary
  sieve subterminality, and maximality after restriction along a member is a
  named CS-12 gate and the bridge from the computational/Pédrot view to
  `IsTopologyLocalPsh`.
- **CS-D-046 — Eliminator acceptance includes the silent constructor:** the
  nondependent recursor must expose whole unit and glue beta laws and the
  path-constructor coherence mapping source silent to target silent.  A
  primitive map with only endpoint typings is not the promised HIT
  eliminator.  Topology-local targets enter through the canonical
  locality-to-algebra conversion.
- **CS-D-047 — The first recursor combines judgmental data beta with whole
  algebra-map coherence:** a map of direct-cover algebras stores, at each
  cover, one equality
  between whole glue functors plus one higher equality comparing the two
  induced silent paths.  Restriction/postcomposition naturality is derived
  at the existing rigid `Hom_func` owner and is not repeated as a component
  field.  Recursive glue is a stable primitive whole-functor constructor, and
  the canonical algebra is assembled transparently from whole glue and
  silent.  The primitive nondependent recursor has narrow runtime beta for
  the whole unit and for pointwise evaluation of recursive glue; the latter
  still consumes and returns whole presheaf maps.  Whole glue-functor
  preservation and silent/path beta remain internal equality and higher-
  equality evidence.  This is the same selected split used by the existing
  categorical HITs: data constructors compute at exact observers, while a
  path constructor's beta need not become a broad generic `eq_ap` rewrite.
  Whole Hom uniqueness remains a separate gate.
- **CS-D-048 — The external cover-index signature does not yet internalize
  question naturality:** `DirectCoverAlgebra` stores, for each externally
  quantified `(U,R,covers)`, a whole functor on matching-family arrows and the
  whole silent law `glue o restriction = id`.  This is internal in section
  and matching-map categories, but the dependent Pi does not itself provide
  action under `f:V->U` and pullback of `R`.  Pédrot's compact oracle argument
  obtains the missing amalgamation equation from naturality because its
  question/answer family is an internal presheaf term; importing that proof
  into the current external Pi would be circular.  There are two honest next
  routes.  The preferred general route constructs an internal covering-
  question classifier with whole pullback/reindexing action, after which
  oracle naturality is inherited.  A bounded fallback may instead define an
  explicitly two-sided external cover algebra and an eliminator restricted
  to targets carrying its whole amalgamation law.  That fallback is a scoped
  interface, not a proof from the current one-sided algebra.  Do not add a
  family of component squares, an opaque right-inverse field to the existing
  recursor, or a rewrite asserting `restriction o glue = id`.  Data-
  constructor beta may remain judgmental at exact stable observers; path and
  higher-coherence beta remain equality evidence unless a concrete scoped
  eliminator observer justifies a confluent rule, as in the existing
  WalkingEnd and direct-cover recursors.
- **CS-D-049 — The first projective-line boundary is a supplied dependent
  total:** `SuppliedProjectiveLinePresentation(K)` retains one already-global
  `BinarySiteRelativeSchemePresentation(K)`, its actual selected binary chart
  intersection, and the existing `BinarySchemeLaurentOverlapPresentation` on
  the literal inherited structure-ring restrictions.  Ordinary Sigma
  projection is its computation.  Because the global structure presheaf
  already owns restrictions, compatibility is inherited; no transition,
  cocycle, or gluing field is added.  This is the smallest end-to-end
  projective-line-style capability and validates the computational owners,
  but it does not construct `Proj`, prove that the supplied global object is
  projective or non-affine, or replace the later graded construction.  Once
  graded `Proj` exists, the standard `P^1` instance should be compared wholly
  with this explicit boundary.
- **CS-D-050 — Superseded checkpoint: cover questions over unrestricted
  higher-sieve transformations:** the first CS-D-048 route represented a question as
  `(U,S)` in
  `Sigma_cat(Op_cat(K),HigherSieveClassifier(K))`.  A base arrow carries the
  question to the strict existing higher-sieve pullback, so identity,
  composition, and higher action remain at that whole owner.  The additional
  assertion that `S` is an ordinary sieve covered by `T` is a proposition-
  valued displayed family over the question total.  Its arbitrary action and
  coherence are therefore internal; on the canonical pullback arrow its
  action agrees by proposition uniqueness with the explicit ordinary-sieve
  and Grothendieck-topology pullback operation.  This agreement is proof-time
  evidence, not a runtime rule that reconstructs dependent proof fields.
  The ambient extension `Sigma(f:y(U),S(f))` and its first projection
  specialize definitionally to the existing ordinary-sieve extension and
  inclusion.  This tranche internalizes question pullback only.  It does not
  yet provide a whole functor from varying questions to extensions, matching
  and section families, or an internally natural glue map; those are the next
  CS-12 gate.  Do not replace that gate with external component squares or
  claim the missing `restriction o glue = id` law prematurely.
  The implementation checkpoint remains useful evidence, but this semantic
  conclusion is superseded by CS-D-051: ordinariness and coverhood are not
  preserved by an arbitrary higher-sieve transformation, and proposition-
  valuedness proves uniqueness only after target evidence exists.
- **CS-D-051 — Eligible cover questions are Path-valued object data:** a
  descent question at `U` is
  `Sigma(R:Sieve(K,U),groth_topology_covers(T,U,R))`.  This retains the
  Cat-valued higher sieve inside `R`, but fibre arrows are paths between
  eligible questions rather than arbitrary transformations between higher
  sieves.  A primitive whole classifier over `Op_cat(K)` owns identity,
  composition, path action, and coherence.  Its selected stable sieve
  observer computes under base transport to `sieve_pullback(p,R)`; the cover
  proof is obtained from the internally transported pair and agrees, by
  proposition uniqueness, with `groth_topology_pullback`.  Stable sieve and
  cover observers are internally compared with the underlying Sigma
  projections, so the runtime owner does not introduce a disconnected record
  semantics.  This narrow observer produces no new critical-pair or inferred-
  slot diagnostic; a rejected direct `fapp1_fapp0` action rule produced ten
  new diagnostics, and a rejected raw `sigma_Fst` commuting bridge produced
  one product-projection overlap.  The extension and inclusion route through
  the existing ordinary-sieve owners.  The next gate remains a whole varying-
  extension/matching/section construction and a whole internal glue map; no
  external component naturality fields or premature locality claim is added.
- **CS-D-052 — Extension, restriction, and glue vary as whole internal
  families:** over the opposite eligible-question total, one whole functor
  sends `(U,R,covers)` to the existing sieve extension and another sends it
  to `y(U)`. Their inclusion is one whole transformation. For each fixed
  presheaf `X`, `hom_con` then supplies Cat-valued matching and section
  families on the question category, and restriction is one displayed
  functor between them. The direct completion's recursive glue is likewise
  one displayed functor from the matching family to the section family; its
  literal component is the deployed whole glue functor, retained as a stable
  recursor head. Thus action on matching arrows and action under question
  pullback are both internal, with no family of external naturality squares.
  This is an intentional strengthening of the HIT signature, not a theorem
  extracted from the old externally indexed algebra. The first boundary does
  not add an arbitrary base-arrow rule: canonical extension/glue pullback
  action remains opaque until the right-inverse proof selects the smallest
  required computing observer. It consequently does not yet establish
  `restriction o glue = id`, locality, or sheafification.  The already
  primitive `silent` path has the opposite orientation
  `glue o restriction = id`; keeping these laws distinct is essential.
- **CS-D-053 — Canonical extension pullback is proof-time specified, while
  internal whole strict glue substitution remains a separate gate:** the action of the
  primitive varying-extension functor at the actual internally pulled-back
  question is compared by one whole path with a stable presheaf map.  That
  stable map computes at a test object and sends a literal `(h,member)` to the
  retained postcomposition pair `(p o h,member)`.  The generic action does not
  runtime-fold to the stable head: the owner-position fold exceeded the
  uniform 90-second checking ceiling, whereas the proof-time whole path and
  both narrow projection rules check promptly.  The varying representable
  action already reduces to direct Yoneda action, so it receives no duplicate
  primitive.  An attempted fully semantic definition through
  `sigma_pullback_total_func` exposed the expected Fubini/base-change square
  but did not elaborate through the current non-transitive proof-time
  comparisons between the represented-Hom and Sigma-total presentations; no
  broad unifier or composition fold is added for that convenience.

  This tranche also corrects an overstatement in CS-D-052 and §13.23.1.
  Ordinary v3.2 strict naturality already joins the two routes through the
  common off-diagonal `tapp1*` owner after projection to an object.  The
  current `Functord(E,D)` representation nevertheless retains a directed
  higher cell between those routes and does not make the two *whole functors*
  definitionally equal.  Therefore the displayed glue owner by itself cannot
  yet yield the whole path needed by `OmegaEquivAlong Cat_cat` for arbitrary
  Cat-valued presheaves.

  A first probe merely postulated that whole path and used `eq_ap`; it proved
  that the type is representable, not that the path follows from the current
  glue constructor.  A decisive follow-up oriented both generic whole routes
  to their common `tapp1_fapp0` owner.  That formulation typechecks and makes
  reflexivity prove whole strict naturality, but its warning-enabled probe
  raises the inherited 1,020 unjoinable-critical-pair inventory to 1,142 and
  would globally collapse distinctions intentionally retained for lax/higher
  displayed functors.  The broad rewrite is rejected.  The next design gate
  is an internal strict displayed-functor specialization, or an equivalently
  principled strict `tapp1*` owner, inhabited by the direct glue constructor.
  It must not be a sheaf-specific family of external naturality squares or an
  opaque per-question path.  A separately named lax/higher completion remains
  possible later, but ordinary sheafification continues only through the
  strict internal specialization.  The desired
  `restriction o glue = id` itself remains a theorem to derive, not a
  constructor.

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
| CS-07b | Selected inherited overlap for the first supplied non-affine-style consumer | Complete and locally checkpointed at `d9e036f`: two rule-free source modules, two nine-assertion reviewers, focused/exact-warning/audit/catalog/authority checks, and 134-target exact-current resumable health are green. CS-07c now attaches projective-line-style coordinate/localization data directly to this overlap | CS-D-031/032 and checkpointed overlap substrate |
| CS-07c | Canonical Laurent transition and actual-overlap adapter | Complete and locally checkpointed at `5118fb1`: the generic rule-free layer derives both Laurent maps by polynomial/localization universality and presents two literal localization maps into one common ring; the thin scheme layer instantiates it at the actual chart rings, inherited overlap ring, and existing restriction maps. A closed global `P1` object and non-affineness theorem remain separate | CS-D-031/032/033 and CS-07b overlap substrate |
| CS-13 | Selected projective-line/projective-space consumer and eventual `Proj` owner | The first assumption-explicit global `P1` capability is complete and locally checkpointed at `7241b00` as the transparent dependent total of the existing binary scheme, actual inherited overlap, and Laurent owners. General `Proj` next needs graded-ring, homogeneous-localization, degree-zero, and irrelevant-ideal infrastructure; once present it should derive the standard `P^n` examples, with a whole comparison to this explicit `P1` boundary. No atlas-first gluing or BNat bridge is a prerequisite. | Audit and select the smallest graded commutative-ring and homogeneous-localization substrate |
| CS-08 | Atlas-first two-affine gluing constructor | Out of current scope, not part of the global-first scheme interface | Reconsider only for a future consumer explicitly constructing a global object from independent affine pieces |
| CS-09 | Small-site restriction and affine/principal-open basis comparison | Later | Concrete small-site consumer |
| CS-10 | Semantic `Scheme_cat`, `Spec_func`, functor-of-points compact opens, and presented-scheme realization | Research continuation | Stable object/morphism interfaces, CS-06, and a genuine open classifier/comparison |
| CS-11 | Point-free support versus stalk-local-ring comparison | Later theorem | Support capability and suitable point/stalk infrastructure |
| CS-12 | Constructed native categorical-HIT/sheafification research | The topology-to-local-object tranche is checkpointed at `5e7505e`; the reusable sequential one-map HIT is checkpointed at `451db48`; the Pédrot-directed `eta/glue/silent` signature, whole glue correction, and unit/glue/silent-coherent recursor are checkpointed through `deeab6d`. Eligible questions and whole varying extension/restriction/glue are checkpointed through `98fe2c6`; CS-D-053's canonical extension-pullback comparison is checkpointed at `337a638`; the internal Pédrot sheaf package is checkpointed at `f119391`; the generic retained-member substitution substrate is checkpointed at `552516c`. The active owner-minimal promotion now provides generic strict ordinary/displayed pointwise-to-whole `OmegaEquivAlong`, one whole restriction/glue transformation tower, the second inverse `restriction o glue = id_Matching`, and `IsTopologyLocalPsh(DirectCoverCompletionPsh)`. New module and central diagnostic targets are focused-green with zero warnings, and strict LHS audits are clean; no long aggregate was rerun. The principal-BNat bridge remains frozen. | Audit the precise scoped comparison between the constructed topology-local total and the opaque supplied `Sheaf_cat` facade; do not invent a definitional coercion. Establish whole Hom uniqueness/universality and the fixed-site reflector/adjunction, then instantiate or compare with `SheafificationCapability`. Follow with CommRing lift and left exactness while keeping the independent `Proj` lane active. |
| CS-12x | Principal-BNat/telescope comparison | Deferred independent generic-localization example. The telescope implementation remains checkpointed and valid; its ignored factor-predicate/ordinary-sieve bridge is not on the scheme or direct-sheaf critical path. | A future concrete consumer requiring comparison of higher principal sieves with ordinary topology |
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

### 13.12 CS-07b inherited binary chart-overlap substrate — 2026-08-03

The first non-affine consumer audit established that two affine labels are
not enough: any projective-line-style coordinate transition must be attached
to the actual common restriction inherited from the supplied global scheme.
The smallest reusable contract is a selected binary product of the two chart
arrows in the conventional slice over that global object. This is an
intersection presentation, not a construction of the global object by
gluing.

The 288-line transparent rule-free generic candidate
`emdash3_2_finite_limits.lp` adds 15 symbols. It presents the pair `x,y : C`
as the Boolean path-discrete diagram, defines `IsBinaryProduct_comp` by the
existing `IsWeightedLimit_cov_comp` terminal-weighted comparison, and retains
one selected product object plus its whole universal comparison. Applying the
comparison to the representable identity derives a whole universal cone;
existing profunctor tensor, evaluation, and cell owners derive its two closed
endpoint projections. No componentwise naturality equations or new rewrite
or unification rules are introduced.

The 297-line transparent rule-free scheme adapter
`emdash3_2_commutative_algebra_scheme_chart_overlaps.lp` adds 14 symbols. A
`BinarySchemeChartOverlapPresentation(S)` is exactly a selected binary product
of the two retained chart objects in
`Slice_cat(K,binary_site_relative_scheme_whole_object(S))`. The generic
comparison supplies both whole slice projections. Existing arrow action of
`slice_domain_func` supplies their arrows in `K`, and existing arrow action of
the global commutative-ring presheaf supplies both restriction homomorphisms
from the chart rings to the overlap ring.

The 91-line generic reviewer and 134-line scheme reviewer contain nine typed
assertions each. Focused checks are green for both sources and both reviewers.
Each warning-enabled target inherits exactly 1,020 unjoinable critical pairs
and 159 replaceable pattern variables from existing dependencies, with no
warning located in either new source. The strict rule-LHS audit remains at
zero unreviewed clauses with 52 annotated slots across 32 intentional clauses.
The unchanged strict catalog remains fully classified at 1,992 kernel checks;
source TOC, report-header and active-reference lint, check-metrics tests,
Python/shell syntax, health staleness, and diff hygiene are green.

The exact-current health set now contains 134 successful targets. A one-time
ignored-cache migration verified all 130 prior targets byte-for-byte against
the recorded `sha256:34b7318f842b5e8c76a08ac3ab1aacbf866b97a5b330e0b804606d993231590b`
snapshot under the unchanged Lambdapi, flags, and 90-second identity, then ran
only the four new targets. Their source/reviewer timings are 2.149/2.153
seconds for the generic product and 16.214/16.107 seconds for the scheme
overlap. The new source-metrics snapshot is
`sha256:381fae406ca61c0c68b3ed5cdca74bb43e9cc7959c064cae93a4c08ce7e354e5`
and the exact checked-content snapshot is
`sha256:062ca9392127f68c4c55a5625f940880943ef00d9a0a9450f0c2d26e2c36513d`.
An initial exact-identity resume miss began replaying unchanged targets and was
stopped after 22 successes without writing a report; the verified migration
then produced the proportional exact-current report above.

The tranche deliberately asserts neither that every category has products nor
that arbitrary chart pairs have pullbacks. It does not reinterpret
`Pullback_catd`, add an overlap/transition/cocycle field to the scheme, require
atlas-first gluing, or claim to have constructed projective line. The next
consumer must identify this inherited overlap with a selected localization or
inversion-coordinate presentation belonging to a supplied global
projective-line-style object.

No full CI, completed kernel-wide replay, root aggregate, push, merge, history
rewrite, publication, atlas-first gluing, or worktree cleanup was performed.
The bounded standard-library boundary is locally checkpointed as `d9e036f`
(`feat: add selected scheme chart overlaps`).

### 13.13 CS-07c canonical Laurent and actual-overlap presentation — 2026-08-03

The first algebra probe reconstructed a one-variable polynomial structure
around an arbitrary target ring. That shape was rejected before promotion:
the existing `CommRingPolynomialAlgebra(A,Unit)` already owns the target,
base map, variable family, and universal property. The promoted 729-line
transparent rule-free module
`emdash3_2_commutative_algebra_laurent.lp` instead consumes that canonical
package directly. Polynomial universality selects the structured map
`A[t] -> A[u,1/u]` with `t |-> u^{-1}`; localization universality selects its
extension `A[t,1/t] -> A[u,1/u]`. Reversing the two packages constructs the
opposite map. Named observations expose the polynomial coordinate equation
and the whole localization-factor triangle without any new rule or unifier.

The same module adds
`CommRingOneVariableLocalizationPresentation(A,R,L,h)`, in which the literal
map `h:R->L` is simultaneously presented as localization at the selected
coordinate of a one-variable polynomial algebra. Two such literal maps into
one target ring form `CommRingLaurentOverlapPresentation`; its two retained
paths state that the internally constructed coordinate changes are the
identity endomorphism of that exact target. These are whole structured-map
paths. They replace the rejected alternative of independently choosing two
localized rings, joining each to the inherited overlap by a disconnected
`DefIso`, and then adding a separate comparison square.

The 78-line transparent rule-free scheme adapter
`emdash3_2_commutative_algebra_scheme_laurent_overlaps.lp` is intentionally
thin. `BinarySchemeLaurentOverlapPresentation(S,overlap)` adds one common
base ring and instantiates the generic package at the literal chart structure
rings, `binary_scheme_chart_overlap_ring`, and the already-derived
`binary_scheme_chart_overlap_restriction0/1`. It therefore does not duplicate
the overlap, restriction maps, transition, or cocycle data and adds nothing
to the general scheme record. The adapter is a projective-line-style
coordinate presentation of supplied global data, not a closed `P1`
construction or a non-affineness theorem.

An early convenience version repeated both full Laurent transition types as
scheme-level projection aliases. Although well typed in isolation, the
combined source exceeded the uniform per-target ceiling after expanding the
full site-relative dependency chain. Those redundant aliases were removed;
the four-symbol adapter exposes only its base ring and the generic coordinate
package. The 154-line algebra reviewer checks eleven generic observations,
including both transition directions and both whole common-overlap identity
paths. The 44-line scheme reviewer checks the constructor/projection beta
laws at the actual ring and restriction endpoints. Together these layers
exercise the full contract without re-expanding the same whole identities at
the heaviest dependency boundary.

Proportional validation is green:

- exact-current health timings are 4.381 seconds for the Laurent source,
  4.789 seconds for its reviewer, 16.022 seconds for the scheme adapter, and
  16.151 seconds for its reviewer;
- warning-enabled checks of all four targets inherit exactly 1,179 warnings
  (1,020 unjoinable critical pairs and 159 replaceable pattern variables),
  with no warning located in either new source or reviewer;
- the strict rule-LHS audit remains at zero unreviewed clauses with 52
  annotated slots across 32 intentional clauses;
- the unchanged strict central catalog remains fully classified at 1,992
  checks; source TOC, report-header and active-reference lint,
  check-metrics/source-TOC/warning-summary tests, Python/shell syntax, and
  whitespace hygiene pass; and
- the exact-current health report contains 138 successful targets. Before
  migrating the ignored resume identity, all 134 prior files recomputed to
  the recorded checked-content snapshot
  `sha256:062ca9392127f68c4c55a5625f940880943ef00d9a0a9450f0c2d26e2c36513d`
  under the unchanged Lambdapi, flags, and 90-second environment. The first
  health refresh reused those exact successes and executed only the four new
  targets. After removing two trailing blank lines, the final exact-identity
  refresh reused 136 successful targets and reran only the two byte-changed
  targets. The source-metrics snapshot is
  `sha256:d3e267fb0a76f504d21f74440a571a068324a054b1ca89fe4aeeed2b255d734e`
  and the exact checked-content snapshot is
  `sha256:495981dc77a2330a8b774c1e4808a5bf1977944c6b1e0c907fcbfbcc32b455fd`.

No full CI, examples aggregate, completed kernel-wide replay, root aggregate,
push, merge, history rewrite, publication, closed projective construction,
atlas-first gluing, or worktree cleanup was performed. One examples wrapper
was discovered to ignore a supplied filename and began the aggregate; it was
interrupted immediately and contributes no validation evidence. The bounded
CS-07c source boundary is locally checkpointed as `5118fb1`
(`feat: add Laurent scheme overlap presentations`).

### 13.14 CS-12a sieve extension and topology-local objects — 2026-08-03

The first CS-12 audit separated two questions that had previously been
conflated.  The universal output contract for localizing one object is already
expressible with existing whole owners: precomposition by the proposed unit
is an `OmegaEquivAlong Cat_cat`, its selected left inverse is the eliminator,
and the equality-valued hom-action extension supplies both whole cancellation
paths.  The ignored probe
`tmp/probes/cs12_single_map_localization_contract.lp` checks this contract and
a closed identity-localization model without adding a rule or pretending that
the identity model is sheafification.

The nontrivial missing bridge was representational.  An ordinary sieve is a
subterminal family over `Into_restr_cat(U)`, whereas local-object semantics
uses a whole map in `Psh_cat(K)`.  The rejected shortcut would have supplied
an unrelated presheaf and arrow annotated only by the same cover witness.
Instead, the promoted generic constructor
`FibrewiseSigma_catd(E,D)` composes `E : K -> Cat` with
`D : Sigma(E) -> Cat`.  Its fibre computes to

```text
Sigma(e : E[k]), D[(k,e)],
```

and `fibrewise_sigma_proj1_funcd` is one whole displayed first projection
whose component computes to the existing `Sigma_proj1_func`.  The family and
projection carry base action, naturality, and higher action internally.  The
first boundary intentionally leaves explicit base-arrow beta and the total
Fubini comparison deferred rather than adding an incomplete component action
calculus.

`emdash3_2_sieve_extensions.lp` is then transparent.  It specializes
fibrewise Sigma to `yoneda_psh(U)` and `sieve_higher(R)`, obtaining the whole
extension `ordinary_sieve_extension_psh(R)` and exact inclusion into `y(U)`.
`PshLocalAtOrdinarySieve(R,X)` fixes precomposition by that inclusion as the
forward arrow of one whole equivalence; `IsTopologyLocalPsh(T,X)` quantifies
the condition over every selected covering sieve.  This is Cat-valued
ordinary-sieve local-object semantics.  Equivalence with the separately
probed anchored weighted-limit descent boundary, a Set/path-valued closed
nontrivial model, the categorical-HIT object former, and functorial reflector
assembly remain later gates.

The owner-position probes and promoted focused checks are green.  The final
warning-enabled downstream reviewer inherits exactly 1,179 warnings
(`1,020` unjoinable critical pairs plus `159` replaceable pattern variables),
with none located in either new source or reviewer.  Both new sources report
zero reconstructible/unreviewed inferred LHS slots.  Source TOC, current-plan
header and active-reference lint, the strict unchanged 1,992-check catalog,
the focused source/reviewer checks, check-metrics/source-TOC/warning-summary
tests, Python/shell syntax, and whitespace hygiene pass.  Exact-current health
is green for all 142 registered targets.  The refresh first recomputed the
old 138-file content identity and reused those exact successes under the
unchanged Lambdapi `3.0.0-90-gdb4f780`, 90-second, warnings-disabled
environment; only the four new source/reviewer targets ran.  Their current
times are `5.607s`, `6.248s`, `5.973s`, and `6.187s`, respectively.  The
source-metrics snapshot is
`sha256:17837cd60e5440a34f77f052396cbe2f1f6de252a1ce7a372a1121316b4d3672`
and the exact checked-content snapshot is
`sha256:bf6327a019ad7865e67d3225096bb53c4664a171847c1607af18087587f7bd6b`.
No full CI, examples aggregate, root aggregate, push, merge, publication,
history rewrite, or worktree cleanup was performed.  The local checkpoint
is `5e7505e` (`feat: add ordinary sieve local-object maps`).

### 13.15 CS-12c sequential categorical-HIT localization — 2026-08-03

The first nontrivial small-site audit selected the existing one-object
`BNat_cat` and the principal higher sieve generated by `bnat_generator`.
The ignored probe `tmp/probes/cs12_bnat_principal_higher_sieve.lp` constructs
that family as the representable on the generator's restriction slice, so its
whole action is inherited rather than supplied componentwise.  It also
records the intentional negative result: fibres at zero/successor arrows do
not definitionally reduce to literal `Path_cat Empty`/`Path_cat Unit`.
Ordinary-sieve subterminality must therefore be proved propositionally from
the uniqueness of Nat factorization.  That proof and any topology declaration
remain outside this checkpoint.

The promoted `emdash3_2_telescope_localization_hit.lp` implements the
Set-targeted localization normal form for the corresponding generator action
`s:A->A`.  Its primitive signature is exactly one set-truncated sequential
HIT: the classifier, point and path constructors, sethood evidence, dependent
induction into set-valued fibres, and one point-constructor beta rule.  The
path beta is a transparent proof-uniqueness theorem.  Both inverse laws for
the whole restriction map from functions out of the telescope to compatible
Nat-indexed cocones are derived by dependent induction, nested `PiFunext`,
Sigma path induction, and proposition-valued coherence.  Neither inverse law
is an opaque symbol.

The selected endomap on the telescope computes by
`inc(n,x) |-> inc(n,s(x))`; its inverse computes by
`inc(n,x) |-> inc(n+1,x)`.  The HIT step supplies both constructor-level
cancellations, dependent induction extends them to all telescope points, and
the existing proof-time `grpd_comp_function`/`grpd_id_function` views package
them as one whole `OmegaEquivAlong Grpd_cat`.  No generic composition fold,
`eq_ap` rewrite, external naturality field, component coherence package, or
primitive universal-property axiom was added.  The 107-line focused reviewer
checks formation, constructors, sethood, point beta, proof-time path beta,
the whole cocone equivalence, both executable shift observations, the whole
transition equivalence, and non-collapse of the path endpoints.

The 886-line source contains 44 symbols and one rewrite.  Its strict LHS audit
reports zero reconstructible compound slots across zero unreviewed clauses.
Warning-enabled checks of the immediate dependency, source, and reviewer all
produce the exact same inherited 1,179 warnings (`1,020` unjoinable critical
pairs and `159` replaceable pattern variables), with no new location.
Focused source/reviewer checks, the strict unchanged 1,992-check catalog,
check-metrics/source-TOC/warning-summary tests, current-plan header and active-
reference lint, and whitespace hygiene are green.

Exact-current resumable health is green for all 144 registered targets.  The
first refresh attempt exposed that adding two registered paths invalidates the
aggregate resume identity and began replaying unchanged files; it was
interrupted rather than allowed to become an unnecessary long aggregate.
The previous 142-target payload was then reused only after mechanically
verifying that its exact old checked-content digest still matched the current
old-file bytes and that Lambdapi version, timeout, warning mode, and extra
flags were unchanged.  The final refresh resumed those 142 exact successes
and ran only the new source (`4.757s`) and reviewer (`2.230s`).  Its source-
metrics snapshot is
`sha256:42a1682e1188e9168b688182061414cc8942084d5945ca01d837a1acfbeab85b`
and checked-content snapshot is
`sha256:d74dbbbb5f7546d70d0720ffaa3524bbdb185784709662962a65ade0dbcfdac4`.
No full CI, examples aggregate, root aggregate, push, merge, publication,
history rewrite, or worktree cleanup was performed.  The local implementation
checkpoint is `451db48` (`feat: add telescope localization HIT`).

This checkpoint remains valid, but it is no longer the next CS-12 dependency.
The Pédrot review recorded below freezes the principal-BNat bridge and starts a
direct recursive cover-completion boundary instead.  The telescope may later
be compared with that construction as an independent one-map model; no such
comparison blocks schemes, projective consumers, or direct sheafification.

### 13.16 CS-12 course correction: direct free-cover HIT — 2026-08-03

The post-checkpoint review of *Pursuing Shtuck* and *Debunking Sheaves*
identified a sequencing error rather than a defect in the promoted telescope.
Localizing one endomap by a sequential colimit is a sound generic-localization
test, but it is not the direct generator-and-relation construction of a free
sheaf.  Continuing through the principal-BNat factor predicate would prove a
representation theorem for that special model while postponing the actual
cover-indexed constructor and the projective consumer.

The revised active design is the whole-presheaf translation of Pédrot's
`ret/ask/silent` quotient-inductive construction.  A matching family is one
whole map from `ordinary_sieve_extension_psh(R)` into the recursively
constructed completion; its compatibility is therefore internal.  Glue
returns one whole map from Yoneda, and the silent path identifies glue of a
section's restriction with that section.  The first promoted boundary must
remain honest about its strength: formation/unit/glue/silent constructors are
a direct free-cover HIT signature, not yet a sheafification reflector.  The
local-target eliminator and whole Hom universal property close the next gate.

The earlier Pédrot paper also records the intentional lax alternative.
Removing the quotient yields dialogue/free-effect branching; replacing its
path by a directed cell yields a candidate lax completion.  Either may become
useful for Cat-valued or higher descent, but ordinary sheafness requires
separatedness and therefore retains an invertible/path-level silent law in the
first model.

The relationship to the historical Cartier glue is now explicit.  Cartier
glue computes amalgamation into one localization carrier over `D(s)`; direct
HIT glue recursively creates sections over every selected cover; and the
existing generic `sheafification_glue` transports maps through the adjunction
after the reflector is available.  These are related construction, algebra,
and mate layers, not interchangeable symbols.

The tracked worktree was clean at `dd793b3` before this correction.  The
ignored `cs12_bnat_principal_higher_sieve` experiment remains unpromoted.  The
nearest baseline source and reviewer for `emdash3_2_sieve_extensions.lp` were
green under the uniform 90-second ceiling; recent 144-target exact-current
health remained applicable to the otherwise unchanged boundary.

The promoted `emdash3_2_direct_cover_completion_hit.lp` now realizes the
smallest honest signature selected by that review.  Its 103 lines contain five
symbols and no rewrite or unification rule: one rigid whole-presheaf former,
one whole unit, one recursive covering-sieve glue constructor, one transparent
restriction alias through the exact sieve inclusion, and one whole silent
path.  The 105-line reviewer checks five positive formation/computation
contracts and two intentional negative boundaries: the carrier does not
definitionally collapse to its generator, and silent does not become a
runtime glue reduction.  The formation deliberately lands in `Psh(K)`; no
opaque locality witness is supplied.  The next eliminator must derive
`IsTopologyLocalPsh`, after which the underlying presheaf and derived evidence
can be packaged as a constructed sheaf and compared scopefully with the rigid
`Sheaf_cat` facade.

Focused source and reviewer checks are green.  Warning-enabled checks of the
immediate dependency, source, and reviewer each reproduce exactly the inherited
1,179 warnings (`1,020` unjoinable critical pairs and `159` replaceable pattern
variables), with no warning located in either new file.  The strict LHS audit
reports zero unreviewed clauses and zero reconstructible compound slots; the
strict 1,992-check catalog, source TOC, plan-header/reference lints,
check-metrics tests, shell syntax, whitespace hygiene, and registered focused
wrapper are green.

Exact-current resumable health is green for all 146 registered targets.  The
144-target state was carried forward only after mechanically confirming the
exact old file list and byte digest
`sha256:d74dbbbb5f7546d70d0720ffaa3524bbdb185784709662962a65ade0dbcfdac4`
and unchanged Lambdapi version, timeout, warning mode, and flags.  The refresh
then ran only the new source (`5.825s`) and reviewer (`6.276s`).  Its source-
metrics snapshot is
`sha256:fc6c51ea40f4315074e5623c841d0e1945d343669f0e2dbc400f8db61bd1daeb`
and checked-content snapshot is
`sha256:e88a256d67fd9ab5e2afae2e827e8df7f94f98f1084a1cbd92f5d09eadd44104`.
No full CI, examples aggregate, root aggregate, push, merge, history rewrite,
publication, or worktree cleanup was performed.  The bounded implementation
and synchronized-plan checkpoint is `ce982e3` (`feat: add direct cover
completion HIT`).

### 13.17 CS-12d whole direct-cover algebra correction — 2026-08-03

The first eliminator audit found a real internality prerequisite in the
checkpointed direct-cover signature. Its matching argument and resulting
section were whole presheaf maps, but the operation sending one matching
family to one section was represented only at objects of the corresponding
hom-categories. That representation did not itself own the action on arrows
between matching families. Likewise, the earlier silent constructor was a
pointwise path rather than one equality of whole section endofunctors.

The exact oracle and recursor clauses in Pédrot's *Pursuing Shtuck* confirm
that this is not merely a presentation preference. The oracle is an internal
operation, its constant-family equation is part of the algebra, and the
recursor must preserve that equation through its path-constructor coherence.
The v3.2 external-site translation therefore uses the whole categories

```text
Match_R(X) = Hom_Psh(R_hat,X),
Sect_U(X)  = Hom_Psh(y(U),X)
```

and packages one cover algebra as a functor
`Match_R(X) -> Sect_U(X)` together with the whole equality
`glue o restriction = id`. This keeps matching-arrow action, ordinary
functoriality, and naturality at generic owners. Pointwise glue and silent
remain derived observations rather than competing primitive data.

The new transparent, rule-free
`emdash3_2_direct_cover_algebras.lp` has 241 lines and 11 symbols. It defines
`DirectCoverAt` and `DirectCoverAlgebra`, their whole glue/silent projections,
and the canonical forgetful map

```text
IsTopologyLocalPsh(T,X) -> DirectCoverAlgebra(T,X)
```

by selecting the existing restriction equivalence's left inverse and whole
left law. Its 109-line reviewer contains eight checks, including exact
projection computations and a negative check that oracle structure is not
definitionally identified with full topology-locality.

The migrated `emdash3_2_direct_cover_completion_hit.lp` has 203 lines and
eight symbols. The primitive completion now retains one canonical whole
`DirectCoverAlgebra`; its public glue functor and whole silent equality are
transparent projections, and the former pointwise glue/silent interfaces are
derived by functor evaluation and `eq_ap`. Its 160-line reviewer contains ten
checks, including the two existing non-collapse checks. Neither source
introduces a rewrite or unification rule.

This tranche does **not** yet cross the first sheafification integration
grade. In particular it supplies no eliminator, no preservation law for the
unit or glue constructors, no silent/path-constructor coherence, no proof of
the missing `restriction o glue = id` law, no
`IsTopologyLocalPsh` proof for the completion, no constructed sheaf object,
and no functor or adjunction. The separately supplied
`SheafificationCapability` therefore remains the active ringed-site consumer
interface. The intended relationship remains the six-grade realization
contract in Section 3.2: the categorical HIT is integrated with the fixed-site
Cat-valued core only when its local objects, whole universal property, and
functorial assembly instantiate that existing capability. Comparison with an
independently supplied capability is subsequent whole/propositional evidence,
never a conversion rule. CommRing lifting, left exactness, and
slice/base-change remain stronger downstream grades.

The next CS-12 gate is consequently the honest recursor over this whole
algebra. It must expose unit beta, whole glue preservation, and the
silent-constructor coherence before any primitive extension map is called an
eliminator. Only then should the pulled-cover/maximality argument attempt to
derive the second restriction/glue law and hence topology-locality.

Focused registered source checks are green in 8.16 and 7.81 seconds, and the
two reviewer checks are green in 7.49 and 7.48 seconds. Warning-enabled checks
of the immediate dependency, both sources, and both reviewers reproduce
exactly the inherited 1,179 warnings: 1,020 unjoinable critical pairs and 159
replaceable pattern variables. No warning is located in either direct-cover
source or reviewer. The strict LHS audit reports zero unreviewed clauses and
zero reconstructible compound slots; the strict 1,992-check catalog has zero
unclassified checks; source TOC, report-header/reference lints,
check-metrics tests, shell syntax, health-snapshot freshness, and whitespace
hygiene are green.

Exact-current resumable health is green for all 148 registered targets. The
old 146-target state was first reproduced byte-for-byte from checkpoint
`472f0bc`, including its checked-content digest
`sha256:e88a256d67fd9ab5e2afae2e827e8df7f94f98f1084a1cbd92f5d09eadd44104`.
The audit found exactly two changed old targets and two new targets, with all
144 other files and the Lambdapi/timeout/warning/flag environment unchanged.
The refresh therefore ran only the new algebra source (5.510 seconds), the
migrated completion source (5.577 seconds), the algebra reviewer (5.969
seconds), and the migrated completion reviewer (5.419 seconds). The resulting
source-metrics snapshot is
`sha256:50a0b77ef469ac17b6aa13b5637d9ecbfb435132246eaaf192c4cfafbeb4af44`
and checked-content snapshot is
`sha256:a9ed8f77040f2cd712d09c67dc7b832e6d6555eb96ff9006dbecc8d8faa53c7a`.
No full CI, examples aggregate, root aggregate, push, merge, history rewrite,
publication, or worktree cleanup was performed.
The bounded implementation and synchronized-plan checkpoint is `1b6a468`
(`feat: internalize direct cover algebra`).

### 13.18 CS-12e whole direct-cover completion recursor — 2026-08-03

The next bounded tranche promotes the recursor contract required by
CS-D-046.  For a whole presheaf map `h:X->Y`, postcomposition gives whole
functors on both section and matching hom-categories.  Their compatibility
with restriction is derived at the existing rigid simultaneous Hom action
`Hom(i_R,h)`: it is proof-time comparison between the two factorizations, not
a new runtime fold and not an externally stored naturality square.

At each cover, a `DirectCoverAlgebraMapAt` consists of one whole equality

```text
postcompose_sections(h) o glue_X
  = glue_Y o postcompose_matching(h)
```

and one higher equality between the two resulting silent paths.  The source
route whisks the source algebra's `glue_X o restriction_X = id` law by `h`.
The target route uses the whole glue-preservation square, the derived
restriction/postcomposition comparison, and the target silent law.  A
`DirectCoverAlgebraMap` quantifies this package over every covering sieve.
Thus action on matching arrows, ordinary naturality, and path coherence all
remain inside the existing functor/equality calculus; no objectwise family of
squares or component laws is added.

The runtime-beta audit refined the representation before checkpointing.
`direct_cover_completion_glue_func` is now the stable primitive whole-functor
constructor and `direct_cover_completion_silent` is its primitive whole path;
`direct_cover_completion_algebra` is assembled transparently from those two
constructors.  This preserves the whole internal algebra while avoiding a
fragile recursor rule against a nested Sigma projection.

The new `emdash3_2_direct_cover_completion_eliminator.lp` selects one
primitive whole recursor and one primitive whole algebra-map/coherence witness
for every target algebra and seed `P->Y`.  Its transparent result package and
typed observations expose:

1. the whole extension `DirectCoverCompletionPsh(T,P)->Y`;
2. judgmental beta for the whole unit map;
3. judgmental beta when that whole map is composed with a recursively glued
   section;
4. one whole glue-preservation equality at every cover; and
5. higher beta/coherence for the silent path constructor.

The unit rule is restricted to composition of the literal recursor with the
literal unit.  The recursive-glue rule is restricted to composition of that
recursor with `fapp0` of the literal primitive whole glue functor.  It sends
the whole matching map through the recursor and evaluates the target's whole
glue functor.  Thus the computational beta is not an object-only substitute
for the algebra-map law: matching-arrow action remains at the two whole glue
functors, and their preservation plus silent coherence remain first-class
internal evidence.

A transparent adapter feeds any `IsTopologyLocalPsh(T,Y)` target through the
already checkpointed `topology_local_direct_cover_algebra`; it adds no new
locality fields.  The reviewer checks both runtime betas directly, alongside
the whole glue-preservation and silent-coherence types.  An owner-position
warning-enabled probe found no new critical pair or replaceable-pattern
warning from the two rules: the warning inventory remains the inherited
1,179 total, split as 1,020 unjoinable critical pairs and 159 replaceable
pattern variables.

The migrated HIT signature is 204 lines and eight symbols.  Its 188-line
reviewer contains twelve positive/negative checks, including exact projection
of the canonical algebra back to the primitive whole glue and silent
constructors.  The eliminator is 767 lines with 21 symbols and two rules; its
204-line reviewer contains twelve checks covering the algebra-map projections,
unit/glue runtime beta, whole glue preservation, silent coherence, and the
topology-local target adapter.  Focused current health checks completed in
5.032, 5.789, 5.544, and 5.450 seconds respectively.

Strict LHS audit, source TOC, active-reference and report-header lints,
check-metrics tests, shell syntax, whitespace hygiene, and the strict
1,992-check catalog with zero unclassified checks are green.  Exact-current
resumable health is green for all 150 registered targets.  The prior tracked
148-target report was verified at checked-content digest
`sha256:a9ed8f77040f2cd712d09c67dc7b832e6d6555eb96ff9006dbecc8d8faa53c7a`;
the only changed old targets are the completion source and reviewer, while
the eliminator source and reviewer are new.  The refresh therefore carried
forward 146 byte-identical successes and ran exactly those four targets.  Its
source-metrics snapshot is
`sha256:fded4e97764696225ce62be25f1551cff831f2cbd5b3304fbb023f27d2d212c3`
and checked-content snapshot is
`sha256:b7902aa39944103d6e25fa78c7eb3a85ec0a95f65f76bf9ef99758d67976542c`.
No full CI, examples aggregate, root aggregate, push, merge, history rewrite,
publication, or worktree cleanup was performed.
The bounded implementation and synchronized-plan checkpoint is `deeab6d`
(`feat: add direct cover completion recursor`).

This tranche completes the first integration grade from Section 3.2 but does
not yet make the completion a sheaf.  In particular it does not derive the
other composite law
`restriction o glue = id`, prove `IsTopologyLocalPsh` for the completion,
establish uniqueness or the whole Hom equivalence, assemble a functor, or
instantiate `SheafificationCapability`.  The post-checkpoint audit in
CS-D-048 refines CS-D-045: the required pulled-cover argument cannot be
derived from the current external dependent Pi alone, because that signature
does not own action in its object/cover indices.  The next mathematical gate
is therefore to internalize the covering-question pullback action or select
an explicitly two-sided scoped target algebra.  Only after that interface
decision yields the other whole composite law should the constructed sheaf
package and whole Hom universality be promoted.

### 13.19 CS-12f post-recursor internality audit — 2026-08-03

The attempted next proof was intentionally audited before adding a second
inverse law.  The current `DirectCoverAlgebra(T,X)` quantifies externally over
an object, sieve, and cover witness.  For each such index it owns a whole
functor from matching maps to sections, so ordinary action on matching-family
arrows and the silent equality are internal.  It does not, however, package
the collection of covering questions itself as a presheaf/category with whole
action under a base arrow and sieve pullback.

This distinction is exactly where the compact Pédrot argument uses more than
the current signature.  In the internal oracle formulation, naturality of
the oracle with respect to question/answer reindexing says that restricting
an amalgamation is the amalgamation of the restricted matching family.  The
usual second composite law then follows from that internal naturality and the
silent equation.  With only an external dependent Pi, invoking that equality
would assume the missing result.  A componentwise family of pullback squares
would make the API externally coherent rather than repair its internal
owner, and an opaque `restriction o glue = id` field would no longer be a
derived property of the checkpointed one-sided HIT algebra.

The active CS-12 problem is therefore an interface choice, not a failed
Lambdapi encoding:

1. construct a whole internal classifier/category of covering questions and
   answers whose action is sieve pullback and matching-family reindexing, then
   formulate the oracle as a whole map over it; or
2. introduce an honestly named two-sided external cover algebra as a scoped
   target class, with a correspondingly restricted recursor and explicit
   coherence for the additional path.

The first route is the preferred reusable sheafification architecture.  The
second may be a useful bounded bridge if a concrete consumer needs the local
object immediately, but it must not be presented as a theorem from the
current `DirectCoverAlgebra`.  No source change has yet selected either route.
The existing recursor remains valid for its stated one-sided algebraic
universal property.

The audit also fixes the HIT computation policy.  HIT does not imply that
every beta law is a rewrite.  Stable data constructors may compute
judgmentally at exact eliminator/observer redexes: the current direct-cover
recursor does this for the whole unit and recursive glue, and WalkingEnd uses
the same scoped pattern.  A path constructor is represented by an equality;
its eliminator beta is normally equality or higher-equality evidence.  It
should become a rewrite only when a concrete observer gives a narrow,
terminating, confluent left-hand side.  A broad equality rewrite for silent
or amalgamation would erase the distinction between runtime normalization
and proof-time coherence and is not authorized by the word *HIT*.

### 13.20 CS-13a supplied global projective-line capability — 2026-08-03

The first projective consumer is deliberately global-first and
assumption-explicit.  The new transparent rule-free
`SuppliedProjectiveLinePresentation(K)` is the dependent total

```text
Sigma S       : BinarySiteRelativeSchemePresentation(K),
Sigma overlap : BinarySchemeChartOverlapPresentation(K,S),
                BinarySchemeLaurentOverlapPresentation(K,S,overlap).
```

The retained scheme already owns its global structure presheaf, locally
ringed capability, covering sieve, and whole affine chart realizations.  The
selected slice product supplies the literal chart intersection and both
restriction maps.  The Laurent package states that both chart rings are
one-variable polynomial algebras over a common base, that those literal maps
are localization maps at the coordinates, and that the two internally
constructed coordinate-inversion endomorphisms of the shared ring are whole
identities.  Consequently the new total needs no gluing, compatibility,
cocycle, external naturality, or disconnected overlap-isomorphism field.

Its seven symbols are ordinary transparent formation, constructor, and
projection aliases.  Canonical nested Sigma projections are used in the two
dependent endpoint types so typechecking does not search through friendly
aliases.  The 93-line source checks in 51.158 seconds.  The 76-line reviewer
contains five definitional assertions for the three retained presentations,
common base ring, and exact generic Laurent package, and checks in 56.034
seconds.  The generic Laurent reviewer already verifies the two whole
transition-identity paths on that exact retained package; repeating their
fully expanded dependent endpoints in the integration reviewer was measured
and removed because it exhausted the per-target ceiling without adding a new
boundary.

This package is the promised smallest end-to-end projective-line-style
computational capability.  It is not a closed construction of `P^1`, does not
prove that its supplied global object is non-affine, and does not implement
graded `Proj`.  The next CS-13 research tranche is an audit of the smallest
graded commutative-ring, homogeneous-localization, degree-zero, and irrelevant-
ideal substrate.  A later constructed `Proj(R[x_0,x_1])` should instantiate
the same global capability and receive a whole comparison with this supplied
boundary rather than create a competing scheme interface.

Both warning-enabled targets retain exactly the inherited 1,179-warning
inventory: 1,020 unjoinable critical-pair diagnostics and 159 replaceable-
pattern diagnostics.  The new rule-free source contributes no warning.  The
strict LHS audit, source TOC, active-reference and report-header lints,
check-metrics/source-TOC tests, shell syntax, whitespace hygiene, and strict
catalog are green.  Exact-current resumable health is green for all 152
registered targets.  The refresh carried forward the 150 byte-identical
successes from the prior exact 150-target state and ran only the two new
targets.  Its source-metrics snapshot is
`sha256:60999793a4b6b9187081bbe54f6a23a19e02a93541f8e250038cf593a245c6f5`
and checked-content snapshot is
`sha256:60dd8aa72d2e3f5dd432446757e65b1698b911cf70a79fc5f7949e65202c99b8`.
No full kernel check, examples aggregate, full CI, root aggregate, push,
merge, history rewrite, publication, or worktree cleanup was performed.
The bounded implementation and synchronized-plan checkpoint is `7241b00`
(`feat: add supplied projective line presentation`).

### 13.21 CS-12g whole internal covering questions — 2026-08-03

The preferred CS-D-048 representation has a green first implementation
boundary.  `DirectCoverQuestion_cat(K)` is the transparent total

```text
Sigma_cat(Op_cat(K), HigherSieveClassifier(K)).
```

Thus a question is a pair `(U,S)` and the canonical total arrow over
`p:V->U` carries it to `(V,p^*S)`.  The base arrow remains literally visible
through the generic Sigma projection, while higher-sieve pullback, identity,
composition, and higher action remain at the already deployed strict
classifier.  No second sieve action is introduced.

`DirectCoverQuestionEvidence(T,U,S)` retains both a proof that `S` is
ordinary and a proof that the resulting ordinary sieve is covered by `T`.
Both fields are propositions, so their dependent total is proposition-valued.
The primitive `DirectCoverQuestionEvidence_catd(T)` is one whole displayed
family over the question category.  Its only new runtime rule exposes the
fibre at a literal pair `(U,S)`.  Arbitrary arrow action and its coherence are
owned by the generic displayed-family calculus.  At a canonical pullback
arrow, `direct_cover_question_evidence_action_agrees` compares that internal
action with the explicit ordinary-sieve/topology pullback.  The comparison is
derived by uniqueness in the proposition-valued target; there is deliberately
no runtime rule that attempts to reconstruct the dependent proof fields.

The same module defines the object-level ambient extension
`FibrewiseSigma_catd(Op_cat(K),yoneda_psh(U),S)` and its whole first
projection.  At `S=sieve_higher(R)` these are definitionally the existing
`ordinary_sieve_extension_psh(R)` and
`ordinary_sieve_extension_inclusion(R)`.  This exact specialization prevents
the internal-question route from creating a competing matching-family or
restriction representation.

The 195-line source has nine public symbols and one narrowly typed fibre rule.
The 83-line reviewer has seven assertions covering proposition-valued
eligibility, explicit pullback, exact ordinary-extension specialization, the
retained base arrow, fibre computation, and proof-time action agreement.
Warning-enabled focused checks complete in 8.463 and 7.844 seconds and retain
exactly the inherited 1,179-warning inventory: 1,020 unjoinable critical-pair
diagnostics and 159 replaceable-pattern diagnostics.  The remaining audit,
catalog, source TOC, active-reference and report-header lints, focused script
tests, shell syntax, and whitespace hygiene are green.  Exact-current
resumable health is green for all 154 registered targets.  The prior
152-target content digest still matched every old target byte-for-byte, so the
refresh carried forward those 152 successes and ran only the new source and
reviewer, which completed in 5.023 and 5.201 seconds.  Its source-metrics
snapshot is
`sha256:a88e7e8906d1b1eec69537785795f8a51eee84dfc2cb385a66dea6a71e57334d`
and checked-content snapshot is
`sha256:99ac3499ba961ff52fafff818e5d28fa6d7206a9bdbf3c10a19a93ee0a44d40d`.
No full kernel check, examples aggregate, full CI, root aggregate, push,
merge, history rewrite, publication, or worktree cleanup was performed.
The bounded implementation and synchronized-plan checkpoint is `c091856`
(`feat: internalize direct cover questions`).

This tranche resolves only the question/pullback part of CS-D-048.  The next
gate is a whole functorial owner for the varying extension

```text
(U,S) |-> FibrewiseSigma_catd(Op_cat(K),yoneda_psh(U),S),
```

or a generic fibrewise-Sigma map construction sufficient to derive it.
Matching families, sections, restriction, and glue must then be lifted as
whole internal families/maps over eligible questions.  Until that succeeds,
the direct completion still has only `glue o restriction = id`; neither
`restriction o glue = id`, `IsTopologyLocalPsh`, constructed-sheaf packaging,
nor sheafification universality has been established.

### 13.22 CS-12g1 eligible-question semantic correction — 2026-08-03

The post-checkpoint audit found that the first CS-12g total was too broad.
`DirectCoverQuestionEvidence_catd(T)` was postulated over the total of every
higher sieve and every higher-sieve transformation.  An arbitrary such
transformation need not preserve pointwise subterminality or target
coverhood.  Consequently the source evidence may be inhabited while the
target evidence is empty.  Proposition-valuedness then supplies uniqueness
of two target witnesses, but it cannot manufacture the missing target
witness.  The old module typechecked because its primitive displayed family
asserted that action; that was not sufficient mathematical justification.

The corrective representation makes eligibility object data:

```text
DirectCoverQuestionData(T,U)
  = Sigma(R : Sieve(K,U), Covers_T(U,R)),

DirectCoverQuestionClassifier(T)[U]
  = Path_cat(DirectCoverQuestionData(T,U)).
```

Ordinary `Sieve` remains the pointwise-subterminal specialization of the
existing Cat-valued higher-sieve carrier.  Thus this correction does not
discard the higher representation.  It says only that ordinary
sheafification quantifies over the ordinary covered fragment and that arrows
inside its question fibres are paths, not arbitrary higher-sieve
transformations.  A future higher/lax sheaf theory may quantify over a
different higher-descent classifier and weighted cones; it should not be
obtained by silently renaming this ordinary topology interface.

One primitive whole family over `Op_cat(K)` owns the contravariant action and
all functorial/higher coherence.  Two selected semantic projections expose
the sieve and cover witness of an eligible question.  Constructor beta is
narrow, and internal Sigma-elimination/pathover theorems compare both
projections with the literal dependent-pair view.  Under base transport only
the sieve observer computes:

```text
question_sieve(p^*q)  -->  sieve_pullback(p, question_sieve(q)).
```

The cover observer of `p^*q` is already well typed at that computed sieve;
proposition uniqueness compares it with the explicit
`groth_topology_pullback` witness.  No runtime rule rebuilds dependent proof
fields.  The question extension and inclusion now route directly through the
existing ordinary-sieve extension and inclusion, so there is still one
matching/restriction representation.

Three probes determined the selected normal form:

1. a direct rule exposing the whole classifier action as `path_map_func`
   typechecked but added ten critical-pair diagnostics around generic
   functorial action;
2. a raw `sigma_Fst(fapp0(...))` commuting bridge reduced the footprint to
   one new unjoinable overlap with generic product-valued functor projection,
   but violated the preferred projection-owner boundary; and
3. the dedicated eligible-question sieve observer typechecks with the exact
   inherited warning inventory: 1,020 unjoinable critical-pair diagnostics
   and 159 replaceable-pattern diagnostics, with zero new warnings.

The corrected 237-line source has twelve public symbols and four narrow
rules.  Its 118-line reviewer has ten assertions covering literal projection
beta, internal agreement with Sigma projection, fibre computation, computing
sieve pullback, proof-time cover comparison, exact reuse of ordinary-sieve
extension/inclusion, and retention of the literal base arrow.  Focused quiet
and warning-enabled checks pass under the uniform 90-second ceiling.  Both
warning-enabled targets retain exactly the inherited 1,179-warning inventory:
1,020 unjoinable critical-pair diagnostics and 159 replaceable-pattern
diagnostics, with zero new warning.

The strict LHS audit, default kernel audit, source TOC, active-reference and
report-header lints, strict catalog check, and whitespace hygiene are green;
catalog regeneration produced no tracked change.  Exact-current registered
health is green for all 154 targets.  Because this correction replaces an
existing registered source, the exact resumable-health identity changed and
the refresh honestly reran all 154 targets rather than reusing an incompatible
state.  The corrected source and reviewer completed in 5.546 and 4.725
seconds.  The resulting source-metrics snapshot is
`sha256:6ce14e6a1deff724bf56bb009ced0bb9084dbbb4deabdaeb8f5c51170b465376`
and checked-content snapshot is
`sha256:64a2b30c14575dc2c7f768314b5a2a510c7f73fb7ff79ebcba1e6428c5fb081b`.
No separate full kernel check, examples aggregate, full CI, root aggregate,
push, merge, history rewrite, publication, or worktree cleanup was performed.
The bounded corrective implementation and synchronized-plan checkpoint is
`0257ce3` (`fix: correct direct cover question indexing`).

This correction strengthens rather than lengthens the sheafification road.
The next semantic owner is the whole varying extension over this eligible
question category, followed by internally reindexed matching and section
families and one whole glue transformation.  The decisive locality law is
still `restriction o glue = id`; after that, completion locality, constructed-
sheaf packaging, whole Hom uniqueness, and functorial reflector assembly
remain the ordered gates.  Left exactness, CommRing lifting, and higher/lax
descent are later strength, not hidden prerequisites for the first ordinary-
sieve reflector.

### 13.23 CS-12h whole varying families and internal glue — 2026-08-03

The CS-D-052 representation has a green promoted implementation.  Let
`Q=DirectCoverQuestion_cat(K,T)`.  The new whole functors have the variance

```text
Extension_T      : Op(Q) -> Psh(K),
Representable_T  : Op(Q) -> Psh(K),
Inclusion_T      : Extension_T => Representable_T.
```

At a literal question `(U,q)`, their values and component are exactly the
existing `ordinary_sieve_extension_psh(question_sieve(q))`, `y(U)`, and
`ordinary_sieve_extension_inclusion(question_sieve(q))`.  The opposite total
is essential: the canonical question arrow from `(U,q)` to its pullback over
`p:V->U` reverses to the direction in which both the pulled-back extension and
`y(V)` map into their original values.

For a fixed presheaf `X`, represented hom supplies the whole Cat-valued
families

```text
Match_X(q) = Hom_Psh(Extension_T(q),X),
Sect_X(q)  = Hom_Psh(Representable_T(q),X).
```

One displayed functor `Restriction_X : Sect_X -> Match_X` has the exact
ordinary-sieve precomposition functor as its literal component.  The direct
completion now also carries

```text
Glue_X : Match_X -> Sect_X
```

as one displayed functor over `Q`.  Its literal component is the already
deployed `direct_cover_completion_glue_func(U,R,covers)`.  Keeping that stable
component head avoids perturbing the checkpointed recursor rules, while the
new displayed owner asserts the intended question-pullback action for every
such component.  This is the precise sense in which `U`, `R`, and `covers`
have been internalized: they remain observable component data, but the
collection varies under one categorical owner rather than an external
dependent Pi plus separate naturality equations.

#### 13.23.1 The two inverse laws and the derived-locality argument

For one covering sieve `R` on `U`, write

```text
r_R : Sect_U(X)  -> Match_R(X),
g_R : Match_R(X) -> Sect_U(X).
```

The primitive `silent` constructor is the whole path

```text
g_R o r_R = id_(Sect_U(X)).
```

It says that gluing the restrictions of an already existing generated
section returns that section.  The missing law has the opposite orientation:

```text
r_R o g_R = id_(Match_R(X)).
```

It says that an arbitrary coherent matching family is recovered by
restricting its glued section.  This is the actual existence half needed to
show that the completion of an arbitrary input presheaf `P` is topology
local.  It is not the special case in which `P` is already a sheaf; that later
case concerns the unit being an equivalence or the reflector being idempotent
on local objects.

The Pédrot-style informal derivation is now sufficiently sharp to guide the
next kernel probe.  Given `m : Match_R(X)` and a member `f:V->U` of `R`:

1. pull `R` and `m` back along `f`; topology stability makes `f^*R` covering,
   and sieve closure plus `f in R` makes `f^*R` maximal;
2. the intended strict substitution law must identify the two whole routes
   `(g_R(m))|f` and `g_(f^*R)(f^*m)`; their object projections already join
   through the internal off-diagonal `tapp1*` owner, while the current
   displayed glue type retains higher arrow data and does not yet expose
   equality of the whole functors;
3. matching-family naturality identifies `f^*m` with the restrictions of the
   single component `m_f`, since at every `h:W->V` both sides are `m_(f o h)`;
4. `silent` at `(V,f^*R)` gives
   `g_(f^*R)(r_(f^*R)(m_f)) = m_f`;
5. the resulting paths for every retained member assemble internally into
   `r_R(g_R(m))=m`, and whole-functor extensionality then gives the missing
   composite-functor path.

The unit/`eta` constructor is not used in this locality proof; it is needed
for the later free/universal property over `P`.  Conversely, whole variation
of `glue` under question pullback is indispensable.  CS-D-052 correctly
places action and higher coherence in the constructor's displayed-functor
type instead of adding a family of external component squares.  CS-D-053
records the necessary qualification: the current `Functord` representation
has strict object-level naturality but retains directed higher data at the
whole-functor boundary.  Ordinary sheaf locality therefore needs the glue
constructor to inhabit an internal strict specialization whose computation
is still owned by `tapp1*`.  Neither an external square family nor an opaque
whole path is the selected interface.  This substitutional structure is
also distinct from the missing `restriction o glue = id` law itself.

This also clarifies the comparison with Quirin--Tabareau's *Lawvere--Tierney
sheafification in Homotopy Type Theory*.  Their Definition 5.5 makes the
restriction map along every dense subobject an equivalence, so both inverse
laws occur in the sheaf predicate.  Their constructed output nevertheless
derives that predicate: Section 5.2 first builds a separated reflection and
then takes a closed subobject of a known sheaf, using Lemma 5.19 and
Proposition 5.20.  The `OTid` HIT of Definition 5.13 is an ingredient in the
universal-property proof for the separated stage, not a direct
`eta/glue/silent` sheaf HIT and not a judgmental `restriction(glue(m))`
rewrite.  The present categorical construction uses a different derivation
mechanism, but follows the same discipline that locality of the constructed
output is proved rather than silently assumed.

The new `emdash3_2_direct_cover_question_families.lp` has 119 lines, six
symbols, and three narrow component rules.  Its 85-line reviewer has six
assertions for extension, representable, inclusion, matching, sections, and
restriction.  `emdash3_2_direct_cover_completion_hit.lp` gains one whole-glue
symbol and one literal-component rule; its reviewer checks both the displayed
type and exact component.  The new source/reviewer, changed HIT
source/reviewer, and unchanged downstream eliminator all pass focused quiet
checks.  Warning-enabled checks for all five targets retain exactly the
inherited 1,179-warning inventory: 1,020 unjoinable critical-pair diagnostics
and 159 replaceable-pattern diagnostics, with zero new warning.

The strict inferred-slot audits of both changed rule-owning sources report
zero unreviewed candidates, while the default kernel audit retains zero
unreviewed and 52 annotated slots across 32 intentional clauses.  Source-TOC,
active-reference, report-header, shell-syntax, focused metrics-unit-test,
diff-hygiene, and strict catalog checks are green.  The fresh registered
health pass checks all 156 source/reviewer targets with current evidence and
zero resumed result under the uniform 90-second per-target ceiling.  Its
source-metrics snapshot is
`sha256:f27342fc0b493e3562314b7f20a6c403f6b4d16219bbfcfbdda5e421b51251f1`
and its checked-content snapshot is
`sha256:fe25158a2e8e0f743297c63899e0b8b6481c6c72d5a8fa85b7554ce2a18bd060`.
No additional `make check`, `make examples`, or `make ci` aggregate was run.

This tranche intentionally stops before inventing an arbitrary action beta.
The whole owners guarantee internal action and naturality, but the extension
action on a canonical pulled-back question is still opaque.  The next proof
must first determine the smallest stable observer needed to identify that
action with postcomposition of a retained sieve member.  Only that scoped
computation should be added, if required, before attempting the Pédrot-style
derivation of `restriction o glue = id`.  External component squares or an
opaque second inverse remain rejected alternatives.  Registry, strict audit,
catalog, health, and plan synchronization are complete.  The bounded
implementation and synchronized-plan checkpoint is `98fe2c6` (`feat:
internalize direct cover glue indexing`).

### 13.24 CS-12i canonical extension pullback and strictness audit — 2026-08-03

The first post-CS-12h probe identified the exact semantic action needed at a
canonical question pullback.  For `p:V->U`, an eligible question `q` at `U`,
and a literal object `(h,member)` of the extension of the internal pullback
question at a test object `W`, the intended image is

```text
(h,member) |-> (p o h,member).
```

The deployed normal form retains the existing represented postcomposition
owner:

```text
Struct_sigma
  (into_restr_arrow(into_restr_postcompose(p,Struct_sigma(W,h))))
  member.
```

This distinction matters.  Replacing it immediately by a raw syntactic
composite would discard the stable `into_restr_postcompose` provenance and
reopen an already proof-time-only represented-Hom comparison.

Three candidate implementations were measured:

1. Folding the generic `fapp1_fapp0` action of
   `direct_cover_question_extension_func` at the exact canonical question
   arrow to a new stable whole map exceeded the uniform 90-second ceiling
   before the downstream completion import finished.  With that single fold
   disabled, the stable component and literal-pair rules pass in under ten
   seconds.  The fold is therefore rejected rather than hidden behind a
   larger timeout.
2. Defining the fibre map transparently through
   `sigma_pullback_total_func` exposed the mathematically correct construction
   but did not elaborate through the current proof-time presentation chain.
   The remaining obligations compare the represented-Hom fibre of Yoneda
   with its `Sigma_cat` presentation and compare the two totalized routes
   `postcompose o sigma_intro` and `sigma_intro o hom_postcomp`.  This is a
   useful future generic Fubini/base-change theorem, not justification for a
   broad runtime fold or a convenience unifier in the direct-cover module.
3. Keeping a stable whole presheaf map with two narrow projection betas, and
   supplying one whole equality from the opaque generic action to that map,
   is fast and type-correct.  `eq_ap` projects the whole comparison first to
   the fibre functor and then to the literal member formula.  The comparison
   is proof-time evidence and the reviewer retains an `assertnot` proving
   that the generic action has not acquired a competing runtime normal form.
   The corresponding representable action already reduces to the direct
   Yoneda action and therefore needs no new owner.

The active source now implements option 3.  It has 384 lines, thirteen
symbols, and five narrow rules.  The 222-line reviewer has twelve
assertions covering the original six family boundaries plus the canonical
whole map, fibre projection, literal pair beta, whole proof-time agreement,
derived pair path, computing Yoneda action, and the intentional generic-action
runtime non-collapse.  The source, reviewer, completion HIT, completion
eliminator, and both completion reviewers pass focused quiet checks.  The two
warning-enabled changed targets retain exactly the inherited 1,020
unjoinable-critical-pair and 159 replaceable-pattern diagnostics, with zero
new warning.  The changed source and the central kernel both retain zero
unreviewed strict inferred-slot candidates.  The already completed registered
health pass checked all 156 targets with zero failure, zero timeout, and zero
resumed result under the uniform 90-second per-target ceiling.  Its current
source snapshot is
`sha256:d24737207cb97306fc24ae272cf17dd5912ab9c35381d04a61391c0509162107`
and its checked-content snapshot is
`sha256:4fcf1cb5f592686bf0a730a1c5096ab0a3701dfdad55e04ac6fddcbb8e879bc8`.
No further aggregate is required before this bounded checkpoint.

#### 13.24.1 Whole strictness must remain internal

The audit found a more important representation distinction than the
extension formula itself.  For

```text
F : Functord(E,D)
```

the active kernel already owns the off-diagonal whole map

```text
functord_transport_func(F,p) = tapp1_fapp0(F,p).
```

Its strict Cat-valued naturality rules make the object actions of

```text
D[p] o F[x]
F[y] o E[p]
```

both reduce through that owner.  This is why no consumer should carry an
external family of object-level naturality squares.  The displayed
internal-hom layer nevertheless retains a directed cell
`fdapp1_int_cell(F,p,u)` between those object routes, and the two *whole
functors* are not definitionally equal.  The failed reflexivity probe prints
exactly the expected residual normal forms: transport-after-component and
component-after-transport.  Thus the whole
`direct_cover_completion_glue_funcd` internalizes question action and higher
coherence, but its current type alone does not provide the equality used in
step 2 of the Pédrot argument.  The current `OmegaEquivAlong Cat_cat`
locality target requires whole functor equality for both inverse laws.

Two tempting repairs were tested and rejected:

1. Postulating one whole path at every canonical pullback question makes
   `eq_ap` produce the desired component equality and checks quickly.  This
   only shows that the stronger contract is well typed.  It would still be an
   opaque sheaf-specific naturality axiom, so it is not promoted.
2. Adding two generic whole rewrite rules

   ```text
   D[p] o F[x]  -> tapp1_fapp0(F,p)
   F[y] o E[p]  -> tapp1_fapp0(F,p)
   ```

   makes both generic whole equalities provable by reflexivity and checks in
   under ten seconds.  A warning-enabled run, however, increases the inherited
   unjoinable-critical-pair inventory from 1,020 to 1,142.  More importantly,
   it silently forces every displayed functor to be whole-strict and erases
   the intentionally available lax/higher interpretation.  This broad rule
   pair is also rejected.

The selected next gate is a principled *internal strict displayed-functor
specialization* (or an equivalent strict `tapp1*` owner).  The direct glue
constructor should inhabit that specialization, and its underlying
`Functord` plus whole substitution computation should be obtained by generic
projections.  Strictness then belongs to the constructor's categorical type,
not to an external square field and not to an ad hoc rule mentioning one
matching family.  A separately named lax/higher cover completion can retain
the present directed semantics later when a consumer exists.

After that specialization, two derived ingredients still remain: the
internally coherent comparison of a pulled matching family with the
restrictions of its retained member, and the whole assembly/extensionality
step from member paths to equality of matching functors.  Pullback-along-
member maximality supplies part of that proof but does not replace either
ingredient.  The desired `restriction o glue = id` remains a theorem, not a
HIT constructor or rewrite rule.  No sheafification, locality, or right
inverse is claimed at this checkpoint.

### 13.25 CS-12j generic strict substitution and retained-member bridge — 2026-08-03

CS-D-053 is locally checkpointed at `337a638` (`feat: specify canonical
cover-extension pullback`).  The post-checkpoint strictness audit then found a
smaller generic solution than the strict displayed-functor subtype proposed
in Section 13.24.  The active `Functord` owner already has the complete
off-diagonal functor

```text
tapp1_func(F,x,y) : Hom_K(x,y) -> Functor(E[x],D[y]).
```

The two ordinary strict routes can therefore be retained as transparent whole
functors in the arrow variable,

```text
p |-> D[p] o F[x]
p |-> F[y] o E[p],
```

and compared proof-time with that one iterable owner.  Two narrow unification
rules now recognize the existing stable precomposition/postcomposition action
heads and return only the trivial constraint.  They do not orient either
route at runtime.  First-class whole paths are `eq_refl` at that proof-time
boundary, and `eq_ap` derives the fixed-arrow paths.  Their transitive
composite is the generic
`functord_transport_strict_naturality(F,p)` theorem.  The direct cover
completion specializes that theorem at the canonical internal pullback
question, yielding

```text
Section[p] o glue_q = glue_(p*q) o Matching[p]
```

as one whole internal path.  No external component square, cover-specific
unifier, or new runtime normal form is involved.

This supersedes the strict-subtype proposal in Section 13.24.1 for the current
ordinary `Functord` facade.  A genuinely lax displayed-functor classifier
would still be a distinct future interface; it is not obtained by weakening
the current strict owner.  The earlier probe that oriented both routes as
runtime rewrites remains rejected: it added 122 unjoinable critical pairs and
globally collapsed intentionally distinct higher presentations.

The identity-specialized normal form was also audited directly.  Replacing

```text
tapp1_fapp0(eta,id_x) -> tapp0_fapp0(eta,x)
```

by a proof-time unifier exposes the generic accumulation redexes, but it
removes real runtime computation.  Adding the two diagonal composition rules
and stable pre/postcomposition projection rules repairs the strict-route
probe, yet an unchanged Eckmann--Hilton consumer still requires the bare
identity component to reduce.  Repair would therefore require a broad,
constructor-by-constructor normal-form migration.  The established identity
beta is retained.  No duplicate capped `tapp1_fapp0` unifier is promoted:
evaluation of the full whole path by `eq_ap` already provides the exact capped
comparison, in accordance with the functor-level projection SOP.

The next Pédrot step needs a whole section of the sieve extension selected by
one retained member `p:V->U`.  The generic covariant Yoneda constructor already
provides it:

```text
ordinary_sieve_member_section(p,member) : y(V) -> R_hat.
```

At `h:W->V`, its internal action is the transported pair
`(p o h, transported member)`.  The only missing typing bridge was between the
two existing represented-family presentations.  An initial exact rule
mentioning `id_(Op K)` was rejected as needlessly identity-specific.  The
kernel now owns the generic proof-time duality

```text
hom_(A^op,B^op,F^op,W) = hom_con(A,W,B,F),
```

implemented as a rigid-head unifier whose constraints recover `A^op`, `B^op`,
and `F^op`.  Its pattern mentions neither an identity functor nor a
hard-coded opposite identity.  Typed reflexivity checks exercise both
equation presentations, while a negative conversion assertion proves that
the two public heads remain distinct runtime forms.  The retained-member
section then routes transparently through `fib_cov_transf`; all arrow action
and naturality remain at that generic internal owner.

The candidate factor map

```text
(p^*R)_hat -> y(V) -> R_hat
```

now forms and checks.  It is not runtime-convertible to the stable canonical
extension-pullback map.  Objectwise, the two maps differ only by the choice of
a proof in proposition-valued sieve membership, so the required pair path is
mathematically canonical.  The remaining formal boundary is stronger:
assembling those internal object paths into equality of the *whole presheaf
maps/functors*.  v3.2 has Pi funextensionality but does not presently expose a
generic strict extensionality principle for primitive `Functor`/`Functord`
objects.  This is also the later assembly boundary from all retained-member
paths to the whole equation `restriction o glue = id`.

The next tranche must therefore first test whether an existing internal
equality/hom owner can perform that assembly.  If it cannot, the design choice
is between:

1. a reusable internal strict functor-extensionality capability with its
   coherence represented by one whole owner; or
2. an honestly enriched categorical-HIT path contract that records the
   strict whole consequence required by ordinary locality.

Neither option may turn into a family of external naturality squares, a
consumer-supplied coherence field, a sheaf-specific runtime rewrite, or an
opaque assertion of the final right inverse.  A weaker directed/lax locality
notion may later use transformations rather than strict paths, but it is not a
silent replacement for the current `OmegaEquivAlong Cat_cat` target.

Focused kernel, presheaf, sieve-extension, direct-HIT, reviewer, and downstream
eliminator checks are green.  The central diagnostics pass.  The focused
warning snapshot remains exactly 1,179 inherited warnings: 1,020 unjoinable
critical pairs and 159 replaceable-pattern diagnostics.  The strict kernel
rule audit remains at zero unreviewed slots.  Catalog/health regeneration and
the local checkpoint are deliberately deferred until this bounded
extensionality decision is settled; no long aggregate was rerun.

### 13.26 CS-12k internal Pédrot sheaf package — 2026-08-03

The post-CS-12j review corrects the final paragraph of Section 13.25 without
discarding its useful generic strict-naturality work. The active obstacle was
phrased too strongly. A generic record-style functor extensionality principle

```text
(forall x, F(x)=G(x)) + externally supplied arrow compatibility  =>  F=G
```

is not the desired architecture and is no longer an active sheaf-formation
gate. Besides requiring a difficult primitive-functor equality principle, it
would encourage consumers to carry object equations and naturality squares
outside the categorical owner. That is contrary to the internality SOP and
unnecessary for the Pédrot-style algebraic definition.

The relevant `isSh` signature is already whole. For the internal category

```text
Q = DirectCoverQuestion_cat(K,T),
```

and the displayed matching and section families of one presheaf `X`, a direct-
cover sheaf structure consists of exactly

```text
glue_all : Functord_Q(Matching_X,Section_X),
silent   : glue_all o restriction_all = id_Section_X.
```

Question pullback, matching-arrow action, and their coherence are therefore
carried by `glue_all`; `silent` is one path between whole displayed functors.
Neither is an outer-LF family indexed manually by `(U,R,covers)`. Literal
cover glue and silent equations are obtained only by component projection,
with `eq_ap` observing the whole path. This use of `eq_ap` does not reconstruct
whole equality from components and introduces no external naturality square.

The new rule-free module
`emdash3_2_direct_cover_internal_sheaves.lp` implements that boundary:

1. `direct_cover_sheaf_silent_source_funcd(T,X,glue)` is the whole composite
   `glue o restriction`;
2. `direct_cover_sheaf_silent_target_funcd(T,X)` is the whole displayed
   identity;
3. `DirectCoverSheafStructure(T,X)` is their dependent Sigma package of one
   whole glue functor and one whole silent path;
4. `direct_cover_sheaf_structure_glue_func` and
   `direct_cover_sheaf_structure_silent` are literal-cover projections;
5. `direct_cover_sheaf_structure_algebra` forgets the whole internal owner to
   the older per-cover `DirectCoverAlgebra` consumed by the deployed recursor;
   ownership is not reversed; and
6. `DirectCoverSheaf(T)` is the transparent total of a presheaf and this
   structure.

The completion module now imports that semantic package. Its primitive whole
`direct_cover_completion_glue_funcd` and
`direct_cover_completion_silent_funcd` transparently construct

```text
direct_cover_completion_sheaf_structure(T,P)
  : DirectCoverSheafStructure(T,DirectCoverCompletionPsh(T,P))
```

and hence `direct_cover_completion_sheaf(T,P) : DirectCoverSheaf(T)`. The
existing `direct_cover_completion_algebra` is now obtained by forgetting from
this structure, rather than by independently reassembling primitive per-cover
fields. The completion recursor gains
`direct_cover_completion_sheaf_recursor_data`, so an internal sheaf target
enters through that one forgetful projection without restating its glue and
silent cover by cover.

This changes the status vocabulary precisely:

- the completion **is** now a syntactic internal Pédrot-style direct-cover
  sheaf;
- it is **not yet** a functorial sheafification reflector;
- it is not definitionally the supplied rigid `Sheaf_cat(K,T,Cat_cat)` facade;
- it has not yet been compared with conventional
  `IsTopologyLocalPsh(K,T,X)`, whose selected `OmegaEquivAlong Cat_cat`
  contains both composite laws;
- in particular, the opposite equation `restriction o glue = id` remains a
  later conventional-locality comparison theorem. It is not a fourth HIT
  constructor and is not required before the algebraic `DirectCoverSheaf`
  name; and
- whole Hom uniqueness/universality, functorial action on input presheaf maps,
  comparison/instantiation of `SheafificationCapability`, CommRing-valued
  lifting, and left exactness remain open.

The generic strict `tapp1_func` comparison and retained-member Yoneda section
from Section 13.25 remain useful for the eventual two-sided locality theorem.
They are no longer forced to solve generic primitive-functor extensionality as
a prerequisite for sheaf formation. The candidate retained-member factor can
be revisited only when the conventional comparison or Hom-universality proof
actually consumes it.

#### 13.26.1 Directed/pseudo fallback and univalence boundary

The current strict path presentation is working and remains selected. If a
later coherence boundary genuinely exceeds equality-path expressivity, the
fallback should be staged as follows:

1. keep all operations and coherence as whole categorical owners;
2. introduce a separately named pseudo/lax direct-cover completion rather than
   silently weakening `DirectCoverSheafStructure`;
3. where the comparison is invertible, assemble a whole natural isomorphism,
   `IsoEvidence`, or appropriate `OmegaEquiv`;
4. use scoped univalence only when the ambient category has the required
   univalence capability and an actual whole equivalence/isomorphism has been
   constructed.

Univalence does not turn an arbitrary directed arrow or noninvertible lax cell
into equality. A merely directed `silent` cell would describe a distinct
effectful/dialogue completion and may be valuable later, but it cannot be
substituted for the strict quotient path without changing the mathematical
object. Conversely, an invertible pseudo presentation may be transported to a
path at a suitably univalent boundary; this is a legitimate contingency, not
an active dependency of the current tranche.

#### 13.26.2 Validation and next gate

The new internal-sheaf source, its reviewer, the migrated completion source
and reviewer, and the downstream eliminator source and reviewer pass focused
checks under the uniform 90-second per-target ceiling. The new semantic module
is rule-free; completion still has its existing one narrow component rule,
and the eliminator retains its existing two narrow computation rules. No new
runtime rewrite, unifier, component-square field, or opaque right inverse is
introduced by this package.

Per the user's proportional-validation instruction, no kernel-wide,
examples-wide, health, CI, or repository aggregate is rerun at this boundary.
The prior exact 1,179-warning comparison and zero-unreviewed strict-rule audit
for the generic strict-naturality tranche remain the relevant unchanged
evidence; focused checks cover the new rule-free package and its direct
consumers. Static source registries and authority prose are synchronized.

The next active CS-12 gate is whole Hom uniqueness/universality for maps out of
the completion, followed by functorial assembly on presheaf arrows. Only then
should the implementation select the narrow comparison with
`IsTopologyLocalPsh`, the rigid sheaf facade, and the supplied
`SheafificationCapability`. This order preserves the computational
`eta/glue/silent` center and avoids reopening external extensionality or
unrelated generated-topology/scheme work.

### 13.27 CS-12l represented reindex accumulation and whole retained members — 2026-08-03

The conventional-locality comparison supplied the first concrete consumer
for reindexing a represented Cat-valued family.  The relevant mathematical
cut is

```text
F^*(hom_con(W,R))  ->  hom_con(W,R o Op(F)),
F^*(hom_(R,W))     ->  hom_(R o F,W).
```

An initial proof-time-only probe established the equality, but the subsequent
normal-form review identified these formulas as genuine accumulation of the
extra indexing functor into the represented diagram.  The selected kernel
contract is therefore:

1. both ordinary represented-family `Pullback_catd` formulas above are runtime
   rewrites;
2. repeated contravariant reindexing joins the existing generic pullback
   accumulation route because opposite composition and ordinary cut
   accumulation already select the same associated composite;
3. generic semantic composition and generic `Pullback_catd` along
   `Sigma_proj1_func` compare with `Sigma_proj1_pullback_catd` only at proof
   time; consumers select that stable runtime owner explicitly;
4. the stable owner's covariant and contravariant accumulated presentations
   compare by
   narrowly shaped rigid-head `unif_rule`s, not rewrites; and
5. the whole iterable Yoneda presentations
   `hom_int(A^op,B^op,F^op)` and `hom_con_int(A,B,F)` likewise compare only at
   proof time, preserving their distinct runtime action owners.

Item 3 is deliberate.  The Sigma-projection stable head owns the existing
`Pi_cat`/`Functord_cat` uncurrying bridge, `sigma_functord_sec`, displayed-cell
evaluation, and path-induction projections.  Rewriting it forward in the
covariant case erased that owner and exposed eleven additional stuck
projection peaks.  Reversing accumulated `hom_` back to the stable pullback
would defeat the selected accumulation direction.  Retaining the stable head
as an explicit consumer selection and comparing both generic Sigma-projection
presentations at proof time is the scoped normal-form boundary requested by
the review.  It removes the former competing runtime peak: a raw represented
pullback now follows represented accumulation, while a consumer needing the
Sigma projection ladder names `Sigma_proj1_pullback_catd` directly.

That migration initially exposed exactly two later subject-reduction
dependencies.  Both were the July displayed-dependent-chain rules that had
overloaded
`section_pullback_sec(Sigma_proj1_func(R),E,s)` as a displayed functor
`R ->_K E`.  A `unif_rule` cannot justify subject reduction for those runtime
betas.  The correction introduces the honestly typed whole owner

```text
section_weaken_funcd(R,E,s) : R ->_K E,
section_weaken_funcd(R,E,s)[k] = const_{R[k]}(s[k]).
```

Its base-arrow action is the existing internal action of `s` and ignores only
the new source-fibre object.  Recursive contexts now explicitly compose this
owner with `sigma_functord_sec` when they require a section over `Sigma(R)`.
Generic `section_pullback_sec` remains unchanged for arbitrary base functors
and continues to compute at literal base objects.  Thus no external
naturality field is introduced and no recursive-variable computation is
discarded; the two semantic roles are no longer conflated under one runtime
head.

All promoted LHSs match rigid heads with variables or inferred `_` slots.
Variance equations such as `B0 = Op(A)` and
`B0 = Op(Sigma(E))` occur in unifier constraint lists rather than as reducible
compound LHS patterns.  The strict inferred-slot audit reports zero
unreviewed candidates.  The superseded interim contract had 1,025 unjoinable
critical pairs, five above the inherited 1,020 because it retained the
generic-versus-specialized runtime peak.  After the two generic Sigma folds
move to proof time and displayed weakening receives its own owner, the active
warning-enabled kernel check reports 1,016: nine below the interim candidate
and four below the inherited checkpoint.  The two higher Cat-valued
`tapp0`/naturality overlaps of the weakening component are the same shaped
overlaps already present for its former `section_pullback_sec` spelling.  One
additional projection-order peak appears when both displayed families are
constant: the generic `tapp0` observation and the constant-family `fapp0`
projection select convertible values but do not currently join by rewriting.
An owner-position probe confirms that a specialized `fapp0` bridge closes
that peak and lowers the kernel count to 1,015.  It remains deliberately
unpromoted because the recursive-context and retained-member consumers need
only the whole displayed owner, and no concrete consumer presently requires
that additional compound-pattern projection.  No functionality is therefore
lost at the selected 1,016-warning boundary; warnings remain diagnostic rather
than an automatic veto.

The active warning-enabled kernel check, strict inferred-slot audit, and the
updated central diagnostic target are green.  The diagnostics retain typed
`eq_refl` controls for both generic Sigma-projection comparisons, runtime
non-collapse controls for both, generic represented accumulation controls,
the explicit weakening component, the recursive two-variable displayed
chain, and its internal base-arrow action.  This is proportional migration
evidence; no examples-wide, health, CI, or repository aggregate is rerun.

The triggering consumer is now green.  For one eligible covering question
`q`, define the whole retained-member category

```text
M_q = Sigma(Op(K), extension(q)).
```

Its objects are retained arrows and membership evidence, while its arrows
already carry postcomposition and membership transport.  One displayed map
and its Sigma total send all retained members internally to their pulled
questions.  Pulling matching, Section, restriction, glue, and silent along
that one functor preserves their whole action.

For a matching map `m : extension(q) -> X`, generic fibre covariance followed
by represented-target postcomposition constructs one displayed family of
retained-member sections.  `sigma_functord_sec` uncurries it to one section
over `M_q`; no family of per-member naturality squares is introduced.  The
actual pulled Section family and this construction family are then compared
through two whole representable diagrams:

```text
representable-through-question
  = representable-through-base-projection.
```

The equality is obtained from the already-internal total question/base path,
opposite functoriality, composition associativity, and Yoneda.  Whole
`hom_int`/`hom_con_int` duality is made first-class before whiskering, rather
than relying on transitivity of a unifier under a composite head.  Applying
`hom_con(X,-)` yields one equality of whole Cat-valued families, and a single
`ind_eq` transports the whole retained-member section into the actual pulled
Section family.  The focused consumer passes against the active kernel with
all probe-local rules removed.

This tranche does **not** yet prove `restriction o glue = id`.  It establishes
the missing internally coherent member-section prerequisite from which that
directed/right-inverse comparison can now be built.  The next tranche should
promote the retained-member construction in a dedicated direct-cover module,
then derive the whole comparison over `M_q`; it must not regress to external
component packaging or generic record-style functor extensionality.

### 13.28 CS-12m functorial retained-member sections and scoped univalence — 2026-08-04

The fixed matching map in CS-12l has now been internalized without changing
the semantic owner.  The generic kernel bridge

```text
sigma_functord_sec_func(R,D)
  : Functor(Functord_cat(R,D),
            Pi_cat(Sigma(R),Sigma_proj1_pullback_catd(R,D)))
```

has object action `FF |-> sigma_functord_sec(FF)`.  Its ordinary functor action
owns the displayed-transformation coherence; there is intentionally no new
component-square field and no bespoke arrow beta.  Composing this bridge with
the full represented-target postcomposition telescope and generic
precomposition by `fib_cov_int(extension(q))` gives one whole functor

```text
Matching_q -> Pi(M_q, pulled Section_X).
```

Thus the matching map `m` now varies internally from the start.  Literal
matching maps and retained arrows are observations of this owner rather than
indices of an external proof family.  The earlier fixed-`m` capped spelling
and the new telescope spelling are deliberately not forced to share a runtime
normal form; that projection-order comparison is proof-time evidence if a
consumer needs it.

The owner-position full-kernel candidate added no warning attributable to the
new bridge.  After promotion, the warning-enabled active kernel remains at the
selected 1,016 unjoinable-pair boundary, the strict inferred-slot audit reports
zero unreviewed clauses, the central diagnostics pass, and the retained-member
consumer passes.  The corresponding focused logs are
`logs/probes/emdash3_2-20260804-003706.log`,
`logs/probes/emdash3_2_checks-20260804-003744.log`, and
`logs/probes/psss12w_retained_member_questions-20260804-003721.log`.  No
health, examples-wide, CI, or repository aggregate was run.

The univalence boundary is now separated into two orthogonal questions:

1. **CS-12 comparison input.**  The final conventional comparison may take a
   scoped `CatIsoUnivalence` capability for the exact whole functor category
   in which `restriction o glue` and `id_Matching` are objects.  Applying
   `isotoid_cat` once to a whole `IsoEvidence` is legitimate and does not
   require proving a global closure theorem first.
2. **Later closure computation.**  Deriving that capability computationally
   from the syntactic shape of a functor category is a useful independent
   library theorem.  Its reduction behavior may be audited by category-shape
   cases later; it is not a prerequisite for the direct-cover comparison.

Likewise, componentwise invertibility must not be confused with a whole
functor-category isomorphism.  `IsoEvidence(Functor_cat(A,B),F,G)` already
means two whole transformations plus their two whole cancellation paths.
For the active v3.2 kernel, ordinary `Transf` and displayed `Functord` are
strictly natural: their directed off-diagonal projections are internal
computational presentations of the strict naturality owner, and the kernel
already exposes whole strict-naturality paths.  Therefore an internally
natural transformation with isomorphic components has a canonical natural
inverse; inverse naturality is derived algebraically from original naturality
and component cancellation rather than supplied as another field.  The
retained-member route has exactly this shape because it is generated from
whole `silent`, pullback-stability, representable/Yoneda paths, and their
internal functor action.  If a future kernel adds genuinely lax
transformations, that must use a distinct classifier or scope this assembly
theorem behind explicit strict/pseudo-invertible coherence; the future lax
case does not weaken or block the present CS-12 contract.

The active stronger goal remains the conventional one.  Derive

```text
restriction o glue = id_Matching,
```

combine it with the already implemented
`glue o restriction = id_Section`, form the existing
`OmegaEquivAlong Cat_cat`, and only then compare the constructed completion
with `IsTopologyLocalPsh` and the supplied sheaf facade.  The syntactic
`DirectCoverSheaf` remains valid before this theorem, but that weaker stopping
point is not the selected CS-12 integration boundary.

### 13.29 CS-12n direct `OmegaEquivAlong` comparison; split retraction retired — 2026-08-04

The post-CS-12m proof-design audit considered encoding matching maps as whole
sections over the retained-member total

```text
M_q = Sigma(Op(K),extension(q))
```

and then reflecting equality through a global decoder.  In abstract notation
this would have introduced an encoder `J`, a decoder `D`, and a split law
`D o J = id`.  The encoding has the standard Grothendieck--Yoneda reading

```text
Nat(extension(q),X)
  -> Pi((V,p,member) : M_q, Nat(y(V),X)),
```

so it is not mathematically spurious.  Nevertheless, a *full split
retraction* is stronger than the conventional sheaf comparison requires and
would put generic category-of-elements infrastructure on the CS-12 critical
path.  It also creates the unacceptable temptation to hide the hard step in
an opaque cancellation constant.

That full `D/J` route is therefore **retired from the active CS-12 design**.
No `sigma_sec_functord_func`, `fib_cov_eval_int`, decoder, or
`groth_yoneda_retract : D o J = id` has been added to the active kernel.  A
future generic Grothendieck--Yoneda equivalence may construct such operations
for independent consumers, but it is neither an assumption nor a dependency
of direct-cover sheafification.

The useful one-way retained-member construction is retained.  It already
provides, as whole internal owners:

1. the category of all retained members and its functor to pulled covering
   questions;
2. the constant-to-pulled-question cone;
3. the Matching and Section images of that cone;
4. the whole strict glue square over that cone;
5. its `Pi_func` image and its application to the internally constant matching
   section; and
6. one transport into the selected pulled-Section family.

The focused probe
`logs/probes/psss12w_retained_member_questions-20260804-013208.log`
typechecks this whole cone comparison.  It introduces no external component
naturality square.  A probe-only companion runtime cut also makes semantic
composition by a contravariantly represented family select the same
accumulated normal form as the already-promoted `Pullback_catd` rule.  That
candidate and the probe-only `Const_catd`/ordinary-constant comparison remain
unpromoted until owner-position warning, subject-reduction, strict-LHS, and
negative-control audits are complete.

The selected direct comparison now has the following target.  For the two
endofunctors of the matching category,

```text
F = restriction_q o glue_q,
G = id_Matching_q,
```

construct one whole strict transformation

```text
rho : Transf(F,G)
```

whose retained-member observations are derived from the whole cone equation
and the already-primitive whole silent path.  No consumer supplies naturality
of `rho`; its action must be inherited from whole internal owners.  Next equip
each fixed component of that already-whole transformation with

```text
OmegaEquivAlong Matching_q (F[m]) (G[m]) rho[m].
```

The generic strict closure to probe is consequently

```text
strict_transf_pointwise_omega_along
  (rho : Transf_A(F,G))
  (u   : Pi x : Obj(A), OmegaEquivAlong_B(F[x],G[x],rho[x]))
  : OmegaEquivAlong_(Functor_cat(A,B))(F,G,rho).
```

The first isolated contract probe is green at
`logs/probes/psss12x_strict_transf_pointwise_omega-20260804-013820.log`.
Because `Transf` has no exposed constructor, the maximally computational
probe surface consists of two primitive whole inverse transformations (one
for the selected left components and one for the selected right components),
one component beta for each, and two primitive whole cancellation-path
assemblers.  The public `strict_transf_pointwise_omega_along` result is then a
transparent application of `omega_equiv_along_intro`.  A single opaque
closure constant would use fewer declarations but would hide its inverse
components and is therefore not selected.  This probe has not been promoted:
it establishes the exact representation boundary, not yet the concrete
direct-cover consumer or an implementation theorem in the active library.

A direct univalence closure from pointwise equalities to `F = G` is not the
selected primitive.  Bare pointwise paths do not carry coherence along the
directed arrows of `A`; adding enough coherence would merely hide the same
whole natural-equivalence assembly in a stronger equality-specific axiom.
`OmegaEquivAlong` is the better owner because it retains the already-whole
forward transformation and its computational inverse observations.  After
the generic closure is available, a readable path-valued helper may be
defined transparently by packaging the fixed-forward evidence as
`OmegaEquiv` and applying the selected univalence cast.  Such a helper adds no
new primitive and removes the final one-line cast from consumers without
collapsing the directed interface into equality prematurely.

This is a generic strict-transformation theorem, not a sheaf axiom and not an
external family of naturality squares.  The whole forward transformation
`rho` supplies strict naturality.  Its pointwise inverse arrows and
cancellation laws determine the inverse components; inverse naturality is
derived algebraically from strict naturality and cancellation.  Because
ordinary `Transf` is presently primitive rather than an exposed record, the
implementation audit must say explicitly whether the closure can be defined
from existing owners or needs one new generic stable assembly owner.  If a
primitive owner is needed, its component observations and cancellation
contract must be exposed and tested; no opaque sheaf-specific inverse or
whole cancellation declaration is acceptable.

Finally, package the resulting fixed-forward evidence as a whole
`OmegaEquiv` and use the selected univalence boundary once to obtain

```text
restriction_q o glue_q = id_Matching_q.
```

Together with the existing whole silent law
`glue_q o restriction_q = id_Section_q`, this gives the conventional
`OmegaEquivAlong Cat_cat` locality interface.  This is the public CS-12
comparison target.  The next probe must first isolate construction of `rho`
and the generic strict closure; it must not revive the stronger `D o J`
retraction, pointwise record extensionality, or external commutative-square
fields.

### 13.30 CS-12o direct Sigma-section action projection — 2026-08-04

The retained-member consumer exposed one precise evaluator-ladder gap.  The
whole uncurrying owner was already present:

```text
sigma_functord_sec_func(R,D)
  : Functor(Functord_cat(R,D),Pi_cat(Sigma(R),pi1^*D)).
```

For `eta : Transfd(FF,GG)`, its generic `fapp1_fapp0` action is already one
whole transformation between `sigma_functord_sec(FF)` and
`sigma_functord_sec(GG)`.  Nothing in this tranche assembles naturality from
an external component family.  The missing operation was only the nested
component beta after that whole action had passed behind the stable section
facade:

```text
sigma_functord_sec_func[eta][(k,r)]
  -> Const_transf(eta[k][r]).
```

The `Const_transf` wrapper is semantically required: a component of the
uncurried section is represented as a transformation between terminal-indexed
constant functors in `D[k]`.  Evaluating it at the unique terminal object
recovers the displayed component `eta[k][r]` itself.

This computation does not follow from naturality alone.  It is the beta law
defining the component of the functorial lift.  Whole naturality of the
generic action then says, for every internal arrow
`a : (k,r) -> (k',r')` in `Sigma(R)`, that the two composites through
`Const_transf(eta[k][r])` and `Const_transf(eta[k'][r'])` agree.  Fibre arrows
specialize this to ordinary naturality of `eta[k]`; arrows changing the base
specialize it to the already-internal displayed naturality of `eta`.

Two owner designs were measured.  A named intermediate
`sigma_functord_sec_transfd(eta)` with a whole-action fold followed by a
component rule typechecks, but raises the active kernel warning inventory from
1,016 to 1,026.  It adds no coherence or semantic operation: it only names the
term already owned by generic action.  The selected design instead adds one
direct runtime projection at the first stable nested observer.  Its full
owner-position candidate retains exactly 1,016 warnings, zero unreviewed
strict-LHS candidates, and a negative control showing that the whole arrow is
not collapsed to an identity or another runtime presentation.

The active kernel, central diagnostics, and actual retained-member action
consumer are focused-green.  Evidence is recorded in:

```text
logs/probes/emdash3_2-20260804-053654.log
logs/probes/emdash3_2-20260804-053717.log
logs/probes/emdash3_2_checks-20260804-053735.log
logs/probes/psss12zt_sigma_functord_sec_action_consumer-20260804-053704.log
logs/probes/psss12z_retained_yoneda_recovery-20260804-053950.log
```

The last check is an important negative boundary.  The new beta does not make
the two large retained matching-functor endpoints judgmentally equal, and an
explicit whole `eq_refl` probe remains rejected.  No broader rewrite or
transitive family of convenience unifiers is justified by that failure.

The next locality step should be stated accurately.  Whole naturality data is
already carried by the retained-member cone and its generic functor actions;
the proof must select/project the resulting whole comparison arrow at the
original matching endpoint, not assemble a transformation from a bare family
of point equations.  Once that already-whole forward arrow is exposed, prove
its fixed components are `OmegaEquivAlong`, apply the strict
pointwise-to-whole closure, and use univalence once to obtain the conventional
whole functor path.  The remaining task is therefore endpoint projection and
pointwise equivalence, not reconstruction of naturality and not the retired
global `D o J` decoder.

### 13.31 CS-12p retained-member endpoint factorization — preliminary 2026-08-04

The next diagnostic sharpens what “endpoint projection” means.  There is one
important distinction between the desired comparison and the whole
retained-member naturality transformation already constructed.  The desired
owner is

```text
rho : restriction_q o glue_q => id_Matching_q.
```

The existing retained-member transformation is not yet `rho`.  For a fixed
retained member `(p:V->U,member)` it lives over the entire total category of
members of the pulled question,

```text
P_p = Sigma(W:Op(K),extension(p*q)[W]),
```

and internally compares the two sections whose literal observations are

```text
A_p,m(h,member_h) = X[h](m(p,member)),
B_p,m(h,member_h) = m(p o h,member_h).
```

This is the strict matching-family naturality needed to identify restrictions
of the retained value with the matching family pulled to `p*q`.  It is one
ingredient in the eventual component of `rho`, through the semantic chain

```text
restriction_p(glue_q(m))
  = glue_(p*q)(pull_p(m))
  = glue_(p*q)(restriction_(p*q)(m(p,member)))
  = m(p,member).
```

The three steps are respectively whole glue substitution, retained-member
naturality, and the already-whole `silent` path at the pulled question.  No
new external naturality square is required.

The immediate failure is one level earlier than this chain.  The exact
right-hand retained-member route is built by horizontally acting on the
internally Yoneda-encoded matching map along the whole retained-member cone
and then applying the identity evaluator.  The named semantic endpoint is
the ordinary pulled matching section.  In schematic notation, with `J(m)` the
internal FibCov/Yoneda encoding and `c_p` the whole cone target functor, the
missing comparison is

```text
eval(action(J(m),c_p))
  = pullback(eval(J(m)),c_p)
  = pull_p(m).
```

The second equality is already established by whole Yoneda recovery followed
by pullback.  The first is the unresolved boundary.  Lambdapi normalizes its
left endpoint through `Functor_comp_pair_func`,
`comp_prod_fapp1_fapp0`, and the stable identity evaluator, while its right
endpoint is presented through `section_pullback_sec` / `sigma_functord_sec`
and ordinary displayed-functor composition.  Even after observing one literal
pulled member, the expected `eq_refl` diagnostic does not close because these
stable heads expose only their local component betas and no whole theorem
currently relates the two association/presentation routes.

There is no known mathematical sheaf obstruction here.  The equation says
that coherent evaluation commutes with reindexing/uncurrying along the whole
cone.  A broad rewrite equating the expanded endpoints would hide that
generic theorem and is not selected.  The next probe should instead
specialize the already-whole `fdapp1_int_transfd(m)` through one whole
pulled-member evaluator.  Its source and target should be obtained as
projections of that internal owner, so that the comparison lands directly at
`restriction_(p*q)(m(p,member))` and `pull_p(m)`.  Existing `Eval_funcd`,
`Product_pair_funcd`, and displayed composition should be tried first; only a
genuinely missing generic stable projection/whole-specialization owner may be
promoted, with a narrow beta and no sheaf-specific naturality field.

Current diagnostic evidence is intentionally mixed:

- `psss12zy_retained_fdapp_whole.lp` is green and proves that
  `fdapp1_int_transfd(m)` remains one whole transformation after Sigma-section
  uncurrying;
- `psss12zz_retained_recovery_endpoint.lp` is green and proves whole recovered
  pullback equals the named `pull_p(m)` endpoint; and
- `psss12zzd_retained_recovery_endpoint_refl.lp` and
  `psss12zze_retained_recovery_component_refl.lp` are expected-negative
  diagnostics showing that the exact evaluator route is not judgmentally the
  recovered endpoint, even at one projected member.

The first generic internalization probe is now also conclusive at the type
boundary.  For fixed `E:B->Cat`, the intended whole operation is

```text
section_pullback_int(E)
  : F:Functor(A,B) ; Pi_B(E) -> Pi_A(Pullback(E,F)),
section_pullback_int(E)[F] = section_pullback_func(F,E).
```

The initial transparent target `F |-> Pi_A(E o F)` cannot own that runtime
component beta: its fibre remains under the semantic
`hom_postcomp_fapp0`/composition presentation, which is only proof-time
comparable with the stable `Pullback_catd(E,F)` endpoint required by
`section_pullback_func`.  Lambdapi therefore correctly rejects the candidate
by subject reduction; a runtime beta must not silently consume a proof-time
classifier comparison.

The revised probe gives the codomain a stable family owner whose object
projection is exactly `Pi_A(Pullback_catd(E,F))`.  With that honest target,
one whole `Functord` and the narrow component rule

```text
section_pullback_int(E)[F] -> section_pullback_func(F,E)
```

typecheck, and applying the component to `s` computes through the existing
`section_pullback_sec(F,E,s)` owner.  The focused
`psss12zzf_section_pullback_internalization.lp` target is green in about 6.5
seconds.  This is interface evidence only: it does not yet justify a new
primitive, prove that the stable target is independent structure, or connect
the owner to the retained-member consumer.

The next bounded question is therefore whether this whole operation is already
derivable from the internal action of `Pi_int_funcd`.  In particular,
`fdapp1_int_cell(Pi_int_funcd,F,E)` already projects to
`section_pullback_func(F,E)` at a fixed pair `(F,E)`.  The preferred result is
to specialize an existing whole action such as `fdapp1_int_transfd` (and its
`Eval_funcd`/`Product_pair_funcd` consumers) so that the variable `F` remains
internal and the stable target projection is inherited.  Only if that route
proves genuinely absent should a generic fixed-`E` pullback-family owner be
considered; it must remain a semantic, reusable section-pullback boundary and
not a sheaf-specific evaluator rule.

No failure above licenses a convenience unifier or a componentwise
reconstruction of naturality.  Once the endpoint bridge yields the actual
whole `rho`, define each `rho[m]` by projection from `rho`, prove its selected
`OmegaEquivAlong` evidence, and apply the strict pointwise-to-whole closure as
recorded in Section 13.29.

The subsequent bounded audit resolves the evaluator/reindexing part of this
boundary and corrects the preliminary diagnosis above.  Three increasingly
specialized whole paths now typecheck:

1. for every ordinary Cat-valued transformation `eta:P=>Q`, the two full
   naturality routes are compared to the existing `tapp1_func(eta,x,y)` owner
   while `eta` remains abstract;
2. specializing that theorem to `section_pullback_transf(F)` gives the whole
   equation

   ```text
   section_pullback(F,D) o Pi_B(eta)
     = Pi_A(F*eta) o section_pullback(F,E);
   ```

3. specializing once more to the retained-member identity evaluator gives one
   internally indexed equation over every pulled member at once,

   ```text
   pull(eval(J(m))) = eval(pull(J(m))).
   ```

The abstract-first staging is semantically significant.  If the evaluator is
substituted before selecting the generic naturality theorem, its diagonal
component computes to a stable projection head and hides the generic
`tapp1_func` pattern.  Constructing the whole generic path first and applying
`eq_ap` afterwards preserves internal naturality and requires no specialized
evaluator rule.  The focused probes
`psss12zzh_generic_transf_naturality_selection.lp`,
`psss12zzg_section_pullback_naturality.lp`, and
`psss12zzi_retained_evaluator_pullback_naturality.lp` are green in roughly
seven, seven, and eight seconds respectively.

That generic theorem does not make the two section representations
definitionally identical.  The remaining structural formula was isolated as

```text
pull_(Sigma(FF))(uncurry(GG)) = uncurry(GG o FF).
```

Two tempting runtime implementations are rejected.  Rewriting the pulled
first-projection family to the selected `Sigma_proj1_pullback_catd` family
adds two unjoinable constant-Sigma/Product critical pairs.  Rewriting
`section_pullback_sec(...,sigma_functord_sec(GG))` directly to
`sigma_functord_sec(GG o FF)` then fails subject reduction: the generic term
inhabits a generic `Pullback_catd` result family, whereas the right side
inhabits the explicitly selected stable Sigma-projection family, and those
classifiers compare only at proof time.  A stable Sigma-section-pullback owner
can state the desired beta honestly, but comparing its whole functor with the
generic pullback functor exposes the corresponding term-level adapter rather
than deriving it.  The classifier unifier is not an identity coercion on
objects.  These failed candidates remain ignored diagnostics in
`psss12zzj_retained_evaluator_endpoint_conversion.lp` and
`psss12zzk_sigma_section_pullback_owner.lp`; none is promotable.

The selected correction stays in one representation from the start and
performs substitution before uncurrying.  For displayed functors

```text
FF : R ->_K S,
GG : S ->_K E,
eta : E ->_K D,
```

ordinary categorical associativity at `Catd_cat(K)` supplies the whole path

```text
eta o (GG o FF) = (eta o GG) o FF.
```

Applying `sigma_functord_sec` to that path yields the desired equality of
whole stable sections without ever constructing the generic
`section_pullback_sec` endpoint.  In the retained consumer, take `GG=J(m)`,
`FF` to be the existing extension-pullback displayed functor, and `eta` to be
the whole identity evaluator.  The associated endpoint is literally the
already-green recovered-pullback owner; composing with whole Yoneda recovery
therefore proves

```text
eval(pull_displayed(J(m))) = pull_p(m)
```

as one equality of sections over the complete pulled-member total.  The
generic `psss12zzl_displayed_uncurry_substitution.lp` and retained
`psss12zzm_retained_displayed_endpoint.lp` probes are green in roughly seven
and three seconds.  They add no primitive, rewrite, unifier, external
naturality field, term coercion, or univalence assumption.

Consequently evaluator/reindexing is no longer the active CS-12p
obstruction.  The next bounded step is to use this stable endpoint as the
target observation of the already-internal retained-member naturality owner,
identify its other endpoint with the restriction of the retained value, and
then carry that whole comparison through glue substitution and `silent`.
This should construct the actual component of `rho`; only after that owner is
whole in both `m` and retained members should pointwise
`OmegaEquivAlong` closure be invoked.

### 13.32 CS-12q conventional locality derived from internal glue — 2026-08-04

The retained-member programme has now crossed the conventional locality gate
in focused probes.  This materially strengthens the preliminary conclusion of
Section 13.31: the obstruction was representational and is now resolved; no
new sheaf axiom, external naturality square, generic record extensionality, or
`D/J` decoder-retraction principle is needed.

The completed derivation has four semantic layers.

1. **Retained section inverse.**  For one internal eligible question
   `q=(R,covers)`, one retained member `(p:V->U,member:p in R)`, and one
   matching map `m:extension(R)->X`, the whole-section theorem is

   ```text
   X[p](glue_q(m))
     = fib_cov(X,V,m[V](p,member)).
   ```

   The proof first compares the canonical action
   `extension(p*q)->extension(q)` with its retained-member factorization,
   transports the matching map through that whole factorization, invokes the
   internally varying glue-pullback computation, and finally uses the whole
   `silent` constructor on the pulled question.  This is the content of the
   green `psss12zzx_retained_glue_silent_inverse.lp` probe.  The selected
   active interface `direct_cover_question_extension_pullback_retained_agrees`
   is a proof-time path between whole presheaf maps, never a runtime collapse
   of their two presentations.

2. **Literal component endpoints.**  Identity evaluation of the two retained
   sections yields the expected point equation

   ```text
   (restriction_q(glue_q(m)))[V](p,member)
     = m[V](p,member).
   ```

   The large exploratory `psss12zza_restriction_glue_component.lp` probe
   deliberately stages both endpoints through named whole owners.  On the
   left, whole represented-arrow action transports the glued section and
   identity evaluation recovers its value at `p`.  On the right, strict
   naturality of the represented matching section recovers `m(p,member)`.
   The public `Psh_cat` composition and active `Catd_cat` composition are
   crossed only by `psh_comp_representation_agrees`; they are not made
   runtime-identical.  Two capped proof-time action comparisons are required
   after generic projections have reduced to rigid heads:

   - `hom_int_precomp_func` versus `hom_con_int_postcomp_func`, the action
     projection of the already selected whole opposite-represented-family
     comparison; and
   - `hom_precomp_along_fapp0` versus raw `comp_fapp0`, with source, target,
     and the projected action checked in unification side conditions.

   Both candidates retain rigid outer heads and select no runtime normal form.
   Their owner-position and critical-pair audits remain mandatory before
   promotion.  The final focused component probe is green with zero warnings.

3. **Whole internal transformation and strict pointwise closure.**  Since
   `Transf` and `Transfd` are primitive classifiers, three rigid theorem
   owners expose one honest projection tower

   ```text
   rho
     : restriction_q o glue_q => id_Matching(q),
   rho[m]
     : restriction_q(glue_q(m)) => m,
   rho[m][V]
     : whole transformation between fibre functors,
   rho[m][V][(p,member)]
     -> path_to_hom(the retained component path).
   ```

   Naturality at all three layers is carried by these whole classifier
   inhabitants; no family of component squares is an input.  The constructor
   projection at `(p,member)` is the only runtime observation and it points to
   the already-derived path.  The focused
   `psss12zzb_restriction_glue_whole_transf.lp` probe is green with zero
   warnings.

   The ordinary and displayed strict pointwise-to-whole closure probes then
   assemble fixed-forward equivalences without assuming functor
   extensionality.  For an already-whole transformation `eta`, pointwise
   `OmegaEquivAlong` evidence selects inverse components.  Rigid whole inverse
   transformation owners expose those components, and two generic whole
   cancellation-path assemblers complete
   `OmegaEquivAlong(Functor_cat(...),F,G,eta)` or its `Functord_cat` analogue.
   These are generic strict-transformation boundaries: they do not accept
   external naturality equations, and they do not identify arbitrary lax
   transformations.  The ordinary `psss12x_strict_transf_pointwise_omega.lp`
   and displayed `psss12zzc_strict_transfd_pointwise_omega.lp` probes are
   green.

4. **Three-level assembly and conventional locality.**  The final
   `psss12zzd_restriction_glue_omega.lp` probe lifts the retained-member
   equivalence successively to:

   ```text
   OmegaEquivAlong(fibre functors, rho[m][V]);
   OmegaEquivAlong(Functord_cat(...), rho[m]);
   OmegaEquivAlong(Functor_cat(Matching,Matching), rho).
   ```

   Casting the last whole equivalence to an object path gives exactly

   ```text
   restriction_q o glue_q = id_Matching(q).
   ```

   This is not the rejected pointwise-equality-to-whole-equality shortcut:
   each lift consumes an already-whole transformation and constructs its
   fixed-forward equivalence.  It is also not the retired `D/J` retraction
   route and uses no category-of-elements decoder.

   Combining that second inverse with the primitive whole HIT law

   ```text
   silent_q : glue_q o restriction_q = id_Section(q)
   ```

   produces the existing public locality classifier directly:

   ```text
   PshLocalAtOrdinarySieve
     K U R (DirectCoverCompletionPsh K T P).
   ```

   Quantifying transparently over `U`, `R`, and `covers`, with
   `q=(R,covers)`, then gives

   ```text
   IsTopologyLocalPsh
     K T (DirectCoverCompletionPsh K T P).
   ```

   The complete integration probe is green under the uniform 90-second
   ceiling in about 3.5 seconds with zero warnings
   (`logs/probes/psss12zzd_restriction_glue_omega-20260804-094239.log`).

This result settles the mathematical feasibility of the direct-cover HIT's
comparison with conventional covering-sieve descent.  It does **not** yet
finish the whole sheafification programme.  The next gates are:

1. promote only the reusable and owner-minimal subset of the exploratory
   proof, with strict LHS, owner-position, warning, and negative non-collapse
   audits;
2. expose the topology-local completion as a syntactic constructed sheaf and
   compare it, under a scoped facade choice, with the existing rigid
   `Sheaf_cat`/`SheafificationCapability` interface;
3. prove whole Hom universality of `eta:P->DirectCoverCompletionPsh(P)` into
   topology-local targets and assemble the fixed-site reflector functor and
   adjunction; and
4. keep the independent computational `Proj`/projective-space lane moving
   without making it depend on reflector completion.

Promotion must not copy the entire exploratory ladder wholesale.  The active
library should retain semantic whole paths and rigid projection owners, while
temporary endpoint aliases and failed normal-form candidates remain ignored
diagnostics.  In particular, no giant endpoint unifier, no broad
`tapp1_fapp0` duplicate, no automatic Sigma eta, and no external component
coherence field is authorized by the green result.

The owner-minimal promotion now implements that decision in two new modules.

- `emdash3_2_strict_pointwise_equivalences.lp` contains the reusable ordinary
  and displayed strict pointwise-to-whole closure. Its rigid inverse owners
  compute at components; generic whole cancellation paths are the explicit
  assembly boundary forced by primitive `Transf`/`Transfd` classifiers.
- `emdash3_2_direct_cover_completion_locality.lp` contains the conventional
  restriction/glue comparison. It retains the fully audited
  retained-member equation as one opaque proof owner, projects it from one
  whole `rho`, performs the three transparent fixed-forward equivalence lifts,
  and constructs `IsTopologyLocalPsh(DirectCoverCompletionPsh)`.

The opaque retained equation is not a new recursive constructor, rewrite, or
consumer field. Equality proof terms do not carry the runtime section data;
the complete derivation from canonical pullback, matching naturality, glue,
and silent remains recorded above and executable in the ignored focused
probes. The active computational surface is the whole transformation tower,
its component beta, its selected inverse transformations, and the existing
restriction/glue functors. Replacing the opaque theorem with a shorter generic
proof term later would not change the public interface.

Both active modules pass focused owner-position checks with zero warnings.
The central diagnostics import them and verify ordinary/displayed inverse
projection, retained-member pointwise projection, the whole second-inverse
path, and topology locality
(`logs/probes/emdash3_2_checks-20260804-095428.log`). Strict LHS audits report
zero unreviewed compound slots in either new module. No aggregate health/CI
run is used at this stage; that remains reserved for the completed bounded
integration checkpoint.

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
> program from clean checkpoint `337a638` by treating
> `REPORT_EMDASH_V3_2_COMPUTATIONAL_SCHEMES_CONTINUATION_PLAN_2026-08-03.md`
> as the living implementation, decision, validation, and recovery ledger.
> Execute only its next ready bounded tranches under the active nested
> Lambdapi SOP.  On CS-12, continue the direct whole-presheaf
> `eta/glue/silent` cover completion from its internal syntactic
> `DirectCoverSheaf` package through whole Hom universality, functorial
> reflector assembly, and scoped comparison with `IsTopologyLocalPsh`, the
> rigid sheaf facade, and the existing `SheafificationCapability`; treat the
> opposite restriction/glue composite as part of that conventional comparison,
> not a prerequisite for algebraic direct-cover sheafhood. Do not call the
> resulting endofunctor a sheafification reflector before those gates or
> conflate direct HIT glue, the adjunction mate, and Cartier localization glue.
> Keep CS-13 as
> an independent active scheme lane: use a supplied global `P1` capability as
> the smallest end-to-end validation of the existing binary/Laurent owners,
> then build graded `Proj` infrastructure from which standard `P^n` is
> ultimately derived and compared wholly with the explicit `P1` boundary.
> Do not revive the frozen principal-BNat bridge, require atlas-first gluing,
> or let either research lane block the other.  Update the plan whenever
> probes refine the architecture; keep action, naturality, and coherence at
> whole internal owners; prefer computational definitions and scoped evidence
> over external component fields or broad rewrites; and reuse exact recent
> evidence rather than run long aggregates for reassurance.  Authorized local
> green checkpoints require synchronized plan/registry/health evidence.  Do
> not push, merge, publish, rebase, amend, reset, rewrite history, clean up
> worktrees, delete branches, or touch another worktree or branch.

The goal service currently has the older `3dd70fd`-worded objective active.
It has no in-place objective-edit operation while that goal remains
unfinished. The objective already delegates implementation order to this
living plan, so the corrected quoted text above is the recovery/next-launch
form while this plan owns the current `DirectCoverSheaf` boundary and detailed
acceptance gates.
