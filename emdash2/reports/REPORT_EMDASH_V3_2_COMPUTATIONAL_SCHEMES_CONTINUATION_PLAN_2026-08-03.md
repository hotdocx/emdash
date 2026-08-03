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
componentwise equations is to be added.  Restriction of `glue` along
`f:V->U` must compute through the pulled-back cover and reindexed matching
map at whole presheaf/action owners.  It must not be retained as an external
naturality square.  The eliminator into a `T`-local target `Y` should extend a
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
| Fixed-site categorical-HIT sheafification construction | First direct constructor boundary implemented; remaining reflector is research-grade but factorable | The whole-presheaf formation/unit/glue/silent signature is green. The next gate is an eliminator into topology-local targets, from which locality must be derived before syntactic sheaf packaging; functorial assembly, rigid `Sheaf_cat` realization, CommRing lift, and left exactness follow separately. |
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
| CS-13 | Selected projective-line/projective-space consumer and eventual `Proj` owner | Active scheme-lane continuation after the direct-cover signature checkpoint: first use an assumption-explicit global `P1` capability to validate the existing binary scheme and Laurent-overlap owners. General `Proj` then needs graded-ring, homogeneous-localization, degree-zero, and irrelevant-ideal infrastructure; once present it should derive the standard `P^n` examples, with a whole comparison to the earlier explicit `P1` boundary. No atlas-first gluing or BNat bridge is a prerequisite. | Representation/ambient-site audit for the selected global object and existing CS-07b/07c owners, followed by graded polynomial/localization infrastructure |
| CS-08 | Atlas-first two-affine gluing constructor | Out of current scope, not part of the global-first scheme interface | Reconsider only for a future consumer explicitly constructing a global object from independent affine pieces |
| CS-09 | Small-site restriction and affine/principal-open basis comparison | Later | Concrete small-site consumer |
| CS-10 | Semantic `Scheme_cat`, `Spec_func`, functor-of-points compact opens, and presented-scheme realization | Research continuation | Stable object/morphism interfaces, CS-06, and a genuine open classifier/comparison |
| CS-11 | Point-free support versus stalk-local-ring comparison | Later theorem | Support capability and suitable point/stalk infrastructure |
| CS-12 | Constructed native categorical-HIT/sheafification research | The topology-to-local-object tranche is checkpointed at `5e7505e`; the reusable sequential one-map HIT is checkpointed at `451db48`; the initial Pédrot-directed `eta/glue/silent` signature is checkpointed at `ce982e3`; and its whole glue-functor/silent-algebra correction plus locality-to-algebra conversion are checkpointed at `1b6a468`. The principal-BNat bridge remains frozen. | Implement the unit/glue/silent-coherent eliminator, derive the oracle-to-restriction-equivalence bridge and locality, package the constructed sheaf, and continue with whole Hom universality, functorial assembly, rigid-facade realization, CommRing lift, and left exactness |
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
> program from clean checkpoint `3dd70fd` by treating
> `REPORT_EMDASH_V3_2_COMPUTATIONAL_SCHEMES_CONTINUATION_PLAN_2026-08-03.md`
> as the living implementation, decision, validation, and recovery ledger.
> Execute only its next ready bounded tranches under the active nested
> Lambdapi SOP.  On CS-12, continue the direct whole-presheaf
> `eta/glue/silent` cover completion with an honest eliminator into
> topology-local targets, derived locality and syntactic constructed-sheaf
> packaging, whole Hom universality, functorial reflector assembly, and scoped
> instantiation/comparison of the existing `SheafificationCapability`; do not
> call the constructor sheafification before those gates or conflate direct
> HIT glue, the adjunction mate, and Cartier localization glue.  Keep CS-13 as
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

As of the `3dd70fd` checkpoint, the goal service still stores the older
unfinished objective in `paused` state.  The attempted replacement above was
rejected because the service exposes no resume/edit operation while an
unfinished goal exists.  Use the quoted objective when the product resumes or
replaces that goal.  The living plan, not the launch sentence, continues to
own the evolving task order and detailed acceptance gates.
