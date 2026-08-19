# EMDASH v3.2 Current Status And SOP

Date: 2026-05-26
Last consolidated: 2026-08-18
Status: living current-state and kernel-development authority

This report describes the active `emdash3_2.lp` architecture and the procedure
for changing it safely. It intentionally records the current selected design,
not the chronological sequence of earlier candidates. Dated implementation
plans in `reports/INDEX.md` retain decision history, rejected orientations, and
detailed probe evidence.

## Sources Of Truth

- `emdash3_2.lp`: active kernel definitions and runtime/proof-time behavior,
  including the reusable equality-local skeleton, restricted `Core₁`, and
  computational `CoreInclTransf` infrastructure.
- `emdash3_2_presheaves.lp`: one-way Cat-valued presheaf standard-library
  facade. It imports the kernel, exposes runtime object/hom projections to
  `Catd_cat(K^op)`, compares the two category heads only at proof time, and
  derives restriction from `Pullback_catd_func(Op_func(F))`. Transparent
  aliases additionally expose Yoneda, restriction-oriented arrow totals,
  conventional slices, and Cat-valued higher sieves through existing owners.
- `emdash3_2_eq1_hom_action.lp`: one-way derived native equality-valued
  hom-action, groupoidality, and structured-transport layer; it imports the
  kernel and is imported by diagnostics/examples, never by the kernel.
- `emdash3_2_eq1_evidence_property.lp`: one-way transparent native
  equality-valued evidence-property, retract-truncation, and finite-`NCat`
  object-truncation layer; it imports the kernel and hom-action extension,
  never conversely.
- `emdash3_2_sieves.lp`: downstream one-way native subterminal-category and
  ordinary-sieve layer. It imports the presheaf and equality-evidence modules,
  packages ordinary sieves as pointwise-subterminal higher sieves, and
  preserves them under the existing pullback action. It declares neither
  `Omega` nor topology.
- `emdash3_2_sites.lp`: downstream one-way direct ordinary-sieve topology
  layer. It exposes membership, a canonical maximal sieve, proposition-valued
  sieve coverages, maximality/pullback/local-character laws, named topology
  projections, and the chaotic topology. It declares no `Omega`, generated
  coverage saturation, sheafification, or descent.
- `emdash3_2_generated_topologies.lp`: downstream one-way, rule-free
  generated-topology layer. Type-valued sieve generators retain their
  presentation witnesses, while generated coverhood is the
  proposition-valued intersection of every Grothendieck topology accepting
  them. Maximality, pullback stability, and local character are inherited
  pointwise; generator inclusion and leastness compute by application. The
  module provides no inductive cover derivations, truncation/HIT, decision
  procedure, affine specialization, sheafification, or scheme.
- `emdash3_2_strict_pointwise_equivalences.lp`: generic strict
  pointwise-to-whole fixed-forward equivalence assembly for ordinary and
  displayed transformations. The forward transformation already owns
  naturality internally. Rigid inverse transformations compute to the
  selected pointwise inverse arrows, and whole cancellation paths complete
  `OmegaEquivAlong` in the corresponding functor category. The module does
  not assemble incoherent arrow families, invert arbitrary lax
  transformations, or add generic functor extensionality.
- `emdash3_2_direct_cover_completion_locality.lp`: downstream conventional
  comparison for the direct whole-presheaf cover-completion HIT. A derived
  retained-member theorem is projected through one whole transformation
  `restriction o glue => id`; strict pointwise closure supplies the second
  functor equality. Together with the HIT's whole silent law, this constructs
  `IsTopologyLocalPsh(DirectCoverCompletionPsh)`. The module does not yet
  identify the syntactic direct-cover sheaf with the rigid `Sheaf_cat` facade,
  assemble the reflector/adjunction, lift to CommRing values, or prove left
  exactness. Whole Hom universality lives in the subsequent module.
- `emdash3_2_direct_cover_completion_universality.lp`: whole
  seed-functoriality and categorical-HIT uniqueness for the direct-cover
  completion recursor. Its object projection computes to the deployed
  recursor; whole unit beta and topology-local eta are higher equality
  evidence. These assemble precomposition by the HIT unit into an
  `OmegaEquivAlong Cat_cat` on Hom categories into every topology-local
  target. The eta law is not generalized to arbitrary maps into an
  independently selected one-sided cover algebra. The module does not yet
  assemble the fixed-site reflector/adjunction, identify the rigid
  `Sheaf_cat` facade, lift to CommRing values, or prove left exactness.
- `emdash3_2_ringed_sites.lp`: downstream one-way, rule-free supplied
  reflective-sheafification layer. A rigid topology- and value-category-indexed
  sheaf classifier is paired with a transparent capability carrying whole
  inclusion and reflector functors, their adjunction, and fixed-counit
  `OmegaEquivAlong` evidence. Generic adjunction owners derive whole internal
  mate/glue maps. Its `ReflectiveCommRingedSite` specialization exposes the
  selected structure sheaf as a whole CommRing-valued presheaf through the
  inclusion. It does not construct canonical sheafification, generated
  saturation, descent or left exactness, impose a local-ring condition, or
  define a scheme.
- `emdash3_2_site_basis.lp`: downstream transparent, rule-free whole
  sheaf-basis layer. Opposite precomposition supplies restriction of
  `V`-valued presheaves along a selected base functor. A supplied sheaf
  restriction is tied to it by one `IsoEvidence` between whole composites,
  and comparison-lemma strength is retained as `OmegaEquivAlong Cat_cat`.
  Generic functor/transformation owners retain action and naturality. A
  proof-time path and derived `IsoEvidence` compare generic precomposition's
  cut normal form with direct composition without adding a runtime rule. It
  does not construct topology, continuity, sheafification, an induced slice, a
  Beck--Chevalley mate, a local-exactness witness, component squares, or a raw
  base-category equivalence.
- `emdash3_2_commutative_algebra_ringed_space_covers.lp`: downstream one-way,
  rule-free global-cover substrate. It retains a reflective CommRinged site,
  a distinguished object of its base category, and an ordinary sieve covering
  that object in the retained topology. The existing Grothendieck-stability
  owner derives covering pullbacks along every arrow, while selected sieve
  members expose their actual restriction arrows. It does not assert that a
  cover is finite or affine, impose locally-ringed support, store overlap or
  cocycle fields, define a scheme, or construct gluing.
- `emdash3_2_commutative_algebra_binary_covers.lp`: downstream transparent,
  rule-free binary cover-generation layer. Every arrow of the retained
  covering sieve carries an executable Boolean-selected chart, an actual
  factor map, and its triangle. Since both charts are already sieve members,
  these witnesses say that the two selected charts generate the retained
  covering sieve. The module constructs no second sieve, rule, unifier,
  external restriction/coherence field, affine label, locally-ringed
  condition, scheme, or gluing operation.
- `emdash3_2_commutative_algebra_ringed_space_restrictions.lp`: downstream
  one-way, rule-free whole chart-slice restriction substrate. It exposes the
  whole conventional slice-domain functor, restricts CommRing-valued
  presheaves by generic composition, and retains a supplied reflective site
  on the actual slice with one whole computational `DefIso` to the ambient
  restriction. It does not derive an induced topology or reflector, add a
  site-morphism/continuity calculus, assert affineness or locally-ringed
  support, define a scheme, or construct gluing.
- `emdash3_2_nat_arithmetic.lp`: one-way reusable Nat arithmetic/sethood
  module. It owns `nat_add`, the canonical `NatSucc_func`, the associativity
  theorem, the Unit/Empty proposition witnesses, and `nat_is_set` without
  importing the walking-HIT surface.
- `emdash3_2_finite_families.lp`: one-way reusable Nat/Sigma finite-family
  layer. It owns the right-associated length-indexed classifier,
  nil/cons/head/tail and singleton/pair observations, pointwise map, dependent
  pointwise evidence, and sethood. It declares no `Fin`, lookup,
  list/Sum/inductive interface, append, permutation quotient, rule, unifier,
  or package eta.
- `emdash3_2_commutative_algebra.lp`: one-way set-carrier commutative-ring
  object module. It separates operation data from eight sufficient law
  fields, exposes readable carrier/operation/law projections, and constructs
  the one-element zero ring. It adds no rewrite/unification rule and declares
  no ring morphism category, localization, finite-family, power, or polynomial
  interface.
- `emdash3_2_commutative_algebra_category.lp`: one-way structured morphism and
  ordinary-category layer. It proves morphism laws proposition-valued,
  morphisms set-valued, and pointwise carrier equality sufficient for full
  structured-map equality; `CommRing_cat` retains generic whole-arrow owners,
  while localization and empty-variable polynomial consumers select stable
  pointwise composition and identity comparisons. The whole invertibility-
  sieve consumer selects a carrier functor with a full Path-map hom action and
  no competing direct capped-action rule.
- `emdash3_2_commutative_algebra_finite.lp`: one-way rule-free finite-algebra
  layer. It owns finite sums/dot products, their structured-map preservation
  theorems, retained coefficient presentations of the unit ideal, and
  base-change-stable algebraic Zariski-cover presentations. It declares no
  `Spec`, localization family, coverage/topology, powers/radicals, fraction,
  polynomial, quotient, or propositional-truncation interface.
- `emdash3_2_commutative_algebra_polynomial.lp`: one-way rule-free
  universal-property layer for free commutative `R`-algebras on a variable
  classifier. It packages contractible structured extensions of base maps and
  valuations, without monomial/coefficient/quotient syntax, a concrete
  positive-variable representation, finite-index facade, unifier, or eta.
- `emdash3_2_commutative_algebra_localization.lp`: one-way localization/unit
  layer. It proves explicit inverse evidence
  proposition-valued, owns path transport and preservation by structured
  maps, and packages localization at one element by contractible pointwise
  factorization. Its universal total-element family exposes Path-valued unit
  evidence at literal ring elements, without concrete fraction, finite-family,
  polynomial, or Zariski syntax.
- `emdash3_2_commutative_algebra_localization_unit.lp`: one-way rule-free
  identity-localization layer. It constructs canonical unit evidence for one,
  proves the factorization space through the pointwise identity contractible,
  and therefore constructs the identity localization of any already-unit
  element. In particular, every ring has a selected localization at one whose
  target and carrier action compute to that ring and the identity. It adds no
  fraction representation, topology, `Spec`, or scheme.
- `emdash3_2_commutative_algebra_localization_zero.lp`: one-way rule-free
  empty-basic-open layer. It derives multiplication and negation at zero,
  proves that invertible zero forces `0=1` and contracts the carrier, and
  constructs the zero ring as the universal localization `R[1/0]`. This is a
  degenerate but computing non-identity-shaped model, not a nondegenerate
  fraction, presheaf, topology, overlap, `Spec`, or scheme interface.
- `emdash3_2_commutative_algebra_localization_idempotent.lp`: one-way
  rule-free fixed-image layer. For `e^2=e`, it constructs the set-valued ring
  `eR={x:R | e*x=x}`, makes its zero/one/addition/negation/multiplication
  compute through the subtype, and proves that `x |-> e*x` has the full
  localization universal property. The selected factor applies the original
  map to the retained underlying fixed point. This is quotient-free and may
  be nondegenerate for a supplied nontrivial idempotent.
- `emdash3_2_commutative_algebra_product.lp`: one-way rule-free componentwise
  product layer. It constructs product rings and componentwise structured maps
  with whole identity/composition paths, while leaving a primitive product
  functor facade consumer-gated.
- `emdash3_2_commutative_algebra_f2.lp`: one-way rule-free closed
  two-element-ring layer on `Bool_grpd`, with all laws proved by internal
  Boolean elimination.
- `emdash3_2_commutative_algebra_localization_split.lp`: one-way rule-free
  split-idempotent consumer. It selects `(1,0)` in a product, builds its
  fixed-image localization and affine arrow, and proves the closed `F2 x F2`
  idempotent differs from zero and one while restriction computes as
  `(x,y) |-> (x,0)`. Matching/descent, `Spec`, and schemes remain downstream.
- `emdash3_2_commutative_algebra_localization_comparison.lp`: one-way rule-free
  overlap layer. It derives unit multiplication/factor extraction, packages
  localization first at `f` and then at the image of `g`, and constructs
  canonical forward/reverse factors against localization at `f*g`. It asserts
  neither equality of chosen localization packages nor inverse laws for the
  comparison maps.
- `emdash3_2_commutative_algebra_localization_overlap.lp`: one-way rule-free
  whole-comparison layer. Contractible localization-factor uniqueness proves
  both cancellation paths for the product/iterated comparison and packages
  the forward map as `OmegaEquivAlong CommRing_cat` and `OmegaEquiv
  CommRing_cat`, without fraction syntax or package equality.
- `emdash3_2_commutative_algebra_presheaves.lp`: one-way CommRing-presheaf
  layer. It exposes transparent values, structured
  restriction maps, carrier application, explicit pointwise
  identity/composition paths, and proposition-valued invertibility support
  closed under further restriction. Pullback and Sigma-totalization through
  the selected carrier/unit families assemble that support as both a higher
  sieve and an ordinary sieve whose literal-arrow membership computes. One
  shaped proof-time represented-family comparison crosses the variance
  presentation boundary without runtime collapse. It declares no topology,
  sheaf, or ringed-site package.
- `emdash3_2_commutative_algebra_locality.lp`: one-way locality
  bridge. It views the existing semantic invertibility sieve as a cover in a
  supplied topology and uses literal membership plus a chosen localization to
  select the universal structured factor into each presheaf value, retaining
  the pointwise factor triangle. PSSS-08c0C packages those factors as one
  internal ordinary transformation over the category of support elements;
  its single component rule exposes the selected factor and generic `tapp1`
  owns naturality. Contractible-factor uniqueness separately derives the
  objectwise restriction equation as a construction audit. It claims no
  limiting/descent comparison, sheaf, ringed-site package, generated topology,
  `Spec`, or scheme.
- `emdash3_2_commutative_algebra_local_ringed_sites.lp`: downstream
  transparent, rule-free topology-local local-ring presentation. The literal
  empty sieve computes to `Empty` membership; invertible zero makes it cover.
  An invertible sum selects a covering sieve and a Boolean unit branch for
  every retained member. This witness-rich interface avoids both a raw sieve
  union and propositional truncation while retaining executable choices. It
  does not assert sheafhood, construct the automatic support laws, compare
  with stalks, classify open immersions, or define schemes.
- `emdash3_2_commutative_algebra_matching.lp`: one-way computational
  matching-family layer. It pulls the selected Path-valued carrier family over
  the category of invertibility-support elements and forms its Pi category.
  Every localization element selects one internally coherent section whose
  literal component applies the corresponding universal factor. PathLift
  supplies equality-path action. The single component rule uses the existing
  full fibre-covariance owner and adds no external naturality field. It
  supplies no inverse/glue, descent equivalence, sheafhood, limiting claim,
  generated topology, `Spec`, or scheme.
- `emdash3_2_commutative_algebra_glue.lp`: one-way rule-free whole
  Cartier-locality layer. It retains the earlier genuine glue functor and its
  point/component observations, then fixes the already-computing restriction
  functor as an `OmegaEquivAlong Cat_cat`. The selected left inverse is one
  whole glue functor with both whole composite-functor paths; evaluating those
  paths derives the earlier compatibility package. At a literal support
  member, the component endpoint observes the selected localization factor
  applied to the glued element. Generic functor action owns matching-arrow
  action; no external naturality family is stored. The sieve `D(s)` need not
  cover, so this is not ordinary covering-sieve sheaf descent or a
  stalk-local-ring theorem; generated topology, `Spec`, and schemes remain
  downstream.
- `emdash3_2_commutative_algebra_affine_glue.lp`: one-way rule-free derived
  affine consumer. For the identity CommRing presheaf on
  `Op_cat CommRing_cat`, it evaluates coherent matching sections at the
  localization-map support centre. Contractible factor uniqueness derives
  the left component law, while the universal factor to each support member
  supplies a whole Sigma arrow whose internal Pi-section action derives the
  Cartier component law. The complete selected-glue package is constructed
  for every chosen affine localization, including the closed split-idempotent
  model; equality of whole functors and ordinary sheaf descent remain open.
- `emdash3_2_commutative_algebra_affine_spec.lp`: one-way rule-free
  computational affine-chart facade. It exposes the conventional big slice
  over `Spec(R)`, its CommRing-valued coordinate presheaf, arbitrary
  structured charts and internal chart arrows, selected basic opens, and the
  product/iterated-localization overlap in both geometric directions.
  Coordinate restriction computes through the generic Sigma projection to
  the existing whole ring maps. This is not yet a small Zariski site, sheaf,
  locally ringed space, or complete scheme.
- `emdash3_2_commutative_algebra_affine_zariski.lp`: one-way rule-free
  generated-topology specialization on the big affine slice. For every
  literal chart `R -> S`, it lifts each selected localization in a finite
  Zariski presentation to a whole slice arrow, retains containment of those
  arrows as witness-rich generator data, and applies the generic
  impredicative-intersection owner. The resulting topology is lawful and least
  among topologies accepting those generators. Its exact internal composite
  endpoint makes the chart triangle reflexive, and coordinate restriction
  computes to the existing whole localization map. It introduces no Sigma
  eta, external naturality or triangle field, coverhood rule, localization
  choice, sheafification, small-site comparison, or scheme.
- `emdash3_2_commutative_algebra_affine_ringed_sites.lp`: one-way rule-free,
  assumption-explicit affine structure-sheaf layer. It consumes the exact
  internally generated big-affine Zariski topology, retains a supplied
  reflective CommRing-valued sheafification capability and one sheaf object,
  and requires a whole `DefIso` from the included structure presheaf to the
  computing affine coordinate presheaf. Readable chart components project
  the two whole transformations; they do not replace internal action or
  naturality with object-only fields. The module does not construct
  sheafification, prove localization locality or a stalk-local-ring theorem,
  compare with the small site, or package a scheme.
- `emdash3_2_commutative_algebra_affine_locality.lp`: one-way rule-free,
  assumption-explicit affine coordinate-locality layer. It requires the
  generic fixed-forward whole localization locality for every object of the
  big affine slice, every coordinate section, and every supplied localization
  package. Literal chart endpoints reduce to the retained ring and chosen
  localization, and a transparent compatibility projection serves the
  earlier component-view glue consumers. It makes no global localization
  choice, does not construct locality, and does not claim covering-sieve
  sheaf descent, stalk-local-ring structure, small-site comparison, or a
  scheme.
- `emdash3_2_commutative_algebra_affine_schemes.lp`: one-way rule-free thin
  computational affine-scheme presentation. It pairs the whole reflective
  structure-sheaf presentation with whole coordinate-localization locality;
  the base ring continues to own the big affine slice and generated topology,
  while finite atlases remain consumer data. Transparent projections expose
  the existing ringed site, whole coordinate `DefIso`, and selected locality.
  It does not construct either capability, duplicate chart/cover/overlap
  action, define general non-affine gluing, compare with the small site,
  construct stalks, or assert a stalk-local-ring theorem.
- `emdash3_2_commutative_algebra_affine_basis.lp`: downstream transparent,
  rule-free whole affine-chart realization layer. A selected whole functor
  from the big affine slice into the actual ambient slice carries the generic
  sheaf-basis equivalence, while direct presheaf restriction retains the
  computing ambient structure presheaf and one whole `DefIso` identifies it
  with an existing affine-scheme presentation. Generic `DefIso` composition
  yields the coordinate comparison. It does not construct those inputs,
  assert raw category equivalence, store local-exact/component coherence,
  transport generic glue, define a general scheme, or impose a stalk-local
  ring condition.
- `emdash3_2_commutative_algebra_affine_cover_charts.lp`: downstream
  transparent, rule-free realization of an actual global cover chart. It
  retains a supplied reflective slice, coordinate ring, existing affine
  presentation, whole affine-basis functor, and the existing whole
  `AffineBasisRealizationAlong`; the coordinate `DefIso` is derived. Readable
  observations are exposed, while dependent projection types stay at literal
  nested-Sigma endpoints and require no package eta, rule, or unifier. It
  stores no overlap/cocycle family and claims no locally-ringed scheme.
- `emdash3_2_commutative_algebra_affine_cover_presentations.lp`: downstream
  transparent, rule-free global-first binary affine-cover layer. It combines
  two charts generating the retained covering sieve with their two whole
  affine realizations. Pullbacks, overlaps, and repeated restrictions remain
  derived at the global and generic composition owners. It is a computational
  cover presentation, not a locally-ringed scheme certificate or atlas-first
  gluing constructor.
- `emdash3_2_commutative_algebra_affine_cover_refinements.lp`: downstream
  transparent, rule-free CS-07 usability consumer. For any retained sieve
  member, generation returns the existing Boolean-selected factorization;
  its side derives the selected affine generator, already-owned whole affine
  realization, and coordinate ring. It deliberately adds no duplicate
  refinement package, rule, unifier, external coherence, claim that the
  refinement itself is affine, global realization, or scheme classifier.
- `emdash3_2_commutative_algebra_locally_ringed_space_presentations.lp`:
  downstream transparent, rule-free whole-object consumer. A supplied
  reflective slice on `K/X` retains topology, sheaf semantics, and one whole
  `DefIso` to the computing ambient restriction; topology-local ring
  computation is attached to that target. Pairing it with the existing binary
  affine atlas produces the fibrewise
  `BinaryLocallyRingedAffineCoverPresentation` certificate. The supplied site
  determines admissible chart geometry; the layer adds no overlap/cocycle
  field, gluing constructor, classical-open comparison, or semantic scheme
  category.
- `emdash3_2_commutative_algebra_site_relative_schemes.lp`: downstream
  transparent, rule-free global usability layer. Its dependent total retains
  one `ReflectiveCommRingedSpaceCover` and the existing locally-ringed binary
  affine-cover certificate. Structure presheaf, restriction, selected cover,
  chart realizations, overlap compatibility, and cocycle behavior remain at
  existing whole owners. This is a site-relative computational scheme
  presentation, not atlas-first gluing, an unqualified classical or Zeuner
  scheme, or a representation-independent `Scheme_cat`.
- `emdash3_2_commutative_algebra_affine_points.lp`: one-way rule-free affine
  functor-of-points/basic-open layer. The existing Yoneda presheaf represents
  `Spec(R)`, the semantic identity-presheaf invertibility sieve is `D(f)`, and
  localization contractibility constructs a `TypeEquiv` between maps
  `R[1/f]->S` and `D(f)`-points at every test ring. Both presheaf actions stay
  at generic owners; there is no external naturality family, whole-presheaf
  equality, univalence principle, topology, sheafhood, or general scheme.
- `emdash3_2_commutative_algebra_affine_atlas.lp`: one-way rule-free concrete
  atlas layer. Complementary idempotents in `R x S` retain their selected
  binary Zariski-cover family, and their orthogonal overlap is represented by
  the computing zero localization. Internal affine chart arrows expose whole
  coordinate restrictions to the zero ring. The closed `F2 x F2` consumer is
  an atlas/glue presentation, not a sheaf theorem, locally ringed space, or
  general scheme record.
- `emdash3_2_commutative_algebra_zariski.lp`: one-way rule-free presented
  affine-Zariski layer. It retains a selected localization package for each
  generator of an algebraic cover presentation, exposes chosen basic-open
  arrows, and derives elementwise base-change factors, pointwise triangles,
  Sigma arrows, and returned pulled-back sieve membership. It makes no global
  localization choice and declares no propositional coverage/topology,
  subcanonicity, `Spec`, or scheme.
- `emdash3_2_walking_end_hit.lp`: one-way opaque one-dimensional walking-
  endomorphism directed-HIT module. It owns the opaque category/base/loop,
  explicit dimension evidence, contextual `Functord` eliminator, derived
  section/recursor views, transparent Code/power/decoder construction, the
  explicit-κ restricted-CoreIncl two-factor spiral specialization, Hom--Nat carrier
  packages, sethood, directed negative consequences, and a separate `BNat`
  consistency model. It contains no generated-word Hom or WalkingEnd-specific
  identity/composition rule.
- `emdash3_2_integer_localization.lp`: transparent rule-free Integer facade
  over the set-truncated telescope localization of Nat successor. It exposes
  zero, nonnegative and negative representatives, inverse successor and
  predecessor actions, sethood, and the set-targeted induction consumed by
  the Circle proof.
- `emdash3_2_circle_hit.lp`: one-way opaque groupoidal Circle HIT. It owns the
  base and generating equality loop, explicit one-dimensional evidence,
  unrestricted dependent elimination, judgmental point computation,
  judgmental dependent `PathOver` loop computation through the stable
  `eq_apd` owner, the universal Integer cover, and the complete encode/decode
  proof. Its ordinary `eq_ap` loop equation remains propositional. Its based
  loop type and the corresponding categorical Hom are explicitly `TypeEquiv`
  to Integer.
- `emdash3_2_groupoidal_interval_hit.lp`: one-way opaque groupoidal interval
  HIT. It owns two distinct endpoint constructors and one generating path,
  with judgmental computation at both points and on the dependent segment
  through the stable `eq_apd` owner. Constant-family recursion inherits those
  dependent betas; its ordinary `eq_ap` segment observation remains
  propositional.
- `emdash3_2_walking_interval_comparison.lp`: concrete comparison from the
  existing join-derived `WalkingArrow_cat` to `Path_cat(Interval_grpd)`. A
  whole profunctor cross cell carries `interval_seg`, the join eliminator
  gives the structural presentation, and one stable deployed unit computes at
  both endpoints while retaining first and next hom action. Generator
  agreement is scoped propositional rather than a generic join-arrow rule.
- `emdash3_2_walking_interval_restriction.lp`: transparent whole restriction
  of interval functions along that deployed unit. Endpoint readings and the
  endpoint-dependent generator `PathOver` derive from one whole functor path,
  and ordinary precomposition retains first hom action.
- `emdash3_2_walking_interval_extension.lp`: whole inverse candidate on
  WalkingArrow representations into `Path_cat(G)`. Interval recursion uses
  the two endpoint images and the selected generator; endpoint observations
  compute judgmentally, ordinary generator beta remains propositional, and
  the primitive whole owner retains first and next action.
- `emdash3_2_walking_interval_universality.lp`: rule-free whole
  mapping-object equivalence against every groupoidal target. Scoped
  categorical-HIT uniqueness supplies both whole cancellation paths and
  packages restriction as `OmegaEquivAlong Cat_cat`; point, endpoint,
  segment, and source-generator readings remain dependent projections. This
  is the completed non-endomorphism source-shape theorem reused by the generic
  recovery below.
- `emdash3_2_groupoidification_hit.lp`: category-indexed free
  groupoidification HIT. `Groupoidify(C) : Grpd` has one whole unit
  `C -> Path(Groupoidify(C))`; its recursor computes judgmentally at every
  represented source object and through `eq_apd` on every represented source
  arrow. Whole extension in the path-valued representation retains first and
  next hom action. This is formation/elimination, not source functoriality.
- `emdash3_2_groupoidification_universality.lp`: transparent whole
  restriction along the generic unit, scoped categorical-HIT beta/eta, and
  the resulting `OmegaEquivAlong Cat_cat` between groupoidal maps and
  path-valued functors for arbitrary `C : Cat` and `G : Grpd`. It declares no
  `Groupoidify_func` or adjunction.
- `emdash3_2_groupoidification_composition.lp`: rule-free explicit generic
  unit compositor for arbitrary composable arrows, recovered from the
  existing internal-action owner. The whole transformation retains one next
  action, and the compositor remains nonidentity even where historical strict
  cuts make its endpoints convertible.
- `emdash3_2_groupoidification_interval_recovery.lp`: derives mutually inverse
  maps between `Groupoidify(WalkingArrow_cat)` and `Interval_grpd` from the
  generic and completed Interval beta/eta laws. Both whole cancellations,
  pointwise quasi-inverse data, and a `TypeEquiv` are explicit; the two HIT
  classifiers are not definitionally identified.
- `emdash3_2_walking_circle_completion.lp`: transparent rule-free concrete
  comparison from WalkingEnd to Circle. It sends the directed generator and
  every Nat power to the Circle generator and its nonnegative powers, and the
  direct Circle encoder agrees with the route through WalkingEnd's Nat
  normal form. It is not a generic groupoidification reflector.
- `emdash3_2_walking_circle_restriction.lp`: transparent rule-free whole
  restriction of Circle functions along the comparison. Its stable
  precomposition owner retains first hom action; base evaluation and the
  generator `PathOver` are derived from one whole comparison.
- `emdash3_2_walking_circle_extension.lp`: whole inverse candidate on
  WalkingEnd representations into `Path_cat(G)`. Its single object rule
  computes to Circle recursion on the selected base and generator. Loop and
  first-arrow agreement remain propositional, while generic hom action stays
  iterable one dimension higher.
- `emdash3_2_walking_circle_universality.lp`: rule-free whole mapping-object
  equivalence. Two scoped categorical-HIT uniqueness paths make extension and
  restriction inverse as whole functors and package restriction as an
  `OmegaEquivAlong Cat_cat`. Dependent projections expose point and generator
  observations without adding a Circle loop rewrite.
- `emdash3_2_walking_circle_monodromy.lp`: rule-free universe-valued consumer.
  A self-equivalence supplies a univalence loop, the whole inverse builds the
  corresponding Circle family, restriction recovers the original WalkingEnd
  representation, and loop transport applies the equivalence's forward map.
  This is not a generic `Groupoidify` construction.
- `emdash3_2_groupoidal_closure.lp`: transparent rule-free representative
  closure for products. The canonical core-inclusion comparison is identity
  on objects and a split/join `TypeEquiv` on every hom carrier. Product path
  transport agrees with both sequential coordinate orders, the resulting
  diamond is coherent, and existing structured transport and `PathOut`
  induction agree with the same primitive right-`J` transport. No category-
  head rewrite, second `J`, proof-time unifier, or Gray tensor is introduced.
- `emdash3_2_path_pseudo_laxity.lp`: transparent rule-free Path realization
  of the generic normal-lax compositor. For `path_map_func(h)`, the existing
  `fapp1_compositor` is an equality between paths and `eq_sym` supplies its
  reverse. Its formal represented-action endpoints compare propositionally
  with the usual `eq_ap`/`eq_trans` formula, and its whole transformation
  retains a next-hom functor between paths-between-paths. The module adds no
  Path-specific runtime fold, proof-time rule, pseudofunctor classifier,
  inverse record, or complete coherence claim.
- `emdash3_2_gray_profiles.lp`: computational strict-functor codes, their
  retained decoder, and the selected `GrayHom_lax` strict-object/lax-arrow
  profile. Its homs reuse the ambient `Transf_cat` tower, while only decoded
  strict carriers make the existing compositor compute to identity. The
  historical global endpoint cuts remain documented pending a later staged
  migration.
- `emdash3_2_walking_arrow.lp`: transparent walking-arrow interface derived
  from `Join_cat(Terminal_cat,Terminal_cat)`. Both endpoints, the generator,
  and its next hom action are projections of existing join owners.
- `emdash3_2_gray_right_closure.lp`: one profiled right-closed slice with an
  opaque `GrayTensor_R`, whole computationally strict curry/uncurry maps,
  equality-valued beta/eta packaged by `OmegaEquivAlong Cat_cat`, and
  identity-derived coevaluation/evaluation. It does not claim the mirror
  closure or full Crans--Gray monoidal structure.
- `emdash3_2_gray_walking_square.lp`: transparent `I tensor I` boundary whose
  four vertices and both coordinate directions derive from coevaluation and
  the retained walking generator; no tensor object or arrow is postulated.
- `emdash3_2_gray_interchanger.lp`: rule-free directed interchanger. The named
  cell is the identity component of the active whole post/left laxity owner,
  its next `tapp1_func` action remains public, and the resulting direction
  confirms the `GrayHom_lax` convention. It adds no standalone square,
  endpoint bridge, rewrite, or unifier.
- `emdash3_2_truncation_reflector.lp`: classified computational homotopy-
  truncation reflector. It realizes `NType_cat(n)` through the existing
  `TruncGrpdU(n)` retained-evidence package, supplies point-computing
  restricted induction and recursion, derives map identity/composition by
  that induction, and uses the existing `path_map_func` for its iterable whole
  Hom action.
- `emdash3_2_semisimplicial_face_codes.lp`: set-classified augmented
  semi-simplex face-map codes. A native indexed skip/keep family owns raw
  structural composition; its public 0-truncation supplies sethood while
  constructors, identities, and composition still compute through the
  existing restricted recursor. It adds no proof-time unifier, internal
  semi-simplex category, join realization, representable, sieve, or Kan
  claim.
- `emdash3_2_semisimplicial_index.lp`: internal augmented semi-simplex
  category. Objects compute to finite vertex counts and Homs to discrete path
  categories of face codes. Identity is the all-keep code; category
  composition reduces at visible public truncation points through
  `face_comp`, while arbitrary composition retains the generic owner. It adds
  no unifier, degeneracy, join realization, representable, sieve, or Kan
  claim.
- `emdash3_2_simplex_shapes.lp`: ordinary Nat-indexed simplex shapes, generic
  whole join-map action, strict-profile join inclusions/maps, and the selected
  five cofaces through dimension two. Its cross datum is the target join's
  existing cross cell reindexed along both inputs; code and whole-functor
  coface equations compute without an external naturality family. It adds no
  augmented-empty realization, arbitrary face decoder, degeneracy,
  representable, sieve, or Kan claim.
- `emdash3_2_coherent_nerve_levels.lp`: variable-dimension ordinal mapping
  categories `Functor_cat(DirectedSimplex_cat(n),C)`. Its separate augmented
  vertex-count shape is empty at zero and recovers the ordinary dimension
  shape at successor levels. Generic Functor/Transf hom action remains
  iterable; no face action, whole semisimplicial nerve, recursive dependent-
  cell bridge, rule, or unifier is added.
- `emdash3_2_tetrahedron_faces.lp`: four selected strict-profile triangle
  cofaces of the ordinal tetrahedron. All six shared edges compute through
  face-code composition. The three edges inside the old triangle also agree
  as composite whole functors; the three edges involving the newly joined
  vertex remain distinct whole-functor presentations pending generic
  join-map composition. It adds no rule, unifier, generic decoder, or top
  tetrahedral cell.
- `emdash3_2_semisimplicial_diagrams.lp`: standard Yoneda semisimplices,
  groupoid-valued semisimplicial diagrams, and their levelwise path-category
  realization. Whole postcomposition remains at the raw functor-category
  owner; realized objects and maps pass through the distinct public
  `Psh_cat` projections. It adds no rule, unifier, representability claim for
  arbitrary diagrams, boundary, horn, or Kan data.
- `emdash3_2_simplex2_sieves.lp`: boundary and three horns of the standard
  two-simplex. Three omission bits compute from raw face codes and descend
  through set truncation; one kind-indexed higher-sieve owner retains generic
  action, ordinary pullback, fibrewise extension, and whole inclusion. It
  adds no generic-dimensional sieve family, degeneracy, spine, Kan condition,
  or filler.
- `emdash3_2_path_groupoid_2horn_fillers.lp`: bounded algebraic 2-nerve of a
  path groupoid. Its three horn restrictions and fillers use path
  composition/inverses, J-derived cancellation, whole function section paths,
  and iterable Path-map lifts. It also exposes generic presheaf-facing horn
  restriction, but does not identify the algebraic carriers with full mapping
  categories or claim an all-dimensional nerve/Kan theorem.
- `emdash3_2_semisimplicial_decalage.lp`: categorical decalage through the
  vertex-appending endofunctor of the internal semi-simplex category. Whole
  base and cone-tip transformations retain generic naturality; presheaf
  restriction shifts levels, and a fixed-tip levelwise `HFiber` has an
  iterable Path-map to its opposite base. A varying-`HFiber` Catd/total
  Path-family owner is not yet active, so no whole displayed semisimplicial
  object or `homd_` comparison is claimed.
- `emdash3_2_circle_connectedness.lp`: transparent rule-free propositional-
  truncation consumer. It constructs
  `Pi x:S1, ||circle_base=x||_{-1}` by dependent Circle induction; the retained
  proposition evidence supplies the generating-loop `PathOver`, so the result
  proves mere connectedness without choosing an untruncated global based path.
  Restricted elimination first turns each merely inhabited based-path fibre
  into a path in `Trunc_grpd(0,Circle_grpd)` and then contracts every point of
  that set truncation. The resulting `IsContr` evidence does not rewrite the
  carrier to `Unit_grpd`. The exact current cross-module health boundary is
  recorded in the validation section below; the focused plans retain their
  historical warning, rule-audit, catalog, and snapshot evidence.
- `emdash3_2_checks.lp`: executable diagnostics and regressions.
- `EMDASH_FOUNDATIONS.md`: mathematical reading guide.
- `REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`: notation
  authority for comments, examples, and future parser work.
- `INDEX.md`: active plans, completed decision records, audits, and generated
  reports.
- `../../docs/TYPESCRIPT_ELABORATOR_V3_2_MASTER_PLAN.md`: active cross-layer
  implementation ledger for the TypeScript elaborator/candidate product
  kernel. It is subordinate to these mathematical sources for every active
  owner and rule.
- `../../docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`: repository-wide
  checkpoint and recovery workflow for explicitly authorized long-running
  implementation goals. It does not relax this SOP.
- `../book/book.json` and `../book/evidence.json`: book source
  ordering/metadata and prose-to-check traceability. They govern the book
  artifact but never override active Lambdapi declarations.
- `REPORT_EMDASH_V3_2_FUNCTORIAL_TYPE_THEORY_BOOK_ARCHITECTURE_PLAN_2026-07-20.md`:
  completed book architecture and implementation ledger.
- `../../docs/EMDASH_BOOK_V3_2_GROUPOIDAL_REALIZATION_EXPANSION_PLAN_2026-08-18.md`:
  completed fourth-spiral book/article and local-release ledger.
- `REPORT_EMDASH_V3_2_AUTONOMOUS_MAINTENANCE_AND_EVOLUTION_PLAN_2026-07-22.md`:
  current cross-project maintenance, triage, and evolution ledger.
- `REPORT_EMDASH_CHECK_CATALOG.md`: generated map of the diagnostic suite.
- `REPORT_EMDASH_HEALTH.md`: generated source metrics and bounded timings.

The active source outranks every report if they disagree. Correct the report
as part of the same maintenance task rather than preserving a known stale
description.

Ignored `.scratchpad/` material is historical recovery data, not a normal
authority. Use the v2 retirement audit when an obsolete-baseline summary is
needed.

## Validated Current Baseline

The current architecture is the native-only baseline closed by P10–P12 of the
completed path-action and compatibility-retirement plan. The former 2,751-line
D0/D1/decoder compatibility module and its seven explicit reviewer clients
are deleted. Active `.lp` sources contain no D0/D1 declaration, reference, or
compatibility import (retirement comments may name them), and the exact legacy
`one_cat_iso_type_equiv` is absent. Native
`OneCat`, hom discreteness/action, finite-dimensional truncation, the one-way
ordinary-isomorphism lift, WalkingEnd/`BNat`, and Nat remain selected.

P9's owner-position deletion probe, promoted bounded active check, and focused
canonical path-category example pass. The generic `PathActionRefinement`
surface, its Nat and PathRecord wrappers, the comparison-only Nat basis, and
the isolated Sum former/action experiment are absent from active `.lp`
sources. Canonical nondependent action is
`fapp1_fapp0(path_map_func(f),p)`, which reduces to `eq_ap(f,p)`; the uncapped
next-hom functor remains available through `fapp1_func`, and dependent witness
transport remains direct `eq_apd`. That dependent action is now an injective
stable owner with its generic reflexive beta; `eq_apd_ind_eqr_path` derives
its agreement with the former transparent J expansion. This makes selected
higher-constructor computation possible without adding a second equality
eliminator.

After compatibility deletion, an exact collision manifest found zero conflict
between the stripped native declarations and existing unsuffixed declarations.
The synchronized token migration mapped 1,570 occurrences of 143 distinct
`NAME_EQ1` identifiers across 18 retained `.lp` files to `NAME`, including 139
implementation declarations and one reviewer-local declaration. The active
API is now solely the unsuffixed native equality-valued representation; no
reverse alias, partial suffixed namespace, semantic rule change, or module
rename was introduced. Bounded `make check` passes after both deletion and
rename.

The 2026-08-01 synchronized PSSS-06b candidate baseline is:

```text
make check                         pass
make examples                      pass
make health                        pass (52 measured targets, 281.632s)
make ci                            pass (52 Lambdapi targets, 241.466s)
diagnostic checks                1,796 (1,604 assert + 192 assertnot)
catalog areas                       69
legacy/unclassified checks          0 / 0
strict LHS audit                    0 unreviewed candidates
intentional LHS annotations        52 slots across 32 clauses
warning inventory               1,179
  unjoinable critical pairs       1,020
  replaceable pattern variables     159
source TOC                          86 parent-correct/sequential headings
```

The unchanged kernel source is 19,736 lines with 765 source-level symbol
declarations, 626 source-level rewrite-rule commands, and 61 unification-rule
commands. `emdash3_2_presheaves.lp` is 174 lines with 14 symbol declarations,
two runtime projection rules, and one unification rule;
`emdash3_2_sieves.lp` is 201 lines with 16 symbol declarations and no rewrite
or unification rule; and `emdash3_2_sites.lp` is 303 lines with 25 symbol
declarations and no rewrite or unification rule. The sites module packages
ordinary-sieve membership, maximality, pullback stability, local character,
and the generic chaotic topology without binding `Omega` or adding generated
coverage saturation.
`emdash3_2_commutative_algebra.lp` is 453 lines with 48 symbol declarations
and no rewrite or unification rule. It packages a `SetU_grpd` carrier, five
operations, eight sufficient commutative-ring laws, readable observations,
and the concrete one-element zero ring. The downstream
`emdash3_2_commutative_algebra_category.lp` is now 502 lines with 32 symbol
declarations, two category projection rules, and no unification rule. It
packages five-field structured ring morphisms, proves their law evidence a
property and their total classifier a set, adds the localization-consumer-
justified pointwise extensionality theorem, and exposes `CommRing_cat` without
a carrier functor or localization package. The downstream rule-free
`emdash3_2_commutative_algebra_localization.lp` is 626 lines with 31 symbol
declarations and no rewrite or unification rule. It owns proposition-valued
unit evidence and contractible pointwise factorization at one selected
element.
The source/example portion of the generated health report is fresh at
`sha256:7344886d649c97bd34312ee60a11632a9502149c860d6093d4a855a9471ed880`;
the fingerprint intentionally excludes volatile timings. P10–P12 remain
closed, and current PSSS work is owned by the living presheaves/sites/schemes
plan indexed below. PSSS-01 through PSSS-04a are green and included in the
authorized local foundation checkpoint. The subsequent PSSS-05a
sieve-descent research
probe is not active source. It now avoids the mixed
pullback-family/`Functor_catd` cast: a profunctor-native canonical cell reduces
at `(V,f,r)` to `P[f]`, is curried to the matching-data boundary, and anchors
the selected weighted comparison by explicit identity-restriction agreement.
A terminal-site/maximal-sieve API consumer is nonempty but supplies its
comparison and agreement as named assumptions. A later warning-neutral rigid-
adapter trial was rejected and removed before checkpointing: it made a
semantic alias rigid only to capture an order-sensitive proof-time comparison
and then encoded the missing agreement as a rewrite. Promotion therefore
remains gated on terminal-map uniqueness/contractibility or another derived
nonempty semantic consumer, not on adding a broad family eta rule.
Independent PSSS-06a is green through full integration CI. PSSS-06b now adds
the separately measured morphism/category layer without depending on the
parked descent probe. Its focused source/reviewer, maintained aggregate,
warning, audit, catalog, 52-target health, and full integration CI gates are
green. PSSS-07a now has its focused source/reviewer/central checks, inherited
warning comparison, zero-clause strict audit, 1,808-check catalog, and
54-target health plus full integration CI green. PSSS-07b is green through
full integration CI. PSSS-07c now has promoted candidate finite-family and
finite-algebra sources, a focused reviewer and central diagnostics, inherited
warnings, zero-clause module audits, maintained `make check`/`make examples`,
and a fresh strict 1,842-check catalog. All 59 health targets pass in 202.751
seconds at source snapshot
`sha256:4127068d1fa2e3dd43f22c8ca1f607d07bb8645ba1467ee22c96425c23ee5f76`;
authority routing is synchronized, and full integration CI passes all 59
Lambdapi targets in 216.912 seconds plus the complete repository-level tail.
The tranche is included in the authorized local foundation checkpoint.
PSSS-07d now adds the stable pointwise identity selected by the generic
`R[Empty]=R` consumer, a 432-line/24-symbol rule-free polynomial universal-
property module, and a 429-line reviewer with 16 positive and two negative
checks. Focused source/reviewer/central, warning/audit, maintained aggregate,
strict 1,860-check/73-area catalog, and authority-synchronization gates are
green. Health passes all 61 source/example targets in 314.231 seconds at
source snapshot
`sha256:35a1d735feeea679e12e62b3bc14690783758c0da59ed1e8f20522f898f075df`;
full integration CI passes all 61 Lambdapi targets in 389.345 seconds. The
final combined checkpoint gate, after the rejected descent adapter was
removed, passes all 61 targets in 342.266 seconds plus 39 Python tests, five
document-registry tests, and the complete repository-integrity tail. The carrier
functor, comparison inverse laws, concrete positive-variable polynomial
representations, relative radical/basic-open data, and geometric Zariski
topology remain separately gated.

PSSS-08a is now an implementation candidate green through maintained
aggregates, exact warning comparison, strict audits, catalog, health, and full
integration CI. The
283-line rule-free
`emdash3_2_commutative_algebra_presheaves.lp` module transparently presents
functors from `K^op` to `CommRing_cat`, applies their actual structured
restriction maps to sections, proves identity/composite restriction paths
through the selected pointwise ring-map views, and exposes proposition-valued
unit support along arrows with downward closure. The generic narrow
opposite-source projection-order bridge selects the whole
`CommRing_cat` identity after opposite identity canonicalizes, while the
rule-free theorem `fapp1_id_path` preserves the same boundary as typed proof
evidence. Carrier application of that generic identity remains opaque; the
selected pointwise identity path supplies the explicit carrier observation.
Generic unit path transport and
structured-map preservation have moved unchanged from the comparison module
to the base localization/unit owner. A 217-line reviewer constructs
invertibility evidence at every arrow of the constant zero-ring presheaf.
Whole-sieve assembly, a carrier functor, topology, sheafhood, and ringed-site
packaging remain separately gated. The strict catalog has 1,874 checks across
74 areas; all 63 health targets pass in 410.967 seconds at source snapshot
`sha256:63b1c75554b4360f042aabc955243ddc96bad42a9df1848be3fd42c61cd40b03`.
Full integration CI passes all 63 Lambdapi targets in 548.573 seconds plus the
complete repository-integrity tail. The tranche is included in the authorized
local PSSS-08a checkpoint.

PSSS-08b selects the full-action ring-carrier functor and assembles the
ordinary invertibility sieve without a direct capped carrier rule or Sigma
eta. Literal `SieveMembership` computes to
the PSSS-08a arrowwise unit predicate, and the constant zero-ring presheaf
supplies an inhabitant at every arrow. Focused and maintained source/reviewer
aggregates are green; the owning-position warning log inherits exactly
`1179 = 1020 + 159` with no changed-module warning location; strict audits
have zero unreviewed candidates. The catalog has 1,893 checks across 75 areas,
including 19 PSSS-08b checks. Health passes all 63 targets in 437.026 seconds
at source snapshot
`sha256:5a969bf2de9ebccd9ff02739dae4964f5314312e1199eb7fba9983ba21c294e3`.
Full integration CI passes all 63 Lambdapi targets in 355.987 seconds,
followed by 39 Python tests, five document-registry tests, and the complete
repository-integrity tail. The tranche is included in the authorized local
PSSS-08b checkpoint.

The old two-sided OneCat theorem was meaningful but had no selected practical
consumer and depended on the retired representation. It was deleted rather
than weakened or re-proved as a cleanup prerequisite. A fully native
object-equality/ordinary-isomorphism equivalence remains optional future work.

Detailed Phase-5/D0/D1 passages in the historical appendix are retained only as
pre-retirement implementation history. Wherever they describe a D0/D1 owner,
compatibility module, suffixed native spelling, or legacy OneCat theorem as
current, this P10/P11 checkpoint supersedes the source-location/status claim.
They are not implementation authorities and must not be used to restore a
retired symbol.

## Historical Checkpoint Appendix

The material from here to `Current Architecture` records dated measurements,
failed candidates, and superseded promotion states. It is provenance only;
the baseline above and the later current-architecture/SOP sections are the
forward authority. New chronological checkpoints belong in their task plan,
not in this appendix.

An earlier fully synchronized 2026-07-18 baseline was:

```text
make check                         pass
make examples                      pass
make ci                            pass
checked files/examples            55
diagnostic checks                1,980 (1,741 assert + 239 assertnot)
unclassified checks                0
strict LHS audit                   0 unreviewed candidates
intentional LHS annotations        45 slots across 27 clauses
warning inventory                  1,128
  unjoinable critical pairs          971
  replaceable pattern variables      157
```

The strict 2026-07-19 walking-HIT slice is implemented through G6 and has
passed bounded kernel, Nat, walking-module, complete diagnostic, and full
reviewer checks. Its measured kernel inventory is `984/159`; the walking owner
is `995/159`; both strict audits have zero unreviewed clauses with 45 annotated
slots across 27 clauses. The refreshed catalog has 2,050 checks
(1,804 `assert` plus 246 `assertnot`) across 76 areas with zero unclassified
checks. Generated health is synchronized; warning checking confirms the
kernel `984/159` inventory; and full local CI passes across 55 files in
320.238s. The walking plan is complete through G8 at its selected practical
boundary. These figures are the pre-redesign fallback baseline.

The post-G8 restricted-CoreIncl redesign resumed from
`851e85b1249aaa120df8492de7ad9506b871ccdc` and now replaces, rather than sits
beside, the former strict Core-inclusion implementation. Kernel section 20
supplies recursive `EqSkeleton_cat`, simultaneous functor action, recursive
inclusion, `Cat1Eq_cat`, `Core1_func`, and computational `CoreInclTransf`.
`CoreInclTransf` computes at its object, full first-hom, and capped first-hom
projections. Its capped value at a functor is the common diagonal
`Core(C) → D`; the separate explicit `core_incl_transf_kappa` square has
non-convertible boundary functors and computes through point, full
off-diagonal, and capped off-diagonal projections inherited from that diagonal.

`core_incl_transf_kappa_left` is actual generic functor precomposition of κ,
followed by narrow equality-induced source/target adjustments for associativity
and the readable semantic `PathLift` presentation. No Core-specific fusion
rewrite, redesign-specific `unif_rule`, or global associativity rule is used.
The right comparison is judgmentally identity and remains checked separately;
`path_lift_non_strict_spiral` therefore uses the minimal
`PathLift(h) ∘ κₗ` composite. The WalkingEnd specialization and contextual
decoder consume this selected spiral. The two old strict Core rewrites, their
two identity-transfor helpers, and `walking_power_spiral_natsucc` are deleted;
they are retained only in git history and the dated plan's historical record.

The replacement passes bounded kernel, walking-module, complete diagnostic,
reviewer-example, warning, and strict-LHS checks. The strict audit has zero
unreviewed clauses and 45 annotated slots across 27 clauses. The catalog has
2,082 checks (1,832 `assert` plus 250 `assertnot`) across 77 areas with zero
unclassified checks. The kernel warning inventory is `1016/159`, and the
walking owner is `1026/159`, down from the additive redesign's `1028/159` and
`1039/159`. No warning is attributed to the explicit κ projection rules.
Warnings remain diagnostics rather than a veto on intended computation.
Generated health is synchronized with all 55 measured files/examples passing,
and full local CI passes those 55 targets in 306.294s.

The walking-endomorphism plan resumed at implementation-goal baseline
`82d0e27...`. Its G1–G6 implementation is active: `WalkingEnd_cat`,
`walking_base`, and `walking_loop` are opaque constants; explicit
`IsNCat(cat_succ cat_zero,WalkingEnd_cat)` evidence supplies only homwise
discreteness; and the contextual `Functord` eliminator computes at the generic
fibre-functor and displayed-cell owners. The generated-word Hom datatype and
all WalkingEnd `Obj`, `Hom`, identity, and composition rules are removed.
Derived sections compute at `piapp0`/`piapp1`; the ordinary recursor's literal
base and literal loop also compute by two narrow projection-order rewrites.
These four observer clauses implement the same two semantic constructor betas.
An open `loop ∘ p` compatibility statement is instead an ordinary equality
derived from generic strict functoriality, with no composite-prefix rewrite or
WalkingEnd-specific `unif_rule`. `BNat` remains a separate consistency model,
never the definitional Hom.

The generic G2 prerequisites are active in the kernel: `Path_cat_func`,
`path_map_func`, `path_map_transf`, their complete `fapp*`/`tapp*` ladder,
the restricted `CoreInclTransf` and explicit κ ladder, transparent semantic
`path_lift_func`, and the reusable `NatSucc_func` in the Nat extension.
Permanent diagnostics build the exact two-factor Nat spiral, retain the
iterable higher action, and negatively guard the retired strict endpoint
conversions. No primitive PathLift, generic directed Core functor, or new
unification rule was added. Capped groupoid-function
composition evaluates pointwise; because `eta_equality` is enabled, conversion
also observes the corresponding whole lambda even though no whole-term fold to
`grpd_comp_function` exists. The living walking plan records exact owner logs,
warning deltas, rejected alternatives, the completed G2 formation/audit gate,
the promoted opaque owner, and the completed G4–G6 construction. The active
walking module now supplies transparent Code and powers, the exact directed
spiral, a contextual representable decoder, both Hom--Nat equality inverses,
a structured forward encoder, carrier/native equivalence packages, two
sethood proofs, and directed loop negative results. The canonical spiral point
equation reduces to reflexivity; the whole selected spiral first traverses
explicit κ-left, and its final endpoint-adjusted public presentation therefore
does not collapse to the raw `PathLift` component or an identity. A reverse
functor from the separate `BNat`
model and a full hom-category equivalence remain deferred until reusable
monoid-action-to-functor and functor-extensionality infrastructure exists.

The adopted equality-valued omega-equivalence overlay is implemented at its
selected operational MVP boundary. This includes the abstract/rigid-universe,
stable Product, uniform explicit-cast, decoder-independent native theorem
chain, homwise groupoidality, literal structured-action/J, equivalence-valued
displayed transport, unrestricted evidence-property, and unconditional
finite-`NCat` object-truncation results. The native next-hom owner is a one-way
derived extension with protected transparent proof helpers and one ordinary
public hom-action constructor; it is not an opaque theorem capability.
`OmegaEquivAlong(f)` decodes to a native
one-constructor record with separate left/right inverse arrows, ordinary
equality-valued cancellation laws in the two endomorphism hom-categories,
four computational observers, an indexed eliminator, and reflexive evidence.
`OmegaEquiv(x,y)` is now a stable abstract record-like facade with an
injective package constructor, forward/evidence observations, a primitive
dependent eliminator with constructor beta, propositional eta, and a
transparent Sigma comparison with two propositional round trips. The general
`object_path_equiv(p)` computational adapter is defined from
`path_to_hom`, `path_sym`, and J-derived laws; it is not an opaque encoder.

The facade and eliminator are primitive kernel interface, but they are not
observationally opaque: their documented constructor/projection/eliminator
betas expose the data. The generic proof-time comparison between
`OmegaEquiv(C,x,y)` and object equality is now active while `C` remains
syntactically abstract; it does not make the classifiers runtime-convertible
or add raw-path observer beta. The rigid Cat and Grpd universe equalities now
runtime-reduce to EQ1, and explicit EQ1 reflexivity packages compute. The
explicit D0 migration adapters described below remain a distinct
compatibility layer.

A specialization audit rejects the earlier abstract `lambda p, p` experiment
as a general public cast. Product repairs the measured specialization failure
by making `ProductPathView` its stable equality normal form while decoding its
carrier to the previous constant-family `SigmaPathView`. It has explicit
construction, projections, elimination, reflexivity, carrier adapters, and a
shaped EQ1 comparison. Generic `eq_refl` remains distinct from canonical
`product_path_refl` even though both expose the expected components.

Opposite retains `Obj(Op_cat(C)) -> Obj(C)`. A direct EQ1 comparison against
that reduced equality passed abstractly but failed at composite Product and
literal-path specializations. The Phase-6 opposite-only intermediary proved
that typed-let staging works, but is now retired in favor of the uniform
`ObjectPathCastView(C,x,y)`. Its carrier reduces to object equality and a
single direct unification rule compares it with EQ1. The public casts in both
directions use a typed `let`, beta-reduce to their input, and have definitional
round trips after abstract, Product, opposite/nested, literal-path, functor,
Cat, and Grpd specialization. Product/opposite compatibility names route
through these general casts. Cast terms do not reify a package, so their
facade observers remain stuck; use `object_path_equiv(p)` when projection
computation is required. No primitive nonreducing cast term is active. These
are current architecture facts owned by the July 17 plan, not new repository-
wide SOP rules. Warnings remain 971/157 and the strict audit remains
zero/45/27.

The literal-path Phase-3 slice adds two narrow proof-time comparisons without
promoting generic direct univalence. `OmegaEquiv(Path_cat A,x,y)` compares
with `x =_A y`, while `Core_incl_func(Path_cat A)` compares with the identity
functor. `path_equiv(p)` is the explicit computational package with
forward arrow `p`, two `path_sym(p)` inverse choices, J-derived laws, facade
elimination, and a next-hom reification consumer. `IsGroupoidalCat(C)` is
equivalence evidence for `Core_cat(C) -> C`; this is the internally univalent/
complete groupoidality notion, not merely the external statement that arrows
have inverses. `Path_cat(A)` has canonical evidence. A bare path is accepted
at the facade type, but its observers deliberately remain stuck. Adding a raw
projection rule reproduces the package/path critical pair at 972/160 and
breaks a consumer, so the explicit package remains required.

The Phase-4 groupoid-universe boundary now makes
`Hom_cat(Grpd_cat,A,B)` the path category of ordinary functions. Stable
`grpd_id_function` and `grpd_comp_function` heads compute pointwise. Generic
identity remains proof-time-comparable. Generic categorical composition keeps
its own whole-term head and proof-time comparison, but its capped application
now computes pointwise; with `eta_equality`, whole-function conversion can
therefore observe the corresponding lambda even though no whole-term rewrite
to `grpd_comp_function` is installed.
Explicit defined adapters connect `TypeEquiv(A,B)` and
`OmegaEquiv(Grpd_cat,A,B)`: the forward adapter uses the selected
contractible-fibre inverse, while the reverse proves the two omega inverse
choices agree and then supplies `EquivByInverse`. Selected maps, inverse
fields, cancellation laws, and the forward-map round trip compute. This adds
no decoder or bridge axiom. `is_equiv_map_by_inverse` is now a fully
transparent theorem: left-oriented path induction and the generic
half-adjoint triangle contract every homotopy fibre, after which the result is
re-centred at the historically selected inverse/right-law witness. The old
selected-centre computation is preserved without its former rewrite rule, and
the contraction proof is real propositional structure rather than an opaque
capability or proof-erasure equation.

The Phase-5 migration bridge makes the retained D0/new-EQ1 relationship
executable in both directions. Old D0 evidence is observed as EQ1 inverse
fields plus decoder-derived ordinary laws. New EQ1 evidence enters legacy D0
through a stable compatibility constructor whose four D0 observations are
specified: inverse fields project directly, and recursive cells apply the
defined `object_path_equiv` adapter to the equality laws before recurring.
Thus two levels of recursive observation compute without `idtoequiv_cat`.
The primitive compatibility head is required only because D0 itself has no
constructor; it is migration surface, not a foundational encoder requirement.
D0 still has no eta/extensionality theorem, so neither evidence round trip is
claimed and both remain negative controls.

Phase-7 migration has retired the redundant standalone
`cat_univalence(C) : CatUnivalence(C)` inhabitant. It had no kernel consumer;
the two diagnostics that mentioned it now use the existing
`cat_univalence_from_decoder(C)`. The computational `idtoequiv_cat` and
`omega_equiv_path` operations, the specified-inverse
`cat_univalence_by_decoder`, and their groupoid counterparts remain while
their real rules and theorem consumers are migrated. No opaque EQ1 encoder or
decoder term was introduced. The new carrier-view rewrite and direct
unification equation are explicitly trusted cast infrastructure, while the
two term operations are transparent identities. This is the current
architecture of the July 17 plan, not a repository-wide rule that all explicit
casts must use this representation.

The transparent `object_path_equiv_D0(p)` compatibility operation is now the
defined route from an object path into retained D0: it composes the general
EQ1 package with the observation-complete migration constructor. Both
ordinary-isomorphism recursive cells and the D1 category-path next-hom
consumer use it instead of `idtoequiv_cat`. The latter's selected functor now
computes to `path_to_hom(Cat_cat,p)`. This reduces, but does not yet eliminate,
the encoder dependency *inside the legacy compatibility surface*;
compatibility round trips, shaped Product computation, OneCat theorems, and
other inventoried consumers remain. The native hom-action and
evidence-property modules and their public examples contain no Cat/Grpd
decoder, D0/D0b, or D0/EQ1 migration reference. Thus decoder migration is
complete at the selected foundational boundary even though full legacy API
retirement is not.

The general-groupoidality layer now lives with the native derived hom-action
owner in `emdash3_2_eq1_hom_action.lp`. For
`g : IsGroupoidalCat(C)`, `groupoidal_core_homwise` applies
`omega_equiv_along_fapp1` directly to `Core_incl_func(C)`, with no
EQ1-to-D0, D0b, or D0-to-EQ1 step. Its selected right inverse sends a directed
arrow to an object path, and the equality-valued right law proves
propositionally that re-including that path recovers the arrow.
`IsDiscreteCat(C)` now stores this native `IsGroupoidalCat(C)` witness as
its second factor, alongside object sethood; packaged `ZeroCat` carriers
therefore provide nonliteral groupoidal witnesses without a D0 migration.
The public homwise path-selection names live in the one-way extension, while
formation and projections remain in the kernel, so no kernel-to-extension
cycle is introduced.

The first slice also checks the existing `path_ind_sec` computation for a
structured Sigma-pullback motive in a groupoidal context. Groupoidality is not
used by that computation: this is the intended specialization-by-weakening
result, showing that structured action needs no second eliminator.

The next slice establishes the exact literal `Path_cat(A)` comparison.
`path_cat_structured_transport` is displayed functor action;
`path_cat_ind_eqr_transport` is primitive right J with a function-valued
motive; and `path_cat_path_ind_app` evaluates the existing
`path_ind_sec`. Two `ind_eqr` proofs and transitivity compare all three. Only
primitive J runtime-reduces to `u` at reflexivity. The two directed
presentations retain negative conversion controls, while narrow proof-time
joins reconcile the Path-category identity and the reflexive
PathOut/Sigma-pullback component order. Broad runtime repairs were rejected;
the selected rules leave warnings at 971/157 and add no decoder, encoder, or
parallel eliminator. This is a current architecture fact for the July 17
plan, not a new general SOP requirement for casts or transport.

The third Phase-9 slice proves the promised equivalence-valued transport
without adding another transport primitive. Ordinary functor action maps
`OmegaEquivAlong` by applying the functor to both inverse arrows and both
equality laws. The groupoidality-selected object path and its reversal then
construct explicit native equivalence evidence for every arrow, using the
pointwise re-inclusion theorem and the existing J-derived path-cancellation
laws. Specializing functor preservation to `D : Catd(C)` equips the existing
`fapp1_fapp0(D,f)` fibre transport with EQ1 evidence; its inverse projections
compute. The construction is transparent and adds no rewrite, unifier,
encoder, decoder, or transport axiom. Selection of the arrow-to-path map now
uses the native equality-valued hom-action owner; no D0b compatibility step remains in
this consumer chain. This classification is specific to the July 17
implementation plan and does not amend the general SOP.

The reusable coherence prerequisite for that migration is now active.
`half_adjoint_counit` adjusts separate equality-valued left/right inverse
homotopies, and `half_adjoint_triangle` derives the standard triangle from
primitive `ind_eqr`, `eq_ap`, homotopy naturality, and path cancellation.
Both are transparent theorems: the adjusted counit and triangle proof compute
on reflexive identity data. No rewrite, unification rule, primitive symbol, or
opaque theorem capability was added. The complete theorem is promoted as
`omega_equiv_along_fapp1` in the one-way extension. Its 56 implementation
lemmas are protected and transparent, its public package projections compute,
and reflexive input normalizes to the identity hom functor. A public
transparent definition could not retain `private` helpers under Lambdapi's
module exposition rules; `protected` helpers passed both the minimal probe and
the full external consumer, so this is not an opacity boundary.

`AllArrowsEquiv(C)` records the pointwise statement that every directed
arrow has native equality-valued evidence, and `groupoidal_all_arrows_equiv` computes
from coherent core groupoidality to that view. The converse is not active:
arbitrary pointwise choices do not yet assemble the coherent omega-functor
`C -> Core_cat(C)` required by `IsGroupoidalCat`. This is a structured
functor assembly/extensionality gate, not a decoder gap.

A direct one-`J` shortcut through the uniform identity cast was measured and
rejected as a computational replacement. The cast gives a raw path the facade
type, but does not reify a package head, so `omega_equiv_to` remains stuck
even on primitive reflexivity. Explicit `object_path_equiv` reification
does compute to `path_to_hom`. This is a July 17 plan-local implementation
fact, not a general requirement that other subsystems introduce encoders or
decoders.

The generic half-adjoint inverse at a literal path category is still
intentionally not definitionally the input path; use the direct
`path_equiv(p)` package for that computation.

The downstream transparent module `emdash3_2_eq1_evidence_property.lp` now
closes the native fixed-arrow evidence-property and finite-dimension
truncation obligations. It first exposes the native record as independent
left- and right-inverse homotopy fibres and proves record eta through the
indexed eliminator. Given any native witness, composition with its forward
arrow is an ordinary equivalence on each inverse-candidate hom classifier;
the transparent `is_equiv_map_by_inverse` theorem therefore contracts both
fibres and then the record. Consequently
`omega_equiv_along_evidence_is_prop(C,x,y,f)` holds for every category and
fixed arrow, with no truncation assumption, axiom, decoder, rewrite, unifier,
or proof erasure. Literal path, discrete, and locally-set proofs remain useful
independent specializations.

The same module proves arbitrary truncation closure under explicit
retractions and uses it twice—Sigma facade to stable facade, then stable
facade to object equality. Transparent `CatDim` recursion combines the hom
induction hypothesis, same-level Sigma truncation, and the general evidence
property to define
`ncat_obj_trunc(n,C,h) : IsObjTruncCat(cat_dim_trunc_level(n),C)` for every
finite native dimension. Its zero equation reduces to
`is_discrete_cat_obj_set`; its successor exposes the expected hom recursion.
The old uninhabited `OmegaEquivAlongEvidenceProp_D0` capability and
`ncat_obj_trunc_from_evidence_prop` conditional theorem were retired by the
2026-07-19 P4 consumer audit. They had no nonself consumer and are superseded
by the unconditional native equality-valued proof. The representation-independent
`prop_is_trunc_cat_dim` helper remains in use by that native proof.

The canonical path action needs no selected-computation facade. For every
ordinary `f : A -> B`, `path_map_func(f)` is the functor
`Path_cat(A) -> Path_cat(B)`; its object action is `f`, its exact capped action
is definitionally `eq_ap(f,p)`, and its full next-hom action remains available
through the generic functor calculus. `PathActionRefinement` stored only an
alternative first-path term and a pointwise comparison with that already
canonical term. It constructed no functor, supplied no higher action, and had
no retained consumer requiring an alternative open-path normal form. P9
therefore removes the package rather than recasting ordinary clients through
an `act` argument. Exceptional future computations may use local comparison
theorems; they do not pre-authorize a generic registry.

The same audit removes the comparison-only Nat successor proof basis and its
two proof-time rules while retaining recursive Nat equality, `NatSucc_func`,
`nat_succ_ind_eqr`, arithmetic/sethood, and WalkingEnd. Dependent PathRecord
witness action remains direct `eq_apd`; any iterable dependent successor would
need an honest displayed functor/section construction. At the user's selected
feature boundary, P9 also retires the isolated Sum carrier, eliminator, map,
action extension, diagnostics, and examples. No native equality-valued, Nat, WalkingEnd,
evidence-property, or frozen-compatibility theorem consumed them. Sum may be
redesigned later from a concrete universal-property or computation demand.

For historical comparison, the equality-overlay selected-MVP checkpoint had
1,917 checks across 70 areas.
The kernel has
21,762 lines, 887 symbols, 596 rewrite rules, and 63 unification rules. The
native hom-action extension has 2,791 lines/69 symbols; the evidence-property
extension has 1,407 lines/60 symbols and adds no explicit rewrite or
unification authority; the downstream Sum library has 430 lines/12 symbols
and owns the four extracted proof-time comparisons. The synchronized 51-file
health and reviewer sweeps pass. The diagnostic suite has 1,684 positive and
233 negative statements. Warnings remain 971/157 and the strict audit remains
zero/45/27. Synchronized 51-file CI passes with 100.845s of measured checking
time; the active July 17 plan records the phase evidence and selected
completion boundary.

The largest warning families are headed by `comp_fapp0`,
`hom_postcomp_fapp0`, `fapp1_fapp0`, and `tapp0_fapp0`. These reports are
diagnostic evidence for locating overlap families. They are not an automatic
veto on semantically required computation and are not a confluence proof.
The path-category E0 repair removed the path-specific
`comp_fapp0(Path_cat)->eq_trans` fold and the false definitional
self-opposite collapse. Two measured `eq_refl` projection-order bridges retain
the shared category-composition owner and reduce the inventory by 37
critical-pair reports; minimizing their recoverable endpoints also removes
four replaceable-variable advisories net. Four proposed oriented-action
runtime bridges were rejected after their owner-position variant added five
critical-pair reports and six replaceable-variable advisories. Typed
proof-time comparisons plus negative conversion controls cover those units
without changing the distinct post/pre runtime owners.
The path-symmetry E1 core now represents reversal by
`Path_sym_func(A) : Path(A)^op -> Path(A)`, with identity object action, one
measured reflexivity projection bridge, generic anti-composition, and
J-derived propositional agreement, involution, and the pointwise Core/opposite
square. Of the twelve E1 warning blocks, typed both-order consumers join the
post/pre action and naturality families, while two Product projection cases
are rejected as untyped rigid-head combinations. The other six exposed
over-specified object endpoints in generic mapped-`DefIso` cancellation:
inferring those endpoints makes both pre- and post-projection spellings
compute and removes 110 critical-pair reports. E1 itself retains six
classified reports, so the net active inventory falls by 98. Open
`path_sym`/`eq_sym` and double-symmetry terms remain non-convertible; no
path-specific composition or cancellation owner was added.
Candidate C now gives the canonical dependent `PathRecord_grpd(A)` a direct
observational equality view through its nested-Sigma presentation. Literal
record reflexivity reduces to the stable `PathRecordPathRefl(A,r)` head;
source and dependent-tail projections compute, and a specialized `ind_eqr`
clause computes only at that reflexive head. The closed registry covers the
shared path-category units, PathSym, Core inclusion, `idtoiso_cat`, and
`idtoequiv_cat`. It does not add arbitrary structural action, arbitrary-
constructor J computation, or runtime record eta. Explicit PathSym category
guards remove four spurious owner matches; five inferred-slot refinements
remove five replaceable advisories. The remaining 17 critical-pair reports
are covered by literal/shaped joins, typed post/pre/naturality diamonds, and
one negative displayed-target control. Relative to E1, the active inventory
therefore changes from 974/159 to 991/157.
Candidate H adds stable `PiHapply`/`PiFunext` owners over the existing
related-input `PiPathView`, pointwise runtime beta, generic-J propositional
eta, and a `TypeEquiv` package for the diagonal observation. Its one
two-rigid-head `unif_rule` preserves the reflexive computation of the
transparent presentation as a generic structurally justified proof-time law;
typed reflexivity tests firing, while negative conversion and arbitrary-J
checks preserve the runtime boundary. A reviewed opaque
`is_equiv_map_by_inverse` theorem capability converts the explicitly supplied
round trips to contractible fibres. Only the selected fibre centre computes;
the contraction path remains opaque. The 29 new diagnostics and reviewer Pi
example pass owner/application-order checks without changing the 991/157
warning inventory or the 45-slot/27-clause LHS audit.
The structural-path compatibility slice adds arbitrary propositional
`sigma_path_decode_encode` and `sigma_path_encode_decode` theorems while
preserving the existing componentwise/J owners and rejecting open runtime
eta. Constructor-exposed reflexivity computes. A distinct literal-reflexivity
base is retained because the proof-time Sigma-reflexivity comparison does not
propagate through nested decode during generic J. Since `PathRecord` equality
already is `PathRecordPathView`, its named encode/decode maps are transparent
identity views; both round trips, shaped reflexivity, the dependent-tail
observer, and one nested PathRecord case compute. The 21 new diagnostics and
reviewer example add no rewrite or unification rule, leave warnings at
991/157, and leave the strict audit at 45 annotated slots across 27 clauses
with zero unreviewed candidates.
The ordinary `TypeEquiv` algebra slice retains `type_equiv_refl` and adds
transparent `type_equiv_sym` and categorical-order `type_equiv_comp` packages.
Their `*_is_equiv` evidence is derived from explicit selected inverse paths
through `is_equiv_map_by_inverse`; no new rewrite or unification rule is
needed. Forward maps, selected inverse maps, right paths, forward-map units,
and forward-map associativity compute. Contraction-derived left paths and
package-level double-symmetry/unit eta stay non-runtime. Twenty-nine new
diagnostics and the reviewer algebra example leave warnings at 991/157 and
the strict audit at 45 annotated slots across 27 clauses with zero unreviewed
candidates.
The groupoid decoder slice names both round trips already carried by
`grpd_univalence_by_decoder`, derives `grpd_univalence_from_decoder`, and makes
its selected contractible-fibre inverse compute to the single operational
`grpd_equiv_path` owner. It deliberately does not identify an arbitrary
legacy `ua_grpd(U,e)` with that decoder. `coe_grpd_idtoequiv` is derived by J;
combined with the decoder right round trip it gives the propositional
`grpd_equiv_path_coe` square and a Pi-universe action consumer. A measured
generic runtime `coe(grpd_equiv_path(e))` orientation was rejected because
the Product-decoder-first branch leaves `coe(product_grpd_path(...))` stuck.
The 16 new diagnostics and reviewer decoder example add no rule or unification
equation, leave warnings at 991/157, and leave the strict audit unchanged.
The first Phase-13 groupoid-universe slice now exposes the same decoder through
the finite named view `GrpdPathView(A,B) := TypeEquiv(A,B)`.
`grpd_path_encode`, `grpd_path_decode`, their two propositional inverse laws,
and `grpd_path_decode_coe` route through the existing decoder owners; Product
diamonds, Pi action, and same-base Sigma formation reuse their existing bodies.
Public universe equality remains opaque. The direct canonical-owner rule was
warning-neutral and passed the full existing suite, but its unstratified
self-universe normalization recursively reopened universe equality and timed
out at 20 seconds, while both baseline equality and the named view normalize
within the bound. The earlier spelling on reducible `Grpd_grpd` also added one
avoidable alias-unfold critical pair; the canonical `(Obj Grpd_cat)` spelling
removed it. Seventeen positive/seven negative diagnostics and a fourteen-
positive/five-negative reviewer example are active. Seven semantic aliases
add no rule or `unif_rule`; warnings remain 971/157 and the strict audit remains
zero/45/27. Quiet view source/check logs end in `20260716-053946`/`054135`,
warning logs in `20260716-054151`/`054233`, the direct self-universe timeout
ends in `20260716-053636`, controls end in `20260716-053720`, and the active
reviewer log ends in `20260716-054558`. The catalog has 1,509 checks across 52
areas; health checks 34 files with a 17,838-line/738-symbol/574-rule/51-
unification-rule kernel and 1,367 positive diagnostics. Synchronized 34-file
CI passes with 182.160s of measured checking time (189.18s wall time).
The next Phase-13 slice selects a different boundary at the categorical
universe. The canonical rule makes `@=(Obj Cat_cat,A,B)` reduce directly to
`OmegaEquiv(Cat_cat,A,B)`; the readable `CatPathView` alias, canonical package
reflexivity, decoder-owned encode/decode and round trips, selected
functor/evidence projections, reflexive Product action, and D0b next-hom
package are active. Self-universe normalization terminates at the opaque
`OmegaEquivAlong_D0` certificate boundary, and the canonical `(Obj Cat_cat)`
spelling is warning-neutral at 971/157; the reducible `Cat_grpd` spelling adds
one avoidable report. Generic `eq_refl` is deliberately retained. Collapsing
it to `omega_equiv_refl` adds three reports and breaks the existing
`omega_equiv_along_obj_path` reflexive action before the outer `eq_ap` beta can
fire. Twenty-two positive/eight negative diagnostics and a fifteen-positive/
six-negative reviewer are active, with no `unif_rule`. The catalog has 1,539
checks across 53 areas; health checks 35 files with a 17,989-line/750-symbol/
575-rule/51-unification-rule kernel and 1,389 positive diagnostics. The full
reviewer sweep passes, and synchronized CI passes with 165.477s of measured
checking time (171.88s wall time). Any future representation of the currently
opaque fixed-arrow certificate must reopen the self-universe normalization
gate.
Historical checkpoint note (superseded 2026-07-19): the next three paragraphs
record the July 16 one-layer observation, conditional truncation, and
dimension-indexed observation promotions at their original checkpoints. P4
has now retired all three D0 experiment families, their self-only diagnostics,
and their reviewer examples. The measured normalization/failure results below
remain useful provenance, but the named operations are no longer active.

At that checkpoint, the next Phase-13 boundary exposed a finite one-layer observation record
for that certificate. `OmegaEquivAlongObservation_D0(f)` is the nested
Sigma/Product of the selected left/right inverse arrows and recursive
left/right cell packages; `omega_equiv_along_observe_D0(u)` fills it through
the existing D0 owners, and `OmegaEquivAlongPathView_D0(u,v)` is equality of
the two records. Canonical view reflexivity and one-way action of a genuine
certificate path are active, including a D0b next-hom consumer. Directly
installing the view as certificate equality is rejected: the owner-position
source exceeds 30 seconds, and an append-only canonical self-universe control
exceeds 20 seconds, while the finite view control finishes. Thirteen positive/
three negative diagnostics and a ten-positive/three-negative reviewer are
active; five semantic symbols add no rule or `unif_rule`, warnings remain
971/157, and the strict audit remains zero/45/27. The catalog has 1,555 checks
across 54 areas; health checks 36 files with an 18,104-line/755-symbol/575-
rule/51-unification-rule kernel and 1,402 positive diagnostics. The full
reviewer sweep passes, and synchronized CI passes with 186.423s of measured
checking time (193.35s wall time). The view supplies neither a reverse decoder
nor evidence eta/property-valuedness. The next bounded theorem slice separates
the now-ready `IsNCat` induction/Sigma/univalence transport from its still-
missing certificate-property inhabitant: the former must take the latter as
an explicit capability rather than postulate it or infer it from the finite
view.
At the following historical checkpoint, that conditional theorem spine was active. The uninhabited classifier
`OmegaEquivAlongEvidenceProp_D0` states the exact global fixed-arrow
property-valuedness premise. `prop_is_trunc_cat_dim` lifts such a proposition
to every native dimension level, and
`ncat_obj_trunc_from_evidence_prop(P,n,h)` computes at zero to the stored
object-set factor and at successor through the homwise induction, same-level
Sigma closure of `OmegaEquiv`, and `cat_univalence_type_equiv`. Eleven
positive/four negative diagnostics and an eight-positive/four-negative
reviewer are active. The typed proof-time negative retains distinct capability
inputs, so no `unif_rule` is added; warnings remain 971/157 and the strict
audit remains zero/45/27. The catalog has 1,570 checks across 55 areas; health
checks 37 files with an 18,173-line/758-symbol/577-rule/51-unification-rule
kernel and 1,413 positive diagnostics. The full reviewer sweep passes, and
synchronized CI passes with 198.816s of measured checking time (206.34s wall
time). Bare `IsNCat` evidence still does not inhabit the theorem, and the
finite observation view still does not construct the capability.
At the final historical checkpoint in this retired experiment family, the recursion-safe representation continuation was completed/promoted.
`OmegaEquivAlongDimObservation_D0(n,h,f)` computes
to Unit at zero and at a successor stores both selected inverse arrows plus
the forward arrow and smaller-dimensional observation of each D0 inverse-cell
package. `omega_equiv_along_dim_observe_D0` reuses the four existing D0 owners;
`OmegaEquivAlongDimPathView_D0` adds only reflexivity and one-way `eq_ap`
action. ZeroCat erasure and OneCat next-cell termination compute. Seventeen
positive/five negative diagnostics and a twelve-positive/four-negative
reviewer pass; six symbols and two two-equation rule families add no
`unif_rule`, preserve 971/157 warnings, and retain zero/45/27 audit. The
catalog has 1,592 checks across 56 areas; health checks 38 files with an
18,452-line/764-symbol/579-rule/51-unification-rule kernel and 1,430 positive
diagnostics. Quiet owner/signature/inherited-check logs end in
`20260716-104217`/`104520`/`104613`, warning logs end in `104636`, and the
scratch/active reviewer logs end in `104802`/`104928`. The indexed view remains
one-way and does not inhabit `OmegaEquivAlongEvidenceProp_D0`. The full
reviewer sweep passes, and synchronized 38-file CI passes with 201.708s of
measured checking time (212.59s wall time).
At its dated 2026-07-16 checkpoint, the first registered elementary-former
action was completed/promoted.
`sum_map(f,g)` is the eliminator-owned canonical
binary-sum map. `sum_obs_action(f,g,u,v)` delegates equal-tag paths to the two
supplied `ObsAction` registrations, returns the impossible input in mixed
selected-action branches, eliminates it in mixed coherence branches, and
packages pointwise agreement with generic `eq_ap`. Transparent `eq_ap`
unfolded before a direct two-action proof-time equation could fire. The
selected architecture therefore uses one stable reflexive action basis per
tag and two direct `unif_rule`s per basis: normalized component reflexivity and
the exact outer-`ind_eqr` normal form. The arbitrary comparison is derived by
ordinary component J and explicitly composes the two paths, without relying
on unification transitivity. This is trust-classified as a semantically
justified former-specific structural action law. Runtime basis/action
conversion, direct transitive proof-time collapse, open selected/semantic
action equality, and package collapse remain negative. Twenty-one positive/
six negative diagnostics and a thirteen-positive/four-negative reviewer pass;
thirteen symbols and four proof-time equations add no runtime rewrite rule,
preserve 971/157 warnings, and retain zero/45/27 audit. The catalog has 1,619
checks across 57 areas; health checks 39 files with an 18,883-line/777-symbol/
579-rule/55-unification-rule kernel and 1,451 positive diagnostics. Final
feasibility/owner/inherited-check logs end in `20260716-112405`/`114250`/
`113027`, warning logs end in `113036`/`113051`, and the active reviewer log
ends in `113631`. Full examples pass, and synchronized 39-file CI passes with
129.250s of measured checking time. Arbitrary structured J/fibrancy, proof
erasure, no-confusion/canonicity, categorical coproduct structure, and other
former actions remain separate. The next bounded replacement probe targets
OneCat-scoped ordinary-iso univalence; it may not restore or consume a global
`cat_iso_univalence` assumption, and must instead derive the ordinary-iso/
omega-equivalence comparison or record the exact missing owner.
That probe has now promoted a bounded one-sided prerequisite.
`iso_evidence_omega_along_D0(i)` is a stable, source-backed
fixed-arrow evidence generator: both inverse observations are
`iso_evidence_from(i)`, while the ordinary left/right inverse equations encode
with `idtoequiv_cat` as the two recursive cells. Its public Sigma package is
`iso_evidence_omega_equiv(i)`. A proposed runtime reflexive fold added four
unjoinable reports; it was rejected. The selected single `unif_rule` compares
only the backed reflexive evidence head with canonical D0 reflexivity at proof
time, is exercised by typed `eq_refl`, and leaves the package and decoder
runtime-distinct. Generic J proves
`iso_evidence_omega_equiv(idtoiso_cat(p)) = idtoequiv_cat(p)` without relying
on unification transitivity. `one_cat_iso_path(X,i)` then uses the canonical
omega decoder, and `one_cat_iso_path_idtoiso(X,p)` supplies the first
decoder-after-encoder round trip.

The full `CatIsoUnivalence` replacement was not claimed by that one-sided
checkpoint. Its focused reverse probe showed the missing endpoint exactly: an arbitrary public omega-equivalence
has separate `left_inv` and `right_inv`; its right cell decodes at
`f o right_inv`, not at the `f o left_inv` endpoint needed by an ordinary
package choosing the left inverse. The next prerequisite at that checkpoint
was a OneCat-derived
directed comparison between those inverses, conversion to a discrete-hom
path, transport of the right law, and nested-Sigma extensionality. Neither a
rewrite nor an unbacked proof-time identification is selected. The then-active
legacy global `cat_iso_univalence` assumptions remain unused by the new owner
and are retired after the full scoped replacement closes. Twelve positive/six
negative diagnostics and a nine-positive/four-
negative reviewer pass; five symbols, two two-equation rule families, and one
proof-time comparison preserve 971/157 warnings and zero/45/27 audit. The
catalog has 1,637 checks across 58 areas; health checks 40 files with a
19,062-line/782-symbol/581-rule/56-unification-rule kernel and 1,463 positive
diagnostics. Final owner/signature/inherited-check logs end in
`20260716-120633`/`121149`/`120824`; warning logs end in `120226`/`120834`, the
intentional reverse failure ends in `120916`, and the active reviewer log ends
in `121326`. Full examples pass; synchronized 40-file CI closes the one-sided
prerequisite with 281.823s of measured checking time.

The dependency-ready inverse-comparison continuation is completed/promoted
with synchronized 40-file CI. The first intended-owner attempt composed the
two recursive cells
through raw `Hom_func` action and failed at three unresolved comparisons: both
unit presentations and the middle associativity step. This is recorded in the
owner log ending `20260716-123757` and is evidence against relying on
unification transitivity, not against the mathematical construction. The
selected owner instead exposes both recursive cell arrows, uses the existing
stable post- and precomposition functors for whiskering, and inserts an
explicit propositional associator through `path_to_hom`. The resulting
`omega_equiv_along_left_to_right_D0(u) : left_inv(u) -> right_inv(u)` is
generic; `one_cat_omega_inverse_path(X,e)` decodes it through hom discreteness.
Canonical reflexivity computes to the identity 2-cell through generic owners,
while the decoded path remains runtime-distinct from `eq_refl`. Eight symbols,
no rewrite, and no `unif_rule` add nine positive/four negative diagnostics and
six positive/three negative reviewer statements; the reviewer now totals
fifteen positive/seven negative statements. Quiet owner/check logs end in
`20260716-124247`/`125136`, warning logs in `125119`/`125140`, and the reviewer
log in `124544`. The warning inventory remains 971/157 and the strict audit
remains zero/45/27. The catalog has 1,650 checks across 59 areas;
health checks 40 files with a 19,373-line/790-symbol/581-rule/56-unification-
rule kernel and 1,472 positive diagnostics. Full examples and synchronized CI
pass with 139.872s of measured checking time. The remaining
full-capability prerequisite is no longer inverse comparison: it is transport
of the right law along the selected inverse path followed by ordinary
nested-Sigma evidence reconstruction and the reverse round trip.

That final OneCat-scoped continuation is now completed/promoted. The generic
`omega_equiv_left_law` and `omega_equiv_right_law` decode the two recursive
cells. `one_cat_omega_right_law_at_left` transports the latter along
`one_cat_omega_inverse_path`, and `one_cat_omega_iso_evidence` reconstructs
ordinary evidence with exact forward/inverse/law projections. In a OneCat,
the inverse-law proof fields live in discrete endomorphism hom-categories;
`discrete_cat_path_proof` and the existing nested-Sigma path owner therefore
prove `one_cat_omega_iso_lift_retract`. Encoder agreement and the categorical
decoder round trip then give `one_cat_idtoiso_iso_path`, completing the
specified inverse pair with `one_cat_iso_path_idtoiso`.

The first packaging attempt targeted the then-active legacy
`CatIsoUnivalenceByDecoder(C)` and failed because that classifier hardcoded
the frozen `iso_evidence_path`; the log ending `20260716-132624` records the
two unresolved decoder comparisons. The selected
`OneCatIsoUnivalenceByDecoder(X)` instead names the scoped decoder explicitly,
derives `one_cat_iso_univalence(X)` through
`is_equiv_map_by_inverse`, and exposes `one_cat_iso_type_equiv(X,x,y)`.
Its forward map, selected inverse, and selected right path compute, while the
contraction-derived left proof remains runtime-distinct. The unused global
capability and hardcoded classifier are retired in the follow-up slice. Ten
semantic symbols add no rewrite or `unif_rule`.
Owner quiet/warning logs end in `133706`/`133718`, inherited-suite logs in
`133745`/`133751`, and the expanded 32-positive/12-negative reviewer in
`134212`; warnings remain 971/157 and the audit remains zero/45/27. The new
active area contributes thirteen positive/two negative diagnostics, bringing
the catalog to 1,678 checks across 61 areas with zero unclassified checks.
Health passes across 40 files at a 19,883-line/804-symbol/581-rule/56-
unification-rule kernel with 1,495 positive diagnostics, and full examples
pass. Synchronized CI passes with 109.546s measured checking time. The scoped
construction is closed; active inventory selects bounded retirement of the
unused global capability inhabitants/classifier while retaining the consumed
`iso_evidence_path` reflexive/Product owner.

That bounded retirement is now promoted. `cat_iso_univalence`,
`cat_iso_univalence_by_decoder`, and `CatIsoUnivalenceByDecoder` had no active
kernel consumer and only three compatibility diagnostics; they are removed
without replacing the assumption. `CatIsoUnivalence` and `isotoid_cat` remain,
and the latter now computes in a diagnostic through
`one_cat_iso_univalence(X)` to `one_cat_iso_path(X,i)`. The obsolete
scoped-vs-global negative is removed because its global term no longer exists.
The Product decoder rules and their checks still consume `iso_evidence_path`
and are unchanged. Owner/check quiet logs end in `140150`/`140155`, warning
logs in `140205`/`140228`, and the 33-positive/11-negative reviewer in
`140406`. Three symbols are removed with no rewrite or `unif_rule`; warnings
remain 971/157, the audit remains zero/45/27, and the catalog has 1,675 checks
across 61 areas with zero unclassified checks. Health passes across 40 files
at a 19,859-line/801-symbol/581-rule/56-unification-rule kernel with 1,493
positive diagnostics, and full examples pass. Synchronized CI passes with
212.799s measured checking time. The global
ordinary-iso capability retirement is closed.

At its dated 2026-07-16 checkpoint, the next former-action continuation was
also completed and promoted. Recursive Nat equality exposes
`(succ m = succ n)` as `(m = n)`, so `nat_succ_obs_action` selects `p |-> p`.
Generic `eq_refl(n)` and outer `eq_refl(succ n)` retain distinct runtime
provenance. The accepted owner therefore introduces
`nat_succ_ap_basis(n)` and two direct, narrowly typed `unif_rule`s: one
compares that stable basis with each reflexivity presentation at proof time.
`nat_succ_component_basis` and `nat_succ_basis_outer` are internal paths, and
generic `ind_eqr` composes them to prove `nat_succ_eq_ap(p)` for an arbitrary
predecessor path. The registered package reuses that theorem as its semantic
coherence and composes through the generic `obs_action_comp` owner. Direct
runtime basis/reflexivity conversion, proof-time transitivity, selected-map/
generic-`eq_ap` conversion, and package collapse remain negative; no
successor-specific J beta or Nat canonicity claim is added.

Owner/check quiet logs end in `141904`/`142047`, warning logs in
`142057`/`142329`, and the active eleven-positive/five-negative reviewer log in
`142721`. Seven symbols and two proof-time equations add no runtime rewrite
rule. Warnings remain 971/157 and the strict audit remains zero/45/27.
Fourteen positive/five negative diagnostics bring the catalog to 1,694 checks
across 62 areas with zero unclassified checks. Health passes across 41 files
at a 19,988-line/808-symbol/581-rule/58-unification-rule kernel with 1,507
positive diagnostics. Full examples and synchronized CI pass; CI records
220.269s measured checking time. This is dated validation evidence, not the
active Nat API. P9 removes the basis, comparison theorem, two proof-time
rules, and selected-action wrapper because no later arithmetic or WalkingEnd
construction consumes them; `NatSucc_func` and `nat_succ_ind_eqr` remain.

Candidate D0 introduces the neutral general-category
`OmegaEquivAlong_D0(f)` certificate independently of the old public
`OmegaEquiv`. Its transparent `OmegaEquiv_D0(x,y)` Sigma package exposes exact
forward/evidence projection beta; selected inverse observations and recursive
higher inverse cells are indexed by the fixed arrow. Reflexive evidence
computes in both inverse slots and both cells, and a diagnostic projects the
left cell and observes reflexivity again in the next hom-category. No raw
inverse-composite cancellation, package eta, compatibility bridge, new
`unif_rule`, or property-valuedness claim is added. Eighteen positive and
three negative diagnostics plus an eight-positive/three-negative reviewer
example pass the owner/projection orders. Quiet and warning-enabled full-file
owner probes end in `20260715-193201`/`193222`; warnings remain 991/157 and the
strict audit remains zero with 45 annotated slots across 27 clauses. The
promoted D0b variable-evidence Cat hom action is described next; D1 is the
remaining public migration gate.
Candidate D0b now constructs
`omega_equiv_along_fapp1_D0(u,x,y)` from variable rather than reflexive
fixed-arrow evidence. Its forward map is exactly `fapp1_func(F,x,y)`. The raw
hom action of either selected inverse functor has the wrong endpoints; the
left inverse is `Hom(eta_x,epsilon_y) o L_1`, while the right inverse combines
components from `L o F ~ id_A` and `F o R ~ id_B` to compare `L` and `R`
before conjugating `R_1`. Both recursive cells are transparent D0 packages
with stable cell/evidence observations and remain iterable for one more
observation. The implementation adds no `unif_rule` or raw cancellation.
Twenty-four positive and two endpoint-negative diagnostics plus an
eight-positive/two-negative reviewer example pass. Quiet owner logs end in
`20260715-194634`/`194846`; warning-enabled logs end in `20260715-194900` and
remain exactly 991/157 with the strict audit unchanged.
D1 replaces the public opaque `OmegaEquiv` classifier by
`Sigma f, OmegaEquivAlong(f)`. Public projections and inverse/cell
observations route through the fixed-arrow evidence owner; reflexive,
opposite, and Product closure use evidence generators rather than duplicated
public destructor rules. `omega_equiv_path` is evidence-indexed, and the
decoder capability now supplies both named propositional round trips, the
derived `cat_univalence_from_decoder`, a named `TypeEquiv`, and the
propositional encoder/`path_to_hom` square. The semantic fibre comparison is
only a one-sided retraction, preserving the package-eta/property-valuedness
boundary. Applying D0b to a category path supplies an exact, iterable
next-hom public omega-equivalence without a per-instance `unif_rule`. Forty-one
positive and five negative diagnostics plus a twelve-positive/four-negative
reviewer example cover the migration. Ten new observation-versus-reflexive-
evidence overlap families have explicit both-order checks; replacing the old
public rule family improves the inventory from 991/157 to 990/157, while the
strict audit remains zero with 45 annotated slots across 27 clauses.
Phase 8 replaces the category-indexed first-class adjunction package by the
relation `Adjunction(F,G)`. `left_adj_func` and `right_adj_func` are now
transparent compatibility views, while `unit_adj_transf` and
`counit_adj_transf` remain stable opaque observations and the sole triangle
discriminators. Both triangles, opposite adjunction, the hom-profunctor mate,
and weighted-limit/colimit preservation now thread the functor indices
directly. The active inventory found no concrete preselected unit/counit
declaration, so promotion adds no unification equation or existential
`AdjunctionPackage`; three positive and three negative diagnostics instead
cover the views, opposite involution, absent untrusted operation agreement,
and raw-operation runtime erasure. The expanded reviewer example checks both
triangles, opposite involution, mate cancellation, and the trust negative.
Minimizing the inferred opposite-functor LHS slots removes the superseded
left/right projection overlaps and improves warnings from 990/157 to 978/157;
the `comp_fapp0` family remains 400 and the strict audit remains unchanged.
The current Phase-P3 boundary supersedes the original Phase-9 D0-backed
implementation of discreteness. `IsDiscreteCat(C)` is exactly the Product of
`IsSetGrpd(Obj(C))` and native `IsGroupoidalCat(C)`. Its Product
constructor/projections compute and no package eta or evidence erasure is
selected. `core_incl_hom_func(C,x,y)` remains the generic hom action and its
object action is exactly `path_to_hom`. The one-way native hom-action module
derives `discrete_core_homwise`, its selected inverse functor, and
`hom_to_path` directly from `groupoidal_core_homwise` and
`groupoidal_arrow_to_path`. Re-inclusion is first exposed as the native
equality `path_to_hom_hom_to_path_path`; the earlier directed-cell API is
retained by applying `path_to_hom` to that equality. The opposite round trip
uses stored object sethood. Both remain non-runtime, and set truncation alone
is an explicit negative. No rewrite or unification equation was added.
The next Phase 9 slice keeps groupoidal truncation and directed dimension
separate. `IsObjTruncCat(n,C)` is exactly `IsTruncGrpd(n,Obj(C))`; native
`CatDim` starts at zero, `IsNCat(cat_zero,C)` computes to the active exact
`IsDiscreteCat(C)`, and the successor recurses over every hom-category.
`NCat(n)` retains a carrier and its evidence, with computing constructor /
projection boundaries and transparent `ZeroCat`/`OneCat` aliases but no
package eta or proof erasure. `one_cat_hom_discrete` projects the successor
evidence, and the one-way native extension owns
`one_cat_hom_core_homwise` as the required equality-valued next-hom consumer.
The original D0 OneCat ordinary-isomorphism decoder was isolated by P5 and is
deleted by P10 together with its compatibility module and reviewer client. It
was never imported by the kernel, native hom-action/evidence-property modules,
main diagnostics, or WalkingEnd spine. P4 promoted the direct one-way native
`iso_evidence_omega_along`/`iso_evidence_omega_equiv` construction. A
focused native replacement of the two-sided OneCat theorem stops at the
intentional stable-cast/facade-package-to-raw-path reification boundary even
for reflexivity. P10 deletes the unused legacy theorem rather than weakening
it, backing it with a new unifier, or making its native re-proof a cleanup
prerequisite. P4
also retired the self-only one-layer/dimension-indexed D0 observations, the
uninhabited D0 evidence-property capability and conditional theorem, and their
three reviewer examples. P5 mechanically extracted every remaining
decoder/D0b/D1 owner; P6's seven-consumer freeze is superseded by P10 deletion
and P7's suffix retention is superseded by P11 unsuffixing.

The synchronized first P4 tranche preserves the kernel warning inventory at
1,016/159 and the strict audit at zero/45/27. The regenerated catalog has
2,034 classified checks across 74 areas with zero unclassified entries;
health passes all 52 surviving source/example targets and the source TOC
remains 87 headings across sections 0–20. Full CI passes those 52 targets with
136.435s aggregate typechecking, all 16 Infinity-Codex tests, and every
repository-integrity gate.

The completed P3 validation had 2,079 classified checks across 77 areas,
passes every reviewer example and all 55 health targets, leaves warnings at
1,016/159 and the strict audit at zero/45/27, and passes full CI with 140.508s
aggregate typechecking. Directed-dimension object truncation is now the
unconditional native `ncat_obj_trunc` theorem; the OneCat-scoped ordinary-
iso decoder remains compatibility work rather than a formation dependency.
The historical bounded object-truncation prerequisite added
`cat_dim_trunc_level : CatDim -> TruncLevel`. It computes from `cat_zero` to
`trunc_zero` and commutes with successor, so one- and two-dimensional codes
normalize to `trunc_one` and its successor. Five positive/one negative active
diagnostics and four positive/one negative additions to the directed-dimension
reviewer example cover formation, both equations, low-dimensional reductions,
and the crucial absence of an evidence coercion from `IsNCat`. The two map
equations leave warnings at 978/157 and the strict audit at zero with 45
intentional slots across 27 clauses. Categorical equivalence invariance and
recursive equivalence-evidence truncation still block the implication theorem.
The synchronized index-bridge CI gate passes all 19 files in 87.056s with
every repository-integrity check.
At its dated 2026-07-15 checkpoint, the first Phase 10 structural-action slice
introduced explicit
`ObsAction(f)` and `ObsDAction(s)` packages. Each stores a selected action and
pointwise next-dimensional agreement with the existing semantic `eq_ap` or
`eq_apd` owner, so specialized computation cannot silently assert an unrelated
path action. Constructor/projection application computes; canonical
registrations use the semantic owners, the registered identity acts by
`p |-> p` on arbitrary paths, and registered nondependent actions compose
pointwise with a J-derived coherence proof. `path_record_action` exposes the
result on the shaped record view, while `path_record_witness_action` transports
the genuinely dependent witness field through `PathOver`. Thirty-one
positive/five negative diagnostics and a ten-positive/three-negative reviewer
example add no rule or `unif_rule`, leave warnings at 978/157, and leave the
strict audit at zero with 45 intentional slots across 27 clauses. Arbitrary
package agreement stays propositional, coherence evidence is retained, and an
arbitrary selected loop still gives no dependent-J beta; fibrancy remains a
separate owner. The synchronized CI gate passes all 18 files in 86.300s with
source TOC, active-reference/header, strict-LHS, fresh-catalog, example, and
repository-integrity checks.
This paragraph records the dated Phase 10 promotion. The 2026-07-19 P1
cleanup subsequently retired the unused dependent package and routed
`path_record_witness_action` directly through `eq_apd`. P2 then replaced the
nondependent registry with `PathActionRefinement` over the exact capped
`path_map_func` action, moved the successor refinement into the Nat extension,
and migrated the downstream Sum surface without retaining old aliases. The
two cleanup phases add no rule or `unif_rule`; warnings remain 1,016/159 and
the LHS audit remains zero/45/27. The synchronized P2 catalog has 2,077 checks
across 77 areas, all 55 health targets and reviewer examples pass, and full CI
passes with 133.929s aggregate typechecking. The original Phase 10 names and
counts above remain dated validation evidence, not the active API. The
2026-07-20 P9 correction further supersedes P2's nondependent selection:
`PathActionRefinement`, its Nat and PathRecord clients, and its comparison-only
support are removed in favor of direct canonical `path_map_func` action.
The general binary-sum foundation extension adds a native two-parameter
`SumData(A,B)` carrier, decoded `Sum_grpd(A,B)` classifier, both constructors,
and dependent `sum_elim` through the generated induction principle. Both
constructor betas compute; six positive and one negative active diagnostics
plus an eight-positive/two-negative reviewer example cover decoding,
formation, dependent use, branch computation, a swap consumer, constructor
non-collapse, and the absence of runtime open eta. The failed grouped-binder
candidate exposed that Lambdapi generalized the second classifier in the
generated recursor; separate `(A : Grpd) (B : Grpd)` parameter binders are the
selected owner. The one decoding rule adds no warning family, leaving the
inventory at 978/157 and the strict audit at zero with 45 intentional slots
across 27 clauses. At that foundation gate observational sum identity and
higher action were separate; the visible identity and registered componentwise
action are now promoted in later bounded slices, while no-confusion,
canonicity, and categorical coproduct structure remain separate.
The synchronized binary-sum CI gate passes all 19 files in 88.539s with every
repository-integrity check. This entire Sum paragraph is dated promotion
evidence: P9 retires the isolated former and action experiment on 2026-07-20
pending a future consumer-led redesign.
General truncation invariance now maps the operational
`grpd_equiv_path(e)` through `X |-> IsTruncGrpd(n,X)`, decodes the resulting
path with `idtoequiv_grpd`, and exposes a canonical `TypeEquiv` of truncation-
evidence classifiers plus both directional evidence maps. Reflexive path,
package, and map computation is active; arbitrary self-equivalences do not
collapse at runtime. Ten positive/one negative diagnostics and a seven-
positive/two-negative reviewer example add no rule or `unif_rule`, preserve
the 978/157 warning inventory, and leave the strict audit at zero with 45
intentional slots across 27 clauses. The synchronized gate passes all 20 files
in 97.398s.
The fixed-map categorical consumer uses the single
`omega_equiv_along_path_D1` decoder rather than reconstructing inverse object
maps from transformation components. Mapping `Obj` over its category path and
applying `idtoequiv_grpd` gives an ordinary equivalence of object classifiers;
the general theorem then supplies a `TypeEquiv` between
`IsObjTruncCat(n,A)` and `IsObjTruncCat(n,B)` and forward/backward evidence
transport. Twelve positive/three negative diagnostics and an eight-positive/
two-negative reviewer example cover formation, reflexive computation, both
round trips, open evidence, and the deliberate absence of runtime agreement
with `fapp0(F)`. Five semantic definitions add no rule or `unif_rule`; warnings
and the strict audit remain 978/157 and zero/45/27. The synchronized gate
passes all 21 files in 98.423s. At that gate, recursive omega-equivalence
evidence truncation and the corresponding Sigma closure argument still
blocked the `IsNCat -> IsObjTruncCat` theorem; the Sigma theorem described
below is now active, leaving the recursive certificate representation/evidence
theorem as the blocker. Categorical invariance no longer blocks it.
General one-step truncation monotonicity is constructive rather than a
weakening rewrite. `eq_sym_trans_self`, `contractible_path_center`, and
`contractible_path_contract` prove the contractible-to-proposition base;
`is_trunc_grpd_succ` then recurses through the generated `ind_TruncLevel`
eliminator. The owners must be split: the path/base lemmas occur after
`IsGroupoidGrpd`, while the all-classifier `TruncMonotonicity` theorem occurs
after `Grpd_grpd` decoding is available. A fully explicit `@Struct_sigma`
base failed elaboration broadly, whereas retaining inferred Sigma indices
passes the focused signature and full owner-position checks. Twelve positive/
one negative diagnostics and an eight-positive/one-negative reviewer example
add six semantic definitions and no rule or `unif_rule`; warnings remain
978/157 and the strict audit remains zero/45/27. The catalog now has 1,261
checks across 39 areas, and health checks all 22 files. The open-centre
negative preserves the absence of proof erasure. Truncation-evidence
property-valuedness and general dependent-Pi closure were separately owned
and are described next; dependent-Sigma closure and recursive omega-
equivalence evidence truncation remain separate.
The synchronized CI gate passes all 22 files in
127.18s with every repository-integrity check.
Truncation evidence is now proposition-valued at every native level.
`is_contr_evidence_path` compares two contractibility witnesses through the
active dependent Sigma path view: it transports the second contraction
function along the first centre path and uses `PiFunext` pointwise in the
contractible path spaces. `is_contr_pi` and `is_prop_pi` provide exactly the
dependent-Pi bases consumed by the level theorem. A transparent
`ind_TruncLevel` declaration inhabits the result, and its base conversion is
bounded, but both applied and unapplied successor conversion probes exceed
60s after unfolding the reducible Pi/equivalence motive. The selected
`is_trunc_grpd_evidence_is_prop` stable head instead has one disjoint two-
equation rule declaration at classifier consumers; it exposes the base or
named successor helper without a proof-time equation. Sixteen positive/two
negative diagnostics and an eight-positive/two-negative reviewer example add
ten symbols and one rule declaration, keep warnings at 978/157, and keep the
strict audit at zero/45/27. The catalog has 1,279 checks across 40 areas;
health checks 23 files with a 16,557-line/685-symbol/569-rule/51-unification-
rule kernel and 1,207 positive diagnostics. Open evidence remains non-
convertible, so this theorem does not erase proofs. General dependent-Sigma
truncation bounds, package-path control, and recursive omega-equivalence
evidence truncation remain separate. The synchronized CI gate passes all 23
files in 75.41s with every repository-integrity check.
Arbitrary-level dependent-Pi truncation closure is now active.
`PiTruncClosure(n)` states the family theorem; `is_trunc_pi` uses
`is_contr_pi` at `-2`, while `trunc_pi_succ` applies the recursive theorem to
the pointwise path family and transports the result back through
`pi_happly_type_equiv` using general `TypeEquiv` invariance. A stable theorem
head has one disjoint two-equation consumer rule declaration, and the readable
`is_prop_pi` alias now routes through its `-1` specialization instead of
duplicating the pointwise equivalence proof. Ten positive/one negative active
diagnostics and an eight-positive/one-negative reviewer example add three
symbols and one rule declaration, preserve 978/157 warnings, and keep the
strict audit at zero/45/27. The catalog has 1,290 checks across 41 areas;
health checks 24 files with a 16,606-line/688-symbol/570-rule/51-unification-
rule kernel and 1,217 positive diagnostics. Open pointwise evidence remains
non-convertible. The synchronized CI gate passes all 24 files in 131.21s.
At the Pi-closure gate, dependent-Sigma closure and recursive omega-equivalence
evidence truncation remained separate; the Sigma theorem is described next.
Same-level dependent-Sigma truncation closure is now active.
`is_contr_sigma` constructs the contractible-total base from contractible base
and fibres. At a successor, `trunc_sigma_succ` recursively truncates the
`SigmaPathView` of two total points: base-path evidence comes from the base
hypothesis, while reducible `PathOver` exposes an equality after transport to
which the source-fibre hypothesis applies. `is_trunc_sigma` is a stable head
with one disjoint two-equation consumer rule declaration; both hypotheses stay
visible. Ten positive/two negative active diagnostics and an eight-positive/
two-negative reviewer example add four symbols and one rule declaration,
preserve 978/157 warnings, and keep the strict audit at zero/45/27. The
catalog has 1,302 checks across 42 areas; health checks 25 files with a
16,721-line/692-symbol/571-rule/51-unification-rule kernel and 1,227 positive
diagnostics. The synchronized CI gate passes all 25 files in 136.09s.
The remaining recursive omega-equivalence evidence theorem is not proof-ready:
`OmegaEquivAlong_D0` is an opaque constant with no general constructor or
eliminator, and its compatibility fibre has only a one-sided retraction. The
finite observation/path view now exposes all four current observations and a
one-way encoder, but the rejected recursive equality rule shows that it does
not supply a bounded reverse decoder or evidence eta. A certificate-
representation redesign or independently justified recursion-safe evidence-
path capability is still required before property-valuedness can be derived;
it must not be postulated from the observations alone.
Truncated-universe carrier/evidence path control is now active.
`TruncGrpdPathView(n,X,Y)` pairs a carrier path with the dependent `PathOver`
between retained evidence fields. The reviewed native-package eliminator
supports constructor-level decoding; proposition-valued evidence reconstructs
the second field from any carrier path. Carrier projection and reconstruction
have named propositional round trips, reconstruction at reflexivity is proved,
and `trunc_grpd_carrier_path_type_equiv` packages the two path classifiers as
an ordinary `TypeEquiv`. Its forward and selected inverse projections compute,
but the inverse laws and generic encode/decode round trip are deliberately not
runtime cancellation. Fifteen positive/three negative active diagnostics and
an eight-positive/three-negative reviewer example add 22 symbols and no rule
or `unif_rule`, preserve 978/157 warnings, and keep the strict audit at
zero/45/27. The catalog has 1,320 checks across 43 areas; health checks 26
files with a 17,447-line/714-symbol/571-rule/51-unification-rule kernel and
1,242 positive diagnostics. Restricted ambient-univalence agreement and the
expected universe-level truncation theorem remain separate; the latter also
needs a truncation theorem for carrier equivalences. The synchronized CI gate
passes all 26 files in 188.15s.
Restricted truncated-universe univalence is now active. The decoder capability
is packaged once as `grpd_univalence_type_equiv`; composing it in categorical
order with `trunc_grpd_carrier_path_type_equiv` yields
`trunc_grpd_univalence_type_equiv`. Its forward map is exactly ambient
`idtoequiv_grpd` after carrier projection, and its selected inverse is exactly
`grpd_equiv_path` followed by evidence-derived package reconstruction. Two
named propositional round trips and inverse reflexivity preserve the runtime
boundary; only forward reflexivity computes. Twelve positive/three negative
diagnostics and an eight-positive/three-negative reviewer example add seven
semantic symbols and no rule or `unif_rule`, preserve 978/157 warnings, and
keep the strict audit at zero/45/27. The catalog has 1,335 checks across 44
areas; health checks 27 files with a 17,547-line/721-symbol/571-rule/
51-unification-rule kernel and 1,254 positive diagnostics. This is restricted
decoder-mediated compatibility, not direct observational universe identity.
The expected package-universe level theorem remains separate; a focused
explicit-inverse probe establishes its contractible `TypeEquiv` base without
proof erasure. The synchronized CI gate passes all 27 files in 282.49s.
The expected truncated-universe level theorem is now active. At the
contractible base, `contractible_map_by_inverse` gives every map a constant
inverse at the source centre, proposition-valued `IsEquivMap` evidence makes
the evidence fibres contractible, and `contractible_type_equiv` applies the
existing Pi/Sigma closure. At successors, the function space inherits target
truncation and equivalence evidence is raised from proposition-valuedness;
source truncation is intentionally not a branch discriminator because only
the base needs it. The stable `is_trunc_type_equiv` owner has one disjoint
two-equation rule declaration, and `is_trunc_grpd_universe` transports the
result through restricted package univalence to prove
`IsTruncGrpd(trunc_succ n,TruncGrpdU n)`. Seventeen positive/three negative
diagnostics and an eleven-positive/three-negative reviewer example add ten
semantic symbols and one rule declaration, preserve 978/157 warnings, and
keep the strict audit at zero/45/27. The catalog has 1,355 checks across 45
areas; health checks 28 files with a 17,735-line/731-symbol/572-rule/
51-unification-rule kernel and 1,271 positive diagnostics. No same-level
universe theorem, direct universe identity, or proof erasure is installed.
The synchronized CI gate passes all 28 files in 155.30s.
The Product reflexivity-provenance cleanup removes the two competing runtime
collapses from `iso_evidence_product(refl,refl)` and
`omega_equiv_along_product_D1(refl,refl)` to their unrelated generic
reflexive evidence heads. Componentwise Product constructors are now the
selected normal forms at reflexivity. Their forward/inverse and decoder
projections compute; selected inverse-arrow observations still join the
generic Product identity spelling, while recursive cells and full decoder
paths deliberately retain their structured Product heads. No replacement
rewrite or `unif_rule` is installed because no typed consumer requires the
proof-time comparison, and omega-evidence property-valuedness remains
unproved. Eleven explicitly scoped Product diagnostics, the adjacent
ordinary-iso and categorical-decoder controls, and a nine-positive/five-
negative reviewer example pass. Owner-position quiet source/check logs end in
`20260716-025427`/`030307`, warning-enabled logs end in
`20260716-030323`/`030715`, and the focused reviewer log ends in
`20260716-031113`. Removing the collapses lowers unjoinable reports by six,
from 978 to 972, while replaceable advisories remain 157 and the strict audit
remains zero/45/27. The catalog has 1,360 checks across 46 areas; health checks
29 files with a 17,714-line/731-symbol/570-rule/51-unification-rule kernel and
1,271 positive diagnostics. Synchronized 29-file CI passes in 189.90s.
The first elementary observational-equality subgate gives the four visible
Boolean constructor pairs their Unit/Empty classifier matrix. Owner-position
evidence rejects the initially probed `eq_refl -> tt` normalization: that
orientation required Boolean-specific J, PathSym, Core, path-unit, and two
encoder registrations and added exactly 42 unjoinable reports (14 literal-
reflexivity consumer overlaps, 12 PathSym functoriality/action/naturality
overlaps, and 16 Core overlaps including four ill-typed displayed-target
combinations). The promoted minimum adds only the four classifier equations.
Generic `eq_refl` retains its runtime provenance, so every existing literal-
reflexivity consumer continues to compute without a new registry; raw `tt`
proofs receive no second beta and no proof-time equation. Twenty-two positive
and eleven negative diagnostics plus an eleven-positive/six-negative reviewer
example pass. Quiet owner/check logs end in `20260716-034236`/`034410`, the
warning-enabled owner/check logs end in `20260716-034258`/`034311`, and the
reviewer log ends in `20260716-034631`. Warnings remain 972/157, the strict
audit remains zero/45/27, the catalog has 1,393 checks across 47 areas, and
health checks 30 files with a 17,728-line/731-symbol/571-rule/51-unification-
rule kernel and 1,293 positive diagnostics. Synchronized 30-file CI passes in
143.199s.
The matching Unit subgate applies the same provenance policy to the sole
visible constructor. One equation reduces `tt = tt` to `Unit_grpd`; generic
`eq_refl Unit_grpd tt` remains the proof normal form, all existing literal-
reflexivity consumers compute, and raw `tt` receives neither a second beta nor
a proof-time equation. Ten positive/nine negative diagnostics and a seven-
positive/six-negative reviewer example pass. Quiet owner/check logs end in
`20260716-040227`/`040238`, warning-enabled logs end in
`20260716-040248`/`040259`, and the reviewer log ends in
`20260716-040444`. Warnings remain 972/157, the audit remains zero/45/27, the
catalog has 1,412 checks across 48 areas, and health checks 31 files with a
17,737-line/731-symbol/572-rule/51-unification-rule kernel and 1,303 positive
diagnostics. Synchronized 31-file CI passes in 153.385s.
The recursive Nat subgate adds the four zero/successor classifier equations:
zero reflexivity exposes Unit, the two mixed cases expose Empty, and successor
equality recurses to predecessor equality. The first classifier-only candidate
passed quiet and 972/157 warning probes, but invalidated the pre-existing broad
`ind_eqr _ u (eq_refl _)` beta. In the focused proof-dependent
`NatJProbeMotive`, Lambdapi accepted a predecessor-reflexivity J term at the
predecessor-indexed result and normalized it to the outer-reflexivity branch,
while an executable negative confirmed that branch did not inhabit the
declared result type. The same broad rule could already consume foreign Unit
and Boolean reflexivity because their visible equality classifiers reduce to
the same `Unit_grpd`.

The promoted prerequisite therefore makes J's category and repeated endpoint
real LHS subject-reduction discriminators. Outer reflexivity still computes;
raw `tt`, foreign reflexivity, and predecessor reflexivity remain stuck at J,
and no registry or `unif_rule` is added. The guard also removes the old generic-
J/PathRecord shaped-reflexivity critical pair, improving warnings from 972/157
to 971/157. The Nat area has 23 positive/11 negative diagnostics, the separate
J-guard area has four negative diagnostics, and the reviewer example has 11
positive/eight negative statements. Rejected unguarded quiet source/check logs
end in `20260716-041943`/`042647`; its warning logs both end in
`20260716-042708`, and the adversarial subject-reduction log ends in
`20260716-043035`. Selected guarded quiet source/check logs end in
`20260716-043247`/`043414`, warning-enabled logs end in
`20260716-043427`/`043428`, and the reviewer log ends in
`20260716-043749`. The strict audit remains zero/45/27. The catalog has 1,450
checks across 50 areas; health checks 32 files with a 17,753-line/731-symbol/
573-rule/51-unification-rule kernel and 1,326 positive diagnostics. The
synchronized 32-file CI gate passes in 151.336s.
The general binary-sum subgate extends the same guarded provenance contract to
parameterized constructors. Four equations reduce inl/inl and inr/inr paths to
their component equality and the two mixed cases to `Empty_grpd`. Generic
outer sum reflexivity remains the proof normal form; component reflexivity is
separately typed by the reduced classifier but receives no J/path/encoder beta
and no proof-time equation. A proof-dependent injective-motive probe confirms
that generic J remains stuck on component reflexivity and that its outer-
indexed branch does not inhabit the component-indexed result.

The first LHS-minimal candidate was critical-pair neutral but retained six
Lambdapi replaceable-variable advisories on reconstructible constructor
indices. Inferring the unused opposite summand and both indices in mixed-tag
clauses removes all six without changing computation. Final quiet source/check
logs both end in `20260716-050336`; final warning-enabled logs both end in
`20260716-050351`; the proof-dependent guard log ends in
`20260716-050426`; and the reviewer log ends in `20260716-050744`. Twenty-four
positive/eleven negative diagnostics and a twelve-positive/eight-negative
reviewer example pass. Warnings remain 971/157 and the strict audit remains
zero/45/27. The catalog has 1,485 checks across 51 areas; health checks 33
files with a 17,777-line/731-symbol/574-rule/51-unification-rule kernel and
1,350 positive diagnostics. The synchronized 33-file CI gate passes with
161.044s of measured checking time
(167.96s wall time), closing the elementary visible-constructor lane.
The displayed-identity/`tdapp0` follow-up replaced the primitive
`id_transfd` normal form by a transparent generic-`id` view and removed 19
older identity critical-pair reports. The complete typed projection-order
package for Cat-valued component naturality, including both identity-base
degenerations, adds 34 classified reports, for a net increase of 15 over the
previous baseline. Its outer category must remain inferred: a product-valued
target can reduce `Functor_cat(X,A×B)` to a product head before the bridge is
selected. A rigid-head alternative fails that product-target diagnostic.
Displayed vertical-composite components now project pointwise through two
SOP-minimal `tdapp0_fapp0` clauses, mirroring the ordinary `tapp0_fapp0`
projection beta. Their outer inferred slots are `_`; the inner composite's
rigid `Functord_cat` or `Transf_cat` category is the discriminator and retains
the information required for subject reduction. The rules pass the generic
strict-action diamond, both identity units, product-target normalization, and
one further component projection without changing the warning inventory. The
reverse fully capped contraction remains rejected: it chooses the wrong
component-projection normal form and its minimal LHS also fails subject
reduction. A proof-time comparison is not a substitute for the selected
runtime projection beta.

The 2026-08-01 PSSS-01 tranche adds the first algebraic-geometry-facing
one-way standard-library module without changing `emdash3_2.lp`.
`Psh_cat(K)` is a rigid Cat-valued presheaf category over `K^op`; `Obj` and
`Hom_cat` project to the active Catd hierarchy, while one direct proof-time
comparison recovers the opposite base. `Psh_pullback_func(F)` is transparent
restriction through `Pullback_catd_func(Op_func(F))`. Its object action
computes through the existing pullback owner and its map action is the generic
functor action; no presheaf-specific identity, composition, naturality, or
point-component rule is installed. Abstract/opposite/nested-opposite typed
comparisons, variance and runtime non-collapse, restriction, and map-action
typing have central and reviewer diagnostics. The owner-position probe is
warning-neutral at `1179 = 1020 + 159`, and strict LHS audits report zero
unreviewed candidates in both the kernel and the new module. The measured
Psh-headed point-component projection remains consumer-gated for PSSS-02.
The regenerated catalog has `1736` checks across `64` mapped areas, health
passes `43` targets, and full CI's Lambdapi sweep checks those targets in
`118.511s` before the repository, book, audit, and catalog gates pass.

The PSSS-02 tranche keeps that boundary rather than adding a facade bridge.
`yoneda_psh_func(K)` is transparently `hom_con_int(id_K)`, so its object,
arrow, and point-component computations are already owned by the active
represented-hom calculus. `arrow_into_catd(K)` Sigma-totalizes those
representables; `Into_restr_cat(U)` names its restriction-oriented fibre and
`Slice_cat(U)` its conventional opposite. `HigherSieveClassifier(K)` applies
the existing contravariant Catd classifier to that total, and
`maximal_higher_sieve(U)` is the existing terminal family. No new rewrite or
unification rule is introduced. The higher-sieve category and presheaves on
the slice compare through the shared proof-time intermediary
`Catd_cat(Into_restr_cat(U))`; their heads deliberately do not directly
convert because experimental unification rules are not transitively chained.
Ordinary subterminal sieves remain absent from the basic presheaf module;
at the PSSS-02 checkpoint, `Omega`, topology, and descent were still absent.
The downstream PSSS-03a/PSSS-04a paragraphs record the later ordinary-sieve
and direct-topology layers without changing this module boundary.
The synchronized PSSS-02 catalog has `1749` checks across `65` mapped areas;
health passes all `44` source/example targets in `177.462s` at source snapshot
`sha256:ed32de14c4750aac2dd92b537a24983ee471697c2d0f4379ecad482e0284936e`.
The strict kernel/module audits and inherited `1179 = 1020 + 159` warning
inventory remain unchanged. Full integration CI passes with a fresh `44`-target
Lambdapi sweep in `191.463s`, `39` Python tests, `5` registry tests, all
document/book gates, strict audit, and strict catalog freshness.

The bounded PSSS-03a tranche adds a separate one-way ordinary-sieve module,
again without editing the kernel. `IsSubterminalCat(C)` combines
`IsPropGrpd(Obj(C))` with native `IsGroupoidalCat(C)`: the first field alone
would not exclude nontrivial directed endomorphisms. The selected contract
derives `IsDiscreteCat(C)`, has canonical proposition-valued `Path_cat`
examples, and has proposition-valued evidence. `Sieve(U)` retains a
`HigherSieve(U)` plus pointwise subterminal evidence, whose dependent function
space is also a proposition. `sieve_pullback(p)` delegates to the existing
higher-sieve classifier action and preserves evidence by selection at the
postcomposed arrow. No new runtime or unification rule is installed.

This tranche deliberately does not bind `Omega`. The ordinary-sieve carrier
has not yet been proved a set, and pulling a retained-evidence package back
along an identity does not judgmentally reconstruct the original package.
An ephemeral primitive-family candidate was warning-neutral only after using
an inferred source but still failed that identity observation. Setness plus an
owner-aligned contravariant family assembly are therefore explicit PSSS-03b
gates, not details hidden by a placeholder. The focused module, reviewer
example, and nine central diagnostics pass. The synchronized catalog has
`1758` checks across `66` areas with zero legacy or unclassified checks, and
health passes all `46` source/example targets in `245.978s` at source snapshot
`sha256:60e1b0a1b2bb2a7d2ada8b87bb333dba1aeb3bcd2cdfa3bd3d4c8f046114dbe2`.
Full integration CI passes with a fresh `46`-target Lambdapi sweep in
`169.931s`, `39` Python tests, `5` registry tests, all document/book gates,
strict audit, and strict catalog freshness.

The focused PSSS-04a tranche adds the rule-free direct-topology module.
`SieveMembership(R,(V,f))` is the object classifier of the subterminal sieve
value and is proposition-valued. `maximal_sieve(U)` is the constant
`Path_cat(Unit_grpd)` family; pullback computes to the maximal sieve on the
source without identifying that literal path category with `Terminal_cat`.
`SieveCoverage(K)` assigns a packaged proposition to every ordinary sieve,
and `IsGrothTopology` stores exactly maximality, pullback stability, and local
character. Local character quantifies genuine restriction-total arrows,
membership evidence, and the existing `sieve_pullback` operation.

The generic `chaotic_groth_topology(K)` makes every sieve covering, so all
three laws compute to `tt`; its `Terminal_cat` instance is the first small
direct combinatorial site. The final quiet and warning-enabled probes pass at
the inherited `1179 = 1020 + 159` warning inventory, the new module has zero
strict-LHS candidates, and focused module/example/central checks pass. Catalog,
health, prose, and final integration CI synchronization subsequently pass at
the exact PSSS-04a baseline recorded in the active living plan.

The independent PSSS-06a tranche adds the rule-free
`emdash3_2_commutative_algebra.lp` object layer. `CommRingOps(A)` stores zero,
one, addition, negation, and multiplication; `IsCommRing(A,ops)` separately
stores additive associativity/commutativity/right-unit/right-inverse,
multiplicative associativity/commutativity/right-unit, and left
distributivity. Commutativity derives the omitted mirror laws. `CommRing`
retains the carrier as a `SetU_grpd` package, so
`comm_ring_carrier_is_set(R)` is available to later morphism-equality work.
The API exposes readable constructors, all eight law projections, and
element-level operations without adding computation beyond the existing
Sigma/function/equality owners.

The checked `zero_comm_ring` is carried by `Unit_grpd`; its open unit laws use
`unit_is_contr` because open Unit variables do not eta-reduce to `tt`. The
module has 453 lines, 48 declarations, and no rule. Its 77-line reviewer has
16 assertions, including a negative package-eta boundary. Fifteen central
checks raise the synchronized catalog to 1,785 checks across 68 areas, with
zero unclassified entries. Health passes all 50 source/example targets in
289.311 seconds at source snapshot
`sha256:32360746ed53dcfb3c2d82bdd1db811151449897b68092217e242a40b2b7217f`.
The owner warning stream remains inherited at `1179 = 1020 + 159`, and the
module-specific strict audit has no clause to report. The downstream
ring-morphism/category tranche is recorded next; localization, finite
families, powers, polynomials, and Zariski constructions remain separate
consumer-gated tranches. Full
integration CI passes a fresh 50-target Lambdapi sweep in 255.698 seconds,
then 39 Python tests, 5 document-registry tests, shell/source/header/reference
lints, book evidence/typography/KaTeX/assembly checks, strict kernel audit,
and strict catalog freshness. The tranche is included in the authorized local
foundation checkpoint.

The subsequent PSSS-06b tranche adds
`emdash3_2_commutative_algebra_category.lp`. A `CommRingHom(R,S)` is a carrier
function paired with explicit zero, one, addition, negation, and
multiplication preservation. Target-carrier sethood makes every preservation
classifier and their combined law package proposition-valued; dependent-Pi
and dependent-Sigma truncation closure then make the full morphism classifier
set-valued. `CommRing_cat` projects directly to `CommRing` objects and
`Path_cat(CommRingHom(R,S))` hom categories, yielding the checked
`comm_ring_cat_is_one_cat` witness without an extra object-classifier facade.

The public API exposes constructors, the transparent carrier function and
point application, all five readable preservation projections, morphism
sethood, pointwise structured-map extensionality, and generic
identity/composition aliases. Whole category identity and composition remain
the existing generic owners. No whole Sigma package is
reconstructed and no broad `sigma_Fst(id/comp_fapp0)` bridge is installed:
the measured broad projection experiment exceeded the 60-second bound, and a
transparent defined wrapper cannot legally own additional rewrite clauses.
The reviewer records both the absence of package eta and the deliberate lack
of projected generic-identity computation. A carrier functor remains gated on
a ring-valued-presheaf consumer and a stable action normal form.

The category module has 394 lines, 29 declarations, two rules, and no
unification rule. Its 134-line reviewer contains two local constructor symbols
and 18 checks, including the two negative boundaries. Eleven central checks
raise the catalog to 1,796 checks across 69 areas with zero unclassified
entries. The final owner warning log
`logs/probes/emdash3_2_commutative_algebra_category-20260801-100906.log`
inherits exactly `1179 = 1020 + 159`; module and full strict audits report zero
unreviewed candidates. Health passes all 52 source/example targets in 281.632
seconds at source snapshot
`sha256:81a135d9add2e80359523e36507998daf854b65cdae37c29dfa2a9728c548bec`.
Focused source, central diagnostics, the reviewer, `make check`, and
`make examples` are green. Full integration CI passes all 52 Lambdapi targets
in 241.466 seconds, followed by 39 Python tests, 5 document-registry tests,
shell/source/header/reference lints, book evidence/typography/KaTeX/assembly
checks, strict kernel audit, and fresh strict catalog verification.

The subsequent PSSS-07a tranche adds
`emdash3_2_commutative_algebra_localization.lp` and uses its first uniqueness
consumer to justify `CommRingHomPointwisePath` and `comm_ring_hom_ext` in the
upstream morphism module. The extensionality proof uses `PiFunext` for carrier
functions and proposition-valued law fibres for the dependent Sigma path; it
does not install package eta.

`CommRingUnitEvidence(R,x)` retains an inverse and the equation `x*y=1`.
Commutativity, associativity, and unit laws prove any two retained inverses
equal by the standard six-step multiplication chain. Carrier sethood then
makes the inverse path and dependent law `PathOver` contractible, so the full
unit-evidence classifier is proposition-valued. A factor through
`iota : R -> L` retains `k : L -> S` plus the pointwise triangle
`k(iota(x))=h(x)`. `IsCommRingLocalizationAt` asks that `iota(f)` be a unit and
that this factor classifier be contractible for every map `h` sending `f` to
a unit; `CommRingLocalizationAt` packages a chosen target, map, and property.
Named projections expose each field without an eta rule.

The reviewer supplies a derived nonempty model: the one-element zero ring
localized at its unique element is itself. Unit contractibility constructs
the centre triangle; a competing triangle yields pointwise map equality;
structured-map extensionality and property-valued triangle evidence complete
the contractible Sigma factor space. This exercises the complete universal
property without numerator/exponent or quotient syntax and without projected
generic-category computation.

The localization module has 626 lines, 31 declarations, and no rewrite or
unification rule. Its 324-line reviewer has 11 local theorem/constructor
symbols, 14 positive checks, and one negative package-eta boundary. Twelve
central diagnostics raise the catalog to `1808 = 1615 + 193` checks across 70
areas with zero unclassified entries. The final owner warning log
`logs/probes/emdash3_2_commutative_algebra_localization-20260801-105911.log`
inherits exactly `1179 = 1020 + 159`; its strict module audit reports zero
candidates across zero clauses. Health passes all 54 source/example targets
in 260.697 seconds at source snapshot
`sha256:7344886d649c97bd34312ee60a11632a9502149c860d6093d4a855a9471ed880`.
Focused source, central diagnostics, the reviewer, `make check`, and
`make examples` are green. Full integration CI passes all 54 Lambdapi targets
in 245.809 seconds, followed by 39 Python tests, 5 document-registry tests,
shell/source/header/reference lints, book evidence/typography/KaTeX/assembly
checks, strict kernel audit, and fresh strict catalog verification. The
tranche is included in the authorized local foundation checkpoint.

The subsequent PSSS-07b tranche adds
`emdash3_2_commutative_algebra_localization_comparison.lp`. Its first overlap
consumer needs pointwise application of a composite structured ring map. The
upstream category module therefore gains the rigid
`comm_ring_hom_comp_pointwise(g,f)` head, whose first Sigma projection computes
to `x |-> g(f(x))`, plus a proof-time comparison with generic
`CommRing_cat` composition and the named theorem view
`comm_ring_hom_comp_pointwise_path`. Generic `comp_fapp0` remains the
whole-arrow runtime owner, and application of that generic composite still
does not reduce pointwise. The green research probe also tested a stable
identity head, but no current PSSS-07b construction consumes it, so it was not
promoted. No carrier functor is added.

The downstream rule-free module proves that unit evidence transports along
paths, is preserved by structured ring maps, is closed under multiplication,
and can be extracted for each factor of a unit product. It packages a chosen
localization at `f` followed by a chosen localization at the image of `g`, and
uses the selected stable composite as its structure map. The two-stage unit
laws prove that this map sends `f*g` to a unit.

Given a chosen localization at `f*g`, its universal property supplies the
forward comparison factor. For the reverse direction, its map first factors
through localization at `f`; the resulting pointwise triangle transports the
unit image of `g`; and the intermediate map then factors through the second
localization. The two staged triangles compose to a triangle over `R`.
`CommRingIteratedLocalizationComparison` packages these forward and reverse
factors and exposes named map/agreement projections. It does not identify the
chosen packages or yet prove the maps inverse; nested factor uniqueness and a
stable identity comparison remain gated on a basic-open equivalence consumer.

The updated category module has 543 lines, 34 declarations, three rules, and
one unification rule. The new comparison module has 1,201 lines, 38
declarations, and no rewrite or unification rule. The 197-line reviewer has 16
positive checks and one negative generic-composite application boundary;
eleven positive and one negative central diagnostics cover the same API.
Focused source, reviewer, and central checks, maintained `make check`, and the
complete reviewer suite are green. The warning-enabled promoted source log
`logs/probes/emdash3_2_commutative_algebra_localization_comparison-20260801-114944.log`
inherits exactly `1179 = 1020 + 159`; strict module audits report zero
unreviewed candidates. The catalog has `1820 = 1626 + 194` checks across 71
areas with zero legacy or unclassified entries. Health passes all 56 targets
in 342.143 seconds at source snapshot
`sha256:ca42854edb4bdbfb75fb2c1efde198708a9fb5099b3e1f70627777a1518004c1`.
The active authority texts and formal-presentation module map are synchronized.
Full integration CI passes all 56 Lambdapi targets in 331.672 seconds,
followed by 39 Python tests, 5 document-registry tests,
shell/source/header/reference lints, book evidence/typography/KaTeX/assembly
checks, strict kernel audit, and fresh strict catalog verification. The tranche
is included in the authorized local foundation checkpoint.

The subsequent PSSS-07c tranche separates a 107-line reusable
`emdash3_2_finite_families.lp` module from the 735-line
`emdash3_2_commutative_algebra_finite.lp` consumer. `FiniteFamily(A,n)` is
Nat recursion into a right-associated constant-family Sigma ending in Unit;
the generic module exposes nine transparent symbols for constructors,
observations, pointwise map, and sethood. A probed `Product_grpd` successor
presentation was rejected: although its carrier computations passed, its
rigid classifier head did not directly consume generic Sigma truncation, and
this consumer does not justify a Product/Sigma comparison rule.

The algebra module has 21 transparent symbols and no rule or unification
rule. It defines right-associated finite sums and dot products and proves by
Nat induction that structured ring maps preserve both. An unimodular
presentation retains coefficients and `sum_i a_i*f_i=1`; it is deliberately
set-valued data rather than a falsely proposition-valued mere-existence
claim. `CommRingZariskiCoverPresentation` retains the length, generators, and
that presentation, is set-valued, and maps along every structured ring map.
The generic singleton `[1]` is a nonempty model, while a binary helper accepts
the correct `a*f+b*g=1` unit-ideal hypothesis.

The 201-line reviewer has 20 positive and two negative checks. The negatives
retain the constant-Sigma/Product non-collapse and the absence of zero-length
Unit package eta. The central suite adds the same 22 diagnostics under one
new mapped area, yielding a fresh strict catalog of 1,842 checks across 72
areas with zero legacy or unclassified entries. Focused source, reviewer, and
central checks, maintained `make check`, and the complete reviewer suite pass.
Warning-enabled source logs
`logs/probes/emdash3_2_finite_families-20260801-123553.log` and
`logs/probes/emdash3_2_commutative_algebra_finite-20260801-123553.log` each
inherit exactly `1179 = 1020 + 159`; both strict module audits report zero
candidates across zero clauses. Health passes all 59 source/example targets
in 202.751 seconds at source snapshot
`sha256:4127068d1fa2e3dd43f22c8ca1f607d07bb8645ba1467ee22c96425c23ee5f76`,
and the active authority routing is synchronized. Full integration CI is
green: all 59 Lambdapi targets pass in 216.912 seconds, followed by 39 Python
tests, 5 document-registry tests, shell/source/header/reference lints, book
evidence/typography/KaTeX/assembly checks, strict kernel audit, and fresh
strict catalog verification. The tranche is included in the authorized local
foundation checkpoint.

This is algebraic cover-presentation data only. It does not yet construct
localizations indexed by the tuple, `Spec`, basic opens, a sieve coverage, or
a topology. Covers of a relative basic open require power/radical data such as
`s^N=sum_i a_i*f_i`, which remains consumer-gated.

The subsequent PSSS-07d tranche defines a polynomial algebra over `R` on a
variable classifier `X` only by its free-algebra universal property. For a
candidate target `P`, base map `iota : R -> P`, and variable map
`vars : X -> |P|`, a factor against `h : R -> S` and valuation
`v : X -> |S|` is a structured map `k : P -> S` retaining the pointwise base
triangle `k(iota(r))=h(r)` and variable triangle `k(vars(x))=v(x)`. The
classifier `IsCommRingPolynomialAlgebra` requires this factor space to be
contractible for every target, base map, and valuation; the chosen
`CommRingPolynomialAlgebra` package exposes target, base map, variables, and
property through transparent named observations.

The two triangle classifiers are proposition-valued by target-carrier
sethood, as is their dependent Sigma. A theorem-level PathOver helper lifts a
path between structured factor maps to a path between complete factors. The
432-line `emdash3_2_commutative_algebra_polynomial.lp` module contains 24
symbols and no rule or unification rule. It is deliberately independent of
the finite-family representation and introduces no monomial, coefficient,
quotient, `Fin`, list, ordinary-inductive, or positive-variable representation
surface.

The first executable model is generic but honestly zero-variable:
`R[Empty]=R` for every commutative ring. It uses `P=R`, the empty variable map,
and the newly justified `comm_ring_hom_id_pointwise(R)` as base map. The centre
extension is `h` itself; empty elimination supplies variable agreement, and a
competitor's base triangle plus `comm_ring_hom_ext` supplies uniqueness. This
consumer promotes one narrow `sigma_Fst` beta and one proof-time comparison at
the ring-category owner. Generic category identity remains the whole-arrow
runtime owner, and its carrier application remains a checked negative.

The category module is now 573 lines with 36 symbols, four rules, and two
unification rules. The polynomial module is 432 lines/24 symbols and rule-free.
The 429-line reviewer has 16 positive and two negative checks; the central
suite has the same 18-check boundary in one mapped area. Focused quiet logs are
`logs/probes/emdash3_2_commutative_algebra_category-20260801-131200.log`,
`logs/probes/emdash3_2_commutative_algebra_polynomial-20260801-131349.log`,
`logs/probes/commutative_ring_polynomial_algebra-20260801-132119.log`, and
`logs/probes/emdash3_2_checks-20260801-132329.log`. Warning-enabled category
and polynomial logs at
`logs/probes/emdash3_2_commutative_algebra_category-20260801-132146.log` and
`logs/probes/emdash3_2_commutative_algebra_polynomial-20260801-132145.log`
each inherit exactly `1179 = 1020 + 159`; strict audits report zero candidates
across zero unreviewed clauses. Maintained `make check`, the complete reviewer
suite, and the strict catalog of 1,860 checks across 73 areas are green.
Authority routing and mathematical/surface documentation are synchronized.
Health passes all 61 source/example targets in 314.231 seconds at source
snapshot
`sha256:35a1d735feeea679e12e62b3bc14690783758c0da59ed1e8f20522f898f075df`.
Full integration CI passes all 61 Lambdapi targets in 389.345 seconds. The
final combined checkpoint gate passes the same 61 targets in 342.266 seconds,
followed by 39 Python tests, five document-registry tests,
shell/source/header/reference lints, book evidence/typography/KaTeX/assembly
checks, strict kernel audit, and fresh strict catalog verification. The
tranche is included in the authorized local foundation checkpoint.

The subsequent PSSS-08a candidate adds the transparent classifier
`CommRingPsh_cat(K)=Functor_cat(Op_cat(K),CommRing_cat)`, named ring values,
structured restriction maps, and point application. It introduces no rigid
facade at this boundary: the ordinary functor category is the only selected
representation and current consumers carry `K` explicitly. This differs from
rigid `Psh_cat`, which usefully mediates its public head and the distinct
`Catd_cat(Op(K))` representation; a future stable-head/base-recovery consumer
may still justify an audited `CommRingPsh_cat` normal-form migration.
Generic whole `CommRing_cat` identities and composites remain opaque on
carrier elements. Named paths instead cross through the selected pointwise
identity/composition maps, so `O[id](s)=s` and
`O[f∘g](s)=O[g](O[f](s))` are available without competing runtime rules.

The first probe failed precisely at specialization of the strict identity
action: `id(Op_cat(K))` had normalized to `id(K)` before the literal generic
redex could be observed. The rule-free generic theorem `fapp1_id_path`, proved
while its source category remains abstract, is the identity analogue of the
existing `fapp1_comp_path` and closes that boundary without a
presheaf-specific rewrite. In the combined elaborator/PSSS history, the
independently validated narrow generic `Op_cat` projection-order bridge is
also retained: it selects the generic whole identity at runtime, but does not
make that whole `CommRing_cat` identity compute on carrier elements. The final
probe
`logs/probes/psss08a_comm_ring_presheaf_invertibility-20260801-151336.log` is
green and retains negative direct carrier computations for both laws.

For `s : |O(U)|`, `CommRingPshInvertibleAlong(O,s,f)` is explicit unit
evidence for `O[f](s)`. It is proposition-valued, and preservation by the
restriction map along `g` plus the composite-restriction path yields evidence
at `f∘g`. The preserved inverse computes to the image of the original
inverse. Because this generic unit operation now has both localization and
presheaf consumers, its path-transport/preservation declarations move
unchanged into the base localization/unit module. The maintained reviewer
constructs support at every arrow of the constant zero-ring presheaf.

The source has 283 lines and 14 rule-free declarations; the reviewer has 217
lines and 17 checks, including two intentional negative generic-carrier
boundaries. Focused source, reviewer, central, and maintained aggregate checks
are green. The warning-enabled source inherits exactly
`1179 = 1020 + 159`; strict audits report zero unreviewed candidates; the
catalog has 1,874 checks across 74 areas; and all 63 health targets pass in
410.967 seconds at source snapshot
`sha256:63b1c75554b4360f042aabc955243ddc96bad42a9df1848be3fd42c61cd40b03`.
Full integration CI passes all 63 Lambdapi targets in 548.573 seconds,
followed by 39 Python tests, five document-registry tests, shell/source/header/
reference lints, book evidence/typography/KaTeX/assembly checks, strict kernel
audit, and fresh strict catalog verification. The authorized checkpoint
includes this tranche. This tranche does not assemble `Sieve(K,U)`: full action and
equality/higher-arrow coherence over `Into_restr_cat(K,U)` remain the PSSS-08b
consumer gate.

The subsequent PSSS-08b implementation closes that gate through existing
family owners rather than an ad hoc sieve action. The selected
`comm_ring_carrier_func : CommRing_cat -> Grpd_cat` computes at ring objects
and exposes its **full** hom action as `path_map_func` on structured carrier
functions. There is intentionally no direct capped `fapp1_fapp0` rule; capping
after the full action computes through the existing Path-map owner, including
the `fib_cov` consumer used by restriction totals. Its transparent
`comm_ring_carrier_catd` composite is therefore iterable at higher cells.

Over the total category of ring elements,
`comm_ring_unit_evidence_total_catd` has the literal fibre
`Path_cat(CommRingUnitEvidence(R,x))`. The family retains generic Catd action;
structured-map preservation of units supplies its semantic action, and the
already proved proposition theorem makes every fibre subterminal. Only the
literal constructor fibre is selected as a runtime rule; no local identity,
composition, or capped-action rule is added.

For `O : CommRingPsh(K)` and `s : |O(U)|`, the total restriction map is the
composite

```text
Into_restr_cat(K,U)
  -> Sigma_{V:K^op} |O(V)|
  -> Sigma_{R:CommRing_cat} |R|,

(V,f) |-> (V,O[f](s)) |-> (O(V),O[f](s)).
```

The first leg is the Sigma total of `fib_cov_transf`; the second is
`sigma_pullback_total_func`. Their source comparison needs one narrow
proof-time bridge between the rigid heads `hom_(K^op,id,U)` and
`hom_con(K,U,id)`. A typed `eq_refl` diagnostic proves that the unifier fires,
while a negative conversion diagnostic proves the two heads remain distinct
at runtime.

Pulling the universal unit family back along this total map gives
`comm_ring_psh_invertibility_higher_sieve`. At a literal `(V,f)`, its fibre
reduces to

```text
Path_cat(CommRingPshInvertibleAlong(O,s,f)),
```

and its object classifier reduces to the PSSS-08a unit-evidence predicate.
`sigma_ind`—rather than a false Sigma package eta—lifts the existing
proposition theorem to `IsOrdinarySieve`; `sieve_intro` then packages
`comm_ring_psh_invertibility_sieve`. The maintained zero-ring consumer's
explicit arrowwise witness inhabits `SieveMembership` in this assembled sieve,
so the result retains the original computational motivation. Focused source,
central-diagnostic, reviewer, and maintained aggregate checks are green. The
warning-enabled owning-position source log
`logs/probes/emdash3_2_commutative_algebra_presheaves-20260801-163403.log`
inherits exactly `1179 = 1020 + 159`, with no changed-module warning location;
strict audits report zero unreviewed candidates. The strict catalog has 1,893
checks across 75 areas, including 19 checks in the dedicated PSSS-08b area,
and zero unclassified entries. Health passes all 63 targets in 437.026 seconds
at source snapshot
`sha256:5a969bf2de9ebccd9ff02739dae4964f5314312e1199eb7fba9983ba21c294e3`.
Full integration CI passes all 63 Lambdapi targets in 355.987 seconds,
followed by 39 Python tests, five document-registry tests, shell/source/header/
reference checks, book evidence/typography/KaTeX/assembly checks, strict
kernel audit, and fresh strict catalog verification. The tranche is included
in the authorized local PSSS-08b checkpoint.

PSSS-08c0 is the first computational locality bridge and deliberately crosses
neither the sheaf nor generated-topology gate. The rule-free
`emdash3_2_commutative_algebra_locality.lp` defines

```text
CommRingPshInvertibilityCover(T,O,U,s) = Covers_T(D_O(s)).
```

This is a proposition about one section, not a claim that every section is
locally invertible or that `O` is a local-ring object. More importantly, for a
chosen localization `ell : Loc_{O(U)}(s)` and literal support member
`m : (f:V->U) in D_O(s)`, the membership computation supplies unit evidence
for `O[f](s)`. The existing contractible localization-factor owner then
selects a structured map

```text
O(U)[1/s]_ell -> O(V)
```

and exposes the carrier triangle `factor(ell,f,m)(ell(x)) = O[f](x)`. The
maintained zero-ring reviewer is a closed executable consumer: its selected
factor at the terminal support member reduces to the actual restriction map
of the constant presheaf. This is the pointwise front of the historical
Cartier condition `lim_{V in D(s)} O(V) = O(U)[1/s]`. At the PSSS-08c0
checkpoint, internal cone assembly, the limiting/descent equivalence, and
sheaf/ringed-site packaging remained explicit next gates; PSSS-08c0C below
closes the first of those gates without crossing the latter two.

The candidate owner has 176 lines, seven symbols, zero rules, and zero
unification rules. Its 145-line reviewer has eight assertions. Focused quiet
owner, reviewer, and central-diagnostic logs are
`logs/probes/emdash3_2_commutative_algebra_locality-20260801-205516.log`,
`logs/probes/commutative_ring_presheaf_locality-20260801-205527.log`, and
`logs/probes/emdash3_2_checks-20260801-205606.log`. Warning-enabled owner and
reviewer logs at timestamp `20260801-205630` inherit exactly
`1179 = 1020 + 159`, with no changed-module warning. The strict rule audit
remains at zero unreviewed clauses and 52 annotated slots across 32
intentional clauses. Five central diagnostics raise the strict catalog to
1,922 checks across 79 mapped areas with zero unclassified entries. Maintained
`make check` and the complete reviewer suite pass. Health passes all 70 source/
example targets in 572.748 summed check-seconds at source snapshot
`sha256:4ceeabad2faf2005b306f78053a3fed6a198576df2138b84d2404e8d8b7379da`.
Full integration CI independently passes all 70 Lambdapi targets in 569.345
summed check-seconds, followed by 39 Python tests, five document-registry
tests, shell/source/header/reference checks, book evidence/typography/KaTeX/
assembly checks, strict kernel audit, and fresh strict catalog verification.
The tranche is included in the authorized local PSSS-08c0 checkpoint
`9db8307`.

PSSS-08c0C closes internal localization-cone assembly. It forms
`Elem(D_O(s))` as the Sigma total of the invertibility sieve, composes its two
existing Sigma projections with `O`, and obtains the diagram
`(V,f,m) |-> O(V)`. One injective transformation owner has type

```text
factorCone(ell) : Const(O(U)[1/s]_ell) => O o dom
```

and its sole component rule computes at the literal element `(V,f,m)` to the
PSSS-08c0 selected universal factor. The ordinary `Transf` classifier provides
the full off-diagonal action; generic `tapp1` cut elimination, rather than a
new family of external squares, owns naturality.

The theorem-level construction audit remains useful. For `f:V->U`, `g:W->V`,
and `m:f in D_O(s)`, mapping the factor triangle at `f` by `O[g]`, followed by
the existing presheaf composition path, packages
`O[g] o factor(ell,f,m)` as a competing factor over `O[f o g]`. Existing
contractibility then gives

```text
factor(ell,f o g,g^*m) = O[g] o factor(ell,f,m).
```

This equality validates the exposed literal components; downstream descent
uses the internal cone and does not retain the equality as an extra
naturality field. The maintained candidate now has 537 lines, fifteen
transparent symbols, one injective transformation owner, one component rule,
and zero unification rules. Its 341-line reviewer has fifteen assertions,
including a closed computation from the literal cone component to the actual
zero-presheaf restriction. Ten central diagnostics cover the PSSS-08c0/08c0C
area. Focused owner, reviewer, and central quiet logs end in `220202`, `220227`,
and `220335`. Warning-enabled maintained owner and reviewer logs end in
`220948` and each inherits exactly `1179 = 1020 + 159`, with no warning at the
changed owner or reviewer. Strict audit reports zero unreviewed locality
clauses and the unchanged kernel total of 52 annotated slots across 32
intentional clauses. Maintained `make check` and the complete reviewer suite
pass. Five new central diagnostics raise the fresh strict catalog to 1,927
checks across 79 mapped areas with zero unclassified entries. Health passes
all 70 source/example targets in 653.252 summed check-seconds at source
snapshot
`sha256:28a8c142d1a0f469349b6af5204ae0270e55a3cb6343c116b3458e8727e1c2e5`.
Full integration CI independently passes all 70 Lambdapi targets in 534.210
summed check-seconds, followed by 39 Python tests, five document-registry
tests, shell/source/header/reference checks, book evidence/typography/KaTeX/
assembly checks, strict kernel audit, and fresh strict catalog verification.
Neither a limiting/descent equivalence nor sheafhood, `Spec`, or a scheme is
claimed. The tranche is included in the authorized local PSSS-08c0C
checkpoint `a724638`.

PSSS-08c0D makes the first direct computational consumer of that cone. Pulling
`comm_ring_carrier_catd` back along the internal CommRing-valued support
diagram gives a family whose literal `(V,f,m)` fibre is
`Path_cat(|O(V)|)`. Its section category

```text
Matching_O(s) = Pi_(V,f,m in D_O(s)) Path_cat(|O(V)|)
```

retains compatibility under every arrow of the support-elements category.
For `x : |O(U)[1/s]_ell|`, one stable section owner computes by

```text
restrict_ell(x)[V,f,m] = factor(ell,f,m)(x).
```

The component deliberately follows the carrier API's selected full-action
route: `fib_cov_tapp0_func` receives `x` before the structured factor map.
Ordinary postcomposition of the ring-valued cone would cap that action too
early and leave element application stuck. No direct capped carrier rule and
no generic projection/cut rewrite is added. The four structural `tapp0_fapp0`
slots on the literal beta remain inferred; its nested Sigma object and stable
section head recover the indices.

`path_lift_fapp0` turns the section-valued function into a genuine functor

```text
Path_cat(|O(U)[1/s]_ell|) -> Matching_O(s),
```

so both localization-element action and equality-path action are internal.
The Pi/Catd classifiers retain matching coherence; consumers do not carry
external naturality squares, identity laws, or composition laws. The closed
zero-ring reviewer evaluates the resulting section at the terminal support
member to the actual constant-presheaf restriction. This is only the
localization-to-matching direction. An inverse/glue package, its executable
component, inverse laws justified by a concrete descent/basic-open consumer,
and later affine overlap evaluation remain separate gates.

The maintained matching module has 135 lines, four symbols, one injective
section owner, one rewrite rule, and zero unification rules. Its 243-line
reviewer has eight assertions. Warning-enabled locality baseline, matching
owner, and reviewer logs ending in `20260801-234652`, `20260801-234706`, and
`20260801-234729` inherit exactly `1179 = 1020 + 159`, with no warning at the
new owner or reviewer. The module-specific strict audit has zero
reconstructible slots across zero unreviewed clauses; the full audit remains
at zero unreviewed clauses and 52 annotated slots across 32 intentional
kernel clauses. Maintained `make check` and the complete reviewer suite pass.
Five new central diagnostics raise the strict catalog to 1,932 checks across
80 mapped areas with zero legacy or unclassified entries. Health passes all
72 source/example targets in 590.748 summed check-seconds at source snapshot
`sha256:939fd71769182759327e8aa3a759f47019d7542a1f45e6d9c08dd9c0c9504d5e`.
Full integration CI independently passes all 72 Lambdapi targets in 528.584
summed check-seconds, followed by 39 Python tests, five document-registry
tests, shell/source/header/reference checks, book evidence/typography/KaTeX/
assembly checks, strict kernel audit, and fresh strict catalog verification.
The tranche is included in the authorized local PSSS-08c0D checkpoint
`28cd0fc`.

PSSS-08c0E selects the converse needed by the computational Cartier
interface without conflating it with ordinary sheaf descent. For a chosen
localization, its public datum begins with a genuine functor

```text
glue_ell : Matching_O(s) -> Path_cat(|O(U)[1/s]_ell|).
```

Consequently arrows between coherent matching families are mapped internally
to equality paths between glued localization elements by ordinary functor
action. The package retains two component observations:

```text
glue_ell(restrict_ell(x)) = x
restrict_ell(glue_ell(m))[e] = m[e].
```

At a literal support element `e=(V,f,r)`, the second left endpoint computes
through the checkpointed matching beta to
`factor_O(ell;f,r)(glue_ell(m))`. These laws are Path-valued fields of a
transparent Sigma package, not rewrite rules and not an external family of
naturality squares. They do not yet constitute inverse transfors between the
composite functors and identities; the mandatory PSSS-08c0F audit must
internalize them or revise the interface before `Spec`. The zero-ring reviewer
constructs the datum rather than
postulating it: the functor is constant at `tt`, and Unit contractibility
proves both observations, including a closed component path to the actual
zero-presheaf restriction.

This is selected basic-open locality over `D(s)`, and `D(s)` need not cover
`U`. The candidate therefore does not claim a sheaf condition, a limiting
comparison, or a native `OmegaEquivAlong`/whole internal equivalence. It is
the direct computational
successor to the historical Cartier `mod_loc_elim` behavior and is intended
to feed a mandatory independent matching/section semantics audit, nontrivial
localization model, and first affine overlap calculation before it is allowed
to orient `Spec`. The historical source is experimental consumer evidence,
not semantic authority. Abstract generated-topology or construction-of-
sheafification work remains off this critical path; a supplied whole
sheafification reflector/adjunction remains a feasible separate MVP
capability. The maintained source, reviewer, and
central focused checks pass; warning-enabled source and reviewer checks
inherit exactly `1179 = 1020 + 159`, with no warning located in either new
file, and strict audits remain unchanged. Maintained `make check` and the
complete reviewer suite pass. Five central diagnostics raise the strict
catalog to 1,937 checks across 81 mapped areas with zero legacy or
unclassified entries. Health passes all 74 source/example targets in 535.569
summed check-seconds at source snapshot
`sha256:88e8dca37f182b8df944a54739a2cc01fb1f499f6f8e4ed7066ea7457b057e19`.
Full integration CI independently passes all 74 Lambdapi targets in 575.487
summed check-seconds, followed by 39 Python tests, five document-registry
tests, shell/source/header/reference checks, book evidence/typography/KaTeX/
assembly checks, strict kernel audit, and fresh strict catalog verification.
The implementation and synchronized authority prose are locally checkpointed
at `eb0c5b6`.

PSSS-08c0F now has its first native-equivalence and algebraic-model results.
An owner-shape probe confirms that canonical restriction has exactly the
fixed-forward classifier
`OmegaEquivAlong Cat_cat Path(localization-carrier) Matching restriction`.
An expected-negative probe confirms that the earlier Pi families of component
paths do not directly inhabit its equalities of whole composite functors. In
the other direction, a green typed probe derives equality of the native left
and right inverse functors, selects the left inverse as one computational
glue, and evaluates its two whole cancellation paths to recover both earlier
component observations and the literal Cartier factor-map equation. Thus the
whole witness retains internal naturality and higher propagation while still
exposing the desired computation; the component package alone remains
provisional.

The new 190-line, ten-symbol
`emdash3_2_commutative_algebra_localization_unit.lp` module implements the
first parametric algebra model. For any already-unit element `f` of `R`, it
constructs the pointwise identity as a localization at `f`: every map factors
through it by itself, and structured-map extensionality plus the
property-valued triangle fibre proves the full factorization Sigma
contractible. Canonical unit evidence for one therefore gives a selected
computing localization `R[1/1]=R` for every ring. The module is rule-free; its
97-line reviewer has thirteen assertions. Focused source, reviewer, and
central checks pass, and warning-enabled checks inherit exactly
`1179 = 1020 + 159` with no warning in either new file. Maintained `make check`
and the complete reviewer suite pass. Five central diagnostics raise the fresh
strict catalog to 1,942 checks across 82 mapped areas with zero unclassified
entries. Health passes all 76 source/example targets in 347.597 summed
check-seconds at source snapshot
`sha256:3c425b8e9adcb68fc80d4992f09dff913863da5185ff03c5c0532192b4cbb899`.
Full integration CI independently passes all 76 Lambdapi targets in 524.197
summed check-seconds, followed by 39 Python tests, five document-registry
tests, shell/source/header/reference checks, book evidence/typography/KaTeX/
assembly checks, the strict kernel audit, and fresh strict catalog
verification. The implementation and synchronized authority prose are locally
checkpointed at `4b93619`. This does not yet provide a genuinely nontrivial
localization, native matching equivalence model, first overlap, `Spec`, or
scheme.

The subsequent PSSS-08c0F empty-open candidate is the 504-line, 21-symbol
rule-free `emdash3_2_commutative_algebra_localization_zero.lp` module. It
derives `x*0=0`, `0*x=0`, and `-0=0`; transports admissible unit evidence to
zero in the target; proves that invertible zero forces `0=1` and hence every
carrier element equals zero; and uses the resulting structured point map to
prove the complete localization-factor Sigma contractible. Thus every ring
has a selected universal-property localization `R[1/0]` whose target is the
zero ring and whose carrier action computes to `tt`. Its 124-line reviewer has
sixteen assertions. Focused source, reviewer, and central checks pass; the
warning-enabled research probe inherits exactly `1179 = 1020 + 159` with no
candidate rule or unifier. Maintained `make check` and the complete reviewer
suite pass. Six central diagnostics raise the fresh strict catalog to 1,948
checks across 83 mapped areas with zero unclassified entries. Health passes
all 78 source/example targets in 510.118 summed check-seconds at source
snapshot
`sha256:b7b459ffd7f1e003cfca1bda95097fe44b3f592e5aea0c9cbb9b46c6dfba5ee2`.
Full integration CI independently passes all 78 Lambdapi targets in 528.561
summed check-seconds, followed by 39 Python tests, five document-registry
tests, shell/source/header/reference checks, book evidence/typography/KaTeX/
assembly checks, the strict kernel audit, and fresh strict catalog
verification. The implementation and synchronized authority prose are locally
checkpointed at `7013915`.
This provides the computational empty-basic-open endpoint but deliberately
does not close the nondegenerate localization, native matching-equivalence,
or affine-overlap gates.

The following PSSS-08c0F candidate now closes the representation-independent
algebraic overlap-equivalence construction. The 987-line, seventeen-symbol,
rule-free
`emdash3_2_commutative_algebra_localization_overlap.lp` module proves that
the checkpointed canonical forward and staged reverse maps between arbitrary
chosen packages for `R[1/(f*g)]` and `R[1/f][1/g]` are inverse as whole
`CommRing_cat` arrows. Product-localization factor uniqueness proves the left
law directly. For the right law, first-localization uniqueness proves the
whole intermediate triangle; evaluating that path gives the second-stage
triangle, and second-localization uniqueness proves the whole composite equal
to identity. Existing pointwise composition/identity paths transport the
result to the generic category owners, with no external naturality field and
no new reduction or unification rule.

The two laws package the canonical forward map as
`OmegaEquivAlong CommRing_cat` with the staged reverse map in both inverse
slots, and derive a first-class `OmegaEquiv CommRing_cat` facade. Twelve
construction helpers are protected; five theorem/package symbols are public.
The 226-line reviewer has eleven assertions covering generic factor-map
uniqueness, both whole laws, both packages, inverse projections, and law
projections. Focused and maintained source, reviewer, and central-diagnostic
checks pass; warning-enabled checks inherit exactly `1179 = 1020 + 159` and
locate no warning in the rule-free candidate. The strict audit remains clean,
and five central diagnostics raise the fresh catalog to 1,953 checks across
84 mapped areas with zero unclassified entries. Health passes all 80
source/example targets in 539.883 summed check-seconds at source snapshot
`sha256:8161bb12f88fd8e829c615b6ec483271bd012b0b846038718fb0300f495b0e39`.
Full integration CI independently passes all 80 Lambdapi targets in 647.194
summed check-seconds, followed by 39 Python tests, five document-registry
tests, shell/source/header/reference checks, book evidence/typography/KaTeX/
assembly checks, the strict kernel audit, and fresh strict catalog
verification. The implementation and synchronized authority prose are locally
checkpointed at `362922d`.

This result is representation-independent: it needs only the localization
universal properties and neither assumes nor exposes fractions. It identifies
the chosen targets by an internal equivalence, not by judgmental package
equality. It therefore closes the first whole algebraic overlap theorem, but
does not yet construct a concrete genuinely nondegenerate localization model,
identify Cartier matching objects with ordinary covering-sieve descent, or
construct `Spec`, structure sheaves, or schemes.

PSSS-08c0G adds the first explicit potentially nondegenerate representation.
For a supplied idempotent `e^2=e`, the rule-free
`emdash3_2_commutative_algebra_localization_idempotent.lp` module constructs
the set-valued fixed-image ring `eR={x:R | e*x=x}` with one equal to `e` and
all five operations inherited computationally from `R`. The structured
scaling map sends `x` to `e*x`. If `h:R->S` makes `h(e)` invertible, then the
preserved idempotence and the elementary invertible-idempotent calculation
force `h(e)=1`; the selected factor sends a fixed point to its underlying
element followed by `h`. Its triangle computes, and every competing factor is
identified first pointwise, then as a whole structured map, then as a complete
factor Sigma using the proposition-valued agreement fibre. Thus the selected
package has the full existing `CommRingLocalizationAt R e` universal
property, with no fraction/quotient syntax, external naturality field,
rewrite rule, or unification rule.

Focused source, reviewer, and central diagnostics plus the maintained
`make check` and `make examples` aggregates are green. Warning-enabled source
and reviewer checks each inherit exactly `1179 = 1020 + 159` warnings, with no
warning located in either new file; the strict LHS audit remains at zero
unreviewed clauses. The generated catalog contains 1,959 checks in 85 mapped
areas with zero legacy or unclassified entries. Health passes all 82
source/example targets in 637.936 summed check-seconds at source snapshot
`sha256:b87e97a3c6a6b62e06dfd5d0c3421c73d2af627baab7c370d9bc14c4d6e9857b`.
Full integration CI independently passes all 82 Lambdapi targets in 591.033
summed check-seconds, followed by 39 Python tests, five document-registry
tests, shell/source/header/reference checks, book evidence/typography/KaTeX/
assembly checks, the strict kernel audit, and fresh strict catalog
verification. The implementation and synchronized authority prose are locally
checkpointed at `1211e06`. The representation can be genuinely nondegenerate
for a nontrivial idempotent, but this tranche does not itself construct one. A
product ring with the witnessed idempotent `(1,0)` and its affine-basic-open
restriction consumer remain the next bounded gate; general fraction models,
matching/sheaf descent, `Spec`, and schemes remain downstream.

PSSS-08c0H closes that bounded concrete-model gate with three rule-free
modules. `emdash3_2_commutative_algebra_product.lp` constructs the product
carrier as the stable `Product_grpd`, transports sethood from the equivalent
constant-family Sigma, builds all ring operations/laws componentwise, and
maps structured morphisms componentwise. It derives equality of the whole
structured maps for identity and composition using `comm_ring_hom_ext`; no
product-specific identity/composition rule or external functoriality field is
added. A first-class binary product functor remains consumer-gated because no
current consumer needs another rigid runtime owner.

`emdash3_2_commutative_algebra_f2.lp` constructs the two-element ring on
`Bool_grpd`: addition is XOR, multiplication is conjunction, negation is the
identity, and every ring law is proved by internal Boolean elimination.
`emdash3_2_commutative_algebra_localization_split.lp` then takes
`e=(1,0):R x S`, proves `e^2=e`, selects the checkpointed fixed-image
localization, and exposes its existing affine-basic-open arrow. The closed
specialization to `F2 x F2` constructs maps from `e=0` and `e=1` to `Empty` by
projecting the contradictory Boolean component. Its carrier restriction
computes transparently as `(x,y) |-> (x,0)`.

This is the first closed localization/basic-open representation that is
neither the identity endpoint nor the empty-open endpoint. It materially
supports the feasibility of computational schemes, but it is not yet a
sheaf/descent theorem: the next semantic gate must exercise the full internal
Cartier matching comparison on this model, preferably as
`OmegaEquivAlong Cat_cat`, before `Spec` consumes the provisional glue API.
The intended non-chaotic Zariski topology, any required propositional
reflection, structure sheaf, and concrete schemes remain separate later
gates.

The three source modules have 506, 254, and 169 lines, 22, 18, and 12 symbols,
and no rewrite or unification rules. The 169-line reviewer has nineteen
assertions, while nine central diagnostics bring the fresh strict catalog to
1,968 checks across 86 mapped areas with zero unclassified entries. Focused
and maintained checks, the exact inherited warning comparison
`1179 = 1020 + 159`, and the strict inferred-slot audit are green. Health
passes all 86 registered source/example targets in 419.730 summed
check-seconds at source snapshot
`sha256:49e571bee9c63afac0e25120e5271816feece3eb969fb0ed17c0893772e4b024`;
full integration CI independently passes the same 86 targets in 450.152
summed check-seconds, followed by 39 Python tests, five document-registry
tests, shell/source/header/reference checks, book evidence/typography/KaTeX/
assembly checks, the strict kernel audit, and fresh strict catalog
verification. The implementation and synchronized authority prose are locally
checkpointed at `e68b6b9`.

PSSS-08c0I now exercises that closed localization against the full internal
matching layer. On `K=Op_cat CommRing_cat`, the identity functor is the affine
CommRing-valued presheaf. Every selected localization `i:R->L` supplies a
canonical member `(L,i)` of `D(s)`, and section evaluation there is a genuine
glue functor. The selected centre factor is propositionally the whole
structured identity by localization-factor contractibility, giving
`glue(restrict(x))=x`.

For any support member `(V,h,member)`, the universal factor `k:L->V` and its
whole structured triangle form a Sigma arrow from the centre to that member.
The sieve-evidence component is selected from the retained subterminal fibre.
Applying the matching section's `piapp1_fapp0` action along this arrow gives
the Cartier equation `k(glue(m))=m(V,h,member)` inside the Pi family; two
Sigma eliminations extend it to every encoded support object. No external
naturality square, object-only functor input, or affine-specific runtime rule
is introduced.

Nested elimination required the normalized proof-time form of the existing
Yoneda represented-family comparison. It remains in the owning presheaf
module, is exercised by typed reflexivity, remains explicitly non-convertible
at runtime, and leaves the owning warning closure unchanged at 1,020
pre-existing warnings. The new 852-line affine module has eighteen symbols
and no rewrite/unification rules; its 135-line reviewer includes a closed
`F2 x F2` package check. Focused source/reviewer/central checks and the strict
audit are green. Maintained source and reviewer aggregates also pass. Seven
central diagnostics raise the fresh strict catalog to 1,975 checks across 87
mapped areas with zero legacy or unclassified entries. Health passes all 88
registered source/example targets in 476.967 summed check-seconds at source
snapshot
`sha256:2edc4569b7b62a6f1600dc622d91857765343944141f4c94ff1f9638d75bdf9d`;
the new source takes 46.527 seconds and its reviewer 25.946 seconds. Full
integration CI independently passes all 88 Lambdapi targets in 546.923 summed
check-seconds, followed by 39 Python tests, five document-registry tests,
shell/source/header/reference checks, book evidence/typography/KaTeX/assembly
checks, the strict kernel audit, and fresh strict catalog verification. The
implementation and synchronized authority prose are locally checkpointed at
`4ed74b0`.

This result establishes that the provisional componentwise glue interface is
constructively meaningful and sufficient for the intended Cartier
computation on a non-endpoint affine open. It does not yet prove equality of
the whole restriction/glue composites. The bounded PSSS-08c0J audit derives a
whole internal left cancellation *transformation*: ordinary `PiFunext`,
`PathLift`, and the existing core-inclusion comparison carry the pointwise
left law without external naturality. It also establishes the exact remaining
boundary. `OmegaEquivAlong Cat_cat` asks for identity-type equality of whole
functor objects, so reflecting that transformation to equality is a functor-
extensionality/univalence principle. On the right, coherent matching sections
are objects of an internal `Pi_cat`, not decoded functions accepted by the
existing `PiFunext`; a Path-valued section-extensionality/initial-centre owner
is absent. No broad equality rule or univalence axiom is added, and this
optional strengthening is no longer a prerequisite for the computational
scheme MVP.

PSSS-10a therefore returns directly to that MVP in
`emdash3_2_commutative_algebra_affine_spec.lp`. For every ring `R`,
`AffineSpecBigSlice_cat(R)` is the conventional geometric opposite of the
existing restriction-oriented total of maps `R -> S`. Its coordinate
presheaf is the first Sigma projection, so values and restriction maps remain
whole structured CommRing data with generic object/arrow action. A structured
triangle produces an internal slice arrow. In particular, the canonical maps
between `R[1/(f*g)]` and `R[1/f][1/g]` lift to chart arrows in both directions,
and coordinate restriction computes to those same maps. Their existing
`OmegaEquiv CommRing_cat` is re-exposed without functor equality or
univalence. The closed split-idempotent localization supplies a non-endpoint
basic-open chart. This is deliberately a big-affine computational precursor,
not yet the small Zariski site or the claimed scheme object; the next MVP gate
is a minimal supplied-cover/atlas package and a concrete chart-gluing
consumer.

The PSSS-10a source has 242 lines and eleven symbols with no rewrite or
unification rules; its 154-line reviewer has ten assertions and the central
suite adds six diagnostics. The strict catalog contains 1,981 checks across
88 areas with no legacy or unclassified entries. Synchronized health passes
all 90 registered targets in 712.925 summed check-seconds; the source,
reviewer, and central checks take 8.438, 24.270, and 28.157 seconds. Both
warning-enabled changed targets inherit exactly `1179 = 1020 + 159` warnings
with zero changed-file locations. The strict audit and the nonduplicative
integration remainder are green, and the implementation plus authority prose
are locally checkpointed at `837cfeb`.

PSSS-10b adds the concrete complementary-idempotent atlas in
`emdash3_2_commutative_algebra_affine_atlas.lp`. For every `R x S`, the
existing algebraic binary-cover constructor records `(1,0)` and `(0,1)` with
unit coefficients, while the existing dependent localization family records
their two fixed-image localization packages. No second chart-family record or
global localization choice is introduced. Orthogonality proves that the
chart intersection is `D(0)`; the existing zero localization makes its
coordinate ring compute to `zero_comm_ring`. Two structured triangles lift
to actual arrows of `AffineSpecBigSlice_cat(R x S)`, and restriction of the
coordinate presheaf along them computes to the whole structured maps from
each chart ring to the zero ring. Generic functor and Sigma owners carry
arrow action and naturality internally.

The closed `F2 x F2` specialization makes the product of the two generators
reduce literally to zero, supplying the first finite non-endpoint affine
atlas/glue presentation. This phrase is intentionally narrower than a
universal gluing theorem: the tranche does not construct a colimit, sheaf,
locally ringed space, or general scheme record. A generic finite-family
tabulation probe is viable, but specializing a recursive chart-family facade
to the full dependent affine chart data exceeded the 60-second target budget
in both producer and split-consumer probes. That convenience facade is not
promoted; `CommRingZariskiCoverFamily` remains the presentation authority and
concrete chart/overlap observations are exposed only where consumed. The
whole-functor equality/univalence boundary from PSSS-08c0J remains optional
and does not enter this construction.

The PSSS-10b source has 402 lines and 20 symbols with no rewrite or
unification rules; its 135-line reviewer has 13 assertions and the central
suite adds six diagnostics. Both warning-enabled changed targets inherit
exactly `1179 = 1020 + 159` warnings with zero changed-file locations. The
strict audit remains at zero unreviewed clauses, and the strict catalog has
1,987 checks across 89 areas with no legacy or unclassified entries.
Synchronized health passes all 92 registered targets in 663.006 summed
check-seconds at source snapshot
`sha256:6ff71dd1ca9dae89e444926ebaab28710a89fddbe8d24484d1a245ec114eb152`;
the new source and reviewer take 9.006 and 9.287 seconds there. The fresh
health traversal is followed by the nonduplicative CI remainder rather than
another long traversal; snapshot/tooling/test/document/book/audit/catalog
gates are green. The implementation and synchronized authority prose are
locally checkpointed at `db91ddf`.

PSSS-10c adds the direct affine functor-of-points/basic-open bridge in
`emdash3_2_commutative_algebra_affine_points.lp`. For each ring `R`,
`affine_spec_functor_of_points(R)` is transparently the existing Yoneda
presheaf on `Op_cat CommRing_cat`; its value at `S` is the whole structured-map
classifier `CommRingHom(R,S)`. The basic open `D(f)` is not a new predicate or
rigid facade: it is the existing ordinary invertibility sieve of the shared
identity CommRing-valued presheaf. Its point classifier computes to the Sigma
of `h:R->S` with actual proposition-valued unit evidence for `h(f)`.

For a selected universal-property localization `i:R->R[1/f]`, precomposition
constructs a `D(f)`-point from every map `R[1/f]->S`. Conversely,
factorization contractibility selects the inverse map. CommRing extensionality
turns its pointwise agreement into equality of whole structured maps;
proposition-valued unit evidence supplies the dependent path required for the
Sigma point; and contractible-factor uniqueness proves the other inverse law.
The two laws assemble directly into

```text
TypeEquiv(CommRingHom(R[1/f],S), AffineSpecBasicOpenPoint(R,f,S)).
```

This construction does not invoke univalence: it produces explicit
equivalence data rather than reflecting equivalence into equality. It is
componentwise in the test ring `S`, while the Yoneda presheaf and semantic
sieve already retain their full object/arrow actions internally. A whole
natural equivalence of presheaves remains a possible downstream theorem, not
an external naturality field or an MVP prerequisite. Generated topology,
sheafhood, subcanonicity, locally ringed structure, and a general scheme remain
separate gates.

The shared transparent identity-presheaf definition moves from the affine
glue consumer to the earlier CommRing-presheaf owner, so both glue and
functor-of-points use one semantic definition. The new 558-line source has 17
symbols and no rewrite or unification rules. Its 209-line reviewer has 15
assertions, including a closed split-idempotent `F2 x F2` instance. Focused
checks of the owner relocation, the existing affine-glue consumer, the new
source, and the reviewer pass within the 60-second target bound. The source
imports only the CommRing-presheaf and ordinary-site vocabulary it actually
uses; removing an unnecessary affine-slice/Zariski/overlap dependency reduced
its focused time from 25.67 to 4.45 seconds and its reviewer to 6.33 seconds
without changing any public declaration. A trial
extension of the already-large central monolith by this import and six
diagnostics reached the 60-second bound without a semantic error; the central
delta was therefore removed rather than increasing the timeout or adding a
rigid shortcut. The dedicated reviewer is the executable diagnostic owner for
this tranche.

Warning-enabled owner and reviewer checks inherit exactly
`1179 = 1020 + 159`, with no warning located in a changed file. The strict
rule audit remains at zero unreviewed clauses, and the unchanged strict
catalog has 1,987 checks across 89 areas with no legacy or unclassified
entries. Synchronized health passes all 94 registered source/example targets
in 793.592 summed check-seconds at source snapshot
`sha256:8d3a5bf7c64f453b11276bbef473c0f88ae7a32faea271d153e8a83ba4171530`.
There the new source takes 4.599 seconds, its reviewer takes 17.733 seconds,
and the unchanged central diagnostics take 31.689 seconds. The fresh health
traversal is followed only by the nonduplicative CI remainder: snapshot,
tooling, 39 Python tests, five document-registry tests, shell/source/report/
reference checks, book evidence/typography/KaTeX/assembly checks, the strict
rule audit, and the strict catalog are green. The authorized local
implementation checkpoint is `154069d`.

PSSS-10c1 adds the rule-free represented-basic-open-intersection bridge in
`emdash3_2_commutative_algebra_affine_intersections.lp`.  At a test ring `S`,
its explicit intersection point is a whole structured map `h:R->S` together
with the transparent Sigma pair of unit evidence for `h(f)` and `h(g)`.
Transport along the CommRing homomorphism multiplication law and the existing
product-unit maps gives functions in both directions between unit evidence
for `h(f*g)` and that pair.  Since both classifiers are propositions, the
map is proved equivalent directly by contractibility of its homotopy fibres;
the same-base Sigma equivalence then yields the pointwise

```text
D(f*g)(S) ~= D(f)(S) intersect D(g)(S).
```

For a selected localization at `f*g`, the public PSSS-10c representation and
the explicit intersection equivalence are retained as a transparent
two-`TypeEquiv` capability.  Their forward and inverse maps compose on the
decoded point carriers, and both composite laws are derived from the two
component equivalence laws.  This is the selected executable representation
normal form: coercing the whole public `TypeEquiv` package through the
sieve-membership alias, or eagerly constructing its generic composite,
exceeds the 60-second elaboration boundary without a semantic error.  No
timeout increase, rigid facade, rewrite, unifier, or duplicate predicate is
introduced.

The 521-line source has 15 symbols and zero rewrite or unification rules.  Its
195-line reviewer has 12 assertions, including the closed `F2 x F2`
complementary-idempotent atlas: the generators multiply definitionally to
zero, so the selected zero localization represents their computationally
empty intersection.  Focused quiet source and reviewer checks pass, and
warning-enabled checks inherit exactly `1179 = 1020 + 159` warnings with no
changed-file location.  The strict LHS audit remains at zero unreviewed
clauses and 52 annotated slots across 32 intentional clauses. The strict
catalog remains at 1,987 checks across 89 areas. Synchronized health passes
all 96 registered targets in 788.439 summed check-seconds at source snapshot
`sha256:8491ed696767a463bb3f3aebe6ea0adfab402432bd04aae0c0efc23d00e1974e`;
the new source/reviewer take 4.595/28.261 seconds and central diagnostics pass
at 57.730 seconds. The nonduplicative integration remainder—snapshot,
tooling/tests, document registry, source/report/reference lints, book checks,
strict audit, and strict catalog—is green. Two earlier traversals under
concurrent elaborator `check:ts` load timed out on different unchanged large
targets; the uncontended traversal passes without raising the 60-second bound
or changing unrelated source. The tranche is included in local checkpoint
`4436a23`.

PSSS-09a now adds the separate rule-free
`emdash3_2_commutative_algebra_zariski.lp` layer.  A presented affine cover
retains its finite unimodular generators together with a dependent finite
family of explicitly selected universal-property localization packages; no
global localization choice is postulated.  Every selected localization is an
actual arrow in the affine restriction total.  Given `h : R -> S` and chosen
localizations at `f` and `h(f)`, the source universal property constructs the
base-change factor, its pointwise triangle, the corresponding Sigma arrow,
and ultimately a returned membership term in the pulled-back ordinary sieve.
The carrier application of the pointwise composite computes to the target
localization map applied to `h(x)`.  Its intentional runtime distinction from
the canonical slice-postcomposition object is crossed by named theorem paths
and Catd transport rather than a new rewrite or unification rule.

The promoted source has 892 lines and 27 symbols, with zero rules and zero
unification rules.  The 246-line reviewer has 15 assertions and includes a
closed zero-ring localization witness for the final pullback-membership term;
12 central diagnostics occupy a dedicated catalog area.  Focused source,
reviewer, central, maintained `make check`, and complete example-suite gates
pass.  Warning-enabled owner and reviewer probes inherit exactly
`1179 = 1020 + 159`, with no changed-module warning location; the strict LHS
audit has zero unreviewed clauses and the unchanged 52 annotated slots across
32 intentional clauses.  The fresh strict catalog has 1,905 checks across 76
areas and zero unclassified entries.  Health passes all 65 source/example
targets in 555.881 summed check-seconds at source snapshot
`sha256:a2b313bcfec0123f399364fd395b5e533917767ef14d16b12da768da81a3a6a8`.
Full integration CI passes all 65 Lambdapi targets in 597.453 summed
check-seconds, followed by 39 Python tests, five document-registry tests,
shell/source/header/reference checks, book evidence/typography/KaTeX/assembly
checks, the strict kernel audit, and fresh strict catalog verification.  The
tranche is ready for its authorized local checkpoint.  Finite family-wide
containment/base-change assembly is PSSS-09b.  Proposition-valued coverage,
generated topology, subcanonicity, `Spec`, and schemes remain honest later
gates; chosen coefficient/localization data is not treated as a proposition.

PSSS-09b1 extends the same rule-free module with selected finite containment
and bounded family base change. The reusable finite-family owner now has
`FiniteFamilyAllOver`: a Nat-recursive family of `Q(x,p)` evidence over an
already-selected `FiniteFamilyAll(P)` witness, plus a generic pointwise map
that accepts source and target evidence families independently. The Zariski
specialization retains one literal `SieveMembership` term per chosen
generator/localization, maps the algebraic cover presentation while accepting
all target localization packages explicitly, and provides a closed zero-ring
singleton whose returned pullback membership is computational data.

The active delta adds no rewrite or unification rule. Direct specialization
of the full generic recursion and a specialized head projection to the
expanded ordinary-sieve membership family exceed the 60-second elaboration
budget. A diagnostic injective membership facade with a beta rule also timed
out and is rejected under the stable-head SOP. Arbitrary-length recursion
stays with `finite_family_all_over_map`; the promoted bounded consumer uses
its ordinary nil/cons observations and the existing elementwise pullback
theorem. The expanded convenience wrapper remains a performance/usability
gate rather than a semantic blocker or justification for rigidity.

The fresh strict catalog has 1,911 checks across 77 mapped areas and zero
unclassified entries. Health passes all 66 source/example targets in 638.261
summed check-seconds at source snapshot
`sha256:271c634e06aaa3ab038b1733f053b4647464e4b5ad623b751c3839e6ca157154`.
Full integration CI independently passes all 66 Lambdapi targets in 627.693
summed check-seconds, followed by 39 Python tests, five document-registry
tests, shell/source/header/reference checks, book
evidence/typography/KaTeX/assembly checks, the strict kernel audit, and fresh
strict catalog verification. PSSS-09b1 is included in local commit
`c8a81b9`.

PSSS-09cZ1 is the bounded supplied-topology boundary. The rule-free
`emdash3_2_commutative_algebra_zariski_topology.lp` candidate defines the
property that every sieve containing all basic-open arrows of a selected
finite Zariski family covers in an already lawful topology on
`Op_cat CommRing_cat`. Both presentation coverhood and whole-topology
compatibility have explicit `IsPropGrpd` witnesses, while generators,
coefficients, localizations, and membership evidence remain untruncated. Its
consumer maps family containment to `groth_topology_covers`; the chaotic
instance is a checked nonempty feasibility model, not an exact or least
Zariski topology. The 144-line owner has 11 symbols and no rules; the 56-line
reviewer has eight assertions. Focused and maintained checks pass. Warning-
enabled owner and reviewer probes inherit exactly `1179 = 1020 + 159`, with
no changed-module warning; the strict audit remains at zero unreviewed clauses
and 52 annotated slots across 32 intentional clauses. Six central diagnostics
raise the catalog to 1,917 checks across 78 mapped areas with zero unclassified
entries. Health passes all 68 source/example targets in 530.846 summed
check-seconds at source snapshot
`sha256:fabcd518cd2f529dbfd79485577412999aa477db290fe4af61465c97bfca242e`.
Full integration CI independently passes all 68 Lambdapi targets in 384.425
summed check-seconds, followed by 39 Python tests, five document-registry
tests, shell/source/header/reference checks, book
evidence/typography/KaTeX/assembly checks, the strict kernel audit, and fresh
strict catalog verification. PSSS-09cZ1 is included in local commit
`d808c29`.

PSSS-09cGI now supplies the generic generated-topology boundary internally.
`GeneratedSieveCover(G,U,R)` quantifies over every Grothendieck topology
accepting the witness-rich generator family `G`; dependent-Pi proposition
closure makes this intersection proposition-valued without truncating the
presentation witnesses. The three topology laws hold pointwise, while
generator inclusion and leastness compute by application. The rule-free
source and nine-assertion reviewer are synchronized through exact inherited
warnings, strict audit/catalog, and 100-target exact-content health in local
checkpoint `d826526`. A truncation/HIT remains conditional on a consumer
needing induction over cover derivations or executable cover normal forms.

PSSS-10dG is the direct affine consumer of that generic owner.
`emdash3_2_commutative_algebra_affine_zariski.lp` constructs a selected
localization chart as a whole arrow of
`AffineSpecBigSlice_cat(R)`. The target structure map is exactly the
existing opposite-precomposition composite `R -> S -> S[1/f]`, so its
triangle proof is reflexive and coordinate restriction computes to the
supplied whole localization map. One outer `sigma_ind` exposes an arbitrary
big-slice chart without adding package eta; selected finite-family containment
then supplies the witness-rich generators. The promoted 178-line source has
seven symbols and no rules or unifiers, and its 120-line reviewer has nine
assertions. Focused quiet checks and warning-enabled checks are green with the
exact inherited `1179 = 1020 + 159` inventory and no changed-file warning;
the strict audit/catalog and exact 102-target health are green. The latter
uses source-metrics snapshot
`sha256:8e19f00c96f37c16449d5f851107a9ca5b722f47657b2d01b224692504b1ab7e`
and check-content snapshot
`sha256:01c61b02268c84c0c334b3fa3f0012c26f68ce52def9959e44a940a1bc7b300c`.
The new source and reviewer passed from source in 24.042 and 23.915 seconds.
The unchanged central aggregate and affine-glue reviewer reached the cold
source limit once and then passed same-limit source retries in 54.587 and
44.889 seconds. No object priming was used. This is the intended big-affine
Zariski topology for the computational MVP, not the small site and not yet a
sheaf or scheme. The synchronized implementation is included in local
checkpoint `a30f6dc`.

PSSS-11a is the first structure-sheaf consumer of that topology. The promoted
`emdash3_2_commutative_algebra_affine_ringed_sites.lp` packages a supplied
`SheafificationCapability`, one object of the corresponding rigid
CommRing-valued sheaf category, and a whole `DefIso` from its included
presheaf to `affine_spec_coordinate_psh(R)`. The resulting
`ReflectiveCommRingedSite` therefore carries exactly
`affine_spec_big_zariski_topology(R)`, while the already-computing coordinate
restrictions remain available through the whole comparison. Its two readable
chart maps use `tapp0_fapp0` to observe the forward and inverse
transformations at a site object; they are not object-only substitute data.
The 230-line source has nine symbols and no rules or unifiers, and its
166-line reviewer has nine assertions. Focused quiet checks and
warning-enabled checks are green with the exact inherited
`1179 = 1020 + 159` inventory and no changed-file warning. Exact-content
health passes all 104 registered targets in 1187.079 summed check-seconds at
source-metrics snapshot
`sha256:c0ba7fc45f04780f9bb149d1a1dc6bf5dd50196c6f949423417ce0066e62d10b`
and check-content snapshot
`sha256:e9d102a79c9d824f40cb0bc6e9f829d3adeaf521becdde1fa3e830ea8b04f02d`.
The final inherited affine-glue reviewer passed in 39.504 seconds with the
ordinary 60-second limit, no object priming, and no special flags. The
synchronized implementation is included in local checkpoint `5ead41c`.
Localization locality, any stalk-local-ring interpretation, small-site
comparison, and the first scheme record remain PSSS-11 follow-ons rather than
claims of this layer.

PSSS-11b supplies the next whole computational boundary without converting
the earlier component observations into an axiom. The strengthened
`emdash3_2_commutative_algebra_glue.lp` defines
`CommRingPshLocalizationLocality` as `OmegaEquivAlong Cat_cat` for the exact
existing localization matching-restriction functor. Its selected left inverse
is one whole glue functor. The existing transparent half-adjoint proof at the
equality/hom-action owner now exposes the generic fact that this selected left
inverse also satisfies the right whole-functor law; the commutative-algebra
module therefore stores both whole paths without duplicating that proof.
Their object/support evaluations derive the earlier glue package. The new
rule-free `emdash3_2_commutative_algebra_affine_locality.lp` specializes this
supplied capability over every big-affine coordinate section and chosen
localization, with literal chart endpoints reducing to the retained ring and
localization. Focused quiet and warning-enabled checks are green with exactly
the inherited `1179 = 1020 + 159` warning inventory and no changed-file
warning; the strict rule audit and 1,992-check/90-area catalog are synchronized.
Exact-content health passes all 106 registered targets in 1059.644 summed
check-seconds at source-metrics snapshot
`sha256:5eed2e7250fc1b3aad8dcc4a66a150b7e69ef0ae069d06d000eab3309a23e8e3`
and check-content snapshot
`sha256:77f8c28fe6639ebb548093f63827f63afe64a1f982d2d10754b9f751ca5c20f2`.
The new source/reviewer pass in 7.831/31.558 seconds; the central checks and
final inherited affine-glue source/reviewer pass in 57.890/38.838/48.300
seconds under the ordinary 60-second limit, with no object priming or special
flags. The proportional nonduplicative integration remainder is green through
42 Python tests, five document-registry tests, health-snapshot verification,
source/report lints, strict audit/catalog, and book
evidence/typography/KaTeX/assembly checks. The synchronized implementation is
included in local checkpoint `8216f28`. This is localization locality over
`D(s)`, which need not cover, not ordinary sheaf descent, stalk-local-ring
structure, or the final scheme package.

`emdash3_2.lp` contains no executable `assert` commands. Diagnostics live in
`emdash3_2_checks.lp`; reviewer-facing milestones live in `examples/`.

## Current Architecture

### Sections 0–3: kernel foundations

The kernel begins with the groupoid/type universe, equality/path induction,
encoded Sigma/Pi/product object layers, and the core category interface.

Active equality/equivalence staging includes:

- decoded elementary H0 classifiers `Empty_grpd`, `Unit_grpd`, `Bool_grpd`,
  and `Nat_grpd`, with native Empty/Unit/Bool/Nat carriers, dependent
  eliminator facades, constructor beta, and a Bool conversion-level
  anti-collapse diagnostic; visible Unit, Boolean, and Nat constructor
  equality additionally compute to Unit, Empty, or predecessor equality while
  generic `eq_refl` retains runtime provenance and open endpoints retain
  primitive equality. Generic J repeats its category and endpoint as
  subject-reduction guards, so a foreign/component proof with the same reduced
  classifier cannot trigger reflexive computation. Remaining elementary
  observational identity, broader no-confusion, higher action for other
  formers, canonicity, and categorical universal properties remain separate.
  The transparent `nat_succ_ind_eqr` facade routes successor-indexed motives
  through predecessor J and computes only at component reflexivity; outer
  reflexivity and open predecessor paths keep their existing runtime
  boundaries. `NatSucc_func` is the ordinary canonical successor functor. The
  comparison-only selected-action basis and its two proof-time rules are
  retired. The isolated Sum former/action experiment is absent pending a
  future consumer-led redesign;
- `Path_cat_func`/`path_map_func` own the canonical iterable action of every
  raw groupoid function: the capped action computes to `eq_ap`, while the
  generic `fapp*` calculus retains every higher action. This is the sole
  nondependent action interface; there is no selected-action registry or
  parallel first-path channel. Canonical nested versus composite action
  remains related propositionally by `eq_ap_comp` where it is not
  judgmentally identical. `PathOut` is a distinct structured groupoidal-J
  owner consuming an already functorial `Catd` motive.
  `path_record_witness_action` uses direct `eq_apd`; any genuine iterable
  dependent replacement is a displayed-functor/section problem;
- the named dependent `PathRecord_grpd(A)` representative, implemented by a
  parametrized one-constructor native carrier with direct source, target, and
  dependent witness projections plus a generated-induction facade; its active
  observational path view, stable shaped reflexivity, projection betas, and
  reflexive specialized J are described below, while runtime record eta,
  arbitrary structural action, and additional arbitrary-constructor J remain
  deliberately absent;
- native `TruncLevel` codes beginning at -2, recursive
  `IsTruncGrpd(n,A)`, and transparent proposition/set/ordinary-groupoid views;
  the successor equation makes equality lowering computational, while the
  decoder-owned ordinary `TypeEquiv` invariance package transports truncation
  evidence in both directions and computes on reflexivity;
- the named one-constructor package `TruncGrpdU(n)`, with computing carrier
  and retained-evidence projections and the aliases `PropU_grpd`,
  `SetU_grpd`, and `GroupoidU_grpd`; carrier/evidence path views, carrier-path
  reconstruction, propositional inverse laws, and the resulting path
  `TypeEquiv` are active; composing with the canonical ambient decoder gives
  restricted equivalence between package equality and carrier `TypeEquiv`,
  while no package eta, proof erasure, or same-level universe theorem is
  selected; `is_trunc_type_equiv` and `is_trunc_grpd_universe` prove the
  expected successor universe level through this restricted equivalence;
- truncation monotonicity, evidence property-valuedness, arbitrary-level
  dependent-Pi closure, and same-level dependent-Sigma closure are active;
  restricted package univalence and the expected universe-level truncation
  theorem are active; truncation reflectors and the representation prerequisite
  for recursive omega-equivalence evidence remain separately statused;
  general `TypeEquiv` invariance and its fixed-map categorical object consumer
  are active;
- `TypeEquiv` with forward/inverse maps and inverse paths, plus identity,
  symmetry, and categorical-order composition with derived `IsEquivMap`
  closure evidence;
- the finite `GrpdPathView(A,B)` universe identity view, with canonical
  reflexivity, decoder-owned encode/decode, propositional inverse laws and
  transport agreement, Product/Pi/Sigma consumers, and no direct public
  universe-equality rule or duplicated univalence body;
- direct rigid Cat/Grpd universe identity to the native
  `OmegaEquiv` facade, with retained generic-reflexivity provenance and
  explicit packages for observer computation. The D0-backed `CatPathView`,
  decoder round trips, Product action, and D0b next-hom package are retired,
  not alternate library interfaces;
- path views for encoded Sigma and Pi types;
- arbitrary propositional Sigma path encode/decode round trips and transparent
  named PathRecord round trips, with constructor-reflexive computation and no
  open runtime eta;
- ordinary `PiHapply`/`PiFunext` over the related-input Pi view, with
  pointwise runtime beta, generic-J propositional eta, an explicitly
  classified proof-time reflexive basis, and contractible-fibre
  `pi_happly_type_equiv`; arbitrary structured-Pi J computation and
  computational fibrancy remain separate;
- the repaired path-category composition boundary: generic `comp_fapp0` owns
  runtime composition, two narrow `eq_refl` unit bridges join both projection
  orders, and `path_comp_eq_trans` proves J-derived propositional agreement;
  `Op_cat(Path_cat(A))` remains a genuine opposite head, while the oriented
  post/pre action heads retain distinct runtime forms and compare with shared
  composition only at proof time; `Path_sym_func(A)` owns path reversal from
  the genuine opposite, generic functoriality owns anti-composition, and
  `path_sym_agrees_eq_sym`, `path_sym_invol`, and
  `path_sym_core_incl_agreement` provide propositional coherence without open
  runtime folds;
- the first Path-realized pseudo-laxity consumer: the formal whole source and
  target remain the generic `functord_transport_*_func` owners,
  `path_map_compositor_path` is the existing `fapp1_compositor` decoded as an
  equality between paths, and `path_map_compositor_inverse` is its `eq_sym`.
  A named two-step propositional comparison—generic represented
  postcomposition to shared composition, then `path_comp_eq_trans`—gives the
  readable `eq_ap`/`eq_trans` endpoints without making them runtime-convertible.
  `path_map_compositor_higher_func` retains one off-diagonal next-hom action as
  a whole functor and therefore leaves generic higher iteration available;
- a computational strict-object/lax-arrow Gray profile and one right-closed
  consumer: `StrictFunctorData` and `strict_functor_carrier` select the strict
  object boundary without duplicating the ambient action hierarchy;
  `GrayHom_lax` reuses `Transf_cat` homs; `GrayTensor_R` has whole strict
  curry/uncurry maps and equality-valued beta/eta; `WalkingArrow_cat` is
  transparently `Join_cat(1,1)`; and the four-object walking square and its
  nonidentity directed interchanger derive from coevaluation and the existing
  whole post/left laxity owner. `gray_interchanger_next_func` retains one next
  action. The raw boundary composites are readable presentations, not a new
  endpoint normal form. Mirror closure, full monoidal coherence, and migration
  of the historical global strict cuts remain outside this tranche;
- `GrpdUnivalence` and decoder-based groupoid-univalence capabilities, with
  named decoder round trips, a canonical contractible-fibre capability
  selecting `grpd_equiv_path`, a propositional decoder transport square, and
  a Pi-universe action consumer; arbitrary legacy `ua_grpd` agreement and
  direct universe identity remain absent;
- `IsoEvidence` for ordinary categorical isomorphism data;
- the general `CatIsoUnivalence` capability type with no global kernel
  inhabitant, ordinary `idtoiso_cat`, and the direct native ordinary-iso lift
  `iso_evidence_omega_along`/`iso_evidence_omega_equiv`;
- native fixed-map categorical object-path/object-`TypeEquiv` construction and
  object-truncation invariance through
  `omega_equiv_along_obj_path` and
  `is_obj_trunc_cat_equiv_type_equiv`. Explicit native reflexivity retains
  its stable facade/package provenance rather than collapsing to a raw path;
- no D0/D0b/D1 compatibility module, decoder facade, reverse alias, or
  self-only compatibility example. Unsuffixed omega-equivalence names denote
  the native equality-valued representation exclusively;
- exact `IsDiscreteCat` Product data with native groupoidality, plus native-
  extension-owned core homwise evidence, `hom_to_path`, both coherent round
  trips, and a recursive cell consumer.
- independent object truncation, native directed-dimension codes, recursive
  `IsNCat`, evidence-retaining `NCat`/`ZeroCat`/`OneCat` packages, and a
  `OneCat` next-hom core-adequacy consumer. The obsolete conditional D0
  evidence-property/object-truncation experiment is retired. The downstream
  native equality-valued module proves unrestricted fixed-arrow
  evidence property, arbitrary truncation under retractions, and unconditional
  finite-`NCat` object truncation with computing base/successor equations. The
  one-way native ordinary-iso lift is active. The compatibility-scoped decoder
  round trips, selected-inverse comparison, reconstruction, and named OneCat
  `TypeEquiv` are retired; a fully native two-sided analogue is optional future
  work rather than a formation or cleanup dependency.
- direct canonical nondependent action through `path_map_func`, with dependent
  witness-field transport through `eq_apd` and no additional
  arbitrary-constructor J.

These are explicit kernel interfaces and checked computation skeletons. They
do not claim that every future univalence/coherence theorem is already
internalized.

### Finite dependent-record convention

Ordinary finite named structures use a parametrized one-constructor native
inductive carrier when later fields depend on earlier ones. A decoded
`*_grpd` classifier owns the public type; named projections are manual semantic
symbols with constructor beta rules, and public projection/eliminator
signatures retain the decoded classifier rather than exposing only the raw
carrier. Use the generated dependent induction principle directly or through
a thin reviewed facade when its raw parameter/motive surface is inconvenient.

Projection rules infer non-discriminating inductive parameters as `_` when
subject reduction and the strict LHS audit permit. Do not add runtime record
eta by default. A small map-plus-property existential may remain an encoded
Sigma; a structure with several stable field names or downstream structural
equality uses the record convention. The active `PathRecord_grpd` is the
executable representative: its original formation/elimination owner-position
and nested-Sigma comparison are warning-neutral, while the record supplies
direct named access and a direct three-field eliminator instead of nested
`sigma_Fst`/`sigma_Snd` chains. This decision is about the public API and
equality telescope, not a claim that nested Sigma is computationally invalid.

### Shaped PathRecord equality

`PathRecordPathView(A,r,s)` reads the named record structurally as
`Σ src : A, Σ dst : A, src = dst` and reuses the existing dependent Sigma
path view. The public equality rule for `PathRecord_grpd(A)` exposes that view
directly. `PathRecordPathRefl(A,r)` is the stable runtime reflexivity head;
`path_record_path_src` and `path_record_path_tail` expose its source and
dependent-tail components. Their beta clauses are ordered separately because
the tail result is indexed by the already-reduced source component.

The generic `ind_eqr` owner remains available for every equality. One narrow
former-specific clause restores its literal-reflexivity beta after record
reflexivity has reduced to the stable head. The same closed-registry policy is
used for generic consumers whose literal `eq_refl` pattern would otherwise be
erased: shared path units, `Path_sym_func`, `Core_incl_func`, `idtoiso_cat`,
and `idtoequiv_cat`. Do not extend this registry mechanically. Inventory a
real literal-reflexivity consumer, place the candidate at its owner, and test
both reduction orders and warning families. In particular, the active slice
does not make raw `sigma_path_refl` compute through J or PathSym; those steps
still depend on structural action and the separate fibrancy/dependent-J
architecture.

### Structural Sigma and PathRecord round trips

`sigma_path_decode_encode(p)` and `sigma_path_encode_decode(w)` prove the two
arbitrary path-characterization composites propositionally through generic J.
They are not open runtime eta rules. Constructor-exposed reflexivity computes
through the existing Sigma eliminator. Keep
`sigma_path_encode_decode_eq_refl` as the literal-reflexivity J base rather
than trying to reuse the stable `sigma_path_refl` theorem inside the nested
decode term: current proof-time unification does not propagate that comparison
transitively.

`PathRecord` needs no second Sigma normalization because its public equality
already reduces to `PathRecordPathView`. Its public encode/decode names are
transparent identity views, so both named round trips, shaped reflexivity, and
the dependent-tail observer compute directly and iterate through a nested
record. Preserve this distinction. Do not infer global eta, arbitrary
structural action, fibrancy, or additional structured-J computation from the
round-trip surface.

### Pi happly/funext equivalence

`PiPointwisePath(A,B,f,g)` is the diagonal family `Π x:A, f(x)=g(x)`.
`PiHapply(p)` observes a `PiPathView` path at `(x,x,refl_x)`, and
`PiFunext(h)` reconstructs its arbitrary related-input action by `ind_eqr` on
the base path. Point application of `PiHapply(PiFunext(h))` reduces to `h(x)`;
the whole functions do not receive a second eta-like runtime rule.

`pi_funext_eta(p)` derives `PiFunext(PiHapply(p))=p` with retained generic J.
Its reflexive base uses one two-rigid-head proof-time equation. Classify this
as a generic semantically justified structural law: the transparent lambda
presentation computes to the same reflexive term, whereas typed `eq_refl`
only confirms that the stable-head rule fires. Keep a conversion-negative
check and an arbitrary structured-Pi J negative check whenever this owner is
changed.

`pi_happly_by_inverse` supplies both propositional round trips explicitly.
The transparent theorem `is_equiv_map_by_inverse` converts such data into the
active contractible-fibre `IsEquivMap`. It constructs the contraction through
left-oriented J and half-adjoint coherence, then re-centres it at
`(g(b),right(b))`. This makes `type_equiv_from` and `type_equiv_right` compute
for `pi_happly_type_equiv`, while the contraction path remains propositional
and does not duplicate `pi_funext_eta`. Do not infer a generic runtime eta,
arbitrary structured J, or fibrancy from this package.

### Ordinary TypeEquiv algebra

`type_equiv_refl(A)`, `type_equiv_sym(e)`, and
`type_equiv_comp(eBC,eAB)` form the ordinary identity/inverse/composition
surface. Composition is in categorical order: its forward map is
`eBC.to(eAB.to(a))`. Symmetry and composition construct explicit
`EquivByInverse` values from `type_equiv_left`/`type_equiv_right` and route
their contractible-fibre evidence through `is_equiv_map_by_inverse`.

Keep these public packages transparent. Their forward maps and the generic
theorem's selected fibre centre make the inverse and right-path projections
compute without extra rules. The contraction proof is transparent but remains
propositional structure, so the derived left projection is only typed, not
identified by conversion with the separately constructed inverse law. Unit
and associativity compute on forward maps; do not promote package eta,
double-symmetry cancellation, or univalence-decoder coherence into this owner.

### Groupoid decoder coherence

`grpd_univalence_by_decoder(A,B)` is the proof authority for the two named
round trips `grpd_equiv_path_idtoequiv` and
`idtoequiv_grpd_equiv_path`. `grpd_univalence_from_decoder` converts that
specified-inverse package to the contractible-fibre `GrpdUnivalence` surface.
Its selected inverse, `grpd_univalence_selected_path`, computes to
`grpd_equiv_path`; this is the canonical capability agreement. Do not infer or
postulate the same agreement for an arbitrary legacy `ua_grpd(U,e)`.

`coe_grpd_idtoequiv` is generic-J transport coherence. Compose it with the
decoder right round trip to obtain the propositional
`grpd_equiv_path_coe(e,a)` square; `grpd_equiv_path_pi_action` is its first
pointwise Pi-universe consumer. Keep this square propositional until each
constructor path has a joining transport owner. The measured broad runtime
orientation competes with Product decoding: decoder-first produces
`coe(product_grpd_path(...))`, for which no component transport rule exists.
Do not promote that fold or disguise the missing Product branch with a
proof-time equation.

The category universe satisfies the directed-universe principle:

```text
Obj(Cat_cat) = Cat
Hom_cat Cat_cat A B = Functor_cat A B.
```

`Catd_cat K`, `Functord_cat`, and `Transfd_cat` are stable displayed facades
for the ordinary Cat-valued functor, transfor, and next-hom presentations.
Their category equalities are proof-time comparisons. Runtime computation
crosses the boundary through documented `Obj` and `Hom_cat` projections, so
neither ordinary nor displayed category heads are erased prematurely.

Generic identity, composition, functor action, and naturality are owned by the
global `id`, `comp_fapp0`, `fapp*`, and `tapp*` calculus. Specialized
`id_func`, `id_funcd`, `id_transfd`, `comp_cat_fapp0`, and
`comp_catd_fapp0` spellings are transparent public views or specialization
surfaces, not parallel owners. No separate ordinary `id_transf` constructor
exists.

### Section 4: ordinary internal hom and variance-separated actions

The represented covariant family is:

```text
hom_(F,W)[y] = Hom_A(W,F[y]).
```

Its postcomposition action is owned by the `hom_postcomp_*` hierarchy:

```text
(F[p])_*(g) = F[p] o g.
```

The represented contravariant family is primitive:

```text
hom_con(W,F)[y] = Hom_A(F[y],W).
```

Its precomposition action is owned by `hom_precomp_along_*`:

```text
(F[p])^*(h) = h o F[p].
```

`hom_int(F)` internalizes the represented source object; `hom_con_int(F)` is
the target-internalized mirror. Both expose their off-diagonal actions through
the rigid two-endpoint hom action:

```text
Hom_func(g,f)[h] = Hom_fapp0(g,f,h) = f o h o g.
```

Runtime normalization preserves the postcomposition, precomposition, and
rigid-`Hom` provenance. Opposite/identity presentations, independently
factored pre/post cuts, and one-inactive-endpoint degenerations are related by
narrow two-rigid-head `unif_rule`s. They are not global runtime folds.

Section 7f now uses that existing variance comparison to expose the ordinary
target-internalized action. `tapp1_con_int_fapp0_transf(epsilon)` is a
transparent application of `tapp1_int_fapp0_transf` to
`Op_transf(epsilon)` in the native opposite presentation. Its fixed-target
projection

```text
tapp1_con_at_transf(epsilon,Y)
  : Hom_A(-,Y) => Hom_B(F[-],G[Y])
```

computes at `X` to `tapp1_func(epsilon,X,Y)`. The identity-specialized owners
are `fapp1_con_int_transf(F)` and `fapp1_con_at_transf(F,Y)`. Applying the
active whole displayed laxity extractor to this fixed-target transfor yields
the pre/right witness through `fdapp1_int_cell`; no independent ordinary
naturality square or new runtime rule is installed. A functor varying higher
arrows between `epsilon`s remains consumer-gated.

Section 18zz now packages both ordinary variance directions without adding a
second coherence calculus:

```text
tapp1_post_laxity_transf(epsilon,X,g)
  : G[g] o epsilon[-] ==> epsilon[g o -]

tapp1_pre_laxity_transf(epsilon,Y,h)
  : epsilon[-] o F[h] ==> epsilon[- o h].
```

The capped `tapp1_post_laxity_cell` and `tapp1_pre_laxity_cell` unfold through
`tapp0_fapp0` to the corresponding `fdapp1_int_cell`. The transparent
`fapp1_compositor(F,g,f)` is the post/left component of the identity transfor,
so it reads `F[g] o F[f] ==> F[g o f]` while retaining the same internal-action
source. Their formal endpoint types stay at the two
`functord_transport_*_func` owners. Readable raw-composition endpoints are
already connected by the existing whole strict-naturality paths; do not add a
duplicate pointwise pre/post unification rule merely to restate them.

`Hom_tele_func`, `Hom_func`, and `Hom_fapp0` retain focused runtime identity
and composition joins because projection can hide the literal generic
functor-action pattern.

`DefIso(C,x,y)` is the computational isomorphism package whose inverse cuts
cancel under the stable hom-action owner. `IsoEvidence` is its ordinary
propositional view.

### Sections 5–7: products, transfors, curry, and adjunctions

The product architecture includes:

- `Product_cat`, componentwise homs, projections, pairing, and symmetry;
- product-valued functor/transfor projection ladders;
- `Product_cat_func` for internalized product formation;
- `Product_map_func` for componentwise endpoint maps;
- `Eval_func`, fixed-object evaluation, semantic curry, and semantic uncurry;
- ordinary weakening, exchange, and contraction packages;
- an indexed `Adjunction(F,G)` relation with transparent left/right
  compatibility views, stable unit/counit observations, both component-level
  triangle cut-elimination laws, opposite-index swapping, and mate consumers.

Cat-valued horizontal action is expressed through the generic
`comp_prod_fapp1_func` / `comp_prod_fapp1_fapp0` owner and its projection
ladder. Remaining `comp_cat_cov_*` / `comp_cat_con_*` names are transparent
readability or Cat-only projection surfaces where they expose transfor
structure; they do not own a duplicate functor law.

The same generic owner, specialized at `Catd_cat K`, also owns fixed-head
pre- and postwhiskering of displayed transformations. Given closed displayed
functors `L`, `F`, `G`, and `H`, and `eta : Transfd(F,G)`, the two inputs
`(eta,id_H)` and `(id_L,eta)` construct the whole transformations `H eta` and
`eta L`. Their fibre component is exposed by one evaluator beta at the
existing `tdapp0_fapp0` and `comp_prod_fapp1_fapp0` heads; it reduces to the
ordinary horizontal action in the fibre. This rule adds no symbol or second
action owner. `tdapp1_int_cell` continues to observe the whole result and
therefore retains its base-arrow and higher-cell action internally. The
identity-specialized full, capped, and base action clauses used by the
TypeScript runtime are pre-existing generic Lambdapi rules, not new
constructor-specific coherence.

This closure supports the bounded contextual surface bodies
`lambda^nd a. H(eta[a])` and `lambda^nd a. eta[L[a]]`. It does not construct a
classifier whose endpoints themselves vary over another context, and it does
not add the currently absent `Transf_catd_func`. Such a constructor remains a
consumer-led question rather than a prerequisite for fixed-head whiskering.

### Sections 8–10: directed Cat-valued families, Sigma/Pi, and mixed variance

Active family constructors include fibre notation, pullback/reindexing,
constant/terminal/opposite families, displayed composition, section
categories, and internalized Pi over varying bases.

```text
Pi_cat(E) =proof-time Functord_cat(Terminal_catd K,E)
Pi_cat(Const_catd K A) ≃ Functor_cat K A  (proof-time comparison).
```

`piapp0_func` and `piapp0` remain semantic definitions over terminal-source
component evaluation; they are not parallel primitive heads. Their full hom
action projects through the generic `tdapp0_func` owner and caps through
`tdapp0_fapp0`, so `pi_hom_fapp0` computes without a Pi-specific bridge.
When that capped component has already hidden a literal generic
`fapp1_fapp0`, four documented projection-order joins recover the two
ordinary naturality orientations and their `tapp1(epsilon,id) ->
tapp0(epsilon)` degenerations. They accumulate to the existing
`tapp1_fapp0` normal form; they do not add a second naturality calculus.
These joins can share the inferred outer category with their surviving
ordinary `tapp1`/`tapp0` operand. Vertical composition is handled separately
as evaluator projection beta: a composite displayed transfor under
`tdapp0_fapp0` expands to the pointwise composite of its displayed
components. This is the same orientation as ordinary `tapp0_fapp0`; it joins
the path where generic `fapp1_fapp0(tapp0_func)` strictness accumulates first
with the path where both operands project first. It does not introduce a
second functoriality calculus.
Likewise, `piapp1_func` remains the terminal-source specialization of
`fdapp1_int_presheaf_arrow`; its first next action reaches
`fdapp1_int_hom_fapp0`, preserving the iterated-hom tower. Runtime evaluation
of a constant-family section still computes through `piapp0` to ordinary
`fapp0`. The hom action of the constant-section constructor is owned by
`Const_transfd_func` / `Const_transfd`, rather than by an ordinary transfor
category fold.

Sigma total objects are dependent pairs. A total arrow consists of a base
arrow and a fibre arrow:

```text
(p,alpha) : (x,u) -> (y,v)
alpha : E[p](u) -> v.
```

`sigma_arrow` and `sigma_transport_arrow` are defined through this hom
characterization. `sigma_map_func` uses the displayed internal-hom projection
ladder for its fibre action; `sigma_map_transf` exposes the next generic hom
action as an ordinary transfor between total maps. Arbitrary displayed
functors are lax rather than silently strict/cartesian.

Asymmetric family reindexing now has its general total-category map. For
`F : A -> K` and `D : Catd K`,

```text
sigma_pullback_total_func(F,D)
  : Sigma_cat(Pullback_catd D F) -> Sigma_cat D
(a,u)       |-> (F[a],u)
(p,alpha)   |-> (F[p],alpha).
```

This owner was added only after auditing `Sigma_func`, `sigma_map_func`,
`Pullback_catd`, `Pullback_catd_func`, and the section/Sigma-introduction
surfaces and finding no existing owner of this base-changing map. It is the
Grothendieck totalization of the existing asymmetric family pullback, not a
generic pullback constructor for arbitrary total functors. Contextual pairing
therefore remains an explicit composite: terminal totalization,
`sigma_map_func` for a section of the pulled-back family, then
`sigma_pullback_total_func`. The direct arrow action of
`sigma_intro_tapp0_func`, a named `section_total` presentation facade, and a
whole-functor first-projection beta remain separate.

Independent Cat-valued displayed siblings reuse the ordinary product
semantics rather than a new `Product_catd` head. For `B,C : Catd K`, the
transparent family

```text
uncurry(Product_cat_func) o Product_pair(B,C)
```

computes its fibre at `k` to `Product_cat(B[k],C[k])` and its transport over
one shared base arrow `p` to `Product_map_func(B[p],C[p])`. The active closure
adds only the missing Cat-valued postcomposition capped-arrow projection and
the narrow same-literal-base product fold. Two unrelated parallel arrows do
not trigger the fold.

The fixed-base universal property is also active without introducing a
product-family head. The three injective owners

```text
Product_projL_funcd(B,C) : Functord(P(B,C),B)
Product_projR_funcd(B,C) : Functord(P(B,C),C)
Product_pair_funcd(FF,GG) : Functord(E,P(B,C))
```

have point, full-action, and capped-action projections, and pairing satisfies
both whole displayed-composition betas. The full and capped results remain
first-class functors, so a next-cell consumer can project them again. The two
beta rules deliberately retain `Catd_cat K` as a subject-reduction guard;
replacing that source classifier by `_` is ill typed. Displayed swap and
diagonal are transparent pairing composites with the displayed projections
and `id_funcd`, not additional primitive owners.

The internalized capped cell of displayed pairing is now componentwise at the
existing generic owner:

```text
fdapp1_int_cell(Product_pair_funcd(FF,GG),p,u)
  -> Product_pair(
       fdapp1_int_cell(FF,p,u),
       fdapp1_int_cell(GG,p,u)).
```

This is one runtime rule and zero new symbols. It closes the next-cell
observation of the already-existing pairing owner; it is not a new product
family, binder, laxity connective, or second functoriality calculus. A
positive conversion and opaque-cell noncollapse assertion live in
`emdash3_2_checks.lp`. Warning-enabled validation retains exactly 1179
warnings—1020 critical pairs and 159 replaceable pattern variables—and strict
LHS audit finds zero unreviewed candidates.

The root-only TypeScript `fibred-displayed-chain-2a` consumer uses this rule
for the exact mixed telescope

```text
k : K; a : A[k]; b : B[(k,a)], c : C[(k,a)];
d : D[((k,a),(b,c))].
```

It keeps the existing recursive `displayedDependentContextLambda` frontend,
derives the independent middle siblings, and transfers three existing
signatures plus nine checked runtime entries through the generic LF engines.
This is bounded elaborator evidence; it does not make arbitrary telescope
depth, general `:^nd`, or parsed surface syntax part of the active kernel.

For frontend reindexing, grouped siblings are canonicalized before Core
emission:

```text
P(B,C)[F]  elaborates as  P(Pullback_catd(B,F),Pullback_catd(C,F)).
```

The raw kernel term `Pullback_catd(P(B,C),F)` still does not convert to that
canonical presentation. No kernel reindexing rule, `Product_catd` head,
global displayed-functor/product conversion, universe-level product
projection, generic total pullback, or full family base-two-cell action is
implied.

`Functor_catd`, `Hom_catd`, and `Transf_catd` are mixed-variance family
constructors. Pointwise formulas do not replace their required base-arrow
actions.

The active constant-middle composition owner is the variance-qualified
displayed lift of ordinary functor composition. For `A : Catd(Op K)`,
`B : Catd K`, and an ordinary category `X`, it has the form

```text
Functor_comp_pair_funcd(A;X;B)
  : Functord(
      P(Functor_catd(A,Const_catd(K,X)),
        Functor_catd(Const_catd(Op K,X),B)),
      Functor_catd(A,B)).
```

At `k`, it maps a pair `(F,G)` to the existing ordinary composite
`Functor_comp_pair_func(F,G)`. Its full and capped base actions reuse the
target `Functor_catd(A,B)` action and remain whole functors, so the generic
`fdapp1_int_cell` and next-hom action can observe them. The rigid mixed
endpoint action remains owned by `Functor_catd` and ultimately by
`Unit_prof`; this package adds no duplicate identity, composition,
naturality, or `Unit_prof` rule.

The ordinary middle `X` is essential. The positive family
`Const_catd(K,X)` and negative family `Const_catd(Op K,X)` have the same
fibre `X`, but a general family over `K` cannot also be used as a family over
`Op K`. Accordingly this owner is a direct application/composition
combinator for bodies such as `G[k](c)(F[k](c)(a))`, not a mixed-curry
principle or a collapse of positive and negative classifiers. Nested binder
introduction remains the direct construction
`lambda^n k. lambda^f c. lambda^f a. t`; neither a total-context section nor
the auxiliary curry packages are prerequisites.

The durable diagnostic area contains seven checks covering the owner point,
constant-family fibre conversion, direct paired object and inner-arrow
computation, capped base action, generic internal cell/next-cell iteration,
and source/target non-collapse. At that owner's recorded checkpoint, warning
comparison was exactly 1,079 critical pairs and 159 replaceable pattern
variables, strict LHS audit was zero/53/33, the catalog contained 1,801
classified checks across 69 areas with zero unclassified checks, and the one
semantic-promotion CI passed all 41 kernel/example targets and
repository-integrity gates. The current combined boundary is recorded below.

The constant-domain displayed-evaluation closure is now active. For
`A : Cat`, `B : Catd K`, and
`S(A,B) = Functor_catd(Const_catd(Op_cat K,A),B)`, the two new reusable
owners are:

```text
Eval_funcd(B)     : Functord(P(S(A,B),Const_catd(K,A)),B)
Terminal_funcd(E) : Functord(E,Const_catd(K,Terminal_cat)).
```

Each has exactly one `tapp0_fapp0` point-component rule:

```text
Eval_funcd(B)[k]     -> Eval_func(A,B[k])
Terminal_funcd(E)[k] -> Terminal_func(E[k]).
```

The second owner composes with `const_section_func` to derive a coherent
fixed argument, so there is no third fixed-argument evaluator. Varying
subject/varying argument and varying subject/fixed argument are both
recursive TypeScript contextual-compiler consumers. The nested consumer
`H[e](G[d])` confirms recursion through both subject and argument
subexpressions rather than a whole-body recognizer.

The global `fapp`/`tapp` calculus remains the sole generic owner of
identity, composition, base-arrow action, and higher naturality. The two
component rules add two intentional critical-pair diagnostics but do not add
constructor-specific coherence rules. The specialization is deliberately
constant-domain: arbitrary mixed-domain evaluation, polarity-directed
contravariant lowering, arbitrary dependent-chain abstraction, and general
displayed-transfor coherence remain separate. The TypeScript frontend now has
bounded one-edge and exact `a; b,c; d` dependent-chain consumers; those
consumer profiles do not imply a general kernel binder.

### Sections 11–17: representables, dependent hom, and displayed action

The dependent-hom architecture is shared by Sigma homs, fibre transport, and
section action. Important owners are:

```text
Rep_catd
Edge_catd_func / HomPresheaf_catd_func
homd_ / homd_int
homd_src_func / homd_src_sec / homd_tgt_func
fib_cov_int / fib_cov_transf
tdapp1_int_func_transfd / fdapp1_int_transfd
fdapp1_int_* / tdapp1_int_*
```

The Sigma-map fibre projection ladder ends at:

```text
fdapp1_int_hom_fapp0(FF,p,u,alpha)
```

with the transported-identity specialization:

```text
fdapp1_int_hom_fapp0(FF,p,u,id) -> fdapp1_int_cell(FF,p,u).
```

This is the component-level displayed laxity normal form. The late section
18zz now promotes it to the whole transformation

```text
functord_laxity_transf(FF,p)
  : D[p] o FF[x] => FF[y] o E[p].
```

The implementation projects the arbitrary whole internal action through the
existing `tdapp0_fapp0`, `tapp0_fapp0`, `pi_hom_fapp0`, dependent-hom, and
self-comma identity-section owners. Its component reduces back to
`fdapp1_int_cell`, and its retained source-fibre arrow action computes through
one `tapp1_func` owner and capped `tapp1_fapp0` projection. No independent
naturality square is postulated, and this concrete consumer did not require a
primitive redesign of the transparent `piapp*` aliases. The section is late
because its identity-section action needs the completed cross-section
normalization environment; an earlier owner-position probe fails before those
dependencies are available.

Section 17 contains generic Sigma/Pi introduction/evaluation, constant
sections, ordinary structural logic, generic functor hom-action, section
pullback, and internal Pi action. Ordinary weakening `Const_func_func` is a
stable ordinary owner separate from the proof-time-only displayed
`const_section_func` facade.

On 2026-08-03 the unused contextual/mixed-curry experiment formerly in
sections 17f/17g was retired under D-DTTLF-USABILITY-083. No TypeScript,
book, or public-surface consumer selected those opaque packages after direct
nested `lambda^n`/`lambda^f`, compact `lambda^fd`, and compact/expanded
`lambda^nd` introduction graduated. Generic Sigma/Pi, pullback,
totalization, product/action, section-action, `Unit_prof`, `Hom_catd`,
`Functor_catd`, `Transf_catd`, and direct-binder owners remain active. The
retired code and checks remain recoverable at their recorded Git checkpoints;
retirement is a trusted-surface cleanup, not a mathematical impossibility
claim. At that retirement checkpoint, warning comparison decreased only
retired-rule interactions, from 1,097 to 1,086 unjoinable critical pairs,
while replaceable-pattern warnings remained 159 and the strict LHS audit
remained zero unreviewed clauses.

### Section 18: Cat-valued profunctors and computational comparison

`Prof_cat(A,B)` is the primitive fixed-endpoint category of Cat-valued
profunctors on `A^op × B`; `Prof(A,B)` is its object classifier and `ProfMap`
is its fixed-endpoint vertical hom.

Active infrastructure includes:

- primitive `Unit_prof(A)` with direct rigid `Hom_*` base action;
- `Prof_reindex` through `Product_map_func(Op_func(F),G)`;
- readable representables `Hom_prof_along`, `Hom_prof`, `Companion_prof`, and
  `Conjoint_prof`;
- shaped cells/elements and internalized reindexing;
- primitive profunctor tensor and fixed-endpoint co-Yoneda maps;
- covariant and contravariant profunctor implication;
- fixed-endpoint eval/lambda inverse pairs;
- weighted cone/limit comparison and the dual weighted-colimit presentation;
- adjunction mate comparison and preservation of weighted limits/colimits;
- primitive directed join and its internally natural cross cell.

`ProfComparison(P,Q)` is a transparent compatibility name for
`DefIso(Prof_cat(A,B),P,Q)`. Its push/pull and evidence APIs route through the
generic `DefIso` and hom-action owners; it is not an independent eliminator
theory.

`Prof_tensor` and implication objects are symbolic primitives where the
current kernel lacks a general coend/coinserter quotient. Their checked beta,
reindexing, and closed-core interfaces state the active computational scope.

### One-way presheaf, sieve, topology, and CommRing-presheaf libraries

The kernel's Catd machinery now has a one-way standard-library facade:

```text
Psh_cat(K) =proof-time Catd_cat(K^op)
Obj(Psh_cat(K)) -> Obj(Catd_cat(K^op))
Hom_Psh(K)(P,Q) -> Functord_cat(K^op,P,Q)
F^* = Psh_pullback_func(F)
    : Psh_cat(B) -> Psh_cat(A).
y_K = yoneda_psh_func(K) : K -> Psh_cat(K)
y_K(U)[V] -> Hom_K(V,U)
Into_restr_cat(U) -> Sigma_(V:K^op) Hom_K(V,U)
Slice_cat(U) -> Op_cat(Into_restr_cat(U))
HigherSieveClassifier(K)[U]
    -> Catd_cat(Into_restr_cat(U)).
IsSubterminalCat(C)
    = Sigma(IsPropGrpd(Obj(C)), IsGroupoidalCat(C)).
Sieve(U)
    = Sigma(S : HigherSieve(U), IsOrdinarySieve(S)).
sieve_pullback(p) : Sieve(U) -> Sieve(V).
SieveMembership(R,(V,f)) -> Obj(R(V,f)).
SieveCoverage(K) -> Pi U, Sieve(U) -> PropU.
GrothTopology(K)
    -> coverage plus maximality, pullback stability, and local character.
CommRingPsh_cat(K) -> Functor_cat(K^op,CommRing_cat).
comm_ring_psh_restrict(O,f,s) -> O[f](s).
CommRingPshInvertibleAlong(O,s,f)
    -> CommRingUnitEvidence(O(V),O[f](s)).
Matching_O(s)
    -> Pi_(V,f,m in D_O(s)) Path_cat(|O(V)|).
restrict_ell : Path_cat(|O(U)[1/s]_ell|) -> Matching_O(s).
restrict_ell(x)[V,f,m] -> factor(ell,f,m)(x).
glue_ell : Matching_O(s) -> Path_cat(|O(U)[1/s]_ell|).
glue_ell(restrict_ell(x)) = x.
factor(ell,f,m)(glue_ell(a)) = a[V,f,m].
```

The category heads do not runtime-collapse. Restriction's object action is
the existing `Pullback_catd(P,Op_func(F))`; ordinary map action and laws remain
generic. Yoneda action is existing represented-hom postcomposition, slice
construction is existing Sigma totalization plus opposite, and higher-sieve
restriction is existing Catd pullback. The higher name is literal. A separate
downstream module selects ordinary sieves by pointwise native subterminality
and preserves that evidence under the same pullback action. It does not prove
the ordinary-sieve carrier set-valued and does not declare `Omega`, descent,
or topology. A further rule-free module packages direct proposition-valued
sieve topologies and the chaotic model without binding `Omega` or itself
adding generated coverhood or sheafification. Downstream one-way modules now
construct the least topology accepting witness-rich generators and the
fixed-site Cat-valued direct-cover reflector described under “Constructed
Cat-Valued Sheafification Status” below. The later CommRing-valued affine and
scheme packages retain supplied structure-sheaf/locality capabilities; they
are not derived silently from that Cat-valued reflector.

The CommRing-valued classifier is transparent rather than a second rigid
presheaf facade. Explicit restriction applies the retained structured-map
function. Identity and composite restriction laws are theorem-level paths
through the selected pointwise ring-map comparisons; generic whole arrows
retain their negative carrier-computation boundaries. Arrowwise unit support
is a property and is closed under further restriction. The downstream carrier
and unit-evidence families assemble it as a whole ordinary sieve, the locality
module packages its selected localization factors as one internal cone, and
the matching module applies those factors to localization elements as
internally coherent Pi sections with equality-path action. The selected glue
module supplies the converse as a genuine functor plus both Path-valued
component observations. It is computational basic-open locality over `D(s)`,
not ordinary sheaf descent; no native whole equivalence is asserted.

### Section 19: PathOut, path induction, and Eckmann–Hilton

For fixed `x : Z`:

```text
PathOut_Z(x) = Sigma (y : Z), Hom_Z(x,y).
```

The canonical arrow from `(x,id_x)` to `(y,p)` is the generic Sigma transport
arrow for the representable family. The primary path-induction package is the
telescope theorem `PathInd_transfd(Z)`; `PathInd_funcd(Z)` is derived by
`Sigma_transfd_funcd`.

The transitivity benchmark computes to ordinary composition. Nested telescope
terms stress the mixed-variance surface.

The first Eckmann–Hilton slice defines 2-endomorphisms of an identity 1-cell,
vertical and represented horizontal composition, the common-middle
equalities, and commutativity `EH_comm`.

## Core Ownership Invariants

### Runtime computation versus proof-time comparison

A rewrite rule selects a runtime normal form and participates in critical
pairs. A `unif_rule` helps elaboration/proof construction when neither side is
chosen as the runtime normal form.

Use:

```text
assert t ≡ u
```

for runtime conversion, and a typed reflexive equality:

```text
eq_refl(t) : τ(t = u)
```

to exercise a proof-time unification comparison. Do not infer runtime
joinability from a successful typed `eq_refl` probe.

### Displayed facade tower

The first three displayed heads remain stable:

```text
Catd_cat K
Functord_cat K E D
Transfd_cat K E D FF GG.
```

They compare at proof time with `Functor_cat K Cat_cat`,
`Transf_cat K Cat_cat E D`, and the corresponding ordinary iterated hom.
Their `Obj` projections compute toward the ordinary presentations, while their
`Hom_cat` projections expose the next displayed rung. Add direct comparisons
at every represented rung; do not rely on unification-rule transitivity.

`Pi_cat K E` is the stable section-category facade over the terminal-source
displayed rung. It compares directly at proof time with both
`Functord_cat K (Terminal_catd K) E` and the corresponding ordinary
`Transf_cat`, while its `Obj` and `Hom_cat` projections expose section objects
and the `Transfd_cat` next hom. The constant-family comparison with
`Functor_cat K A` is also direct; do not rely on comparison transitivity.

For sections over `Sigma_proj1_pullback_catd`, the distinct `Pi_cat` and
`Functord_cat` heads now support a direct proof-time uncurrying comparison.
Runtime subject reduction for `path_ind_sec -> fib_cov_transf` crosses the
general Pi/displayed object ladder and one measured join between ordinary
`Obj(Transf_cat)` classifiers. A direct specialized displayed-`Obj` rule is
redundant. The next `Transfd_cat` projection is retained for iterability.

The stable projection-pullback family is now an explicit runtime selection,
not the automatic reduct of either
`comp_cat_fapp0(D,Sigma_proj1_func(R))` or
`Pullback_catd(D,Sigma_proj1_func(R))`.  Both generic presentations compare
with `Sigma_proj1_pullback_catd(R,D)` through narrowly typed `unif_rule`s.
This keeps generic represented-family reindex accumulation as the selected
runtime cut and removes the competing generic-versus-stable normal form.
Consumers requiring the projection ladder name the stable family directly.

Recursive dependent-variable weakening consequently uses the explicit whole
displayed functor

```text
section_weaken_funcd(R,E,s) : R ->_K E
section_weaken_funcd(R,E,s)[k] = const_{R[k]}(s[k]).
```

Its base-arrow action is the already-internal action of `s` and is independent
of the new source-fibre object.  `sigma_functord_sec` then uncurries this
displayed functor when a section over `Sigma(R)` is needed.  Generic
`section_pullback_sec(F,E,s)` remains available and computes at literal base
objects; it is no longer overloaded as the stable displayed weakening owner.

The uncurrying operation is functorial at one whole owner:

```text
sigma_functord_sec_func(R,D)
  : Functor(Functord_cat(R,D),Pi_cat(Sigma(R),pi1^*D)).
```

Its object action selects `sigma_functord_sec(FF)`.  Its generic arrow action
already carries displayed-transformation naturality internally, while one
narrow runtime projection restores the component beta hidden by the stable
section facade:

```text
sigma_functord_sec_func[eta][(k,r)]
  -> Const_transf(eta[k][r]).
```

Do not describe this projection beta as a theorem of naturality alone.  It is
the defining observation of the functorial uncurrying lift; generic naturality
states that these observations commute along arrows of `Sigma(R)`.  Do not add
a second named transformation head merely to restate the same intermediate
action unless an independent consumer needs that head and its warning/owner
audit justifies it.

### One generic owner for ordinary laws

The global `fapp*`/`tapp*` calculus is the sole owner of ordinary identity,
composition, functoriality, and naturality. A constructor-specific rule whose
only content is one of those laws indicates a missing internalized
functor/transfor owner or a detached projection.

Do distinguish a duplicate structural law from projection beta. Once a
stable evaluator head such as `tapp0_fapp0` or `tdapp0_fapp0` has erased the
literal generic evaluation-action pattern, a rule exposing the component of a
composite is the next rung of the evaluator ladder:

```text
tapp0(x,eta o epsilon)
  -> tapp0(x,eta) o tapp0(x,epsilon)
tdapp0(x,eta o epsilon)
  -> tdapp0(x,eta) o tdapp0(x,epsilon).
```

This pointwise expansion coexists with the generic strict-functor cut
`F[g] o F[f] -> F[g o f]` because the rules operate at different heads and
must be tested as a joining projection diamond.

The generic higher-component rung is now explicit:

```text
Theta : eta -> eta'
tapp0_hom_fapp0(Y,Theta) : eta[Y] -> eta'[Y].
```

It is the capped hom action of `tapp0_func(Y)`, with computational identity
and vertical-composition projections. Its `Cat_cat` specialization reduces to
the pre-existing `tdapp0_fapp0` stable head; the former direct Cat-only capped
rule is retired, while `fapp1_func(tapp0_func(Y))` still exposes the whole
`tdapp0_func(Y)` action. The owner-position diagnostic delta is exactly
`+30` critical pairs (`25` composition, `3` identity, and `2`
specialization/evaluator interactions), with no replaceable-LHS growth or
subject-reduction failure. Treat this classified delta as projection evidence,
not as permission to add reverse joins mechanically.

A specialized projection-order bridge is exceptional but legitimate when:

1. a stable projection erases the literal generic-owner pattern;
2. an outer generic cut competes with that projection;
3. the two paths do not already join;
4. a focused owner-position probe establishes one canonical orientation.

Never install both orientations or generate such bridges mechanically.

### Hom variance and Došen cuts

When a term is already expressed through a stable hom-action owner, fold
consecutive actions to the one action indexed by the composite arrow:

```text
(F q)_*((F p)_*(g)) -> (F(q o p))_*(g)
(F p)^*((F q)^*(g)) -> (F(q o p))^*(g).
```

The second formula reflects contravariance: `q o p` first traverses `p`, then
`q`, while the induced precomposition actions are encountered in the reverse
endpoint order. These are the current runtime accumulation orientations.

Raw expanded compositions should normally remain `comp_fapp0` terms. Use the
existing proof-time bridges when a theorem compares them with stable hom-action
syntax. Add a raw runtime bridge only for a concrete consumer after testing
owner-first and projection-first reductions.

### Omega-friendly structure

Prefer functor-level folds over capped object rules when later hom action is
needed. A RHS that computes one selected cell can lose the functor object
required for the next dimension.

A formula `E[x] = ...` is only the object part of a directed family. A formula
`eta[x] = ...` is only a transfor component. Identify the base-arrow action and
off-diagonal/naturality action or explicitly record them as deferred.

## Before Editing The Kernel

1. Identify the semantic owner and whether the desired result is runtime or
   proof-time.
2. Search current declarations, rules, checks, examples, and the relevant plan
   with `rg`.
3. Decide whether a missing projection, transparent alias, or canonical
   endpoint fixes the problem before introducing a stable head.
4. Write the mathematical formula and the intended normal form.
5. Probe the candidate in a temporary full-file copy at its owning position.
6. Add a focused conversion assertion or typed `eq_refl` consumer.
7. Run a bounded quiet check; enable warnings when interactions are unclear.
8. Promote the smallest working change and add a durable diagnostic/example.
9. Update the task report when the architecture or a rejected orientation
   matters beyond the local rule.

## Rewrite And LHS Hygiene

### Minimal inferred slots

Keep reconstructible source/target/category/family arguments as `_` on rule
LHSs unless they are:

- the actual constructor discriminator;
- a composition-interface guard;
- required for subject reduction;
- a measured decision-tree/performance guard.

Observational classifier equations can make identity types with distinct
categories or endpoints decode to the same classifier. Whenever such an
equation is added, re-audit every beta whose LHS matches a proof constructor
while leaving those indices inferred. A quiet full check is insufficient:
instantiate a proof-dependent injective motive, compute the candidate term,
and verify that its normal form still inhabits the declared result. The generic
`ind_eqr` beta therefore repeats both its category and reflexive endpoint; this
is a subject-reduction guard, not optional overspecification. A proof-time
`unif_rule` cannot repair an ill-typed runtime beta.

Compound reducible inferred terms such as `fapp0 F x`, `Functor_catd ...`,
`Op_cat(Hom_cat ...)`, or transparent readability aliases can cause brittle
matching and conversion explosions.

Audit candidates with:

```bash
python3 scripts/audit_rule_lhs.py --show-kept
make audit-rules
```

Do not apply the scanner mechanically. Probe each `_` replacement. Mark a
measured exception immediately above the rule:

```text
// lhs-audit: keep SLOT[,SLOT] -- reason
```

The rule applies at rewrite-family scale, not only one slot at a time. Match on
the true stable discriminee and do not copy surrounding presentation wrappers
across sibling rules. For example, when `Op_func(_,_,F)` selects the case,
extra `Op_cat A`, `Op_cat B`, product-functor, or transparent-alias endpoints
should remain inferred unless the theorem genuinely distinguishes those
wrappers. A surface pattern that works for a variable endpoint may otherwise
stop matching when that endpoint normalizes to a product or functor category.

### Explicitness depends on the surface

Do not apply LHS minimality as a blind whole-file formatting rule. The four
main surfaces have different needs:

1. **Rewrite and unification patterns:** keep the stable discriminator
   explicit and reconstructible endpoint/category/family slots implicit.
   Apply this discipline to both sides of a `unif_rule`.
2. **Rule RHSs and defined-symbol bodies:** omit only arguments that are
   syntactically recoverable from the visible data. A fixed parameter that is
   not determined by the remaining arguments must stay visible even if an
   expected type happens to recover it in one probe.
3. **Theorem-style examples:** prefer the compact mathematical formula;
   projectionwise product/Sigma statements are often clearer and more robust
   than raw dependent-constructor equality.
4. **Diagnostic assertions:** keep canonical source/target endpoints explicit
   when the purpose is to expose the full `fapp1_func`, `fapp1_fapp0`, product,
   or displayed-action shape. Compactness must not turn a regression into a
   test of accidental endpoint inference.

This distinction preserves readability without erasing the information needed
for matching, subject reduction, or a stable diagnostic.

### Outer eliminators over active cuts

Treat an LHS such as:

```text
sigma_Fst(comp_fapp0(...))
sigma_Snd(fapp0(specialized_func,...))
```

as a high-risk commuting conversion. The outer projection and inner cut can
reduce in competing orders. Prefer:

1. an existing generic projection ladder;
2. a constructor beta rule;
3. a stable intermediate component;
4. an equation at the functor/transfor owner;
5. propositional evidence when judgmental computation is unnecessary.

A new commuting conversion requires a concrete consumer, focused checks for
both paths, an owner-position full-file probe, and warning classification.

### Canonical types and expected-type probes

Prefer reduced declared types and canonical endpoints:

```text
τ(Functord E D)
Hom_cat Z x y
Functord_cat E D
```

Use unreduced types only when the exact projection route is intentional and
document why.

A bare `assert t ≡ u` lets Lambdapi infer both sides independently. When a real
consumer supplies an expected type, test that typed shape explicitly before
concluding that conversion fails: first check the raw term at the intended
type `T` (or bind it with a temporary helper returning `T`), then test
conversion or typed reflexivity using that term. Keep a bare conversion
assertion only when both sides are expected to elaborate without contextual
type information.

Do not introduce decoded `*_TYPE` or parallel classifier heads merely to make
binders shorter. Such a head needs to join the existing category/classifier
reductions and can create a second semantic layer. Keep ownership at canonical
heads such as `Transf_cat`, `Functord_cat`, and `Product_cat`; use narrow
`Obj(...)` elaboration aids only when a measured consumer requires them.

### Constants and unification limits

A `constant` cannot head a rewrite LHS. Changing it to `injective` is a global
normal-form migration requiring full downstream, subject-reduction, warning,
and decision-tree review.

Unification rules are experimental and not reliably transitive. Prefer two
rigid heads or a stable intermediary. Apply inferred-slot hygiene to both sides
of a `unif_rule`.

### Stable heads and semantic equivalences

Add a stable head only when later rules need a visible constructor or a focused
probe establishes a real discrimination/performance boundary that a smaller
projection or canonical endpoint cannot solve. A surface-readable name alone
is not enough; transparent aliases should normally remain definitions.

Notation-only heads such as `Fibre_cat(E,k) = fapp0(E,k)` should not receive
broad injectivity or inversion rules: equality of two fibres must not generally
recover the entire family and index.

Likewise, familiar equivalences for maps out of the terminal category are not
global runtime computation by default:

```text
Functor_cat(1,A) ≃ A
Transf_cat(const(u),const(v)) ≃ Hom_A(u,v).
```

Prefer a consumer-local projection/fold through the existing section and
component owners. Promote a global terminal-source rewrite only after a
concrete consumer, both reduction orders, and the warning/subject-reduction
effects have been measured.

## Identity Normal Forms

Identity may appear as `@id`, the transparent `id_func`, `id_funcd`, or
`id_transfd` views, or a specialized projected identity. There is no separate
ordinary `id_transf` constructor. A rule for the generic surface does not
automatically match every proof-time-comparable category presentation.

Prefer narrow typed consumer rules or a coherent small specialization package
over broad global identity rewrites. The current middle-constrained generic
composition identity rules keep the shared middle object as the true cut
interface while inferring outer endpoints. Competing runtime identity
spellings are joined through the typed pre/post proof-time bridge; that
proof-time joinability is the selected criterion for this measured overlap.
Across the ordinary/displayed first-hom facade, identity-specialized
`tdapp1_int_*` consumers explicitly accept generic `id` at both
`Functord_cat(E,D)` and `Transf_cat(K,Cat,E,D)`. This is a typed façade package,
not a global rewrite between the two identity terms.

## Comment And Layout SOP

Put a brief comment immediately above most semantic symbols and nontrivial
rule families:

- public constructor: mathematical name/formula and primitive/defined status;
- stable head: projection formula and generic owner;
- transparent alias: explicitly label it an alias/view;
- rewrite: label beta, projection, cut, accumulation, or confluence join;
- unification: state that it is proof-time only;
- evidence symbol: state the proposition witnessed.

One comment may cover a cohesive `rule ... with ...` command.

Use compact horizontal layout for simple stable-head rules. Keep vertical
layout for nested endpoint formulas, deliberate explicit guards, and
diagnostic assertions that expose canonical endpoints.

Do not duplicate a semantic body in a readability helper. Route aliases
through the named semantic constructor.

## Development And Validation Workflow

### Persistent goals and Git checkpoints

A long-running Codex `/goal` must recover the current authority, active plan,
owner positions, worktree list, staged and unstaged diffs, and bounded baseline
on every continuation. A baseline commit is comparison evidence; do not reset
a descendant implementation to it.

Persistence alone does not authorize Git mutations. When the user or the
task's launch prompt explicitly authorizes local checkpoint commits, use the
repository workflow in
`../../docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`. A kernel checkpoint is
eligible only after the smallest owner-position experiment has a typed
positive consumer and relevant negative/non-collapse evidence, proportional
warning and rule audits are complete, affected diagnostics/catalog/health and
plan ledgers are synchronized, and the staged diff contains no unrelated work.

Checkpoint authorization never weakens the semantic promotion procedure and,
unless separately requested, never includes push, merge, rebase, amend, reset,
publication, branch deletion, or worktree removal. Correct failed experiments
with new reviewable evidence/commits or compare explicit experiment branches;
do not erase the decision trail.

### Bounded checks

```bash
EMDASH_TYPECHECK_TIMEOUT=90s make check
timeout 90s lambdapi check emdash3_2.lp
make check-warnings
```

The 90-second value is a uniform per-file ceiling for focused probes, warning
checks, registered aggregates, and health traversals. The central diagnostics
and several focused consumers now have measured green runs near 60 seconds, so
the older split limits could classify the same valid import path differently.
This is a timeout ceiling, not permission to run broad aggregates for
reassurance. If a quiet check times out or hides the interaction, rerun the
smallest target with warnings enabled before changing the architecture.
Resumable health evidence continues to require exact checked-content and
environment identity, including the timeout.

### Focused probes

```bash
scripts/probe.sh tmp/probes/name.lp
scripts/explain_failure.py logs/probes/name.log
```

Ordinary experiments belong under ignored `tmp/probes/`. Move durable
reviewer-facing computations to `examples/`.

### Warning and decision-tree diagnosis

```bash
make warning-summary
scripts/explain_failure.py --warning logs/warnings/latest.log
scripts/decision_tree.sh SYMBOL
scripts/decision_tree.sh --png /tmp/tree.png SYMBOL
```

The compact warning summary reports both overlap-term heads and unordered
pairs of the two participating rewrite-rule heads. Its strict structural
parser rejects a critical-pair block that lacks one term head or exactly two
participants, preventing a changed Lambdapi warning format from silently
dropping families. This is a completeness check on the inventory, not a
semantic classification of joinability; the raw stream remains authoritative.

Use the smallest Lambdapi debug flag set: `u` unification, `c` conversion, `q`
rewriting, `w` weak-head normalization, `s` subject reduction, `k` local
confluence, `d` decision-tree compilation, and `i` typing. Never use
`--no-sr-check` for promoted code.

### Catalog, examples, CI, and health

```bash
make examples
make catalog
make toc
make ci
make health
```

`make catalog` can be non-strict during exploration; `make ci` requires a fresh
catalog and zero unclassified checks. `make toc` requires the header source map
to match every formal section/subsection heading exactly and is also part of
CI. Run `make health` after meaningful architecture/check changes.

### Type-aware search

Use `rg` for ordinary discovery and:

```bash
scripts/lambdapi_search.sh 'name = hom_int'
scripts/lambdapi_search.sh 'type >= Prof_imply_cov'
```

for normalization/type-aware search.

## Constructed Cat-Valued Sheafification Status

The direct cover-completion program now reaches the existing supplied
fixed-site capability. `emdash3_2_direct_cover_completion_universality.lp`
provides the whole seed-functorial recursor, higher unit beta, topology-local
eta/uniqueness, and the resulting Hom `OmegaEquivAlong`. The subsequent
`emdash3_2_direct_cover_sheafification.lp` realizes only
`Sheaf_cat(K,T,Cat_cat)` as pairs `(P,IsTopologyLocalPsh(P))`; arbitrary value
categories remain opaque.

One whole inclusion forgets locality, and one whole reflector maps `P` to its
local direct cover completion. The indexed adjunction is declared at the raw
`Functor_cat(Op_cat(K),Cat_cat)` boundary required by the generic package,
while a scoped proof-time comparison preserves rigid `Psh_cat(K)` as the
computational owner. Its unit and counit compute to the HIT unit and the
identity-seeded recursor. Recursor beta and topology-local eta derive both
cancellation laws, giving the exact fixed-counit `OmegaEquivAlong` and a term
of the existing `SheafificationCapability(K,T,Cat_cat)`.

The facade's runtime composition projection exposes twelve additional
`comp_fapp0`/generic-naturality warning blocks: the imported baseline is
1,017 critical pairs plus 159 replaceable-pattern advisories, and the
integrated module reports 1,029 plus 159. A proof-time-only stable-composition
alternative was rejected because dependent endpoints still required the same
category projection while adding indirection. The direct rule is retained as
the honest inherited category operation; strict LHS audit is clean. These
warnings remain measured diagnostic evidence, not a claim of global
confluence.

After integration of the completed TypeScript-elaborator, PSSS, internal-
laxity, profiled-Gray, WalkingEnd--Circle, dependent Circle-computation, and
bounded WalkingArrow--interval histories, the exact-current selected-source
warning boundary is 1,271
diagnostics: 1,112 unjoinable critical pairs and 159
replaceable-pattern advisories. The strict
LHS audit is zero unreviewed clauses, 58 annotated slots, and 34 intentional
clauses. The generated catalog contains 2,197 classified checks across 109
areas with zero legacy or unclassified entries.

The exact-current registered health boundary is green for all 208 maintained
targets—94 source/diagnostic files and 114 reviewer examples—under the uniform
90-second per-target ceiling. All 208 report exit 0, with 1,958.460 summed
check-seconds. Exact byte comparison verified the 201 unchanged predecessor
targets before reusing their successful evidence. The changed central
diagnostic and four new generic-groupoidification sources checked fresh in
26.978 and 2.425--2.648 seconds; the two new reviewers checked fresh in 2.415
and 2.697 seconds. The final report records exactly 201 resumed successes. The
source-metrics snapshot is
`sha256:1cd888aa1183aa4ed623e59ef3d49d1c94c007814c51fe18df5801669ff75038`
and the checked-content snapshot is
`sha256:a4688354d8a468615d2861efe23053ce8484c28bda9ca8a95aae3e6d97bda5b4`.
No separate `make check`, `make examples`, `make ci`, or repository-wide
aggregate was run. The required resumable health refresh was bounded to the
changed/new targets after byte-identical predecessor evidence was selected.

## Book And Renderer Workflow

The book is a first-class exposition artifact under `book/`. Its
chapter files are authoring sources; the ignored
`print/public/emdash-book.md` file is deterministic generated input for
the renderer. Book theorem-like claims use the four statuses defined in
`book/STYLE.md` and checked claims cite `book/evidence.json`.

The current locally promoted artifact is the draft expanded development
edition `0.5.0-dev`, dated 2026-08-18: 343 tagged US Letter pages, 16 embedded
fonts, and PDF SHA-256
`54a11407eb9ca1203979413f3231003ada85021ef2578e247ab922fccd918ad7`.
Its deterministic owner and public copy are byte-identical. This artifact
status is publication evidence, not a new mathematical authority.

```bash
./scripts/pnpmw run book:assemble
./scripts/pnpmw run book:typography
./scripts/pnpmw run book:check
./scripts/pnpmw run book:render
```

Run these commands from the Git root. A fresh checkout or worktree is prepared
with `./scripts/bootstrap-worktree.sh`.

`book:typography` rejects TeX commands hidden in Markdown code spans,
suspicious bare TeX control words in math, raw TeX in prose, and strict KaTeX
parse failures. `book:check` verifies that typography gate together with
source order, attribution/provenance, anchors and links, evidence
declarations/reviewers, generated freshness, and embedded diagram schemas.
`book:render` adds a local-asset, bounded browser
pagination check. Renderer implementation and optional local upstream-package
instructions live in `print/README.md`; prose style and licensing live
in `book/STYLE.md`, `book/CREDITS.md`, and
`book/LICENSE.md`.

The book must describe `BNat` as a separate model and present the
directed normalization cell before the hom-discreteness equality. A physical
split of `emdash3_2.lp` is not a prerequisite for book development.

## Current Deferred Boundaries

The following remain explicit future work rather than hidden assumptions:

- full general dependent adjunctions `Sigma_F ⊣ F^* ⊣ Pi_F`, including the
  planned `Pi_f`/comma-category infrastructure;
- remaining displayed structural logic and product/curry compatibility; the
  transparent Cat-valued sibling product now has fixed-base
  projection/pairing, derived swap/diagonal, point/full/capped action, both
  universal-property betas, and same-base `Product_map_func` transport, while
  universe-level projection transfors, raw kernel pullback stability, a
  global `Functord_cat` product conversion, dependent-chain exchange, and
  full family base-two-cell action remain open;
- a named `section_total` presentation facade and packaged projection laws;
  its transparent expression and the general
  `sigma_pullback_total_func(F,D)` base-change totalization are active;
- semantic uncurry action on arbitrary transfors;
- a named public facade varying higher arrows between ordinary transfors, and
  a complete recursive simplicial/omega interface beyond the active whole
  post/left and pre/right surfaces. The existing second `homd_`/Sigma internal
  action has already passed one current-source, no-associativity tetrahedral
  probe, so that validated generic action is not itself an open gap;
- the arrow action of `sigma_intro_tapp0_func`;
- off-diagonal `tapp1_*` projections for `sigma_map_transf` beyond its current
  point-component computation;
- a fully internalized general coend/coinserter semantics for profunctor tensor;
- general tensor associativity/coherence and complete co-Yoneda equivalences;
- dependent elimination and semantic collage construction for primitive join;
- CommRing lifting and left exactness of the now-constructed fixed-site
  Cat-valued direct-cover reflector, together with slice transport and
  locally ringed scheme packaging; the rigid Cat-valued `Sheaf_cat` facade
  and existing `SheafificationCapability` are already instantiated;
- an inductive/HIT presentation of generated topology with derivation
  induction or executable cover normal forms. The active impredicative
  intersection already supplies proposition-valued least generated topology,
  including the direct big-affine Zariski specialization, without truncating
  witness-rich presentations;
- specialized higher `fapp1*` projections of `Hom_tele_func` beyond current
  demand;
- raw unreified-path observer computation, reverse pointwise-to-coherent-core
  assembly, and consumer-led core-universe inclusion functors. A fully native
  two-sided OneCat object-equality/ordinary-isomorphism equivalence remains
  optional future work; the former compatibility decoder, its theorem, and
  its reviewer clients are already deleted and are not prerequisites;
- generic abstraction of the completed walking-endomorphism presentation,
  full functor-category initiality, a displayed dependent path-action/section
  construction, source action for the now-active category-indexed
  `Groupoidify(C)`, the resulting `Groupoidify_func`/`Path_cat_func`
  adjunction, and general higher-inductive categories or pushouts. The generic
  formation, whole unit/recursor, arbitrary-target mapping equivalence,
  compositor observation, and WalkingArrow--Interval recovery are already
  active. Ordinary raw-function `path_map_func` is the complete canonical
  nondependent action. A future exceptional former may add a local comparison
  theorem, and a future dependent consumer may motivate the displayed
  construction, but neither reinstates a generic selected-action registry by
  default;
- a finalized parser/surface language;
- module splitting of the single kernel file after comment/section boundaries
  stabilize.

Consult `INDEX.md` for the active plan owning a deferred item. Do not copy a
constructor-local law from an older plan without first rechecking the current
generic owner.

## Retirement And Recovery Policy

The v3.1 and v2 baselines are retired from normal checking and design work.
Their surviving lessons are represented in the active source, this SOP,
Foundations, canonical syntax, current plans, and the v2 retirement audit.

Infinity Codex uses the Git-root `.codex/hooks.json` and shared
`scripts/infinity_codex.py` for launches from either the repository root or
this package. There is intentionally no nested `emdash2/.codex/hooks.json`,
because Codex would run both matching layers. Response archives remain under
this package's ignored `tmp/ai-responses/` for continuity and are recovery
evidence only. Authority remains:

```text
active code/SOP -> active plan and side-task ledger
                -> explicitly linked decision responses -> raw archive.
```

After compaction/interruption, re-read the active authorities and task plan,
inspect staged/unstaged diffs, relocate symbols with `rg`, and run a bounded
baseline check before continuing.
