<a id="appendix-status"></a>

# Appendix F. Implementation Status And Research Directions

This appendix summarizes the boundary of the fourth-spiral groupoidal-
realization development edition. The generated
[evidence register](#appendix-evidence) remains the detailed claim-by-claim
authority.

## F.1 Status Matrix

| Area | Checked nucleus used by the book | Explicit boundary |
| --- | --- | --- |
| Equality-local type theory | Equality induction, path action, Sigma/Pi path interfaces, elementary inductives | No claim of a complete standalone HoTT implementation |
| Directed categories | Iterated homs, identities, composition, functors, transfors, opposites, products | No complete weak omega-category metatheory or model theorem |
| Directed families | Fibres, transport, family morphisms, Sigma totals, Pi sections, displayed hom action, fibrewise products, pullback totalization, displayed evaluation, and finite canonical sibling/Sigma telescopes | Arbitrary dependency or variance graphs, unrestricted mixed introduction/evaluation, and exchange across genuine dependency remain open |
| Cut and transfor calculus | Lower-star postcomposition, upper-star precomposition, off-diagonal `tapp1`, horizontal composition, selected universal beta/eta cuts, whole internal displayed laxity, ordinary post/pre surfaces, and the retained functor compositor | No unrestricted runtime associativity rewrite, completed generic lax classifier, or claim that all higher coherence is judgmental |
| Equivalence and univalence | `TypeEquiv`, groupoid univalence, truncated-universe univalence, native recursive omega-equivalence facade and one-way hom action | No full general object-equality/ordinary-isomorphism equivalence for arbitrary categories |
| Induction | Nat and equality induction, fixed/varying-source `PathOut` induction, composition benchmark | No general equivalence with homotopy-initial categorical algebras |
| Directed and groupoidal HITs | Opaque WalkingEnd and Circle signatures, the groupoidal interval, category-indexed `Groupoidify(C)`, selected dependent eliminators, and constructor computation at their reviewed owners | No general directed/HIT signature compiler, arbitrary pushout or cell-complex schema, or automatic positivity/coherence checker |
| Truncation and height | Recursive truncation properties and closure, evidence-property, finite `IsNCat` object truncation, classified `NType_cat(n)` targets, point-computing `Trunc_ntype(n,A)`, restricted elimination, and whole map action | No general directed categorical truncation, arbitrary quotient schema, left-exactness theorem, or complete comparison with every hub-and-spoke presentation |
| WalkingEnd calculation | Code, encode, power, spiral, contextual decoder, normalization cell/path, two inverse laws, carrier equivalence, noninvertibility results, and the whole free-inversion comparison with the Circle | No packaged monoid isomorphism, reverse `BNat` functor, full hom-category equivalence with `BNat`, or directed initiality theorem |
| Groupoidal realization | Path categories and path functors; product-path split/join and coherent transport; Circle/Integer encode-decode and monodromy; WalkingEnd/Circle and WalkingArrow/interval mapping theorems; category-indexed groupoidification; path-realized pseudo-laxity | Source functoriality and the packaged groupoidification adjunction, closure for every former, generic simplex regressions, and a complete computational HoTT metatheory remain open |
| Profiled Gray direction | Computational strict-functor codes, the strict-object/lax-arrow `GrayHom_lax` profile, one selected right closure, the walking square, and a nonidentity interchanger with retained next action | No mirror closure, full Crans–Gray biclosed monoidal structure, tensor functoriality/coherence, or global strict-cut migration |
| Ordinary categorical specialization | Precategories, univalent categories, strict categories, functors, natural transformations, and ordinary Yoneda developed over the native vocabulary | These readable one-categorical theorems are mathematical development, not definitions of native `Cat` |
| Adjunctions and equivalences | Triangle cuts and hom-profunctor comparison; one-way lift from ordinary isomorphism to native evidence | No checked native fully-faithful/essentially-surjective characterization or general adjointification package |
| Yoneda and profunctors | Cat-valued profunctors, endpoint reindexing, representables, shaped cells, fixed-middle tensor, co-Yoneda beta/fusion | No general coend semantics, tensor associativity package, full Cat-valued Yoneda equivalence, or profunctor bicategory |
| Presheaves and sieves | Cat-valued presheaves, Yoneda and slices, higher sieves, ordinary pointwise-subterminal sieves, pullback membership, and commutative-ring invertibility sieves | No global ordinary-sieve classifier, automatic representation by one open, topology, descent, or sheafification follows from this layer |
| Sites and descent | Ordinary-sieve Grothendieck topology laws, chaotic model, internally generated least topology, whole sieve extensions, matching and section Hom families, and topology-locality | No inductive cover derivations, coverhood decision procedure, automatic subcanonicity, sheafification reflector, or identification with a separate rigid sheaf facade follows from locality alone |
| Direct cover sheafification | Cat-valued categorical-HIT completion with whole return/glue/silent data, derived topology-locality, recursor, whole Hom universality, adjunction, and reflective counit | Fixed-site and Cat-valued only; no arbitrary coefficients, commutative-ring lift, left exactness, site base-change theorem, or classical plus-construction comparison |
| Commutative algebra | Set-carrier rings and structured maps, finite unimodular presentations, polynomial and localization universal-property interfaces, selected unit/zero/idempotent models, and whole iterated/product-localization equivalence | No arbitrary polynomial/localization existence, monomial or fraction representation, categorical product theorem, global ring-package identity, or affine geometry follows from this layer alone |
| Affine geometry | Yoneda functor of points; ordinary basic-open sieve; pointwise localization representation and multiplicative intersection; big affine slice, coordinate presheaf, and least generated Zariski topology; assumption-explicit reflective structure sheaf, localization locality, and thin affine presentation | No whole natural basic-open equivalence, global localization choice, CommRing-valued sheafification construction, small-site comparison, subcanonicity, stalk-local theorem, qcqs comparison, or representation-independent category of affine schemes |
| Site-relative schemes | One global reflective ringed object and covering sieve; witness-rich binary generation; whole actual-slice restriction; supplied affine-basis realizations; topology-local ring forcing; dependent binary scheme total; selected actual overlap with derived ring restrictions | Binary and relative to the supplied site; no atlas-first gluing, induced slice topology, arbitrary pullback construction, overlap-affineness theorem, scheme-morphism category, compact-open/classical comparison, or representation-independent scheme theorem |
| Supplied projective-line boundary | Universal-property Laurent transition maps; literal common-overlap identity package; thin adapter to actual inherited chart restrictions; dependent total of one already-global scheme, its actual overlap, and Laurent coordinates | The global object and Laurent identity paths remain supplied; no atlas-first gluing, projectivity or non-affineness proof, graded ring, homogeneous localization, degree-zero construction, `Proj`, or general projective space |
| Opposite, duality, and dagger | Opposite category action and selected opposite-duality comparisons | Dagger, unitary structure, and dagger univalence are mathematical development pending a native involutive interface |
| Structure identity and saturation | Truncation/evidence-property footholds and ordinary-isomorphism lift | Generic native structure identity and Rezk completion, including their higher universal properties, are research boundaries |
| Weighted limits and Kan interfaces | Weighted representability, beta/eta comparison, right-adjoint preservation, terminal/conjoint specializations | Standard end formulas, pointwise Kan semantics, existence, and general dependent adjunctions are not globally packaged |
| Weighted colimits and join | Opposite-dual colimit preservation, terminal/companion specializations, primitive join recursor and three beta observations | General coend semantics and join-as-collage mapping, hom-decomposition, opposite, and dependent-elimination theorems remain open |
| Formal presentation | Checked categorical owners; a bounded TypeScript outer LF, explicit Core, contextual elaborator, checker/runtime, reviewed text subset, adjunction/structure declaration conveniences, and client-side reviewer | No compiler for the complete book surface, arbitrary displayed coherence, general record/inductive facility, or whole-library transfer; readable notation is not a second kernel |
| Metatheory and models | Bounded typechecking, subject-reduction checks performed by Lambdapi, focused diagnostics, and the concrete BNat model | No global confluence, normalization, canonicity, decidability, consistency, or semantic-soundness theorem for the full combined calculus |
| Production artifact | Manifest assembly, provenance/evidence checks, local assets, bounded browser validation, and deterministic PDF export | External mathematical peer review and a non-draft public edition remain future release work |

## F.2 Near-Term Formal Strengthening

The most direct strengthening of Theorem 8.1 is to package composition and
addition compatibility. Its proof can use the checked power recursion, Nat
addition associativity, and both carrier inverse laws. The desired result is a
monoid-level comparison with an explicit orientation matching `BNat`.

Next comes a reverse functor from `BNat` to WalkingEnd and a comparison
with the existing model functor. This requires reusable action-to-functor and
functor-extensionality infrastructure; it should not be simulated by making
the opaque hom definitionally Nat-valued.

Full initiality is a further layer. It asks for a category of endomorphism
algebras, structured maps, and coherent higher transfors, followed by an
appropriate contractibility or equivalence theorem.

Generic groupoidification now supplies its target-side mapping equivalence,
but not yet its action on a source functor $C\to D$. The next categorical
strengthening is to derive that action from extension of the composite unit,
prove its identity and composition laws by whole uniqueness, and only then
package the adjunction with the path-category functor. The mapping theorem
should not be renamed an adjunction before that source action exists.

## F.3 Foundational Extensions

A reusable directed-HIT schema should generate contextual elimination and
constructor computation from typed object, arrow, and higher-cell boundaries.
Its validation must include rewrite overlap and subject-reduction behavior,
not only a semantic signature.

The active classified truncation reflector now constructs a groupoidal
$n$-truncated target rather than merely certifying an existing classifier.
Future work should compare that sorted interface with classical hub-and-spoke
presentations, add selected quotient consumers, and investigate
left-exactness. Directed categorical truncation remains a different problem:
it must specify which lower arrows and compositions are preserved.

The univalence programme should continue to separate carrier equivalence,
ordinary categorical isomorphism, and native equality-valued recursive
equivalence. A full theorem relating object equality and ordinary isomorphism
must be proved at the intended categorical level rather than recovered through
retired compatibility aliases.

## F.4 Categorical Extensions

The representable/profunctor and identity layers suggest four staged projects:

1. package a fully faithful Yoneda embedding with mapping-category
   equivalences and higher naturality;
2. construct or model Cat-valued coends/coinserters and relate the opaque
   tensor to their universal property;
3. assemble associators, unitors, and horizontal cell composition into a
   coherent profunctor bicategory or suitable omega-categorical analogue.
4. design generic structure identity and Rezk completion interfaces only after
   the intended native equivalence and higher mapping properties are fixed.

Weighted limits, colimits, adjunctions, duality, and joins now enter the
expanded chapter sequence through the triangle reductions, right-adjoint
weighted-limit preservation, its opposite-dual colimit theorem, and the join
recursor. The checked interfaces are the theorem spine; neighboring Kan,
end/coend, dagger, collage, and dependent-elimination theory remains
explicitly status-labeled rather than presented as a feature catalogue.

The selected Gray slice adds a concrete higher-dimensional stress test. Its
walking-square interchanger is derived from the ordinary internal laxity
action, but a full Gray theory still needs the mirror closure, tensor action,
and coherent associativity and unit data. Those are structural projects, not
extra fields to append to the current interchanger example.

## F.5 Semantics And Proof-Assistant Engineering

The largest research objective is a semantics and metatheory for a precisely
stated fragment: typing, substitution, subject reduction, normalization or a
weaker operational theorem, and interpretation in a suitable strict/lax
omega-categorical model. The current executable artifact is evidence for
specific interfaces, not a substitute for that theorem.

The renewed TypeScript product now elaborates a bounded direct-TypeScript and
categorical-text surface into backend-neutral explicit Core, then checks and
reduces that Core with a small dependent logical framework. Its contextual
categorical layer covers reviewed ordinary, natural, displayed-functorial,
and displayed-natural binders. Within the canonical sibling/Sigma normal form
it supports finite dependency depth and sibling groups; qualified finite
Hom-category recursion and finite rigid indexed-section chains are also
executable. An optional deterministic Lambdapi path remains a conformance
oracle. It is not a production dependency, and the active Lambdapi
development remains the mathematical authority.

The same outer LF has two bounded authoring conveniences. One declares an
adjunction from already typed rectangular data, or from a counit and whole
hom transpose, while retaining proof-time rather than runtime agreement with
the stable observations. The other declares an unparameterized,
nonrecursive, single-constructor dependent structure with named projections
and projection beta rules. Both expand to ordinary declarations; neither adds
a trusted Core form, categorical owner, general record eta, eliminator,
recursion, or positivity principle.

This is a real executable bridge, visible in the client-side integrated
reviewer, but not completion of the canonical mathematical surface. Arbitrary
dependency and variance graphs, coherence outside the qualified grammar, a
compiler for the whole book notation, a general record or inductive facility,
and systematic transfer of the remaining library are still engineering
boundaries. The older TypeScript prototype remains historical feasibility
evidence; its stale category-specific layer is neither an authority nor the
architecture of the renewed product.

Ordinary DevOps makes checks, assembly, and release repeatable. The project's
MathOps discipline additionally separates mathematical owners, independent
reviewers, generated evidence and health views, authored sources, and
deterministic release artifacts. That separation makes drift and provenance
auditable. It does not convert a passing build, warning inventory, browser
run, or reproducible PDF into a confluence, normalization, consistency, or
soundness theorem.

## F.6 Reading Claims Across Editions

The edition version in `book/book.json` identifies the source snapshot
policy for generated artifacts. A later edition may promote a research
boundary only when the evidence register names active owners and independent
checks, or when the claim is explicitly reclassified as mathematical
development with stated prerequisites. Dated reports preserve why a boundary
was chosen; they do not override the current code.
