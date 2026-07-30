<a id="appendix-status"></a>

# Appendix F. Implementation Status And Research Directions

This appendix summarizes the boundary of the expanded development edition.
The generated [evidence register](#appendix-evidence) remains the detailed
claim-by-claim authority.

## F.1 Status Matrix

| Area | Checked nucleus used by the book | Explicit boundary |
| --- | --- | --- |
| Equality-local type theory | Equality induction, path action, Sigma/Pi path interfaces, elementary inductives | No claim of a complete standalone HoTT implementation |
| Directed categories | Iterated homs, identities, composition, functors, transfors, opposites, products | No complete weak omega-category metatheory or model theorem |
| Directed families | Fibres, transport, family morphisms, Sigma totals, Pi sections, displayed hom action, fixed-base fibrewise products, asymmetric pullback totalization, and constant-domain displayed evaluation | Arbitrary displayed telescope depth, mixed-domain evaluation, and exchange across genuine dependency remain open |
| Cut and transfor calculus | Lower-star postcomposition, upper-star precomposition, off-diagonal `tapp1`, horizontal composition, selected universal beta/eta cuts | No unrestricted runtime associativity rewrite or claim that all higher coherence is judgmental |
| Equivalence and univalence | `TypeEquiv`, groupoid univalence, truncated-universe univalence, native recursive omega-equivalence facade and one-way hom action | No full general object-equality/ordinary-isomorphism equivalence for arbitrary categories |
| Induction | Nat and equality induction, fixed/varying-source `PathOut` induction, composition benchmark | No general equivalence with homotopy-initial categorical algebras |
| Directed HITs | One opaque WalkingEnd signature, contextual eliminator, section and recursor specializations | No general directed-HIT signature compiler or arbitrary cell-complex schema |
| Truncation and height | Recursive truncation properties and closure, evidence-property, finite `IsNCat` object truncation | No general truncation reflector or arbitrary truncation HIT |
| WalkingEnd calculation | Code, encode, power, spiral, contextual decoder, normalization cell/path, two inverse laws, carrier equivalence and noninvertibility results | No packaged monoid isomorphism, reverse `BNat` functor, full hom-category equivalence, or initiality theorem |
| Higher groupoidal shadow | Selected Eckmann–Hilton commutativity slice | No claim that all directed structure is groupoidal |
| Ordinary categorical specialization | Precategories, univalent categories, strict categories, functors, natural transformations, and ordinary Yoneda developed over the native vocabulary | These readable one-categorical theorems are mathematical development, not definitions of native `Cat` |
| Adjunctions and equivalences | Triangle cuts and hom-profunctor comparison; one-way lift from ordinary isomorphism to native evidence | No checked native fully-faithful/essentially-surjective characterization or general adjointification package |
| Yoneda and profunctors | Cat-valued profunctors, endpoint reindexing, representables, shaped cells, fixed-middle tensor, co-Yoneda beta/fusion | No general coend semantics, tensor associativity package, full Cat-valued Yoneda equivalence, or profunctor bicategory |
| Opposite, duality, and dagger | Opposite category action and selected opposite-duality comparisons | Dagger, unitary structure, and dagger univalence are mathematical development pending a native involutive interface |
| Structure identity and saturation | Truncation/evidence-property footholds and ordinary-isomorphism lift | Generic native structure identity and Rezk completion, including their higher universal properties, are research boundaries |
| Weighted limits and Kan interfaces | Weighted representability, beta/eta comparison, right-adjoint preservation, terminal/conjoint specializations | Standard end formulas, pointwise Kan semantics, existence, and general dependent adjunctions are not globally packaged |
| Weighted colimits and join | Opposite-dual colimit preservation, terminal/companion specializations, primitive join recursor and three beta observations | General coend semantics and join-as-collage mapping, hom-decomposition, opposite, and dependent-elimination theorems remain open |
| Formal presentation | Checked categorical owners; a bounded TypeScript outer LF, explicit Core, contextual elaborator, checker/runtime, and reviewed text subset | No compiler for the complete book surface, arbitrary displayed coherence, or whole-library transfer; readable notation is not a second kernel |
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

## F.3 Foundational Extensions

A reusable directed-HIT schema should generate contextual elimination and
constructor computation from typed object, arrow, and higher-cell boundaries.
Its validation must include rewrite overlap and subject-reduction behavior,
not only a semantic signature.

A truncation reflector should construct a universal truncated target rather
than merely certify an existing classifier. Directed categorical truncation
would additionally need to specify which lower arrows and compositions are
preserved.

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
and displayed-natural binders, including one mixed dependent telescope. An
optional deterministic Lambdapi path remains a conformance oracle; it is not
a production dependency, and the active Lambdapi development remains the
mathematical authority.

This is a real executable bridge, but not completion of the canonical
mathematical surface. Arbitrary displayed coherence, unrestricted telescope
depth and variance, a compiler for the whole book notation, and systematic
transfer of the remaining library are still engineering boundaries. The
older TypeScript prototype remains historical feasibility evidence; its
stale category-specific layer is neither an authority nor the architecture
of the renewed product.

On the engineering side, a physical split of `emdash3_2.lp` remains
optional. It should begin only when a measured dependency or evidence-ownership
problem justifies the migration, and it must preserve declaration/rule order
and all current checks one boundary at a time.

## F.6 Reading Claims Across Editions

The edition version in `book/book.json` identifies the source snapshot
policy for generated artifacts. A later edition may promote a research
boundary only when the evidence register names active owners and independent
checks, or when the claim is explicitly reclassified as mathematical
development with stated prerequisites. Dated reports preserve why a boundary
was chosen; they do not override the current code.
