<a id="appendix-status"></a>

# Appendix F. Implementation Status And Research Directions

This appendix summarizes the boundary of the expanded development edition.
The generated [evidence register](#appendix-evidence) remains the detailed
claim-by-claim authority.

## F.1 Status matrix

| Area | Checked nucleus used by the book | Explicit boundary |
| --- | --- | --- |
| Equality-local type theory | Equality induction, path action, Sigma/Pi path interfaces, elementary inductives | No claim of a complete standalone HoTT implementation |
| Directed categories | Iterated homs, identities, composition, functors, transfors, opposites, products | No complete weak omega-category metatheory or model theorem |
| Directed families | Fibres, transport, family morphisms, Sigma totals, Pi sections, displayed hom action | Whole-square laxity facade remains deferred where it would duplicate the internal owner |
| Equivalence and univalence | `TypeEquiv`, groupoid univalence, truncated-universe univalence, native recursive omega-equivalence facade and one-way hom action | No full general object-equality/ordinary-isomorphism equivalence for arbitrary categories |
| Induction | Nat and equality induction, fixed/varying-source `PathOut` induction, composition benchmark | No general equivalence with homotopy-initial categorical algebras |
| Directed HITs | One opaque WalkingEnd signature, contextual eliminator, section and recursor specializations | No general directed-HIT signature compiler or arbitrary cell-complex schema |
| Truncation and height | Recursive truncation properties and closure, evidence-property, finite `IsNCat` object truncation | No general truncation reflector or arbitrary truncation HIT |
| WalkingEnd calculation | Code, encode, power, spiral, contextual decoder, normalization cell/path, two inverse laws, carrier equivalence and noninvertibility results | No packaged monoid isomorphism, reverse `BNat` functor, full hom-category equivalence, or initiality theorem |
| Higher groupoidal shadow | Selected Eckmann–Hilton commutativity slice | No claim that all directed structure is groupoidal |
| Profunctors | Cat-valued profunctors, endpoint reindexing, representables, shaped cells, fixed-middle tensor, co-Yoneda beta/fusion | No general coend semantics, tensor associativity package, full Yoneda equivalence, or profunctor bicategory |
| Production artifact | Manifest assembly, provenance/evidence checks, local assets, bounded browser validation, deterministic PDF command | Publication editing and external peer review remain future release work |

## F.2 Near-term formal strengthening

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

## F.3 Foundational extensions

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

## F.4 Categorical extensions

The representable/profunctor layer suggests three staged projects:

1. package a fully faithful Yoneda embedding with mapping-category
   equivalences and higher naturality;
2. construct or model Cat-valued coends/coinserters and relate the opaque
   tensor to their universal property;
3. assemble associators, unitors, and horizontal cell composition into a
   coherent profunctor bicategory or suitable omega-categorical analogue.

Weighted limits, colimits, adjunctions, duality, and joins now enter the
expanded chapter sequence through the triangle reductions, right-adjoint
weighted-limit preservation, its opposite-dual colimit theorem, and the join
recursor. The checked interfaces are the theorem spine; neighboring Kan,
end/coend, dagger, collage, and dependent-elimination theory remains
explicitly status-labeled rather than presented as a feature catalogue.

## F.5 Semantics and proof-assistant engineering

The largest research objective is a semantics and metatheory for a precisely
stated fragment: typing, substitution, subject reduction, normalization or a
weaker operational theorem, and interpretation in a suitable strict/lax
omega-categorical model. The current executable artifact is evidence for
specific interfaces, not a substitute for that theorem.

On the engineering side, a physical split of `emdash3_2.lp` remains
optional. It should begin only when a measured dependency or evidence-ownership
problem justifies the migration, and it must preserve declaration/rule order
and all current checks one boundary at a time.

## F.6 Reading claims across editions

The edition version in `book/book.json` identifies the source snapshot
policy for generated artifacts. A later edition may promote a research
boundary only when the evidence register names active owners and independent
checks, or when the claim is explicitly reclassified as mathematical
development with stated prerequisites. Dated reports preserve why a boundary
was chosen; they do not override the current code.
