<a id="appendix-glossary"></a>

# Appendix D. Glossary And Concept Index

This appendix fixes the vocabulary used by the expanded development edition.
Each entry points to the place where the idea is constructed or used, rather
than to a page number that would change with paper size and typography.

## D.1 Glossary

<a id="glossary-adjunction"></a>

**Adjunction.** Functors $F:A\to B$ and $G:B\to A$ equipped either with a
unit and counit satisfying the two triangle laws or with an equivalent
natural hom comparison. In the active calculus, the triangles are universal
cuts with selected computational owners. See [Chapter 12](#chapter-12).

<a id="glossary-arrow-induction"></a>

**Arrow induction.** Extension of data at the reflexive outgoing arrow to a
section over $\mathsf{PathOut}$. Unlike equality induction, its base category may
contain noninvertible arrows. See [Chapter 5](#chapter-5).

<a id="glossary-based-hom"></a>

**Based hom-category.** For a selected base object $*$ and endpoint
$x$, the category $H_x=\operatorname{Hom}_W(*,x)$. Its objects are based
1-arrows and its arrows are based 2-cells. See [Chapter 8](#chapter-8).

<a id="glossary-bnat"></a>

**BNat.** The separate one-object category with $\mathbb N$-valued hom, zero
identity, and addition composition. It is a concrete model of the walking
signature, not the definition of WalkingEnd. See
[§8.1.2](#chapter-8-1-2).

<a id="glossary-canonical-surface"></a>

**Canonical mathematical surface.** The readable notation in which the book
states categorical judgments and rule schemas. It maps to stable kernel
owners but is not itself a currently implemented parser language. See
[Appendix G.5](#appendix-formal-presentation-g5).

<a id="glossary-carrier-equivalence"></a>

**Carrier equivalence.** An equivalence between underlying classifiers, here
$\operatorname{Hom}_W(*,*)\simeq\mathbb N$. It does not by itself package
preservation of composition or an equivalence of ambient categories. See
[Theorem 8.1](#chapter-8).

<a id="glossary-cat-family"></a>

**Cat-valued directed family.** A functor $E:K\to\mathsf{Cat}$. It assigns a
category $E[k]$ to each base object and a transport functor $E[p]$
to each directed base arrow. See [Chapter 2](#chapter-2).

<a id="glossary-categorical-height"></a>

**Categorical height.** The recursive `IsNCat` condition: dimension zero
is discreteness, and successor dimension asks every hom-category to have the
preceding dimension. See [Chapter 7](#chapter-7).

<a id="glossary-native-category"></a>

**Category, native.** An object of `Cat`, with iterable category-valued homs.
It is not definitionally an ordinary HoTT precategory. See
[Chapters 2](#chapter-2) and [10](#chapter-10).

<a id="glossary-code"></a>

**Code.** The Cat-valued family over WalkingEnd whose base fibre is
$\mathsf{Path}(\mathbb N)$ and whose generator action is successor. See
[§8.1.3](#chapter-8-1-3).

<a id="glossary-coyoneda"></a>

**Co-Yoneda cut.** Elimination of a representable leg from a profunctor
composite. The checked theorem is a shaped, fixed-middle beta/fusion law; a
general coend theorem remains separate. See [Chapter 13](#chapter-13).

<a id="glossary-contextual-eliminator"></a>

**Contextual eliminator.** An eliminator that constructs a displayed functor
between two varying families from base-fibre data and coherent constructor
cells. Sections and ordinary recursors are special cases. See
[Chapter 6](#chapter-6).

<a id="glossary-cut-elimination"></a>

**Cut elimination.** Controlled normalization at the semantic owner of an
arrow, family, structural, or universal cut. It does not mean installing
unrestricted associativity as a global rewrite. See [Chapter 9](#chapter-9).

<a id="glossary-dagger"></a>

**Dagger structure.** A chosen contravariant involution on one category,
identity on objects in the ordinary presentation and coherent with retained
higher action in a prospective native presentation. It is not merely the
operation of taking an arbitrary opposite category. See
[Chapter 14](#chapter-14).

<a id="glossary-directed-hit"></a>

**Directed higher-inductive type/category.** A presentation with object,
directed-arrow, and possibly higher-cell constructors whose arrow generators
are not silently inverted. The current book has one selected implementation,
WalkingEnd, not a general schema. See [Chapter 6](#chapter-6).

<a id="glossary-directed-normalization"></a>

**Directed normalization cell.** The cell
$p\to\mathsf{decode}(\mathsf{encode}(p))$ constructed by the contextual decoder before
hom-discreteness extracts equality. See
[§8.1.4](#chapter-8-1-4).

<a id="glossary-discrete-category"></a>

**Discrete category.** A category whose hom structure agrees with equality of
objects at the selected interface. In a one-dimensional category every
hom-category is discrete; this does not make every ambient 1-arrow invertible.
See [§7.6](#chapter-7).

<a id="glossary-duality"></a>

**Duality.** Either a proof method that transports a theorem through the
opposite construction or additional structure comparing a category with an
opposite. It never licenses an unannounced variance reversal. See
[Chapters 14](#chapter-14) and [17](#chapter-17).

<a id="glossary-elaborator"></a>

**Elaborator.** A future, optional compilation layer that would parse surface
notation, infer omitted categorical data, select stable owners, and emit
explicit Lambdapi terms. The historical parent TypeScript prototype is
feasibility evidence, not that compiler. See
[Appendix G.5](#appendix-formal-presentation-g5).

<a id="glossary-evidence-status"></a>

**Evidence status.** One of checked, formal consequence, mathematical
development, or research boundary. The status describes the relation between
prose and the active artifact. See [How to Read](#how-to-read) and
[Appendix B](#appendix-evidence).

<a id="glossary-formal-presentation"></a>

**Formal presentation.** The four-layer account consisting of the
computational categorical kernel, the canonical mathematical surface, an
optional future elaborator, and external semantic models. The kernel comes
first; it is not post-hoc semantics for an unspecified traditional syntax.
See [Appendix G](#appendix-formal-presentation).

<a id="glossary-functor"></a>

**Functor.** A map with object and iterated-hom action. Generic functoriality,
not constructor-specific laws, owns identity and composition preservation.
See [Chapter 2](#chapter-2).

<a id="glossary-group-completion"></a>

**Group completion.** A future construction freely adjoining inverse motion
to the walking directed generator. It is the proper route from Nat powers
toward integers or a circle comparison. See [§8.1.5](#chapter-8-1-5).

<a id="glossary-hom-action"></a>

**Hom action.** The functorial action induced on a hom-category. Emdash keeps
covariant postcomposition, contravariant precomposition, and simultaneous
two-endpoint action as distinct computational owners. See
[Chapters 2](#chapter-2), [9](#chapter-9), and [13](#chapter-13).

<a id="glossary-join"></a>

**Join.** The selected directed category generated by left and right
embeddings together with cross arrows from the left side to the right side.
Its recursor and three beta observations are checked; a general collage
mapping property and dependent eliminator are not. See
[Chapter 17](#chapter-17).

<a id="glossary-kan-extension"></a>

**Kan extension.** A universal extension along a functor. This edition
expresses right and left Kan interfaces as conjoint- and companion-weighted
limits and colimits; identifying those interfaces with the full standard
pointwise semantics remains mathematical development. See Chapters
[16](#chapter-16) and [17](#chapter-17).

<a id="glossary-lower-star"></a>

**Lower-star action.** Postcomposition: if $g:w\to x$ and $u:x\to y$, then
$u_*(g)=u\circ g:w\to y$. Its active owners are `hom_postcomp_func` and
`hom_postcomp_fapp0`. See [§9.2](#chapter-9).

<a id="glossary-natural-transformation"></a>

**Natural transformation.** In the ordinary specialization, a pointwise
family $\alpha_x:F(x)\to G(x)$ satisfying a naturality equation. A native
transfor retains an off-diagonal action and iterates to higher hom levels, so
the two notions are related but not definitionally identical. See
[Chapter 11](#chapter-11).

<a id="glossary-off-diagonal-action"></a>

**Off-diagonal transfor action.** If $\eta:F\Rightarrow G$ and $f:x\to y$,
then $\eta[f]:F(x)\to G(y)$. Adjacent functor actions accumulate into this
term by strict naturality. See
[Chapter 9](#chapter-9).

<a id="glossary-omega-equivalence"></a>

**Omega-equivalence.** The native recursive equality-valued equivalence
interface for categorical cells. It is distinct from a bare carrier
`TypeEquiv` and from ordinary isomorphism evidence. See
[Chapter 4](#chapter-4).

<a id="glossary-opposite"></a>

**Opposite category.** The active arrow-reversing construction
$C\mapsto C^{\mathrm{op}}$. Opposite duality exchanges selected limit and
colimit interfaces while preserving a visible variance ledger. See
[Chapter 14](#chapter-14).

<a id="glossary-path-category"></a>

**Path category.** $\mathsf{Path}(A)$, the equality-local groupoidal category
on a classifier $A$. It embeds ordinary identity reasoning into the directed
calculus without identifying every directed hom with equality. See
[Chapter 2](#chapter-2).

<a id="glossary-pathout"></a>

**PathOut.** The outgoing-arrow category
$\sum_{y:Z}\operatorname{Hom}_Z(x,y)$ at a fixed source $x$. Its canonical
arrow from $(x,\mathrm{id}_x)$ to $(y,p)$ drives arrow induction. See
[Chapter 5](#chapter-5).

<a id="glossary-precategory"></a>

**Precategory, ordinary.** A classifier of objects with set-valued homs,
identities, composition, and category laws. It is used as a readable
one-categorical specialization of the native iterated-hom architecture. See
[Chapter 10](#chapter-10).

<a id="glossary-profunctor"></a>

**Profunctor.** A Cat-valued functor
$A^{\mathrm{op}}\times B\to\mathsf{Cat}$, contravariant in its first endpoint
and covariant in its second. See
[Chapter 13](#chapter-13).

<a id="glossary-representable"></a>

**Representable.** A family or profunctor obtained from an ambient hom. Its
action is composition, which makes it the computational bridge between
universal properties and cut elimination. See
[Chapters 5](#chapter-5) and [13](#chapter-13).

<a id="glossary-rezk-completion"></a>

**Rezk completion.** A completion intended to turn the selected weak
equivalences into equivalences as seen by saturated targets. The book gives
ordinary Yoneda-image and higher-inductive constructions and a prospective
native specification; no native implementation is claimed. See
[Chapter 15](#chapter-15).

<a id="glossary-rewrite"></a>

**Runtime rewrite.** A directed reduction selecting an intended normal form.
It is distinct from proof-time unification and internal propositional
equality. See [Appendix E](#appendix-computation).

<a id="glossary-saturation"></a>

**Saturation.** The property that the chosen identity-to-equivalence map is
itself an equivalence, or the result of freely enforcing that property by a
completion. Saturation is not finite categorical height. See
[Chapter 15](#chapter-15).

<a id="glossary-strict-category"></a>

**Strict category, ordinary HoTT sense.** A precategory whose object
classifier is a set. This is object-level truncation and must not be confused
with strict transfor computation or strict higher associativity. See
[Chapter 14](#chapter-14).

<a id="glossary-strict-transfor"></a>

**Strict transfor.** A native transfor for which the selected two-sided
naturality cuts compute through the global `tapp*` calculus. The adjective
does not say that every coherence law in its ambient category is
judgmental. See [Chapters 9](#chapter-9) and [14](#chapter-14).

<a id="glossary-structure-identity"></a>

**Structure identity principle.** A theorem identifying equality of
structured objects with an appropriate structure-preserving equivalence when
the displayed notion of structure is univalent or standard. The ordinary
theorem is developed mathematically; a generic native package is a research
boundary. See [Chapter 15](#chapter-15).

<a id="glossary-transfor"></a>

**Transfor.** An arrow in a functor category, generalizing a natural
transformation through off-diagonal and higher hom action. See
[Chapters 9](#chapter-9) and [11](#chapter-11).

<a id="glossary-truncation"></a>

**Truncation evidence.** A recursive property of an existing classifier: at
the base level it is contractibility, and at successor levels it truncates
all identity classifiers one step lower. It is not a truncation reflector.
See [Chapter 7](#chapter-7).

<a id="glossary-univalence"></a>

**Univalence.** An interface relating identity of classifiers or packages to
an appropriate equivalence. This edition has checked groupoid and restricted
truncated-universe interfaces but does not claim one universal directed
univalence axiom. See [Chapter 4](#chapter-4).

<a id="glossary-unitary"></a>

**Unitary arrow.** In a dagger category, an arrow whose dagger is an inverse.
The ordinary theory is developed in Chapter 14; a native unitary classifier
awaits the selected dagger interface and coherent higher action. See
[Chapter 14](#chapter-14).

<a id="glossary-upper-star"></a>

**Upper-star action.** Precomposition: if $u:x\to y$ and $h:y\to z$, then
$u^*(h)=h\circ u:x\to z$. Its active owners are
`hom_precomp_along_func` and `hom_precomp_along_fapp0`. The action is
contravariant in $u$. See [§9.2](#chapter-9).

<a id="glossary-weighted-colimit"></a>

**Weighted colimit.** A representation of a weighted-cocone profunctor. The
selected interface and left-adjoint preservation theorem are checked through
opposite duality; full coend semantics is not assumed. See
[Chapter 17](#chapter-17).

<a id="glossary-weighted-limit"></a>

**Weighted limit.** A representation of a weighted-cone profunctor, with beta
and eta supplied by a chosen profunctor comparison. The selected interface
and right-adjoint preservation theorem are checked. See
[Chapter 16](#chapter-16).

<a id="glossary-walkingend"></a>

**WalkingEnd.** The opaque one-dimensional directed HIT/category with a base
object and a directed generating endomorphism. See
[Chapters 6](#chapter-6) and [8](#chapter-8).

<a id="glossary-yoneda"></a>

**Yoneda principle.** Natural maps out of a representable are determined by
their value at the identity. The ordinary equivalence is developed by
encode-decode, while the active native theorem is the shaped co-Yoneda cut;
full Cat-valued Yoneda remains a named boundary. See
[Chapter 13](#chapter-13).

## D.2 Index strategy

This edition uses the linked concept index as its stable index. Terms
are curated rather than extracted from raw identifier frequency; synonyms
point to one canonical entry, and every destination is an explicit HTML
anchor checked by the source gate.

Page numbers are deliberately absent from the source because they depend on
the renderer, paper size, and font metrics. A later release tool may resolve
these anchors to PDF page labels, but the anchor remains the authority. New
index entries should be added when a concept is defined or changes status,
not for every occurrence of its implementation name.
