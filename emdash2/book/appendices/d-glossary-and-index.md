<a id="appendix-glossary"></a>

# Appendix D. Glossary And Concept Index

This appendix fixes the vocabulary used by the expanded development edition.
Each entry points to the place where the idea is constructed or used, rather
than to a page number that would change with paper size and typography.

## D.1 Glossary

<a id="glossary-arrow-induction"></a>

**Arrow induction.** Extension of data at the reflexive outgoing arrow to a
section over `PathOut`. Unlike equality induction, its base category may
contain noninvertible arrows. See [Chapter 5](#chapter-5).

<a id="glossary-based-hom"></a>

**Based hom-category.** For a selected base object `*` and endpoint
`x`, the category `H_x=Hom_W(*,x)`. Its objects are based
1-arrows and its arrows are based 2-cells. See [Chapter 8](#chapter-8).

<a id="glossary-bnat"></a>

**BNat.** The separate one-object category with Nat-valued hom, zero identity,
and addition composition. It is a concrete model of the walking signature,
not the definition of WalkingEnd. See [§8.1.2](#chapter-8-1-2).

<a id="glossary-carrier-equivalence"></a>

**Carrier equivalence.** An equivalence between underlying classifiers, here
`TypeEquiv(Hom_W(*,*),Nat)`. It does not by itself package preservation of
composition or an equivalence of ambient categories. See
[Theorem 8.1](#chapter-8).

<a id="glossary-cat-family"></a>

**Cat-valued directed family.** A functor `E:K->Cat`. It assigns a
category `E[k]` to each base object and a transport functor `E[p]`
to each directed base arrow. See [Chapter 2](#chapter-2).

<a id="glossary-categorical-height"></a>

**Categorical height.** The recursive `IsNCat` condition: dimension zero
is discreteness, and successor dimension asks every hom-category to have the
preceding dimension. See [Chapter 7](#chapter-7).

<a id="glossary-code"></a>

**Code.** The Cat-valued family over WalkingEnd whose base fibre is
`Path(Nat)` and whose generator action is successor. See
[§8.1.3](#chapter-8-1-3).

<a id="glossary-contextual-eliminator"></a>

**Contextual eliminator.** An eliminator that constructs a displayed functor
between two varying families from base-fibre data and coherent constructor
cells. Sections and ordinary recursors are special cases. See
[Chapter 6](#chapter-6).

<a id="glossary-directed-hit"></a>

**Directed higher inductive type/category.** A presentation with object,
directed-arrow, and possibly higher-cell constructors whose arrow generators
are not silently inverted. The current book has one selected implementation,
WalkingEnd, not a general schema. See [Chapter 6](#chapter-6).

<a id="glossary-directed-normalization"></a>

**Directed normalization cell.** The cell
`p -> decode(encode(p))` constructed by the contextual decoder before
hom-discreteness extracts equality. See
[§8.1.4](#chapter-8-1-4).

<a id="glossary-discrete-category"></a>

**Discrete category.** A category whose hom structure agrees with equality of
objects at the selected interface. In a one-dimensional category every
hom-category is discrete; this does not make every ambient 1-arrow invertible.
See [§7.6](#chapter-7).

<a id="glossary-evidence-status"></a>

**Evidence status.** One of checked, formal consequence, mathematical
development, or research boundary. The status describes the relation between
prose and the active artifact. See [How to Read](#how-to-read) and
[Appendix B](#appendix-evidence).

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

<a id="glossary-lower-star"></a>

**Lower-star action.** Postcomposition: if `g:w→x` and `u:x→y`, then
`u_*(g)=u∘g:w→y`. Its active owners are `hom_postcomp_func` and
`hom_postcomp_fapp0`. See [§9.2](#chapter-9).

<a id="glossary-upper-star"></a>

**Upper-star action.** Precomposition: if `u:x→y` and `h:y→z`, then
`u^*(h)=h∘u:x→z`. Its active owners are
`hom_precomp_along_func` and `hom_precomp_along_fapp0`. The action is
contravariant in `u`. See [§9.2](#chapter-9).

<a id="glossary-cut-elimination"></a>

**Cut elimination.** Controlled normalization at the semantic owner of an
arrow, family, structural, or universal cut. It does not mean installing
unrestricted associativity as a global rewrite. See [Chapter 9](#chapter-9).

<a id="glossary-off-diagonal-action"></a>

**Off-diagonal transfor action.** For `eta:F=>G` and
`f:x->y`, the arrow `eta[f]:F(x)->G(y)`. Adjacent functor
actions accumulate into this term by strict naturality. See
[Chapter 9](#chapter-9).

<a id="glossary-omega-equivalence"></a>

**Omega-equivalence.** The native recursive equality-valued equivalence
interface for categorical cells. It is distinct from a bare carrier
`TypeEquiv` and from ordinary isomorphism evidence. See
[Chapter 4](#chapter-4).

<a id="glossary-path-category"></a>

**Path category.** `Path(A)`, the equality-local groupoidal category on
a classifier `A`. It embeds ordinary identity reasoning into the directed
calculus without identifying every directed hom with equality. See
[Chapter 2](#chapter-2).

<a id="glossary-pathout"></a>

**PathOut.** The outgoing-arrow category
`sum_(y:Z) Hom_Z(x,y)` at a fixed source `x`. Its canonical arrow
from `(x,id_x)` to `(y,p)` drives arrow induction. See
[Chapter 5](#chapter-5).

<a id="glossary-profunctor"></a>

**Profunctor.** A Cat-valued functor `A^op times B -> Cat`, contravariant
in its first endpoint and covariant in its second. See
[Chapter 13](#chapter-13).

<a id="glossary-representable"></a>

**Representable.** A family or profunctor obtained from an ambient hom. Its
action is composition, which makes it the computational bridge between
universal properties and cut elimination. See
[Chapters 5](#chapter-5) and [13](#chapter-13).

<a id="glossary-rewrite"></a>

**Runtime rewrite.** A directed reduction selecting an intended normal form.
It is distinct from proof-time unification and internal propositional
equality. See [Appendix E](#appendix-computation).

<a id="glossary-transfor"></a>

**Transfor.** An arrow in a functor category, generalizing a natural
transformation and continuing to higher hom levels. See
[Chapter 9](#chapter-9).

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

<a id="glossary-walkingend"></a>

**WalkingEnd.** The opaque one-dimensional directed HIT/category with a base
object and a directed generating endomorphism. See
[Chapters 6](#chapter-6) and [8](#chapter-8).

## D.2 Index strategy

The initial edition uses this linked concept index as its stable index. Terms
are curated rather than extracted from raw identifier frequency; synonyms
point to one canonical entry, and every destination is an explicit HTML
anchor checked by the source gate.

Page numbers are deliberately absent from the source because they depend on
the renderer, paper size, and font metrics. A later release tool may resolve
these anchors to PDF page labels, but the anchor remains the authority. New
index entries should be added when a concept is defined or changes status,
not for every occurrence of its implementation name.
