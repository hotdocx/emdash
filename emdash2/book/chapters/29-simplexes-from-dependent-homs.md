<a id="chapter-29"></a>

# 29. Simplexes From Dependent Homs

A directed edge has two vertices and one arrow. A directed triangle adds three
edges and a comparison between a composite edge and a direct one. A
tetrahedron adds four triangles and a cell relating their comparison data. The
pattern continues, but its usual description becomes increasingly
combinatorial: every new dimension carries many faces, and those faces must
agree on all of their shared lower faces.

Functorial type theory offers another description. Begin with a category
$C$. Choose an object, then an outgoing arrow, then an outgoing arrow in the
category of outgoing arrows, and continue. Each new choice is made in a
category whose objects already contain the entire previous boundary. Its
arrows contain a base arrow together with a dependent arrow above transport.
The next hom action therefore supplies the next coherence without asking for
a separately written coherence record.

This chapter relates that native dependent presentation to the familiar
combinatorics of standard simplexes. Injective monotone maps give a computing
category of faces. Directed joins give the finite ordinal categories
$\Delta[n]$. Representables give standard semisimplices. Iterated outgoing
paths give the native dependent cells. Finally, a structural recursion builds
one canonical dependent simplex inside every $\Delta[n]$ and maps it along
every functor $\Delta[n]\to C$.

The result is deliberately semisimplicial: faces are present, degeneracies are
not. It is also deliberately weaker than a categorical normal-form theorem.
The construction computes one canonical simplex and all of its nonempty face
observations in variable dimension; it does not yet identify the whole
mapping category $\operatorname{Functor}(\Delta[n],C)$ with a whole category
of dependent simplexes.

## 29.1 The Shape Before The Coordinates

Write $\Delta[n]$ for the finite ordinal category

$$
0\longrightarrow 1\longrightarrow\cdots\longrightarrow n,
\tag{29.1}
$$

including the unique composite arrow $i\to j$ whenever $i\leq j$. A functor
$H:\Delta[n]\to C$ is the conventional categorical presentation of an
$n$-simplex in $C$. At dimension two it selects three vertices, the three
arrows

$$
p_{01}:x_0\to x_1,
\qquad
p_{12}:x_1\to x_2,
\qquad
p_{02}:x_0\to x_2,
\tag{29.2}
$$

and whatever comparison is selected by the functorial profile between
$p_{12}\circ p_{01}$ and $p_{02}$. At dimension three, the four restrictions
of $H$ to three vertices are its triangular faces.

There are already three distinct notions in this paragraph.

- The category $\Delta[n]$ is the *ordinal shape*.
- The representable $\operatorname{Hom}(-,[n])$ on the category of injective
  ordinal maps is the *standard semisimplex*.
- The data obtained by repeatedly entering an outgoing-path category is the
  *dependent simplex*.

The first is a finite source category. The second records how all smaller
faces enter that source. The third is a native normal form for the data seen
inside a target. The value of the construction below is not that these three
expressions can be printed. It is that their face and higher-cell operations
are owned by functors already present in the theory.

The ordinal shapes themselves grow by directed join:

$$
\Delta[0]\equiv\mathbf 1,
\qquad
\Delta[n+1]\equiv\Delta[n]\star\mathbf 1.
\tag{29.3}
$$

The new terminal vertex receives one arrow from every old vertex. Thus
joining with $\mathbf 1$ adds exactly the new final vertex and all arrows that
point toward it. The construction is directed: it does not add inverse arrows
from the new vertex back into the old ordinal.

## 29.2 Faces Form A Computing Category

Use the augmented cardinal convention. The natural number $m$ represents the
finite ordinal with $m$ vertices, so zero is the empty ordinal, one is a
vertex, two is an edge, and three is a triangle. An injective monotone map from
the $p$-vertex ordinal to the $n$-vertex ordinal can be encoded by a word of
length $n$: at each target position, either skip that position or keep it.

The structural constructors have the form

$$
\begin{aligned}
\mathsf{skip}&:\mathsf{Face}(p,n)
  \longrightarrow\mathsf{Face}(p,n+1),\\
\mathsf{keep}&:\mathsf{Face}(p,n)
  \longrightarrow\mathsf{Face}(p+1,n+1).
\end{aligned}
\tag{29.4}
$$

The all-keep word is identity. Composition substitutes one word into the kept
positions of another. Its four skip/keep cases are ordinary structural
recursion, so closed faces compute rather than requiring a theorem for every
pair of dimensions.

These codes are classified as sets before becoming public face maps. The
classification removes unwanted higher ambiguity in the combinatorial index,
while restricted recursion preserves computation on visible constructors.
They form the homs of the internal augmented semi-simplex category
$\Delta_+^{\mathrm{inj}}$:

$$
\operatorname{Obj}(\Delta_+^{\mathrm{inj}})=\mathbb N,
\qquad
\operatorname{Hom}(p,n)=\mathsf{Path}(\mathsf{Face}(p,n)).
\tag{29.5}
$$

Identity and composition are the identity and composition of face codes. The
homs are locally discrete, but the enclosing category remains an ordinary
internal category, so functors and transfors on it use the generic iterable
action calculus.

The standard $n$-simplex is now Yoneda:

$$
\boldsymbol\Delta[n]
  :=\operatorname{Hom}_{\Delta_+^{\mathrm{inj}}}(-,n+1).
\tag{29.6}
$$

The shift by one converts from dimension to vertex count. Evaluating
$\boldsymbol\Delta[n]$ at a $p$-vertex ordinal returns the code of a
$p$-vertex face of $[n]$. Restriction is composition of face codes. A
groupoid-valued semisimplicial diagram is consequently a functor

$$
X:(\Delta_+^{\mathrm{inj}})^{\mathrm{op}}\longrightarrow\mathbf{Grpd},
\tag{29.7}
$$

and postcomposition with the path-category operation realizes all its levels
and face maps as a Cat-valued presheaf. Because realization is one whole
postcomposition functor, arrows between diagrams and their higher action are
retained as well.

<!-- evidence:SEMISIMPLICIAL-FACE-SUBSTRATE -->

> **Formal status — checked.** Evidence
> `SEMISIMPLICIAL-FACE-SUBSTRATE`. Skip/keep face codes, their composition,
> the augmented injective index category, join-built ordinal shapes, Yoneda
> standard semisimplices, and whole groupoid-to-Cat diagram realization are
> active. No degeneracy maps or full simplex category are asserted.

## 29.3 A Simplex Is An Iterated Outgoing Path

The combinatorial index says which face is selected. It does not yet explain
why a higher simplex should have the right dependent boundary. That
explanation begins with the outgoing-arrow category from Chapter 5:

$$
\operatorname{PathOut}_C(x)
  =\sum_{y:C}\operatorname{Hom}_C(x,y).
\tag{29.8}
$$

An object is an endpoint $y$ and an arrow $p:x\to y$. An arrow between
$(y,p)$ and $(z,q)$ contains an arrow $r:y\to z$ together with a cell from
$r\circ p$ to $q$. Thus one step into `PathOut` adds a vertex, the edge from
the fixed source, and the comparison that makes the resulting triangle
coherent.

This observation can be iterated. Put

$$
S_0(C):=C.
\tag{29.9}
$$

After choosing a flag $s_k\in\operatorname{Obj}(S_k)$, define

$$
S_{k+1}(C;s_0,\ldots,s_k)
  :=\operatorname{PathOut}_{S_k}(s_k).
\tag{29.10}
$$

A zero-simplex is an object $x_0$ of $C$. A one-simplex is an object
$e_{01}=(x_1,p_{01})$ of $\operatorname{PathOut}_C(x_0)$. A two-simplex is
an object $t_{012}$ of
$\operatorname{PathOut}_{\operatorname{PathOut}_C(x_0)}(e_{01})$.
Unpacked readably, it contains an edge $p_{02}$ and an arrow from $e_{01}$ to
$e_{02}$; the latter contains $p_{12}$ and a two-cell

$$
\alpha_{012}:p_{12}\circ p_{01}\Longrightarrow p_{02}.
\tag{29.11}
$$

No triangle record has been introduced. Equation (29.11) is the dependent
fibre component of an arrow in a Sigma total.

The generic calculation is worth stating. Let $E$ be a Cat-valued family on
$K$, and consider total objects $(x,u)$ and $(y,v)$. Their hom in the total
category has the native presentation

$$
\operatorname{Hom}_{\sum E}((x,u),(y,v))
  \simeq
  \sum_{p:x\to y}
    \operatorname{Hom}_{E(y)}(E[p](u),v).
\tag{29.12}
$$

The second factor is precisely a dependent hom. Specializing $E$ to the
representable family $\operatorname{Hom}_C(x_0,-)$ gives (29.11). Nesting
this hom slice beneath the next outgoing-path Sigma gives tetrahedra, then
higher simplexes. The recursion is therefore semantic before it is coded:
every stage is built from the existing `Hom`, dependent `Sigma`, and
dependent-hom owners.

With both total endpoints fixed, (29.12) projects $(p,\alpha)$ to $p$ and,
through covariant fibre action, to $E[p](u)$ in the already fixed fibre
$E(y)$. The latter is internal transport, not the independently varying
simplex target supplied by the outer `PathOut` Sigma in (29.8).

## 29.4 Why A Tetrahedron Has Four Surfaces

An ordinary globular arrow has two endpoints, whereas a tetrahedron has four
faces. The recursive triangle category supplies the difference through two
nested fibrations.

Write

$$
S_1=\operatorname{PathOut}_C(x_0),
\qquad
S_2=\operatorname{PathOut}_{S_1}(e_{01}).
$$

For a visible $e_{01}=(x_1,p_{01})$, a triangle in $S_2$ has the nested form

$$
t_{012}=(e_{02},q_{012}),
\qquad
e_{02}=(x_2,p_{02}),
\qquad
q_{012}=(p_{12},\alpha_{012}).
$$

The outer pair remembers the target edge $e_{02}$. The inner Hom-of-Sigma pair
remembers the base edge $e_{12}=(x_2,p_{12})$ and comparison $\alpha_{012}$.

Now take two triangles $t_{012},t_{013}\in S_2$. An arrow

$$
\Theta:t_{012}\longrightarrow t_{013}
\tag{29.13}
$$

is the volume of the tetrahedron $0123$. Its ordinary source and target are
the faces $012$ and $013$. Two whole line projections provide the remaining
faces:

$$
\begin{aligned}
d_{02}(t_{01i})&=e_{0i},
&d_{02}[\Theta]&=t_{023},\\
d_{12}(t_{01i})&=e_{1i},
&d_{12}[\Theta]&=t_{123}.
\end{aligned}
$$

The first is the target projection of the outer `PathOut` Sigma. The second
uses the base-arrow projection of the inner Hom-of-Sigma, whose dependent
fibre is organized by `homd_int`. Pairing them gives one whole boundary
functor. Their shared vertices and edges are consequently preserved by
ordinary functor action rather than imposed by a hand-written boundary
equation.

An ordinary functor $F:C\to D$ maps the whole recursive triangle category by
iterated `PathOut` action. Within its fixed-endpoint Hom-of-Sigma slice, the
displayed part is mapped by the existing internal dependent action: the base
cell is retained while the fibre cell is sent through the next displayed hom
action. Applying the hom action once more remains meaningful. This is the same
iteration that produced the laxity witness of Chapter 28; here its geometric
reading is a higher simplex.

<!-- evidence:DEPENDENT-SIMPLEX-INTERNAL-ACTION -->

> **Formal status — checked.** Evidence
> `DEPENDENT-SIMPLEX-INTERNAL-ACTION`. The fixed-endpoint dependent hom is the
> active hom of a Sigma total and retains its base/transport observations. The
> recursive `PathOut` triangle category has whole target-line and base-line
> projections whose hom actions expose faces $023$ and $123$. A visible
> tetrahedral constructor computes through the existing displayed internal
> action, and one further hom action is retained. No standalone tetrahedron
> filler or coherence record is added.

## 29.5 Codes Without A Second Semantics

Equations (29.9)-(29.10) are dependent in a strong sense: the category at the
next stage depends on the previously selected object. Ordinary recursion into
a fixed codomain cannot store that changing type directly. An internal code
is useful here, but only if it remembers the native category rather than
interpreting a parallel syntax of cells.

The intrinsic code has two constructors. Its zero case is indexed by $C$.
Its successor stores an existing code indexed by $K$ and a flag
$x\in\operatorname{Obj}(K)$, and is indexed by
$\operatorname{PathOut}_K(x)$. Schematically,

$$
\begin{aligned}
\mathsf{zero}_C
  &: \mathsf{Code}(C,0;C),\\
\mathsf{step}(c,x)
  &: \mathsf{Code}(C,n+1;\operatorname{PathOut}_K(x))
     \quad(c:\mathsf{Code}(C,n;K)).
\end{aligned}
\tag{29.14}
$$

The semicolon records the already-decoded category. Public code packaging may
hide $K$, but decoding merely projects that index. It does not traverse a
syntax tree and rebuild `Hom`, `Sigma`, or `PathOut`. This makes the code an
internal witness to the changing boundary, not a second definition of what a
simplex means.

Faces recurse simultaneously on the flagged code and the skip/keep word.
There are three structural situations.

1. Skipping the newest vertex selects a face of the fixed flag and returns a
   constant whole functor.
2. Keeping the newest vertex after skipping its predecessor selects the
   corresponding face through the first projection of `PathOut`.
3. Keeping both newest vertices maps the whole outgoing path by the recursively
   selected lower face functor.

The third case is where higher action matters: a face is not only a function
on stored points, but a functor on the outgoing-path category. The result
retains its own hom action. Direct and sequential face presentations are not
globally collapsed to one judgmental normal form; the structural recursion
provides the selected whole observation.

## 29.6 The Ordinal Source Grows By A Transformation

The code recursion describes arbitrary flags. To compare it with the standard
ordinal, one needs a canonical flag in every $\Delta[n]$. The directed join
equation (29.3) supplies the first step. Extend the identity of the old
ordinal across
$\Delta[n]\star\mathbf 1$. The old observed outgoing-path map and the
primitive join outgoing-path map are related by one whole transformation.

Suppose a nonzero stage has already produced:

$$
d,\qquad F,G:K\longrightarrow B,
\qquad\epsilon:F\Longrightarrow G.
\tag{29.15}
$$

For a selected old source $s\in\operatorname{Obj}(K)$, the new code and source
are

$$
d':=\mathsf{step}(d,F(s)),
\qquad
s':=(G(s),\epsilon_s).
\tag{29.16}
$$

The second expression is an object of
$\operatorname{PathOut}_B(F(s))$: its endpoint is $G(s)$ and its outgoing
arrow is the component of the whole transformation. For the next flag, lift
$\epsilon$ through `PathOut`. The lift is again a whole transformation, so its
component supplies the next cell and its hom action remains available.

The first stage uses the identity-join comparison. Every later stage repeats
the same `PathOut` lift. This makes (29.16) a structural successor, not a table
with separate clauses for triangles, tetrahedra, and four-simplexes.

## 29.7 The Four-Simplex As A Decisive Finite Test

Dimension four is the first compact test that combines the recursive source,
a genuinely higher component, every coface, arbitrary target mapping, and a
retained next action. Beginning with the canonical source edge and triangle,
the join comparison is lifted three times:

$$
\begin{aligned}
\epsilon_1&:=\text{identity-join outgoing-path comparison},\\
\epsilon_2&:=\operatorname{PathOutLift}(\epsilon_1,e_{01}),\\
\epsilon_3&:=\operatorname{PathOutLift}(\epsilon_2,t_{012}),\\
\omega_{01234}&:=(\epsilon_3)_{s_{0123}}.
\end{aligned}
\tag{29.17}
$$

The component $\omega_{01234}$ is the fourth-level cell. Pairing it with its
endpoint constructs an object of the existing native four-simplex classifier;
it is not supplied as an opaque filler.

For every functor

$$
H:\Delta[4]\longrightarrow C,
\tag{29.18}
$$

the existing mapped-code action sends this single source to a dependent
four-simplex in $C$. The five skip-one-vertex codes expose its tetrahedral
faces

$$
0123,\qquad 0124,\qquad 0134,\qquad 0234,\qquad 1234.
\tag{29.19}
$$

Native Sigma projections separately expose the source, target, base
tetrahedron, and readable dependent top component. These two views have the
same intended geometry, but they retain different construction histories.
The development does not force every code-selected face to be judgmentally
equal to every native projection.

The same construction is checked for an arbitrary target category, a selected
computationally strict target map, and an exact path-category target. A wrong
recursive source is rejected, the top cell is not identified with an
arbitrary replacement, and the next action of $\epsilon_3$ remains available.

<!-- evidence:ORDINAL-DEPENDENT-FOUR-SIMPLEX -->

> **Formal status — checked.** Evidence
> `ORDINAL-DEPENDENT-FOUR-SIMPLEX`. One canonical four-simplex is constructed
> from the generic join comparison and repeated whole `PathOut` lift. It maps
> under every $H:\Delta[4]\to C$, exposes all five cofaces, passes strict and
> path-valued profile checks, remains noncollapsed, and retains one higher
> action.

## 29.8 The Variable-Dimensional Theorem

The finite calculation is not the definition. It validates the structural
successor that Nat recursion can iterate. Let

$$
\mathsf{Obs}(C,n)
  :=\sum_{c:\mathsf{DependentSimplexCode}(C,n)}
      \operatorname{Obj}(\operatorname{decode}(c)).
\tag{29.20}
$$

This is the present object package called `DependentSimplexObservation`. It
contains both the intrinsic boundary code and one object of its native decoded
category.

<!-- evidence:ORDINAL-DEPENDENT-SIMPLEX-RECURSION -->

> **Formal status — checked.** **Theorem 29.1 (the variable-dimensional ordinal
> dependent simplex).** Evidence `ORDINAL-DEPENDENT-SIMPLEX-RECURSION`. For
> every natural number $n$ there is a canonical
> $s_n\in\mathsf{Obs}(\Delta[n],n)$ computed by Nat recursion and the
> structural successor (29.16). Every $H:\Delta[n]\to C$ induces a canonical
> observation $H_*(s_n)\in\mathsf{Obs}(C,n)$. Every nonempty injective face
> code has a whole face observation. Base and successor computations,
> selected source objects through dimensions zero to four, wrong-index
> rejection, noncollapse of the successor cell, and one generic next action
> are checked.

The theorem is uniform in $n$, but its validation claim is deliberately
finite where readability matters. The source and successor are genuinely
variable-dimensional; the explicit zero-through-four checks show that the
recursor reaches the existing native classifiers and the expected finite
geometry. They are not an induction theorem identifying the new source
judgmentally with every earlier hand-written presentation.

The theorem also separates construction from observation. The canonical
source lives once in $\Delta[n]$. Mapping it by $H$ uses the generic mapped
decoder; it does not reconstruct the source in $C$. Face restriction then
uses the generic code action. Thus source recursion, target mapping, and face
selection are three composable whole operations.

## 29.9 Comparison With Other Recursive Presentations

Semisimplicial types are a well-known stress test for dependent type theory.
The boundary of an $(n+1)$-simplex depends on all lower dimensions, and the
coherence needed at the next stage depends on that boundary. Different
approaches make different parts of this dependency primitive.

Kolomatskaia and Shulman's displayed type theory presents semisimplicial types
through a compact displayed or cone interface
[12](#ref-kolomatskaia-shulman-sst). Herbelin and Ramachandra reconstruct the
frame, restriction, and coherence dependencies through iterated parametricity,
first for semisimplicial and semicubical sets and then in an indexed very
dependent formulation
[13](#ref-herbelin-ramachandra-parametricity),
[14](#ref-herbelin-ramachandra-very-dependent). These comparisons clarify why
neither an ordinary fixed-codomain Nat recursor nor a flat record of faces is
sufficient.

The emdash construction chooses another ownership boundary. Categories and
category-valued families are already internal types. `PathOut` is already a
Sigma of a representable. A hom in that Sigma already exposes a dependent
hom. Whole functor and transfor action already iterate. The semantic simplex
is therefore built from these owners directly. The code layer is introduced
only to internalize the changing native category in variable dimension.

This does not make the external combinatorics disappear. Face codes remain
the clean way to name arbitrary restrictions, and the semi-simplex category
organizes them globally. Nor does it prove that every other presentation is
equivalent. It shows a computational bridge at a precise point: the same
simplex can be observed combinatorially by injective faces and natively as an
iterated dependent outgoing path.

## 29.10 The Whole Mapping-Category Boundary

The strongest tempting statement is

$$
\operatorname{Functor}_{\mathrm{cat}}(\Delta[n],C)
\simeq
\mathsf{DependentSimplex}_{\mathrm{cat}}(C,n).
\tag{29.21}
$$

Equation (29.21) is not yet a theorem. Its right side is intentionally written
with a future name. The active `DependentSimplexObservation(C,n)` in (29.20)
is a groupoid-valued object total; it is not a whole category with the arrows
and higher cells required by (29.21).

Constructing the right side requires a category whose objects recover
(29.20), whose homs express compatible transformations of all dependent
frames, and whose higher action agrees with the native internal-action tower.
One must then construct comparison functors in both directions, whole beta and
eta witnesses, and compatibility with face action. An objectwise decoding
function, even one that computes in every dimension, is not that equivalence.

The other major absent operation is degeneracy. The current index has
injective monotone maps only. Adding surjections would require a computational
account of repeated vertices and identity cells compatible with the dependent
recursion. No degeneracy law is inferred merely because each ambient category
has identities.

Consequently this chapter does not claim a full simplicial object, arbitrary
horn fillers, a Kan complex, a Segal or Rezk theorem, complicial structure, or
a comparison with Street orientals. The existing two-dimensional path-groupoid
horn fillers are bounded consumers, not a general consequence of Theorem
29.1.

## 29.11 The End Of The Fifth Spiral

The earlier chapters moved repeatedly between points and arrows, local data
and whole action, directed cells and paths. Simplexes make that movement
recursive. A point becomes an outgoing arrow. An outgoing arrow becomes an
arrow between outgoing arrows. The base and fibre of that arrow become two
faces of the next cell. Its whole image supplies another face. Repeating the
same construction raises the dimension without changing foundations.

The combinatorial and dependent views play complementary roles. Face words
say which vertices survive. Yoneda packages all such restrictions into the
standard semisimplex. Directed join constructs the ordinal source. Dependent
hom and Sigma explain the cell above its boundary. Whole transformation action
constructs the successor. The code merely remembers which native category the
next step inhabits.

This is the computational lesson of Theorem 29.1. Higher-dimensional data need
not be introduced as an ever-growing list of coherence fields when the theory
already knows how a dependent arrow acts. The retained action is the resource
from which the next dimension is observed.

The lesson is also a boundary. Constructing one canonical simplex in every
dimension is not the same as classifying all simplexes. Faces are not
degeneracies. A semisimplicial substrate is not a Kan or Segal theory. By
keeping those differences visible, the checked recursion can serve as a
foundation for later simplicial methods without being mistaken for their
completion.
