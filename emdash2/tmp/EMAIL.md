LONGER TECHNICAL APPENDIX
=========================

Functorial Type Theory in emdash v3.2

Abstract. Functorial Type Theory asks what happens when the substitutional
discipline of dependent type theory is extended to genuinely categorical
variables: objects may vary along arrows, families carry directed transport,
and functoriality and naturality are internal operations that may compute
rather than external proof obligations. The emdash v3.2 research artifact
develops this idea in an outer dependent logical framework and an inner
directed dependent theory of categories, Cat-valued families, Sigma totals,
sections, dependent homs, functors, transfors, profunctors, and selected
universal constructions.

Five mathematical threads expose the architecture. Directed arrow induction
transports reflexive data along a canonical Sigma arrow and computes ordinary
composition. A directed higher-inductive walking endomorphism is normalized
to the natural-number powers of its generator. In local geometry, the locus
where a section becomes invertible is constructed first as a sieve D_U(s),
before one asks whether an open represents it; finite localization charts
then generate a Zariski topology, while a direct return/glue/silent
categorical HIT constructs fixed-site Cat-valued sheafification. Returning to
the groupoidal layer, a Circle/Integer encode-decode theorem restores inverse
powers, category-indexed groupoidification characterizes maps out by a whole
mapping equivalence, and one profiled Gray right closure exposes a nonidentity
walking-square interchanger from the same internal laxity action.
Finally, injective face codes form an internal semi-simplex category, directed
join builds the ordinal shapes `Delta[n]`, and iterated outgoing paths build
their native dependent cells. One Nat recursion constructs a canonical
ordinal source in variable dimension, maps it into arbitrary target
categories, exposes every nonempty face, and retains another higher action;
selected computations are checked through dimension four.

The same distinction between readable syntax and explicit structure appears
in the implementation. A TypeScript elaborator accepts usual binder-and-
variable notation for a reviewed ordinary/natural/displayed fragment and
lowers it to backend-neutral explicit emdash Core. The Core is checked and
evaluated by a small TypeScript dependent-LF kernel; selected judgments can
also be emitted deterministically to the authoritative Lambdapi/emdash
development. Thus the two logical-framework realizations share an explicit
categorical boundary without pretending that the complete Lambdapi library
has already been transferred. A client-side reviewer exposes representative
source, explicit Core, inferred type, computation, and rejection evidence
without requiring a production Lambdapi process in the browser.

Book: https://doi.org/10.5281/zenodo.21544186


Directed dependent hom and arrow induction
-------------------------------------------

For a category-valued family

```
E : K ⊢ Cat
```

where `⊢` denotes a functor category, and fixed data `x : K`, `u : E[x]`,
emdash forms the directed dependent hom

```
homd_E(x,u)
  : Π(y : K^op), E[y^-] ⊢_[y] (Hom_K(x,y)^op ⊢ Cat).
```

Here `⊢_[y]` is the mixed-variance displayed form of `⊢`, and `y^-`
records that the `E`-argument is contravariant. At `y`, `v : E[y]`, and
`f : x → y`, its value is

```
Hom_{E[y]}(E[f](u),v).
```

This dependent hom organizes the arrows of the Sigma total:

```
Hom_{ΣE}((x,u),(y,v))
  = Σ(f : x → y), Hom_{E[y]}(E[f](u),v).
```

Fix a category `Z` and `x : Z`. The outgoing-arrow category is

```
PathOut_Z(x) = x ↓ Z = Σ(y : Z), Hom_Z(x,y).
```

Its objects are `(y,p)` with `p : x → y`. In the ordinary coslice,
`(x,id_x)` is initial. The canonical arrow to `(y,p)` is not literally the
base arrow `p`: it is the Sigma arrow whose base component is `p` and whose
fibre component is an identity. More precisely,

```
ρ_{x,y,p}
  := σ_transport_arrow(Rep_Z(x),p,id_x)
   = σ_arrow(p,id_p)
  : (x,id_x) → (y,p),
```

where the second presentation uses the endpoint computation

```
Rep_Z(x)[p](id_x) = p ∘ id_x = p.
```

Thus `id_p` is an arrow in the transported fibre, and `p` is the first
component of the total arrow `ρ`.

For a motive and reflexive datum

```
E : PathOut_Z(x) ⊢ Cat
u : E[(x,id_x)],
```

fixed-source arrow induction is the section

```
Ind_x(E,u) : Π(a : PathOut_Z(x)), E[a]

Ind_x(E,u)(y,p) = E[ρ_{x,y,p}](u).
```

This resembles path induction but assumes no inverse for `p`. It extends
data at the reflexive outgoing arrow along a directed total arrow.

For the composition motive

```
E[(y,p)] := Rep_Z(y) ⊢ Rep_Z(x)
```

and initial datum `id : Rep_Z(x) ⊢ Rep_Z(x)`, evaluation gives ordinary
composition. For `p : x → y` and `q : y → z`,

```
Ind_x(E,id)[(y,p)][z][q] ↝ q ∘ p.
```

The runtime normal form is the represented-hom cut `(q)_*(p)`; ordinary
composition is its typed mathematical presentation. The calculation is not a
special rewrite attached to a theorem name: it passes through motive
transport along `ρ`, representable action, and generic hom action.

The source object may itself vary. An arrow `r : x → y` induces

```
r^* : (y ↓ Z) ⊢ (x ↓ Z)
r^*(z,q) = (z,q ∘ r).
```

Consequently the section-taking target varies by pullback:

```
Π(a : x ↓ Z), E(a)
  ⊢
Π(b : y ↓ Z), E(r^*(b)),

s ↦ (b ↦ s(r^*(b))).
```

The source-indexed induction theorem is therefore one displayed
transformation. Its naturality is internal to that transformation rather
than supplied as a family of external squares.

The notation is also executable. The current frontend accepts, for example,

```
λ^f  x. (H x) (K x)
λ^nd k : K. composeCells (theta k) (eta k)
```

with `^f`, `^n`, `^fd`, and `^nd` marking functorial, natural,
displayed-functorial, and displayed-natural binding. Variable occurrences are
recursively factored through identity, weakening, pairing, evaluation,
reindexing, totalization, and internal action. The resulting explicit Core
can be checked directly by TypeScript/emdash and, for the reviewed profile,
emitted to Lambdapi/emdash for conformance. Unsupported variance or escaped
variables are rejected rather than assigned an invented coherence law.


A directed HIT and its normalization
------------------------------------

The first concrete directed higher-inductive calculation declares a global,
opaque, one-dimensional walking endomorphism rather than defining its hom as
a word type or as the natural numbers:

```
constant WalkingEnd : Cat

base : Obj(WalkingEnd)
loop : Hom_WalkingEnd(base,base).
```

Apply the whole-HIT recursor to the category universe, choosing the
equality-local category `ℕ` at the base and successor on the loop:

```
Code := rec_WalkingEnd(Cat_cat; ℕ, Succ)

Code[base] = ℕ
Code[loop] = Succ : ℕ ⊢ ℕ.
```

Every based arrow acts through `Code`, so its action on zero defines

```
encode_x(p) = Code[p](0).
```

The inverse is not obtained by inspecting `p` as a word. Define forward
powers and the based representable family:

```
power(0)   = id_base
power(n+1) = loop ∘ power(n)

Rep_base[x] = Hom_WalkingEnd(base,x).
```

The loop action and successor are related by the spiral transformation

```
spiral : Rep_base[loop] ∘ power ⇒ power ∘ Succ.
```

The contextual displayed eliminator then produces one coherent decoder over
all endpoints:

```
decodeᵈ := indᵈ_WalkingEnd(Code,Rep_base,power,spiral)

decode_x : Obj(Code[x]) → Hom_WalkingEnd(base,x)
decode_base = power

norm_p : p → decode_x(encode_x(p))
         inside Hom_WalkingEnd(base,x).
```

Only after this directed normalization cell is constructed does
one-dimensionality turn it into equality. At the base,

```
power(encode_base(p)) = p
encode_base(power(n)) = n

Hom_WalkingEnd(base,base) ≃ ℕ
    (equivalence of underlying carriers).
```

The answer is `ℕ`, not `ℤ`, because direction matters: `loop` has no right
inverse. The equivalence follows from whole-HIT elimination and its base/loop
computations; `ℕ` was not installed as the hom by definition.

At the next hom level, the Eckmann–Hilton calculation concerns
2-endomorphisms of an identity 1-cell:

```
2End_B(x) = Hom_{Hom_B(x,x)}(id_x,id_x)

α,β : 2End_B(x)
β · α = β * α = α · β.
```

Here `·` is vertical composition and `*` is horizontal composition derived
from whiskering. Their common unit and interchange identify the two products
and force commutativity.


Groupoidal realization and a directed Gray interchanger
--------------------------------------------------------

The path category places equality inside the same iterable categorical
interface. For a groupoidal classifier `A`,

```
Obj(Path(A))       = A
Hom_Path(A)(x,y)   = (x = y).
```

This is not groupoidification: `Path(A)` exposes equality already present in
`A`, whereas groupoidification freely realizes directed arrows as paths. A
representative closure theorem makes the distinction computationally useful:

```
Path(A × B) → Path(A) × Path(B)
```

is the identity on objects and an equivalence on every hom. For a dependent
family over `A × B`, direct transport along a paired path agrees with transport
first in either coordinate; the two comparisons form a coherent diamond.

The Circle is an opaque groupoidal HIT rather than a quotient of WalkingEnd:

```
Circle : Grpd
base   : Circle
loop   : base = base.
```

Its dependent eliminator computes both at the point and at the dependent
action on the loop:

```
circle_ind(D,b,ell)(base)       ↝ b
apd(circle_ind(D,b,ell),loop)   ↝ ell.
```

The ordinary constant-family `ap` equation remains propositional, so there is
one selected higher-constructor computation rather than two competing normal
forms. Localizing natural-number successor to an equivalence gives the
Integer classifier. Circle monodromy is successor, and universal-cover
encode/decode yields

```
Hom_Circle(base,base) ≃ ℤ.
```

The comparison `WalkingEnd → Path(Circle)` sends `loop^n` to the nonnegative
Circle power. More generally, every directed category `C` has a groupoidal
realization with one whole unit

```
Groupoidify(C) : Grpd
η_C : C → Path(Groupoidify(C)).
```

For every groupoid `G`, restriction along `η_C` and whole extension are inverse
at the level of mapping categories:

```
Hom_Grpd(Groupoidify(C),G)
  ≃_ω Functor(C,Path(G)).
```

The recursor computes on represented points and on dependent action over every
represented source arrow; beta and eta are paths between whole functors, so
higher action is retained. Specializing `C` to the two-ended WalkingArrow
recovers the independently presented groupoidal Interval up to equivalence.
This is the target-side universal property. Source action
`Groupoidify(H)`, the whole `Groupoidify_func`, and the packaged adjunction
with `Path` remain future interfaces.

The same internal-action calculus keeps directed laxity visible. Its functor
compositor is a cell

```
φ^F_{g,f} : F[g] ∘ F[f] ⇒ F[g ∘ f].
```

In a path target this cell is invertible; at a decoded computationally strict
functor code it reduces to identity; in a general directed target it need not
be invertible. The selected strict-object/lax-arrow profile reuses the ambient
transfor and higher-hom tower:

```
GrayHom_lax(A,B)

GrayHom_lax(A ⊗_R B,C)
  ≃_ω GrayHom_lax(A,GrayHom_lax(B,C)).
```

Coevaluation at two walking arrows produces four vertices and two boundary
routes. Projecting the existing whole laxity action gives the oriented,
nonidentity interchanger

```
χ : a₁ ∘ b₀ ⇒ b₁ ∘ a₀,
```

with one next hom action still available. This is one checked profiled right
closure and a low-dimensional coherence stress test. It is not the mirror
closure, tensor functoriality/coherence, a full Crans–Gray biclosed monoidal
structure, or a global migration of the prototype's historical strict cuts.


Simplexes from dependent homs
------------------------------

The combinatorial and dependent descriptions of a simplex are both internal.
In the augmented convention, an injective ordinal map is a skip/keep code

```
Face(p,n),
```

whose identity and composition compute structurally. These codes form the
locally discrete homs of the augmented semi-simplex category. Yoneda gives the
standard representable semisimplex, while directed join gives the ordinal
source shapes

```
Delta[0]   = 1
Delta[n+1] = Delta[n] * 1.
```

The native cell presentation uses no second simplex record. Put `S_0(C)=C`;
after selecting `s_k : Obj(S_k)`, define

```
S_{k+1} = PathOut_{S_k}(s_k).
```

Because `PathOut` is a Sigma of a representable hom, its arrows pair a base
cell with a dependent cell above transport. At dimension two this contains
`p12 o p01 => p02`. At dimension three, ordinary source and target plus the
whole base and endpoint-action projections give the four tetrahedral faces,
and the next internal action remains available.

An intrinsically indexed flag code records the changing native category
without reimplementing it. A whole stage

```
F,G : K -> B
epsilon : F => G
```

sends an old source `s` to

```
code'   = step(code,F[s])
source' = (G[s],epsilon[s]).
```

The first stage is induced by identity extension across the ordinal join;
later stages lift `epsilon` through `PathOut`. Nat recursion therefore
constructs a canonical source for variable `n`. Mapping it under arbitrary
`H : Functor(Delta[n],C)` and restricting it by the existing nonempty
`FaceCode` action are whole operations. Dimensions zero through four, all
five tetrahedral faces of the four-simplex, noncollapse, and a retained next
action are checked.

The current `DependentSimplexObservation(C,n)` packages objects, not a whole
category of all dependent simplexes. Degeneracies and the whole equivalence

```
Functor_cat(Delta[n],C) ~= DependentSimplex_cat(C,n)
```

remain explicit next steps, as do general Kan, Segal, and Rezk structure.


Profunctors, weighted universals, and duality
---------------------------------------------

A Cat-valued profunctor is represented as a directed family

```
Prof(A,B) = A^op × B ⊢ Cat.
```

The checked calculus contains representables `Hom(F ~,G —)`, endpoint
reindexing, shaped profunctor cells, a selected symbolic tensor `⊗`,
co-Yoneda maps, and covariant and contravariant internal homs with
evaluation/lambda cancellation. Weighted limits are expressed by
representability rather than by a separately copied cone calculus:

```
WeightedLimit_cov(F,W,L)
  = ProfComparison(
      Prof_imply_cov(Hom(~,F _),W(—,_)),
      Hom(~,L —)).
```

For an adjunction `S ⊣ R`, right-adjoint preservation of a selected weighted
limit is assembled from an inverse adjunction mate, reindexing of the input
comparison along `S`, and the mate at the proposed limit. Dually, if
`W : J ⇸ J′`, `F : J → A`, and `C : J′ → A` is a supplied `W`-weighted
colimit, then

```
W-Colim_A(F,C)
    ⇒
W-Colim_B(S ∘ F,S ∘ C)
```

for a left adjoint `S`. The proof is the right-adjoint limit theorem in
opposite categories:

```
W-colimit in A
  ↔ W^op-limit in A^op
  → S^op preserves that limit, since R^op ⊣ S^op
  → W^op-limit in B^op
  ↔ W-colimit in B.
```

The adjunction is retained as one indexed structured witness; unit, counit,
transpose, and mate operations are projections from that witness rather than
unrelated component data. The calculus also includes a primitive
directed-inductive join category with two inclusions and one internally
natural cross cell. General coend semantics, a complete profunctor
bicategory, and unrestricted weighted (co)limit existence are not claimed.


From invertibility sieves to sheafification
-------------------------------------------

For a category `K`, a Cat-valued presheaf `P : K^op ⊢ Cat` assigns a
category of observations to every stage and a restriction functor to every
change of stage. A higher sieve may retain a category of witnesses over each
probe; an ordinary sieve is the subterminal case in which only the
proposition of membership remains.

Let `O : K^op ⊢ CommRing` be a presheaf of commutative rings, let `U : K`,
and let `s : O(U)`. For a probe `p : V → U`, define

```
D_U(s)(p) := Unit_{O(V)}(p^*s).
```

Ring maps preserve units, so membership restricts along every
`q : W → V`. The successful probes form an ordinary sieve on `U`. This is
the geometric organizing principle:

```
invertibility's sieve D_U(s), before invertibility's open.
```

The phrase “the open on which `s` is invertible” combines two statements:

1. invertibility is stable under change of stage, hence defines a sieve; and
2. that sieve is represented by one object over `U`.

The first holds on an arbitrary site. The second is additional geometry. In
the coherent/qcqs setting emphasized by Max Zeuner, a representing compact
open is precisely the largest compact open on which `s` is invertible. The
sieve formulation recovers that perspective when representability holds and
remains meaningful when no such representative has been selected.

For affine geometry, write `Aff = CommRing^op`. The generalized points of a
ring `R` at a test ring `S` are maps `h : R → S`, and

```
D_R(f)(S)
  = Σ(h : R → S), Unit_S(h(f)).
```

Given a localization by its universal property,

```
ι_f : R → R[1/f],
```

composition with `ι_f` and the contractible factorization property give, for
every test ring `S`,

```
Hom_CommRing(R[1/f],S) ≃ D_R(f)(S).
```

Thus localization represents the invertibility question pointwise without
requiring a fraction normal form. Unit algebra also gives

```
D_R(fg)(S) ≃ D_R(f)(S) ∩ D_R(g)(S).
```

A finite family `f₁,…,fₙ` with a certificate `Σᵢ aᵢfᵢ = 1`, together with
selected localizations, presents a finite family of basic charts. The least
Grothendieck topology accepting all such presentations is constructed as the
intersection of all accepting topologies. It satisfies maximality, pullback
stability, and local character, while retaining generator inclusion and
leastness. This universal construction does not assert a decision procedure
or an inductive syntax for coverhood.

For a fixed site `(K,J)`, a Cat-valued presheaf `P`, and a covering sieve `R`
on `U`, matching families and global sections are whole hom-categories:

```
Match_P(R) = Hom(R̂,P)
Sect_P(U)  = Hom(yU,P).
```

Restriction is precomposition with the inclusion `R̂ → yU`. A presheaf is
local at `R` when

```
Sect_P(U) → Match_P(R)
```

is an equivalence, and it is a sheaf when this holds for every covering
sieve. Sheafification is stronger: it must construct a local object from an
arbitrary presheaf, functorially and universally.

The direct cover completion `aP` is specified at the categorical-HIT boundary
by three whole operations:

```
return : P → aP

glue_q : Match_{aP}(R) → Sect_{aP}(U)

silent_q : glue_q ∘ restriction_q = id.
```

This is a categorical realization of the Pédrot-style free-sheaf pattern,
stated over actual covering questions rather than through a separate modal
surface theory. Glue is recursive because newly glued data may enter later
matching families. It is a functor, not only an object-level choice, and it
varies displayedly over the category of all eligible covering questions.
Whole naturality supplies pullback compatibility. The other inverse law for
restriction and glue is then derived; a recursor extends maps into local
targets; and categorical-HIT uniqueness yields

```
Hom(aP,Y) ≃ Hom(P,Y)
```

for every topology-local `Y`. Hence direct cover completion assembles the
fixed-site Cat-valued reflector

```
a : Psh_Cat(K) ⇄ Sh_Cat(K,J) : i,
                  a ⊣ i.
```

This construction is carried out directly in categorical semantics. Actual
presheaves, sieves, sites, matching families, and whole functors live in the
inner functorial type theory; TypeScript/emdash or Lambdapi/emdash supplies
the surrounding binders, conversion, rewriting, comparison, and unification.
No separate abstract modal type theory is required in order for this
categorical semantics to be computationally internal. A modal language may
still be useful as a concise interface; it is not a prerequisite for the
construction above.


Affine schemes, site-relative schemes, and the projective boundary
------------------------------------------------------------------

The affine construction now has a computational spine:

```
ring map
  → affine probe
  → invertibility sieve D(f)
  → localization R[1/f]
  → basic chart
  → generated big Zariski topology.
```

The current affine-scheme presentation then pairs this constructed spine with
two explicit capabilities: a supplied reflective commutative-ring-valued
structure sheaf wholly identified with the computing coordinate presheaf,
and supplied coordinate-localization locality on each `D(s)`. These
assumptions are visible because the constructed Cat-valued reflector has not
yet been lifted to commutative rings or proved left exact.

A general scheme presentation follows a global-first route. Begin with one
global reflective ringed object `X`, one covering sieve on `X`, and two
selected affine charts that constructively generate it. Whole restriction to
the actual slice, local-ring forcing, and affine-basis comparisons are
retained once. If a chart intersection is supplied as a product in the
slice, its object, overlap ring, and two restriction maps are derived from
the global presheaf rather than copied into an atlas record. The resulting
object is a binary, site-relative computational scheme presentation, not yet
an atlas-first gluing theorem or a representation-independent category of
schemes.

On a selected actual overlap of two affine-line charts, polynomial and
localization universal properties construct the Laurent coordinate changes

```
t ↦ u⁻¹,
u ↦ t⁻¹.
```

The supplied projective-line total packages one global site-relative scheme,
its actual chart intersection, and these whole Laurent comparisons. It does
not construct the global line from two charts. In particular, the active
artifact has no graded-ring interface, homogeneous localization, degree-zero
construction, `Proj`, general projective space `Pⁿ`, or non-affineness
theorem. The binary line is the smallest end-to-end test of the coordinate
machinery and the stated boundary for a future construction of

```
Pⁿ_A = Proj A[x₀,…,xₙ].
```

These qualifications are part of the result. Emdash currently demonstrates
that directed dependency, readable categorical binders, higher-inductive
normalization, weighted universal constructions, sieve-centered local
geometry, a Cat-valued sheafification reflector, free groupoidal realization,
profiled Gray interchange, and variable-dimensional dependent-simplex
recursion inhabit one executable architecture. It does
not claim that every displayed variance, every groupoidal closure, every
coefficient category, or the representation-independent theory of schemes
has already been completed.


-------------------------------------------------------------------------------


SHORTER TECHNICAL APPENDIX
==========================

The basic construction underneath the emdash kernel/book is the
ω-categorical directed dependent hom. For a category-valued family
`E : K ⊢ Cat`, and `x : K`, `u : E[x]`, emdash forms

```
homd_E(x,u)
  : Π(y : K^op), E[y^-] ⊢_[y] (Hom_K(x,y)^op ⊢ Cat),
```

whose value at `y`, `v : E[y]`, and `f : x → y` is
`Hom_{E[y]}(E[f](u),v)`. It organizes arrows in Sigma totals:

```
Hom_{ΣE}((x,u),(y,v))
  = Σ(f : x → y), Hom_{E[y]}(E[f](u),v).
```

For a category `Z`, put

```
x ↓ Z = Σ(y : Z), Hom_Z(x,y).
```

The reflexive object is `(x,id_x)`; write its canonical arrow to `(y,p)`
simply as `p`. Thus, for

```
E : (x ↓ Z) ⊢ Cat
u : E[(x,id_x)],
```

directed arrow induction has the compact form

```
Ind_x(E,u) : Π(a : x ↓ Z), E(a)

Ind_x(E,u)(y,p) = E(p)(u).
```

For `E[(y,p)] := Rep_Z(y) ⊢ Rep_Z(x)` and reflexive datum `id`, it computes
ordinary composition:

```
Ind_x(E,id)[(y,p)][z][q] ↝ q ∘ p.
```

The current TypeScript elaborator lets the same internal operations be
authored with familiar bound variables—e.g. `λ^f x. (H x) (K x)` and
displayed/natural variants—then lowers them to explicit emdash Core. The Core
is checked by TypeScript/emdash; selected judgments are also emitted to the
authoritative Lambdapi/emdash backend for conformance.

---

The first concrete directed HIT is opaque rather than defined by its desired
endomorphism type:

```
constant WalkingEnd : Cat

base : Obj(WalkingEnd)
loop : Hom_WalkingEnd(base,base).
```

Its whole recursor sends `base` to `ℕ` and `loop` to successor:

```
Code := rec_WalkingEnd(Cat_cat; ℕ,Succ)

Code[base] = ℕ
Code[loop] = Succ.
```

For a based arrow `p`, define `encode_x(p)=Code[p](0)`. In the other
direction,

```
power(0)   = id_base
power(n+1) = loop ∘ power(n),
```

and a spiral coherence

```
Rep_base[loop] ∘ power ⇒ power ∘ Succ
```

feeds the contextual displayed eliminator. It returns a coherent decoder and
a directed normalization cell

```
p → decode_x(encode_x(p)).
```

One-dimensionality then gives

```
power(encode_base(p)) = p
encode_base(power(n)) = n

Hom_WalkingEnd(base,base) ≃ ℕ
    (underlying carriers).
```

The result is `ℕ`, not `ℤ`, because `loop` is directed and has no right
inverse.

At the next hom level, Eckmann–Hilton gives

```
2End_B(x) = Hom_{Hom_B(x,x)}(id_x,id_x)

α,β : 2End_B(x)
β · α = β * α = α · β,
```

where `·` is vertical composition and `*` is horizontal composition.

---

The groupoidal return keeps the same computational distinction. The Circle
has `base`, `loop : base = base`, judgmental point and dependent-loop
computation, and a successor-localized universal cover with

```
Hom_Circle(base,base) ≃ ℤ.
```

WalkingEnd maps its forward powers to the nonnegative Circle powers. For an
arbitrary directed category, one whole unit

```
η_C : C → Path(Groupoidify(C))
```

gives the target-side mapping equivalence

```
Hom_Grpd(Groupoidify(C),G)
  ≃_ω Functor(C,Path(G)).
```

The recursor computes on represented points and dependent first cells and
retains higher action. Source functoriality and the packaged adjunction remain
separate.

The generic compositor `F[g] ∘ F[f] ⇒ F[g ∘ f]` becomes invertible in a path
target and becomes identity at a decoded strict code, but may remain directed
otherwise. One selected strict-object/lax-arrow right closure

```
GrayHom_lax(A ⊗_R B,C)
  ≃_ω GrayHom_lax(A,GrayHom_lax(B,C))
```

derives the nonidentity walking-square interchanger
`a₁ ∘ b₀ ⇒ b₁ ∘ a₀` from whole laxity. This is a profiled coherence test, not
the full Crans–Gray monoidal theory.

---

Injective face codes, directed joins, and iterated outgoing paths also give a
compact internal semisimplicial layer:

```
Delta[n+1] = Delta[n] * 1
S_0(C) = C
S_{k+1} = PathOut_{S_k}(s_k).
```

One Nat recursion constructs the canonical ordinal dependent simplex at
variable `n`; arbitrary `H : Functor(Delta[n],C)` maps it into `C`, and the
existing nonempty `FaceCode` action exposes its faces while retaining higher
action. Dimensions zero through four are checked. This is not yet a whole
`Functor_cat(Delta[n],C) ~= DependentSimplex_cat(C,n)` equivalence, and it adds
no degeneracies or general Kan/Segal/Rezk theorem.

---

Cat-valued profunctors are directed families

```
Prof(A,B) = A^op × B ⊢ Cat.
```

Emdash includes representables, endpoint reindexing, shaped cells, selected
tensor/co-Yoneda/internal-hom operations, and weighted universal comparisons.
For a weight `W : J ⇸ J′`, a selected `W`-weighted colimit `C` of
`F : J → A`, and an adjunction `S ⊣ R`,

```
W-Colim_A(F,C)
  ⇒ W-Colim_B(S ∘ F,S ∘ C).
```

This is obtained from right-adjoint preservation of weighted limits by
opposite normalization, rather than by duplicating the proof.

---

For local geometry, let `O : K^op ⊢ CommRing`, `s : O(U)`, and
`p : V → U`. Define the invertibility sieve

```
D_U(s)(p) := Unit_{O(V)}(p^*s).
```

It is stable under every refinement of `p`. Thus the primary object is
invertibility's sieve, not a previously chosen invertibility open. A compact
open may represent this sieve in a coherent/posetal setting, but
representability is an additional theorem.

For affine tests,

```
D_R(f)(S) = Σ(h : R → S), Unit_S(h(f)),

Hom_CommRing(R[1/f],S) ≃ D_R(f)(S)
```

for every supplied localization and test ring `S`. Moreover
`D_R(fg) ≃ D_R(f) ∩ D_R(g)` pointwise, while finite unit-ideal families
generate the big Zariski topology.

For a covering sieve `R` on `U` and a Cat-valued presheaf `P`,

```
Match_P(R) = Hom(R̂,P)
Sect_P(U)  = Hom(yU,P).
```

Sheafhood says that restriction from sections to matching families is an
equivalence. Direct cover completion constructs sheafification by a
categorical HIT with

```
return : P → aP
glue   : Match_{aP}(R) → Sect_{aP}(U)
silent : glue ∘ restriction = id,
```

followed by a recursor and whole uniqueness:

```
Hom(aP,Y) ≃ Hom(P,Y)

a : Psh_Cat(K) ⇄ Sh_Cat(K,J) : i,
                  a ⊣ i.
```

The construction lives directly in ordinary categorical semantics—actual
presheaves, sieves, sites, and functors—made computationally internal by the
surrounding TypeScript or Lambdapi logical framework. It does not require a
separate modal type theory.

The affine layer connects `D(f)`, localization, intersections, finite covers,
the coordinate presheaf, and an assumption-explicit reflective structure
sheaf. A global-first binary scheme presentation retains one ringed object,
one covering sieve, two affine generators, local-ring behavior, and inherited
restrictions and overlaps. On a supplied projective-line presentation, the
actual overlap carries the Laurent changes

```
t ↦ u⁻¹,
u ↦ t⁻¹.
```

This is a checked site-relative/projective-line capability, not yet an
atlas-first gluing theorem. Graded rings, homogeneous localization, `Proj`,
general projective space `Pⁿ`, and non-affineness remain future work.
