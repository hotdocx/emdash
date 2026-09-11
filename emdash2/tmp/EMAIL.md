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

Several mathematical threads expose the architecture. Directed arrow induction
transports reflexive data along a canonical Sigma arrow and computes ordinary
composition. A monad-primary full-functor interface combines whole unit and
multiplication observations with whole Kleisli extension, while ordinary
composition computes Došen's triangular reductions. Selected binary and empty
products expose whole projection, pairing, and terminal-arrow computation;
inside slices, chosen pullback and dependent-product structures extend them to
the three-adjoint chain `Σ_u ⊣ u* ⊣ Π_u`. A directed higher-inductive walking
endomorphism is normalized to the natural-number powers of its generator. In
local geometry, the locus where a section becomes invertible is constructed
first as a sieve D_U(s), before one asks whether an open represents it; finite
localization charts then generate a Zariski topology, while a direct
return/glue/silent categorical HIT constructs fixed-site Cat-valued
sheafification. Returning to the groupoidal layer, a Circle/Integer
encode-decode theorem restores inverse powers, category-indexed
groupoidification characterizes maps out by a whole mapping equivalence, and
one profiled Gray right closure exposes a nonidentity walking-square
interchanger from the same internal laxity action. That laxity is also
internalized cubically by applying the same triangular `homd_int` after an
inner Sigma total has made edges into objects. Generic Sigma-Hom then exposes
lax squares, and iterating the resulting derived lax-arrow category produces
cubes; `{L,R,*}` face codes act through whole restriction functors and retain
higher action. Finally, injective face codes form an internal semi-simplex
category. Directed join builds the ordinal shapes `Delta[n]`, and the internal
dependent hom
keeps the base-arrow layer of a dependent cell functorial. Iterated outgoing
paths place that layer beneath an independently varying target endpoint. This
nested double fibration produces native dependent simplexes. One Nat recursion
constructs a canonical ordinal source in variable dimension, maps it into
arbitrary target categories, exposes every nonempty face, and retains another
higher action; selected computations are checked through dimension four.

A further algebraic thread connects these internal structures to a focused
native TypeScript computer-algebra engine. Categorical programs lower whole
universal operations to polynomial and matrix computations while retaining
their selected objects, maps, relations, and factor data. Coherent kernel and
cokernel adjunctions make homology a whole functor; a whole connecting
transformation, three exact homology-window interiors, and finite assembly
are exercised by a nonsplit polynomial-module computation. Explicit proof–CAS
bindings then let the formal layer use the same results without running the
universal algorithms again or pretending that finite equations establish
every universal-property contract.

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

Research status. This appendix includes development-branch work; publishing
updated book artifacts is a separate step. The current whole-opposite and
Sigma-Hom encodings have known variance/soundness defects awaiting a separate
repair. “Checked” below records particular typechecks and computational
interfaces in this research calculus, not a global consistency certificate.
Formal claims depending on those higher-variance encodings remain unqualified
pending repair. The local ordinary-category interpretation of the homological
constructions must be distinguished from an unrestricted higher-categorical
semantics.


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
compositor is an already-existing cell

```
φ^F_{g,f} : F[g] ∘ F[f] ⇒ F[g ∘ f].
```

In a path target this cell is invertible; in a general directed target it need
not be. Strictness and pseudofunctoriality are properties of this existing
internal action, not alternate functor grammars. `IsStrictFunctor(F)` supplies
an endpoint path and identifies the compositor with the equality-induced
arrow, while `IsPseudoFunctor(F)` equips its fixed-forward readable
presentation with a native equivalence witness. The exact strict package is

```
StrictFunctor(A,B)
  = Σ(F : A ⊢ B), IsStrictFunctor(F).
```

The selected strict-object/lax-arrow profile uses these packages as objects
and reuses the ambient transfor and every higher-hom category as its hom tower:

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
In particular, no claim here depends on the separate continuing work to
re-home those historical global cuts at explicit profiles.


Cubical cells from the same internal action
--------------------------------------------

The key point is that a square is still produced by the triangular dependent
hom, not by a new square former. For an ordinary category-valued family `D`,
generic Sigma-Hom computation has the familiar form

```
Hom_{ΣD}((x,u),(y,v))
  = Σ(p : x → y), Hom_{D[y]}(D[p](u),v).
```

It says that an arrow in a Sigma total is a base arrow together with one fibre
arrow after transport. This is the same triangular mechanism used for
dependent arrows and simplexes.

To apply it cubically, begin with a mixed-variance family

```
E : K₁^op ⊢ Catd(K₂).
```

First internalize the second endpoint by an ordinary Sigma total:

```
Edge_E[x₁] := Σ(x₂ : K₂), E[x₁][x₂].
```

An object is `(x₂,u)` with `u : E[x₁][x₂]`. In the specialization
`E = hom_int(id_C)`, this is literally an edge `u : x₁ → x₂`. Now make the
variance adjustment

```
D_E[x₁] := Edge_E[x₁]^op
```

and reuse the existing whole dependent internal hom at its identity displayed
functor:

```
homdc_int(E) := homd_int(id_{D_E}).
```

This is a transparent definition, not a primitive cubical constructor. After
selecting target edge `(y₂,v)`, source edge `(x₂,u)`, and
`a : x₁ → y₁`, ordinary `homd_int` gives

```
Hom_{Edge_E[x₁]}
  ((x₂,u), Edge_E[a^op](y₂,v)).
```

Generic Sigma-Hom computation—not a square-specific rule—then exposes an
object as

```
b : x₂ → y₂
α : E[x₁][b](u) → E[a^op][y₂](v).
```

For `E = hom_int(id_C)`, the two existing Hom actions compute the endpoints:

```
E[x₁][b](u)    = b ∘ u
E[a^op][y₂](v) = v ∘ a.
```

Therefore the fibre arrow is precisely the directed 2-cell

```
α : b ∘ u ⇒ v ∘ a.
```

A particular square genuinely includes a chosen `α`, just as any directed
2-cell is data. What is absent is a bespoke record field or independently
postulated lax-commutativity law: the classifier and both endpoints of `α`
were computed by existing `homd_int`, Hom action, and Sigma-Hom.

The category of such arrows is also a transparent total:

```
TwoSided_E
  := (Σ(x₁ : K₁^op), Edge_E[x₁]^op)^op

LaxArrow(C)
  := TwoSided_{hom_int(id_C)}.
```

Its objects are edges. Its arrows have the canonical nested Sigma form

```
(a,(b,α)).
```

The readable constructor `lax_square(a,b,α)` merely packages that generic
term; it owns no separate square computation. The inner and outer opposites
select the displayed lax direction. The corresponding unreversed comma-total
orientation exposes the opposite, oplax cell `v ∘ a ⇒ b ∘ u`; changing
variance exchanges the two directions rather than removing the cell.

The source and target projections are whole functors, so both side-arrow
directions and the comparison cell retain their next actions. The public
`CubicalArrow` names are transparent readability aliases for this derived
`LaxArrow` construction, not a duplicate square theory. In short:

```
ordinary Sigma + pointwise opposite + homd_int
  → homdc_int
  → two-sided total
  → LaxArrow
  → CubicalArrow.       // transparent alias
```

Native cubical levels are genuine Nat recursion:

```
Cube_C(0)   = C
Cube_C(n+1) = LaxArrow(Cube_C(n)).
```

Objects at levels one, two, and three are edges, lax squares, and cubes. Face
maps are intrinsically indexed words in `{L,R,*}`: `L` and `R` fix the newest
coordinate at its two endpoints, while `*` retains it. Structural substitution
of these words computes, and their whole action satisfies the recursive
reading

```
L(f) ↦ face(f) ∘ source
R(f) ↦ face(f) ∘ target
*(f) ↦ LaxArrow(face(f)).
```

The star case consumes the retained `IsPseudoFunctor` property; it does not
invent a second forward map. The resulting whole semicubical nerve is

```
N_□(C) : SemiCubePlus^op ⊢ Cat
N_□(C)[n] = Cube_C(n).
```

Its generic arrow action remains available above every face restriction. A
recursive finite family exposes all `2n` immediate faces. Yoneda supplies an
object-level section/evaluation beta between the standard representable
semicube and a native cube, without asserting a whole equivalence.

The Gray and cubical readings meet through a fixed right bracketing:

```
GrayCube_R(1)   = I
GrayCube_R(n+2) = I ⊗_R GrayCube_R(n+1)

StrictFunctor(GrayCube_R(n+1),C)
  → Obj(Cube_C(n+1)).
```

This decoder is one internal Nat recursion. Dimensions one through three are
checked, and at dimension two its transformation graph recovers the same
coordinate-swapped interchanger as the walking-square calculation. The result
does not yet include an inverse decoder, a mapping-category equivalence,
alternate bracketings, tensor associativity, degeneracies, connections, or
Kan filling.


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

The bridge to the dependent presentation is the whole internal dependent hom
`homd_int`: it supplies the inner base-arrow-and-comparison layer of a
simplex, while the enclosing `PathOut` Sigma retains its independently varying
target edge. Put `S_0(C)=C`; after selecting `s_k : Obj(S_k)`, define

```
PathOut_C(x) = Σ(y : C), Hom_C(x,y)
S_{k+1}     = PathOut_{S_k}(s_k).
```

For a visible first edge `e₀₁=(x₁,p₀₁)`, a triangle is an object

```
t₀₁₂ = (e₀₂,q₀₁₂) : S_2,

e₀₂  = (x₂,p₀₂)
q₀₁₂ = (p₁₂,α₀₁₂).
```

Here `α₀₁₂ : p₁₂ ∘ p₀₁ ⇒ p₀₂`. The outer `PathOut` Sigma and the inner
`homd_int`/Hom-of-Sigma presentation give two genuinely different whole line
projections:

```
d_target(t₀₁₂) = e₀₂ = (x₂,p₀₂)
d_base(t₀₁₂)   = e₁₂ = (x₂,p₁₂).
```

If `Θ : t₀₁₂ → t₀₁₃` is a tetrahedral volume, ordinary source and target give
faces `012` and `013`, while functor action gives

```
d_target[Θ] = face 023
d_base[Θ]   = face 123.
```

Thus the four surfaces arise from the ordinary endpoints and the two nested
fibrations, not from a separately postulated tetrahedron record or boundary
equation. The next internal action remains available, so the construction
continues beyond a capped tetrahedron.

An intrinsically indexed flag code records the changing native category
without reimplementing it. A whole stage

```
F,G : K ⊢ B
ε : F ⇒ G
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


Monad computation in the triangular presentation
--------------------------------------------------

For a whole endofunctor `T : A ⊢ A`, an indexed witness

```
M : Monad_A(T)
```

has stable whole observations

```
η_M : id_A ⇒ T
μ_M : T ∘ T ⇒ T
```

and a whole extension functor

```
(-)*_{M,X,Y}
  : Hom_A(X,T(Y)) ⊢ Hom_A(T(X),T(Y)).
```

The whole extension retains another hom action. Its point observation sends
`f : X → T(Y)` to `f* : T(X) → T(Y)`. The standard semantic formula

```
f* = μ_Y ∘ T[f]
```

is a proof-time comparison rather than a runtime expansion of the stable
extension head. Ordinary ambient composition owns the monadic duals of
Došen's triangular reductions:

```
ηᶜ(g) ∘ f   ⇝ ηᶜ(g ∘ f)
g* ∘ ηᶜ(f)  ⇝ g ∘ f
g* ∘ f*     ⇝ (g* ∘ f)*
(η_X)*      ⇝ id_TX.
```

Here `η_X = ηᶜ(id_X)`. The first law is inherited from generic
transformation naturality. The accumulation orientation removes the top-level
cut between two extension-generated arrows and retains a single extension
whose internal cut has lower degree. The standard multiplication observation
uses the same triangular normal-form language at components:

```
μ_X ⇝ (id_TX)*.
```


Products, terminal objects, and indexed base change
----------------------------------------------------

A selected binary product begins with a whole functor, not with unrelated
objectwise choices:

```
P : C × C ⊢ C

κ₁ : P ⇒ pr₁
κ₂ : P ⇒ pr₂.
```

For `f : X → A` and `g : X → B`, pairing is itself the point of a whole
represented-family transformation

```
⟨-,-⟩_X
  : Hom_C(X,A) × Hom_C(X,B) ⊢ Hom_C(X,P(A,B)).
```

Consequently higher arrows between possible legs are mapped to higher arrows
between their pairings. Došen's antecedential projections

```
K₁ᵃ(h) = h ∘ κ₁
K₂ᵃ(h) = h ∘ κ₂
```

make the principal structural cuts visible:

```
K₁ᵃ(h) ∘ ⟨f,g⟩ ⇝ h ∘ f
K₂ᵃ(h) ∘ ⟨f,g⟩ ⇝ h ∘ g

⟨f,g⟩ ∘ k ⇝ ⟨f ∘ k,g ∘ k⟩
h ∘ Kᵢᵃ(f) ⇝ Kᵢᵃ(h ∘ f)
⟨κ₁,κ₂⟩ ⇝ id.
```

The generic whole-functor action is retained, rather than expanded as another
runtime normal form. It agrees at proof time with the triangular map:

```
P[f,g] ≐ ⟨K₁ᵃ(f),K₂ᵃ(g)⟩.
```

Here `≐` means proof-time agreement. The selected product calculus is distinct
from the always-available product *category* constructor and from the stronger
weighted-limit presentation; an explicit adapter can relate a supplied
weighted comparison without manufacturing one from beta and eta alone.

The empty product is a selected terminal object `t` with one whole canonical
arrow transformation

```
! : id_C ⇒ Const_t.
```

Its component and off-diagonal action compute through the terminal cut

```
!_B ∘ h ⇝ !_A.
```

Unrestricted uniqueness is not a variable-headed rewrite. Instead
`Hom_C(A,t)` is contractible, recentered at `!_A`, and every `f : A → t`
therefore has an internal path `f = !_A`. A thin cartesian package merely
pairs the already-selected binary and empty products; it introduces no second
set of operations or rules.

The same introduction/elimination discipline becomes indexed in slices. For
`u : X → Y`, postcomposition always gives

```
Σ_u : C/X ⊢ C/Y.
```

A chosen pullback structure supplies one opposite-variance whole family with
exact fibres `C/X` and action

```
u* : C/Y ⊢ C/X,

Σ_u ⊣ u*.
```

The unit and counit are actual whole transformations. Their off-diagonal
actions `γᶜ` and `φᵃ` satisfy the full rectangular reductions

```
φᵃ(h) ∘ Σ_u(γᶜ(k)) ⇝ h ∘ Σ_u(k)
u*(φᵃ(h)) ∘ γᶜ(k) ⇝ u*(h) ∘ k.
```

The associated mate functors act on whole hom-categories:

```
Hom_{C/Y}(Σ_u(a),g) ⇄ Hom_{C/X}(a,u*(g)).
```

Their point and whole composites cancel, while the stable computational
presentation remains proof-time comparable with the explicit unit/counit
formulas. A pullback cone is therefore already an object of the left-hand hom,
not a record storing two legs and a commuting-square proof. If
`g : Z → Y`, the selected slice object

```
u*(g) = (Q, π₁ : Q → X)
```

is the pullback object. The counit supplies `π₂ : Q → Z` and the retained
directed square

```
g ∘ π₂ ⇒ u ∘ π₁.
```

In a locally discrete category this recovers the usual strict equation.

A selected dependent-product structure supplies the third whole slice family
and the second adjunction:

```
Π_u : C/X ⊢ C/Y

Σ_u ⊣ u* ⊣ Π_u.
```

Its unit/counit transfors, both Došen rectangles, whole transpose and
untranspose, and the varying-endpoint hom comparison reuse the same generic
adjunction calculus. This is a computational foundation for local cartesian
closure, not yet a convention-sensitive LCCC package: derived slice
exponentials, Beck–Chevalley, Frobenius, pushout duality, and comparison with
independently selected weighted pullbacks remain later coherence layers.


An algebra engine beneath categorical programs
-----------------------------------------------

Which computations belong to the categorical calculus, and which need an
effective algebraic presentation? Emdash now has both layers. Its own
TypeScript engine implements exact integer/rational arithmetic, sparse
multivariate polynomials, Gröbner and membership computations, elimination
and saturation, polynomial-module syzygies, and bounded resolution
constructions. Coefficients, polynomial rings, monomial orders, module ranks,
and presentations remain explicit. A matrix over one parent is not silently
used over another.

A mathematical operation is separate from its algorithm and execution
engine. For example, a categorical program may request a kernel once, retain
its whole result, and use the same selected object and embedding in later
lifting operations. Primitive and derived operation roles record their
prerequisites. Explicit bindings lower these whole categorical operations to
typed algebra computation graphs, whose native and compiled results can be
compared without choosing new universal objects.

This takes inspiration from CAP/homalg: ring algorithms and constructive
categorical operations are separate reusable layers. The present compiler
performs explicit whole-operation lowering; it is not yet a general optimizer
or an automatic inliner for arbitrary categorical algorithms. CAP, homalg,
and Singular are useful design references or optional differential oracles,
not runtime prerequisites of the native computations.

The results are mathematical data, not merely answers or certificates. A
membership calculation retains coefficients and a remainder; a kernel
calculation retains a presentation and its structural maps; a bounded
homology calculation retains the actual degree objects, induced maps,
connecting windows, and factor witnesses. These data are needed by the next
computation even when no proof assistant is involved.

The proof assistant adds a typed realization of a particular formal question:

```
formal goal and selected computational presentation
  → typed operation and categorical/algebraic program
  → native whole result
  → observation, formal data, or explicit adoption.
```

Running a computation alone adds no theorem. Its data can be reified into
explicit emdash Core, its equations can be adopted with an explicit trust
decision, and a checked proof-plan route is available where useful. The
operation, coefficient bindings, exact goal, selected result and subsequent
interpretation stay connected. A changed target or different selection is
not accepted merely because a similar-looking calculation succeeded.

Large Gröbner or homology computations are explicit operations, not hidden
inside logical-framework conversion. This keeps ordinary categorical cuts
predictable while allowing algorithms, execution limits and implementations
to evolve. The integration is therefore computation-first: verification may
be useful, but proving the CAS correct is not a prerequisite for using it.


Presentations, universal operations, and whole homology
-------------------------------------------------------

The effective module representation is categorical. A presentation over `R`
is a relation map, and a raw morphism retains both generator and relation
matrices:

```
ρ_P : R^r_P → R^g_P

F : R^g_P → R^g_Q
W : R^r_P → R^r_Q
ρ_Q W = F ρ_P.
```

Two generator matrices induce the same quotient map when a coefficient
matrix `L` satisfies

```
ρ_Q L = F − G.
```

Relation preservation and equality of represented maps are different jobs.
The formal Freyd category forms its quotient Homs by groupoidifying the raw
agreement category and taking its set truncation. Presentations remain the
primary objects; element semantics can be derived representably. The native
solver supplies actual coefficient witnesses, whereas the formal interface
does not extract a chosen matrix witness from an arbitrary truncated
quotient path.

Generic preadditive and additive structure provides abelian Hom groups,
bilinear composition, biproducts and a zero object. Kernel and cokernel
interfaces retain universal factors and their reconstruction laws. Normal
mono/epi operations then construct image/coimage comparisons, their
isomorphism, and the fibre-product/pushout stability used in homological
arguments. These are not declarations that selected image and kernel objects
are literally identical.

The whole-functor interface organizes the same universal choices. In an
ordinary-category working profile, write `2` for the walking arrow and let

```
D_C = Functor_cat(2,C)
J(A) = (A → 0)
I(A) = (0 → A).
```

Coherent presentations provide

```
K : D_C ⊢ C             J ⊣ K
Q : D_C ⊢ C             Q ⊣ I.
```

The counit of the first adjunction supplies kernel embeddings; the unit of
the second supplies cokernel projections. Their mates supply lifts and
colifts. Proof-time usability relates these observations to the original
selected operations while leaving the whole functor heads available for
generic adjunction computation. A coherent presentation is supplied
structure, not an automatic consequence of finitely many matrix equations.

For a coherent family of zero-composition diagrams,

```
U : B ⊢ C
D : B ⊢ D_C
h : J ∘ U ⇒ D,
```

the kernel adjunction constructs the whole boundary transformation, and the
cokernel functor constructs homology:

```
β = K[h] ∘ η_U : U ⇒ K ∘ D

H = Q ∘ Arr(β) : B ⊢ C.
```

Here `Arr(β)` is the whole walking-arrow diagram family introduced by the
actual transformation `β`. At a point this is the familiar construction

```
Z = Ker(d)
k : Z → source(d)
b : source(dNext) → Z,     k ∘ b = dNext
H = Coker(b).
```

But the family formula already has functoriality and higher Hom action;
there is no separate list of naturality squares to supply. The existing
generic cut remains the owner of

```
H[g] ∘ H[f] ⇝ H[g ∘ f].
```

The native source category is the existing internal comma construction

```
Z_C = (J ↓ id_D_C).
```

Its objects are `h : J(A) ⇒ d`; the source component is the incoming arrow,
and naturality gives its zero composite with the differential of `d`.
The category and its maps reuse internal Hom/Sigma structure, rather than a
new grammar of complexes with manually stored commuting squares. Its
ordinary-target specialization gives a whole one-degree functor
`H : Z_C ⊢ C`. Operational universal records are views at that same H object,
not a second homology reached by an object-equality cast.

Exactness still expresses a universal property: the actual boundary into
the selected cycle kernel is epic. The generic six-term snake sequence has
all four interior exactness results. At whole-H endpoints, a direct
connecting construction uses an epic cover of source cycles, lifting into
target cycles, and descent through the original boundary cokernel. The
five-term window

```
H_n(A) → H_n(B) → H_n(C) ─δ_n→ H_(n−1)(A) → H_(n−1)(B)
```

has all three adjacent-zero laws and all three interior exactness results.
For a coherent window family, its vertical columns are whole functors
`V_C,V_A : B ⊢ Z_C`, and connecting is an actual transformation

```
δ : H ∘ V_C ⇒ H ∘ V_A.
```

Its component computes to the direct lifting/descent construction. Generic
transfor action supplies naturality and further action; the caller does not
prove an extra naturality square and then package a transformation.

A finite iterator assembles coherent windows while retaining their original
arrows and interior evidence. The native bounded result also retains its
actual outside-support zero homologies. The final symbolic zero-endpoint
attachment is separately deferred. Reconstruction and exactness proofs still
use explicit paths; this is a constructive reference implementation with
whole operations, not a claimed Došen-style decision procedure for all
homological arrow expressions or a category of unbounded complexes.


A nonsplit calculation at the proof–CAS boundary
------------------------------------------------

Let `R = ℚ[x]` and `S = R/(x)`, viewed as an `R`-module. Take the two-degree
complexes

```
A : R ─x→ R
B : R ─x→ R
C : S ─0→ S,
```

with inclusion `i` given by multiplication by `x` and projection `p` given
by quotient. Each supported row is

```
0 → R ─x→ R → S → 0.
```

It is nonsplit: every `R`-linear map `S → R` has image annihilated by `x`,
hence is zero. No section of the quotient projection can be used. The
nontrivial homology sequence is

```
0 → H₁(C) ─δ₁→ H₀(A) ─H₀(i)→ H₀(B) ─H₀(p)→ H₀(C) → 0

0 → S ─id→ S ─0→ S ─id→ S → 0.
```

For a representative `r` of a class in `H₁(C)`, its middle differential is
`xr`, which lifts through the inclusion as `r`. Passing to target homology
therefore gives `δ₁(r̄) = r̄`. This is independent of changing a representative
by `xu`; it is not a choice of an `R`-linear section.

The actual returned matrices are

```
δ₁ = [1],       H₀(i) = [x],       H₀(p) = [1].
```

The middle matrix is zero in the target quotient, not as a raw matrix. The
composite after connecting retains the coefficient witness

```
ρ_target [1] = [x] = [x][1] − [0],     ρ_target = [x].
```

Even the selected `H₀(C)` retains one generator with relation columns
`[x,x]`: the original relation and the incoming boundary. It represents
`S`, but no smaller presentation is substituted behind the formal consumer.
The whole bounded result shares its selected homologies and maps across
neighboring windows rather than recomputing them at each occurrence.

The formal connection has three distinct kinds of information. Computed
equations justify individual raw maps and agreements. Selected-provider
semantics bind the all-test factor operations at the retained kernel choices.
Whole-model interpretation binds the actual formal H and connecting
observations to those same native results. For an introduced chain map `m`,
write `F_native` for its reified induced arrow. With `P_z` the reified
selected presentation and `Obs` the existing complete arrow-object
observation,

```
H_M[z] = P_z
Obs(H_M[m]) = Obs(F_native)
Obs(δ_M)   = Obs(δ_native).
```

An arrow observation includes its source, target and arrow together. These
are explicitly adopted semantic bindings, not runtime rules that make every
H expression invoke the CAS. The coherent model `M` is supplied, and its
normality enhancement is required for the connecting interpretation; a
finite list of matrix equations does not construct that model automatically.

The end-to-end consumer constructs a formal raw sequence and selected
homology/exactness at every displayed interior, then interprets the retained
whole-H points, induced maps, and all three connecting windows. Only the
middle connecting is nonzero. The interpretation preserves the original
objects, arrows and shared row evidence, and makes no new kernel, homology or
connecting selection. Thus formal mathematics can use an actual H term and
its action while native algebra supplies its effective presentation. Neither
an unrestricted quotient-witness decoder nor a proof of every native
algorithm is inserted as an implicit prerequisite.


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


Finite affine computation and varying-ring Čech cochains
--------------------------------------------------------

The native affine layer realizes principal localization by adjoining an
inverse. For a presented algebra `R = k[x₁,…,x_m]/I`,

```
R[1/f] = k[x₁,…,x_m,t]/(I,tf−1).
```

Relation-checked algebra maps, presented tensor products and affine fibre
products reuse the same exact polynomial operations. A successful
unit-ideal calculation retains coefficients `Σᵢ aᵢfᵢ = 1` and the selected
basic-open charts, rather than only returning a cover Boolean.

The proof–CAS adapter reifies those coefficients and inverse equations,
explicitly binds the selected localization's universal semantics, and uses
the existing formal localization and cover constructors. Face-denominator
units and overlap factors are then derived formally from those same
localizations; the caller does not handwrite a new equation for every face.
This separates an effective presentation from its universal-property
interpretation without preventing ordinary affine computation.

For a presented `R`-module `M`, modules over its different localizations need
not share one scalar parent. The native varying-ring diagram retains
semilinear restriction maps and forms finite additive cochain groups

```
Cⁿ = ∏_(i₀<⋯<iₙ) M[1/(f_i₀⋯f_iₙ)].
```

Each component lives over its own actual localized ring. The differential
adds signed face images only after they land in the same target component:

```
(d s)_J = Σ_p (−1)^p res_(J,p)(s_(J without p)).
```

The two routes through every repeated face have equal composite images and
opposite signs, so the implementation retains their cancellations and
computes `d²(s)=0` on the supported degrees. The input is the existing face
diagram, not an additional collection of commuting-square witnesses.

This is finite cochain computation, not yet Čech cohomology. A localization
is not silently treated as a finitely presented module over the original
ring, and the final retained degree is not given an invented zero successor.
Connecting these heterogeneous cochains to a cohomology solver requires its
own justified effective representation; the fixed-ring bounded homology
engine is not applied merely because both constructions use differentials.

These qualifications are part of the result. Emdash currently demonstrates
that directed dependency, readable categorical binders, higher-inductive
normalization, monad and cartesian cut elimination, indexed
`Σ_u ⊣ u* ⊣ Π_u` structure, weighted universal constructions,
sieve-centered local geometry, a Cat-valued sheafification reflector, free
groupoidal realization, profiled Gray interchange, native cubical action,
variable-dimensional dependent-simplex recursion, and retained proof–CAS
computation inhabit one development architecture. Whole kernel/cokernel and
homology operations, generic snake/window exactness, nonsplit bounded
computations and finite affine cochains now test that connection. It does
not claim that every displayed variance, every groupoidal closure, every
coefficient category, or the representation-independent theory of schemes
has already been completed.


-------------------------------------------------------------------------------


SHORTER TECHNICAL APPENDIX
==========================

This is a development snapshot, not a global consistency claim. Known
variance/soundness defects in the whole-opposite and Sigma-Hom encodings
remain separately tracked; formal claims depending on those higher-variance
encodings remain unqualified pending repair. The checked interfaces below
and the local ordinary-category homological interpretation do not assert
that those foundational repairs or the separate strictness migration are
complete.

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

For a category `Z`, define the outgoing-arrow category

```
PathOut_Z(x) := x ↓ Z = Σ(y : Z), Hom_Z(x,y).
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
target but may remain directed otherwise. `IsStrictFunctor(F)` and
`IsPseudoFunctor(F)` constrain that same existing internal action; the strict
package is exactly `Σ(F : A ⊢ B), IsStrictFunctor(F)`, not a decoded parallel
grammar. One selected strict-object/lax-arrow right closure

```
GrayHom_lax(A ⊗_R B,C)
  ≃_ω GrayHom_lax(A,GrayHom_lax(B,C))
```

derives the nonidentity walking-square interchanger
`a₁ ∘ b₀ ⇒ b₁ ∘ a₀` from whole laxity. This is a profiled coherence test,
not the full Crans–Gray monoidal theory or the still-separate global migration
of historical strict cuts.

The square is another use of the same triangular formula

```
Hom_{ΣD}((x,u),(y,v))
  = Σ(p : x → y), Hom_{D[y]}(D[p](u),v).
```

For `E : K₁^op ⊢ Catd(K₂)`, first make edges into objects and correct the
variance:

```
Edge_E[x₁] := Σ(x₂ : K₂), E[x₁][x₂]
D_E[x₁]    := Edge_E[x₁]^op

homdc_int(E) := homd_int(id_{D_E}).
```

After fixing edge objects `(x₂,u)`, `(y₂,v)`, and `a : x₁ → y₁`, generic
Sigma-Hom exposes

```
b : x₂ → y₂
α : E[x₁][b](u) → E[a^op][y₂](v).
```

For `E = hom_int(id_C)`, ordinary post- and precomposition reduce this to

```
α : b ∘ u ⇒ v ∘ a.
```

Thus a square is a triangular `homd_int` arrow between edge objects. The
derived total has objects `u` and arrows `(a,(b,α))`; the readable
`lax_square(a,b,α)` only packages this canonical nested Sigma term. It does
not introduce a square record or a separate commutativity law. Iteration then
gives native cubical levels

```
Cube_C(0)   = C
Cube_C(n+1) = LaxArrow(Cube_C(n)),
```

while intrinsically indexed `{L,R,*}` words compute face substitution and act
by whole restriction functors. They assemble a semicubical nerve
`N_□(C) : SemiCubePlus^op ⊢ Cat`, retain higher action, and expose all `2n`
immediate faces. A fixed-bracketing right-Gray cube decoder maps strict Gray
cube diagrams to native cubes; dimensions one through three are checked, and
dimension two recovers the walking-square interchanger. No inverse decoder,
whole mapping equivalence, degeneracies, connections, Kan fillers, alternate
bracketings, or Gray monoidal coherence is claimed.

---

Injective face codes, directed joins, and iterated outgoing paths also give a
compact internal semisimplicial layer:

```
Delta[n+1] = Delta[n] * 1
S_0(C) = C
S_{k+1} = PathOut_{S_k}(s_k).
```

The internal dependent hom supplies the inner base-arrow-and-comparison pair,
while the outer `PathOut` Sigma supplies the varying target edge. For
`e₀₁=(x₁,p₀₁)`, a triangle therefore has the nested form

```
t₀₁₂ = (e₀₂,q₀₁₂),
e₀₂  = (x₂,p₀₂),
q₀₁₂ = (p₁₂,α₀₁₂).
```

Here `α₀₁₂ : p₁₂ ∘ p₀₁ ⇒ p₀₂`.

Two whole projections return the target edge `e₀₂=(x₂,p₀₂)` and the base edge
`e₁₂=(x₂,p₁₂)`. For a volume `Θ : t₀₁₂ → t₀₁₃`, their hom actions give faces
`023` and `123`; ordinary source and target give `012` and `013`. The boundary
therefore comes from nested functorial projections, not a separate record,
and the next internal action remains available.

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

For `T : A ⊢ A`, the monad interface combines whole transformations

```
η : id_A ⇒ T
μ : T ∘ T ⇒ T
```

with a whole extension functor sending `f : X → T(Y)` to
`f* : T(X) → T(Y)`. Ordinary composition computes the Došen-oriented laws

```
ηᶜ(g) ∘ f   ⇝ ηᶜ(g ∘ f)
g* ∘ ηᶜ(f)  ⇝ g ∘ f
g* ∘ f*     ⇝ (g* ∘ f)*
(η_X)*      ⇝ id_TX.
```

Here `η_X = ηᶜ(id_X)`. The semantic equation `f* = μ_Y ∘ T[f]` is
proof-time, so it does not erase the stable extension head. Standard
multiplication components use the same triangular language:

```
μ_X ⇝ (id_TX)*.
```

---

A selected binary product is a whole functor `P : C × C ⊢ C` with whole
projections and whole represented-family pairing. Its triangular cuts compute:

```
K₁ᵃ(h) ∘ ⟨f,g⟩ ⇝ h ∘ f
K₂ᵃ(h) ∘ ⟨f,g⟩ ⇝ h ∘ g
⟨f,g⟩ ∘ k ⇝ ⟨f ∘ k,g ∘ k⟩
⟨κ₁,κ₂⟩ ⇝ id.
```

The whole action `P[f,g]` agrees at proof time with
`⟨K₁ᵃ(f),K₂ᵃ(g)⟩`; it is not expanded as a competing runtime form. A
selected terminal object has

```
! : id_C ⇒ Const_t
!_B ∘ h ⇝ !_A,
```

while arbitrary uniqueness follows from contractibility of `Hom_C(A,t)`
rather than a variable-headed rule.

For `u : X → Y`, postcomposition in slices always supplies `Σ_u : C/X ⊢ C/Y`.
Chosen pullbacks and dependent products add whole functors

```
u*  : C/Y ⊢ C/X
Π_u : C/X ⊢ C/Y

Σ_u ⊣ u* ⊣ Π_u.
```

Both adjunctions retain actual whole unit/counit transfors, the full Došen
rectangles, whole mate action, and Hom-category comparison. The pullback of
`g : Z → Y` is the selected slice object `u*(g)`; its counit supplies the
second projection and directed square. Thus a cone is an object of
`Hom_{C/Y}(Σ_u(a),g)`, not a separately stored pair of legs and equation.
Beck–Chevalley, Frobenius, derived slice exponentials, and the final
convention-sensitive LCCC package remain later layers.

---

The same mathematics now has a focused native TypeScript algebra engine:
exact arithmetic, sparse polynomials, Gröbner/membership operations, syzygies,
presented modules, and bounded homological computation. Operations are
separate from algorithms and engines. CAP/homalg-inspired categorical roles
record prerequisites, and explicitly bound whole operations lower to typed
algebra computation graphs. This is not yet a general optimizing compiler,
and external CAS systems are optional references or oracles.

Results retain the data needed by later mathematics: coefficients, relations,
structural maps, selected universal objects and factor witnesses. The formal
interface binds a named goal to its selected computational presentation and
whole result. Execution may return ordinary data, reified formal terms or an
explicitly adopted claim; merely running the CAS adds no theorem. Heavy
algebraic algorithms remain explicit operations, not hidden conversion rules.

For a presentation `ρ_P : R^r_P → R^g_P`, a raw map and an agreement have
different coefficient witnesses:

```
ρ_Q W = F ρ_P             — relation preservation
ρ_Q L = F − G             — agreement of quotient maps.
```

The Freyd category keeps presentations primary and obtains quotient Homs by
groupoidification and set truncation of raw agreements. Native algorithms
produce usable witnesses; the formal interface does not decode arbitrary
truncated paths into chosen matrices.

Whole kernel and cokernel presentations relate to these selected operations
through adjunctions. With `2` the walking arrow and `D_C = Functor_cat(2,C)`,

```
J(A) = (A → 0),       J ⊣ K
I(A) = (0 → A),       Q ⊣ I.
```

For a coherent family `h : J ∘ U ⇒ D`, the whole boundary and homology are

```
β = K[h] ∘ η_U
H = Q ∘ Arr(β).
```

The native one-degree source is the existing comma category `(J ↓ id_D_C)`
in the ordinary-target profile. Its diagram objects and maps reuse internal
Hom/Sigma structure; no new list of naturality squares is an input. H is an
actual derived functor with generic cut computation and further Hom action,
and its operational record views retain the same selected objects.

The generic six-term snake has four interior exactness results. The whole-H
window has three, and connecting is an actual transformation between H of
its two vertical column functors. Its component computes to the direct
lifting/descent construction at those same H endpoints. Finite iteration
retains the original arrows and interior evidence; the final symbolic
zero-endpoint attachment is deferred, although native bounded computations
already retain their outside-support zero data. These interfaces do not yet
constitute a general homological normalization calculus.

For the concrete nonsplit example, set `R=ℚ[x]`, `S=R/(x)` and take

```
A : R ─x→ R,     B : R ─x→ R,     C : S ─0→ S.
```

The rows `0 → R ─x→ R → S → 0` admit no `R`-linear section. Nevertheless the
connecting map is nonzero: a representative `r` has middle differential
`xr`, lifts through the inclusion as `r`, and gives `δ₁(r̄)=r̄`. The retained
matrices are `[1]`, `[x]`, `[1]` for `δ₁`, `H₀(i)`, `H₀(p)`. The middle
map is quotient-zero, witnessed by the target relation `[x]`, while `H₀(C)`
retains its original relation columns `[x,x]` rather than substituting a
smaller presentation.

The formal consumer uses these same choices. For a supplied coherent model
`M`, computed equations, all-test universal-provider semantics and whole-model
interpretation stay distinct:

```
H_M[z] = P_z
Obs(δ_M) = Obs(δ_native).
```

Here `P_z` is the reified selected presentation, and `Obs` retains source,
target and arrow together. These are explicit semantic bindings, not new
runtime CAS rewrites. The coherent model and its normality are supplied;
their existence is not inferred from finite matrix tests. All retained
degree maps and connecting windows are interpreted without another kernel,
homology or connecting selection. This is a usable formal/CAS interface,
not a claim of closed quotient effectiveness or verification of every native
algorithm.

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

The native affine computation now also realizes localization by adjoining
an inverse, `R[1/f] = R[t]/(tf−1)`, and retains relation-checked algebra maps,
tensor products, finite charts and overlap data. The proof–CAS cover adapter
reifies the unit-ideal coefficients and inverse equations, separately binds
the selected universal semantics, then derives face units and overlap
factors through the existing formal constructors.

For a presented module `M` over the base ring, the finite Čech cochains of
its localization diagram are heterogeneous additive tuples:

```
Cⁿ = ∏_(i₀<⋯<iₙ) M[1/(f_i₀⋯f_iₙ)]
(d s)_J = Σ_p (−1)^p res_(J,p)(s_(J without p)).
```

Each signed contribution lands in its actual target module before addition.
Repeated-face composites agree and their signs cancel, giving native `d²=0`
computations without new caller-supplied square witnesses. This does not
assume that all localizations are finitely presented over the original ring
or that a truncated diagram has an extra zero differential. Čech cohomology,
derived categories and spectral sequences remain further developments.
