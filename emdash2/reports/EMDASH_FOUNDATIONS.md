# emdash Foundations

Draft status: this document is a mathematician-facing reading guide for the
current `emdash3_2.lp` theory. It presents the intended mathematics in ordinary
category/type-theory notation and deliberately suppresses most Lambdapi rewrite
engineering details.

The implementation is still evolving. This note describes the current directed
categorical foundation, not a finished proof assistant surface language.
For parser/comment notation, use
`REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md` as the authority.

## 1. Reading Guide

The central idea is to treat categories, functors, transformations, functorial
families of categories, dependent sums, dependent products, and dependent homs
as one computational theory.

The notation is intentionally close to dependent type theory:

```text
F : A ⊢ B              ordinary functor
F[x]                    action of F on an object
F[f]                    action of F on an arrow
E : K ⊢ Cat            functorial family of categories over K
E[k]                    fibre category at k
Σ_k E[k]                total category of a family
Π_k E[k]                category of sections of a family
s[k]                    value of a section at k
s[f]                    action of a section over f : x ->^K y
```

The word "directed" matters. The base `K` is a category with real arrows, not
just a type of points. Consequently, pointwise constructions must usually carry
naturality data over base arrows.

### Implementation Reading Note

This document gives the mathematical surface. The Lambdapi file also contains
stable projection heads such as `tapp0_fapp0`, `homd_src_func`,
`fdapp1_int_hom_fapp0`, and `fdapp1_int_cell`. These names are kernel
normalization artifacts: they preserve enough structure for rewrite rules and
higher hom-actions to keep computing.

When planning implementation work, use this document to understand the
mathematics, then use
`REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md` for the rewrite
hygiene and stable-head ownership rules. Do not infer from the surface formula
alone that a new primitive head is needed; first locate the current semantic
owner in `emdash3_2.lp`.

## 2. Categories And Hom-Categories

A category `A` has:

```text
Obj(A)                  objects of A
Hom_A(x,y)              category of arrows from x to y
id_x                    identity arrow
g ∘ f                   composition
```

The hom between two objects is itself a category. This is the basic
ω-categorical shape: arrows, higher arrows, and higher comparisons are
represented by iterating `Hom`.

The opposite category reverses homs:

```text
Obj(A^op) = Obj(A)
Hom_{A^op}(x,y) = Hom_A(y,x)
```

There is also a terminal category `1`, whose object and hom data are all
contractible.

## 3. Equality And Path Categories

The theory includes a HoTT-style equality infrastructure at the groupoid/type
level:

```text
x =_A y       : Grpd
refl_x        : x = x
J             equality induction
```

From any groupoid/type `A`, there is a path category:

```text
Path(A)
Obj(Path(A)) = A
Hom_{Path(A)}(x,y) = Path(x =_A y)
```

Composition in `Path(A)` is path transitivity.

This is motivation and infrastructure, not yet the full HoTT program. The
current v3.2 theory does not yet characterize equality in Sigma types, equality
in Pi types, equality in the universe, univalence, equivalences, or pushouts.
Those are intentionally deferred.

## 4. The Universe Of Categories

The category universe `Cat` is itself a category:

```text
Obj(Cat) = categories
Hom_Cat(A,B) = Functor(A,B)
```

Thus an arrow in the universe of categories is a functor. This is the directed
universe principle used throughout the development.

Ordinary functors have object and arrow actions:

```text
F : A → B
F[x] : Obj(B)
F[f] : Hom_B(F[x],F[y])
```

This is a useful discipline throughout the development: an equation such as
`E[x] = ...` is only the object part of a functorial or natural construction.
When `x` ranges over a directed category, the corresponding arrow action over
`p : x -> y` is part of the structure, not a later cosmetic detail.

The same warning applies one level up. A displayed equation such as
`eta[x] = ...` gives only the component of a natural transformation. Its
functorial/naturality action over arrows is represented primarily by
`tapp1_func eta`; capped projections such as `tapp1_fapp0 eta p`, or
constructor-specific `*_tapp1_*` helpers, may be the relevant implementation
surface. That arrow action must still be specified or explicitly deferred
before the construction is treated as implemented.

The theory also has transformation categories:

```text
Transf(F,G)
```

whose objects are transformations from `F` to `G`. A transformation
`ϵ : F => G` has point components:

```text
ϵ[x] : Hom_B(F[x],G[x])
```

## 5. Directed Families

A directed family of categories over `K` is a functor:

```text
E : K ⊢ Cat
```

The theory writes this as a category-valued family:

```text
E : Catd(K)
E[k] = fibre of E at k
```

Terminology used in this note:

- A **functorial family** is a category-valued functor `E : K ⊢ Cat`.
- A **natural family morphism** `FF : E ⊢ D` is a family of functors that is
  natural in the base variable.
- A **natural family transformation** `ϵ : FF => GG` is a family of
  transformations that is natural in the base variable.

The implementation names for these are `Catd`, `Functord`, and `Transfd`,
respectively. The words "displayed" and "family" still occur in implementation
names, but this document uses "functorial" and "natural" to emphasize the
variance over base arrows.

A natural family morphism has fibre functors:

```text
FF : k :^n K ; E[k] ⊢ D[k]
FF[k] : E[k] ⊢ D[k]
```

A natural family transformation has fibrewise components:

```text
ϵ : FF => GG
ϵ[k] : FF[k] => GG[k]
ϵ[k](u) : Hom_{D[k]}(FF[k](u), GG[k](u))
```

Basic family operations:

```text
Const_K(A)[k] = A
1_K = Const_K(1)
E^op[k] = E[k]^op
F^*E[a] = E[F[a]]
```

## 6. Dependent Sums: Total Categories

For a functorial family `E : K → Cat`, the dependent sum or total category is:

```text
Σ_K E = Σ_k E[k]
```

Its objects are dependent pairs:

```text
Obj(Σ_K E) = Σ (k : Obj K), Obj(E[k])
```

An object is written `(k,u)` with `u : E[k]`.

The hom category between two total objects is a directed dependent hom over the
base hom:

```text
Hom_{Σ E}((x,u),(y,v))
  = total category over Hom_K(x,y)
    whose fibre at f : x → y is
      Hom_{E[y]}(E[f](u), v)
```

Equivalently, an arrow `(x,u) → (y,v)` consists of:

```text
f : Hom_K(x,y)
α : Hom_{E[y]}(E[f](u), v)
```

The implementation presents this through an opposite-total convention, but the
mathematical content is exactly the base arrow plus dependent fibre arrow.

A natural family morphism `FF : E → D` induces a map on totals:

```text
Σ(FF)(k,u) = (k, FF[k](u))
```

The current kernel also exposes the canonical total arrow over a base arrow:

```text
sigma_transport(E,p,u) : (x,u) → (y,E[p](u))
```

and the action of a Sigma map on such arrows:

```text
Σ(FF)[sigma_transport(E,p,u)]
  = sigma_map_transport(FF,p,u).
```

These are now definitions over the smaller Sigma-arrow constructor for total
arrows as `(base arrow, fibre arrow)` pairs, not additional axioms.

The first projection is a functor:

```text
π₁ : Σ_k E[k] → K
π₁(k,u) = k
```

For a constant family, the expected non-dependent sum is the product:

```text
Σ_K Const_K(A) = K × A
```

The current v3.2 file represents this by the direct normal form:

```text
Sigma_cat(Const_catd K A) ↪ Product_cat K A
```

The product projections have the expected readings:

```text
π₁ : K × A → K
π₂ : K × A → A
```

Product-valued functors now use the product normal form:

```text
Functor(X, A × B) = Functor(X,A) × Functor(X,B)
```

The projection functors are stable computational heads:

```text
Product_projL_func(A,B) : A × B → A
Product_projR_func(A,B) : A × B → B
```

Projection computation is consumer-oriented:

```text
π₁(H[i]) = (π₁ H)[i]
π₁(eta[i]) = (π₁ eta)[i]
π₁(eta[p]) = (π₁ eta)[p]
```

and homs reduce pointwise:

```text
Hom_{K×A}((x,u),(y,v)) = Hom_K(x,y) × Hom_A(u,v)
```

## 7. Dependent Products: Section Categories

For a functorial family `E : K → Cat`, the dependent product is the category of
sections:

```text
Π_K E = Π_k E[k]
```

An object `s : Π_K E` assigns:

```text
s[k] : E[k]
```

and carries coherent action over base arrows. For a base arrow `f : x → y`, the
section has a comparison arrow:

```text
s[f] : Hom_{E[y]}(E[f](s[x]), s[y])
```

For a constant family, sections are ordinary functors:

```text
Π_K Const_K(A) = Functor(K,A)
```

and evaluation of a section in the constant-family case agrees with ordinary
functor application:

```text
F[k] as a section = F[k] as an ordinary functor value
```

In `emdash3_2.lp`, this is represented by the rewrite
`Pi_cat (Const_catd K A) ↪ Functor_cat K A` and by an assertion equating
`piapp0 F k` with `fapp0 F k` in that case.

Conceptually, a section should also determine a functor into the total
category:

```text
section_total(s) : K → Σ_K E
section_total(s)(k) = (k, s[k])
π₁ ∘ section_total(s) = id_K
```

This construction is not currently exposed as a named primitive in v3.2. It is
a useful future facade: it would let section action be understood through the
same Sigma-category infrastructure used for total-category arrows. The current
implementation instead exposes the direct section action `s[f]`, with the
dependent hom construction as the shared internal architecture.

## 8. Arrows Between Sections

In non-directed HoTT notation one might expect:

```text
Hom_{Π E}(s,t) = Π_k Hom_{E[k]}(s[k],t[k])
```

For a directed base `K`, this pointwise slogan is incomplete. The components
must be natural with respect to all arrows of `K`.

The directed form used in v3.2 is:

```text
Hom_{Π E}(s,t)
  = natural family transformations from s to t
```

Pointwise, such a transformation `α : s => t` still has components:

```text
α[k] : Hom_{E[k]}(s[k], t[k])
```

but these components are constrained by naturality over every base arrow
`f : x ->^K y`. This is why the implementation uses `Transfd`, not a naive
pointwise dependent product of homs.

When the base is non-directed or only path-like, the distinction between
"functorial in k" and "natural in k" collapses. In the directed theory, it is
essential.

## 9. Dependent Homs And Fibre Transport

Given a family `E : K → Cat`, an object `u : E[x]`, and a base arrow
`f : x → y`, the theory has covariant fibre transport:

```text
E[f](u) : E[y]
```

The covariant transport of the object `u` is represented by a functor:

```text
transport_{E,x,u,y} : Hom_K(x,y) → E[y]
transport_{E,x,u,y}(f) = E[f](u)
```

The dependent hom construction is contravariant in the base hom. It is a
category-valued functor:

```text
homd_E(x,u,y,v) : Hom_K(x,y)^op → Cat
homd_E(x,u,y,v)[f]
  = Hom_{E[y]}(E[f](u), v)
```

Here "packages" means that `homd_E(x,u,y,v)` is not merely a pointwise formula:
it is one functorial object carrying the object, arrow, and higher action of
dependent fibre arrows over the base hom.

### Simplicial Reading

The same construction has a simplicial/Grothendieck reading. The Sigma total
over `homd_E(x,u,y,v)` packages a base arrow `f : x → y` together with a fibre
arrow `E[f](u) → v`, so it is a cell living over a chosen base edge. Ordinary
`hom_int`, after fixing a source object `W`, gives the first triangle/surface
presentation over an edge; dependent `homd_E`, after fixing `x,u`, is the
dependent iteration step. When the family itself is hom-shaped, this
Sigma-of-hom pattern supplies the next "cell over a cell" layer. This is an
interpretation of the existing hom/Sigma architecture, not a separate primitive
or rewrite surface.

This also motivates a recurring v3.2 implementation idiom: when one endpoint
of a hom varies by a functor, write the family as a hom-indexed family rather
than as a raw composition of endpoint functors. For example, for `f : A ⊢ B`,
the family:

```text
b ↦ (a ↦ Hom_B(b,f[a]))
```

is the internal package:

```text
hom_int B A f : Op_cat B ⊢ Catd_cat A.
```

This packages the pre/postcomposition actions under the hom constructor, which
is better aligned with cut-elimination than first introducing an explicit
`comp_cat*` pipeline and later trying to fold it away.

More generally, dependent homs can be formed along a natural family morphism
`FF : D → E`, allowing endpoint data in different families. The endpoint form
specializes to the identity-family case above.

This same dependent hom architecture is shared by total-category homs and
section action:

```text
Hom_{Σ E}((x,u),(y,v))
  uses the total category over homd_E(x,u,y,v)

s[f] : homd_E(x,s[x],y,s[y])[f]
```

or, unfolded:

```text
s[f] : Hom_{E[y]}(E[f](s[x]), s[y])
```

A future named `section_total(s) : K → Σ_K E` would make this sharing more
visible at the presentation level, but the common core is already the
dependent-hom construction.

## 10. Mixed-Variance Families

Several useful families are mixed-variance. If:

```text
A : K^op → Cat
B : K → Cat
```

then the pointwise functor family is:

```text
Functor_catd(A,B)[k] = Functor(A[k], B[k])
```

The mixed variance is in the two inputs: precomposition in the source family is
contravariant, while postcomposition in the target family is covariant.

For one family `E : K → Cat` and two sections:

```text
X : Π_k E[k]^op
Y : Π_k E[k]
```

the fibrewise hom family is:

```text
Hom_catd(E,X,Y)[k] = Hom_{E[k]}(X[k], Y[k])
```

For two families of functors, the fibrewise transformation family has the same
mixed-variance shape. A source section `FF` is read in the opposite of the
functor family, and a target section `GG` is read in the original functor
family:

```text
FF : Π_k Functor(A[k],B[k])^op
GG : Π_k Functor(A[k],B[k])
Transf_catd(A,B,FF,GG)[k] = Transf(FF[k], GG[k])
```

These pointwise constructions are useful, but they do not replace the full
natural transformation structure when arrows over the base must be tracked.

## 11. Basic Sigma/Pi Operations And Adjunction Shadows

The active v3.2 implementation now includes a basic first-class ordinary
functor adjunction interface. For categories `R` and `L`, an adjunction package

```text
J : Adjunction(R,L)
```

has stable projections:

```text
left_adj_func(J)     : R ⊢ L
right_adj_func(J)    : L ⊢ R
unit_adj_transf(J)   : id_R => right(J) o left(J)
counit_adj_transf(J) : left(J) o right(J) => id_L
```

The package also has the two component-level triangle cut-elimination rules:

```text
counit[f] o left(unit[g]) -> f o left(g)
right(counit[g]) o unit[f] -> right(g) o f
```

This is intentionally not the old v2 parameterized `adj` interface with
projection/evidence-irrelevance unification rules. The v3.2 form is a
first-class package with stable projection heads; parameterized bridges can be
added later only if a concrete theorem needs them.

The current theory includes the expected basic operations:

```text
sigma_intro_E : E → Const_K(Σ_k E[k])
sigma_intro_E[k](u) = (k,u)
```

```text
pi_eval_E : Const_K(Π_k E[k]) → E
pi_eval_E[k](s) = s[k]
```

```text
const_section_{K,A} : A → Π_K Const_K(A)
const_section_{K,A}(a) = const(a)
```

Here `const(a)` is the constant functor/section with value `a`:

```text
const(a)[k] = a
```

When `K = 1`, this specializes to the ordinary object functor:

```text
const_section_{1,A}(a) = Obj_func(a) : 1 → A
```

In the implementation, `Obj_func(a)` is a defined alias for the terminal-domain
constant functor `Const_func(1,A,a)`.

Pullback of sections along a base functor is also present:

```text
section_pullback_F : Π_b E[b] → Π_a E[F[a]]
section_pullback_F(s)[a] = s[F[a]]
```

These are currently basic operations and beta laws, not a completed general
adjunction package. They should be read as visible instances or shadows of the
expected future dependent adjunctions along a functor `F : A → B`:

```text
Σ_F ⊣ F^* ⊣ Π_F
```

Some higher action/coherence rules for these helpers remain future work. The
object-level beta laws above are the current intended reading.

## 12. Synthetic Path Induction

For a category `Z` and source object `x : Z`, the outgoing-path category is:

```text
PathOut_Z(x) = Σ y : Z, Hom_Z(x,y)
```

An object is written `(y,p)`, where `p : Hom_Z(x,y)`. The reflexive outgoing
path is:

```text
reflout_x = (x,id_x).
```

A path-induction motive at fixed `x` is a directed family:

```text
E : PathOut_Z(x) → Cat.
```

The fixed-`x` eliminator has the expected dependent-product shape:

```text
path_ind_sec(Z,x,E,u) : Π q : PathOut_Z(x), E[q]
u : E[reflout_x]
```

and computes at `(y,p)` by transporting `u` along the canonical arrow:

```text
rho_{x,y,p} : reflout_x → (y,p)
```

In the current implementation this arrow is not axiomatic. It is the canonical
Sigma transport arrow for the representable family:

```text
rho_{x,y,p} =
  sigma_transport_arrow(Rep_Z(x), p, id_x)
```

using the endpoint computation:

```text
Rep_Z(x)[p](id_x) = p.
```

The canonical Sigma transport arrow itself is defined from the fundamental
Sigma-hom characterization: a total arrow is a base arrow plus a fibre arrow,
and `sigma_transport_arrow(E,p,u)` is the special case with the identity fibre
arrow at `E[p](u)`.

The primary internalized theorem is the telescope form over varying `x`:

```text
PathInd_transfd(Z)
  : x :^n Z ; PathOutReflEval_Z[x] => PathOutPi_Z[x]
```

where:

```text
PathOutReflEval_Z[x][E] = E[reflout_x]
PathOutPi_Z[x][E]       = Π q : PathOut_Z(x), E[q].
```

Its component is the fixed-`x` theorem:

```text
PathInd_transfd(Z)[x] = PathInd_func(Z,x)
PathInd_transfd(Z)[x][E](u) = path_ind_sec(Z,x,E,u).
```

The fixed-`x` rho-section is the path induction instance for the representable
motive on `PathOut_Z(x)`:

```text
pathout_refl_arrow_sec(x)
  = path_ind_sec(Rep_{PathOut_Z(x)}((x,id_x)), id_{(x,id_x)}),
pathout_refl_arrow_sec(x)[(y,p)] = rho_{x,y,p}.
```

The Sigma-total presentation is now derived from this telescope theorem:

```text
PathInd_funcd(Z) =
  Sigma_transfd_funcd(PathInd_transfd(Z)).
```

The generic uncurrying law is:

```text
Sigma_transfd_funcd(eta)[(k,r)] = eta[k][r].
```

For canonical total arrows, the intended internal normal form is the existing
off-diagonal transfor component:

```text
Sigma_transfd_funcd(eta)[sigma_transport(R,p,r)]
  is represented by
tapp1_fapp0(Sigma_transfd_funcd(eta), sigma_transport(R,p,r)).
```

The kernel deliberately does not fold this to one external route around a
naturality square, such as `T[p](eta[x](c))`. Action over arbitrary Sigma-total
arrows remains outside the immediate milestone.

This keeps the theorem surface sequential:

```text
(x :^n Z) →
  (E :^n Catd(PathOut_Z(x))) →
    E[reflout_x] → Π q : PathOut_Z(x), E[q]
```

while still providing the compiled Sigma-total form needed by existing
transport and total-category infrastructure.

## 13. What Is Deferred

The current foundations intentionally do not yet include:

- HoTT computation rules for equality in Sigma types.
- HoTT computation rules for equality in Pi types.
- Universe equality or Voevodsky-style univalence.
- Equivalence/isomorphism theory for categories.
- Pushouts, joins, or higher inductive categories.
- A finalized surface syntax for the future proof assistant.
- Full coherence APIs for every Sigma/Pi helper.
- A named `section_total(s) : K → Σ_K E` construction and its projection laws.
- Full product/curry adjunction coherence for `Product_cat`, beyond the
  current product normal form, projection computation, and functor-level
  curry/uncurry action laws.
- General dependent adjunctions `Σ_F ⊣ F^* ⊣ Π_F` along arbitrary base
  functors.

These are compatible future directions. The current v3.2 milestone is the
directed categorical foundation: universes as categories, functorial
Cat-valued families, total categories, section categories, dependent homs, and
section action over base arrows.

## 14. Implementation Glossary

This table maps the mathematical notation above to the current `emdash3_2.lp`
vocabulary.

| Mathematical notation | Current implementation name |
| --- | --- |
| `Cat` | `Cat_cat` as the category of categories; `Cat` as the meta-class of categories |
| `Obj(A)` | `Obj A` |
| `Hom_A(x,y)` | `Hom_cat A x y` |
| `Functor(A,B)` | `Functor_cat A B` / `Functor A B` |
| `F[x]` | `fapp0 F x` |
| `F[f]` | `fapp1_fapp0 F f` |
| `Transf(F,G)` | `Transf_cat F G` / `Transf F G` |
| `ϵ[x]` | `tapp0_fapp0 x ϵ` |
| `Catd(K)` | `Catd_cat K` / `Catd K` |
| `E[k]` | `Fibre_cat E k` |
| `F^*E` | `Pullback_catd E F` |
| `Const_K(A)` | `Const_catd K A` |
| `E^op` | `Op_catd E` |
| `Π_k E[k]` | `Pi_cat E` |
| `s[k]` | `piapp0 s k` |
| `s[f]` | `piapp1_fapp0 s f` |
| `Π_K Const_K(A) = Functor(K,A)` | rewrite for `Pi_cat (Const_catd K A)` |
| `const_section_{K,A}` | `const_section_func K A` |
| `const_section_{K,A}(a)` | `Const_func K A a` |
| `Σ_k E[k]` | `Sigma_cat E` |
| `(k,u)` | `Struct_sigma k u` |
| `π₁` | `Sigma_proj1_func E` |
| `Σ(FF)` | `sigma_map_func FF` |
| `E[f](u)` | `fapp0 (fib_cov_tapp0_func E x y u) f` |
| `homd_E(x,u,y,v)` | `homd_ (id_funcd E) x u y v` |
| Natural family morphisms | `Functord_cat E D` / `Functord E D` |
| Natural family transformations | `Transfd_cat FF GG` / `Transfd FF GG` |
| `Functor_catd(A,B)` | `Functor_catd A B` |
| `Hom_catd(E,X,Y)` | `Hom_catd E X Y` |
| `Transf_catd(A,B,FF,GG)` | `Transf_catd A B FF GG` |
| `PathOut_Z(x)` | `PathOut_cat Z x` |
| `(y,p) : PathOut_Z(x)` | `pathout_obj Z x y p` |
| `reflout_x` | `pathout_refl_obj Z x` |
| `rho_{x,y,p}` | `pathout_refl_arrow Z x y p` |
| `PathInd_transfd(Z)` | `PathInd_transfd Z` |
| `Sigma_transfd_funcd(eta)` | `Sigma_transfd_funcd eta` |
| Sigma-total path induction | `PathInd_funcd Z` |
| `section_total(s)` | future presentation-level facade; not currently named |
| `K × A` | `Product_cat K A`; also the normal form of `Sigma_cat(Const_catd K A)` |
| `π₁ : K × A → K` | `Product_projL_func K A` |
| `π₂ : K × A → A` | `Product_projR_func K A` |

The implementation contains additional projection heads to make Lambdapi
normalization reliable. They are part of the checked kernel engineering, not
part of the conceptual surface theory described in this note.
