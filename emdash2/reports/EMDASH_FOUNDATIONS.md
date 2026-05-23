# emdash Foundations

Draft status: this document is a mathematician-facing reading guide for the
current `emdash3_2.lp` theory. It presents the intended mathematics in ordinary
category/type-theory notation and deliberately suppresses most Lambdapi rewrite
engineering details.

The implementation is still evolving. This note describes the current directed
categorical foundation, not a finished proof assistant surface language.

## 1. Reading Guide

The central idea is to treat categories, functors, transformations, dependent
families of categories, dependent sums, dependent products, and dependent homs
as one computational theory.

The notation is intentionally close to dependent type theory:

```text
F : A -> B              ordinary functor
F[x]                    action of F on an object
F[f]                    action of F on an arrow
E : K -> Cat            directed family of categories over K
E[k]                    fibre category at k
Sigma_k E[k]            total category of a family
Pi_k E[k]               category of sections of a family
s[k]                    value of a section at k
s[f]                    action of a section over f : x -> y
```

The word "directed" matters. The base `K` is a category with real arrows, not
just a type of points. Consequently, pointwise constructions must usually carry
naturality data over base arrows.

## 2. Categories And Hom-Categories

A category `A` has:

```text
Obj(A)                  objects of A
Hom_A(x,y)              category of arrows from x to y
id_x                    identity arrow
g o f                   composition
```

The hom between two objects is itself a category. This is the basic
omega-categorical shape: arrows, higher arrows, and higher comparisons are
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
F : A -> B
F[x] : Obj(B)
F[f] : Hom_B(F[x],F[y])
```

The theory also has transformation categories:

```text
Transf(F,G)
```

whose objects are transformations from `F` to `G`. A transformation `epsilon :
F => G` has point components:

```text
epsilon[x] : Hom_B(F[x],G[x])
```

## 5. Directed Families

A directed family of categories over `K` is a functor:

```text
E : K -> Cat
```

The theory writes this as a category-valued family:

```text
E : Catd(K)
E[k] = fibre of E at k
```

A morphism of directed families is a natural family of functors:

```text
FF : E -> D
FF[k] : E[k] -> D[k]
```

A transformation between such family morphisms has fibrewise components:

```text
epsilon : FF => GG
epsilon[k] : FF[k] => GG[k]
epsilon[k](u) : Hom_{D[k]}(FF[k](u), GG[k](u))
```

Basic family operations:

```text
Const_K(A)[k] = A
1_K = Const_K(1)
E^op[k] = E[k]^op
F^*E[a] = E[F[a]]
```

## 6. Dependent Sums: Total Categories

For a directed family `E : K -> Cat`, the dependent sum or total category is:

```text
Sigma_K(E) = Sigma_k E[k]
```

Its objects are dependent pairs:

```text
Obj(Sigma_K(E)) = Sigma (k : Obj K), Obj(E[k])
```

An object is written `(k,u)` with `u : E[k]`.

The hom category between two total objects is a directed dependent hom over the
base hom:

```text
Hom_{Sigma E}((x,u),(y,v))
  = total category over Hom_K(x,y)
    whose fibre at f : x -> y is
      Hom_{E[y]}(E[f](u), v)
```

Equivalently, an arrow `(x,u) -> (y,v)` consists of:

```text
f : Hom_K(x,y)
alpha : Hom_{E[y]}(E[f](u), v)
```

The implementation presents this through an opposite-total convention, but the
mathematical content is exactly the base arrow plus dependent fibre arrow.

A family morphism `eta : E -> D` induces a map on totals:

```text
Sigma(eta)(k,u) = (k, eta[k](u))
```

The first projection is a functor:

```text
pi1 : Sigma_k E[k] -> K
pi1(k,u) = k
```

## 7. Dependent Products: Section Categories

For a directed family `E : K -> Cat`, the dependent product is the category of
sections:

```text
Pi_K(E) = Pi_k E[k]
```

An object `s : Pi_K(E)` assigns:

```text
s[k] : E[k]
```

and carries coherent action over base arrows. For a base arrow `f : x -> y`,
the section has a comparison arrow:

```text
s[f] : Hom_{E[y]}(E[f](s[x]), s[y])
```

For a constant family, sections are ordinary functors:

```text
Pi_K(Const_K(A)) = Functor(K,A)
```

and section evaluation agrees with functor application:

```text
s[k] = s[k] as an ordinary functor value.
```

## 8. Arrows Between Sections

In non-directed HoTT notation one might expect:

```text
Hom_{Pi E}(s,t) = Pi_k Hom_{E[k]}(s[k],t[k])
```

For a directed base `K`, this pointwise slogan is incomplete. The components
must be natural with respect to all arrows of `K`.

The directed form used in v3.2 is:

```text
Hom_{Pi E}(s,t)
  = displayed natural transformations from s to t
```

Pointwise, such a transformation `alpha : s => t` still has components:

```text
alpha[k] : Hom_{E[k]}(s[k], t[k])
```

but these components are constrained by naturality over every base arrow
`f : x -> y`. This is why the implementation uses displayed transformations,
not a naive pointwise dependent product of homs.

When the base is non-directed or only path-like, the distinction between
"functorial in k" and "natural in k" collapses. In the directed theory, it is
essential.

## 9. Dependent Homs And Fibre Transport

Given a family `E : K -> Cat`, an object `u : E[x]`, and a base arrow
`f : x -> y`, the theory has covariant fibre transport:

```text
E[f](u) : E[y]
```

This is represented internally by a functor:

```text
Hom_K(x,y) -> E[y]
f |-> E[f](u)
```

The dependent hom construction packages the category of fibre arrows over a
base arrow:

```text
homd_E(x,u,y,v)[f]
  = Hom_{E[y]}(E[f](u), v)
```

More generally, dependent homs can be formed along a displayed/family morphism
`FF : D -> E`, allowing endpoint data in different families. The endpoint form
specializes to the identity-family case above.

The section action formula is then:

```text
s[f] : homd_E(x,s[x],y,s[y])[f]
```

or, unfolded:

```text
s[f] : Hom_{E[y]}(E[f](s[x]), s[y])
```

## 10. Mixed-Variance Families

Several useful families are mixed-variance. If:

```text
A : K^op -> Cat
B : K -> Cat
```

then the pointwise functor family is:

```text
Functor_catd(A,B)[k] = Functor(A[k], B[k])
```

For one family `E : K -> Cat` and two sections:

```text
X : Pi_k E[k]^op
Y : Pi_k E[k]
```

the fibrewise hom family is:

```text
Hom_catd(E,X,Y)[k] = Hom_{E[k]}(X[k], Y[k])
```

For two families of functors `FF, GG`, the fibrewise transfor family is:

```text
Transf_catd(A,B,FF,GG)[k] = Transf(FF[k], GG[k])
```

These pointwise constructions are useful, but they do not replace the full
displayed/natural transformation structure when arrows over the base must be
tracked.

## 11. Generic Sigma/Pi Operations

The current theory includes the expected generic operations:

```text
sigma_intro_E : E -> Const_K(Sigma_k E[k])
sigma_intro_E[k](u) = (k,u)
```

```text
pi_eval_E : Const_K(Pi_k E[k]) -> E
pi_eval_E[k](s) = s[k]
```

```text
const_section : A -> Pi_k A
const_section(a)[k] = a
```

```text
section_pullback_F : Pi_b E[b] -> Pi_a E[F[a]]
section_pullback_F(s)[a] = s[F[a]]
```

Some higher action/coherence rules for these helpers remain future work. The
object-level beta laws above are the current intended reading.

## 12. What Is Deferred

The current foundations intentionally do not yet include:

- HoTT computation rules for equality in Sigma types.
- HoTT computation rules for equality in Pi types.
- Universe equality or Voevodsky-style univalence.
- Equivalence/isomorphism theory for categories.
- Pushouts, joins, or higher inductive categories.
- A finalized surface syntax for the future proof assistant.
- Full coherence APIs for every Sigma/Pi helper.

These are compatible future directions. The current v3.2 milestone is the
directed categorical foundation: universes as categories, directed
Cat-valued families, total categories, section categories, dependent homs, and
section action over base arrows.

## 13. Implementation Glossary

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
| `epsilon[x]` | `tapp0_fapp0 x epsilon` |
| `Catd(K)` | `Catd_cat K` / `Catd K` |
| `E[k]` | `Fibre_cat E k` |
| `F^*E` | `Pullback_catd E F` |
| `Const_K(A)` | `Const_catd K A` |
| `E^op` | `Op_catd E` |
| `Pi_k E[k]` | `Pi_cat E` |
| `s[k]` | `piapp0 s k` |
| `s[f]` | `piapp1_fapp0 s f` |
| `Sigma_k E[k]` | `Sigma_cat E` |
| `(k,u)` | `Struct_sigma k u` |
| `pi1` | `Sigma_proj1_func E` |
| `Sigma(eta)` | `sigma_map_func eta` |
| `E[f](u)` | `fapp0 (fib_cov_tapp0_func E x y u) f` |
| `homd_E(x,u,y,v)` | `homd_ (id_funcd E) x u y v` |
| Displayed family morphisms | `Functord_cat E D` / `Functord E D` |
| Displayed transformations | `Transfd_cat FF GG` / `Transfd FF GG` |
| `Functor_catd(A,B)` | `Functor_catd A B` |
| `Hom_catd(E,X,Y)` | `Hom_catd E X Y` |
| `Transf_catd(A,B,FF,GG)` | `Transf_catd A B FF GG` |

The implementation contains additional projection heads to make Lambdapi
normalization reliable. They are part of the checked kernel engineering, not
part of the conceptual surface theory described in this note.
