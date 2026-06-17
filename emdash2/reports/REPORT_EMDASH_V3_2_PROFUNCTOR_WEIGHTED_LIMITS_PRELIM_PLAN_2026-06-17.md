# EMDASH v3.2 Profunctor, Weighted Limit, And Duality Preliminary Plan

Date: 2026-06-17

Status: preliminary implementation plan. No implementation from this report has
been attempted in `emdash3_2.lp` yet.

## Scope

This report plans the v3.2 reimplementation of the useful ideas from the
obsolete `cartierSolution13.lp` sections:

```text
INDUCTIVE DATA TYPE, EXAMPLE OF THE JOIN CATEGORY
TENSOR (AND KAN EXTENSIONS AND CO-YONEDA REDUCTIONS) HOM FOR MODULES
INTERNAL HOM (IMPLICATION), LAMBDA CALCULUS FOR MODULES
WEIGHTED LIMITS, RIGHT ADJOINTS PRESERVE WEIGHTED LIMITS
DUALITY, COVARIANT VS CONTRAVARIANCE, LEFT ADJOINTS PRESERVE COLIMITS
```

The goal is not to port the old `mod` layer literally. The old file mixed
good design ideas with obsolete syntax, incomplete naturality, heavy rewrite
rules, and some incorrect duality attempts. In v3.2 the intended owner is the
current directed-family architecture:

```text
Catd_cat(K)
Pullback_catd(E,F)
Const_catd(K,A)
Op_cat, Op_func, Op_catd, Op_funcd
Product_cat(A,B)
Hom_catd(E,X,Y)
Functord_cat(E,D)
Transf_catd(A,B,FF,GG)
Adjunction(R,L)
```

The current `Pi_along_func` and displayed structural-logic plans are supporting
references only. They should be implemented during this work only when a
specific profunctor construction needs them.

## Review Assessment 2026-06-17

The global shape of this plan is coherent with the current v3.2 architecture:

```text
profunctor facade
  -> shaped profunctor elements and transformations
  -> primitive tensor and named co-Yoneda maps
  -> implication/eval/lambda
  -> weighted limits
  -> adjunction bridge
  -> op-duality theorem for left adjoints and colimits
```

The main correctness constraint is that every pointwise formula must be backed
by a functorial owner. For profunctors this means:

```text
R[a,b]                       object/fibre formula only
R[(p,q)]                     required base-arrow action
Prof_transf_cat(...)         natural family of fibre functors
Prof_hom(F,R,G)              transformation out of the unit profunctor
```

The main feasibility result from a temporary probe is positive: the semantic
Phase 1 substrate can be expressed with the current kernel. In particular, a
probe typechecked definitions equivalent to:

```text
Product_map_func(F,G)
Prof_base(A,B) := Product_cat (Op_cat A) B
Unit_prof(F,G) := Hom_catd(Const_catd(Prof_base A B,X), source, target)
Prof_reindex(R,F,G) := Pullback_catd R (Product_map_func(Op_func F,G))
Prof_transf_cat(R',F,R,G) := Functord_cat R' (Prof_reindex R F G)
Prof_hom(F,R,G) := Obj(Prof_transf_cat(Unit_prof(id_I,id_I),F,R,G))
```

The same probe checked:

```text
Unit_prof(F,G)[a,b] = Hom_X(F[a],G[b])
Prof_reindex(R,F,G)[a',b'] = R[F[a'],G[b']]
```

Implementation detail from the probe: early declarations should use reduced
canonical types such as:

```text
τ (Catd (Prof_base A B))
```

rather than relying everywhere on a readability alias:

```text
τ (Prof A B)
```

The alias is still useful for comments and later APIs, but the first landed
definitions should keep canonical `Catd(base)` types in symbol declarations and
diagnostic assertions until unification behavior is proven stable.

## Design Reassessment 2026-06-17

The old Cartier design systematically worked with functor-shaped objects:

```text
F : I -> A
G : I -> B
hom F R G
```

instead of only point objects:

```text
a : Obj A
b : Obj B
R[a,b]
```

This should not be ported blindly. In v3.2 the correct layering is:

```text
1. Fibre-direct layer:
   R : Catd(A^op x B)
   Fibre_cat R (a,b)
   fapp1_func R / fapp1_fapp0 R

2. Shaped/equipment layer:
   Prof_transf_cat(R',F,R,G)
   Prof_hom(F,R,G)
   tensor/int-hom/weighted-limit universal maps
```

The fibre-direct layer should be used whenever a construction only needs a
pointwise category or the existing directed-family arrow action. The shaped
layer is justified when a theorem must be natural in a test category `I`, or
when the statement is genuinely an equipment/proarrow cell over functors
`F : A' -> A` and `G : B' -> B`.

Consequently, `Prof_hom` is not a replacement for direct access to:

```text
Fibre_cat R (a,b)
catd_transport_func(R,(p,q))
```

It is the naturality/universal-property layer over those fibres. Weighted
limits and adjunction preservation really do need this layer because their
universal properties quantify over shaped probes `M : I -> B`, not just over
terminal-shaped points.

The implementation should therefore avoid duplicating the whole ordinary
category theory inside profunctors. Prefer this order:

```text
define fibre-direct semantic owner first;
add a shaped facade only when a universal property needs it;
add a primitive stable head only when a downstream rewrite needs that head.
```

Potential missing core/kernel primitives exposed by this review:

```text
Product_mapR_func_func or Product_swap_func, if duality needs right-side maps;
Product_map_func only as a stable helper if two-variable product maps recur;
Op_transf for ordinary transformations;
Op_adjunction for first-class adjunctions;
adjunction hom-isomorphism as a profunctor transformation bridge;
coend/coinserter infrastructure if tensor is ever made semantic;
Initial_cat or empty hom categories for full collage/join semantics.
```

At present, only the first four are near-term kernel candidates. Coends and
initial homs are larger foundations and should not block the symbolic
profunctor calculus.

## Stable-Head Policy

Use three implementation classes.

### Defined Readability Aliases

These should start as definitions/aliases, not primitive stable heads:

```text
Prof_base(A,B)
Prof_cat(A,B)
Prof(A,B)
Product_map_func(F,G), if needed only for fixed external F,G
Cov_repr_prof(F)
Con_repr_prof(G)
Prof_hom_cat(F,R,G)
Prof_hom(F,R,G), initially
```

Reason: each has a clear semantic owner in existing infrastructure
(`Product_cat`, `Catd_cat`, `Pullback_catd`, `Hom_catd`, or
`Functord_cat`). Adding injective heads too early would create a parallel API
with extra unification commitments.

### Semantic Constructors That May Need Stable Heads Later

These should be implemented semantically first, but are plausible future stable
heads if downstream rewrite rules need a clean discriminator:

```text
Unit_prof(F,G)
Prof_reindex(R,F,G)
Prof_transf_cat(R',F,R,G)
Product_swap_func(A,B)
Product_mapR_func_func(A,B,B')
Product_map_func(F,G), if used by op-duality/reindexing rules repeatedly
```

The criterion is operational, not aesthetic: add a stable head only after a
probe shows that a downstream rule cannot reliably match or compute through
the semantic body.

### Primitive Calculus Heads

These likely need primitive stable heads from the beginning:

```text
Prof_tensor(R,S)
Prof_imply_cov(O,Q)
Prof_imply_con(Q,O)
Prof_eval_cov_transf / Prof_lambda_cov_transf
WeightedLimit_cov / WeightedLimit_con
weighted_limit_*_univ_transf
weighted_limit_*_cone_transf
Op_transf
Op_adjunction
Op_weighted_limit_cov / Op_weighted_limit_con
```

Reason: v3.2 does not currently have semantic coends, closed bicategory
structure, or op-dual universal-property transport from which these can be
definitionally derived. Their computation should be governed by explicit
beta/eta and naturality rules.

## Internalization Strategy

The Cartier port must track which variables are merely Lambdapi parameters and
which variables have been internalized as functorial arguments. The v3.2 SOP is
incremental:

```text
external fixed symbol
  -> functorial package in one variable
  -> functorial package in several variables
  -> projection rules back to the external symbol
  -> higher hom-action/projection rules only when demanded by checks
```

Existing examples:

```text
Product_cat(A,B)
Product_cat_func[A][B] = A x B
Product_cat_fapp1_tapp0_func(F,B) = F * 1_B
Product_mapL_func_func(A,A',B)[F] = F * 1_B

Pullback_catd(E,F)
Pullback_catd_func(F)[E] = F^*E
Catd_cat_func[F] = Pullback_catd_func(F)

Pi_cat(E)
Pi_func(K)[E] = Pi_cat(E)
Pi_int_funcd[K] = Pi_func(K)
Pi_pullback_funcd(G)[x] = Pi_func(G[x])
```

The profunctor port should follow this pattern. Do not start with the most
internal possible symbol unless a concrete computation already needs it.

### Provisional Internalization Ladder

For the profunctor facade:

```text
Level 0:
  Prof_base(A,B)
  Prof_cat(A,B)
  R : Catd(Prof_base(A,B))

Level 1:
  Prof_reindex_func(F,G)
    : Prof_cat(A,B) -> Prof_cat(A',B')
  Prof_reindex_func(F,G)[R] = Prof_reindex(R,F,G)

Level 2:
  internalize in F and/or G only if repeated reindexing/naturality rules need it
```

`Prof_reindex_func(F,G)` is the first likely internalized helper because it is
mostly already supplied by:

```text
Pullback_catd_func(Product_map_func(Op_func F,G)).
```

The hard part is not internalizing in `R`; the hard part is deciding whether
`Product_map_func(Op_func F,G)` itself needs a stable two-variable product-map
owner.

For the unit profunctor:

```text
Level 0:
  Unit_prof(F,G) : Prof(A,B)

Level 1:
  Unit_prof_func(F)
    : (B -> X) -> Prof_cat(A,B)
  or
  Unit_prof_func_right(G)
    : (A -> X)^op -> Prof_cat(A,B)

Level 2:
  Unit_prof_func2
    : (A -> X)^op x (B -> X) -> Prof_cat(A,B)
```

The variance is important:

```text
Unit_prof(F,G)[a,b] = Hom_X(F[a],G[b])
```

is contravariant in `F` and covariant in `G`. Therefore a fully internalized
two-variable owner should have source morally:

```text
Product_cat (Op_cat (Functor_cat A X)) (Functor_cat B X)
```

and target:

```text
Prof_cat(A,B).
```

This is exactly the kind of internalization that should be delayed until a
downstream theorem needs it. The first implementation can use the semantic
`Hom_catd` owner and later add `Unit_prof_func2` with projection rules:

```text
Unit_prof_func2[(F,G)] = Unit_prof(F,G)
Unit_prof_func2[(alpha,beta)] = pre/postcomposition on hom fibres
```

For tensor:

```text
Level 0:
  Prof_tensor(R,S) : Prof(A,C)

Level 1:
  Prof_tensor_func(A,B,C)
    : Prof_cat(A,B) x Prof_cat(B,C) -> Prof_cat(A,C)
  Prof_tensor_func[(R,S)] = Prof_tensor(R,S)

Level 2:
  equipment-level tensor over reindexing spans:
  Tensor_cov_transf / Tensor_con_transf analogues
```

The fixed-base tensor functor is the internal form of the ordinary bifunctor
on profunctor categories. The old Cartier transformation constructors are more
general: they are equipment cells over functors between bases. Those should
not replace the fixed-base functor; they should sit above it.

For implication:

```text
Level 0:
  Prof_imply_cov(O,Q)
  Prof_imply_con(Q,O)

Level 1:
  Prof_imply_cov_func(Q)
    : Prof_cat(A,B) -> Prof_cat(A,C)
  Prof_imply_con_func(Q)
    : Prof_cat(A,B) -> Prof_cat(C,B)

Level 2:
  two-variable closed-structure functors and equipment-level naturality
```

For weighted limits:

```text
Level 0:
  WeightedLimit_cov(F,W,L) : TYPE

Level 1:
  universal/cone maps functorial in the probe M : I -> B

Level 2:
  naturality of the weighted-limit package in F, W, L, and adjunction data
```

The universal property is inherently shaped: even if the limit object is a
point or point-family, the statement quantifies over all probes `M : I -> B`.
So weighted limits are one of the places where the old "functors into a
category" discipline is not accidental. It expresses enriched/natural
parametricity of the universal property.

### Internalization Decision Rule

For each proposed symbol, ask:

```text
1. Is this only a pointwise/fibre formula?
   Use direct Catd/fibre infrastructure.

2. Is this a fixed-base functorial operation?
   Add a `*_func` package over `Prof_cat(...)` with fapp0/fapp1 projections.

3. Does this vary over base functors or substitutions?
   Add an equipment-level transformation constructor.

4. Does this require coends, closed bicategory structure, or a universal
   property not present in v3.2?
   Use a primitive calculus head with beta/eta rules.
```

This rule is more important than the old Cartier naming. It lets the port keep
the concrete applications while changing the architecture when v3.2 already
has a better semantic owner.

## Unit Profunctor Versus Existing Hom Infrastructure

`Unit_prof(F,G)` should not be treated as a fundamentally new hom theory. For
fixed:

```text
F : A -> X
G : B -> X
```

there are two coherent semantic presentations:

```text
1. Hom_catd presentation:
   Unit_prof(F,G)
     := Hom_catd(Const_catd(A^op x B,X), F o piL, G o piR)

2. hom_int/curry presentation:
   Unit_prof(F,G)
     := uncurry(hom_int(G) o Op_func(F))
```

where:

```text
hom_int(G) : X^op -> Catd(B)
hom_int(G)[x][b] = Hom_X(x,G[b])
```

and:

```text
(hom_int(G) o Op_func(F))[a][b] = Hom_X(F[a],G[b]).
```

A temporary probe checked that the `uncurry(hom_int(G) o Op_func(F))`
presentation computes fibrewise to:

```text
Hom_X(F[a],G[b])
```

and agrees fibrewise with the `Hom_catd` presentation. This strongly suggests
that the first implementation of `Unit_prof` should be a defined semantic
alias, not a primitive stable head.

The two presentations have different strengths:

```text
Hom_catd presentation:
  best for direct indexed-hom reading over the profunctor base A^op x B;
  packages both endpoints as sections over the same base;
  aligns with `Prof_base` and `Prof_reindex`.

hom_int/curry presentation:
  best for reusing the existing hom-action owners;
  exposes precomposition in F and postcomposition in G through hom_int,
  hom_precomp_along_*, and hom_postcomp_*;
  explains why curry/uncurry is relevant but not necessarily a new primitive.
```

Therefore the likely implementation order is:

```text
1. Define Unit_prof semantically through Hom_catd for base clarity.
2. Add checks showing its fibre formula.
3. Add a comparison/check with uncurry(hom_int(G) o Op_func(F)).
4. Only add Unit_prof_func2 if later proofs need functoriality in F and G
   as a reusable package.
```

If `Unit_prof_func2` is eventually added, it should be understood as an
internalized packaging of existing hom infrastructure:

```text
Unit_prof_func2
  : Product_cat (Op_cat (Functor_cat A X)) (Functor_cat B X)
      -> Prof_cat(A,B)
Unit_prof_func2[(F,G)] = Unit_prof(F,G)
```

Its hom-action should not invent new hom composition rules. It should project
to the existing pre/postcomposition heads where possible. In particular,
comparison with `hom_int` should drive the design of any projection rules.

Relationship to `homd_int`: `Unit_prof` is the ordinary/Cat-valued hom-family
case. `homd_int(FF)` is the displayed/dependent analogue where the endpoint
varies through a displayed functor over a base. They should remain separate
semantic owners. A future displayed profunctor/unit theory should be built by
analogy with `homd_int`, not by forcing `Unit_prof` to cover dependent
endpoints.

### Single-Argument Core Versus Binary Convenience

Refinement: the primitive/core unit-hom profunctor should probably have one
functor argument, not two.

The existing `hom_int` already has the shape:

```text
hom_int(G) : X^op -> Catd(B)
G : B -> X
hom_int(G)[x][b] = Hom_X(x,G[b])
```

Therefore the direct profunctor analogue is the right-representable/hom
profunctor:

```text
Hom_prof(G) : Prof(X,B)
Hom_prof(G)[x,b] = Hom_X(x,G[b])
```

This is the profunctor form of the existing single-argument `hom_int(G)`.
The identity/unit profunctor on `X` is the specialization:

```text
Unit_prof(X) := Hom_prof(id_X) : Prof(X,X)
```

The two-endpoint form used in the Cartier draft is then a derived
left-reindexed convenience:

```text
Hom_prof_along(F,G) : Prof(A,B)
F : A -> X
G : B -> X

Hom_prof_along(F,G)
  := Prof_reindex(Hom_prof(G), F, id_B)

Hom_prof_along(F,G)[a,b] = Hom_X(F[a],G[b]).
```

So the answer to "is the two-functor form necessary?" is:

```text
mathematically/foundationally:
  no; the single-argument hom profunctor plus left reindexing is enough.

as notation/API for weighted limits and adjunction formulas:
  probably yes as a semantic alias, because formulas such as
  Hom_prof_along(M,F) are much easier to read than an explicit reindexing
  expression.

as a primitive stable rewrite owner:
  not initially; add it only if downstream tensor/weighted-limit rules need a
  stable head that cannot be recovered from Hom_prof + Prof_reindex.
```

This also clarifies naming. The most precise split would be:

```text
Hom_prof(G) or Right_repr_prof(G)
  core single-argument right-representable profunctor.

Unit_prof(X)
  identity/unit profunctor, defined as Hom_prof(id_X).

Hom_prof_along(F,G) or Unit_prof_along(F,G)
  binary convenience, defined by left reindexing Hom_prof(G).
```

The old report shorthand `Unit_prof(F,G)` should be read as this binary
convenience unless/until we settle final names.

Temporary probe result: a primitive single-argument `Probe_Hom_prof(G)` with
the direct fibre computation:

```text
Probe_Hom_prof(G)[x,b] -> Hom_X(x,G[b])
```

typechecked. The derived binary object:

```text
Pullback_catd(Probe_Hom_prof(G), Product_cat_fapp1_tapp0_func(Op_func(F),B))
```

also typechecked as a definition. A fully normalized fibre assertion for that
derived binary expression should be added later with the landed `Prof_reindex`
surface, not forced during the naming/design probe.

Important caveat about the proposed "curry projection":

```text
curry(Hom_prof(G)) -> hom_int(G)
```

is conceptually the right comparison. But in the current v3.2 source,
`curry_func_func` is a transparent semantic composite and `curry_func` is a
defined alias, not an opaque primitive stable head. A probe showed that
Lambdapi refuses a rewrite rule headed by `curry_func` because it is defined
with `≔`; a rule against `fapp0 curry_func_func ...` is not enough to make the
expected comparison assertion reduce robustly. Therefore, if we want this
projection as computation, we should first promote or add a stable curry
projection owner. Do not assume the current curry aliases are safe rewrite
owners.

### Curried Hom Infrastructure Versus General Profunctors

There are two different questions that should not be conflated.

First, internalize the existing `hom_int` in its functor argument:

```text
hom_int(F) : X^op -> Catd(B)
```

where `F : B -> X`. A possible internal package would be:

```text
hom_int_func(X,B)
  : (B -> X) -> (X^op -> Catd(B))
hom_int_func[X,B][F] = hom_int(F)
```

This is a one-functor internalization. Its hom-action on a transformation
`eta : F => G` is postcomposition by `eta`. If this package is added, it
should probably be named something unambiguous like `hom_int_func`, not
`hom_int_int`: the latter name does not say whether one is internalizing only
the target functor argument of `hom_int`, or also adding a second endpoint
functor.

Conceptually, this one-functor package is a Yoneda-style/representable
inclusion into the curried profunctor category:

```text
Prof_curried_cat(X,B) := Functor_cat (Op_cat X) (Catd_cat B)

hom_int_func(X,B)
  : Functor_cat B X -> Prof_curried_cat(X,B)
```

Its image consists of profunctors representable in the contravariant `X`
variable. That is useful and central, but it is not the same as the category of
all profunctors.

Second, build a unit/representable profunctor from two endpoint functors:

```text
F : A -> X
G : B -> X
Unit_prof(F,G)[a,b] = Hom_X(F[a],G[b]).
```

This is a two-functor construction. It can be factored through the one-functor
package by substitution and uncurry:

```text
Unit_prof(F,G)
  = uncurry(hom_int(G) o Op_func(F)).
```

So if a later `Unit_prof_func2` exists, it should be understood as:

```text
Unit_prof_func2(F,G)
  = uncurry(hom_int_func[X,B](G) o Op_func(F))
```

morally, not as a new independent hom calculus.

The current v3.2 source already has a related two-functor internal hom-action:

```text
tapp1_int_func_transf(F,G)
  : Transf(F,G)
      -> Transf(hom_int(id_A), hom_int(G) o Op_func(F)).
```

This is evidence that the two-endpoint functorial story belongs to ordinary
hom-action infrastructure. It should be reused when designing any future
`hom_int_func` or `Unit_prof_func2` projection rules.

More precisely, `tapp1_int_func_transf` is not just the postcomposition
hom-action of `hom_int_func`. It is the richer binary hom-action:

```text
Hom_A(-,-) -> Hom_B(F- ,G-)
```

so it belongs next to the one-variable postcomposition action, not as a
replacement for it. A future `hom_int_func` may still need its own projection
head for:

```text
eta : F => G
hom_int(F) => hom_int(G)
```

unless the existing `hom_postcomp_*` heads are enough for the required checks.

However, this does not make `hom_int_func` or `Unit_prof_func2` a replacement
for general profunctors. They describe representable/unit profunctors. A
general profunctor is an arbitrary family:

```text
R : Catd(A^op x B)
```

or equivalently, in curried form:

```text
Rcur : A^op -> Catd(B).
```

The curried form is useful and closer to `hom_int`; the uncurried product-base
form is useful for `Prof_reindex`, tensor endpoints, and direct fibre access.
They should be treated as two surfaces for the same general concept, related by
curry/uncurry, not as two competing theories.

This answers the "could `hom_int_int` be the profunctor concept?" question as
follows:

```text
hom_int_func:
  yes, as the representable/Yoneda inclusion into curried profunctors;
  no, as the full profunctor concept.

Unit_prof_func2:
  yes, as the binary endpoint package for Hom_X(F[a],G[b]);
  no, as the full profunctor concept.

Prof_curried_cat / Prof_cat:
  yes, as the full profunctor concept, with curried and uncurried surfaces.
```

So the globally coherent architecture is:

```text
ordinary hom infrastructure
  hom_int(F)
  hom_int_func(X,B)                    // if needed
  tapp1_int_func_transf(F,G)

representable/unit profunctors
  Unit_prof(F,G)
  Unit_prof_func2(F,G)                 // if needed

general profunctors
  Prof_curried_cat(A,B)                // optional facade
  Prof_cat(A,B) = Catd_cat(A^op x B)   // product-base facade
```

The maps between these layers should be explicit comparison/projection maps.
They should not be collapsed by broad rewrite rules.

Because `curry_func_func` and `uncurry_func_func` are semantic composites with
nontrivial `comp_cat_fapp0` cuts, avoid adding broad rewrite rules that fold
arbitrary:

```text
uncurry(hom_int(G) o Op_func(F))
```

into a primitive `Unit_prof` head. Prefer:

```text
Unit_prof := Hom_catd(...)          // base clarity
comparison checks with hom_int      // inherited hom-action story
optional stable projections later   // only if downstream rules need them
```

If a curried profunctor facade becomes useful, introduce it explicitly:

```text
Prof_curried_cat(A,B) := Functor_cat (Op_cat A) (Catd_cat B)
```

and relate it to:

```text
Prof_cat(A,B) := Catd_cat(Product_cat(Op_cat A,B))
```

by named curry/uncurry comparison maps, not by unrestricted global rewrites.
This keeps the core profunctor API independent of the current complexity of
`uncurry_func_func`.

Implementation consequence: the first implementation should not attempt to
make the uncurried product form disappear. Tensor, weighted limits, and
reindexing all naturally inspect fibres over pairs `(a,b)` or `(b,c)`. The
curried form should be introduced when it buys reuse of existing `hom_int` and
composition infrastructure, not as a replacement for the product-base surface.

Displayed/dependent profunctors are a separate future layer. That is where a
`homd_int`-style analogue becomes relevant: a displayed profunctor over a base
profunctor would need endpoint families and dependent hom-action over the base
profunctor's cells. Do not solve that while implementing ordinary `Unit_prof`.

## Main Design Stance

The working v3.2 reading of a profunctor is:

```text
Prof_base(A,B) := Product_cat (Op_cat A) B
Prof_cat(A,B)  := Catd_cat(Prof_base(A,B))
Prof(A,B)      := Obj(Prof_cat(A,B))
```

This means a v3.2 profunctor is Cat-valued, not Set-valued or groupoid-valued:

```text
R : A^op x B -> Cat
```

Most of the old calculus should still make sense at this level. However, any
step that relies on set-truncation, proof-irrelevance, discreteness,
groupoidness, or an actual coend quotient must be treated as a pause point.
The implementation should not silently add a hidden truncation assumption.

The old `hom F R G` should be read as a shaped element of a profunctor, not as
just the pointwise family `i |-> R(F[i],G[i])`. The variance-correct v3.2
reading is:

```text
Prof_hom(F,R,G)
  = transformations from the unit profunctor on I
    to the pullback of R along F^op x G.
```

This matches the old intent: an object of a category is generalized to a
functor-shaped object `F : I -> C`, and an arrow is generalized to a natural
transformation or profunctor element over that shape.

## Guardrails

Do not add broad global reductions such as:

```text
Prof_tensor(R,Unit_prof) -> R
Product_cat(C,Terminal_cat) -> C
Product_cat(Terminal_cat,C) -> C
```

without a focused probe and a report update explaining the critical pairs.

For tensor/co-Yoneda, prefer named transformations and elimination beta rules
over type-level erasure of a whole tensor expression. The obsolete file itself
contains warnings around `P tensor Unit`.

For terminal products, the current `Product_cat` package is an injective stable
constructor with object, hom, projection, functor, transfor, and internalized
product-action rules. A global collapse

```text
Product_cat C Terminal_cat -> C
```

would change object normal forms from sigma pairs `(x,*)` to `x`, and would
therefore need compatible rules for:

```text
Product_pair
Product_projL_func / Product_projR_func
Hom_cat(Product_cat ...)
Functor_cat X (Product_cat ...)
Product_cat_func
Product_cat_fapp1_tapp0_func
Transf_cat X (Product_cat ...)
```

This may be feasible as a later strictification pass, but it is not a
prerequisite for the profunctor calculus. The first implementation should keep
terminal products explicit.

## Phase 0: Baseline And Probes

Before editing `emdash3_2.lp`, create focused probe copies under `tmp/probes/`
and run:

```bash
scripts/probe.sh tmp/probes/<name>.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

Each phase should add compact checks to `emdash3_2_checks.lp`, not active
`assert` commands in the main source.

Initial probe targets:

```text
Prof_base(A,B) normalizes to Product_cat (Op_cat A) B.
Prof_cat(A,B) normalizes to Catd_cat(Prof_base(A,B)).
Fibre_cat(Hom_prof(G),(x,b)) normalizes to Hom_cat X x (G[b]).
Hom_prof_along(F,G) typechecks as the left reindexing of Hom_prof(G).
Fibre_cat(Hom_prof_along(F,G),(a,b)) normalizes to Hom_cat X (F[a]) (G[b]).
Prof_reindex(R,F,G) has the expected fibre over (a',b').
Prof_hom(id_I,Hom_prof_along(F,G),id_I) exposes the expected transformation
shape.
```

Probe outcome so far: the single-argument `Hom_prof(G)` fibre rule typechecks,
and the binary `Hom_prof_along(F,G)` object typechecks as a left reindexing of
it. The earlier broader probe also showed direct semantic routes for
`Prof_base`, `Prof_cat`, `Prof_reindex`, and the `Prof_hom` wrapper as a
semantic `Obj(Functord_cat ...)`. More ambitious normal-form assertions for
`Hom_prof_along` and `Prof_hom` should wait until the first landed checks show
which projection surface is most readable.

## Phase 1: Profunctor Facade

Add readable semantic aliases first:

```text
Prof_base(A,B) : Cat
Prof_cat(A,B)  : Cat
Prof(A,B)      : Grpd
```

One possible helper is a product-map functor:

```text
Product_map_func(F,G)
  : Product_cat A B -> Product_cat A' B'
```

For fixed external `F` and `G`, this should first be a semantic pair through
the existing product-valued functor normal form:

```text
Struct_sigma
  (comp_cat_fapp0 F (Product_projL_func A B))
  (comp_cat_fapp0 G (Product_projR_func A B))
```

The existing product infrastructure already internalizes the fixed-right
left-factor action:

```text
Product_cat_fapp1_tapp0_func(F,B) = F * 1_B
Product_mapL_func_func(A,A',B)[F] = F * 1_B
```

So a new primitive `Product_map_func` is not justified merely to write
`Prof_reindex`. It becomes justified only if downstream rules need a stable
two-variable product-map discriminator, or if we need functoriality in both
`F` and `G` simultaneously. A full semantic two-variable map can later be
factored through fixed-side maps and product swap once the right-side/swap
layer is landed.

For profunctor reindexing:

```text
Prof_reindex(R,F,G)
  : Prof(A',B')

where
  R : Prof(A,B)
  F : A' -> A
  G : B' -> B

Prof_reindex(R,F,G)
  := Pullback_catd R (Product_map_func (Op_func F) G).
```

The first hom/unit profunctor should start with the single-argument core:

```text
Hom_prof(G) : Prof(X,B)

where G : B -> X

Hom_prof(G)[x,b] = Hom_X(x,G[b]).
```

Likely implementation route:

```text
K      := Product_cat (Op_cat X) B
source := Product_projL_func (Op_cat X) B
target := comp_cat_fapp0 G (Product_projR_func (Op_cat X) B)

Hom_prof(G) := Hom_catd(Const_catd K X, source, target)
```

Then define the binary endpoint form by left reindexing:

```text
Hom_prof_along(F,G)
  := Prof_reindex(Hom_prof(G), F, id_B)
```

The direct single-argument fibre rule has been probed successfully. Add a
stable binary `Hom_prof_along`/`Unit_prof_along` projection head only if later
checks need a dedicated discriminator.

Then define the old Cartier-shaped element category:

```text
Prof_transf_cat(R',F,R,G)
  := Functord_cat R' (Prof_reindex(R,F,G))

Prof_hom(F,R,G)
  := Obj(Prof_transf_cat(Unit_prof(id_I,id_I),F,R,G))
```

where `F : I -> A` and `G : I -> B`.

If this last definition is too brittle, introduce a stable `Prof_hom` head only
after proving the semantic version fails to compute in a focused assertion.

### Phase 1 Refined Implementation Sketch

Use canonical declarations first:

```text
Prof_base(A,B) : Cat
Prof_base(A,B) := Product_cat (Op_cat A) B

Prof_cat(A,B) : Cat
Prof_cat(A,B) := Catd_cat(Prof_base(A,B))

Prof(A,B) : Grpd
Prof(A,B) := Obj(Prof_cat(A,B))
```

The readable alias `Prof(A,B)` should be used in comments and maybe in public
theorem statements only after the core definitions typecheck in reduced form.

Product maps should be semantic pairs:

```text
Product_map_func(F,G)
  := (F o Product_projL_func, G o Product_projR_func)
```

Required checks:

```text
Product_map_func(F,G)[(a,b)] = (F[a],G[b])
Product_map_func(F,G)[(p,q)] = (F[p],G[q])
```

The object check already probes cleanly. The arrow check should be added when
the active implementation lands, because later `Prof_reindex` and `Op_prof`
depend on product-map arrow action.

For the unit profunctor:

```text
K      := Prof_base(A,B)
source := Op_func(F) o Product_projL_func(Op_cat A,B)
target := G          o Product_projR_func(Op_cat A,B)

Unit_prof(F,G) := Hom_catd(Const_catd(K,X), source, target)
```

The key point is that:

```text
source : Obj(Pi_cat(Op_catd(Const_catd(K,X))))
target : Obj(Pi_cat(Const_catd(K,X)))
```

because:

```text
Pi_cat(Op_catd(Const_catd(K,X))) -> Functor_cat K (Op_cat X)
Pi_cat(Const_catd(K,X))          -> Functor_cat K X
```

This is why `Hom_catd` is the correct owner: it packages both the fibre formula
and the base-arrow action of the hom family.

The first `Prof_hom` API should be:

```text
Prof_transf_cat(R',F,R,G)
  : Cat
  := Functord_cat R' (Prof_reindex(R,F,G))

Prof_hom_cat(F,R,G)
  : Cat
  := Prof_transf_cat(Unit_prof(id_I,id_I),F,R,G)

Prof_hom(F,R,G)
  : Grpd
  := Obj(Prof_hom_cat(F,R,G))
```

This is a shaped profunctor element. In the representable case:

```text
R = Unit_prof(id_C,id_C)
F,G : I -> C
```

it should behave like the category/type of natural transformations `F => G`.
Do not force this as a global rewrite initially; add a named comparison or a
focused check once the `Prof_hom` projection surface is known.

Representable profunctors for ordinary functors should be aliases:

```text
Cov_repr_prof(F : A -> B) := Unit_prof(F,id_B)  : Prof(A,B)
Con_repr_prof(G : B -> A) := Unit_prof(id_A,G)  : Prof(A,B)
```

These are important later because adjunctions are most naturally bridges
between the covariant and contravariant representables of the left and right
adjoint functors.

## Phase 2: Tensor And Co-Yoneda

The tensor of profunctors is semantically coend-like:

```text
R : Prof(A,B)
S : Prof(B,X)
R tensor S : Prof(A,X)
```

The current v3.2 kernel has Sigma and Pi categories, but it does not yet have a
general coend or quotient/coinserter package. Therefore the first implementation
should use a stable primitive head:

```text
Prof_tensor(R,S) : Prof(A,X)
```

and add only the reindexing rules that are needed by checks:

```text
Prof_tensor(R,S) reindexed on the left
Prof_tensor(R,S) reindexed on the right
```

Next add transformation constructors mirroring the useful old asymmetry:

```text
Prof_tensor_cov_transf
Prof_tensor_con_transf
Prof_tensor_cov_hom_hom
Prof_tensor_con_hom_hom
Prof_tensor_cov_hom_transf
```

The co-Yoneda reduction should be exposed by named transformations:

```text
Prof_coyoneda_unit_tensor_cov_transf
Prof_coyoneda_unit_tensor_con_transf
```

and by narrow beta rules saying that composing the co-Yoneda transformation
with the corresponding tensor-introduction form cancels. Do not initially add:

```text
Prof_tensor(R,Unit_prof(...)) -> R
Prof_tensor(Unit_prof(...),R) -> R
```

The old "Kan extension" idea belongs here in the profunctor sense: tensor and
its right adjoints are the primitive calculus; ordinary functors appear as
representable/unit profunctors. This is distinct from the pending
`Pi_along_func` plan, although a later derived formula may relate the two.

### Tensor Coherence To Track

The primitive tensor should be treated as a bicategorical composition operator,
not as a mere binary type former. The eventual coherence layer should contain
named transformations, not broad type-level rewrites:

```text
Prof_tensor_assoc_transf
Prof_tensor_unitL_transf
Prof_tensor_unitR_transf
Prof_tensor_assoc_inv_transf
Prof_tensor_unitL_inv_transf
Prof_tensor_unitR_inv_transf
```

The first implementation does not need all of these, but the names matter for
global coherence. If tensor associativity is made a rewrite too early, it can
interact badly with reindexing and co-Yoneda reductions. Prefer beta rules
only when a named associator/unit map is composed with a tensor introduction or
elimination form.

The expected unit profunctor for tensor over `B` is:

```text
Unit_prof(id_B,id_B) : Prof(B,B)
```

Do not collapse:

```text
R tensor Unit_prof(id_B,id_B)
Unit_prof(id_A,id_A) tensor R
```

at the type level until there is a concrete associativity/unit coherence test.

## Phase 3: Internal Hom / Implication

Add profunctor implication as right-adjoint-like structure to tensor:

```text
Prof_imply_cov(O,Q) : Prof(A,C)
  where O : Prof(A,B), Q : Prof(C,B)

Prof_imply_con(Q,O) : Prof(C,B)
  where Q : Prof(A,C), O : Prof(A,B)
```

corresponding to the old:

```text
O <= Q
Q => O
```

The first slice should implement the covariant side only:

```text
Prof_imply_cov_transf
Prof_eval_cov_transf
Prof_lambda_cov_transf
Prof_eval_cov_hom_transf
Prof_lambda_cov_transf_hom
```

with beta/eta:

```text
lambda(eval(t)) -> t
eval(lambda(t)) -> t
```

Only after the covariant side has stable checks should the contravariant side
be added. The old file had several heavy naturality rules here; in v3.2 these
should be introduced one at a time, driven by failing checks rather than by a
bulk port.

The intended adjunction patterns are:

```text
Prof_transf_cat(Prof_tensor(P,Q), F, O, G)
  <-> Prof_transf_cat(P, F, Prof_imply_cov(O,Q), id)

Prof_transf_cat(Prof_tensor(P,Q), F, O, G)
  <-> Prof_transf_cat(Q, id, Prof_imply_con(P,O), G)
```

The exact span arguments should be fixed by probes. The old implementation had
both covariant and contravariant tensor-introduction rules because composable
spans are asymmetric. Preserve that asymmetry instead of trying to hide it
behind one over-general constructor.

## Phase 4: Weighted Limits

Weighted limits should be packaged over the profunctor implication layer:

```text
WeightedLimit_cov(F,W,L) : TYPE

where
  F : J -> B
  W : Prof(J',J)
  L : J' -> B
```

Intended reading:

```text
L = F <= W
```

but represented by universal transformations:

```text
weighted_limit_cov_univ_transf
weighted_limit_cov_cone_transf
```

with beta/eta cancellation rules. The old formulas translate schematically as:

```text
univ:
  ((Unit_prof(M,F)) <= W) -> Unit_prof(M,L)

cone:
  Unit_prof(M,L) -> ((Unit_prof(M,F)) <= W)
```

for every shaped object `M : I -> B`.

Endpoint check for the covariant case:

```text
Unit_prof(M,F) : Prof(I,J)
W              : Prof(J',J)
Unit_prof(M,F) <= W : Prof(I,J')
Unit_prof(M,L)      : Prof(I,J')
```

So the universal and cone maps should live in transformation categories between
profunctors over `I` and `J'`, most likely:

```text
weighted_limit_cov_univ_transf(isl,M)
  : Prof_transf_cat(Prof_imply_cov(Unit_prof(M,F),W),
                    id_I,
                    Unit_prof(M,L),
                    id_J')

weighted_limit_cov_cone_transf(isl,M)
  : Prof_transf_cat(Unit_prof(M,L),
                    id_I,
                    Prof_imply_cov(Unit_prof(M,F),W),
                    id_J')
```

The exact argument order should follow the landed `Prof_transf_cat` API, but
the endpoint categories should be as above. These endpoint checks are more
important than the final names.

The right-adjoint-preservation theorem needs a narrow adjunction/profunctor
bridge. The current v3.2 `Adjunction(R,L)` package gives:

```text
left_adj_func(J)  : R -> L
right_adj_func(J) : L -> R
unit_adj_transf(J)
counit_adj_transf(J)
```

but it does not yet provide the old `Adj_cov_hom` / `Adj_con_hom` transpose
operations. Add a v3.2 bridge only in the form needed by weighted limits:

```text
Adjunction_unit_prof_cov
Adjunction_unit_prof_con
Adjunction_transpose_cov
Adjunction_transpose_con
```

or better names once the exact endpoint formulas are probed.

Then add:

```text
right_adjoint_preserves_weighted_limit_cov
```

as a symbolic construction whose computation is expressed by composition of
the adjunction bridge, the weighted-limit universal map, and implication
naturality.

### Adjunction Bridge Shape

For an adjunction:

```text
J : Adjunction(A,B)
L := left_adj_func(J)  : A -> B
R := right_adj_func(J) : B -> A
```

the bridge needed by weighted limits is the hom-isomorphism as a profunctor
transformation:

```text
Unit_prof(L o M, F)  <->  Unit_prof(M, R o F)
```

where:

```text
M : I -> A
F : K -> B
```

Both sides are profunctors `Prof(I,K)`:

```text
Unit_prof(L o M,F)[i,k] = Hom_B(L(M[i]),F[k])
Unit_prof(M,R o F)[i,k] = Hom_A(M[i],R(F[k]))
```

This should replace the old broad `Adj_cov_hom` / `Adj_con_hom` layer. The
bridge can be built from `unit_adj_transf` and `counit_adj_transf`, with the
existing triangle rewrite rules providing the beta cancellations. The first
implementation should expose only the bridge maps that the preservation proof
uses.

## Phase 5: Duality And Left Adjoints Preserve Weighted Colimits

This is the most important part of the old duality section. Do not port the
old broad `Op_*` rewrite block wholesale. Build only the missing duality
operations required for the theorem:

```text
Op_transf          ordinary transformations
Op_adjunction     Adjunction(A,B) -> Adjunction(Op_cat B, Op_cat A)
Op_prof           Prof(A,B) -> Prof(Op_cat B,Op_cat A)
Op_prof_transf
Op_weighted_limit_cov
Op_weighted_limit_con
```

The ordinary transformation dual should reverse the transformation direction:

```text
eta : Transf(F,G)
Op_transf(eta) : Transf(Op_func(G), Op_func(F))
```

because a component `F[x] -> G[x]` in `B` is a component
`G[x] -> F[x]` in `B^op`.

For adjunctions:

```text
J : Adjunction(A,B)
Op_adjunction(J) : Adjunction(Op_cat B, Op_cat A)
```

with:

```text
left_adj_func(Op_adjunction(J))  = Op_func(right_adj_func(J))
right_adj_func(Op_adjunction(J)) = Op_func(left_adj_func(J))
```

`Op_prof` is a design-sensitive point because profunctors are Cat-valued in
v3.2. The likely operation must combine:

```text
base swap between A^op x B and B x A^op
pointwise Op_catd if the theorem needs fibre-op duality
```

This must be probed before installing rules. In particular, do not assume the
Set-valued formula automatically transfers to Cat-valued profunctors.

More explicitly, for:

```text
R : Prof(A,B)
```

the op-dual should have type:

```text
Op_prof(R) : Prof(Op_cat B, Op_cat A)
```

The base of the target is:

```text
Prof_base(Op_cat B,Op_cat A)
  = Product_cat B (Op_cat A)
```

while the base of `R` is:

```text
Prof_base(A,B)
  = Product_cat (Op_cat A) B
```

Therefore `Op_prof` needs a product-swap functor:

```text
Product_swap_func(B,Op_cat A)
  : Product_cat B (Op_cat A) -> Product_cat (Op_cat A) B
```

and probably pointwise opposite on fibres:

```text
Op_prof(R) := Pullback_catd(Op_catd(R), Product_swap_func(B,Op_cat A))
```

The `Op_catd(R)` part is the design choice forced by Cat-valued profunctors:
it reverses higher cells inside each profunctor value. If a later theorem only
needs base reversal and not fibre reversal, document that as a different
operation rather than overloading `Op_prof`.

Once these operations exist, define the left-adjoint theorem by duality:

```text
left_adjoint_preserves_weighted_colimit_con
  := Op_prof_transf(
       right_adjoint_preserves_weighted_limit_cov(
         Op_weighted_limit_cov(...),
         Op_adjunction(...),
         Op_func(M)))
```

The expected public theorem should mention left adjoints preserving weighted
colimits directly; the implementation can be the op-dual of the right-adjoint
limit theorem.

The weighted-colimit theorem should be the dual of the right-adjoint limit
theorem, not a second independent proof. This is the main reason to implement
`Op_weighted_limit_cov/con` before broad colimit-specific APIs.

## Phase 6: Directed Inductive Type / Join Category

The old join section is best treated as a stress test for higher/directed
inductive categories, not as a prerequisite for tensor.

There are two possible v3.2 routes:

```text
1. Primitive directed inductive join:
   Join_cat(A,B)
   join_fst_func : A -> Join(A,B)
   join_snd_func : B -> Join(A,B)
   join_cross_hom : shaped arrows from A-side to B-side
   join_elim_func with beta rules

2. Profunctor collage:
   Collage_prof(R)
   Join(A,B) := Collage_prof(Terminal_prof(A,B))
```

The collage route is mathematically cleaner, but a full category collage also
needs a story for homs in the reverse direction. If that requires an
`Initial_cat` or a primitive empty hom category, pause and design it explicitly.

The primitive directed-inductive route can be implemented earlier as an
example, provided its eliminator states naturality over shaped objects and does
not pretend to be a complete generic inductive-type framework. The useful
initial check is the old beta rule:

```text
join_cross_hom ; join_elim_func(first,second,cross) -> cross
```

expressed in current v3.2 `Functor`/`Transf`/`Prof_hom` vocabulary.

## Conditional Dependencies

Use `REPORT_EMDASH_V3_2_PI_ALONG_FUNCTOR_IMPLEMENTATION_PLAN_2026-06-11.md`
only if a profunctor construction specifically needs a right Kan formula along
an ordinary functor. The tensor/implication calculus should not wait for
`Pi_along_func`.

Use `REPORT_EMDASH_V3_2_FUNCTOR_STRUCTURAL_LOGIC_PRELIM_PLAN_2026-06-04.md`
only if a proof needs displayed exchange, contraction, or product/curry
compatibility. Ordinary weakening/exchange/contraction already exist.

## Coherence, Completeness, And Feasibility

Current assessment:

```text
Phase 1 profunctor facade: feasible now; semantic route probed successfully.
Phase 2 tensor: feasible as primitive calculus; not complete as coend semantics.
Phase 3 implication: feasible as primitive adjoint calculus; probe covariant first.
Phase 4 weighted limits: feasible as universal packages over implication.
Phase 5 op-duality: feasible, but needs product swap and careful fibre-op choice.
Phase 6 join: feasible as primitive directed-inductive example; collage needs more.
```

Completeness gaps to keep explicit:

```text
No general coend/coinserter quotient currently exists.
No bicategory-of-profunctors coherence layer currently exists.
No ordinary Op_transf or Op_adjunction currently exists.
No Product_swap_func currently exists as a named product-map helper.
No Initial_cat currently exists for a full collage/join story.
No truncation/discreteness assumption is available or intended.
```

This is still globally coherent because the first implementation path does not
pretend to compute coends or quotients. It builds a Dosen-style symbolic
calculus whose reductions are beta/eta and named universal-map cancellations.
If a later semantic coend layer is added, `Prof_tensor` can become a semantic
owner or receive comparison maps without invalidating the public calculus.

## Suggested Implementation Order

1. Add the profunctor facade and `Unit_prof` semantic checks.
2. Add reindexing and `Prof_hom`.
3. Add primitive `Prof_tensor` plus narrow transformation constructors.
4. Add covariant implication/eval/lambda beta-eta.
5. Add weighted-limit packages and the adjunction transpose bridge.
6. Add op-duality operations required for left-adjoint colimit preservation.
7. Add the join/directed-inductive example, either primitive or via collage.

Each step should leave:

```text
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

passing, and should add report notes when a semantic definition has to become a
stable primitive head.
