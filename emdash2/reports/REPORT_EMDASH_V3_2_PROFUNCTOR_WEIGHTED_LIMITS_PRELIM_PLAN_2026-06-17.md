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
Fibre_cat(Unit_prof(F,G),(a,b)) normalizes to Hom_cat X (F[a]) (G[b]).
Prof_reindex(R,F,G) has the expected fibre over (a',b').
Prof_hom(id_I,Unit_prof(F,G),id_I) exposes the expected transformation shape.
```

## Phase 1: Profunctor Facade

Add readable semantic aliases first:

```text
Prof_base(A,B) : Cat
Prof_cat(A,B)  : Cat
Prof(A,B)      : TYPE
```

The key helper is a product-map functor:

```text
Product_map_func(F,G)
  : Product_cat A B -> Product_cat A' B'
```

implemented through the existing product-valued functor normal form:

```text
Struct_sigma
  (comp_cat_fapp0 F (Product_projL_func A B))
  (comp_cat_fapp0 G (Product_projR_func A B))
```

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

The first unit profunctor should be semantic rather than primitive:

```text
Unit_prof(F,G) : Prof(A,B)

where
  F : A -> X
  G : B -> X

Unit_prof(F,G)[a,b] = Hom_X(F[a],G[b]).
```

Likely implementation route:

```text
K      := Product_cat (Op_cat A) B
source := comp_cat_fapp0 (Op_func F) (Product_projL_func (Op_cat A) B)
target := comp_cat_fapp0 G           (Product_projR_func (Op_cat A) B)

Unit_prof(F,G) := Hom_catd(Const_catd K X, source, target)
```

This relies on the existing reduction:

```text
Hom_catd(Const_catd K Cat_cat,X,Y) -> Functor_catd(Op_func X,Y)
```

only for Cat-indexed homs. For ordinary homs in a fixed `X`, the direct
`Hom_catd(Const_catd K X, source, target)` route should be probed first.

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

## Phase 3: Internal Hom / Implication

Add profunctor implication as right-adjoint-like structure to tensor:

```text
Prof_imply_cov(O,Q) : Prof(A,C)
Prof_imply_con(Q,O) : Prof(C,B)
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

## Phase 5: Duality And Left Adjoints Preserve Weighted Colimits

This is the most important part of the old duality section. Do not port the
old broad `Op_*` rewrite block wholesale. Build only the missing duality
operations required for the theorem:

```text
Op_transf          ordinary transformations
Op_adjunction     Adjunction(R,L) -> Adjunction(Op_cat L, Op_cat R)
Op_prof           Prof(A,B) -> Prof(Op_cat B,Op_cat A)
Op_prof_transf
Op_weighted_limit_cov
Op_weighted_limit_con
```

`Op_prof` is a design-sensitive point because profunctors are Cat-valued in
v3.2. The likely operation must combine:

```text
base swap between A^op x B and B x A^op
pointwise Op_catd if the theorem needs fibre-op duality
```

This must be probed before installing rules. In particular, do not assume the
Set-valued formula automatically transfers to Cat-valued profunctors.

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
