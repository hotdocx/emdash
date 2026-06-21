# EMDASH v3.2 Profunctor, Weighted Limit, And Duality Preliminary Plan

Date: 2026-06-17

Status updated: 2026-06-22

Status: the first end-to-end implementation pass is complete through Phase 6a.
The requested computational surface for Cat-valued profunctors, tensor,
internal hom, weighted limits, preservation by right adjoints, dual weighted
colimits, preservation by left adjoints, and the nondependent directed join
recursor is active in `emdash3_2.lp`. The plan is now in refinement and
semantic-completion mode rather than initial feasibility mode.

Latest validation:

```text
make check   passed
make health  passed
make ci      passed

emdash3_2_checks.lp: 549 checks
check catalog:       15 areas, 0 unclassified checks
```

## Overall Implementation Status 2026-06-19

The main applications that motivated this plan are now expressible and have
computational rewrite interfaces. The implementation deliberately remains a
symbolic Dosen-style calculus where the current kernel lacks general
coend/end, quotient, bicategorical-coherence, or directed-inductive semantics.

| Phase | Landed implementation | Explicit remaining work |
| --- | --- | --- |
| 0. Baseline and probes | Incremental probe/log/report workflow used throughout all phases. | Continue using focused probes for every nontrivial rewrite or internalization extension. |
| 1. Profunctor facade | `Prof_base`, `Prof_cat`, `Hom_prof_along`, `Hom_prof`, `Unit_prof`, semantic `Hom_prof_func`, `Product_map_func`, `Prof_reindex`, `Prof_transf_cat`, `Prof_hom_cat`, and `Prof_hom`. | Ordinary-`Transf_cat` comparisons, broader endpoint internalization, and further curry/uncurry comparison projections only when demanded downstream. |
| 2. Tensor and co-Yoneda | Primitive `Prof_tensor`, endpoint reindexing, general and shaped tensor cells, `Prof_comp_transf`, identities, and symmetric identity-representable co-Yoneda beta rules. `Prof_func_transf`/`Prof_func_hom` are now available. | General co-Yoneda rules using `Prof_func_hom`, tensor associativity/unit coherence, and semantic coend/coinserter ownership. |
| 3. Internal hom | Covariant and contravariant implications, mixed-variance cell actions, inverse general/shaped eval-lambda operations, fixed-weight `Prof_imply_cov_func(Q)`, fixed-endpoint `Prof_imply_cov_func2_transf`, and direct mixed-variance bifunctor `Prof_imply_cov_func2` with checked object/full/capped action, identity/composition, and unary specialization. | End semantics, broader eval naturality, fixed-left `Prof_imply_con_func(P)`, separate higher-arrow projections, and any demanded tensor/implication adjunction package. |
| 4. Weighted limits | Ordinary `WeightedCone_prof`/`IsWeightedLimit_cov_iso`; computational `ProfComparison`/`WeightedLimit_cov`; arbitrary-map push/pull and selected universal/cone cells; ambient adjunction comparison; and genuinely defined ordinary and computational right-adjoint preservation theorems. The established public names are transparent aliases of the representability implementation. | Naturality in additional theorem parameters, unit/counit component projections, and any further selected-map presentation requested by concrete consumers. |
| 5. Duality and weighted colimits | `Op_transf`, `Op_adjunction`, `Product_swap_func`, base-swap-only `Op_prof`, `Op_prof_transf`, transparent `WeightedColimit_con`, and the full `left_adjoint_preserves_weighted_colimit_con` witness derived by duality. | Direct colimit-oriented projection names and a non-looping semantic pullback/reindex comparison for `Op_prof_transf`. |
| 6a. Directed join | `Terminal_prof`, internally natural `join_cross_transf`, derived shaped `join_cross_hom`, and `join_elim_func` with inclusion and cross beta rules. | Dependent elimination, explicit join object/hom decomposition, a generic directed-inductive framework, and/or semantic collage construction. |

The central success criterion has therefore been reached:

```text
right adjoints preserve Cat-valued profunctor-weighted limits;
left adjoints preserve the dual weighted colimits by computation through Op;
the join example exercises a directed categorical recursor with an internally
natural generating cross cell.
```

This does not mean that a complete semantic bicategory of Cat-valued
profunctors has been constructed. No Set/groupoid truncation assumption was
introduced, and no existing symbolic primitive is being presented as a
general coend, end, quotient, or collage implementation.

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

## Planning Status And Revision Discipline

Every architecture proposed in this report is provisional. The names,
factorizations, stable-head choices, phase boundaries, and implementation order
are working hypotheses to be tested by focused Lambdapi probes and by the
category-theoretic statements that later phases actually require. They may be
adjusted, replaced, or rolled back as implementation exposes missing
functoriality, bad normal forms, non-joinable rules, or a better semantic owner.

In particular, this is not a porting specification for the corresponding
`cartierSolution13.lp` declarations and rules. That file is evidence about
useful target computations and about failure modes, not an API to reproduce.
Before implementing each old section:

```text
1. Restate the intended construction from ordinary category/profunctor
   semantics, independently of the old Lambdapi formulation.
2. Identify the least-internal and one-variable-internal forms actually needed
   by the target theorem or computation.
3. Locate reusable v3.2 semantic owners and projection infrastructure.
4. Probe the semantic definition and its required object/arrow/naturality
   computations.
5. Introduce a primitive stable head only for a demonstrated rewrite,
   discrimination, termination, or performance requirement.
6. Reassess the design before continuing to the next phase.
```

Discovering a missing general kernel construction is an expected outcome, not
an exceptional failure. Such a side task should be isolated and implemented as
general infrastructure when its mathematical ownership is broader than
profunctors. Examples may include product-map action, opposite transformations,
adjunction transport, coend-like quotients, or directed-inductive eliminators.
After completing such a prerequisite, return to the original phase and
re-evaluate whether its proposed profunctor-specific head is still necessary.

Backtracking is required rather than discouraged when a probe shows that:

```text
the proposed normal form hides a variable needed by downstream matching;
two primitive heads create competing canonical forms;
a rule duplicates computation already owned by a general constructor;
pointwise object equations cannot be extended functorially or naturally;
the old Cartier statement was stronger, weaker, or differently oriented than
the genuine categorical construction;
later weighted-limit or duality formulas reveal an asymmetric design that
cannot support both variance directions coherently.
```

Accordingly, words such as "recommended", "should", and "likely primitive"
below describe the current best candidate, not a frozen public interface.

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
Hom_prof(G) := right-representable hom profunctor
Hom_prof_along(F,G) := Prof_reindex(Hom_prof(G), F, id_B)
Prof_reindex(R,F,G) := Pullback_catd R (Product_map_func(Op_func F,G))
Prof_transf_cat(R',F,R,G) := Functord_cat R' (Prof_reindex R F G)
Prof_hom(F,R,G) := Obj(Prof_transf_cat(Unit_prof(I),F,R,G))
```

The same probe checked:

```text
Hom_prof(G)[x,b] = Hom_X(x,G[b])
Hom_prof_along(F,G)[a,b] = Hom_X(F[a],G[b])
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
Unit_prof(X), as notation for Hom_prof(id_X)
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
Hom_prof(G)
Hom_prof_along(F,G)
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

The current hypothesis is that these may need primitive stable heads from the
beginning:

```text
Prof_tensor(R,S)
Prof_imply_cov(O,Q)
Prof_imply_con(Q,O)
Prof_eval_cov_transf / Prof_lambda_cov_transf
WeightedLimit_cov
weighted_limit_cov_univ_transf
weighted_limit_cov_cone_transf
Op_transf
Op_adjunction
```

Reason: v3.2 does not currently have semantic coends, closed bicategory
structure, or op-dual universal-property transport from which these can be
definitionally derived. Their computation may therefore need explicit beta/eta
and naturality rules. This classification must be rechecked immediately before
each head is introduced; a prerequisite side task may reveal a better general
semantic owner. Phase 5d performed that recheck and found that
`WeightedColimit_con`, `Op_weighted_limit_cov`, and
`Op_weighted_colimit_con` are transparent aliases/wrappers over
`WeightedLimit_cov`; they do not need primitive stable heads.

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

For the hom/unit profunctor:

```text
Level 0:
  Hom_prof_along(F,G) : Prof(A,B)
  Hom_prof(G) := Hom_prof_along(id_X,G)       // notation/specialization
  Unit_prof(X) := Hom_prof_along(id_X,id_X)

Level 1a, ordinary curried right-endpoint internalization:
  hom_int_func(X,B)
    : (B -> X) -> Prof_curried_cat(X,B)
  hom_int_func(X,B)[G] = hom_int(G)

Level 1b, one profunctor endpoint internalized at a time:
  Hom_prof_cov_func(F)
    : (B -> X) -> Prof_cat(A,B)
  Hom_prof_cov_func(F)[G] = Hom_prof_along(F,G)

  Hom_prof_con_func(G)
    : (A -> X)^op -> Prof_cat(A,B)
  Hom_prof_con_func(G)[F] = Hom_prof_along(F,G)

Level 2:
  Hom_prof_along_func2
    : (A -> X)^op x (B -> X) -> Prof_cat(A,B)
```

The variance is important:

```text
Hom_prof_along(F,G)[a,b] = Hom_X(F[a],G[b])
```

is contravariant in `F` and covariant in `G`. The two Level 1b packages expose
exactly those two variances without internalizing the pair simultaneously.
They are the likely packages needed by weighted limits:

```text
limit_cov:
  M varies in Hom_prof_along(M,F), hence use Hom_prof_con_func(F)

limit_con:
  M varies in Hom_prof_along(F,M), hence use Hom_prof_cov_func(F)
```

The fixed-`F` curried analogue does not require adding `F` as an argument to
the core `hom_int_func`. Existing precomposition infrastructure can
postprocess the whole internalized package:

```text
hom_int_along_func(F)
  := comp_cat_con_func(Op_func(F)) o hom_int_func(X,B)

hom_int_along_func(F)[G]
  = hom_int(G) o Op_func(F).
```

A focused probe confirmed that this definition and object projection
typecheck. Therefore:

```text
hom_int_func:
  should retain the smallest natural arity G |-> hom_int(G).

hom_int_along_func(F):
  may be introduced as a named fixed-F package if downstream rules repeatedly
  need G |-> hom_int(G) o Op_func(F).

Hom_prof_cov_func(F):
  is the corresponding uncurried package if the product-base profunctor head
  is the rewrite-facing owner.
```

The left-endpoint package is genuinely contravariant. A candidate curried
owner is:

```text
hom_con_int_func(G)
  : (A -> X)^op -> Prof_curried_cat(A,B)

hom_con_int_func(G)[F]
  = hom_int(G) o Op_func(F).
```

Its object formula coincides with the fixed-`G` side of the same hom
profunctor, but its hom-action must project to precomposition. The current
`hom_con(W,F)` is an `injective` transparent definition through `hom_` over
opposites, together with rules that canonicalize its action to the stable
`hom_precomp_along_*` heads. This means the first new primitive, if one is
needed, should be the reusable `hom_con_int_func(G)` package rather than an
automatic promotion of the existing object-level `hom_con` alias. Promote
`hom_con` itself only if a focused rewrite-facing probe needs to discriminate
on that head.

A fully internalized two-variable owner would have source morally:

```text
Product_cat (Op_cat (Functor_cat A X)) (Functor_cat B X)
```

and target:

```text
Prof_cat(A,B).
```

This is exactly the kind of internalization that should be delayed until a
downstream theorem needs both endpoints to vary simultaneously. The first
implementation should keep `Hom_prof_along(F,G)` external and add only the
one-endpoint package demanded by the first weighted-limit or co-Yoneda check:

```text
Hom_prof_cov_func(F)[G] = Hom_prof_along(F,G)
Hom_prof_con_func(G)[F] = Hom_prof_along(F,G)

// only later, if a theorem quantifies over both endpoints:
Hom_prof_along_func2[(F,G)] = Hom_prof_along(F,G)
Hom_prof_along_func2[(alpha,beta)] = pre/postcomposition on hom fibres
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

## Hom Profunctor Versus Existing Hom Infrastructure

The hom/unit profunctor should not be treated as a fundamentally new hom
theory. Its smallest semantic factorization is the one-argument object:

```text
Hom_prof(G) : Prof(X,B)
G : B -> X
Hom_prof(G)[x,b] = Hom_X(x,G[b]).
```

This is the uncurried profunctor form of the existing:

```text
hom_int(G) : X^op -> Catd(B)
hom_int(G)[x][b] = Hom_X(x,G[b]).
```

The binary endpoint form from the Cartier draft should be read as the
left-reindexed convenience:

```text
F : A -> X
G : B -> X
Hom_prof_along(F,G) : Prof(A,B)
Hom_prof_along(F,G) := Prof_reindex(Hom_prof(G), F, id_B)
```

For this binary convenience there are two coherent semantic presentations:

```text
1. Hom_catd presentation:
   Hom_prof_along(F,G)
     := Hom_catd(Const_catd(A^op x B,X), F o piL, G o piR)

2. hom_int/curry presentation:
   Hom_prof_along(F,G)
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

and agrees fibrewise with the `Hom_catd` presentation. This proves that the
binary `Hom_prof_along(F,G)` is not mathematically foundational. It does not
settle the rewrite-facing normal form: the later Cartier audit shows that
co-Yoneda, weighted limits, adjunction, and duality repeatedly need both
reindexed endpoints visible.

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

Therefore the current implementation order is:

```text
1. Keep Hom_prof(G) as the semantic factorization and comparison model.
2. Add Hom_prof_along(F,G) as the sole rewrite-facing primitive/stable head,
   with direct fibre and hom-action projections.
3. Define Hom_prof(G) and Unit_prof(X) as identity-endpoint notation or
   specializations, not competing primitive heads.
4. Add fold rules from representable Prof_reindex expressions into
   Hom_prof_along(F,G).
5. Add checks comparing Hom_prof_along(F,G) with the Hom_catd and curried
   presentations.
6. Add Hom_prof_cov_func(F) or Hom_prof_con_func(G) only when a universal
   formula needs that endpoint internalized.
7. Add Hom_prof_along_func2 only if a theorem genuinely varies both endpoints.
```

If `Hom_prof_along_func2` is eventually added, it should be understood as an
internalized packaging of existing hom/reindexing infrastructure:

```text
Hom_prof_along_func2
  : Product_cat (Op_cat (Functor_cat A X)) (Functor_cat B X)
      -> Prof_cat(A,B)
Hom_prof_along_func2[(F,G)] = Hom_prof_along(F,G)
```

Its hom-action should not invent new hom composition rules. It should project
to the existing pre/postcomposition heads where possible. In particular,
comparison with `hom_int` should drive the design of any projection rules.

Relationship to `homd_int`: `Hom_prof` is the ordinary/Cat-valued hom-family
case. `homd_int(FF)` is the displayed/dependent analogue where the endpoint
varies through a displayed functor over a base. They should remain separate
semantic owners. A future displayed profunctor/unit theory should be built by
analogy with `homd_int`, not by forcing `Hom_prof` to cover dependent endpoints.

### Single-Argument Core Versus Binary Convenience

Refinement: the semantic core unit-hom profunctor has one functor argument,
but the current rewrite audit favors a single two-endpoint primitive normal
form.

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
  yes, because formulas such as
  Hom_prof_along(M,F) are much easier to read than an explicit reindexing
  expression.

as a primitive stable rewrite owner:
  current evidence says yes: reindexing, co-Yoneda, weighted limits,
  adjunction, and duality all benefit from matching the binary endpoint
  normal form. Make it the single rewrite-facing hom-prof head rather than
  adding it beside a competing primitive Hom_prof.
```

This also clarifies naming. The most precise split would be:

```text
Hom_prof_along(F,G)
  sole primitive/stable rewrite-facing hom profunctor.

Hom_prof(G) or Right_repr_prof(G)
  semantic/notation specialization Hom_prof_along(id_X,G).

Unit_prof(X)
  identity/unit specialization Hom_prof_along(id_X,id_X).
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

With a stable curry comparison package, the picture improves. A focused probe
with a fresh primitive:

```text
Probe_curry_func_func
  : (A x B -> C) -> (A -> (B -> C))
```

successfully typechecked the rule:

```text
Probe_curry_func_func[Hom_prof(G)] -> hom_int(G)
```

provided the rule and assertion used canonical categories:

```text
source = Catd_cat(Product_cat(Op_cat X,B))
target = Functor_cat(Op_cat X)(Catd_cat B)
```

rather than reducible `Functor_cat _ Cat_cat` wrappers. So a primitive
profunctor-specific `Prof_curry*` is a feasible way to make
`Hom_prof_along(id_X,G)` inherit the existing `hom_int(G)` story
computationally, without first reverting ordinary global curry.

### Cartier Binary-Argument Audit

Reviewing the relevant `cartierSolution13.lp` sections gives the following
diagnosis.

The binary `Unit_mod(F,G)` is not semantically necessary. Its meaning is always:

```text
Unit_mod(F,G)[a,b] = Hom_X(F[a],G[b]).
```

This can be reconstructed from:

```text
Hom_prof(G) : Prof(X,B)
Prof_reindex(Hom_prof(G), F, id_B) : Prof(A,B).
```

However, binary endpoints were operationally important in the Cartier draft
because `Unit_mod(F,G)` was the normal form for a reindexed representable. The
core substitution rules were:

```text
Unit_mod(F,G) << K  -> Unit_mod(F, G o K)
K >> Unit_mod(F,G)  -> Unit_mod(K o F, G)
```

This kept composed endpoints visible as direct arguments of `Unit_mod`, rather
than buried under a pullback/product-map/curry expression.

Places where this mattered:

```text
Yoneda actions:
  h : hom F R G
  h ∘>' N  : transf(Unit_mod(G,N), F, R << N, id)
  M _'∘> h : transf(Unit_mod(M,F), id, M >> R, G)

Tensor/co-Yoneda:
  coyoneda_Unit_Tensor_cov_transf matches P ⊗ Unit_mod(G,N).
  Here both G : B -> B' and N : J -> B' may be non-identity.

Internal hom:
  comp_Imply_cov_mod uses (Unit_mod(G,N) ⇐ W).

Weighted limits:
  limit_cov_univ_transf uses (Unit_mod(M,F) ⇐ W).
  limit_con_univ_transf uses (W ⇒ Unit_mod(F,M)).
  Here M : I -> B and F : J -> B are both genuine endpoints.

Adjunction accumulation/naturality:
  Adj_cov_hom and Adj_con_hom keep parameters Z and M/N as direct arguments,
  and rewrite them under extra substitutions.
  Several rules accumulate extra functor composition into both endpoint slots.

Duality:
  Op_mod(Unit_mod(F,G)) -> Unit_mod(Op_func(G), Op_func(F)).
```

From pure category-theory semantics, these do not force a primitive binary
unit. For example:

```text
P ⊗ Hom_B(G-,N-)
```

is a whiskered/reindexed co-Yoneda situation. It can be described from the
ordinary identity hom profunctor plus functorial restriction along `G` and
`N`. Similarly, `Unit_mod(M,F)` in weighted limits is just the hom profunctor
of `B` restricted along two shaped probes. Semantically, the two functors are
reindexing data.

What the Cartier draft shows is not semantic necessity; it shows that the old
rewrite system wanted the restriction data already absorbed into a visible
normal form before co-Yoneda, weighted-limit, adjunction, and duality rules
matched.

Therefore the refined conclusion is:

```text
Semantic necessity of primitive binary unit:
  no.

Operational need for a binary normal form:
  likely yes, unless Prof_reindex + primitive curry + comparison rules give
  equally stable normal forms.

Recommended v3.2 compromise:
  if binary endpoint rules are needed, make the binary head the only
  rewrite-facing hom-prof head;
  treat Hom_prof(G) as notation for Hom_prof_along(id_X,G), not as a competing
  primitive;
  orient Prof_reindex(Hom_prof_along(F,G),F',H) by endpoint composition;
  orient further reindexing of Hom_prof_along by endpoint composition;
  only then port co-Yoneda, weighted limits, adjunction, and duality rules.
```

In other words, the binary form is still only a reindexed hom profunctor
semantically, but if it appears in rewrite-rule LHSs it must be a
primitive/stable head, not a transparent alias. Avoid maintaining two competing
primitive heads:

```text
Hom_prof(G)
Hom_prof_along(id_X,G)
```

for the same normal form. Either orient one away immediately, or prefer a
single two-endpoint head and make the one-argument spelling notation.

Candidate normal-form rules:

```text
Hom_prof(G)
  := Hom_prof_along(id_X,G)        // notation/readability, not primitive

Prof_reindex(Hom_prof_along(id_X,G), F, H)
  -> Hom_prof_along(F, G o H)

Prof_reindex(Hom_prof_along(F,G), F', H)
  -> Hom_prof_along(F' o F, G o H)

curry*(Hom_prof_along(id_X,G))
  -> hom_int(G)

curry*(Hom_prof_along(F,G))
  -> hom_int(G) o Op_func(F)

Op_prof(Hom_prof_along(F,G))
  -> Hom_prof_along(Op_func(G), Op_func(F))
```

Composition order in the schematic rules must be adjusted to the landed
`comp_cat_fapp0` convention, but the invariant is clear: all reindexing cuts
on representables should accumulate into endpoint functor arguments before
co-Yoneda, weighted-limit, adjunction, or duality rules try to match them.

A focused probe with a primitive two-endpoint head confirmed this is feasible:

```text
Hom_prof_along(F,G)[a,b] -> Hom_X(F[a],G[b])
curry*(Hom_prof_along(F,G)) -> hom_int(G) o Op_func(F)
curry*(Hom_prof_along(id_X,G)) -> hom_int(G)
```

using the same canonical `Catd_cat(Product_cat(...))` and
`Functor_cat(...)(Catd_cat ...)` source/target forms required by the
single-argument primitive-curry probe.

### Curried Hom Infrastructure Versus General Profunctors

There are three different questions that should not be conflated.

First, internalize the existing `hom_int` in its present functor argument:

```text
hom_int(G) : X^op -> Catd(B)
G : B -> X
```

The smallest natural package is:

```text
hom_int_func(X,B)
  : (B -> X) -> (X^op -> Catd(B))
hom_int_func(X,B)[G] = hom_int(G)
```

This is a one-functor internalization. Its hom-action on a transformation
`eta : G => G'` is postcomposition by `eta`. If this package is added, it
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

Fixing another endpoint `F : A -> X` does not force `F` into the primitive
arity of `hom_int_func`. The current `comp_cat_con_func` already internalizes
precomposition by a fixed functor, so the complete fixed-`F` family can be
formed after `G` has been internalized:

```text
hom_int_along_func(F)
  := comp_cat_con_func(Op_func(F)) o hom_int_func(X,B)

hom_int_along_func(F)[G]
  = hom_int(G) o Op_func(F)
  : A^op -> Catd(B).
```

A focused probe typechecked this semantic definition and its object
projection. Therefore `hom_int_func` should not acquire an external `F`
parameter merely because later formulas use `Hom_X(F-,G-)`. Add a named
`hom_int_along_func(F)` stable head only if weighted-limit or adjunction rules
must match that partial family directly.

Second, internalize the left endpoint contravariantly. Fixing `G : B -> X`
gives the distinct package:

```text
hom_con_int_func(G)
  : Op_cat(Functor_cat A X) -> Prof_curried_cat(A,B)

hom_con_int_func(G)[F]
  = hom_int(G) o Op_func(F).
```

Although its object projection has the same expression as the fixed-`F`
package, its hom-action is different: a transformation in the original
`Functor_cat A X` direction acts by precomposition and therefore becomes
contravariant. This package is not supplied merely by the object-level
`hom_int_func`.

The current source already expresses:

```text
hom_con(W,F)[y] = Hom_X(F[y],W)
```

as an `injective` transparent definition through `hom_` over opposites. Its
action is then canonicalized to the primitive `hom_precomp_along_*` projection
heads. Thus the present evidence does not yet require changing `hom_con`
itself from a semantic alias to a primitive stable object head. The likely
missing primitive is the higher contravariant package
`hom_con_int_func(G)`, whose projections should reuse
`hom_precomp_along_*`. Reconsider primitive `hom_con` only if a concrete rule
must discriminate on `hom_con` before those projections are exposed.

Third, build the uncurried unit/representable profunctor from two endpoint
functors:

```text
F : A -> X
G : B -> X
Hom_prof_along(F,G)[a,b] = Hom_X(F[a],G[b]).
```

This is a two-functor construction. It can be factored through the one-functor
package by substitution and uncurry:

```text
Hom_prof_along(F,G)
  = uncurry(hom_int(G) o Op_func(F)).
```

So if a later `Hom_prof_along_func2` exists, it should be understood as:

```text
Hom_prof_along_func2(F,G)
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
`hom_int_func` or `Hom_prof_along_func2` projection rules.

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

The two one-endpoint uncurried packages should project to the same binary
normal form:

```text
Hom_prof_cov_func(F)
  : Functor_cat B X -> Prof_cat(A,B)
Hom_prof_cov_func(F)[G] = Hom_prof_along(F,G)

Hom_prof_con_func(G)
  : Op_cat(Functor_cat A X) -> Prof_cat(A,B)
Hom_prof_con_func(G)[F] = Hom_prof_along(F,G).
```

A focused probe typechecked both signatures and projection rules. This is
preferable to immediately internalizing the pair `(F,G)`, because the weighted
limit universal properties vary only one probe endpoint at a time:

```text
Hom_prof_along(M,F)  // M varies contravariantly
Hom_prof_along(F,M)  // M varies covariantly.
```

None of these packages replaces general profunctors. They describe only
representable/unit profunctors. A general profunctor is an arbitrary family:

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

Hom_prof_along_func2:
  yes, as the binary endpoint package for Hom_X(F[a],G[b]);
  no, as the full profunctor concept.

Prof_curried_cat / Prof_cat:
  yes, as the full profunctor concept, with curried and uncurried surfaces.
```

So the globally coherent architecture is:

```text
ordinary hom infrastructure
  hom_int(G)
  hom_int_func(X,B)                    // G varies covariantly
  hom_int_along_func(F)                // semantic fixed-F postprocessing
  hom_con_int_func(G)                  // F varies contravariantly, if needed
  tapp1_int_func_transf(F,G)

representable/unit profunctors
  Hom_prof_along(F,G)                  // single binary rewrite normal form
  Hom_prof(G) = Hom_prof_along(id_X,G)
  Unit_prof(X) = Hom_prof_along(id_X,id_X)
  Hom_prof_cov_func(F)                  // internalized G
  Hom_prof_con_func(G)                  // internalized F
  Hom_prof_along_func2                  // only if both must vary

general profunctors
  Prof_curried_cat(A,B)                // optional facade
  Prof_cat(A,B) = Catd_cat(A^op x B)   // product-base facade
```

The maps between these layers should be explicit comparison/projection maps.
They should not be collapsed by broad rewrite rules.

#### Direct Product Projections Versus Curry Comparison

`Hom_prof_along` needs direct product-base projections regardless of whether a
curry comparison exists:

```text
fapp0(Hom_prof_along(F,G),(a,b))
  -> Hom_X(F[a],G[b])

fapp1_func(Hom_prof_along(F,G),...)
  -> the existing pre/postcomposition hom-action packages

fapp1_fapp0(Hom_prof_along(F,G),...)
  -> the capped pre/postcomposition action.
```

These computations are used by profunctor reindexing, tensor, co-Yoneda, and
direct fibre inspection. A curry projection cannot replace them.

Conversely, a curry comparison exposes the whole curried family and lets the
new profunctor head inherit the existing `hom_int` theory:

```text
Prof_curry(Hom_prof_along(F,G))
  -> hom_int(G) o Op_func(F).
```

The recommended design is therefore hybrid:

```text
direct fapp* projections:
  foundational computation of the uncurried Hom_prof_along head

stable Prof_curry comparison:
  bridge to hom_int and the curried partial packages

ordinary curry_func_func:
  retain its current semantic implementation unless generic curry rules,
  independently of profunctors, prove that it must again be primitive.
```

Git history confirms that the present ordinary-curry design was deliberate.
Before commit `e867e2a` on June 1, 2026, `curry_func`, `curry_func_func`, and
several curry-specific action heads were primitive. That commit redefined
`curry_func_func` through `Product_pair_tele_func`,
`comp_cat_cov_func_func`, and `comp_cat_con_func`, and removed the duplicated
curry-specific action ladder. The historical rearchitecture report included
in that commit says that generic pairing and pre/postcomposition should own
those computations.

#### Product-Functor Adjunction Interpretation

For a fixed category `B`, the ordinary categorical owner of curry/uncurry is
the adjunction:

```text
L_B(A) := Product_cat A B
R_B(C) := Functor_cat B C

L_B is left adjoint to R_B
```

with unit and counit components:

```text
eta_A : A -> Functor_cat B (Product_cat A B)
eta_A  = Product_pair_tele_func(A,B)
eta_A[x][y] = (x,y)

epsilon_C : Product_cat (Functor_cat B C) B -> C
epsilon_C = Eval_func(B,C)
epsilon_C[(G,y)] = G[y].
```

Thus the current semantic definitions have exactly the standard mate
factorizations:

```text
curry(F : A x B -> C)
  = R_B(F) o eta_A
  = comp_cat_cov_func(F) o Product_pair_tele_func(A,B)

uncurry(G : A -> Functor_cat B C)
  = epsilon_C o L_B(G)
  = Eval_func(B,C) o (G x id_B).
```

So the understanding that the curry/uncurry correspondence is definable from
the unit-counit presentation of this adjunction is correct. More precisely, the
unit and counit induce the mate maps between:

```text
Functor_cat (Product_cat A B) C
Functor_cat A (Functor_cat B C).
```

In ordinary `Cat` this is naturally an isomorphism of functor categories, not
only a bijection of object sets. The present v3.2 source implements the
underlying functors and their principal pointwise computations, but it does not
yet package the complete adjunction or prove all of:

```text
naturality of eta and epsilon in the category variables;
the two triangle identities;
curry(uncurry(G)) = G and uncurry(curry(F)) = F at the full
functor/transformation level;
compatibility with the higher transfor actions needed by the omega setting.
```

This also clarifies the "more basic primitives" question. The unit component
already decomposes computationally into constant sections, identity, product
pairing, and pre/postcomposition. The left action `L_B(G) = G x id_B`
decomposes through the product-functor infrastructure. Evaluation is canonical
from the functor-category semantics, but it is not supplied by binary products
alone; the current kernel keeps `Eval_func` as a named computational
constructor with pointwise object and hom-action rules. Future work may further
factor its implementation, but should preserve evaluation as the semantic
owner of application.

Consequently, do not globally revert `curry_func_func` merely to obtain a
rewrite discriminator for hom profunctors. First probe a profunctor-specific
stable comparison:

```text
Prof_curry_func(A,B)
  : Prof_cat(A,B) -> Prof_curried_cat(A,B)

Prof_curry_func(A,B)[Hom_prof_along(F,G)]
  -> hom_int(G) o Op_func(F).
```

This preserves the ordinary semantic curry architecture while giving
profunctor rules a stable head. Promote global `curry_func_func` back to a
primitive only if the same rewrite-facing need appears for non-profunctor
consumers too.

Because ordinary `curry_func_func` and `uncurry_func_func` are semantic
composites with nontrivial `comp_cat_fapp0` cuts, avoid broad rules that fold
arbitrary:

```text
uncurry(hom_int(G) o Op_func(F))
```

into a primitive binary head. Prefer:

```text
Hom_prof_along(F,G)                 // binary uncurried normal form
direct fapp* projections             // product-base computation
Prof_curry comparison                // bridge to hom_int
one-endpoint packages                // only as demanded by universal formulas
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

The partial-internalization probe additionally confirmed:

```text
hom_int_func(X,B)[G] = hom_int(G)

hom_int_along_func(F)
  := comp_cat_con_func(Op_func(F)) o hom_int_func(X,B)

hom_con_int_func(G)[F]
  = hom_int(G) o Op_func(F)

Hom_prof_cov_func(F)[G] = Hom_prof_along(F,G)
Hom_prof_con_func(G)[F] = Hom_prof_along(F,G).
```

Only the signatures, object projections, and fixed-`F` semantic composition
were probed. Their transformation/hom actions remain implementation work and
must be routed through the existing post/precomposition heads.

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

The semantic specification should start with the single-argument core:

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

Read this as the semantic specification. Two implementation routes were
probed:

```text
Route A: one-argument stable head
  Hom_prof(G) is primitive/stable.
  Hom_prof_along(F,G) is added only if a later probe proves it is needed.

Route B: two-endpoint stable head
  Hom_prof_along(F,G) is the only rewrite-facing primitive.
  Hom_prof(G) is notation for Hom_prof_along(id_X,G).
```

Route A remains mathematically valid and its direct fibre rule typechecks, but
the Cartier rewrite audit and the endpoint-internalization analysis now favor
Route B. Route B avoids competing heads and keeps all reindexing cuts visible
as endpoint arguments.

If Route A were chosen and needed a primitive curry projection:

```text
curry*(Hom_prof(G)) -> hom_int(G)
```

then `Hom_prof` should be declared as a stable/injective head with projection
rules, not merely as a transparent `≔` alias. The `Hom_catd` expression remains
the correctness model and comparison check.

For the recommended Route B, the stable profunctor-curry projections are:

```text
curry*(Hom_prof_along(F,G)) -> hom_int(G) o Op_func(F)
curry*(Hom_prof_along(id_X,G)) -> hom_int(G)
```

The two-endpoint primitive probe confirmed this route is mechanically feasible.

Either way, specify the binary endpoint form semantically by left reindexing:

```text
Hom_prof_along(F,G)
  := Prof_reindex(Hom_prof(G), F, id_B)
```

The direct single-argument fibre rule has been probed successfully, but it is
now a semantic comparison result rather than the proposed rewrite API.
`Hom_prof_along` should be an injective/stable symbol with fold rules from
representable reindexing. Do not implement it as a transparent alias because
co-Yoneda, weighted-limit, adjunction, and duality rules are expected to match
it in their LHSs.

Then define the old Cartier-shaped element category:

```text
Prof_transf_cat(R',F,R,G)
  := Functord_cat R' (Prof_reindex(R,F,G))

Prof_hom(F,R,G)
  := Obj(Prof_transf_cat(Unit_prof(I),F,R,G))
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

For the semantic one-argument comparison model:

```text
K      := Prof_base(X,B)
source := Product_projL_func(Op_cat X,B)
target := G o Product_projR_func(Op_cat X,B)

Hom_prof(G) := Hom_catd(Const_catd(K,X), source, target)
```

Again, this is the semantic specification. The implementation can use an
identity-left specialization of the binary stable head:

```text
Hom_prof(G) := Hom_prof_along(id_X,G).
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

The actual rewrite-facing declaration should be the binary endpoint surface:

```text
injective symbol Hom_prof_along(F,G) : Prof(A,B)

fibre(Hom_prof_along(F,G),(a,b))
  -> Hom_X(F[a],G[b])

Prof_reindex(Hom_prof_along(F,G),F',G')
  -> Hom_prof_along(F o F',G o G')
```

The exact composition order must follow `comp_cat_fapp0`, and the hom-action
projections must be probed against `hom_precomp_along_*` and
`hom_postcomp_*`. The semantic identity:

```text
Hom_prof_along(F,G)
  = Prof_reindex(Hom_prof(G),F,id_B)
```

should be retained as a comparison/fold rule, not as a transparent definition.

After the fixed-parameter object rules pass, add only the one endpoint package
needed by the first universal-property check:

```text
Hom_prof_con_func(G)[F] = Hom_prof_along(F,G)
Hom_prof_cov_func(F)[G] = Hom_prof_along(F,G).
```

The first `Prof_hom` API should be:

```text
Prof_transf_cat(R',F,R,G)
  : Cat
  := Functord_cat R' (Prof_reindex(R,F,G))

Prof_hom_cat(F,R,G)
  : Cat
  := Prof_transf_cat(Unit_prof(I),F,R,G)

Prof_hom(F,R,G)
  : Grpd
  := Obj(Prof_hom_cat(F,R,G))
```

This is a shaped profunctor element. In the representable case:

```text
R = Unit_prof(C)
F,G : I -> C
```

it should behave like the category/type of natural transformations `F => G`.
Do not force this as a global rewrite initially; add a named comparison or a
focused check once the `Prof_hom` projection surface is known.

Representable profunctors for ordinary functors should be aliases:

```text
Cov_repr_prof(F : A -> B) := Hom_prof_along(F,id_B)  : Prof(A,B)
Con_repr_prof(G : B -> A) := Hom_prof_along(id_A,G)  : Prof(A,B)
```

These are important later because adjunctions are most naturally bridges
between the covariant and contravariant representables of the left and right
adjoint functors.

### Implementation Log 2026-06-18: Phase 1a

The first bounded implementation slice is now active in `emdash3_2.lp`.
It intentionally stops before general profunctor reindexing and shaped
profunctor elements.

Landed transparent aliases:

```text
Prof_base(A,B) := Product_cat (Op_cat A) B
Prof_cat(A,B)  := Catd_cat(Prof_base(A,B))
Prof(A,B)      := Obj(Prof_cat(A,B))
```

Landed stable representable owner:

```text
Hom_prof_along(F,G) : Catd(Product_cat(Op_cat A,B))
Hom_prof_along(F,G)[ab]
  = Hom_X(F[sigma_Fst(ab)],G[sigma_Snd(ab)])
```

The implementation confirmed Route B from the design review:

```text
Hom_prof(G) := Hom_prof_along(id_X,G)
Unit_prof(X) := Hom_prof_along(id_X,id_X)
```

Both are transparent specializations. There is no competing primitive
`Hom_prof` or `Unit_prof` head.

The first full action rung is:

```text
Hom_prof_along_fapp1_func(F,G,ab,ab')
```

and for:

```text
ab  = (a,b)
ab' = (a',b')
p : a' ->^A a
q : b  ->^B b'
```

its action computes as:

```text
h |-> G[q] o h o F[p].
```

The rule is factored through the existing semantic owners:

```text
hom_precomp_along_func(F,G[b],p)
hom_postcomp_func(G,F[a'],q)
```

rather than introducing profunctor-specific pre/postcomposition helpers.
The direct capped `fapp1_fapp0` rule joins the generic
`fapp0(fapp1_func(...),...)` route at the same composite.

One initial probe attempted to pattern the full action only at explicit
`Struct_sigma(a,b)` endpoints. Although the object rule worked, that full
action surface was brittle for subject reduction and matching. The accepted
design computes on arbitrary product objects using:

```text
sigma_Fst(ab)
sigma_Snd(ab)
```

and keeps explicit pairs only in diagnostic assertions. This is both more
general and more consistent with the existing product-projection architecture.

The active checks cover:

```text
the three facade aliases;
the representable fibre formula;
the full action projection;
the capped pre/postcomposition composite;
the element action h |-> G[q] o h o F[p];
the Hom_prof and Unit_prof fibre specializations;
pointwise agreement with the Hom_catd semantic model.
```

Deferred from this slice at the time of Phase 1a; the first two items were
subsequently landed in Phase 1b:

```text
Product_map_func or another two-sided product-map owner;
Prof_reindex and its representable fold;
Prof_transf_cat, Prof_hom_cat, and Prof_hom;
Hom_prof_con_func and Hom_prof_cov_func;
Prof_curry_func and comparison with hom_int;
Cov_repr_prof and Con_repr_prof notation.
```

The focused probe and the bounded active check both passed. The probe log is:

```text
logs/probes/profunctor_phase1_facade_probe-20260618-165702.log
```

### Implementation Log 2026-06-18: Phase 1b

The second bounded slice adds the general two-sided product map and profunctor
reindexing.

The general product map remains a transparent semantic construction:

```text
Product_map_func(F,G)
  := (F o Product_projL_func, G o Product_projR_func)

Product_map_func(F,G)[(a,b)] = (F[a],G[b])
Product_map_func(F,G)[(p,q)] = (F[p],G[q]).
```

Its checks cover both the full `fapp1_func` projections and the capped
`fapp1_fapp0` projections. No new primitive product-map action hierarchy was
introduced.

The initial probe then tried:

```text
Prof_reindex(R,F,G)
  := Pullback_catd(R,Product_map_func(Op_func(F),G)).
```

as a transparent definition. Its fibre and arrow computations worked, but
Lambdapi refused the required representable fold because a rewrite rule cannot
target a symbol already defined with `≔`. This is the concrete operational
reason for promoting reindexing itself.

The landed architecture is therefore:

```text
symbol Prof_reindex(R,F,G) : Prof(A',B')

Prof_reindex(R,F,G)[a',b'] = R[F[a'],G[b']]

Prof_reindex_fapp1_func(R,F,G,ab,ab')
  : Hom(ab,ab') ->
      (Prof_reindex(R,F,G)[ab] ->
       Prof_reindex(R,F,G)[ab']).
```

`Prof_reindex` is stable but deliberately not declared injective. Its object,
full-action, and capped-action rules all route through:

```text
Product_map_func(Op_func(F),G)
```

and the original `R` action. Thus the stable head supplies rewrite
discrimination without claiming that reindexing data can be semantically
recovered from the resulting profunctor.

The representable accumulation rule is now active:

```text
Prof_reindex(Hom_prof_along(F,G),F',G')
  -> Hom_prof_along(F o F',G o G').
```

In particular:

```text
Prof_reindex(Hom_prof(G),F,id_B)
  -> Hom_prof_along(F,G).
```

Nested general reindexing and identity reindexing are intentionally deferred.
Adding them now would introduce associativity and overlap obligations not
needed by the first shaped-element construction. They should be probed when a
specific downstream formula requires those normal forms.

The active checks cover:

```text
Product_map_func object action;
Product_map_func full and capped arrow action;
Prof_reindex fibre computation;
Prof_reindex full and capped arrow action;
general representable endpoint accumulation;
the Hom_prof left-reindex specialization.
```

The successful focused probe log is:

```text
logs/probes/profunctor_phase1b_reindex_probe-20260618-170923.log
```

### Implementation Log 2026-06-18: Phase 1c

The third bounded slice adds the shaped-cell and shaped-element layer without
promoting any new stable head:

```text
Prof_transf_cat(R',F,R,G)
  := Functord_cat(R',Prof_reindex(R,F,G))

Prof_hom_cat(F,R,G)
  := Prof_transf_cat(Unit_prof(I),F,R,G)

Prof_hom(F,R,G)
  := Obj(Prof_hom_cat(F,R,G)).
```

Here:

```text
R' : Prof(A',B')
F  : A' -> A
R  : Prof(A,B)
G  : B' -> B.
```

Thus `Prof_transf_cat` is the category of natural family morphisms:

```text
R' -> Prof_reindex(R,F,G)
```

on the common base `A'^op × B'`. The shaped-element specialization uses a
single probe category `I` on both sides and the source `Unit_prof(I)`.

A focused probe confirmed that transparent definitions are sufficient. In
particular:

```text
Prof_hom_cat(F,Unit_prof(C),G)
  -> Functord_cat(Unit_prof(I),Hom_prof_along(F,G)).
```

This is the intended representable shaped-element normal form. The reduction
uses the Phase 1b representable reindex fold; it does not require a new
`Prof_hom` discriminator.

The implementation deliberately does not install a global rewrite:

```text
Prof_hom_cat(F,Unit_prof(C),G) -> Transf_cat(F,G).
```

Although these categories should be related by the representable/Yoneda
semantics, they are not presently definitionally identical in the kernel.
Any such relationship should first be exposed by a named comparison map or
isomorphism with focused component and naturality checks.

The first Phase 1c checks cover:

```text
the general Prof_transf_cat classifier;
the Prof_hom_cat common-shape specialization;
the Prof_hom object classifier;
the Unit_prof representable target fold;
general representable endpoint accumulation under Prof_transf_cat.
```

No endpoint-internalized `Hom_prof_*_func` package and no curry comparison was
needed by these checks. Those remain demand-driven side tasks for the first
tensor, implication, weighted-limit, or adjunction formula that genuinely
quantifies over an endpoint.

The successful focused probe log is:

```text
logs/probes/profunctor_phase1c_shaped_elements_probe-20260618-195732.log
```

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
Unit_prof(B) = Hom_prof(id_B) : Prof(B,B)
```

Do not collapse:

```text
R tensor Unit_prof(B)
Unit_prof(A) tensor R
```

at the type level until there is a concrete associativity/unit coherence test.

### Implementation Log 2026-06-18: Phase 2a-b

The first tensor slice is now active as a symbolic bicategorical calculus.
The tensor itself is a stable, opaque primitive:

```text
Prof_tensor(R,S) : Prof(A,X)

R : Prof(A,B)
S : Prof(B,X).
```

No fibre formula is claimed. In particular, the implementation does not
encode a fake Sigma category in place of the missing coend quotient.

General endpoint reindexing computes by:

```text
Prof_reindex(Prof_tensor(R,S),F,G)
  -> Prof_tensor(
       Prof_reindex(R,F,id_B),
       Prof_reindex(S,id_B,G)).
```

This rule justified activating the previously deferred neutral law:

```text
Prof_reindex(R,id_A,id_B) -> R.
```

The focused probe checked the overlap at identity endpoint functors. It joins:
the tensor-distribution branch reduces both inner identity reindexings and
reaches the same `Prof_tensor(R,S)` normal form. The representable reindex fold
also joins the identity rule because composition with identity reduces.

The first equipment-cell constructor is:

```text
Prof_tensor_transf(r,s).
```

For:

```text
r : Prof_transf_cat(R',F,R,M)
s : Prof_transf_cat(S',M,S,G),
```

it produces:

```text
Prof_transf_cat(
  Prof_tensor(R',S'),
  F,
  Prof_tensor(R,S),
  G).
```

This is a deliberate redesign of the Cartier surface. The old
`Tensor_cov_transf` and `Tensor_con_transf` differed only in where a middle
substitution was syntactically exposed. In v3.2, `Prof_transf_cat` already
records both endpoint functors and both old premises elaborate to the same
general cell type. Keeping two primitive constructors would therefore create
duplicate normal forms without semantic content.

The first shaped introduction forms are:

```text
Prof_tensor_hom_hom(M,r,s)
  : Prof_hom(F,Prof_tensor(R,S),G)

Prof_tensor_hom_transf(M,r,s)
  : Prof_transf_cat(R',F,Prof_tensor(R,S),G).
```

The named right- and left-unit co-Yoneda maps are:

```text
Prof_coyoneda_unit_tensor_cov_transf(pp,N)
  : Prof_transf_cat(
      Prof_tensor(P,Hom_prof_along(G,N)),
      F,
      P',
      N)

Prof_coyoneda_unit_tensor_con_transf(pp,M)
  : Prof_transf_cat(
      Prof_tensor(Hom_prof_along(M,F),P),
      M,
      P',
      G).
```

They retain both non-identity endpoint functors directly in
`Hom_prof_along`, as required by the co-Yoneda semantics reviewed from the old
draft. They are named cells, not type-level rewrites:

```text
Prof_tensor(P,Unit_prof) -> P
Unit_prof tensor P -> P
```

remain intentionally absent.

The first probe attempt wrote cell terms as `τ(Prof_transf_cat(...))`. It
failed because `Prof_transf_cat` is a category, not its object classifier.
The accepted declarations use the canonical:

```text
τ(Obj(Prof_transf_cat(...))).
```

No readability-only `Prof_transf` classifier was added.

Co-Yoneda beta rules remain deferred for a concrete architectural reason. A
beta statement must compose or apply a cell:

```text
R' -> Prof_reindex(R,F,G)
```

to another cell or shaped element whose base is itself reindexed. The active
kernel does not yet have the general equipment-cell composition/application
operation. Implementing it plausibly requires:

```text
reindexing a Functord cell along endpoint functors;
nested Prof_reindex accumulation;
composition through comp_catd_fapp0;
focused identity and associativity joins.
```

This is the next Phase 2 prerequisite. Adding one-off co-Yoneda cancellation
heads before that operation exists would duplicate the missing general
calculus.

The active checks cover:

```text
neutral profunctor reindexing;
general, left-only, right-only, and identity tensor reindexing;
representable accumulation inside tensor reindexing;
the general tensor-cell constructor;
both shaped tensor introductions;
both named co-Yoneda cell types.
```

Successful focused probe logs:

```text
logs/probes/profunctor_phase2a_tensor_reindex_probe-20260618-200925.log
logs/probes/profunctor_phase2b_tensor_cells_probe-20260618-201218.log
```

The failed classifier probe is retained as:

```text
logs/probes/profunctor_phase2b_tensor_cells_probe-20260618-201134.log
```

### Implementation Log 2026-06-18: Phase 2c

The general equipment-cell composition/application prerequisite and the first
computational co-Yoneda rules are now active.

#### Endpoint accumulation

Iterated ordinary functor composition now has the left-associated normal form:

```text
H o (G o F) -> (H o G) o F.
```

This orientation was added only after nested profunctor reindexing required a
join with representable endpoint accumulation. It joins the existing left and
right identity rules in the focused probe.

Nested profunctor reindexing now computes:

```text
Prof_reindex(Prof_reindex(R,F,G),F',G')
  -> Prof_reindex(R,F o F',G o G').
```

The representable overlap joins because functor composition is normalized
left-associatively. Identity and tensor-reindexing overlaps also passed the
focused assertions.

#### Internalized reindexing

The attempted semantic definition:

```text
Prof_reindex_func(F,G)
  := Pullback_catd_func(Product_map_func(Op_func(F),G))
```

did not provide a usable arrow action. The transparent body unfolded to
`Pullback_catd` before the object projection could expose the stable
`Prof_reindex` endpoint, leaving unsolved conversion goals between semantic
pullbacks and stable profunctor families.

The landed package is therefore:

```text
Prof_reindex_func(F,G)
  : Prof_cat(A,B) -> Prof_cat(A',B')

Prof_reindex_func(F,G)[R]
  -> Prof_reindex(R,F,G)

Prof_reindex_transf(r,F,G)
  : Functord(
      Prof_reindex(R,F,G),
      Prof_reindex(S,F,G)).
```

The identity action computes:

```text
Prof_reindex_transf(r,id_A,id_B) -> r.
```

These stable heads are justified projection owners, not an alternative
semantics: pullback along `Op_func(F) × G` remains the comparison model.

#### General cell composition

For:

```text
r : Prof_transf_cat(R0,F01,R1,G01)
s : Prof_transf_cat(R1,F12,R2,G12),
```

the stable composite is:

```text
Prof_comp_transf(s,r)
  : Prof_transf_cat(
      R0,
      F12 o F01,
      R2,
      G12 o G01).
```

Its semantic route is:

```text
comp_catd_fapp0(
  Prof_reindex_transf(s,F01,G01),
  r)
  -> Prof_comp_transf(s,r).
```

The first attempt kept `Prof_comp_transf` transparent, but Lambdapi correctly
refused co-Yoneda rewrite rules on a symbol defined with `≔`. Composition was
therefore promoted to a stable head only after this concrete rewrite-facing
failure.

`Prof_id_transf(R)` is the stable identity cell, with:

```text
Prof_comp_transf(Prof_id_transf(R1),r) -> r
Prof_comp_transf(s,Prof_id_transf(R0)) -> s.
```

The probe also tested a fold from generic `id_funcd`, but `id_funcd` is a
protected constant and cannot head a new rule. No global identity behavior was
changed. `Prof_id_hom(B)` is only readable notation for the identity cell of
the unit profunctor.

#### Symmetric tensor introductions

The already active introductions are now completed by:

```text
Prof_tensor_transf_hom(M,r,s),
```

which combines a shaped element on the left with a general cell on the right.
Together:

```text
Prof_tensor_hom_transf   // general left, shaped right
Prof_tensor_transf_hom   // shaped left, general right
Prof_tensor_hom_hom      // shaped on both sides
Prof_tensor_transf       // general on both sides
```

cover the first tensor-introduction surface without duplicating Cartier's
syntactic covariant/contravariant split.

#### Co-Yoneda beta

Both named co-Yoneda maps now cancel tensor introduction in the
identity-representable case:

```text
Prof_comp_transf(
  Prof_coyoneda_unit_tensor_cov_transf(pp,id_B),
  Prof_tensor_hom_transf(id_B,qq,Prof_id_hom(B)))
  -> Prof_comp_transf(pp,qq)

Prof_comp_transf(
  Prof_coyoneda_unit_tensor_cov_transf(pp,id_B),
  Prof_tensor_hom_hom(id_B,p,Prof_id_hom(B)))
  -> Prof_comp_transf(pp,p)

Prof_comp_transf(
  Prof_coyoneda_unit_tensor_con_transf(pp,id_A),
  Prof_tensor_transf_hom(id_A,Prof_id_hom(A),qq))
  -> Prof_comp_transf(pp,qq)

Prof_comp_transf(
  Prof_coyoneda_unit_tensor_con_transf(pp,id_A),
  Prof_tensor_hom_hom(id_A,Prof_id_hom(A),p))
  -> Prof_comp_transf(pp,p).
```

The actual rule LHSs use the stable canonical form:

```text
Hom_prof_along(id_X,id_X)
```

rather than transparent `Unit_prof(X)`. A probe using `Unit_prof` as the
discriminator compiled a branch but failed to reduce after the alias unfolded.
This confirms the Phase 1 policy that `Hom_prof_along` is the sole
rewrite-facing representable head.

These are deliberately narrow beta rules. General co-Yoneda cancellation along
an arbitrary functor requires a canonical shaped element:

```text
Prof_func_hom(F)
  : Prof_hom(F,Unit_prof(B),F),
```

packaging the hom-action of `F`. Phase 6a now supplies this as the transparent
shaped view `Prof_func_hom(F)` of the stable equipment cell
`Prof_func_transf(F)`. Generalizing the co-Yoneda beta LHSs remains a separate
task.

Still deferred:

```text
associativity/coherence rules for Prof_comp_transf;
tensor associator and unitors;
general co-Yoneda beta rules using Prof_func_hom(F);
type-level tensor-unit collapses;
coend/coinserter semantics.
```

The active checks cover:

```text
left-associated ordinary functor composition;
nested profunctor reindexing;
Prof_reindex_func object projection;
Prof_reindex_transf type and identity action;
Prof_comp_transf type and semantic fold;
left and right composition identities;
the missing symmetric tensor introduction;
two right-unit and two left-unit co-Yoneda beta reductions.
```

Successful focused probe logs:

```text
logs/probes/profunctor_phase2c_cell_composition_probe-20260618-204159.log
logs/probes/profunctor_phase2c_left_coyoneda_probe-20260618-204527.log
```

Important failed probes influencing the design:

```text
logs/probes/profunctor_phase2c_cell_composition_probe-20260618-203557.log
  transparent Prof_reindex_func did not expose stable endpoints;

logs/probes/profunctor_phase2c_cell_composition_probe-20260618-203740.log
  transparent Prof_comp_transf could not own beta rules;

logs/probes/profunctor_phase2c_cell_composition_probe-20260618-203941.log
  generic id_funcd is protected and was left unchanged;

logs/probes/profunctor_phase2c_cell_composition_probe-20260618-204020.log
  transparent Unit_prof was unsuitable as a rewrite discriminator.
```

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

### Implementation Log 2026-06-18: Phase 3a

The covariant implication and lambda calculus are now active.

For:

```text
O : Prof(A,X)
Q : Prof(B,X),
```

the stable primitive is:

```text
Prof_imply_cov(O,Q) : Prof(A,B).
```

This is the symbolic right adjoint to:

```text
P |-> Prof_tensor(P,Q).
```

No fibre/end formula is claimed. As with tensor, the current implementation
provides a computational universal calculus without pretending that the
missing end construction is already present.

#### Reindexing

Result endpoint reindexing computes by:

```text
Prof_reindex(Prof_imply_cov(O,Q),F,M)
  -> Prof_imply_cov(
       Prof_reindex(O,F,id_X),
       Prof_reindex(Q,M,id_X)).
```

Thus the first result endpoint acts on the left endpoint of `O`, while the
second result endpoint acts contravariantly through the left endpoint of `Q`.
The identity overlap reduces back to `Prof_imply_cov(O,Q)` using the Phase 2
neutral reindex rule.

#### Mixed-variance cell action

For:

```text
o : Prof_transf_cat(O,F,O',id_X)
q : Prof_transf_cat(Q',M,Q,id_X),
```

the constructor:

```text
Prof_imply_cov_transf(o,q)
```

has target:

```text
Prof_transf_cat(
  Prof_reindex(Prof_imply_cov(O,Q),id_A,M),
  F,
  Prof_imply_cov(O',Q'),
  id_B').
```

This records the correct variance directly: covariant in `O`, contravariant
in `Q`. It is the cleaned-up v3.2 counterpart of Cartier's
`Imply_cov_transf`.

#### General eval/lambda

For:

```text
P : Prof(A,B)
Q : Prof(B,X)
O : Prof(A',X)
F : A -> A',
```

the two stable operations are:

```text
Prof_eval_cov_transf:
  Prof_transf_cat(P,F,Prof_imply_cov(O,Q),id_B)
  ->
  Prof_transf_cat(Prof_tensor(P,Q),F,O,id_X)

Prof_lambda_cov_transf:
  Prof_transf_cat(Prof_tensor(P,Q),F,O,id_X)
  ->
  Prof_transf_cat(P,F,Prof_imply_cov(O,Q),id_B).
```

Both cancellation directions compute:

```text
Prof_lambda_cov_transf(Prof_eval_cov_transf(t)) -> t
Prof_eval_cov_transf(Prof_lambda_cov_transf(t)) -> t.
```

The rule LHSs keep category, profunctor, and endpoint parameters explicit.
The first compact probe could not reconstruct the common tensor codomain
through two nested polymorphic heads. Explicit stable parameters solved the
subject-reduction problem without changing the public constructor types.

#### Shaped eval/lambda

The shaped specialization is:

```text
Prof_eval_cov_hom_transf:
  Prof_hom(F,Prof_imply_cov(O,Q),id_A)
  ->
  Prof_transf_cat(Q,F,O,id_X)

Prof_lambda_cov_transf_hom:
  Prof_transf_cat(Q,F,O,id_X)
  ->
  Prof_hom(F,Prof_imply_cov(O,Q),id_A).
```

It also has both beta/eta cancellations. This is the direct replacement for
Cartier's `Eval_cov_hom_transf` and `Lambda_cov_transf_hom`, expressed through
the landed shaped-element API rather than a separate primitive `hom` type.

The active checks cover:

```text
general and identity implication reindexing;
the mixed-variance implication cell type;
general eval-after-lambda and lambda-after-eval;
shaped eval-after-lambda and lambda-after-eval.
```

The successful focused probe log is:

```text
logs/probes/profunctor_phase3a_imply_cov_probe-20260618-210306.log
```

The initial compact beta-rule failure is retained as:

```text
logs/probes/profunctor_phase3a_imply_cov_probe-20260618-210209.log
```

Deferred to later focused slices:

```text
naturality of eval/lambda under Prof_tensor_transf;
fixed-base internalized Prof_imply_cov_func(Q);
fixed-base internalized Prof_imply_con_func(P);
two-variable implication functors;
end-based semantics or comparison maps;
interaction with Prof_comp_transf beyond beta/eta.
```

### Implementation Log 2026-06-18: Phase 3b

The contravariant implication and its symmetric lambda calculus are now active.

For:

```text
P : Prof(A,B)
O : Prof(A,X),
```

the stable primitive is:

```text
Prof_imply_con(P,O) : Prof(B,X).
```

It is the symbolic right adjoint to:

```text
Q |-> Prof_tensor(P,Q).
```

As on the covariant side, this is a computational universal interface rather
than a claim that the missing end construction has already been implemented.

#### Reindexing

Result endpoint reindexing computes by:

```text
Prof_reindex(Prof_imply_con(P,O),M,G)
  -> Prof_imply_con(
       Prof_reindex(P,id_A,M),
       Prof_reindex(O,id_A,G)).
```

Thus the first result endpoint acts on the right endpoint of `P`, while the
second result endpoint acts on the right endpoint of `O`. Identity reindexing
again joins with the general Phase 2 neutral rule.

#### Mixed-variance cell action

For:

```text
p : Prof_transf_cat(P',id_A,P,M)
o : Prof_transf_cat(O,id_A,O',G),
```

the constructor:

```text
Prof_imply_con_transf(p,o)
```

maps the left-reindexed source implication to `Prof_imply_con(P',O')`.
This records the semantic variance directly: contravariant in `P`, covariant
in `O`. It is the v3.2 replacement for Cartier's `Imply_con_transf`, with the
arguments ordered like the implication inputs rather than preserving the old
surface order.

#### General eval/lambda

For:

```text
P : Prof(A,B)
Q : Prof(B,X)
O : Prof(A,X')
G : X -> X',
```

the checked inverse operations implement:

```text
Prof_transf_cat(Q,id_B,Prof_imply_con(P,O),G)
  <->
Prof_transf_cat(Prof_tensor(P,Q),id_A,O,G).
```

Both beta/eta cancellation directions compute. Their rule LHSs keep all
category, profunctor, and endpoint arguments explicit, following the stable
Phase 3a pattern.

#### Shaped eval/lambda

Setting `Q = Unit_prof(B)` and applying the right-unit co-Yoneda reading gives
the symmetric shaped interface:

```text
Prof_hom(id_B,Prof_imply_con(P,O),G)
  <->
Prof_transf_cat(P,id_A,O,G).
```

This shaped pair was absent as a complete lambda calculus in the old Cartier
draft, but follows from the same tensor-hom adjunction and required no new
kernel primitive. It is useful for the later dual weighted-colimit surface.

The active checks cover:

```text
general and identity implication reindexing;
the mixed-variance implication cell type;
general eval-after-lambda and lambda-after-eval;
shaped eval-after-lambda and lambda-after-eval.
```

The strengthened focused probe log is:

```text
logs/probes/profunctor_phase3b_imply_con_probe-20260618-220433.log
```

Deferred from this slice:

```text
naturality of eval/lambda under Prof_tensor_transf;
interaction with Prof_comp_transf beyond beta/eta;
internalized implication functors;
end-based semantics or comparison maps.
```

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

### Implementation Log 2026-06-18: Phase 4a

The first covariant weighted-limit package is active:

```text
WeightedLimit_cov(F,W,L) : Grpd
```

for:

```text
F : J -> B
W : Prof(J',J)
L : J' -> B.
```

For every `M : I -> B`, a witness exposes inverse cells:

```text
weighted_limit_cov_univ_transf:
  Prof_imply_cov(Hom_prof_along(M,F),W)
  ->
  Hom_prof_along(M,L)

weighted_limit_cov_cone_transf:
  Hom_prof_along(M,L)
  ->
  Prof_imply_cov(Hom_prof_along(M,F),W).
```

Both cells live over identity endpoint functors on `I` and `J'`. Their two
composites reduce through `Prof_comp_transf` to the corresponding
`Prof_id_transf`. This packages the universal representable isomorphism
without claiming an end formula for implication.

The witness is `Grpd`-valued rather than a raw Lambdapi `TYPE`, consistently
with `Adjunction`, `Functor`, `Transf`, and the rest of the v3.2 object
classifier architecture.

Naturality in the externally quantified probe `M` remains deferred. It should
be added only when a concrete preservation or internalization check determines
the required endpoint action.

Successful focused probe:

```text
logs/probes/profunctor_phase4a_weighted_limit_cov_probe-20260618-220949.log
```

### Implementation Log 2026-06-18: Phase 4b

The narrow adjunction/profunctor bridge is active:

```text
Adjunction_prof_transpose:
  Hom_prof_along(left(adj) o M,F)
  ->
  Hom_prof_along(M,right(adj) o F)

Adjunction_prof_untranspose:
  Hom_prof_along(M,right(adj) o F)
  ->
  Hom_prof_along(left(adj) o M,F).
```

Both are equipment cells over identity endpoints and cancel in both
directions under `Prof_comp_transf`.

These are stable primitive heads, not transparent definitions. The current
kernel can express the pointwise unit/counit formulas but has no general
constructor that assembles those pointwise functors into a displayed natural
transformation between `Hom_prof_along` families. Future component projection
rules should reduce these heads to:

```text
f |-> right(f) o unit
g |-> counit o left(g),
```

using the existing ordinary adjunction triangle reductions. Until those
projections are required, this pair is the smallest bridge replacing the old
broad `Adj_cov_hom` / `Adj_con_hom` subsystem.

Successful focused probe:

```text
logs/probes/profunctor_phase4b_adjunction_bridge_probe-20260618-221240.log
```

### Implementation Log 2026-06-18: Phase 4c

The universal-map part of right-adjoint preservation is active as a
transparent semantic composite:

```text
right_adjoint_preserves_weighted_limit_cov_univ_transf.
```

For `adj : Adjunction(A,B)` and a weighted limit `L` of `F` by `W`, its source
and target are:

```text
Prof_imply_cov(
  Hom_prof_along(M,right(adj) o F),
  W)
->
Hom_prof_along(M,right(adj) o L).
```

Its definition is exactly:

```text
Prof_imply_cov_transf(
  Adjunction_prof_untranspose(adj,M,F),
  Prof_id_transf(W))
;
weighted_limit_cov_univ_transf(isl,left(adj) o M)
;
Adjunction_prof_transpose(adj,M,L).
```

Here semicolons indicate equipment-cell composition in execution order. The
small transparent helper `Adjunction_prof_imply_untranspose` routes the first
step through the named `Prof_imply_cov_transf` semantic constructor. Explicit
category and endpoint arguments are retained on the nested
`Prof_comp_transf` spine because the compact inferred form left unresolved
polymorphic endpoints.

The theorem intentionally returns the universal cell rather than prematurely
constructing:

```text
WeightedLimit_cov(right(adj) o F,W,right(adj) o L).
```

Giving projection rules for such a witness would overlap the generic
weighted-limit beta/eta rules. Proving the expanded branches join requires
the still-deferred naturality of implication and of the adjunction bridge.
This is the next semantic prerequisite, not a reason to make the preservation
map opaque.

Successful focused probe:

```text
logs/probes/profunctor_phase4c_right_adjoint_limit_probe-20260618-221641.log
```

Failed probes retained as elaboration evidence:

```text
logs/probes/profunctor_phase4c_right_adjoint_limit_probe-20260618-221444.log
logs/probes/profunctor_phase4c_right_adjoint_limit_probe-20260618-221504.log
logs/probes/profunctor_phase4c_right_adjoint_limit_probe-20260618-221525.log
logs/probes/profunctor_phase4c_right_adjoint_limit_probe-20260618-221604.log
```

Deferred after Phase 4c:

```text
naturality in the shaped probe M;
component projections of transpose/untranspose to unit/counit formulas;
the preserved weighted-limit cone;
the full right-adjoint-preserves-WeightedLimit_cov witness;
contravariant weighted-colimit packages, to be obtained through Phase 5
duality rather than copied from the obsolete draft.
```

### Implementation Log 2026-06-19: Phase 4d

The full right-adjoint preservation witness is now active:

```text
right_adjoint_preserves_weighted_limit_cov(isl,adj)
  : WeightedLimit_cov(
      right(adj) o F,
      W,
      right(adj) o L).
```

The Phase 4c universal map had to be promoted from a transparent definition to
the stable head:

```text
right_adjoint_preserves_weighted_limit_cov_univ_transf.
```

The exact three-step semantic composite still computes: a rewrite on the
outer `Prof_comp_transf` spine folds it to this stable head. The promotion was
required because the universal map is now a discriminator in the preserved
witness's beta/eta joins; the transparent composite was elaboration-unstable
in that position.

The witness's universal projection computes to the stable map. Its inverse
cone remains abstractly owned by `WeightedLimit_cov`, and two
constructor-local `Prof_comp_transf` rules join that projected universal map
with the generic weighted-limit beta/eta laws. No global implication
naturality or composition-associativity rule was needed.

This is intentionally narrower than the initially anticipated solution. An
explicit formula for the preserved cone is still useful future work, but it is
not a prerequisite for expressing or computing the preservation witness.

Successful focused probe:

```text
logs/probes/profunctor_phase4d_preserved_limit_witness_probe-20260619-012036.log
```

Failed probes retained as design evidence:

```text
logs/probes/profunctor_phase4d_preserved_limit_witness_probe-20260619-011543.log
logs/probes/profunctor_phase4d_preserved_limit_witness_probe-20260619-011625.log
logs/probes/profunctor_phase4d_preserved_limit_witness_probe-20260619-011648.log
logs/probes/profunctor_phase4d_preserved_limit_witness_probe-20260619-011704.log
logs/probes/profunctor_phase4d_preserved_limit_witness_probe-20260619-011851.log
logs/probes/profunctor_phase4d_preserved_limit_witness_probe-20260619-011910.log
logs/probes/profunctor_phase4d_preserved_limit_witness_probe-20260619-012001.log
```

Remaining Phase 4 refinements:

```text
an explicit semantic preserved-cone composite;
naturality in the shaped probe M;
component projections of transpose/untranspose to unit/counit formulas.
```

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
WeightedColimit_con
Op_weighted_colimit_con
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

### Implementation Log 2026-06-19: Phase 5a

The ordinary duality prerequisites are active.

`Op_transf` maps:

```text
eta : Transf(F,G)
```

to:

```text
Op_transf(eta) : Transf(Op_func(G),Op_func(F)).
```

It has checked involution, identity, reversed vertical composition, component
projection, and swapped off-diagonal action. `Op_adjunction` maps:

```text
Adjunction(A,B) -> Adjunction(Op_cat B,Op_cat A)
```

and computes:

```text
left(Op_adjunction(adj))  -> Op_func(right(adj))
right(Op_adjunction(adj)) -> Op_func(left(adj))
unit(Op_adjunction(adj))  -> Op_transf(counit(adj))
counit(Op_adjunction(adj))-> Op_transf(unit(adj)).
```

Successful focused probe:

```text
logs/probes/profunctor_phase5a_ordinary_duality_probe-20260619-012526.log
```

The initial failed diagnostic log is:

```text
logs/probes/profunctor_phase5a_ordinary_duality_probe-20260619-012459.log
```

### Implementation Log 2026-06-19: Phase 5b

`Product_swap_func(A,B)` is active with:

```text
sigma_Fst(Product_swap_func) -> Product_projR_func
sigma_Snd(Product_swap_func) -> Product_projL_func;
```

direct object and arrow computations, involution under composition, and
compatibility with `Op_func`.

The object-level profunctor dual is:

```text
Op_prof(R)
  := Pullback_catd(R,Product_swap_func(B,Op_cat A)).
```

The earlier tentative pointwise `Op_catd(R)` is rejected for the current
higher-category opposite. The kernel already computes:

```text
Hom_cat(Op_cat X,b,a) -> Hom_cat(X,a,b),
```

so representables dualize correctly by base swap alone. Pointwise fibre-op
would produce an additional `Op_cat(Hom_cat(X,a,b))`, dualizing the hom
category twice relative to the established `Op_cat` semantics.

The active checks cover product-swap objects and involution, `Op_func` of
swap, general `Op_prof` fibre projection, and representable fibres.
Profunctor-cell duality and whole-object involution remain separate later
slices.

Successful focused probe:

```text
logs/probes/profunctor_phase5b_op_prof_probe-20260619-013045.log
```

Failed probes recording the projection-ladder and endpoint corrections:

```text
logs/probes/profunctor_phase5b_op_prof_probe-20260619-012931.log
logs/probes/profunctor_phase5b_op_prof_probe-20260619-012950.log
logs/probes/profunctor_phase5b_op_prof_probe-20260619-013006.log
logs/probes/profunctor_phase5b_op_prof_probe-20260619-013020.log
```

### Implementation Log 2026-06-19: Phase 5c

The stable profunctor-cell dual is active:

```text
r : Prof_transf_cat(A,A',B,B',R',F,R,G)

Op_prof_transf(r)
  : Prof_transf_cat(
      Op_cat B, Op_cat B',
      Op_cat A, Op_cat A',
      Op_prof(R'), Op_func(G),
      Op_prof(R), Op_func(F)).
```

Here `r` is a cell `R' -> R` over `F : A' -> A` and `G : B' -> B`.
Object-level `Op_prof` swaps the bases but does not opposite the fibres.
Consequently `Op_prof_transf` also preserves the cell direction and preserves,
rather than reverses, equipment-cell composition order.

The active rules cover identity and composition. A double application folds
back to the original cell, supported by the narrow canonical cancellation:

```text
(H o Product_swap_func(B,A)) o Product_swap_func(A,B) -> H.
```

The involution rule is accepted by Lambdapi's subject-reduction checker. A
standalone involution equality in `emdash3_2_checks.lp` is deliberately
omitted because elaborating its deeply transparent dependent endpoint type
fails even though the kernel rule is accepted. The final focused probe checks
the type, identity, and composition computations.

`Op_prof_transf` remains primitive. Two attempted semantic bridges through
the hom action of `Pullback_catd_func(Product_swap_func)` were rejected: the
direct `Prof_reindex` comparison failed subject reduction, while the
reoriented fold caused a 30-second typecheck loop. No broad semantic rewrite
was installed.

Successful focused probe:

```text
logs/probes/profunctor_phase5c_op_prof_transf_probe-20260619-014651.log
```

Failed probes recording the involution prerequisite, endpoint correction, and
rejected semantic bridges:

```text
logs/probes/profunctor_phase5c_op_prof_transf_probe-20260619-014412.log
logs/probes/profunctor_phase5c_op_prof_transf_probe-20260619-014436.log
logs/probes/profunctor_phase5c_op_prof_transf_probe-20260619-014537.log
logs/probes/profunctor_phase5c_op_prof_transf_probe-20260619-014558.log
```

### Implementation Log 2026-06-19: Phase 5d

The weighted-colimit classifier is active as a transparent dual alias:

```text
WeightedColimit_con(F,W,L)
  := WeightedLimit_cov(
       Op_func(F),
       Op_prof(W),
       Op_func(L))
```

where the right-hand side lives in the opposite ambient and index categories.
For:

```text
F : J -> B
W : Prof(J,J')
L : J' -> B,
```

the dual weight has exactly the covariant-limit orientation:

```text
Op_prof(W) : Prof(Op_cat J',Op_cat J).
```

This design keeps `WeightedLimit_cov` as the sole universal-property owner.
The conversions:

```text
Op_weighted_limit_cov
Op_weighted_colimit_con
```

are transparent identity wrappers after `Op_func`, `Op_prof`, and
double-product-swap involution normalize. Their round trip is checked.

The full preservation theorem is:

```text
left_adjoint_preserves_weighted_colimit_con(isc,adj)
  := right_adjoint_preserves_weighted_limit_cov(
       isc,
       Op_adjunction(adj)).
```

The right adjoint of `Op_adjunction(adj)` computes to
`Op_func(left_adj_func(adj))`, and `Op_func` distributes over composition, so
the returned opposite-limit witness is definitionally the desired colimit
witness for `left(adj) o F` and `left(adj) o L`.

This is simpler and stronger than copying the obsolete theorem as a single
universal transformation: the public result is the full weighted-colimit
witness and inherits the existing limit beta/eta interface through the
transparent alias. Direct colimit-oriented names for the universal and cone
projections remain deferred until downstream use justifies them. A fully
expanded inherited-universal-map assertion encountered the known deep
dependent elaboration failure; no additional kernel rewrite was installed.

Successful focused probes:

```text
logs/probes/profunctor_phase5d_weighted_colimit_dual_probe-20260619-020959.log
logs/probes/profunctor_phase5d_weighted_colimit_dual_probe-20260619-021021.log
logs/probes/profunctor_phase5d_weighted_colimit_dual_probe-20260619-021157.log
```

The failed expanded-projection diagnostic is retained at:

```text
logs/probes/profunctor_phase5d_weighted_colimit_dual_probe-20260619-021132.log
```

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

### Implementation Log 2026-06-19: Phase 6a

The first primitive directed-inductive join slice is active. The key redesign
is that the old data:

```text
one_hom(I,a,b)
natural_eq(...)
```

is not ported as an externally Lambdapi-quantified family plus a separate
coherence proof. It is one internally natural equipment cell:

```text
cross :
  Terminal_prof(A,B)
  ->
  Hom_prof_along(first,second).
```

Here:

```text
Terminal_prof(A,B)
  := Const_catd(Product_cat(Op_cat A,B),Terminal_cat).
```

This cell lives in `Prof_transf_cat`, so its displayed-functor structure owns
naturality simultaneously in the contravariant `A` endpoint and covariant `B`
endpoint.

The reusable prerequisite:

```text
Prof_func_transf(F) :
  Unit_prof(A) -> Unit_prof(B)
```

is the representable equipment cell induced by the hom action of
`F : A -> B`. It has checked identity and composition reductions.
`Prof_func_hom(F)` is only a transparent shaped-element alias for the same
stable cell. `Prof_terminal_hom(F,G)` supplies the unique shaped element of a
terminal profunctor.

The primitive join surface is:

```text
Join_cat(A,B)
join_fst_func : A -> Join_cat(A,B)
join_snd_func : B -> Join_cat(A,B)
join_cross_transf :
  Terminal_prof(A,B)
  ->
  Hom_prof_along(join_fst_func,join_snd_func)
join_cross_hom(a,b)
join_elim_func(first,second,cross) : Join_cat(A,B) -> E.
```

`join_cross_hom(a,b)` is derived by composing `join_cross_transf` with
`Prof_terminal_hom(a,b)`, rather than postulated independently.

The recursor has beta rules on both inclusions. Its cross beta law composes the
canonical cross cell with `Prof_func_transf(join_elim_func(...))` and reduces
to the supplied `cross`. A second narrow rule gives the corresponding shaped
computation without installing global equipment-cell associativity.

The rewrite LHSs use canonical stable forms:

```text
Hom_prof_along(id,id)
Const_catd(...,Terminal_cat)
```

rather than the transparent `Unit_prof` and `Terminal_prof` aliases.

Successful final focused probe:

```text
logs/probes/profunctor_phase6a_join_probe-20260619-023809.log
```

Earlier successful milestones:

```text
logs/probes/profunctor_phase6a_join_probe-20260619-023444.log
logs/probes/profunctor_phase6a_join_probe-20260619-023527.log
logs/probes/profunctor_phase6a_join_probe-20260619-023711.log
logs/probes/profunctor_phase6a_join_probe-20260619-023727.log
```

The failed logs record endpoint elaboration, the correction from a constant to
a rewrite-capable `Prof_func_transf` head, and expanded cross-beta assertions
that fail during dependent elaboration even though the rewrite rules pass
subject reduction:

```text
logs/probes/profunctor_phase6a_join_probe-20260619-023349.log
logs/probes/profunctor_phase6a_join_probe-20260619-023411.log
logs/probes/profunctor_phase6a_join_probe-20260619-023428.log
logs/probes/profunctor_phase6a_join_probe-20260619-023544.log
logs/probes/profunctor_phase6a_join_probe-20260619-023620.log
logs/probes/profunctor_phase6a_join_probe-20260619-023630.log
logs/probes/profunctor_phase6a_join_probe-20260619-023746.log
```

This remains deliberately provisional. It does not yet provide dependent
elimination, object/hom case decompositions for `Join_cat`, a generic
directed-inductive framework, or a proof that `Join_cat` is a semantic collage
of `Terminal_prof`. Those are separate design checkpoints, not implicit claims
of this primitive recursor.

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
Phase 1 profunctor facade: landed, including general cells and shaped elements.
Phase 2 tensor/co-Yoneda: landed as a primitive computational calculus; semantic coends and broad coherence remain.
Phase 3 implication: both variance directions and general/shaped beta-eta landed; end semantics and broader naturality remain.
Phase 4 weighted limits: full covariant witness and right-adjoint preservation landed; naturality/component refinements remain.
Phase 5 op-duality: object/cell duality and full left-adjoint weighted-colimit preservation landed.
Phase 6 join: first primitive nondependent directed-inductive slice landed; dependent elimination and collage remain.
```

Completeness gaps to keep explicit:

```text
No general coend/coinserter quotient currently exists.
No bicategory-of-profunctors coherence layer currently exists.
No semantic pullback/reindex comparison for Op_prof_transf currently exists.
No direct colimit-oriented universal/cone projection names currently exist.
No Initial_cat currently exists for a full collage/join story.
No truncation/discreteness assumption is available or intended.
```

This is still globally coherent because the first implementation path does not
pretend to compute coends or quotients. It builds a Dosen-style symbolic
calculus whose reductions are beta/eta and named universal-map cancellations.
If a later semantic coend layer is added, `Prof_tensor` can become a semantic
owner or receive comparison maps without invalidating the public calculus.

## Implemented Order And Next Refinements

1. Phase 1a, landed: facade aliases, `Hom_prof_along`, its first full
   action, `Hom_prof`, and `Unit_prof`.
2. Phase 1b, landed: semantic `Product_map_func`, stable `Prof_reindex`, its
   full action, and representable endpoint accumulation.
3. Phase 1c, landed: transparent `Prof_transf_cat`, `Prof_hom_cat`, and
   `Prof_hom`; the checks did not demand endpoint-internalized or curry
   comparison packages.
4. Phase 2a-c, landed: primitive `Prof_tensor`, endpoint reindexing,
   generalized and shaped tensor introductions, equipment-cell composition,
   and symmetric identity-representable co-Yoneda beta rules.
5. Phase 3a-b, landed: both implication variances, mixed-variance cell actions,
   and general/shaped eval-lambda beta-eta.
6. Phase 4a-d, landed: covariant weighted-limit universal package, the narrow
   adjunction/profunctor transpose bridge, stable universal-map computation,
   and the full right-adjoint preservation witness.
7. Phase 5a-d, landed: ordinary transfor/adjunction duality,
   `Product_swap_func`, base-swap-only object-level `Op_prof`, and stable
   profunctor-cell duality, followed by the transparent weighted-colimit
   classifier and the full left-adjoint preservation witness.
8. Phase 6a, landed: primitive join, internally natural cross cell, shaped
   cross arrows, and nondependent recursor beta rules. Assess dependent
   elimination and/or semantic collage only as later independent slices.
9. Representability redesign refinement, landed: semantic
   `Hom_prof_func(J,B)` with generic strict arrow action and pointwise
   postcomposition components; fixed-weight `Prof_imply_cov_func(Q)` with
   object/full/capped arrow action, strict unary identity/composition, endpoint
   reindex compatibility, and a bridge from the identity-endpoint
   specialization of `Prof_imply_cov_transf`.
10. Representability cutover, landed 2026-06-22:
    `WeightedLimit_cov` now aliases `IsWeightedLimit_cov_comp`; its selected
    universal/cone maps are identity applications of push/pull;
    `right_adjoint_preserves_weighted_limit_cov` now aliases the transparent
    three-comparison theorem. The primitive witness, theorem-specific
    universal-map head, giant exact-syntax fold, and local equipment
    cancellation rules are retired. Weighted-colimit preservation remains the
    same transparent dual construction.
11. Mixed-variance implication internalization, landed 2026-06-22:
    `Prof_imply_cov_func2` directly internalizes the covariant profunctor and
    contravariant weight over
    `Prof_cat(A,X) x Op_cat(Prof_cat(B,X))`.
    `Prof_imply_cov_func2_transf` owns simultaneous fixed-endpoint action, and
    the functor's object/full/capped projections consume arbitrary opaque
    product objects and arrows through `sigma_Fst`/`sigma_Snd`. Identity,
    composition, unary-specialization, and general-cell folds are checked.
    The earlier curried workaround was removed after componentwise projection
    rules for arbitrary product identities closed the actual kernel gap.

All listed landed steps leave:

```text
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

passing. Further refinements should preserve the same discipline: add report
notes when a semantic definition must become a stable primitive head, compare
each extension again with pure categorical semantics, record prerequisite
kernel work, and revise earlier provisional choices rather than preserving
them for compatibility with this report or with `cartierSolution13.lp`.

The most natural independent next slices are:

```text
1. Generalize co-Yoneda beta rules using the landed Prof_func_hom.
2. Add weighted-limit probe naturality and/or explicit preserved-cone formulas.
3. Design dependent elimination for Join_cat without assuming collage
   semantics prematurely.
4. Investigate semantic end/coend comparison layers without replacing the
   stable public calculus until termination and computation are demonstrated.
```
