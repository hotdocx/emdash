# EMDASH v3.2 Pair-Telescope And Curry Rearchitecture Plan

Date: 2026-06-01

Status: partially implemented in `emdash3_2.lp`. Stages 1-5a below are now
installed and checked for the pair telescope, ordinary curry object
computation, the `tapp1_at_transf` one-projection refinement, and the semantic
transfor action of `curry_func_func`. Evaluation and the uncurry
rearchitecture remain deferred.

Update on 2026-06-02: the remaining curry-transfor work should first consolidate
the relationship between `hom_*` and `comp_cat_*` composition packages. The
consolidated plan is recorded in Stage 5a below.

## Executive Summary

The proposed direction is feasible, but it should be implemented in stages.
The new `Product_cat` architecture already gives the right normal form:

```text
Functor_cat X (Product_cat A B)
  -> Product_cat (Functor_cat X A) (Functor_cat X B)
```

That means the pairing telescope

```text
pair_tele : A -> (B -> Product_cat A B)
```

can be represented internally as a product of two functors:

```text
A -> (B -> A x B)
  = A -> ((B -> A) x (B -> B))
  = (A -> B -> A) x (A -> B -> B)
```

The intended definition is:

```text
Product_pair_tele_func(A,B)
  = Struct_sigma
      (const_section_func B A)
      (Const_func A (Functor_cat B B) (id_func B))
```

Mathematically:

```text
pair_tele[x]    = (const_x, id_B)
pair_tele[x][y] = (x,y)
pair_tele[p][y] = (p,id_y)
```

The implementation installed the generic layers that were missing at the start
of this plan:

1. an intermediate off-diagonal hom-action functor `tapp1_func`, sitting
   between the internal `tapp1_int_fapp0_transf` package and the capped
   `tapp1_fapp0` projection;
2. the arrow action of `const_section_func`, i.e. constant natural
   transformations induced by arrows;
3. the transfor action of `comp_cat_cov_func`, i.e. postcomposition of a
   natural transformation by an ordinary functor;
4. the transfor action of `comp_cat_cov_func_func`, i.e. functoriality of
   postcomposition in the postcomposing functor.

The later composition review refined the ownership model:

- generic `hom_*` packages should own the meaning of precomposition and
  postcomposition in higher homs;
- Cat-specific `comp_cat_*_transf` stable heads should own component
  computation with `tapp0_fapp0`, `tapp1_func`, and capped `tapp1_fapp0`;
- `comp_func_tele` is only the identity-functor special case of a more general
  hom-postcomposition telescope and should be removed rather than kept as a
  separate primitive alias.

With those layers installed, `curry_func_func` is defined through:

```text
curry_func_func
  = comp_cat_con_func(Product_pair_tele_func(A,B))
      o comp_cat_cov_func_func
```

Equivalently, its object projection computes to:

```text
curry(F) = comp_cat_cov_func(F) o Product_pair_tele_func(A,B)
curry(F)[x][y] = F[(x,y)]
```

The old curry hom-action helper heads are not part of the new core
architecture. They were removed when unused rather than retained as parallel
rewrite facades. Reintroduce a helper only as a projection from
`curry_func_func`, after a focused probe shows a real consumer need.

The current semantic evaluation layer was useful as a probe, but the next
implementation pass should replace its argument order. Keep the symbol names
`Eval_func` and `Eval_fapp1_func`, but orient evaluation as
`Eval_func(A,B)[(F,x)] = F[x]`. This lets uncurry be built from the outer
arrow-action of internal product formation, with no swap/symmetry functor.

## Current State

`emdash3_2.lp` currently has:

- product-valued functors represented by the product of functor categories;
- stable product projection functors `Product_projL_func` and
  `Product_projR_func`;
- projection-oriented product computation for `fapp0`, `fapp1_func`,
  `fapp1_fapp0`, `tapp0_fapp0`, and `tapp1_fapp0`;
- `const_section_func K A : A -> Pi_cat K (Const_catd K A)`, whose object
  action computes to `Const_func K A a`;
- `comp_cat_cov_func G : (X -> Y) -> (X -> Z)`, whose object action computes
  to `comp_cat_fapp0 G F`;
- `tapp1_at_transf`, the fixed-source one-projection layer, and `tapp1_func`,
  the off-diagonal hom-action functor
  `Hom_A(X,Y) -> Hom_B(F[X],G[Y])`;
- `comp_cat_cov_func_func`, packaging postcomposition as a functor in the
  postcomposing functor, including `comp_cat_cov_func_func_fapp1_func`,
  `comp_cat_cov_func_func_transf`,
  `comp_cat_cov_func_func_tapp1_func`, and
  `comp_cat_cov_func_func_tapp1_fapp0` for its transfor action;
- `comp_cat_con_func`, packaging precomposition by a fixed functor, with
  `comp_cat_con_fapp1_func` and `comp_cat_con_transf`;
- `curry_func_func` as the primary semantic curry package, with `curry_func`
  and `curry_fapp0_func` only definitional object projections;
- a temporary left-ordered `Eval_func`, `Eval_fapp1_func`, and `Eval_at_func`,
  which should be replaced by the right-ordered convention described in Stage 6;
- a temporary `uncurry_eval_arg_func` / `uncurry_eval_func` companion, which
  should be replaced by product-functoriality via `Product_cat_func`;
- an uncurry scaffold with stable object and hom-action heads.

The curry-specific transfor behavior is now owned by generic mechanisms:

- pairing into a product should be owned by `Product_pair_tele_func`;
- off-diagonal naturality should be owned by a reusable `tapp1_func` layer,
  not only by capped `tapp1_fapp0` rules;
- constant-natural-transformation computation should be owned by
  `const_section_func`;
- postcomposition of transfors should be owned by `comp_cat_cov_func`;
- precomposition of transfors is owned by `comp_cat_con_func` and
  `comp_cat_con_transf`, not by curry-only helpers.

## Feasibility Review

### Pair Telescope

The pair telescope is a good replacement for an ad hoc
`Product_insertR_func(A,B,x) : B -> Product_cat A B`.

The more internal version is:

```text
Product_pair_tele_func(A,B)
  : Functor A (Functor_cat B (Product_cat A B))
```

with definition:

```text
Struct_sigma
  (const_section_func B A)
  (Const_func A (Functor_cat B B) (id_func B))
```

The object-level computation should check directly:

```text
fapp0 (fapp0 Product_pair_tele_func x) y
  == Struct_sigma x y
```

The arrow-level computation should be checked projectionwise first, because
the product architecture intentionally avoids broad eta rules of the form
`h -> Struct_sigma (sigma_Fst h) (sigma_Snd h)`.

Target checks:

```text
sigma_Fst (tapp0_fapp0 ... y (pair_tele[p])) == p
sigma_Snd (tapp0_fapp0 ... y (pair_tele[p])) == id_B(y)
```

and similarly for `tapp1_fapp0` over an arrow `q : y -> y'` in `B`:

```text
sigma_Fst (tapp1_fapp0 ... (pair_tele[p]) q) == p
sigma_Snd (tapp1_fapp0 ... (pair_tele[p]) q) == q
```

After `tapp1_func` is installed, prefer the stronger functor-level checks:

```text
sigma_Fst (tapp1_func ... (pair_tele[p]) y y')
  == Const_func (Hom_cat B y y') (Hom_cat A x x') p

sigma_Snd (tapp1_func ... (pair_tele[p]) y y')
  == fapp1_func (id_func B) y y'
```

These projectionwise checks are the right local normal form unless we later
choose to add a carefully controlled product eta principle.

### Intermediate `tapp1_func`

The current `tapp1_fapp0` is intentionally capped:

```text
tapp1_fapp0 eta p : Hom_B(F[X],G[Y])
```

For architecture work, this loses the hom-functor structure. Add an
intermediate stable projection:

```text
tapp1_func [A B F G X Y] eta
  : Functor
      (Hom_cat A X Y)
      (Hom_cat B (fapp0 F X) (fapp0 G Y))
```

with the capping rule:

```text
fapp0 (tapp1_func eta X Y) p
  -> tapp1_fapp0 eta p
```

Add product projection rules analogous to the existing `tapp1_fapp0`
projection rules:

```text
sigma_Fst (tapp1_func eta i j)
  -> tapp1_func (sigma_Fst eta) i j

sigma_Snd (tapp1_func eta i j)
  -> tapp1_func (sigma_Snd eta) i j
```

where the target category of the original transfor is a `Product_cat`.

#### Bridge From `tapp1_int_fapp0_transf`

The bridge from the internal package to `tapp1_func` should use an intermediate
one-projection stable head:

```text
tapp1_at_transf eta X
  : Transf(hom_A(X,-), hom_B(F[X],G[-]))
```

The projection ladder is:

```text
tapp0_fapp0 X (tapp1_int_fapp0_transf eta)
  -> tapp1_at_transf eta X

tapp0_fapp0 Y (tapp1_at_transf eta X)
  -> tapp1_func eta X Y
```

The old direct composite remains a checked consequence:

```text
tapp0_fapp0 Y
  (tapp0_fapp0 X (tapp1_int_fapp0_transf eta))
  -> tapp1_func eta X Y
```

This keeps the meaningful semantic layer visible. `tapp1_at_transf eta X`
is the fixed-source natural family in the target object, and may become the
right place to express ordinary lax-naturality data, analogously to the current
component-level `functord_laxity_*` architecture for displayed functors.

This still refines the SOP: a nested projection assertion is acceptable when
the discriminants are stable projection heads and the reducible endpoint
families are not used as rewrite-rule discriminators. In Lambdapi, keep the
source/target endpoint arguments implicit or as `_` on the rule LHSs. The
stable heads should be `tapp0_fapp0`, `tapp1_int_fapp0_transf`, and
`tapp1_at_transf`.

The risk is typechecking the bridge, not the mathematical rule. The endpoint
families reduce through:

```text
fapp0 (hom_int A A id_A) X
  -> hom_ A A id_A X

fapp0 (hom_ A A id_A X) Y
  -> Hom_cat A X Y
```

and:

```text
fapp0 (comp_cat_fapp0 (hom_int B A G) (Op_func F)) X
  -> fapp0 (hom_int B A G) (F[X])
  -> hom_ B A G (F[X])

fapp0 (hom_ B A G (F[X])) Y
  -> Hom_cat B (F[X]) (G[Y])
```

These are the "reducible endpoint families": endpoint types whose canonical
shape is recovered only after reductions through `comp_cat_fapp0`, `hom_int`,
`hom_`, `Op_func`, and `Transf_cat K Cat_cat -> Functord_cat`. The checked
implementation avoids using those reducible families as discriminators by
installing the two smaller rules above and a focused assertion for the old
double projection.

### Constant Transfors

The current `const_section_func K A` only has object action:

```text
const_section_func(K,A)[a] = Const_func K A a
```

To compute its arrow action, add a stable hom-action package. Recommended
names:

```text
Const_transf_func(K,A,x,y)
  : Functor
      (Hom_cat A x y)
      (Transf_cat (Const_func K A x) (Const_func K A y))

Const_transf(K,A,p)
  : Transf(Const_func K A x, Const_func K A y)
```

Expected rules:

```text
fapp1_func (const_section_func K A) x y
  -> Const_transf_func K A x y

fapp0 (Const_transf_func K A x y) p
  -> Const_transf K A p

fapp1_fapp0 (const_section_func K A) x y p
  -> Const_transf K A p

tapp0_fapp0 ... k (Const_transf K A p)
  -> p

tapp1_func ... k k' (Const_transf K A p)
  -> Const_func (Hom_cat K k k') (Hom_cat A x y) p
```

The capped `tapp1_fapp0` computation should then follow by applying the
generic capping rule for `tapp1_func`. For a constant natural transformation,
the off-diagonal component over any base arrow in `K` is still the same arrow
`p : x -> y` in `A`.

### Postcomposition By A Functor

`comp_cat_cov_func` was originally understood as a specialization of
categorical composition in `Cat_cat`:

```text
comp_func_tele Cat_cat X Y Z
  : (Y -> Z) -> ((X -> Y) -> (X -> Z))

comp_cat_cov_func(G)
  = (comp_func_tele Cat_cat X Y Z)[G]
```

Temporary probing showed that this semantic source computes on objects:

```text
comp_cat_cov_func(G)[F][x] = G[F[x]]
```

However, the transfor action is not currently exposed:

```text
comp_cat_cov_func(G)[eta][x] = G[eta[x]]
```

Add a stable postcomposition package rather than relying on large nested
left-hand sides under `tapp0_fapp0`.

Update on 2026-06-02: Stage 5a refines this explanation. The better generic
owner is not the old `comp_func_tele` alias, but the generalized
`hom_postcomp_tele_func` / `hom_postcomp_func` projection of `hom_`. The
existing `comp_cat_cov_func` and `comp_cat_cov_transf` should remain the
Cat-specific stable heads for ordinary functor and transfor computation.

Recommended names:

```text
comp_cat_cov_fapp1_func(X,Y,Z,G,F,H)
  : Functor
      (Transf_cat F H)
      (Transf_cat (comp_cat_fapp0 G F) (comp_cat_fapp0 G H))

comp_cat_cov_transf(X,Y,Z,G,eta)
  : Transf(comp_cat_fapp0 G F, comp_cat_fapp0 G H)
```

Expected rules:

```text
fapp1_func (comp_cat_cov_func G) F H
  -> comp_cat_cov_fapp1_func G F H

fapp0 (comp_cat_cov_fapp1_func G F H) eta
  -> comp_cat_cov_transf G eta

fapp1_fapp0 (comp_cat_cov_func G) F H eta
  -> comp_cat_cov_transf G eta

tapp0_fapp0 ... i (comp_cat_cov_transf G eta)
  -> fapp1_fapp0 G (tapp0_fapp0 ... i eta)

tapp1_func ... i j (comp_cat_cov_transf G eta)
  -> comp_cat_fapp0
       (fapp1_func G (F[i]) (H[j]))
       (tapp1_func eta i j)
```

The final two rules should keep inferred source/target endpoints implicit or
as variables on the LHS. The discriminators are the stable heads
`comp_cat_cov_transf`, `tapp0_fapp0`, and `tapp1_func`; avoid writing
reducible endpoint expressions as LHS discriminators.

### Rules Versus `tapp1_*`

Use direct `tapp0_fapp0` and `tapp1_func` rules for the first implementation.
Keep `tapp1_fapp0` as the capped projection obtained by applying
`fapp0 (tapp1_func eta X Y) p`.

`tapp1_int_func_transf` and `tapp1_int_fapp0_transf` remain useful as a future
internal action package. The immediate bridge from `tapp1_int_fapp0_transf` to
ordinary components now goes through `tapp1_at_transf`, then `tapp1_func`. The
important point is that new semantic rules should target the highest reusable
layer they need: `tapp1_at_transf` for fixed-source naturality, `tapp1_func`
for hom-functor action, and `tapp1_fapp0` only for capped components.

Later, after the direct rules are checked, we can decide whether
`tapp1_int_func_transf` should compute to the same stable postcomposition
transfor package.

## Implementation Status On 2026-06-01

Implemented and checked in `emdash3_2.lp`:

- `tapp1_func`, the functor-level off-diagonal component
  `Hom_A(X,Y) -> Hom_B(F[X],G[Y])`;
- product projection rules for `tapp1_func`;
- identity-transfor rules for `tapp1_func` and `tapp1_fapp0`;
- `tapp1_at_transf`, the fixed-source one-projection layer
  `Hom_A(X,-) => Hom_B(F[X],G[-])`, plus the two projection rules
  `tapp1_int_fapp0_transf -> tapp1_at_transf -> tapp1_func`;
- `Const_transf_func` and `Const_transf`, with `tapp0_fapp0`,
  `tapp1_func`, and capped `tapp1_fapp0` computation;
- the hom-action of `const_section_func`;
- `Product_pair_tele_func`, with object and arrow computation checked
  projectionwise;
- `comp_cat_cov_fapp1_func` and `comp_cat_cov_transf`, with `tapp0_fapp0`,
  `tapp1_func`, and capped `tapp1_fapp0` computation.
- generic full hom-action rules for ordinary identity and composition:
  `fapp1_func(id_func) -> id_func` and
  `fapp1_func(comp_cat_fapp0 F G) -> comp_cat_fapp0(F_1,G_1)`;
- generic object-level functor packages for composition:
  `comp_cat_cov_func_func`, with
  `comp_cat_cov_func_func[X,Y,Z][G] = comp_cat_cov_func(G)`, and
  `comp_cat_con_func(F)`, with `comp_cat_con_func(F)[G] = G o F`;
- semantic curry core:
  `curry_func_func` is defined as
  `comp_cat_con_func(Product_pair_tele_func(A,B)) o comp_cat_cov_func_func`,
  while `curry_func` and `curry_fapp0_func` are definitional projections from
  `curry_func_func`;
- late semantic sanity checks showing
  `curry(F)[x][y] = F[(x,y)]`, after the `Product_pair_tele_func` computation
  rules are in scope.

Implementation lessons:

- The direct nested bridge from `tapp1_int_fapp0_transf` to `tapp1_func`
  typechecked, but the implementation now uses `tapp1_at_transf` as the
  stable one-projection layer. This preserves the whole fixed-source transfor
  for future lax-naturality infrastructure while keeping the old nested
  projection as a checked consequence.
- `Product_pair_tele_func` rules should be installed after
  `const_section_func`, because its stable component projections are
  `const_section_func B A` and `Const_func A (Functor_cat B B) id_B`.
- The `fapp1_func` and `fapp1_fapp0` rules for `Product_pair_tele_func` need
  the normalized product target
  `Product_cat (Functor_cat B A) (Functor_cat B B)` on the LHS, not the
  reducible target `Functor_cat B (Product_cat A B)`.
- Full product eta assertions such as
  `pair_tele[x][y] == Struct_sigma x y` are more brittle than projectionwise
  assertions. The checked assertions use `sigma_Fst`/`sigma_Snd`.
- Direct capped rules for `Const_transf` and `comp_cat_cov_transf` are kept so
  the existing `tapp1_fapp0` API still computes and joins with the new
  `tapp1_func` layer.
- The object rule for `Product_pair_tele_func` should use the normalized
  target `Product_cat (Functor_cat B A) (Functor_cat B B)`, matching the
  already-normalized `fapp1_func` and `fapp1_fapp0` rules. The reducible target
  `Functor_cat B (Product_cat A B)` was too weak once semantic curry exposed
  the normalized target during type preservation.
- Fully semantic ordinary curry object computation also needs full hom-action
  computation for ordinary identity and composition. Adding
  `fapp1_func(id_func)` and `fapp1_func(comp_cat_fapp0 F G)` made the
  definitional route through `comp_cat_cov_func(F) o Product_pair_tele_func`
  expose the expected object beta law.
- Rewriting old curry helper heads such as `curry_outer_transf` directly to
  semantic compositions is not the recommended core architecture. A probe
  showed that those helper rules add type-preservation cost and distract from
  the priority symbol. They were removed when unused; future transfor action
  should come from generic precomposition/postcomposition packages.

## Implementation Order / Remaining Work

The validated implementation order was:

```text
tapp1_func
  -> Const_transf / const_section_func hom-action
	  -> Product_pair_tele_func
	  -> comp_cat_cov_func postcomposition
	  -> curry rearchitecture
	  -> Eval_func / evaluation-based uncurry companion
```

The temporary evaluation-based uncurry companion proved the needed component
computations, but its argument order is not the desired global architecture.
The remaining order is:

```text
hom/composition consolidation
  -> generic hom-postcomposition and hom-precomposition hom-actions
  -> Cat-specific precomposition transfor action
  -> curry_func_func transfor-action refinement
  -> Product_cat_func / product-functorial action
  -> replace Eval_func with right-ordered evaluation
  -> replace uncurry_func_func through Eval_func and product action
  -> delete or redefine obsolete uncurry helper heads
```

The completed lower layers are kept in this section as an implementation
record: starting with curry would have forced the new architecture to lean on
the old capped `tapp1_fapp0` and curry-specific heads. Starting with
`tapp1_func` gave the constant-transfor, pair-telescope, postcomposition, and
future evaluation rules the typed hom-functor layer they all need.

### Stage 1: Intermediate `tapp1_func`

Add the typed off-diagonal hom-action functor:

```text
tapp1_func eta X Y
  : Functor (Hom_cat A X Y) (Hom_cat B (F[X]) (G[Y]))
```

with:

```text
fapp0 (tapp1_func eta X Y) p -> tapp1_fapp0 eta p
```

Add product projection rules for `sigma_Fst`/`sigma_Snd` over `tapp1_func`.

Then add the first-projection stable head:

```text
tapp1_at_transf [A B F G] eta X
  : Transf_cat
      (hom_ A A (id_func A) X)
      (hom_ B A G (fapp0 F X))
```

Mathematically:

```text
tapp1_at_transf(eta,X)
  : Hom_A(X,-) => Hom_B(F[X],G[-])
```

with bridge rules:

```text
tapp0_fapp0 X (tapp1_int_fapp0_transf eta)
  -> tapp1_at_transf eta X

tapp0_fapp0 Y (tapp1_at_transf eta X)
  -> tapp1_func eta X Y
```

Also keep a regression assertion for the old composite projection:

```text
tapp0_fapp0 Y
  (tapp0_fapp0 X (tapp1_int_fapp0_transf eta))
  == tapp1_func eta X Y
```

### Stage 2: Constant Transfor Infrastructure

Add `Const_transf_func` and `Const_transf` near `Const_func` or near
`const_section_func`, depending on dependency order. The likely dependency
order is:

- `Const_func` exists early;
- `Transf_cat`, `tapp0_fapp0`, `tapp1_fapp0`, and `tapp1_func` exist later;
- `const_section_func` exists much later in the Pi section.

Therefore the practical location may be close to `const_section_func`, after
the transfor projection heads are available.

Add focused assertions:

```text
const_section_func(K,A)[a] == Const_func K A a
fapp1_fapp0(const_section_func K A, p) == Const_transf K A p
Const_transf(p)[k] == p
tapp1_func(Const_transf(p),k,k') == Const_func(...,p)
Const_transf(p)[q] == p              -- capped consequence
```

Use a temporary copy first, then port into `emdash3_2.lp`.

### Stage 3: Product Pair Telescope

Add:

```text
Product_pair_tele_func [A B]
  : Functor A (Functor_cat B (Product_cat A B))
```

with projection behavior equivalent to:

```text
Struct_sigma
  (const_section_func B A)
  (Const_func A (Functor_cat B B) (id_func B))
```

Add focused assertions:

```text
pair_tele[x][y] == Struct_sigma x y

sigma_Fst(pair_tele[p][y]) == p
sigma_Snd(pair_tele[p][y]) == id y

sigma_Fst(pair_tele[p][q]) == p
sigma_Snd(pair_tele[p][q]) == q
```

Phrase the last three in actual Lambdapi with `tapp0_fapp0` and
`tapp1_func` projections; add capped `tapp1_fapp0` assertions only as
consequences.

### Stage 4: Postcomposition Transfor Infrastructure

Add the hom-action package for `comp_cat_cov_func`:

- `comp_cat_cov_fapp1_func`;
- `comp_cat_cov_transf`;
- `fapp1_func`/`fapp0`/`fapp1_fapp0` bridge rules;
- `tapp0_fapp0` and `tapp1_func` component rules.

Add focused assertions:

```text
comp_cat_cov_func(G)[eta][i] == G[eta[i]]
tapp1_func(comp_cat_cov_func(G)[eta],i,j)
  == G[i,j] o tapp1_func(eta,i,j)
comp_cat_cov_func(G)[eta][p] == G[eta[p]]  -- capped consequence
```

The generic precomposition stage is the main prerequisite for replacing
curry-specific outer transfor computation.

### Stage 5: Route Curry Through Pair Telescope

The old curry object heads are now projections from the semantic route, not
independent primitive structure:

```text
curry_func_func
  = comp_cat_con_func(Product_pair_tele_func(A,B)) o comp_cat_cov_func_func

curry_func(F)
  = curry_func_func[F]

curry_fapp0_func(F,x)
  = curry_func(F)[x]
```

After `Product_pair_tele_func` computation rules are in scope, the checked
object beta laws are:

```text
curry(F)[x][y] = F[(x,y)]
uncurry(curry(F))[(x,y)] = F[(x,y)]
curry(uncurry(G))[x][y] = G[x][y]
```

Implementation detail:

```text
comp_cat_cov_func_func[X,Y,Z][G] = comp_cat_cov_func(G)
comp_cat_con_func(F)[G] = G o F
```

These are stable object-level heads for now. They could later be redefined
through `hom_int` / `hom_` if the generic internal-hom package exposes the
needed functorial action without extra rewrite-rule pressure.

The action of `curry_func_func` on a transfor `eta : F => G` is deliberately
not reintroduced as a curry-only stable facade. A fully semantic version should
use the precomposition analogue of `comp_cat_cov_transf`, because
`curry(eta)[x]` is the precomposition of `eta` by
`Product_pair_tele_func[x]`.

### Stage 5a: Hom/Composition Consolidation

This addendum records the 2026-06-02 review of `comp_*`, `hom_*`, and their
`Cat_cat` specializations. It is the next implementation target before resuming
`curry_func_func` transfor action.

#### Problem

The current file has several composition-related heads:

```text
comp_fapp0
comp_cat_fapp0
comp_cat_cov_func
comp_cat_cov_func_func
comp_cat_con_func
comp_func_tele
hom_precomp_func
hom_
hom_int
```

The hierarchy should not contain many semantically interdependent names that
are unrelated syntactically. In particular:

- `comp_func_tele` is not used as infrastructure; static search shows it is
  declared and then used only by its own sanity assertion and reports;
- `comp_cat_cov_func_func` and `comp_cat_con_func` were added as object-level
  composition packages, but their relationship to `hom_`, `hom_int`, and
  `hom_precomp_func` should be made explicit before adding more curry action
  rules;
- `comp_cat_cov_transf` is already a useful stable head for Cat-specific
  postcomposition of transfors, but its semantic source should be documented as
  the Cat-specialized hom-postcomposition action.

#### Ownership Principle

Use two layers:

```text
generic hom_* heads
  own semantic higher-hom action

Cat-specific comp_cat_* stable heads
  own ordinary transfor component computation
```

The reason for the split is important. Generic higher-hom actions live in an
arbitrary category `A : Cat`; their outputs are just arrows in hom-categories.
For arbitrary `A`, there is no general `tapp0_fapp0` or `tapp1_func` projection
API. These projections only become available after specializing to:

```text
A = Cat_cat
Hom_cat Cat_cat X Z = Functor_cat X Z
Hom_cat (Functor_cat X Z) P Q = Transf_cat P Q
```

Therefore rules such as:

```text
tapp0_fapp0 (comp_cat_cov_transf G eta) i
  -> G[eta[i]]

tapp1_func (comp_cat_cov_transf G eta) i j
  -> G_1(F[i],H[j]) o tapp1_func eta i j
```

are not generic `hom_*` rules. They are Cat-specific projection rules for the
Cat-specialized higher-hom action. The same applies to the planned
precomposition rules:

```text
tapp0_fapp0 (comp_cat_con_transf F eta) x
  -> eta[F[x]]

tapp1_func (comp_cat_con_transf F eta) x y
  -> tapp1_func eta (F[x]) (F[y]) o F_1(x,y)
```

This justifies keeping `comp_cat_cov_transf` and `comp_cat_con_transf` as stable
Cat-specific heads even if their meaning is owned by generic `hom_*` packages.
Do not make these transfor heads transparent aliases that unfold away before
`tapp0_fapp0` or `tapp1_func` can discriminate on them.

#### Generic Postcomposition From `hom_`

For:

```text
R : I -> A
W : Obj(A)
```

the covariant hom functor is:

```text
hom_ R W : I -> Cat
hom_ R W [i] = Hom_A(W, R[i])
```

Expose its hom-action through stable projection heads:

```text
hom_postcomp_tele_func(R,W,i,j)
  : Functor
      (Hom_cat I i j)
      (Functor_cat
        (Hom_cat A W (R[i]))
        (Hom_cat A W (R[j])))

hom_postcomp_func(R,W,r)
  : Functor
      (Hom_cat A W (R[i]))
      (Hom_cat A W (R[j]))
```

Recommended rules:

```text
fapp1_func (hom_ R W) i j
  -> hom_postcomp_tele_func(R,W,i,j)

fapp0 (hom_postcomp_tele_func(R,W,i,j)) r
  -> hom_postcomp_func(R,W,r)

fapp0 (hom_postcomp_func(R,W,r)) g
  -> R[r] o g
```

Implementation note from the 2026-06-02 probe: do not add the broad direct fold

```text
fapp1_fapp0 (hom_ R W) r
  -> hom_postcomp_func(R,W,r)
```

as an early global rule. It typechecks locally, but it changes old normal forms
used by downstream path-induction assertions. Keep the existing compatibility
rule:

```text
fapp0 (fapp1_fapp0 (hom_ R W) r) g
  -> R[r] o g
```

and use `hom_postcomp_func` explicitly, or through
`hom_postcomp_tele_func`, when the stable postcomposition functor itself is the
desired normal form.

Then expose the hom-action of `hom_postcomp_func` itself:

```text
hom_postcomp_fapp1_func(R,W,r,g,h)
  : Functor
      (Hom_cat (Hom_cat A W (R[i])) g h)
      (Hom_cat
        (Hom_cat A W (R[j]))
        (R[r] o g)
        (R[r] o h))

hom_postcomp_fapp1_fapp0(R,W,r,alpha)
  : Hom_cat
      (Hom_cat A W (R[j]))
      (R[r] o g)
      (R[r] o h)
```

Recommended rules:

```text
fapp1_func (hom_postcomp_func(R,W,r)) g h
  -> hom_postcomp_fapp1_func(R,W,r,g,h)

fapp0 (hom_postcomp_fapp1_func(R,W,r,g,h)) alpha
  -> hom_postcomp_fapp1_fapp0(R,W,r,alpha)

fapp1_fapp0 (hom_postcomp_func(R,W,r)) alpha
  -> hom_postcomp_fapp1_fapp0(R,W,r,alpha)
```

The old `comp_func_tele(A,x,y,z)` is just the special case:

```text
hom_postcomp_tele_func(id_func A, x, y, z)
```

Delete `comp_func_tele` and replace its local sanity assertion with an assertion
for `hom_postcomp_tele_func` or `hom_postcomp_func`.

#### Cat-Specialized Postcomposition

Specialize generic postcomposition by:

```text
A = Cat_cat
I = Cat_cat
R = id_func Cat_cat
W = X
i = Y
j = Z
r = G : Y -> Z
```

Then:

```text
hom_postcomp_tele_func(id_Cat, X, Y, Z)
  : (Y -> Z) -> ((X -> Y) -> (X -> Z))

hom_postcomp_func(id_Cat, X, G)
  : (X -> Y) -> (X -> Z)
```

The Cat-specific names are:

```text
comp_cat_cov_func_func(X,Y,Z)
  ~= hom_postcomp_tele_func(id_Cat, X, Y, Z)

comp_cat_cov_func(G)
  ~= hom_postcomp_func(id_Cat, X, G)
```

Their transfor action is the Cat specialization of
`hom_postcomp_fapp1_fapp0`:

```text
comp_cat_cov_fapp1_func(G,F,H)
  ~= hom_postcomp_fapp1_func(id_Cat, X, G, F, H)

comp_cat_cov_transf(G,eta)
  ~= hom_postcomp_fapp1_fapp0(id_Cat, X, G, eta)
```

Keep `comp_cat_cov_transf` stable because it owns ordinary transfor component
projection:

```text
tapp0_fapp0 (comp_cat_cov_transf G eta) i
  -> G[eta[i]]

tapp1_func (comp_cat_cov_transf G eta) i j
  -> G_1(F[i],H[j]) o tapp1_func eta i j

tapp1_fapp0 (comp_cat_cov_transf G eta) p
  -> G[eta[p]]
```

If probes are clean, add bridge/fold rules from the Cat-specialized generic
heads to the `comp_cat_cov_*` heads. Prefer folding generic specialized forms
to the existing Cat-specific stable heads rather than unfolding the stable heads
away.

The next functorial layer is postcomposition as a functor in the postcomposing
functor:

```text
comp_cat_cov_func_func(X,Y,Z)
  : (Y -> Z) -> ((X -> Y) -> (X -> Z))

comp_cat_cov_func_func_transf(eta : G => H)
  : comp_cat_cov_func(G) => comp_cat_cov_func(H)
```

Its object component is precomposition of `eta` by the input functor:

```text
tapp0_fapp0 (comp_cat_cov_func_func_transf eta) F
  -> comp_cat_con_transf(F, eta)
```

Its off-diagonal component over `alpha : F => K` is horizontal composition:

```text
tapp1_fapp0 (comp_cat_cov_func_func_transf eta) alpha
  -> comp_cat_cov_func_func_tapp1_fapp0(eta, alpha)

comp_cat_cov_func_func_tapp1_fapp0(eta, alpha)
  = (comp_cat_cov_transf H alpha) o (comp_cat_con_transf F eta)
```

Important SOP lesson from the probe: the projection-rule LHSs for
`comp_cat_cov_func_func_transf` must leave source and target category slots
implicit:

```text
tapp0_fapp0 _ _ _ _ F (comp_cat_cov_func_func_transf eta)
```

Do not write the LHS as:

```text
tapp0_fapp0 (Functor_cat X Y) (Functor_cat X Z) ...
```

That shape works for variable `Y`, but it fails in the curry/product use case,
where `Y = Product_cat A B` and the new product architecture rewrites
`Functor_cat B (Product_cat A B)` to a product of functor categories. This is
exactly the kind of reducible endpoint family that should not appear as an LHS
discriminator.

#### Generic Precomposition From `hom_int`

The existing `hom_int` package internalizes represented-object variance:

```text
hom_int(R) : A^op -> (I -> Cat)
hom_int(R)[X][i] = Hom_A(X, R[i])
```

The current file already exposes the object component of this represented-object
action:

```text
tapp0_fapp0
  b
  (fapp1_fapp0 (hom_int R) f)
  -> hom_precomp_func(f)
```

where:

```text
f : X -> Y
hom_precomp_func(f)
  : Hom_A(Y,Z) -> Hom_A(X,Z)

hom_precomp_func(f)[g] = g o f
```

This existing rule is the correct semantic anchor: `hom_precomp_func` is not an
unrelated helper, but the represented-object action of `hom_int`.

Add the missing hom-action package for `hom_precomp_func`:

```text
hom_precomp_fapp1_func(f,g,h)
  : Functor
      (Hom_cat (Hom_cat A Y Z) g h)
      (Hom_cat
        (Hom_cat A X Z)
        (g o f)
        (h o f))

hom_precomp_fapp1_fapp0(f,alpha)
  : Hom_cat
      (Hom_cat A X Z)
      (g o f)
      (h o f)
```

Recommended rules:

```text
fapp1_func (hom_precomp_func f) g h
  -> hom_precomp_fapp1_func(f,g,h)

fapp0 (hom_precomp_fapp1_func(f,g,h)) alpha
  -> hom_precomp_fapp1_fapp0(f,alpha)

fapp1_fapp0 (hom_precomp_func f) alpha
  -> hom_precomp_fapp1_fapp0(f,alpha)
```

Do not immediately add broad rules connecting the off-diagonal
`tapp1_func` projection of `hom_int` to `hom_precomp_fapp1_func`. The
off-diagonal action of `hom_int` over a base arrow in `I` combines
precomposition in the represented object with postcomposition by `R` in the
target object. That mixed rule is real but broader than the immediate curry
milestone.

#### Cat-Specialized Precomposition

Specialize generic precomposition by:

```text
A = Cat_cat
f = F : X -> Y
g = G : Y -> Z
h = H : Y -> Z
alpha = eta : G => H
```

Then:

```text
hom_precomp_func(Cat_cat,F)
  : (Y -> Z) -> (X -> Z)

hom_precomp_fapp1_fapp0(Cat_cat,F,eta)
  : (G o F) => (H o F)
```

The Cat-specific names are:

```text
comp_cat_con_func(F)
  ~= hom_precomp_func(Cat_cat,F)

comp_cat_con_fapp1_func(F,G,H)
  ~= hom_precomp_fapp1_func(Cat_cat,F,G,H)

comp_cat_con_transf(F,eta)
  ~= hom_precomp_fapp1_fapp0(Cat_cat,F,eta)
```

The component rules are Cat-specific projections:

```text
tapp0_fapp0 (comp_cat_con_transf F eta) x
  -> eta[F[x]]

tapp1_func (comp_cat_con_transf F eta) x y
  -> tapp1_func eta (F[x]) (F[y]) o F_1(x,y)

tapp1_fapp0 (comp_cat_con_transf F eta) p
  -> eta[F[p]]
```

As with postcomposition, keep `comp_cat_con_transf` stable. It is the head that
ordinary-transfor projection rules should discriminate on. The generic
`hom_precomp_*` layer owns the meaning; the Cat-specific stable head owns the
component computation.

Implementation choice for `comp_cat_con_func`:

- preferred probe: define it as the `Cat_cat` specialization of
  `hom_precomp_func`;
- fallback: keep it as a stable object-level facade and add a fold/bridge from
  the Cat-specialized `hom_precomp_func` to `comp_cat_con_func`.

The preferred route is more semantic, but the fallback is acceptable if
Lambdapi's subject-reduction or critical-pair checking becomes brittle.

#### Recommended Implementation Order

Probe in a temporary copy first, then port into `emdash3_2.lp`:

```text
1. Delete `comp_func_tele` and its assertion.
2. Add `hom_postcomp_tele_func` and `hom_postcomp_func`.
3. Add `hom_postcomp_fapp1_func` and `hom_postcomp_fapp1_fapp0`.
4. Relate Cat-specialized postcomposition to existing `comp_cat_cov_*` heads.
5. Add `hom_precomp_fapp1_func` and `hom_precomp_fapp1_fapp0`.
6. Define or bridge `comp_cat_con_func` as the Cat specialization of
   `hom_precomp_func`.
7. Add `comp_cat_con_fapp1_func` and `comp_cat_con_transf` as stable
   Cat-specific heads.
8. Add `tapp0_fapp0`, `tapp1_func`, and capped `tapp1_fapp0` rules for
   `comp_cat_con_transf`.
9. Re-run the existing curry object-beta assertions.
10. Resume `curry_func_func` transfor action using `comp_cat_con_transf`
    rather than curry-only helper heads.
```

Add focused assertions at each layer:

```text
hom_postcomp_func(R,W,r)[g] == R[r] o g
hom_precomp_func(f)[g] == g o f

comp_cat_cov_transf(G,eta)[i] == G[eta[i]]
comp_cat_con_transf(F,eta)[x] == eta[F[x]]

tapp1_func(comp_cat_cov_transf(G,eta),i,j)
  == G_1(F[i],H[j]) o tapp1_func(eta,i,j)

tapp1_func(comp_cat_con_transf(F,eta),x,y)
  == tapp1_func(eta,F[x],F[y]) o F_1(x,y)
```

The last two should use explicit canonical `Hom_cat` endpoint forms in
assertions, but the corresponding rewrite-rule LHSs should keep inferred
source/target endpoints implicit or as `_`.

Implementation status on 2026-06-02:

- steps 1-10 above are implemented and checked in `emdash3_2.lp`;
- `comp_func_tele` was deleted and its assertion now uses
  `hom_postcomp_func(id_func A, x, q)`;
- `hom_postcomp_tele_func`, `hom_postcomp_func`,
  `hom_postcomp_fapp1_func`, and `hom_postcomp_fapp1_fapp0` are installed;
- Cat-specialized postcomposition folds to the existing `comp_cat_cov_func`,
  `comp_cat_cov_func_func`, `comp_cat_cov_fapp1_func`, and
  `comp_cat_cov_transf` heads;
- `comp_cat_cov_func_func_fapp1_func` and
  `comp_cat_cov_func_func_transf` give the functor-in-postcomposer hom-action;
- `comp_cat_cov_func_func_tapp1_func` and
  `comp_cat_cov_func_func_tapp1_fapp0` give its off-diagonal action, with
  `comp_cat_cov_func_func_tapp1_fapp0(eta,alpha)` defined as
  `(comp_cat_cov_transf H alpha) o (comp_cat_con_transf F eta)`;
- `hom_precomp_fapp1_func` and `hom_precomp_fapp1_fapp0` are installed;
- Cat-specialized precomposition folds through `comp_cat_con_func`,
  `comp_cat_con_fapp1_func`, and `comp_cat_con_transf`;
- `comp_cat_con_transf` has checked `tapp0_fapp0`, `tapp1_func`, and capped
  `tapp1_fapp0` component rules;
- `curry_func_func` now has checked semantic transfor-action assertions through
  composition, including:

```text
fapp1_fapp0(curry_func_func, eta)
  = comp_cat_con_transf(
      Product_pair_tele_func,
      comp_cat_cov_func_func_transf(eta))

tapp0_fapp0(fapp1_fapp0(curry_func_func, eta), x)
  = comp_cat_con_transf(Product_pair_tele_func[x], eta)

tapp0_fapp0(tapp0_fapp0(fapp1_fapp0(curry_func_func, eta), x), y)
  = eta[(x,y)]
```

The next implementation target is Stage 6/Eval/uncurry design, not additional
curry-only helper heads.

### Stage 6: Right-Ordered Evaluation And Uncurry

Recommended adjustment: keep the public names `Eval_func`,
`Eval_fapp1_func`, and related evaluation helpers, but replace the current
temporary left-ordered convention by right-ordered evaluation.

The target convention is:

```text
Eval_func(A,B) : Product_cat (Functor_cat A B) A -> B
Eval_func(A,B)[(F,x)] = F[x]
```

The hom-action should expose a stable intermediate functor whose product
component order mirrors the source product:

```text
Eval_fapp1_func [A B] [F G : Functor A B] [x y : Obj A]
  : Functor
      (Product_cat (Transf_cat F G) (Hom_cat A x y))
      (Hom_cat B (F[x]) (G[y]))

Eval_fapp1_func[(eta,p)] = tapp1_fapp0 eta p

fapp1_func Eval_func (F,x) (G,y)
  -> Eval_fapp1_func F G x y
```

This keeps evaluation from being only a capped `tapp1_fapp0` wrapper:
`fapp1_func Eval_func` has a typed functorial component, while the capped
rule is merely the object action of that component. The right-ordered
`Eval_at_func` should also be reversed accordingly:

```text
Eval_at_func(x) : Functor_cat (Functor_cat A B)
                              (Product_cat (Functor_cat A B) A)
Eval_at_func(x)[F] = (F,x)

fapp0_func x
  ~= Eval_func(A,B) o Eval_at_func(x)
```

This replaces the current temporary left-ordered `Eval_at_func`, where the
fixed object was the first product component.

The reason for the reorientation is uncurry. Introduce an internalized product
functor layer:

```text
Product_cat_func : Functor Cat_cat (Functor_cat Cat_cat Cat_cat)
Product_cat_func[A][B] = Product_cat A B
```

With this orientation, the outer arrow-action at
`G : Functor_cat A (Functor_cat B C)` gives the needed product map directly:

```text
G * 1_B : Product_cat A B -> Product_cat (Functor_cat B C) B
(G * 1_B)[(x,y)] = (G[x], y)
(G * 1_B)[(p,q)] = (G[p], q)
```

Then uncurry has the semantic form:

```text
uncurry(G)
  = Eval_func(B,C) o (G * 1_B)

uncurry(G)[(x,y)] = G[x][y]
uncurry(G)[(p,q)] = tapp1_fapp0 (G[p]) q
```

No product symmetry/swap functor is required. This is the main advantage over
the current temporary `uncurry_eval_arg_func`, which used the left-ordered
argument map:

```text
(x,y) |-> (y, G[x]) : Product_cat A B -> Product_cat B (Functor_cat B C)
```

That companion proved the object and capped arrow computations, but it does not
package the functoriality of `G` in the correct product-functorial layer and
should not become the final architecture.

Implementation notes for the next pass:

- add `Product_cat_func` or a stable projection of it before replacing
  `Eval_func`;
- add a reusable product-map head for the outer action, e.g.
  `Product_mapL_func` / `Product_outer_map_func` / final name TBD, satisfying
  projectionwise object and arrow rules for `G * 1_B`;
- replace the existing `Eval_func`, `Eval_fapp1_func`, and `Eval_at_func`
  declarations/rules in place, keeping the symbol names but changing the
  product order;
- rebuild `uncurry_func_func` through `Eval_func(B,C)` and the product action;
- delete or redefine the old `uncurry_func`, `uncurry_fapp1_func`,
  `uncurry_func_fapp1_func`, `uncurry_transf`, `uncurry_eval_arg_func`, and
  `uncurry_eval_func` only after the new `uncurry_func_func` assertions pass.

## Rewrite Hygiene

Use the v3.2 SOP:

- probe nontrivial rewrite rules in a temporary copy before editing the active
  file;
- use bounded checks, e.g. `timeout 60s lambdapi check -w emdash3_2.lp` or
  `EMDASH_TYPECHECK_TIMEOUT=60s make check`;
- avoid compound expressions in LHS implicit arguments;
- keep source/target categories implicit unless they are the actual
  discriminator;
- allow a focused nested projection rule when all discriminators are stable
  projection heads and reducible endpoint families are kept implicit;
- add assertions immediately after each new computation layer;
- prefer projectionwise product assertions over broad product eta rewrites;
- add stable heads only when they represent reusable semantic objects or avoid
  fragile nested projection LHSs.

## Expected Outcome

The feasible near-term endpoint is:

```text
pair_tele[x][y] = (x,y)
pair_tele[p][y] = (p,id_y)          -- projectionwise
curry(F)[x][y]  = F[(x,y)]
curry(F)[p][y]  = F[(p,id_y)]       -- via tapp1_func, then capped
uncurry(G)[(x,y)] = G[x][y]
uncurry(G)[(p,q)] = tapp1_fapp0 (G[p]) q
```

The intended uncurry endpoint is `Eval_func(B,C) o (G * 1_B)`, where
`Eval_func` uses the right-ordered convention and `G * 1_B` is supplied by the
outer action of product formation. Existing stable uncurry helper heads should
be kept only until this replacement has passed focused object, `fapp1_func`,
and capped `fapp1_fapp0` assertions.
