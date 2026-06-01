# EMDASH v3.2 Pair-Telescope And Curry Rearchitecture Plan

Date: 2026-06-01

Status: proposed implementation plan. This is not yet implemented in
`emdash3_2.lp`.

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

The object computation has already been probed successfully in a temporary
copy. The arrow computation needs three missing generic layers:

1. an intermediate off-diagonal hom-action functor `tapp1_func`, sitting
   between the internal `tapp1_int_fapp0_transf` package and the capped
   `tapp1_fapp0` projection;
2. the arrow action of `const_section_func`, i.e. constant natural
   transformations induced by arrows;
3. the transfor action of `comp_cat_cov_func`, i.e. postcomposition of a
   natural transformation by an ordinary functor.

Once those are installed, `curry(F)` can be routed through:

```text
curry(F) = comp_cat_cov_func(F) o Product_pair_tele_func(A,B)
```

`uncurry_func` should remain stable/primitive for now. A fully semantic
uncurry should probably use an evaluation functor, but that should be deferred
until `tapp1_func` exists; otherwise evaluation would duplicate the current
capped projection infrastructure instead of clarifying it.

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
- `tapp1_int_fapp0_transf`, the internalized off-diagonal naturality package,
  and `tapp1_fapp0`, the capped ordinary off-diagonal component, but no stable
  intermediate functor
  `Hom_A(X,Y) -> Hom_B(F[X],G[Y])`;
- a curry/uncurry scaffold with several dedicated stable heads:
  `curry_func`, `curry_fapp0_func`, `curry_inner_fapp1_func`,
  `curry_outer_fapp1_func`, `curry_outer_transf`, `curry_func_func`,
  `curry_transf`, and their uncurry analogues.

The current curry-specific heads are doing work that should eventually be
owned by more generic mechanisms:

- pairing into a product should be owned by `Product_pair_tele_func`;
- off-diagonal naturality should be owned by a reusable `tapp1_func` layer,
  not only by capped `tapp1_fapp0` rules;
- constant-natural-transformation computation should be owned by
  `const_section_func`;
- postcomposition of transfors should be owned by `comp_cat_cov_func`.

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

The bridge from the internal package to `tapp1_func` can probably be a single
nested projection rule:

```text
tapp0_fapp0 Y
  (tapp0_fapp0 X (tapp1_int_fapp0_transf eta))
  -> tapp1_func eta X Y
```

This refines the SOP: a nested projection is acceptable when the discriminants
are stable projection heads and the reducible endpoint families are not used
as discriminators. In Lambdapi, keep the source/target endpoint arguments
implicit or as `_` on the LHS. The stable heads should be the two
`tapp0_fapp0` projections and `tapp1_int_fapp0_transf`.

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
`hom_`, `Op_func`, and `Transf_cat K Cat_cat -> Functord_cat`. The rule should
be probed in a temporary copy. If it checks cleanly and does not noticeably
hurt decision-tree behavior, keep it. If not, split it into a first-projection
stable head and then the second projection to `tapp1_func`.

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

`comp_cat_cov_func` should be understood as a specialization of categorical
composition in `Cat_cat`:

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
`tapp1_func` should be tried as the single nested projection rule above. If it
is fragile, introduce the one-projection stable head as a fallback. The
important point is that new semantic rules should target `tapp1_func`, not
only `tapp1_fapp0`.

Later, after the direct rules are checked, we can decide whether
`tapp1_int_func_transf` should compute to the same stable postcomposition
transfor package.

## Proposed Implementation Stages

The implementation order for the next turn should start below curry:

```text
tapp1_func
  -> Const_transf / const_section_func hom-action
  -> Product_pair_tele_func
  -> comp_cat_cov_func postcomposition
  -> curry rearchitecture
  -> deferred Eval_func / uncurry rearchitecture
```

Starting with curry would force the new architecture to lean on the old capped
`tapp1_fapp0` and curry-specific heads. Starting with `tapp1_func` gives the
constant-transfor, pair-telescope, postcomposition, and future evaluation
rules the typed hom-functor layer they all need.

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

Then probe the single nested bridge:

```text
tapp0_fapp0 Y
  (tapp0_fapp0 X (tapp1_int_fapp0_transf eta))
  -> tapp1_func eta X Y
```

If that rule fails or introduces bad decision-tree behavior, add a first
projection stable head and route the bridge in two smaller rules.

The fallback first-projection head should be named and typed along these
lines:

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

with semantic definition:

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

This stage is the main prerequisite for replacing curry-specific outer
transfor computation.

### Stage 5: Route Curry Through Pair Telescope

The plan is to replace the old curry architecture, not preserve its current
symbols as primitive structure. During migration, keep only what is needed to
keep the file checkable. A conservative first edit is to add a semantic alias
or redefine only the object-action helper:

```text
curry_fapp0_func(F,x)
  = comp_cat_fapp0 F (fapp0 Product_pair_tele_func x)
```

Then keep:

```text
fapp0 (curry_func F) x -> curry_fapp0_func F x
```

This preserves existing downstream references while making the object-level
computation semantic:

```text
curry(F)[x][y] == F[(x,y)]
```

After Stage 4 passes, evaluate whether `curry_outer_transf` can be redefined
or replaced by the generic postcomposition transfor:

```text
curry(F)[p]
  = comp_cat_cov_func(F)[Product_pair_tele_func[p]]
```

After the new core is in place, old heads such as `curry_outer_transf`,
`curry_outer_fapp1_func`, and `curry_inner_fapp1_func` should be removed,
deferred, or reintroduced only as aliases over the new architecture.

### Stage 6: Keep Uncurry Stable

Leave `uncurry_func` and its current hom-action rules unchanged during this
iteration.

A future semantic design would likely introduce:

```text
Eval_func(A,B) : Product_cat A (Functor_cat A B) -> B
Eval_func(A,B)[(x,F)] = F[x]
Eval_func(A,B)[(p,eta)] = fapp0 (tapp1_func eta x y) p
```

The hom-action should not be specified only by the capped last line. To expose
`fapp1_func Eval_func`, introduce the intermediate hom-action functor:

```text
Eval_fapp1_func [A B] [x y : Obj A] [F G : Functor A B]
  : Functor
      (Product_cat (Hom_cat A x y) (Transf_cat F G))
      (Hom_cat B (F[x]) (G[y]))

Eval_fapp1_func[(p,eta)]
  = fapp0 (tapp1_func eta x y) p
```

Then:

```text
fapp1_func Eval_func (x,F) (y,G)
  -> Eval_fapp1_func x y F G
```

This is why `Eval_func` is deferred until after `tapp1_func`: without this
intermediate hom-action functor, evaluation would merely repackage
`tapp1_fapp0` and duplicate the existing capped projection API.

With this order, the existing `fapp0_func x` can later be understood as a
stable projection of evaluation at the fixed point `x`, using a constant
functor into the first product component and the identity functor on
`Functor_cat A B`.

Schematically:

```text
fapp0_func x
  ~= Eval_func(A,B)
       o (Const_func (Functor_cat A B) A x,
          id_func (Functor_cat A B))
```

A semantic uncurry could then be:

```text
uncurry(G)
  = Eval_func(B,C)
      o (Product_projR_func A B,
         comp_cat_fapp0 G (Product_projL_func A B))
```

This evaluation layer should remain deferred. It probably does not require an
internal `Product_cat_func` as a prerequisite for fixed `A,B`, but it does
require `tapp1_func` if it is to expose `fapp1_func Eval_func` rather than
only capped `fapp1_fapp0` behavior.

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
```

with `uncurry_func` still stable.

This should reduce the number of curry-specific primitive heads over time, but
the implementation should only demote those heads after the generic constant
transfor and postcomposition rules pass focused assertions.
