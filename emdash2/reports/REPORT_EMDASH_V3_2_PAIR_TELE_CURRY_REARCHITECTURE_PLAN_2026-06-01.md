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
copy. The arrow computation needs two missing generic computations:

1. the arrow action of `const_section_func`, i.e. constant natural
   transformations induced by arrows;
2. the transfor action of `comp_cat_cov_func`, i.e. postcomposition of a
   natural transformation by an ordinary functor.

Once those are installed, `curry(F)` can be routed through:

```text
curry(F) = comp_cat_cov_func(F) o Product_pair_tele_func(A,B)
```

`uncurry_func` should remain stable/primitive for now. A fully semantic
uncurry would naturally use an evaluation functor, but introducing that now
would expand the scope and is not needed for the current milestone.

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
- a curry/uncurry scaffold with several dedicated stable heads:
  `curry_func`, `curry_fapp0_func`, `curry_inner_fapp1_func`,
  `curry_outer_fapp1_func`, `curry_outer_transf`, `curry_func_func`,
  `curry_transf`, and their uncurry analogues.

The current curry-specific heads are doing work that should eventually be
owned by more generic mechanisms:

- pairing into a product should be owned by `Product_pair_tele_func`;
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

These projectionwise checks are the right local normal form unless we later
choose to add a carefully controlled product eta principle.

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

tapp1_fapp0 ... k k' (Const_transf K A p) q
  -> p
```

The `tapp1_fapp0` rule is feasible and useful. For a constant natural
transformation, the off-diagonal component over any base arrow in `K` is still
the same arrow `p : x -> y` in `A`.

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

tapp1_fapp0 ... i j (comp_cat_cov_transf G eta) p
  -> fapp1_fapp0 G (tapp1_fapp0 ... i j eta p)
```

The final two rules should keep inferred source/target endpoints implicit or
as variables on the LHS. The discriminators are the stable heads
`comp_cat_cov_transf`, `tapp0_fapp0`, and `tapp1_fapp0`; avoid writing
reducible endpoint expressions as LHS discriminators.

### Rules Versus `tapp1_*`

Use direct `tapp0_fapp0` and `tapp1_fapp0` rules for the first
implementation.

`tapp1_int_func_transf` and `tapp1_int_fapp0_transf` remain useful as a future
internal action package, but routing this change through them immediately
would add another layer of transfor-category endpoints before the simpler
ordinary capped rules are known to work. The current file already treats
`tapp1_fapp0` as the reserved off-diagonal ordinary naturality projection, so
it is the right first target for constant transfors and postcomposition.

Later, after the direct rules are checked, we can decide whether
`tapp1_int_func_transf` should compute to the same stable postcomposition
transfor package.

## Proposed Implementation Stages

### Stage 1: Constant Transfor Infrastructure

Add `Const_transf_func` and `Const_transf` near `Const_func` or near
`const_section_func`, depending on dependency order. The likely dependency
order is:

- `Const_func` exists early;
- `Transf_cat`, `tapp0_fapp0`, and `tapp1_fapp0` exist later;
- `const_section_func` exists much later in the Pi section.

Therefore the practical location may be close to `const_section_func`, after
the transfor projection heads are available.

Add focused assertions:

```text
const_section_func(K,A)[a] == Const_func K A a
fapp1_fapp0(const_section_func K A, p) == Const_transf K A p
Const_transf(p)[k] == p
Const_transf(p)[q] == p
```

Use a temporary copy first, then port into `emdash3_2.lp`.

### Stage 2: Product Pair Telescope

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
`tapp1_fapp0` projections.

### Stage 3: Postcomposition Transfor Infrastructure

Add the hom-action package for `comp_cat_cov_func`:

- `comp_cat_cov_fapp1_func`;
- `comp_cat_cov_transf`;
- `fapp1_func`/`fapp0`/`fapp1_fapp0` bridge rules;
- `tapp0_fapp0` and `tapp1_fapp0` component rules.

Add focused assertions:

```text
comp_cat_cov_func(G)[eta][i] == G[eta[i]]
comp_cat_cov_func(G)[eta][p] == G[eta[p]]
```

This stage is the main prerequisite for replacing curry-specific outer
transfor computation.

### Stage 4: Route Curry Through Pair Telescope

Do not delete all existing curry stable heads in the first edit. First add a
semantic alias or redefine only the object-action helper:

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

After Stage 3 passes, evaluate whether `curry_outer_transf` can be redefined
or replaced by the generic postcomposition transfor:

```text
curry(F)[p]
  = comp_cat_cov_func(F)[Product_pair_tele_func[p]]
```

Only then remove or demote `curry_outer_transf`,
`curry_outer_fapp1_func`, and possibly `curry_inner_fapp1_func`.

### Stage 5: Keep Uncurry Stable

Leave `uncurry_func` and its current hom-action rules unchanged during this
iteration.

A future semantic design would likely introduce:

```text
Eval_func(B,C) : Product_cat (Functor_cat B C) B -> C
uncurry(G) = Eval_func o (G o Product_projL_func, Product_projR_func)
```

That is a coherent later step, but it is not needed to make the pair-telescope
half computational.

## Rewrite Hygiene

Use the v3.2 SOP:

- probe nontrivial rewrite rules in a temporary copy before editing the active
  file;
- use bounded checks, e.g. `timeout 60s lambdapi check -w emdash3_2.lp` or
  `EMDASH_TYPECHECK_TIMEOUT=60s make check`;
- avoid compound expressions in LHS implicit arguments;
- keep source/target categories implicit unless they are the actual
  discriminator;
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
curry(F)[p][y]  = F[(p,id_y)]       -- after postcomposition rules
```

with `uncurry_func` still stable.

This should reduce the number of curry-specific primitive heads over time, but
the implementation should only demote those heads after the generic constant
transfor and postcomposition rules pass focused assertions.
