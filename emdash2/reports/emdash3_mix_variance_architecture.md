# emdash3 Mixed-Variance Architecture for Directed `homd`

## Summary

This report consolidates the revised architecture for a fully internal
dependent-hom construction over directed families:

```text
E : Fam Z    i.e.    E : Z -> Cat
```

The main conclusion is that the old `Catd`-style formulation

```text
homd_curry E : Op_catd E -> ...
```

does not directly generalize to arbitrary directed `E : Z -> Cat`.
For a plain covariant family, there is no functorial operation reversing
the base variance of `E`; only the fibres can be opposited objectwise.
The correct directed construction must instead use a mixed-variance
family functor:

```text
Functor_fam [K]
  (A : Fam (Op_cat K))
  (B : Fam K)
  : Fam K
```

and its internalized functor-object form:

```text
Functor_mix_fam_func [K]
  : Functor
      (Op_cat (Fam_cat (Op_cat K)))
      (Functor_cat (Fam_cat K) (Fam_cat K))
```

This makes it possible to build the fully internal directed `homd`
target with the desired endpoint order:

```text
x : Z,
u : E[x]^op,
y : Z^op,
v : E[y],
f : Hom_Z(x,y)
  |- Hom_{E[y]}(E(f)(u), v)
```

The construction is semantically meaningful for directed families because
mixed variance accounts for precomposition on the functor-domain side and
postcomposition on the functor-codomain side.

## Background and Problem

The older `emdash2.lp` `homd_curry` pipeline typechecked because it lived
in the `Catd` layer. That layer has an operation:

```text
Op_catd : Catd Z -> Catd (Op_cat Z)
```

with fibre computation:

```text
Fibre_cat (Op_catd E) z
  -> Op_cat (Fibre_cat E z)
```

For `E = Fibration_cov_catd M`, this only gives the fibre-level normal
form:

```text
Fibre_cat (Op_catd (Fibration_cov_catd M)) z
  -> Op_cat (M z)
```

It does not turn a covariant functor `M : Z -> Cat` into a genuine
contravariant family over `Z`. The action along reversed base arrows is
not supplied by `M`; a covariant `M` provides pushforward along
`f : x -> y`, not pullback along `f`.

This means that for the new directed `Fam` layer, the following direct
`Catd` intuition is not sound:

```text
E : Z -> Cat
homd_curry E : E^op -> ...
```

There is no canonical directed family `E^op` over `Op_cat Z` obtained
from a general `E : Z -> Cat`. Objectwise one can form `E[z]^op`, but the
base action has the wrong variance.

Nevertheless, the endpoint Sigma-hom formula is valid:

```text
sigma_hom_fam E x u y v
  : Functor (Op_cat (Hom_cat Z x y)) Cat_cat

f |-> Hom_cat (E[y]) (E(f)(u)) v
```

because `x`, `u`, `y`, and `v` are fixed parameters. The task is to
recover a fully internal construction whose projections produce this
endpoint order, without pretending that `E` itself has a global opposite
family.

## Directed Family Layer

The intended directed family layer is ordinary Cat-valued functors:

```text
Fam_cat (K : Cat) : Cat
  := Functor_cat K Cat_cat

Fam (K : Cat) : Grpd
  := Obj (Fam_cat K)
```

The fibre/app notation is only a readability head:

```text
Fam_app_cat [K] (E : tau (Fam K)) (k : tau (Obj K)) : Cat
  -> fapp0 E k
```

The existing name `Fibre_cat` may be reused as a compatibility spelling,
but conceptually in the directed `Fam` layer it means only application of
a Cat-valued functor.

Basic family constructors:

```text
Pullback_fam [A B] (E : tau (Fam B)) (F : tau (Functor A B))
  : tau (Fam A)
  := comp_cat_fapp0 E F

Const_fam K A : tau (Fam K)
  := comp_cat_fapp0 (Obj_func A) (Terminal_func K)

Terminal_fam K : tau (Fam K)
  := Const_fam K Terminal_cat
```

Sections are natural transformations from the terminal family:

```text
Pi_cat [K] (E : tau (Fam K)) : Cat
  := Transf_cat (Terminal_fam K) E
```

The internal functor object for sections is:

```text
Pi_func (K : Cat)
  : tau (Functor (Fam_cat K) Cat_cat)

fapp0 (Pi_func K) E
  -> Pi_cat E
```

This is the terminal-domain special case of a dependent function space.

## Mixed-Variance Family Functor

For a directed base `K`, the pointwise category

```text
k |-> Functor_cat (A[k]) (B[k])
```

is covariantly functorial in `k` only when the source family has the
opposite base variance:

```text
A : Fam (Op_cat K)
B : Fam K
```

The required constructor is:

```text
Functor_fam [K]
  (A : tau (Fam (Op_cat K)))
  (B : tau (Fam K))
  : tau (Fam K)
```

with fibre rule:

```text
Fam_app_cat (Functor_fam A B) k
  -> Functor_cat (Fam_app_cat A k) (Fam_app_cat B k)
```

Semantically, along a base arrow `f : k -> k'`:

- `B(f)` gives postcomposition:

  ```text
  B[k] -> B[k']
  ```

- `A` is a family over `Op_cat K`, so the same `f` is seen as an arrow
  `k' -> k` in `Op_cat K`, giving:

  ```text
  A[k'] -> A[k]
  ```

  which is exactly the direction needed for precomposition.

Thus `Functor_fam A B` acts on a functor `A[k] -> B[k]` by
precomposition with `A[k'] -> A[k]` and postcomposition with
`B[k] -> B[k']`.

To use this in internal composition pipelines, the object-level
constructor is not enough. We need the curried functor-object form:

```text
Functor_mix_fam_func [K]
  : tau
      (Functor
        (Op_cat (Fam_cat (Op_cat K)))
        (Functor_cat (Fam_cat K) (Fam_cat K)))
```

with beta rules:

```text
fapp0 (Functor_mix_fam_func K) A
  -> Functor_mix_fam_fapp0_func A

fapp0 (Functor_mix_fam_fapp0_func A) B
  -> Functor_fam A B
```

Equivalently:

```text
fapp0 (fapp0 (Functor_mix_fam_func K) A) B
  -> Functor_fam A B
```

This is the directed-family analogue of the current
`Functor_catd_func`, but it has the correct mixed variance rather than
assuming both families live over the same directed base.

## Internal Edge Family

The edge family must be defined internally, not only by object-level
specification.

The goal is:

```text
Edge_fam Z : tau (Functor (Op_cat Z) (Fam_cat Z))

Fam_app_cat (fapp0 (Edge_fam Z) x) y
  -> Op_cat (Hom_cat Z x y)
```

The current `emdash3.lp` already contains the necessary ingredients:

```text
hom_int [A B] (F : tau (Functor B A))
  : tau (Functor (Op_cat A) (Functor_cat B Cat_cat))

op : tau (Functor Cat_cat Cat_cat)

op_val_func [Z]
  : tau
      (Functor
        (Functor_cat Z Cat_cat)
        (Functor_cat Z Cat_cat))
  := comp_cat_cov_func Z Cat_cat Cat_cat op
```

Since:

```text
hom_int Z Z (id_func Z)
  : Functor (Op_cat Z) (Functor_cat Z Cat_cat)
```

and:

```text
Fam_cat Z = Functor_cat Z Cat_cat
```

the internal definition is:

```text
Edge_fam [Z : Cat]
  : tau (Functor (Op_cat Z) (Fam_cat Z))
≔ comp_cat_fapp0
     op_val_func[Z]
     (hom_int Z Z (id_func Z))
```

Fully explicit in the current style:

```text
Edge_fam [Z : Cat]
  : tau (Functor (Op_cat Z) (Fam_cat Z))
≔ @comp_cat_fapp0
     (Op_cat Z)
     (Functor_cat Z Cat_cat)
     (Functor_cat Z Cat_cat)
     (@op_val_func Z)
     (@hom_int Z Z (@id_func Z))
```

The computation is:

```text
fapp0 (fapp0 (Edge_fam Z) x) y
  -> Op_cat (Hom_cat Z x y)
```

This does not require exposing an uncurried functor
`Z^op x Z -> Cat`. The category `Functor_cat Z Cat_cat` already
internalizes the `y : Z` context, and `hom_int` already provides the
curried `x : Z^op` dependence.

For later use in a `Z`-indexed construction, apply ordinary opposite to
the outer functor:

```text
Op_func (Edge_fam Z)
  : tau (Functor Z (Op_cat (Fam_cat Z)))
```

This is the precise replacement for informal phrases like
`"op composed with hom_int"`: the inner `op` is `op_val_func Z`, and the
outer variance flip is `Op_func`.

## Presheaf-Family Classifier

The construction also needs a functorial way to turn a family of
categories into the family of Cat-valued functors out of it.

For each base `K`, define:

```text
Presheaf_fam_func [K]
  : tau
      (Functor
        (Op_cat (Fam_cat (Op_cat K)))
        (Fam_cat K))
```

by evaluating the mixed-variance functor constructor at the constant
Cat-family:

```text
Presheaf_fam_func K
  := comp_cat_fapp0
       (fapp0_func (Const_fam K Cat_cat))
       (Functor_mix_fam_func K)
```

More explicitly, if:

```text
Functor_mix_fam_func K
  : Functor
      (Op_cat (Fam_cat (Op_cat K)))
      (Functor_cat (Fam_cat K) (Fam_cat K))
```

and:

```text
fapp0_func (Const_fam K Cat_cat)
  : Functor
      (Functor_cat (Fam_cat K) (Fam_cat K))
      (Fam_cat K)
```

then:

```text
Presheaf_fam_func K
  : Functor
      (Op_cat (Fam_cat (Op_cat K)))
      (Fam_cat K)
```

with object computation:

```text
fapp0 (Presheaf_fam_func K) H
  -> Functor_fam H (Const_fam K Cat_cat)
```

and therefore:

```text
Fam_app_cat (fapp0 (Presheaf_fam_func K) H) k
  -> Functor_cat (Fam_app_cat H k) Cat_cat
```

This is deliberately functorial in `H`. It must not be implemented as a
mere object-level abbreviation.

For the dependent hom construction we use `K = Op_cat Z`:

```text
Presheaf_fam_func (Op_cat Z)
  : Functor
      (Op_cat (Fam_cat Z))
      (Fam_cat (Op_cat Z))
```

Then compose with the opposite of `Edge_fam Z`:

```text
HomPresheaf_fam [Z]
  : tau (Functor Z (Fam_cat (Op_cat Z)))
≔ comp_cat_fapp0
     (Presheaf_fam_func (Op_cat Z))
     (Op_func (Edge_fam Z))
```

Objectwise:

```text
Fam_app_cat (fapp0 (HomPresheaf_fam Z) x) y
  -> Functor_cat (Op_cat (Hom_cat Z x y)) Cat_cat
```

where:

```text
x : Obj Z
y : Obj (Op_cat Z)
```

This is the desired internal family:

```text
x : Z |-> (y : Z^op |-> Hom_Z(x,y)^op -> Cat)
```

## Directed `homd` Target

Let:

```text
E : tau (Fam Z)
```

The desired endpoint order is:

```text
x : Z,
u : E[x]^op,
y : Z^op,
v : E[y],
f : Hom_Z(x,y)
  |- Hom_{E[y]}(E(f)(u), v)
```

The outer family of targets is obtained by first, for each `x`, forming a
mixed family over `Op_cat Z`:

```text
Functor_fam [Op_cat Z]
  E
  (fapp0 (HomPresheaf_fam Z) x)
  : Fam (Op_cat Z)
```

This is well-typed because with `K = Op_cat Z`:

```text
Fam (Op_cat K) = Fam Z
```

so the first argument of `Functor_fam [Op_cat Z]` may be `E`.

Objectwise this family is:

```text
y : Z^op |- Functor_cat (E[y]) (Functor_cat (Hom_Z(x,y)^op) Cat)
```

Then close over `y` by sections:

```text
Pi_func (Op_cat Z)
```

Internally, define the target family:

```text
Homd_target_fam [Z] (E : tau (Fam Z))
  : tau (Fam Z)
```

as:

```text
Homd_target_fam E
  := comp_cat_fapp0
       (comp_cat_fapp0
         (Pi_func (Op_cat Z))
         (fapp0 (Functor_mix_fam_func (Op_cat Z)) E))
       (HomPresheaf_fam Z)
```

Type trace:

```text
fapp0 (Functor_mix_fam_func (Op_cat Z)) E
  : Functor (Fam_cat (Op_cat Z)) (Fam_cat (Op_cat Z))

Pi_func (Op_cat Z)
  : Functor (Fam_cat (Op_cat Z)) Cat_cat

comp_cat_fapp0
  (Pi_func (Op_cat Z))
  (fapp0 (Functor_mix_fam_func (Op_cat Z)) E)
  : Functor (Fam_cat (Op_cat Z)) Cat_cat

HomPresheaf_fam Z
  : Functor Z (Fam_cat (Op_cat Z))

Homd_target_fam E
  : Functor Z Cat_cat
```

Objectwise:

```text
fapp0 (Homd_target_fam E) x
  -> Pi_cat
       (Functor_fam
         E
         (fapp0 (HomPresheaf_fam Z) x))
```

That is:

```text
x : Z
  |- Pi_{y : Z^op}
       Functor_cat
         E[y]
         (Functor_cat (Hom_Z(x,y)^op) Cat)
```

The final `homd` category is then the category of transformations from
the fibre-opposite source family to this target:

```text
Homd_int_cat [Z] (E : tau (Fam Z)) : Cat
  := Transf_cat
       (comp_cat_fapp0 op E)
       (Homd_target_fam E)
```

Here:

```text
comp_cat_fapp0 op E : Fam Z
```

has fibre:

```text
x |- Op_cat (E[x])
```

An object of `Homd_int_cat E` is therefore a natural transformation:

```text
op o E  =>  Homd_target_fam E
```

Its component at `x` is a functor:

```text
E[x]^op
  -> Pi_{y : Z^op}
       Functor_cat
         E[y]
         (Functor_cat (Hom_Z(x,y)^op) Cat)
```

Evaluating that component at `u : E[x]^op`, then evaluating the section
at `y : Z^op`, then evaluating the resulting functor at `v : E[y]`,
gives:

```text
Functor_cat (Op_cat (Hom_cat Z x y)) Cat_cat
```

This is the fully internal source of:

```text
sigma_hom_fam E x u y v
```

## Endpoint Projection

The endpoint projection should be a stable head, not the foundation:

```text
homd_eval_func [Z] (E : tau (Fam Z))
  (x : tau (Obj Z))
  (u : tau (Obj (Op_cat (Fam_app_cat E x))))
  (y : tau (Obj (Op_cat Z)))
  (v : tau (Obj (Fam_app_cat E y)))
  : tau (Functor (Op_cat (Hom_cat Z x y)) Cat_cat)
```

Its intended source is:

1. take the component at `x` of an object of `Homd_int_cat E`,
2. apply it to `u : E[x]^op`,
3. evaluate the resulting `Pi_cat` section at `y : Z^op`,
4. apply the resulting functor `E[y] -> (Hom_Z(x,y)^op -> Cat)` to `v`.

For the canonical `homd` object, the endpoint should normalize to:

```text
sigma_hom_fam E x u y v
  : Functor (Op_cat (Hom_cat Z x y)) Cat_cat
```

with object computation:

```text
fapp0 (sigma_hom_fam E x u y v) f
  -> Hom_cat
       (Fam_app_cat E y)
       (fib_cov_tapp0_fapp0 E f u)
       v
```

where `f` is an object of `Op_cat (Hom_cat Z x y)`, semantically a base
arrow `x -> y`.

The endpoint head exists to keep rewrite rules manageable. It should not
replace the internal construction.

## Why the Outer and Inner Closures Look Different

The construction uses:

```text
Transf_cat (op o E) (Homd_target_fam E)
```

for the outer `x,u` layer, but:

```text
Pi_func (Op_cat Z)
```

for the inner `y` layer. This is not a semantic inconsistency.

`Pi_cat D` is the terminal-domain special case:

```text
Pi_cat D = Transf_cat (Terminal_fam K) D
```

The outer layer cannot be closed by `Pi_func`, because its source is not
terminal. It must quantify over:

```text
u : E[x]^op
```

and this is represented by the non-terminal source family:

```text
op o E : Fam Z
```

The inner `y` layer has no additional non-terminal source after
`Functor_fam` packages the `v : E[y]` argument into the pointwise functor
category:

```text
Functor_cat E[y] (Hom_Z(x,y)^op -> Cat)
```

So it is correctly closed as a section over `y : Z^op`:

```text
Pi_func (Op_cat Z)
```

Thus both layers use the same conceptual mechanism:

```text
dependent functions are transfors
```

The outer layer is the general case; the inner layer is the terminal
source case.

## Relation to `Catd` and Core Families

For core/path-indexed families, `Op_cat (Core_cat Z)` reduces back to
`Core_cat Z`, so the older `Catd` constructors can be recovered as
special cases. This explains why the old `emdash2.lp` architecture could
typecheck with `Op_catd` and `Functor_catd`.

For directed `Fam Z`, however, the `Catd` operations are not the right
foundation:

- `Op_catd` is not available for arbitrary `Fam Z`.
- `Functor_catd E D` with both arguments over the same directed base is
  not generally covariant.
- `Fibration_cov_catd M` should not be treated as the directed
  Grothendieck construction for all purposes; for the revised v3
  architecture, the real directed total is `Sigma_cat M`.

The mixed-variance layer is the directed replacement for the part of
`Catd` that was previously doing too much implicit variance work.

## Implementation Sequence

1. Add or confirm the generic directed family wrappers:

   ```text
   Fam_cat K := Functor_cat K Cat_cat
   Fam K := Obj (Fam_cat K)
   Fam_app_cat E k -> fapp0 E k
   Const_fam K A
   Terminal_fam K
   Pullback_fam E F
   Pi_cat E := Transf_cat (Terminal_fam K) E
   Pi_func K
   ```

2. Add `Functor_fam`:

   ```text
   Functor_fam [K]
     (A : tau (Fam (Op_cat K)))
     (B : tau (Fam K))
     : tau (Fam K)
   ```

   with the fibre rule:

   ```text
   Fam_app_cat (Functor_fam A B) k
     -> Functor_cat (Fam_app_cat A k) (Fam_app_cat B k)
   ```

3. Add `Functor_mix_fam_func`:

   ```text
   Functor_mix_fam_func [K]
     : Functor
         (Op_cat (Fam_cat (Op_cat K)))
         (Functor_cat (Fam_cat K) (Fam_cat K))
   ```

   with beta rules exposing `Functor_fam`.

4. Define `Edge_fam` internally:

   ```text
   Edge_fam Z
     := op_val_func Z o hom_int Z Z (id_func Z)
   ```

   with the sanity assertion:

   ```text
   fapp0 (fapp0 (Edge_fam Z) x) y
     == Op_cat (Hom_cat Z x y)
   ```

5. Define `Presheaf_fam_func K` functorially:

   ```text
   Presheaf_fam_func K
     := fapp0_func (Const_fam K Cat_cat) o Functor_mix_fam_func K
   ```

6. Define:

   ```text
   HomPresheaf_fam Z
     := Presheaf_fam_func (Op_cat Z) o Op_func (Edge_fam Z)
   ```

7. Define:

   ```text
   Homd_target_fam E
     := Pi_func (Op_cat Z)
          o (fapp0 (Functor_mix_fam_func (Op_cat Z)) E)
          o HomPresheaf_fam Z
   ```

8. Define the outer internal category:

   ```text
   Homd_int_cat E
     := Transf_cat (comp_cat_fapp0 op E) (Homd_target_fam E)
   ```

9. Add stable endpoint projections and connect them to
   `sigma_hom_fam` by rewrite rules only after the internal target
   typechecks.

## Test and Validation Plan

Run incrementally:

```text
lambdapi check -w emdash3.lp
```

Final repository check:

```text
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

Required assertions:

```text
Fam_app_cat (Const_fam K A) k
  == A

Fam_app_cat (Pullback_fam E F) a
  == Fam_app_cat E (fapp0 F a)

fapp0 (Pi_func K) E
  == Pi_cat E

Fam_app_cat (Functor_fam A B) k
  == Functor_cat (Fam_app_cat A k) (Fam_app_cat B k)

fapp0 (fapp0 (Functor_mix_fam_func K) A) B
  == Functor_fam A B

fapp0 (fapp0 (Edge_fam Z) x) y
  == Op_cat (Hom_cat Z x y)

Fam_app_cat (fapp0 (HomPresheaf_fam Z) x) y
  == Functor_cat (Op_cat (Hom_cat Z x y)) Cat_cat

fapp0 (Homd_target_fam E) x
  == Pi_cat
       (Functor_fam
         E
         (fapp0 (HomPresheaf_fam Z) x))
```

Endpoint/Grothendieck validation once projection heads are added:

```text
homd_eval_func E x u y v
  == sigma_hom_fam E x u y v

fapp0 (sigma_hom_fam E x u y v) f
  == Hom_cat (Fam_app_cat E y)
       (fib_cov_tapp0_fapp0 E f u)
       v

Hom_cat (Sigma_cat E) (Struct_sigma x u) (Struct_sigma y v)
  == Op_cat (Sigma_cat (sigma_hom_fam E x u y v))
```

## Assumptions and Open Points

- `Fam_cat K` is definitionally `Functor_cat K Cat_cat`.
- `Pi_cat E` is definitionally or canonically `Transf_cat (Terminal_fam K) E`.
- `Functor_mix_fam_func` is added as real internal functorial
  infrastructure; object-level abbreviations are not enough.
- `Edge_fam` is defined through `hom_int` and `op_val_func`, not through
  a product/uncurry encoding of `Z^op x Z -> Cat`.
- The endpoint projection can remain a stable head for rewrite
  discipline, but the fully internal construction is the
  mixed-variance `Transf_cat` object above.
- The old `Catd`/`Op_catd` path remains valid only for core/isofibration
  semantics or as a compatibility layer, not as the foundation for
  directed `Fam Z`.

