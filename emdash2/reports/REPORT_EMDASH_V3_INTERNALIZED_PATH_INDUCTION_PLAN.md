# emdash v3.2 Internalized Constructors And Path Induction Plan

Draft status: proposed follow-up implementation plan. As of 2026-05-26, the
first internalized-constructor and fixed-`x` path-induction layers have been
implemented in `emdash3_2.lp`; see
`reports/REPORT_EMDASH_V3_INTERNALIZED_PATH_INDUCTION_IMPLEMENTATION_REPORT_2026-05-26.md`.

Date: 2026-05-26.

## Scope

This report consolidates the design discussion after the implementation of
`reports/REPORT_EMDASH_V3_PI_ALIAS_SIGMA_PROJ1_PLAN.md`.

The immediate question is how to move from the current fixed-parameter directed
induction symbol:

```lambdapi
symbol path_ind_sec [Z : Cat] (x : τ (Obj Z))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x))))
  : τ (Obj (Pi_cat E));
```

to more internal forms where the motive, the chosen basepoint, and eventually
the outer object `x` are themselves handled by functorial or natural packages.

The report is intentionally a plan, not a claim that all proposed symbols are
already implementable. Several phases below are prerequisite discovery phases.
The main goal is to keep the next implementation iterations ordered and to
avoid confusing object-level notation with actual internalized Lambdapi
constructors.

## Current Implemented Baseline

The current `emdash3_2.lp` already contains the important first layer.

### Pi Alias

`Pi_cat` is now a defined alias:

```lambdapi
symbol Pi_cat [K : Cat] (E : τ (Catd K)) : Cat
≔ @Functord_cat K (@Const_catd K Terminal_cat) E;
```

The constant-family collapse was moved to the canonical head:

```lambdapi
rule @Functord_cat $K (@Const_catd $K Terminal_cat) (@Const_catd $K $A)
  ↪ Functor_cat $K $A;
```

This is the right direction. It removes one kernel representation of section
categories and lets section morphisms route through the general `Functord_cat`
and `Transfd_cat` machinery.

### Projection Pullback

The current file has the special stable pullback head:

```lambdapi
injective symbol Sigma_proj1_pullback_catd [K : Cat]
  (R D : τ (Catd K))
  : τ (Catd (@Sigma_cat K R));
```

with the important bridge:

```lambdapi
rule @Functord_cat
      (@Sigma_cat $K $R)
      (@Const_catd (@Sigma_cat $K $R) Terminal_cat)
      (@Sigma_proj1_pullback_catd $K $R $D)
  ↪ @Functord_cat $K $R $D;
```

This remains a central design choice. We should not make all `Pullback_catd`
cases syntactic constructors yet. The Sigma-projection case is special because
it expresses a comprehension conversion:

```text
Π_{(k,r):ΣR} D[k]  ==  Functord_cat R D
```

### Fixed-`x` PathOut And Directed Induction

The current file defines the raw representable and outgoing-arrow total:

```lambdapi
symbol Rep_catd_func [Z : Cat]
  : τ (Functor (Op_cat Z) (Catd_cat Z))
≔ @hom_int Z Z (@id_func Z);

symbol Rep_catd [Z : Cat] (x : τ (Obj Z))
  : τ (Catd Z)
≔ @fapp0 (Op_cat Z) (Catd_cat Z) (@Rep_catd_func Z) x;

symbol PathOut_cat [Z : Cat] (x : τ (Obj Z)) : Cat
≔ @Sigma_cat Z (@Rep_catd Z x);
```

Thus:

```text
Rep_Z(x)[y]      = Hom_Z(x,y)
PathOut_Z(x)     = Σ_y Hom_Z(x,y)
```

The current `path_ind_sec` already supports a motive depending on the
path/arrow:

```text
E : Catd(PathOut_Z(x))
```

and computes by transporting over the base `PathOut_Z(x)`:

```text
path_ind_sec(x,E,u)[(y,p)]
  = fib_cov_tapp0_func(E, (x,id_x), (y,p), u)
      (pathout_refl_arrow x y p)
```

The special case:

```text
E = Sigma_proj1_pullback_catd (Rep_Z(x)) D
```

reduces to the older ordinary fibration transport package:

```text
path_ind_sec x (Sigma_proj1_pullback_catd Rep_x D) u
  == fib_cov_transf D x u
```

This is the correct compatibility result.

## Main Design Thesis

More internal path induction should be built in layers.

Do not jump directly to a fully internal `path_ind` over all variables. The
current language lacks enough infrastructure to express every prerequisite
cleanly, especially when the base category of motives varies with `x`.

The correct order is:

1. Internalize universe and constructor operations that are already
   mathematically functorial.
2. Internalize `Pi_func` naturally in the base category.
3. Internalize fixed-`x` path induction over the motive category.
4. Internalize `x` only after the varying-base motive category is available.
5. Use directed composition/transitivity as the benchmark for whether the
   design computes correctly.

The most important discipline is:

```text
Object-level formulas are not internalization.
```

For example, a prose formula such as:

```text
PathInd_tgt_catd Z x [E] = Pi_cat E
```

is not enough. In Lambdapi, the internalized constructor must be expressed by
an actual functor or displayed functor, for example by applying `Pi_func` at the
appropriate motive category:

```text
PathInd_tgt_catd Z x
  should be represented by Pi_func (PathOut_cat Z x)
  or by a family whose fibre action reduces to that functor.
```

The same warning applies to notation like `[E]`, `[(x,E)]`, or `D[y]`.
Those are only surface readings. The implementation must provide the functor,
displayed functor, or section whose `fapp0`/`tapp0_fapp0` rules make those
readings compute.

## Variance Principles

The variance must come from the mathematical action, not from the apparent
arity of a constructor.

### `Catd_cat` Is Contravariant In The Base

`Catd_cat K` is the category of functorial families:

```text
K -> Cat
```

A functor:

```text
F : A -> B
```

acts by pullback:

```text
F^* : Catd(B) -> Catd(A)
```

Therefore the internalized category-of-families operation should live over the
opposite category of `Cat`:

```text
Catd_cat_func : Functor (Op_cat Cat_cat) Cat_cat
```

with object action:

```text
Catd_cat_func[K] = Catd_cat K
```

and arrow action along `F : A -> B`, seen as an arrow `B -> A` in
`Op_cat Cat_cat`:

```text
Catd_cat_func[F] = Pullback_catd_func F
  : Catd_cat B -> Catd_cat A
```

This is a prerequisite for internalizing the outer `x`, because the motive
category:

```text
Catd_cat(PathOut_Z(x))
```

varies with `x`.

### `Pi` Is Naturally Contravariant In The Base

For a functor:

```text
F : A -> B
```

there is a canonical pullback-on-sections map:

```text
section_pullback_func F E
  : Pi_B(E) -> Pi_A(F^*E)
```

So the fully internal Pi operation should not be a plain section over
`Cat_cat`. A plain section over `Cat_cat` would have the wrong direction unless
we also had a pushforward operation.

The right shape is a displayed/natural object over `Op_cat Cat_cat`:

```text
Pi_int_funcd
  : Functord
      Catd_cat_func
      (Const_catd (Op_cat Cat_cat) Cat_cat)
```

At an object `K`, its component is:

```text
Pi_int_funcd[K] = Pi_func K
  : Catd_cat K -> Cat_cat
```

Along `F : A -> B`, viewed as an arrow `B -> A` in `Op_cat Cat_cat`, its
naturality data should be exactly:

```text
Pi_func B(E) -> Pi_func A(F^*E)
```

implemented by `section_pullback_func F E`.

The current file has `Pi_func K` and `section_pullback_func F E`, but it does
not yet have this global `Pi_int_funcd` package.

## Relationship To Existing Universe Hom Infrastructure

Several constructor packages are homs in universe categories. This fact should
guide implementation and documentation, even when stable names are kept for
readability or rewrite control.

### `Functor_cat_func`

The current file has:

```lambdapi
constant symbol Functor_cat_func
  : τ (Functor (Op_cat Cat_cat) (Functor_cat Cat_cat Cat_cat));
```

Semantically, this is the internal hom in `Cat_cat`:

```text
A |-> Functor_cat A -
```

It is closely related to:

```text
hom_int Cat_cat Cat_cat (id_func Cat_cat)
```

but the current stable heads should not be replaced casually. A safer
implementation strategy is to document the relationship and add focused
component assertions, rather than trying to identify every package by broad
rewrite rules.

### `Catd_cat_func`

`Catd_cat_func` should likely be definable from existing infrastructure:

```text
Catd_cat_func
  ~= comp_cat_fapp0
       (fapp0_func Cat_cat Cat_cat Cat_cat)
       Functor_cat_func
```

The reason is:

```text
Functor_cat_func[K]       = Functor_cat K -
evaluation at Cat_cat     = Functor_cat K Cat_cat
Functor_cat K Cat_cat     -> Catd_cat K
```

The implementation should first probe this definition and add assertions:

```text
fapp0 Catd_cat_func K == Catd_cat K
```

and, if arrow action can be made to compute cleanly:

```text
fapp1_fapp0 Catd_cat_func F == Pullback_catd_func F
```

### `Functord_cat`

`Functord_cat K E D` is already the hom category in `Catd_cat K`:

```lambdapi
rule Hom_cat (@Catd_cat $K) $E $D
  ↪ @Functord_cat $K $E $D;
```

This matters for the directed composition benchmark. A family like:

```text
y |-> Functord_cat (Rep_Z(y)) (Rep_Z(x))
```

should not necessarily require a new primitive `Functord_cat_func`. It can be
formed using ordinary hom infrastructure in the category `Catd_cat Z`.

For example, with:

```text
Rep_catd_func Z : Op Z -> Catd_cat Z
Rep_Z(x)         : Obj(Catd_cat Z)
```

the family:

```text
y |-> Hom_{Catd_cat Z}(Rep_Z(y), Rep_Z(x))
```

can be expressed by a `hom_con`-style construction over `Catd_cat Z`.
Because `Hom_cat (Catd_cat Z)` reduces to `Functord_cat`, the fibre should
reduce to:

```text
Functord_cat (Rep_Z(y)) (Rep_Z(x))
```

This is the preferred first approach. Add a named wrapper only if the raw
`hom_con` expression becomes too brittle or unreadable.

### `Functor_catd` And `Transf_catd`

The current file already knows:

```text
Functor_catd(A,B)[k]      = Functor_cat(A[k],B[k])
Transf_catd(A,B,FF,GG)[k] = Transf_cat(FF[k],GG[k])
Hom_catd(Functor_catd A B, FF, GG) -> Transf_catd A B FF GG
```

This should be remembered during internalization work. It may allow us to reuse
`Functor_cat_func`, `hom_int`, `hom_con`, and `Hom_catd` infrastructure rather
than adding new primitive packages for every pointwise constructor.

The rule of thumb is:

```text
Reuse existing hom/category infrastructure first.
Add stable heads only for real rewrite discrimination or inference stability.
```

## Proposed Internalization Layers

### Layer 0: Keep The Current Implemented Kernel Stable

Before adding new internalized packages, keep the current successful baseline:

- `Pi_cat` remains a defined alias for terminal-source `Functord_cat`.
- `Sigma_proj1_pullback_catd` remains the special stable comprehension head.
- `path_ind_sec` remains the fixed-`Z`, fixed-`x` section constructor.
- `pathout_refl_arrow` remains a constant until Sigma hom normal forms are
  strong enough to construct it.

No broad rewrite rule should be added for:

```text
Pullback_catd
Pi_cat
path_ind_sec at arbitrary underspecified bases
```

The previous probe showed that an overly broad path-induction evaluation rule
can time out. Future rules should match canonical unfolded heads narrowly.

### Layer 1: Internalize `Catd_cat`

Add a package for the category-of-families construction:

```lambdapi
symbol Catd_cat_func
  : τ (Functor (Op_cat Cat_cat) Cat_cat)
≔ comp_cat_fapp0
     (@fapp0_func Cat_cat Cat_cat Cat_cat)
     Functor_cat_func;
```

Expected object assertion:

```lambdapi
assert [K : Cat] ⊢
  @fapp0 (Op_cat Cat_cat) Cat_cat Catd_cat_func K
    ≡ Catd_cat K;
```

Then add a stable pullback functor package:

```lambdapi
injective symbol Pullback_catd_func [A B : Cat]
  (F : τ (Functor A B))
  : τ (Functor (Catd_cat B) (Catd_cat A));

rule @fapp0 (@Catd_cat $B) (@Catd_cat $A)
      (@Pullback_catd_func $A $B $F) $E
  ↪ @Pullback_catd $A $B $E $F;
```

If the arrow action of `Catd_cat_func` is tractable, add the fold:

```text
Catd_cat_func[F] -> Pullback_catd_func F
```

The exact Lambdapi syntax should be probed carefully because `F : A -> B` is
seen as an arrow `B -> A` in `Op_cat Cat_cat`.

Acceptance checks for this layer:

```text
Catd_cat_func[K] == Catd_cat K
Pullback_catd_func(F)[E] == Pullback_catd E F
```

### Layer 2: Internalize `Pi_func` Naturally

Add the global natural/displayed Pi package:

```text
Pi_int_funcd
  : Functord
      Catd_cat_func
      (Const_catd (Op_cat Cat_cat) Cat_cat)
```

At object `K`, it should project to the existing `Pi_func K`:

```text
Pi_int_funcd[K] == Pi_func K
```

The naturality along `F : A -> B` should use `section_pullback_func F`.

Likely supporting symbol:

```lambdapi
symbol section_pullback_transf [A B : Cat]
  (F : τ (Functor A B))
  : τ (Transf
      (@Pi_func B)
      (@comp_cat_fapp0
        (@Catd_cat B)
        (@Catd_cat A)
        Cat_cat
        (@Pi_func A)
        (@Pullback_catd_func A B F)));
```

with component:

```text
section_pullback_transf(F)[E] == section_pullback_func F E
```

The exact type may need adjustment to match the current transformation
encoding, but the semantic target is fixed:

```text
Pi_B(E) -> Pi_A(F^*E)
```

Important warning: do not replace this with a plain `Pi_int_func` over
`Cat_cat`. That orientation would demand:

```text
Pi_A(F^*E) -> Pi_B(E)
```

which is not available without a pushforward/right Kan extension structure.

Acceptance checks for this layer:

```text
Pi_int_funcd[K] == Pi_func K
section_pullback_transf(F)[E] == section_pullback_func F E
section_pullback_func(F,E)(s)[a] == s[F a]
```

### Layer 3: Internalize `PathOut` As A Functor Of `x`

The current fixed-`x` definitions can be packaged functorially.

Raw representables are already internalized:

```text
Rep_catd_func Z : Op_cat Z -> Catd_cat Z
```

Define the outgoing-arrow category as a functor of `x`:

```lambdapi
symbol PathOut_cat_func [Z : Cat]
  : τ (Functor (Op_cat Z) Cat_cat)
≔ comp_cat_fapp0
     (@Sigma_func Z)
     (@Rep_catd_func Z);
```

Object action should compute to:

```text
PathOut_cat_func Z [x] == PathOut_cat Z x
```

Then define the motive category varying with `x`.

Since:

```text
PathOut_cat_func Z : Op Z -> Cat
Catd_cat_func       : Op Cat -> Cat
```

we use opposite on `PathOut_cat_func Z`:

```text
Op_func(PathOut_cat_func Z) : Z -> Op Cat
```

and compose:

```lambdapi
symbol PathOutMotives_catd [Z : Cat]
  : τ (Catd Z)
≔ comp_cat_fapp0
     Catd_cat_func
     (@Op_func (Op_cat Z) Cat_cat (@PathOut_cat_func Z));
```

Expected fibre:

```text
PathOutMotives_catd Z [x]
  == Catd_cat(PathOut_cat Z x)
```

This layer is the first real prerequisite for internalizing the outer `x`.

Acceptance checks:

```text
PathOut_cat_func(Z)[x] == PathOut_cat Z x
PathOutMotives_catd(Z)[x] == Catd_cat(PathOut_cat Z x)
```

### Layer 4: Internalize Fixed-`x` Path Induction Over Motives

Before internalizing `x`, make the fixed-`x` constructor more internal in its
motive and basepoint arguments.

For fixed `Z` and `x`, define the source family over the motive category:

```text
PathInd_src_catd Z x : Catd(Catd_cat(PathOut_cat Z x))
PathInd_src_catd Z x [E] = E[(x,id_x)]
```

This should be implemented as an evaluation-at-refl functor, not as an
object-level bracket formula. The expected object action is:

```text
E |-> Fibre_cat E (pathout_refl_obj Z x)
```

A likely package is:

```text
pathout_refl_eval_func Z x
  : Functor (Catd_cat(PathOut_cat Z x)) Cat_cat
```

with:

```text
pathout_refl_eval_func Z x [E]
  == Fibre_cat E (pathout_refl_obj Z x)
```

Then the source family is this functor read as a `Catd` over the motive
category.

The target family over the same motive category is simply Pi:

```text
PathInd_tgt_catd Z x : Catd(Catd_cat(PathOut_cat Z x))
PathInd_tgt_catd Z x [E] = Pi_cat E
```

Implementation should reuse:

```text
Pi_func (PathOut_cat Z x)
```

not a new object-level rewrite.

Then define a fixed-`x` internal path-induction displayed functor:

```text
PathInd_func Z x
  : Functord
      (PathInd_src_catd Z x)
      (PathInd_tgt_catd Z x)
```

At a motive `E`, its fibre functor should map:

```text
u : E[(x,id_x)]
```

to:

```text
path_ind_sec Z x E u : Pi_cat E
```

This is strictly more internal than the current `path_ind_sec`: it pushes `E`
and `u` inside a functorial/natural package, while still keeping `Z` and `x`
external.

Expected component rule:

```text
PathInd_func(Z,x)[E](u) == path_ind_sec Z x E u
```

This is the best next target before trying to internalize the outer `x`.

### Layer 5: Internalize `pathout_refl_arrow`

The current:

```lambdapi
constant symbol pathout_refl_arrow [Z : Cat] (x y : τ (Obj Z))
  (p : τ (Hom Z x y))
  : τ (Hom
      (@PathOut_cat Z x)
      (@pathout_refl_obj Z x)
      (@pathout_obj Z x y p));
```

is intentionally a placeholder.

For fixed `Z` and `x`, a more internal version should be a section of the
representable in `PathOut_Z(x)`:

```text
pathout_refl_arrow_sec Z x
  : Obj (Pi_cat
      (Rep_catd (PathOut_cat Z x) (pathout_refl_obj Z x)))
```

with pointwise computation:

```text
pathout_refl_arrow_sec Z x [(y,p)]
  == pathout_refl_arrow Z x y p
```

This does not yet construct the arrow; it packages it.

The eventual construction should come from the Sigma hom normal form for:

```text
PathOut_Z(x) = Sigma_cat(Rep_Z(x))
```

The intended arrow from `(x,id_x)` to `(y,p)` has:

```text
base arrow:      p : Hom_Z(x,y)
fibre witness:   p = p after transporting id_x along p
```

In the strict categorical encoding, this should be expressible by the identity
or canonical arrow in the fibre hom category after the Sigma hom/dependent-hom
normal forms are strong enough.

Do not force this construction too early. Keeping the constant while packaging
it as a section is a safer intermediate step.

### Layer 6: Directed Composition As The Benchmark

The practical test for fixed-`x` path induction is directed composition:

```text
forall y z, Hom_Z(x,y) -> Hom_Z(y,z) -> Hom_Z(x,z)
```

This is the fixed-source version of HoTT path transitivity:

```text
forall x y z, x = y -> y = z -> x = z
```

Fixed `x` is enough for this local composition operation. The fully quantified
version, where `x` itself varies naturally, requires the later outer-`x`
internalization and probably product/reordering infrastructure.

For fixed `x`, define a motive over `PathOut_Z(x)` whose fibre at `(y,p)` is:

```text
Functord_cat (Rep_Z(y)) (Rep_Z(x))
```

This category contains natural transformations:

```text
Hom_Z(y,-) -> Hom_Z(x,-)
```

An object of this category is exactly "precompose by p".

The motive should be formed by reusing hom infrastructure in `Catd_cat Z`.
With:

```text
Rep_catd_func Z : Op Z -> Catd_cat Z
Rep_Z(x)         : Obj(Catd_cat Z)
```

use a `hom_con`-style family mathematically:

```text
CompTarget_catd Z x [y]
  = Hom_{Catd_cat Z}(Rep_Z(y), Rep_Z(x))
  = Functord_cat (Rep_Z(y)) (Rep_Z(x))
```

Implementation note added after the 2026-05-26 iteration: the raw `hom_con`
alias was not a good enough rewrite discriminator for the full composition
benchmark. The implemented kernel uses `CompTarget_catd` as a stable head with
the same fibre meaning and a specific base-arrow action head.

Then pull it back along the projection:

```text
Sigma_proj1_func (Rep_Z(x)) : PathOut_Z(x) -> Z
```

so that the motive at `(y,p)` is:

```text
CompMotive_x[(y,p)] = CompTarget_x[y]
```

The intended kernel head is the existing special projection pullback:

```text
CompMotive_catd Z x
  = Sigma_proj1_pullback_catd
      (Rep_catd Z x)
      (CompTarget_catd Z x)
```

The basepoint object at `(x,id_x)` is:

```text
id_funcd Z (Rep_Z(x))
  : Functord_cat (Rep_Z(x)) (Rep_Z(x))
```

Applying `path_ind_sec` should produce:

```text
compose_from_x
  : Π (y,p), Functord_cat (Rep_Z(y)) (Rep_Z(x))
```

and evaluating the resulting natural transformation at:

```text
q : Hom_Z(y,z)
```

should compute to:

```text
q ∘ p : Hom_Z(x,z)
```

The expected computation should come from existing hom-action rules, especially
the rule for `hom_`:

```lambdapi
rule fapp0 (@fapp1_fapp0 $B Cat_cat (@hom_ $A $B $F $W) $X $Y $f) $g
  ↪ comp_fapp0 (fapp1_fapp0 $F $f) $g;
```

For this benchmark, the relevant instance is the hom action in the category
`Catd_cat Z`, induced by the representable functor `Rep_catd_func Z`. If this
does not compute all the way to `comp_fapp0 q p`, add only focused assertions
or narrow rules around the representable action.

This benchmark is important because it tests the whole design:

- arrow-dependent motives over `PathOut_Z(x)`;
- the `Sigma_proj1_pullback_catd` bridge;
- reuse of `hom_con` and `Functord_cat` as homs in `Catd_cat Z`;
- computation of representable action to ordinary composition.

### Layer 7: Internalize The Outer `x`

Only after Layers 1-6 should we attempt the outer-`x` version.

At that point we should have:

```text
PathOutMotives_catd Z [x] = Catd_cat(PathOut_Z(x))
```

and a Pi package reindexed along `PathOut_cat_func Z`:

```text
PathOutPi_funcd Z
  : Functord
      (PathOutMotives_catd Z)
      (Const_catd Z Cat_cat)
```

with component:

```text
PathOutPi_funcd Z [x] = Pi_func(PathOut_cat Z x)
```

The fixed-`x` source family:

```text
E |-> E[(x,id_x)]
```

must also become a family varying with `x`. This is harder than the target,
because the evaluation point:

```text
pathout_refl_obj Z x : Obj(PathOut_Z(x))
```

itself varies in a varying category.

The likely shape is:

```text
PathIndSrc_catd Z
  : Catd (Sigma_cat Z (PathOutMotives_catd Z))
```

whose fibre at `(x,E)` is:

```text
E[(x,id_x)]
```

and:

```text
PathIndTgt_catd Z
  : Catd (Sigma_cat Z (PathOutMotives_catd Z))
```

whose fibre at `(x,E)` is:

```text
Pi_cat E
```

Then the fully outer-`x` internal path induction would be a displayed functor:

```text
PathInd_funcd Z
  : Functord PathIndSrc_catd PathIndTgt_catd
```

with component:

```text
PathInd_funcd Z [(x,E)](u) == path_ind_sec Z x E u
```

This is a plausible target, but it depends on successful implementation of:

- `Catd_cat_func`;
- `Pullback_catd_func`;
- `Pi_int_funcd`;
- `PathOut_cat_func`;
- `PathOutMotives_catd`;
- evaluation at a moving object in a moving category;
- enough Sigma total/category infrastructure to express the base
  `Σ_x Catd(PathOut_x)`.

It should not be implemented first.

### Layer 8: Full Transitivity Requires More Context Infrastructure

The fully quantified theorem:

```text
forall x y z, Hom_Z(x,y) -> Hom_Z(y,z) -> Hom_Z(x,z)
```

is not just fixed-`x` path induction. To express it as a closed internal object
with all variables bound naturally, we will likely need:

- iterated products or Sigma/Pi context categories;
- projections from those contexts;
- symmetry/exchange maps for reordering variables;
- stable pullback rules along those projections;
- surface syntax conventions for the implicit context rearrangements.

Therefore, fixed-`x` composition is the near-term benchmark. Full transitivity
is a later context-engineering benchmark.

## Recommended Implementation Order

### Phase 1: Add `Catd_cat_func`

Probe the definition by composition from `Functor_cat_func`.

Add only object-action assertions first. If those pass, add
`Pullback_catd_func` and a narrow arrow-action fold.

Validation:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
```

### Phase 2: Add `Pullback_catd_func`

Introduce the functorial package:

```text
F |-> F^*
```

but only for the action on families:

```text
Pullback_catd_func(F)[E] == Pullback_catd E F
```

Do not make `Pullback_catd` itself an injective general constructor.

### Phase 3: Add `Pi_int_funcd`

Implement the global Pi natural/displayed package over `Op_cat Cat_cat`.

If generic displayed naturality projections for `Functord` are not available,
add a specialized `section_pullback_transf` first and document that it is the
naturality data of `Pi_int_funcd`.

### Phase 4: Add `PathOut_cat_func` And `PathOutMotives_catd`

Package:

```text
x |-> PathOut_Z(x)
x |-> Catd_cat(PathOut_Z(x))
```

as actual functor/family terms.

This phase should include assertions that the object fibres reduce to the
existing fixed-`x` symbols.

### Phase 5: Add Fixed-`x` Internal `PathInd_func`

For fixed `Z,x`, define:

```text
PathInd_src_catd Z x
PathInd_tgt_catd Z x
PathInd_func Z x
```

with component:

```text
PathInd_func(Z,x)[E](u) == path_ind_sec Z x E u
```

This is the next conceptual milestone.

### Phase 6: Package `pathout_refl_arrow`

Add:

```text
pathout_refl_arrow_sec Z x
```

as a section over `PathOut_Z(x)` whose pointwise value is the current
`pathout_refl_arrow`.

Do not force its construction from Sigma homs in the same phase unless the
necessary normal forms are already straightforward.

### Phase 7: Implement The Fixed-`x` Composition Benchmark

Build:

```text
CompTarget_catd Z x [y] = Functord_cat (Rep_Z(y)) (Rep_Z(x))
CompMotive_catd Z x     = pullback along Sigma_proj1_func(Rep_Z(x))
```

Use `path_ind_sec` at the identity natural transformation.

Add assertions for:

```text
compose_from_x(y,p) : Functord_cat (Rep_Z(y)) (Rep_Z(x))
compose_from_x(y,p)[z](q) == q ∘ p
```

If the final assertion does not reduce, inspect the representable/hom action
path before adding new heads.

### Phase 8: Attempt Outer-`x` Internalization

Only after the fixed-`x` benchmark passes, define the total base:

```text
Σ_x Catd(PathOut_Z(x))
```

and add:

```text
PathIndSrc_catd Z
PathIndTgt_catd Z
PathInd_funcd Z
```

This phase is expected to reveal missing infrastructure around moving
evaluation points and context projections.

## Validation Strategy

Each phase should be checked with:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
```

Full validation after a coherent phase:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

Recommended focused assertions:

```text
Catd_cat_func[K] == Catd_cat K
Pullback_catd_func(F)[E] == Pullback_catd E F
Pi_int_funcd[K] == Pi_func K
section_pullback_transf(F)[E] == section_pullback_func F E
PathOut_cat_func(Z)[x] == PathOut_cat Z x
PathOutMotives_catd(Z)[x] == Catd_cat(PathOut_cat Z x)
PathInd_tgt_catd(Z,x)[E] == Pi_cat E
PathInd_src_catd(Z,x)[E] == Fibre_cat E (pathout_refl_obj Z x)
PathInd_func(Z,x)[E](u) == path_ind_sec Z x E u
pathout_refl_arrow_sec(Z,x)[(y,p)] == pathout_refl_arrow Z x y p
CompTarget_catd(Z,x)[y] == Functord_cat (Rep_Z(y)) (Rep_Z(x))
compose_from_x(y,p)[z](q) == comp_fapp0 q p
```

## Risks And Guardrails

### Broad Pullback Normalization

Do not make general `Pullback_catd` injective or rewrite-heavy. Use:

```text
Pullback_catd_func
```

as a functor package, and keep:

```text
Sigma_proj1_pullback_catd
```

as the special discriminable comprehension head.

### Wrong Pi Variance

Do not introduce a plain `Pi_int_func` over `Cat_cat` unless a pushforward
operation has been added. The canonical operation is:

```text
Pi_B(E) -> Pi_A(F^*E)
```

so the base is `Op_cat Cat_cat`.

### Object-Level Internalization

Do not accept definitions that only state fibre equations in comments. Every
internalized layer needs an actual package:

```text
Functor
Functord
Pi_cat section
Sigma_cat total
```

and component rules/assertions.

### Rewriting Through Defined Notation

Since `Pi_cat`, `Rep_catd`, and `PathOut_cat` are defined names, rules that
must fire reliably may need to match their canonical unfolded forms, as the
current `path_ind_sec` rule already does.

### Moving Refl Is Not A Strict Section For Free

The assignment:

```text
x |-> (x,id_x) : PathOut_Z(x)
```

is an object in a varying category. It is not automatically an ordinary
functorial section of `PathOut_cat_func`. Its naturality is tied to composition
and to the eventual construction of `pathout_refl_arrow`.

Treat this as a real source-side problem, not as notation.

## Open Questions

1. What is the cleanest generic projection for base-arrow naturality of a
   `Functord` object?

   The current file has strong component projections at objects, but the global
   `Pi_int_funcd` naturality may require an explicit projection or a specialized
   `section_pullback_transf`.

2. Should `Catd_cat_func` be a definition or an injective stable head?

   First preference: define it from `Functor_cat_func` and evaluation at
   `Cat_cat`. Add a stable head only if rules involving it become too brittle.

3. How much of `Sigma_func` should be internalized in the base category?

   For `PathOut_cat_func Z`, objectwise `Sigma_func Z` is enough. A fully
   base-varying Sigma package has subtler variance because `F : A -> B` induces
   `Σ_A(F^*E) -> Σ_B(E)`, not the same direction as Pi.

4. Can `pathout_refl_arrow` be constructed now from Sigma homs?

   Tentative answer: not yet. Package it as a section first, then construct it
   after Sigma hom/dependent-hom normal forms are stable.

5. Does the fixed-`x` composition benchmark compute to `comp_fapp0` without new
   rewrite rules?

   Resolved for the current fixed-`x` benchmark: the raw `hom_con` path was too
   brittle, so `CompTarget_catd` is implemented as a stable head with a narrow
   arrow-action rule. The final assertion `path_comp_sec(x)[p][z](q) == q ∘ p`
   now typechecks.

6. When should full `forall x y z` transitivity be attempted?

   After fixed-`x` composition works and after product/context projection and
   variable-exchange infrastructure exists.

## Summary Recommendation

The next implementation should not try to replace `path_ind_sec` immediately
with a single maximally internal symbol.

The best next move is:

1. add `Catd_cat_func` and `Pullback_catd_func`;
2. add `Pi_int_funcd` with `section_pullback_func` as its naturality;
3. package `PathOut_cat_func` and `PathOutMotives_catd`;
4. internalize fixed-`x` path induction as a displayed functor over the motive
   category;
5. use fixed-`x` directed composition as the computation benchmark;
6. only then internalize the outer `x`.

This keeps the architecture aligned with the current successful Pi-alias and
Sigma-projection-pullback design, while making the path-induction layer
progressively more internal instead of guessing the final form too early.
