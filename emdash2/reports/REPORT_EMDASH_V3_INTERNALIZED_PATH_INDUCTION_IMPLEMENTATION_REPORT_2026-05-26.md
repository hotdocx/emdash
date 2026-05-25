# emdash v3.2 Internalized Path Induction Implementation Report

Date: 2026-05-26.

## Scope

This report records the first implementation pass for
`reports/REPORT_EMDASH_V3_INTERNALIZED_PATH_INDUCTION_PLAN.md`.

The implemented work covers the prerequisite internalized-constructor layers
and the fixed-`x` path-induction packaging. It deliberately stops short of the
fully internal outer-`x` path induction and the full directed-composition
normalization proof.

## Implemented In `emdash3_2.lp`

### Internalized `Catd_cat`

Added:

```lambdapi
symbol Catd_cat_func : τ (Functor (Op_cat Cat_cat) Cat_cat)
```

defined by evaluating the existing `Functor_cat_func` at `Cat_cat`.

Added a focused assertion:

```text
Catd_cat_func[K] == Catd_cat K
```

### Pullback Functor Package

Added:

```lambdapi
injective symbol Pullback_catd_func [A B : Cat]
  (F : τ (Functor A B))
  : τ (Functor (Catd_cat B) (Catd_cat A));
```

with object action:

```text
Pullback_catd_func(F)[E] == Pullback_catd E F
```

The general `Pullback_catd` remains a composition definition. This keeps the
special `Sigma_proj1_pullback_catd` as the only discriminable comprehension
pullback head.

### Global Pi Object Component

Added:

```lambdapi
constant symbol Pi_int_funcd
  : τ (Functord
      Catd_cat_func
      (@Const_catd (Op_cat Cat_cat) Cat_cat));
```

with component rule:

```text
Pi_int_funcd[K] == Pi_func K
```

The rule uses implicit source/target family slots because the fully spelled
form was too brittle for assertions after conversion.

### Section Pullback Transfor

Added:

```lambdapi
injective symbol section_pullback_transf [A B : Cat]
  (F : τ (Functor A B))
```

as the ordinary naturality component:

```text
Pi_func B(E) -> Pi_func A(F^*E)
```

with component:

```text
section_pullback_transf(F)[E] == section_pullback_func F E
```

This documents the intended naturality of `Pi_int_funcd` without adding a broad
base-arrow projection for arbitrary `Functord` objects.

### PathOut As A Functor Of `x`

Added:

```lambdapi
symbol PathOut_cat_func [Z : Cat]
  : τ (Functor (Op_cat Z) Cat_cat);
```

with:

```text
PathOut_cat_func(Z)[x] == PathOut_cat Z x
```

Added the varying motive-category family:

```lambdapi
symbol PathOutMotives_catd [Z : Cat]
  : τ (Catd Z);
```

with:

```text
PathOutMotives_catd(Z)[x] == Catd_cat(PathOut_cat Z x)
```

This is the first prerequisite for eventual outer-`x` internalization.

### Packaged Refl Arrow Section

Added:

```lambdapi
constant symbol pathout_refl_arrow_sec [Z : Cat] (x : τ (Obj Z))
  : τ (Obj (Pi_cat
      (@Rep_catd
        (@PathOut_cat Z x)
        (@pathout_refl_obj Z x))));
```

with pointwise computation:

```text
pathout_refl_arrow_sec(Z,x)[(y,p)]
  == pathout_refl_arrow Z x y p
```

This packages the existing constant `pathout_refl_arrow`; it does not yet
construct it from Sigma hom normal forms.

### Fixed-`x` Internal Path Induction

Added the source and target families over the motive category:

```lambdapi
symbol PathInd_src_catd [Z : Cat] (x : τ (Obj Z))
  : τ (Catd (@Catd_cat (@PathOut_cat Z x)));

symbol PathInd_tgt_catd [Z : Cat] (x : τ (Obj Z))
  : τ (Catd (@Catd_cat (@PathOut_cat Z x)));
```

with fibres:

```text
PathInd_src_catd(Z,x)[E] == E[(x,id_x)]
PathInd_tgt_catd(Z,x)[E] == Pi_cat E
```

Added:

```lambdapi
constant symbol PathInd_func [Z : Cat] (x : τ (Obj Z))
  : τ (Functord
      (@PathInd_src_catd Z x)
      (@PathInd_tgt_catd Z x));
```

with component:

```text
PathInd_func(Z,x)[E](u) == path_ind_sec Z x E u
```

This is the first genuinely more-internal version of the current
`path_ind_sec`, while still keeping `Z` and `x` external.

### Fixed-`x` Composition Benchmark Infrastructure

Added:

```lambdapi
injective symbol CompTarget_catd [Z : Cat] (x : τ (Obj Z)) : τ (Catd Z);
symbol CompMotive_catd [Z : Cat] (x : τ (Obj Z))
  : τ (Catd (@PathOut_cat Z x));
```

where:

```text
CompTarget_catd(Z,x)[y] == Functord_cat (Rep_Z(y)) (Rep_Z(x))
CompMotive_catd(Z,x)[(y,p)] == Functord_cat (Rep_Z(y)) (Rep_Z(x))
```

The first implementation tried to keep `CompTarget_catd` as a readable
`hom_con` alias in `Catd_cat Z`. The later root-cause analysis below changed
it into a stable computational family head, while preserving the same fibre
meaning.

Added:

```lambdapi
symbol path_comp_sec [Z : Cat] (x : τ (Obj Z))
  : τ (Obj (@Functord_cat Z (@Rep_catd Z x) (@CompTarget_catd Z x)));
```

as the reduced `fib_cov_transf` normal form of path induction on the
composition motive.

The compatibility assertion:

```text
path_ind_sec Z x (CompMotive_catd Z x) (id_funcd Rep_x)
  == path_comp_sec Z x
```

typechecks.

### Representable Precomposition Action

Follow-up implementation added the missing narrow representable-action layer.

Added:

```lambdapi
symbol hom_precomp_func [A : Cat] [X Y Z : τ (Obj A)]
  (f : τ (Hom A X Y))
  : τ (Functor (Hom_cat A Y Z) (Hom_cat A X Z));
```

with object action:

```text
hom_precomp_func(f)(g) == g ∘ f
```

Added a component rule for `hom_int` along its contravariant represented-object
argument:

```text
(hom_int F)[f]_b == hom_precomp_func(f)
```

in the precise orientation:

```text
f : Hom_A(x,y)
hom_int(F)[f]_b : Hom_A(y,F b) -> Hom_A(x,F b)
```

For the raw representable:

```text
Rep_catd_func Z : Op Z -> Catd_cat Z
```

this gives:

```text
Rep_catd_func[p]_z == hom_precomp_func(p)
```

Added:

```lambdapi
symbol path_comp_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  : τ (Functord (@Rep_catd Z y) (@Rep_catd Z x));
```

defined as the representable action of `p`. The focused computation now
typechecks:

```text
path_comp_func(p)[z](q) == q ∘ p
```

### Root Cause And Composition Redesign

The final review corrected the earlier stable-head diagnosis. The semantic
`hom_con` presentation is viable:

```text
CompTarget_catd Z x
  := hom_con (Catd_cat Z) (Rep_Z x) (Op Z) (Rep_catd_func Z)
```

The actual blockers were narrower:

1. v3.2 had a rule for the full hom-action of opposite functors,
   `fapp1_func (Op_func F)`, but not the capped action
   `fapp1_fapp0 (Op_func F)`. The `hom_con` route unfolds through `hom_` and
   produces exactly this capped opposite-functor action. The accepted rule is:

   ```lambdapi
   rule @fapp1_fapp0 _ _ (@Op_func $A $B $F) $X $Y $f
     ↪ @fapp1_fapp0 $A $B $F $Y $X $f;
   ```

2. Several benchmark assertions exposed reducible fibre expressions such as
   `Fibre_cat (CompTarget_catd Z x) y` in explicit source/target slots of
   `fapp0`. The fibre itself computes correctly, but those explicit slots can
   make conversion search brittle. The assertions were rewritten to use the
   canonical normal forms:

   ```text
   Hom_cat Z x y
   Functord_cat Z (Rep_Z y) (Rep_Z x)
   ```

With those two corrections, `CompTarget_catd` is implemented purely as the
semantic `hom_con` alias, not as a primitive stable family head. No
CompTarget-specific `fapp0`, `fapp1_func`, or `fapp1_fapp0` rules are retained;
the fibre and hom-action computations are inherited from the alias body. The
action helper names are retained only as readable aliases, and their types use
the canonical `Functord_cat` endpoints:

```lambdapi
symbol CompTarget_fapp1_func [...]
  : Functor
      (Functord_cat Z (Rep_Z a) (Rep_Z x))
      (Functord_cat Z (Rep_Z b) (Rep_Z x))
≔ fapp1_fapp0 (hom_con ...) p;

symbol CompTarget_fapp1_func_func [...]
  : Functor
      (Hom_cat Z a b)
      (Functor_cat
        (Functord_cat Z (Rep_Z a) (Rep_Z x))
        (Functord_cat Z (Rep_Z b) (Rep_Z x)))
≔ fapp1_func (hom_con ...) a b;
```

The earlier CompTarget-specific shortcut:

```text
CompTarget_fapp1_func(p)(id_{Rep_x}) -> path_comp_func(p)
```

is no longer needed; the computation is inherited from the semantic `hom_con`
body.

The resulting fixed-`x` benchmark typechecks:

```text
path_comp_sec(x)[p]       == path_comp_func(p)
path_comp_sec(x)[p][z](q) == q ∘ p
```

## Validation

Commands run successfully after the implemented changes:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

The full check covers:

- `emdash2.lp`;
- `emdash3_1.lp`;
- `emdash3_2.lp`.

## Remaining Work

Near-term:

- use the fixed-`x` composition result as the benchmark for future
  path-induction internalization;
- avoid broad underspecified `tapp0_fapp0` rules, since earlier probes timed
  out before the stable `CompTarget_catd` redesign.

Later:

- construct `pathout_refl_arrow` from Sigma hom/dependent-hom normal forms;
- internalize the outer `x` using `PathOutMotives_catd`;
- add context/product/projection/exchange infrastructure before attempting full
  `forall x y z` transitivity as a closed internal theorem.
