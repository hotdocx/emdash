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

Follow-up implementation added the narrow arrow-action fold:

```text
Catd_cat_func[F] == Pullback_catd_func F
```

for `F : A -> B`, read as an arrow `B -> A` in `Op_cat Cat_cat`.
Because `Catd_cat_func` is a definition, the accepted rule matches the
canonical unfolded composition head with middle category `Catd_cat Cat_cat`,
not the readability form `Functor_cat Cat_cat Cat_cat`.

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

### Generic Base-Arrow Transport Reassessment

The path-induction transport square should not remain the only place where
base-arrow functoriality is visible. The implementation now includes a generic
core layer:

```lambdapi
symbol catd_transport_func [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  : τ (Functor (Fibre_cat E x) (Fibre_cat E y));

symbol functord_transport_func [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  : τ (Functor (Fibre_cat E x) (Fibre_cat D y));

symbol functord_transport_lhs_func ...
symbol functord_transport_rhs_func ...
constant symbol functord_transport_transf ...
```

with checked object-action reductions for the two naturality routes:

```text
functord_transport_lhs_func(FF,p)(u)
  == catd_transport_func(D,p)(Fibre_func(FF,x)(u))

functord_transport_rhs_func(FF,p)(u)
  == Fibre_func(FF,y)(catd_transport_func(E,p)(u))
```

This is the uniform prerequisite for path-specific coherence squares.

The implementation also added the canonical total Sigma arrow:

```lambdapi
constant symbol sigma_transport_arrow [K : Cat] (E : τ (Catd K))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (Hom
      (Sigma_cat K E)
      (Struct_sigma x u)
      (Struct_sigma y (catd_transport_func(E,p)(u))));
```

`pathout_motive_transport_arrow` is no longer a path-specific primitive; it is
defined as the specialization of `sigma_transport_arrow` to
`PathOutMotives_catd Z`.

A more ambitious generic action helper for `Sigma_catd_functord_catd` along
`sigma_transport_arrow` was probed, but the fully expanded transfor-component
definition hit the bounded-check timeout. That helper was not added. The next
foundational prerequisite is a smaller stable projection for that Sigma-family
action.

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

The source side is routed through the named helper
`pathout_refl_eval_func Z x`, whose object action is evaluation at
`pathout_refl_obj Z x`.

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
only retained action helper is the readable capped-action alias
`CompTarget_fapp1_func`; its type uses canonical `Functord_cat` endpoints:

```lambdapi
symbol CompTarget_fapp1_func [...]
  : Functor
      (Functord_cat Z (Rep_Z a) (Rep_Z x))
      (Functord_cat Z (Rep_Z b) (Rep_Z x))
≔ fapp1_fapp0 (CompTarget_catd Z x) p;
```

No separate `CompTarget_fapp1_func_func` alias is retained. The full hom-action
is just the ordinary term `fapp1_func (CompTarget_catd Z x) a b`, reducing
through the semantic `hom_con` definition when needed.

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

### First Outer-`x` Path-Induction Package

Follow-up implementation added the first checked outer-`x` package over:

```text
Sigma_cat Z (PathOutMotives_catd Z)
```

Supporting rules added:

```text
Pullback_catd_func(F)[η][a] == η[F a]
Pullback_catd(Const_catd B C, F) == Const_catd A C
```

The second rule is the constant-family pullback normal form needed for the
target side.

Added:

```lambdapi
symbol PathOutPi_funcd [Z : Cat]
  : Functord (PathOutMotives_catd Z) (Const_catd Z Cat_cat)
```

as the pullback of `Pi_int_funcd` along `Op_func (PathOut_cat_func Z)`, with:

```text
PathOutPi_funcd(Z)[x] == Pi_func(PathOut_cat Z x)
```

Added the total-base target family:

```lambdapi
symbol PathIndTgt_catd [Z : Cat]
  : Catd (Sigma_cat Z (PathOutMotives_catd Z))
```

via the new universe-valued total-family helper:

```lambdapi
Sigma_catd_functord_catd(FF)[(k,r)] == FF[k](r)
```

specialized to `FF : Functord R (Const_catd K Cat_cat)`.

The checked target fibre is:

```text
PathIndTgt_catd(Z)[(x,E)] == Pi_cat E
```

Added the matching source-side evaluation package:

```lambdapi
symbol pathout_refl_eval_func [Z : Cat] (x : τ (Obj Z))
  : τ (Functor (@Catd_cat (@PathOut_cat Z x)) Cat_cat);

constant symbol PathOutReflEval_funcd [Z : Cat]
  : τ (Functord (@PathOutMotives_catd Z) (@Const_catd Z Cat_cat));
```

with checked component computation:

```text
PathOutReflEval_funcd(Z)[x] == pathout_refl_eval_func Z x
pathout_refl_eval_func(Z,x)[E] == E[(x,id_x)]
```

Follow-up implementation added two narrower computational bridges toward the
moving-`x` source action:

```text
(F o G)[f] == F[G[f]]
```

for ordinary functor composition, and:

```lambdapi
symbol pathout_refl_eval_base_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Functor
      (Fibre_cat E (@pathout_refl_obj Z x))
      (Fibre_cat E (@pathout_obj Z x y p)));
```

with:

```text
PathOutMotives_catd(Z)[p](E)[(y,id_y)] == E[(y,p)]
pathout_refl_eval_base_func(Z,x,y,p,E) == E[pathout_refl_arrow Z x y p]
pathout_refl_eval_base_func(Z,x,y,p,E)(u)
  == fib_cov_tapp0_func(E,(x,id_x),(y,p),u)(pathout_refl_arrow Z x y p)
```

This is the checked source-side map required by moving reflexive evaluation.
It is not yet packaged as the full naturality/coherence transfor for
`PathOutReflEval_funcd`.

Follow-up implementation added a canonical transported-motive helper and source
transport package:

```lambdapi
symbol pathout_motive_transport_obj [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Catd (@PathOut_cat Z y));

symbol pathout_motive_transport_arrow [Z : Cat]
  [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Hom
      (Sigma_cat Z (PathOutMotives_catd Z))
      (Struct_sigma x E)
      (Struct_sigma y (pathout_motive_transport_obj Z x y p E)));

symbol PathIndSrc_transport_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Functor
      (Fibre_cat (@PathIndSrc_catd Z) (Struct_sigma x E))
      (Fibre_cat
        (@PathIndSrc_catd Z)
        (Struct_sigma y (@pathout_motive_transport_obj Z x y p E))));
```

with checked computation:

```text
pathout_motive_transport_obj(Z,x,y,p,E) == PathOutMotives_catd(Z)[p](E)
pathout_motive_transport_arrow(Z,x,y,p,E)
  == sigma_transport_arrow(PathOutMotives_catd Z,p,E)
PathIndSrc_catd(Z)[(y,pathout_motive_transport_obj Z x y p E)] == E[(y,p)]
PathIndSrc_transport_func(Z,x,y,p,E) == pathout_refl_eval_base_func Z x y p E
PathIndSrc_transport_func(Z,x,y,p,E)(u)
  == fib_cov_tapp0_func(E,(x,id_x),(y,p),u)(pathout_refl_arrow Z x y p)
```

This gives the source side a stable action helper for the canonical
transported-motive total arrow. A direct `fapp1_fapp0 PathIndSrc_catd` rewrite
for this arrow was intentionally not added; the helper avoids depending on a
fragile rewrite match against the currently-defined total-family head.

The target side now has the matching section-pullback helper:

```lambdapi
symbol PathOut_transport_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  : τ (Functor (PathOut_cat Z y) (PathOut_cat Z x));

symbol pathout_pi_transport_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Functor
      (@Pi_cat (@PathOut_cat Z x) E)
      (@Pi_cat (@PathOut_cat Z y) (@pathout_motive_transport_obj Z x y p E)));

symbol PathIndTgt_transport_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Functor
      (Fibre_cat (@PathIndTgt_catd Z) (Struct_sigma x E))
      (Fibre_cat
        (@PathIndTgt_catd Z)
        (Struct_sigma y (@pathout_motive_transport_obj Z x y p E))));
```

with checked computation:

```text
PathOut_transport_func(Z,x,y,p) == PathOut_cat_func(Z)[p]
pathout_motive_transport_obj(Z,x,y,p,E)
  == Pullback_catd(E, PathOut_transport_func Z x y p)
PathOut_transport_func(Z,x,y,p)(pathout_refl_obj Z y) == pathout_obj Z x y p
PathIndTgt_transport_func(Z,x,y,p,E)
  == section_pullback_func(PathOut_transport_func Z x y p,E)
PathIndTgt_transport_func(Z,x,y,p,E)(s)[q]
  == s[PathOut_transport_func(Z,x,y,p)(q)]
PathIndTgt_transport_func(Z,x,y,p,E)(s)[pathout_refl_obj Z y]
  == s[pathout_obj Z x y p]
```

This completes the current source/target transport pair for canonical
transported-motive arrows. It is still not the full naturality proof for
`PathInd_funcd`; it supplies the two sides that such a coherence statement must
relate.

The path-induction coherence square has now been named at functor level:

```text
symbol PathInd_transport_lhs_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Functor
      (PathIndSrc_catd Z [(x,E)])
      (PathIndTgt_catd Z [(y,pathout_motive_transport_obj Z x y p E)]));

symbol PathInd_transport_rhs_func [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Functor
      (PathIndSrc_catd Z [(x,E)])
      (PathIndTgt_catd Z [(y,pathout_motive_transport_obj Z x y p E)]));

constant symbol PathInd_transport_transf [Z : Cat] [x y : τ (Obj Z)]
  (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x)))
  : τ (Transf
      (PathInd_transport_lhs_func Z x y p E)
      (PathInd_transport_rhs_func Z x y p E));
```

The checked object actions are:

```text
PathInd_transport_lhs_func(Z,x,y,p,E)(u)
  == PathIndTgt_transport_func(Z,x,y,p,E)(path_ind_sec Z x E u)

PathInd_transport_rhs_func(Z,x,y,p,E)(u)
  == path_ind_sec Z y (pathout_motive_transport_obj Z x y p E)
       (PathIndSrc_transport_func(Z,x,y,p,E)(u))
```

This is the current precise coherence boundary. A fully expanded
`PathInd_transport_app` component was probed, but it made conversion search hit
the bounded-check timeout, so it was not added. Future work should introduce a
smaller stable projection head before exposing component-level coherence.

Added the matching source family and outer path-induction displayed functor:

```lambdapi
symbol PathIndSrc_catd [Z : Cat]
  : Catd (Sigma_cat Z (PathOutMotives_catd Z));

constant symbol PathInd_funcd [Z : Cat]
  : Functord (PathIndSrc_catd Z) (PathIndTgt_catd Z);
```

with checked component rules:

```text
PathIndSrc_catd(Z)[(x,E)] == E[(x,id_x)]
PathInd_funcd(Z)[(x,E)] == path_ind_func_fapp0 Z x E
PathInd_funcd(Z)[(x,E)](u) == path_ind_sec Z x E u
```

`PathIndSrc_catd` is now routed through the same
`Sigma_catd_functord_catd` total-family helper as `PathIndTgt_catd`, using
`PathOutReflEval_funcd`. This gives the source side a displayed-functor
interface. The concrete map along a base arrow is now represented by
`PathIndSrc_transport_func`; the functor-level coherence square is named by
`PathInd_transport_transf`, while the component-level projection remains open.

The rule LHSs deliberately keep the total-base source category implicit. A probe
with explicit `Sigma_cat Z (PathOutMotives_catd Z)` did not fire after the
defined motive family normalized to its canonical composition pipeline.

## Validation

Commands run successfully after the implemented changes:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

The full check covers:

- `emdash2.lp`;
- `emdash3_2.lp`.

The same validation was rerun after adding the `Catd_cat_func` arrow-action
fold and after the first outer-`x` package, and both commands still succeeded.

## Remaining Work

Near-term:

- use the fixed-`x` composition result as the benchmark for future
  path-induction internalization and outer-`x` refinements;
- refine the base-arrow action/coherence of `PathOutReflEval_funcd`,
  `PathIndSrc_catd`, `PathIndTgt_catd`, and `PathInd_funcd`; the current package
  has checked fibres/components, canonical source and target transport helpers,
  and the functor-level coherence square `PathInd_transport_transf`, but not a
  cheap component-level coherence projection;
- add a stable, generic `Sigma_catd_functord_catd` action projection along
  `sigma_transport_arrow`; a fully expanded helper was probed and timed out, so
  this should be designed as a smaller core projection rather than reusing a
  large transfor-component expression directly;
- avoid broad underspecified `tapp0_fapp0` rules, since earlier probes timed
  out before the root cause was narrowed to missing projection rules and
  non-canonical explicit source/target slots.

Later:

- construct `pathout_refl_arrow` from Sigma hom/dependent-hom normal forms;
- strengthen the outer-`x` package once moving evaluation at `(x,id_x)` has a
  computational arrow-action story;
- add context/product/projection/exchange infrastructure before attempting full
  `forall x y z` transitivity as a closed internal theorem.
