# emdash v3.2 Pi Alias And Sigma Projection Pullback Consolidated Status

Date: 2026-05-31

Status: active consolidation for the v3.2 Pi-alias, Sigma-projection-pullback,
section-action, and early directed-induction foundation.

This report supersedes:

- `reports/REPORT_EMDASH_V3_PI_ALIAS_SIGMA_PROJ1_PLAN.md`
- `reports/REPORT_EMDASH_V3_PI_ALIAS_SIGMA_PROJ1_IMPLEMENTATION_REPORT_2026-05-25.md`

Those older reports can be retired after this consolidation. The active
implementation source remains `emdash3_2.lp`.

## Executive Summary

The Pi-alias and Sigma-projection-pullback migration is implemented and remains
part of the current v3.2 foundation.

The canonical section category is no longer a primitive kernel head:

```text
Pi_cat(E)
  = Functord_cat(Const_catd(K,Terminal_cat), E).
```

The special Sigma projection pullback is the stable comprehension head:

```text
Sigma_proj1_pullback_catd(R,D)
  = D pulled back along Sigma_proj1_func(R).
```

It supports the defining comprehension conversion:

```text
Pi_{(k,r):Sigma(R)} D[k]
  = Functord_cat(R,D).
```

The old terminal-specialized internal section-action chain:

```text
piapp1_int
piapp1_int_src_transf
piapp1_int_src_app
piapp1_int_tgt_transf
```

has been retired. The surviving section-action names:

```text
piapp1_src_obj
piapp1_func
piapp1_fapp0
```

are section-action surface/helper notation, not a separate Pi-specific
internal action pipeline.

The early directed-induction work from these reports has also been absorbed by
the later synthetic path-induction milestone:

```text
PathOut_Z(x) = Sigma y : Z, Hom_Z(x,y)
rho_{x,y,p} = sigma_transport_arrow(Rep_Z(x),p,id_x)
PathInd_transfd(Z) : Transfd(PathOutReflEval_funcd(Z), PathOutPi_funcd(Z)).
```

For the full current path-induction theorem status, read
`reports/REPORT_EMDASH_V3_2_SYNTHETIC_PATH_INDUCTION_CONSOLIDATED_PLAN_AND_STATUS_2026-05-31.md`.

## Current Implemented Architecture

### Pi As A Defined Alias

Current implementation:

```text
Pi_cat(E)
  := Functord_cat(Const_catd(K,Terminal_cat), E).
```

Consequences:

- `Pi_cat` is notation, not an injective kernel discriminator.
- There are no rewrite rules whose LHS is headed by `Pi_cat`.
- There is no `Obj(Pi_cat ...)` unification helper.
- Hom categories of section categories reduce through the general
  `Functord_cat` route:

  ```text
  Hom_cat(Pi_cat(E),s,t)
    = Transfd_cat(Const_catd(K,Terminal_cat),E,s,t).
  ```

This removes the old duplicate normal form:

```text
Pi_cat(E)
Functord_cat(Const_K(1),E)
```

and keeps terminal-source displayed functors as the kernel representation of
sections.

### Constant-Family Sections

Constant-family section collapse is attached to the canonical
`Functord_cat` head:

```text
Functord_cat(Const_catd(K,Terminal_cat), Const_catd(K,A))
  -> Functor_cat(K,A).
```

Therefore:

```text
Pi_cat(Const_catd(K,A))
  = Functor_cat(K,A)
```

by unfolding `Pi_cat`.

### Pi Functor Packages

`Pi_func(K)` remains a stable functor package:

```text
Pi_func(K)[E] = Pi_cat(E).
```

This is still useful even though `Pi_cat` is defined notation, because
`Pi_func` internalizes section-category formation as a functor on `Catd_cat(K)`.

The later internalized-varying-base layer is also active:

```text
Pi_int_funcd
  : (K :^n Cat^op) -> (K -> Cat) -> Cat

Pi_int_funcd[K] = Pi_func(K).
```

and:

```text
Pi_pullback_funcd(G)[x] = Pi_func(G[x]).
```

The pullback fold routes the semantic `Pi_int_funcd`/`Pullback_catd_func`
expression into the stable `Pi_pullback_funcd(G)` head.

### Section Evaluation

Section evaluation remains defined surface notation:

```text
piapp0_func(E,k) : Pi_cat(E) -> E[k]
piapp0(s,k)      = s[k].
```

The generic evaluation transfor uses canonical `Functord_cat` source spelling:

```text
pi_eval_transf(E)
  : Functord(Const_catd(K, Functord_cat(Const_K(1),E)), E)

pi_eval_transf(E)[k] = piapp0_func(E,k).
```

This avoids matching on `Pi_cat` in a place where the head is only defined
notation.

### Section Pullback

Section pullback also uses canonical source and target categories:

```text
section_pullback_func(F,E)
  : Functord_cat(B,Const_B(1),E)
    -> Functord_cat(A,Const_A(1),F^*E).
```

Object action:

```text
section_pullback_func(F,E)(s)[a] = s[F[a]].
```

The application rule is intentionally headed by `section_pullback_func` and
keeps source/target categories inferred:

```text
fapp0(section_pullback_func(F,E),s)
  -> section_pullback_sec(F,E,s).
```

The later Pi-laxity layer exposes the same operation as a naturality
component:

```text
section_pullback_transf(F)[E] = section_pullback_func(F,E).
```

For varying bases:

```text
functord_laxity_fdapp1_cell(Pi_pullback_funcd(G),p,E)
  -> section_pullback_func(G[p],E).
```

This component-level rule is now the path-induction target-transport source of
truth. The whole displayed-laxity transfor interface is deferred until the
source object can be internalized cleanly.

### Sigma Projection Pullback

The special projection pullback remains active:

```text
Sigma_proj1_pullback_catd(R,D)
  : Catd(Sigma_cat(R)).
```

Its fundamental computations are:

```text
Pullback_catd(D, Sigma_proj1_func(R))
  -> Sigma_proj1_pullback_catd(R,D)

Sigma_proj1_pullback_catd(R,D)[(k,r)]
  -> D[k].
```

The comprehension bridge is:

```text
Functord_cat(
  Sigma_cat(R),
  Const_catd(Sigma_cat(R),Terminal_cat),
  Sigma_proj1_pullback_catd(R,D))
  -> Functord_cat(R,D).
```

Equivalently:

```text
Pi_cat(Sigma_proj1_pullback_catd(R,D))
  = Functord_cat(R,D).
```

and:

```text
Hom_cat(Pi_cat(Sigma_proj1_pullback_catd(R,D)),s,t)
  = Transfd_cat(R,D,s,t).
```

This special head is preferred over broad `Pullback_catd` injectivity or
general pullback rewrite rules.

### Section Action

The retired Pi-specific internal chain is gone. The remaining section-action
surface is:

```text
piapp1_src_obj(s,f) = E[f](s[x])
piapp1_func(s,x,y)[f] = s[f]
piapp1_fapp0(s,f) = piapp1_func(s,x,y)[f].
```

Current status:

- `piapp1_src_obj` is a definition through `fib_cov_tapp0_func`.
- `piapp1_fapp0` is a definition through `piapp0(piapp1_func(...),f)`.
- `piapp1_func` remains the section-level package over the base-arrow
  category, with a constant-family computation rule.
- The old `piapp1_int_*` projection chain is not active.

This preserves user-facing section action while avoiding a separate
terminal-source internal action pipeline. Further reduction of `piapp1_func`
to a fully defined alias over generic displayed action remains optional future
cleanup.

### Raw Representables And PathOut

The plan’s raw covariant representable is implemented:

```text
Rep_catd_func(Z) = hom_int(id_Z)
Rep_Z(x)[y]      = Hom_Z(x,y).
```

This is distinct from:

```text
Edge_Z(x)[y] = Hom_Z(x,y)^op.
```

`Edge_catd_func` remains the pointwise-opposite classifier used by presheaf and
dependent-hom contravariance. Directed induction uses the raw covariant
representable.

Outgoing path categories are:

```text
PathOut_Z(x) = Sigma_cat(Rep_Z(x)).
```

with:

```text
pathout_obj(x;y,p) = (y,p)
pathout_refl_obj(x) = (x,id_x).
```

The old implementation report still described `pathout_refl_arrow` as a
constant future construction. That is now superseded. Current v3.2 defines:

```text
pathout_refl_arrow(Z,x,y,p)
  = sigma_transport_arrow(Rep_Z(x),p,id_x).
```

### Fixed-Source Directed Induction

The early directed-induction primitive remains:

```text
path_ind_sec(Z,x,E,u)
  : Pi q : PathOut_Z(x), E[q].
```

Its component computes by fibre transport over `PathOut_Z(x)`:

```text
path_ind_sec(Z,x,E,u)[(y,p)]
  = E[rho_{x,y,p}](u).
```

The projection-pullback specialization still computes to ordinary covariant
transport:

```text
path_ind_sec(
  Z,x,
  Sigma_proj1_pullback_catd(Rep_Z(x),D),
  u)
  -> fib_cov_transf(D,x,u).
```

This is now one piece of the larger fixed-source and telescope path-induction
stack:

```text
PathInd_func(Z,x)
PathInd_transfd(Z)
PathInd_funcd(Z) = Sigma_transfd_funcd(PathInd_transfd(Z)).
```

## Settled Decisions

1. `Pi_cat` is notation, not a primitive stable head.

   Do not reintroduce `Pi_cat` injectivity, `Obj(Pi_cat ...)` unification, or
   rewrite rules whose LHS is headed by `Pi_cat`.

2. `Functord_cat(Const_K(1),E)` is the canonical kernel representation of
   sections.

   Declarations and rules that need stable matching should use the canonical
   `Functord_cat` form, not `Pi_cat` in inferred family slots.

3. `Pi_func` remains a real internal package.

   A defined `Pi_cat` does not make `Pi_func`, `Pi_int_funcd`, or
   `Pi_pullback_funcd` unnecessary. These are functorial/natural packages.

4. `Sigma_proj1_pullback_catd` is the right special stable head.

   It captures a genuine comprehension rule. Avoid broad redesign of
   `Pullback_catd` unless a future theorem proves a concrete need.

5. Section action should not revive `piapp1_int_*`.

   Keep section action aligned with generic displayed action and dependent homs.
   `piapp1_*` names may remain surface/helper notation, but the retired
   terminal-specialized projection chain should stay retired.

6. Raw representables are distinct from edge/presheaf classifiers.

   Use `Rep_catd` for covariant outgoing-path transport. Use `Edge_catd_func`
   for pointwise-opposite presheaf/dependent-hom infrastructure.

7. The early directed-induction targets have been subsumed by synthetic path
   induction.

   The old future items "construct rho" and "package directed induction" are
   completed in newer form through Sigma transport and `PathInd_transfd`.

## Superseded Or Historical Items From The Old Reports

The following old items should not be carried forward as active plan text:

- Primitive/injective `Pi_cat`, direct `Pi_cat` rewrite rules, and
  `Obj(Pi_cat ...)` unification.
- The terminal-specialized `piapp1_int_*` projection chain.
- Treating `pathout_refl_arrow` as an unexplained constant. It is now Sigma
  transport.
- A broad `Pullback_catd` injective constructor or broad pullback rewrite
  surface.
- Overly broad `tapp0_fapp0` rules for path induction. The active rules keep
  the canonical unfolded base/source family shape where matching needs it.
- Temporary probe filenames and phase-by-phase migration mechanics from
  2026-05-25.

## Remaining Work

### Optional `piapp1_func` Cleanup

Decide whether `piapp1_func` should remain a stable section-action package or
become a fully defined alias over the generic displayed action path. Do this
only after focused assertions show the generic path gives the same useful
normal forms.

### Section Pullback Internalization

`section_pullback_func` remains a fixed helper:

```text
section_pullback_func(F,E).
```

A future more-internal version may be useful:

```text
section_pullback_int
```

indexed naturally over the functor argument `F`, with the pullback-family
functor built compositionally and then passed through `Pi_func`. This is not
needed for the current path-induction milestone because `section_pullback_transf`
and Pi laxity already supply the needed target transport.

### Sigma Intro Arrow Action

The arrow action of `sigma_intro_tapp0_func` remains deferred. The intended
action is:

```text
alpha : u -> v in E[k]
  |-> (id_k, alpha) in Sigma(E).
```

This should wait until the relevant identity/fibre-transport normal forms for
Sigma homs are needed by a downstream theorem.

### Internalized Constructor Audit

Continue the audit with the current rule:

```text
Internalize only constructors whose parameters genuinely vary under a binder.
```

Already active and useful:

```text
Pi_func
Pi_int_funcd
Pi_pullback_funcd
Sigma_func
Sigma_proj1_pullback_catd
Sigma_catd_functord_catd
Sigma_transfd_funcd
Rep_catd_func
PathOut_cat_func
hom_int
homd_int
fib_cov_int
```

Do not add internalized constructors merely for symmetry.

## Validation

For implementation changes touching this area:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
git diff --check
```

At the time of the old implementation report, these commands succeeded:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

This consolidated report is documentation-only. It does not require a Lambdapi
typecheck by itself.

## Retirement Checklist

After this report is accepted:

1. Keep `emdash3_2.lp` as the implementation source of truth.
2. Keep this file as the active Pi/Sigma projection-pullback status report.
3. Retire or delete:

   ```text
   reports/REPORT_EMDASH_V3_PI_ALIAS_SIGMA_PROJ1_PLAN.md
   reports/REPORT_EMDASH_V3_PI_ALIAS_SIGMA_PROJ1_IMPLEMENTATION_REPORT_2026-05-25.md
   ```

4. Do not preserve old active guidance that says `pathout_refl_arrow` remains
   a constant future construction; that has been superseded by Sigma transport.
5. Do not resurrect `piapp1_int_*` or primitive `Pi_cat` unless a future
   focused probe demonstrates a new, concrete need.
