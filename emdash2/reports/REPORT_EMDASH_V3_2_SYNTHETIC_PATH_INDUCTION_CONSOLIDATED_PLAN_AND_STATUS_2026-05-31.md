# emdash v3.2 Synthetic Path Induction Consolidated Plan And Status

Date: 2026-05-31

Status: active consolidated source for the v3.2 synthetic/telescope
path-induction milestone.

This report supersedes the two long historical files:

- `reports/REPORT_EMDASH_V3_SYNTHETIC_PATH_INDUCTION_TELESCOPE_PLAN_2026-05-27.md`
- `reports/REPORT_EMDASH_V3_SYNTHETIC_PATH_INDUCTION_TELESCOPE_IMPLEMENTATION_REPORT_2026-05-27.md`

Those files can be retired after this consolidation. The active implementation
source remains `emdash3_2.lp`; this report records the settled design, current
status, and forward plan without preserving the full chronological probe log.

## Executive Summary

The synthetic/telescope path-induction milestone is achieved in the intended
primary form:

```text
PathInd_transfd(Z)
  : Transfd(PathOutReflEval_funcd(Z), PathOutPi_funcd(Z)).
```

The surface reading is:

```text
(x :^n Z) ->
  (E :^n Catd(PathOut_Z(x))) ->
    E[(x,id_x)] -> Pi q :^f PathOut_Z(x), E[q].
```

The component normal forms are checked:

```text
PathInd_transfd(Z)[x]       = PathInd_func(Z,x)
PathInd_transfd(Z)[x][E]    = path_ind_func_fapp0(Z,x,E)
PathInd_transfd(Z)[x][E](u) = path_ind_sec(Z,x,E,u).
```

The Sigma-total theorem is no longer the primitive theorem. It is the derived
uncurried presentation:

```text
PathInd_funcd(Z)
  = Sigma_transfd_funcd(PathInd_transfd(Z)).
```

This recovers the useful compiled Sigma-total form over:

```text
Sigma x : Z, Catd(PathOut_Z(x)).
```

The fixed-source transitivity benchmark computes through both presentations:

```text
PathInd_transfd(Z)[x][CompMotive_Z(x)](id)[(y,p)][z](q)
  -> q o p

PathInd_funcd(Z)[(x,CompMotive_Z(x))](id)[(y,p)][z](q)
  -> q o p.
```

The telescoped/internal composition package supporting this benchmark is:

```text
comp_func_tele(A,x,y,z)
  : Hom_A(y,z) -> (Hom_A(x,y) -> Hom_A(x,z))

comp_func_tele(A,x,y,z)[g][f] = g o f.
```

This is the current omega-friendly composition packaging. Do not replace it
with the older v2 product-based composition package as the first move.

The canonical path-out arrow is not axiomatic:

```text
rho_{x,y,p}
  = pathout_refl_arrow(Z,x,y,p)
  = sigma_transport_arrow(Rep_Z(x), p, id_x).
```

The latest Sigma-map/laxity design is the standalone lax-prefix
precomposition normal form:

```text
Sigma(FF)(p,alpha)
  = (p,
     fapp0
       (functord_laxity_precomp_func(FF,p,u,FF[y]v))
       (functord_transport_fibre_fapp1_fapp0(FF,p,u,alpha))).
```

The older composite fibre wrapper is deleted from the active file.

## Active Sources

Read these first for current v3.2 work:

- `emdash3_2.lp`
- `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`
- this consolidated report
- `reports/EMDASH_FOUNDATIONS.md`
- `reports/REPORT_EMDASH_V3_FAITHFUL_SURFACE_SYNTAX_PLAN.md`, when editing
  comments or future surface syntax

The v2 file `emdash2.lp` remains a reference for rewrite/unification style and
older stable-head patterns. It is not the active theory target.

## Current Implemented Architecture

### Directed Families

The active implementation uses directed Cat-valued families as the canonical
normal form:

```text
Catd_cat(K) = Functor_cat(K, Cat_cat).
```

The principal directed-family infrastructure includes:

```text
Fibre_cat(E,k)                  = E[k]
Const_catd(K,A)[k]              = A
Pullback_catd(E,F)[a]           = E[F[a]]
Pi_cat(E)                       = sections of E
Sigma_cat(E)                    = total category of E
Functor_catd, Hom_catd,
Transf_catd                     = mixed-variance family constructors
```

The file keeps helper aliases routed through semantic constructors. Notation
heads such as `Fibre_cat` are not treated as globally injective semantic
constructors.

### Fixed-Source Path Induction

For `Z : Cat` and `x : Obj(Z)`:

```text
Rep_Z(x)[y]      = Hom_Z(x,y)
PathOut_Z(x)     = Sigma y : Z, Hom_Z(x,y)
pathout_obj(x;y,p) = (y,p)
reflout_x        = (x,id_x).
```

The fixed-source theorem is:

```text
path_ind_sec(Z,x,E,u)
  : Pi q : PathOut_Z(x), E[q]

u : E[reflout_x].
```

It is packaged as:

```text
PathInd_func(Z,x)
  : Functord(PathInd_src(Z,x), PathInd_tgt(Z,x)).
```

The pointwise computation is:

```text
PathInd_func(Z,x)[E][u]
  = path_ind_sec(Z,x,E,u).
```

### Moving Source Object

The motive category varies over the source object:

```text
PathOutMotives_Z[x] = Catd(PathOut_Z(x)).
```

This is implemented as:

```text
PathOutMotives_catd(Z) : Catd(Z).
```

For `p : x -> y`, the action is pullback along path-out transport:

```text
PathOut_transport_func(p) : PathOut_Z(y) -> PathOut_Z(x)
PathOut_transport_func(p)[(z,q)] = (z, q o p)
pathout_motive_transport_obj(p,E) = PathOut_transport_func(p)^* E.
```

The source and target functors of the telescope theorem are:

```text
PathOutReflEval_funcd(Z)
  : Functord(PathOutMotives_Z, Const_Z(Cat))

PathOutPi_funcd(Z)
  : Functord(PathOutMotives_Z, Const_Z(Cat)).
```

They compute componentwise as:

```text
PathOutReflEval_funcd(Z)[x][E] = E[(x,id_x)]
PathOutPi_funcd(Z)[x][E]       = Pi q : PathOut_Z(x), E[q].
```

### Primary Telescope Theorem

The primary theorem is the displayed transformation:

```text
PathInd_transfd(Z)
  : Transfd(PathOutReflEval_funcd(Z), PathOutPi_funcd(Z)).
```

This is the correct internalized-`x` theorem because the `Transfd` type carries
the naturality in the varying source object. The core milestone should not be
recast as a separate external naturality square.

The useful source and target transports induced by `p : x -> y` are:

```text
PathIndSrc_transport(p,E)
  = E[rho_{x,y,p}]

PathIndTgt_transport(p,E)
  = section_pullback(PathOut_transport_func(p), E).
```

The target transport computes through Pi laxity:

```text
fdapp1_int_cell(PathOutPi_funcd(Z),p,E)
  -> PathIndTgt_transport_func(p,E)
  -> section_pullback_func(PathOut_transport_func(p),E).
```

### Derived Sigma-Total Presentation

Generic uncurrying is:

```text
Sigma_transfd_funcd(eta)[(k,r)] = eta[k][r].
```

The path-induction Sigma-total package is now:

```text
PathInd_funcd(Z)
  = Sigma_transfd_funcd(PathInd_transfd(Z)).
```

This presentation is useful for compiled context-extension behavior over:

```text
Sigma x : Z, PathOutMotives_Z[x].
```

It should not be treated as the primitive theorem. In particular, arbitrary
non-cartesian Sigma-arrow naturality is not required for the current
path-induction milestone.

### Rho And PathOut Coherence

The canonical path-out arrow is:

```text
rho_{x,y,p}
  : (x,id_x) -> (y,p) in PathOut_Z(x).
```

It is implemented as:

```text
pathout_refl_arrow(Z,x,y,p)
  = sigma_transport_arrow(Rep_Z(x), p, id_x).
```

The endpoint computation is checked:

```text
Rep_Z(x)[p](id_x) = p.
```

The rho-section is derived through path induction on the representable motive:

```text
pathout_refl_arrow_sec(x)
  = path_ind_sec(Rep_{PathOut_Z(x)}((x,id_x)), id_{(x,id_x)})

pathout_refl_arrow_sec(x)[(y,p)] = rho_{x,y,p}.
```

Do not define `pathout_refl_arrow` itself as the component of
`pathout_refl_arrow_sec`: `path_ind_sec` already computes using
`pathout_refl_arrow`, and defining rho through the section would introduce a
recursive computation path.

The current file also checks the useful rho composition regression:

```text
PathOut_transport(p)[rho_{y,z,q}] o rho_{x,y,p}
  = rho_{x,z,q o p}.
```

This is achieved through Sigma-arrow composition and representable strictness,
not by a path-specific axiom.

## Sigma, Pi, Product, And Laxity Infrastructure

### Sigma Foundation

The fundamental Sigma hom characterization is installed:

```text
Hom_{Sigma E}((x,u),(y,v))
  = Sigma (p : Hom_K(x,y)), Hom_{E[y]}(E[p](u),v).
```

The constructor is:

```text
sigma_arrow(E,u,v,p,alpha).
```

Canonical transport is transparent:

```text
sigma_transport_arrow(E,p,u)
  = sigma_arrow(E,u,E[p](u),p,id_{E[p](u)}).
```

Sigma-arrow composition computes as:

```text
(q,beta) o (p,alpha)
  -> (q o p, beta o E[q][alpha]).
```

Sigma-map object action is:

```text
sigma_map_func(FF)[(k,u)] = (k, FF[k](u)).
```

Its current arrow action is lax-prefix, not strict-cartesian in general.

### Product Warm-Up

`Product_cat(A,B)` has been reintroduced as the non-dependent warm-up:

```text
Obj(A x B) = Obj(A) x Obj(B)
Hom_{A x B}((x,u),(y,v)) = Hom_A(x,y) x Hom_B(u,v).
```

Product-valued functors now reduce to product categories:

```text
Functor_cat X (Product_cat A B)
  -> Product_cat (Functor_cat X A) (Functor_cat X B).
```

The projection functors are the stable heads:

```text
Product_projL_func(A,B) : A x B -> A
Product_projR_func(A,B) : A x B -> B.
```

The file includes product object projections, object pairing, projection
functor computation, product-transfor decomposition, projection rules for
`tapp0_fapp0` and `tapp1_fapp0`, and ordinary curry/uncurry beta/action laws:

```text
curry(F)[x][y] = F[(x,y)]
uncurry(G)[(x,y)] = G[x][y].
```

This is still not a full Product/Functor adjunction package. The current
normal form makes product pairing silent at the category level, but
adjunction-style coherence remains deferred until a downstream theorem needs
it.

Constant-family Sigma now reduces directly:

```text
Sigma_cat(Const_catd K A) = Product_cat K A.
```

Do not reintroduce bridge functors for constant-family Sigma unless a concrete
new theorem requires them.

### Pi Laxity

The internal Pi package is:

```text
Pi_int_funcd
  : Functord(Catd_cat_func, Const_{Cat^op}(Cat)).
```

For `F : A -> B`, Pi is contravariantly natural:

```text
section_pullback_transf(F)
  : Pi_func(B) => Pi_func(A) o Pullback_catd_func(F).
```

Pi pullback/section pullback remains available as a whole ordinary transfor:

```text
section_pullback_transf(F)[E] = section_pullback_func(F,E).
```

The displayed Pi-laxity computations are currently installed at the component
level:

```text
fdapp1_int_cell(Pi_int_funcd,F,E)
  -> section_pullback_func(F,E)

fdapp1_int_cell(Pi_pullback_funcd(G),p,E)
  -> section_pullback_func(G[p],E).
```

This is the source of the path-induction target transport normal form.

### Displayed Laxity Extraction

For a displayed functor:

```text
FF : Functord(E,D)
p  : x -> y
```

there are two route functors:

```text
functord_transport_lhs_func(FF,p) = D[p] o FF[x]
functord_transport_rhs_func(FF,p) = FF[y] o E[p].
```

The active component-level laxity interface is:

```text
fdapp1_int_cell(FF,p,u)
  : D[p](FF[x](u)) -> FF[y](E[p](u)).
```

A whole-transfor laxity interface is deliberately deferred until the source
object `u` can be internalized cleanly. The intended declaration is preserved
as design guidance, but it is not a live symbol in `emdash3_2.lp`:

```text
symbol functord_laxity_transf [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  : τ (@Transf
      (Fibre_cat E x)
      (Fibre_cat D y)
      (@functord_transport_lhs_func K E D FF x y p)
      (@functord_transport_rhs_func K E D FF x y p));
```

The non-circular source of the active cell is the internal displayed hom-action:

```text
fdapp1_int_transfd(FF)
```

applied to the canonical/cartesian dependent-hom triangle. The checked
projection ladder is:

```text
fdapp1_int_transfd(FF)
  -> fdapp1_int_section_arrow(FF,x,u)
  -> fdapp1_int_tgt_arrow(FF,x,u,y)
  -> fdapp1_int_presheaf_arrow(FF,x,u,y,v)
  -> fdapp1_int_hom_func(FF,p,u,v)
  -> fdapp1_int_cell(FF,p,u).
```

The stable canonical triangle is:

```text
homd_id_canonical_triangle(E,p,u)
  : homd_(id_E,x,u,y,E[p]u)[p].
```

Only the narrow primitive identity shape:

```text
id(E[y], E[p]u)
```

folds to this head. Do not add broad identity rewrites from arbitrary identity
presentations back to `homd_id_canonical_triangle`.

### Current Sigma-Map Lax Normal Form

The active Sigma-map arrow normal form is:

```text
Sigma(FF)(p,alpha)
  = (p,
     fapp0
       (functord_laxity_precomp_func(FF,p,u,FF[y]v))
       (functord_transport_fibre_fapp1_fapp0(FF,p,u,alpha))).
```

The pieces are:

```text
functord_laxity_precomp_func(FF,p,u,w)
  : Hom_D[y](FF[y](E[p]u),w)
    -> Hom_D[y](D[p](FF[x]u),w)

functord_transport_fibre_fapp1_fapp0(FF,p,u,alpha)
  ~= FF[y][alpha].
```

The capped precomposition action is:

```text
functord_laxity_precomp_fapp0(FF,p,u,beta)
  ~= beta o laxity(FF,p)[u].
```

The canonical transport case reduces through the provenance-preserving stable
post-action head, not through a raw target identity:

```text
functord_laxity_precomp_fapp0
  (FF,p,u,
   functord_transport_fibre_fapp1_fapp0
     (FF,p,u,homd_id_canonical_triangle(E,p,u)))
  -> fdapp1_int_cell(FF,p,u).
```

The previous composite wrapper:

```text
functord_laxity_precomp_fibre_func
functord_laxity_precomp_fibre_fapp0
```

has been removed. Reintroduce it only if a concrete theorem needs a named
functor for the whole operation:

```text
alpha |-> precompose_by(laxity(FF,p)[u])[FF[y][alpha]].
```

## Settled Design Decisions

1. `PathInd_transfd` is primary.

   The path-induction theorem is a displayed transformation over the varying
   source object. Its type is the naturality package. Do not replace it with an
   external transport-square theorem.

2. `PathInd_funcd` is derived.

   The Sigma-total package is the compiled/uncurried form:

   ```text
   PathInd_funcd = Sigma_transfd_funcd(PathInd_transfd).
   ```

3. The first Sigma is essential; the second is compiled context.

   `PathOut_Z(x) = Sigma y, Hom_Z(x,y)` is the mathematical outgoing-path
   category. `Sigma x, PathOutMotives_Z[x]` is useful as a compiled telescope,
   but it should not drive the theorem design.

4. Internalization must be synthetic.

   Object-level formulas are not enough. Functor actions, displayed actions,
   components, and capped arrow actions must compute at the surfaces used by
   downstream theorems.

5. Rho is Sigma transport.

   `rho_{x,y,p}` is `sigma_transport_arrow(Rep_Z(x),p,id_x)`. The rho-section
   is derived using path induction, but rho itself should not unfold to that
   section component.

6. Laxity comes before Sigma action.

   The non-circular pipeline is:

   ```text
   internal hom-action -> extracted laxity -> Sigma action consumes laxity.
   ```

   Do not extract laxity from `Sigma(FF)` if `Sigma(FF)` already uses that
   laxity.

7. Pi target transport is a component-level laxity specialization.

   `PathIndTgt_transport` comes from
   `fdapp1_int_cell(PathOutPi_funcd,p,E)` and ultimately from Pi
   pullback/section pullback.

8. The active Sigma-map action is lax-prefix standalone precomposition.

   The current normal form exposes `functord_laxity_precomp_func` and
   `functord_transport_fibre_fapp1_fapp0`; it does not use the older composite
   fibre wrapper.

9. Capped action is not the full omega API.

   The current Sigma and path-induction computations use `fapp1_fapp0`.
   Exposing full `fapp1_func(sigma_map_func FF)` as a functor between Sigma
   hom-categories remains future work.

10. Ordinary functor/transfor laxity follows the same internal-action pattern.

    Ordinary functoriality and naturality laxity should be exposed through the
    non-displayed internal hom-action packages:

    ```text
    fapp1_int_transf(F)
    tapp1_int_fapp0_transf(eta)
    ```

    The terminal-base encoding is useful as a comparison, but it is not by
    itself the foundational source of ordinary laxity.

11. Strictness is currently partly global and partly local.

    Global strict functoriality and ordinary naturality rules still exist in
    `emdash3_2.lp`. Known strict constructors such as representable transport
    also have focused collapses. The future strict/lax split remains deferred.

## Rewrite And Normalization SOP

Keep these rules for future implementation turns:

- Probe nontrivial rewrite/unification changes in a temporary copy with a
  focused assertion.
- Prefer semantic definitions first. Add a stable head only after a focused
  probe shows a real projection, discrimination, or performance boundary.
- Keep inferred source/target categories and endpoint-family slots implicit on
  rewrite LHSs unless they are the actual discriminator.
- In assertions, prefer canonical endpoint forms such as `Hom_cat ...` and
  `Functor_cat ...` over reducible wrappers such as
  `Fibre_cat(DefinedAlias,k)` when conversion search matters.
- Do not add rules on transparent aliases such as `Sigma_catd_transport_func`
  merely because the alias is readable. Match the lower stable action head
  when a computation really must be exposed.
- Do not globally reverse `comp_cat_fapp0` or other central composition
  orientation rules to force one theorem. Prefer focused precomposition or
  postcomposition heads in the local cut-elimination direction needed by the
  theorem.
- Treat `unif_rule` as elaboration/unification guidance, not as computation.
  It should not replace a missing conversion rule.
- Preserve provenance when it is computationally useful. For example, the
  Sigma canonical case keeps:

  ```text
  functord_transport_fibre_fapp1_fapp0(FF,p,u,homd_id_canonical_triangle(...))
  ```

  instead of erasing it to a raw target identity.

## Forward Plan

### Phase 1: Keep The Consolidated Milestone Stable

Do not reopen the primary theorem shape. Future edits should preserve:

```text
PathInd_transfd primary
PathInd_funcd derived
rho via Sigma transport
target transport via Pi laxity/section pullback
Sigma-map action via standalone lax-prefix precomposition.
```

Before changing any of these surfaces, add or keep focused regressions showing
the fixed-source and Sigma-total transitivity benchmarks still compute to
`q o p`.

### Phase 2: Extend Only Concrete Missing Computations

Expose more `Sigma_transfd_funcd` action/naturality only when a downstream
theorem needs that exact surface. The old route-specific canonical transport
helper was removed for good reason: it chose one external route around a square
instead of the internal off-diagonal component.

If a theorem needs the Sigma-total transport presentation of
`Sigma_catd_functord_catd(Pi_pullback_funcd(G))`, implement it as a focused
total-action theorem tied to the stable lower action head, not as a broad rule
on the transparent `Sigma_catd_transport_func` alias.

### Phase 3: Improve Laxity Extraction Without Circularity

The component bridge from `fdapp1_int_transfd(FF)` to
`fdapp1_int_cell(FF,p,u)` is checked. A future cleanup may add a
whole-transfor laxity interface derived from the internal hom-action path, but
only after the source object `u` can be internalized without making the current
component computation misleading. Until then, the whole-transfor declaration is
documentation only, not an active interface.

### Phase 4: Add Strict Collapses Locally

Known strict/cartesian constructors should get focused collapses only when a
regression exposes a missing computation. The current representable/pathout
strict collapse is keyed on `Rep_transport_func` and should remain the model.

Do not add broad global rules saying arbitrary Sigma maps preserve canonical
transport strictly. That is false for general lax displayed functors.

### Phase 5: Defer The Strict/Lax Split

A future v2-style split remains important:

```text
StrictFunctor_cat / sfunc_func
StrictTransf_cat / stransf_transf
StrictFunctord_cat / sfuncd_funcd
```

This is not a prerequisite for the achieved path-induction milestone. It should
be a separate cleanup/generalization phase after local laxity and Sigma/Pi
computations remain stable.

### Phase 6: Defer Global Motive Families

The coherent global-section theorem:

```text
M : Obj(Pi_cat(PathOutMotives_Z))
u : Pi x, M[x][(x,id_x)]
--------------------------------
Pi x, Pi q : PathOut_Z(x), M[x][q]
```

is meaningful but not the core path-induction constructor. Keep it deferred.

### Phase 7: Defer Full Product/Functor Adjunction Coherence

The product and curry/uncurry warm-up is useful infrastructure. Full
Product/Functor adjunction coherence should be added only when required by a
specific theorem.

### Phase 8: Surface Syntax

Future surface syntax should present:

```text
PathOut_Z(x) = Sigma y : Z, Hom_Z(x,y)
E : Catd(PathOut_Z(x))
E[(y,p)] or E(y,p)
PathInd_transfd(Z)
```

as the user-facing theorem. The kernel should continue using the categorical
`Catd(PathOut_Z(x))` representation rather than introducing a separate curried
kernel motive type.

## Validation

For any implementation turn touching `emdash3_2.lp`, run:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
git diff --check
```

If a bounded check times out after adding a rule, treat it as a rewrite or
conversion regression until a focused temporary-file probe proves otherwise.

At the time of the superseded implementation report, the full validation set
was:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
git diff --check
```

This consolidated report is documentation-only. It does not itself require a
Lambdapi typecheck, but reference updates should still pass `git diff --check`.

## Retirement Checklist For The Old Reports

After this file is accepted:

1. Keep `emdash3_2.lp` as the implementation source of truth.
2. Keep `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md` for
   rewrite/debugging SOP.
3. Replace references to the two old synthetic path-induction plan/log files
   with this report.
4. Move the two old reports to an ignored historical folder or delete them only
   after confirming no active docs still point to them.
5. Do not preserve superseded intermediate names as active guidance:

   ```text
   Sigma_transfd_transport_func
   sigma_map_fibre_arrow
   functord_laxity_precomp_fibre_func
   functord_laxity_precomp_fibre_fapp0
   ```

   They were useful probes but are not current architecture.
