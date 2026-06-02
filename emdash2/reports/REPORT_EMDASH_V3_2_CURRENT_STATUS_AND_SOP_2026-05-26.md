# EMDASH v3.2 Current Status And SOP

Date: 2026-05-26

This report is the current orientation point for `emdash3_2.lp`. It consolidates
the useful implementation lessons from the older HOM/FAM/PI/CONST plan and
implementation log, plus the later Pi-alias, Sigma-projection, and internalized
path-induction work.

## Current Source Of Truth

- Active implementation: `emdash3_2.lp`.
- Current synthetic/telescope path-induction plan and implementation status:
  `reports/REPORT_EMDASH_V3_2_SYNTHETIC_PATH_INDUCTION_CONSOLIDATED_PLAN_AND_STATUS_2026-05-31.md`.
- Current Pi-alias and Sigma projection-pullback status:
  `reports/REPORT_EMDASH_V3_2_PI_ALIAS_SIGMA_PROJ1_CONSOLIDATED_STATUS_2026-05-31.md`.
- Current pair-telescope/Product-curry rearchitecture plan:
  `reports/REPORT_EMDASH_V3_2_PAIR_TELE_CURRY_REARCHITECTURE_PLAN_2026-06-01.md`.
- The older synthetic/telescope path-induction plan and implementation report
  from 2026-05-27 are superseded by that consolidated report and are no longer
  forward guidance.
- The older Pi-alias/Sigma-projection plan and implementation report from
  2026-05-25 are superseded by the Pi/Sigma consolidated status report.
- Superseded internalized-path reports remain useful as historical
  implementation records, but they are no longer the forward plan.
- This report records repository-level SOP and retirement guidance.

Retired historical references:

- The old v3.1 baseline and superseded HOM/FAM/PI/CONST plan/report have been
  moved to ignored `.scratchpad/retired/2026-05-26_v3_1_hom_fam_pi_const/`.
- Do not consult those archived files during normal v3.2 work. Recover them
  only for explicitly requested historical comparison.

## Current v3.2 Status

`emdash3_2.lp` now has:

- directed Cat-valued families via `Catd_cat K` as the canonical normal form of
  `Functor_cat K Cat_cat`;
- strict functoriality rules for ordinary functors, oriented as
  cut-elimination (`F[g] o F[f]` folds to `F[g o f]`);
- ordinary binary products with the product-valued functor normal form
  `Functor_cat X (Product_cat A B)` to
  `Product_cat (Functor_cat X A) (Functor_cat X B)`, stable projection
  functors `Product_projL_func`/`Product_projR_func`, and
  projection-oriented computation for `fapp0`, `fapp1_func`, `fapp1_fapp0`,
  `tapp0_fapp0`, and `tapp1_fapp0`;
- pair-telescope/curry prerequisite layers:
  `tapp1_at_transf`, `tapp1_func`, `Const_transf_func`, `Const_transf`,
  `Product_pair_tele_func`, `hom_postcomp_tele_func`, `hom_postcomp_func`,
  `hom_postcomp_fapp1_func`, `hom_postcomp_fapp1_fapp0`,
  `hom_precomp_fapp1_func`, `hom_precomp_fapp1_fapp0`,
  `comp_cat_cov_fapp1_func`, `comp_cat_cov_transf`,
  `comp_cat_cov_func_func_fapp1_func`, `comp_cat_cov_func_func_transf`,
  `comp_cat_cov_func_func_tapp1_func`,
  `comp_cat_cov_func_func_tapp1_fapp0`, `comp_cat_con_fapp1_func`, and
  `comp_cat_con_transf`, giving functor-level off-diagonal transfor components,
  the fixed-source transfor projection layer, constant-transfor computation,
  product pair-telescope computation, hom-owned post/precomposition action, and
  Cat-specific component computation for post/precomposition of transfors;
- semantic ordinary curry routing through the pair telescope:
  `curry_func_func` is defined through
  `comp_cat_con_func(Product_pair_tele_func)` and
  `comp_cat_cov_func_func`; `curry_func` and `curry_fapp0_func` are
  definitional projections, and the checked object beta law is
  `curry(F)[x][y] = F[(x,y)]`; its checked transfor component law is
  `curry(eta)[x][y] = eta[(x,y)]`, obtained through
  `comp_cat_cov_func_func_transf` and `comp_cat_con_transf` rather than a
  curry-only facade;
- product evaluation through right-ordered `Eval_func` and `Eval_fapp1_func`,
  fixed-object evaluation through `Eval_at_func`, and the fold
  `Eval_func o Eval_at_func(x) = fapp0_func(x)`, with `fapp0_func(x)` now also
  exposing its functor-level hom-action as `tapp0_func`;
- internalized product formation through `Product_cat_func`, with the
  fixed-right product action `G * 1_B` exposed through the stable ladder
  `Product_cat_fapp1_func` / `Product_cat_fapp1_fapp0_functord` /
  `Product_cat_fapp1_tapp0_func`;
- semantic uncurry through `uncurry_func_func` and `uncurry_func`, now defined as
  `Eval_func(B,C) o (G * 1_B)` and checked on objects and capped hom-action,
  with `G * 1_B` routed through the `Product_cat_func` stable projection ladder
  rather than through an independent `Product_mapL*` theory;
- `Pi_cat` as a section-category alias through `Functord_cat`;
- Sigma categories and `Sigma_proj1_pullback_catd` for projection pullbacks;
- the fundamental `Hom(Sigma)` characterization in the Sigma section, plus
  `sigma_arrow` as the base-arrow/fibre-arrow constructor for total arrows;
- generic base-arrow transport helpers:
  `catd_transport_func`, `functord_transport_func`,
  `functord_transport_lhs_func`, `functord_transport_rhs_func`, the canonical
  total arrow `sigma_transport_arrow` defined through `sigma_arrow`,
  `sigma_map_transport_arrow` for the action of Sigma maps on canonical total
  arrows, and `Sigma_catd_transport_func` as the transparent action of
  `Sigma_catd_functord_catd` on those canonical arrows;
- internalized `Catd_cat_func`, `Pullback_catd_func`, `Pi_int_funcd`, and
  `Pi_pullback_funcd`
  infrastructure, including the checked arrow-action fold
  `Catd_cat_func[F] == Pullback_catd_func F` and the semantic Pi-pullback fold
  `Pullback_catd_func[G][Pi_int_funcd] == Pi_pullback_funcd G`;
- fixed-`Z,x` path induction packages:
  `PathInd_src_catd`, `PathInd_tgt_catd`, and `PathInd_func`;
- outgoing-path family infrastructure:
  `PathOut_cat`, `PathOut_cat_func`, `PathOutMotives_catd`,
  `pathout_refl_obj`, `pathout_refl_eval_func`,
  `pathout_refl_eval_base_func`, `pathout_motive_transport_obj`,
  `PathOut_transport_func`, `PathIndSrc_transport_func`,
  `PathIndTgt_transport_func`, and `pathout_refl_arrow_sec`, with
  `pathout_refl_arrow` now constructed from the generic
  `sigma_transport_arrow` and `pathout_refl_arrow_sec` derived from
  `path_ind_sec` componentwise;
- primary telescope path-induction packaging:
  `PathInd_transfd : Transfd(PathOutReflEval_funcd, PathOutPi_funcd)`;
- derived Sigma-total path-induction packaging:
  `PathInd_funcd = Sigma_transfd_funcd(PathInd_transfd)`, with checked
  fibre/component rules over `Sigma_cat Z (PathOutMotives_catd Z)`, with
  `PathOutPi_funcd` restored as the semantic `Pi_int_funcd` pullback instance
  folding through `Pi_pullback_funcd`, and checked source/target transports
  defined directly as rho-evaluation and section pullback;
- the fixed-`x` directed composition benchmark:
  `path_comp_sec(x)[p][z](q) == q o p`;
- `CompTarget_catd` as the semantic `hom_con` alias over `Catd_cat Z`, not as a
  primitive stable family head.

The current full check is:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

At the time of this report it checks:

```text
emdash2.lp
emdash3_2.lp
```

The old v3.1 baseline is no longer part of the ordinary check path.

## SOP: Rewrite And Conversion Hygiene

Probe before committing nontrivial rewrite changes:

```bash
cp emdash3_2.lp tmp_rule_probe.lp
timeout 30s lambdapi check -w tmp_rule_probe.lp
```

Add a focused assertion exercising the intended normal form. A rule that
typechecks but does not prove the assertion, or times out on it, is not ready.

Keep inferred source/target arguments implicit in rule LHSs unless they are the
real discriminator. The useful discriminator is usually the explicit data head:
for example `Op_funcd`, `comp_catd_fapp0`, `homd_int`, or `tapp0_fapp0`, not
the reducible endpoint categories around it.

This matters especially when the endpoint category may be a functor category
into a product. Under the current product architecture,
`Functor_cat X (Product_cat A B)` rewrites to
`Product_cat (Functor_cat X A) (Functor_cat X B)`. A rule LHS such as
`tapp0_fapp0 (Functor_cat X Y) ... (stable_head ...)` may work for variable
`Y` but fail when `Y` is `Product_cat A B`. Prefer
`tapp0_fapp0 _ _ _ _ ... (stable_head ...)` when the stable head is the real
discriminator.

When an explicit source/target category slot is needed in an assertion or rule,
prefer canonical normal forms:

```text
Hom_cat Z x y
Functord_cat Z (Rep_catd Z y) (Rep_catd Z x)
```

over reducible readability wrappers:

```text
Fibre_cat (CompTarget_catd Z x) y
```

The wrapper may compute in isolation, but nested explicit slots can make
conversion search brittle.

Prefer semantic definitions before adding new primitive stable heads. If a
semantic definition fails to compute, first check:

- whether a corresponding capped projection rule is missing, such as
  `fapp1_fapp0 (Op_func F)` when `fapp1_func (Op_func F)` already exists;
- whether explicit arguments force a reducible or non-canonical form;
- whether a helper alias duplicates a semantic body instead of routing through
  the named semantic constructor.

Do not duplicate semantic bodies in helper aliases. If a construction has a
named semantic constructor, readable helpers should call that constructor. The
`CompTarget_catd` cleanup is the model:

```text
CompTarget_catd Z x
  := hom_con (Catd_cat Z) (Rep_catd Z x) (Op_cat Z) (Rep_catd_func Z)

CompTarget_fapp1_func p
  := fapp1_fapp0 (CompTarget_catd Z x) p
```

No separate `CompTarget_fapp1_func_func` alias is needed; full hom-action is the
ordinary `fapp1_func (CompTarget_catd Z x)`.

Do not install an independent stable-head theory for an action already owned by
an internalized functor. A helper may be useful as notation, but it should be a
definition or projection of the owning constructor's action. The product
reassessment is the model:

```text
Product_cat_func[A][B] = Product_cat A B

fapp1_func Product_cat_func A A'
  -> Product_cat_fapp1_func(A,A')

fapp1_fapp0 Product_cat_func A A' G
  -> Product_cat_fapp1_fapp0_functord(A,A',G)

G * 1_B
  := Product_cat_fapp1_tapp0_func(A,A',B,G)

G |-> G * 1_B
  := Product_mapL_func_func(A,A',B)
   = tapp0_func(B) o Product_cat_fapp1_func(A,A')
```

If a helper is retained for a projection from an internalized functor, it should
be an adjacent stable projection rung, not a raw nested chain. The product
reassessment is the model: `Product_cat_fapp1_tapp0_func` owns object and
capped-arrow computation for `G * 1_B`; `Product_mapL_func_func` remains a
defined functorial readability package; the former `Product_mapL_transf` stable
bridge has been removed.

### Readability Cleanup SOP

Readability cleanup is useful, but it should not erase the information that
Lambdapi needs for rule discrimination and subject reduction. Treat the file as
having four different surfaces:

1. **Rule LHSs.** Keep these conservative. The stable discriminator should be
   explicit, and inferred source/target arguments should remain implicit unless
   they are the discriminator. Avoid compound reducible endpoint expressions in
   implicit slots.

2. **Rule RHSs and defined-symbol bodies.** These may be cleaned by omitting
   redundant implicit arguments, but only after a probe confirms type
   preservation. Do not hide parameters that are not syntactically recoverable
   from the visible arguments. For example, `Product_cat_fapp1_tapp0_func`
   usually needs its fixed-right factor visible as
   `Product_cat_fapp1_tapp0_func A A' B G`; `G` alone does not determine `B`.

3. **Theorem-style assertions.** Prefer the mathematical formula when Lambdapi
   can infer it. For products, projectionwise assertions are often clearer and
   more robust than equality of raw `Struct_sigma` constructors:

   ```text
   sigma_Fst ((G * 1_B)[(x,y)]) = G[x]
   sigma_Snd ((G * 1_B)[(x,y)]) = y
   ```

   This avoids forcing Lambdapi to infer the dependent family argument of
   `Struct_sigma`.

4. **Diagnostic assertions.** These may remain explicit. This is especially
   appropriate for full `fapp1_func` and capped `fapp1_fapp0` assertions,
   product-valued hom-actions, and regression checks whose purpose is to expose
   canonical endpoints. In those cases compact formulas can make Lambdapi
   reconstruct endpoints through large `sigma_Fst`/`sigma_Snd` terms and fail
   with misleading conversion goals.

The Product/Eval cleanup probe is the current model. Object-level formulas such
as `Eval_func(A,B)[(F,x)] = F[x]` can be compact. Full hom-action checks such
as `fapp1_func Eval_func (F,x) (G,y)` should keep canonical source/target
categories explicit, because the assertion is a projection/regression witness,
not just a user-facing mathematical formula.

### Terminal-Source Equivalences Are Not Global Computation

Mathematically, maps out of the terminal category satisfy familiar equivalences:

```text
Functor_cat Terminal_cat A ~= A
Transf_cat
  (Const_func Terminal_cat Y u)
  (Const_func Terminal_cat Y v)
  ~= Hom_cat Y u v
```

Do not install these equivalences as broad rewrite rules by default. They are
semantic identifications, not projection rules. Making one of them definitional
creates pressure to make the whole `1 -> X` equivalence definitional, including
rules for `Functor_cat Terminal_cat A`, `Obj_func`, `Const_func`, and terminal
evaluation. That tends to hide which projection path produced a term and can
interfere with the stable-head normalization discipline.

Prefer consumer-local projection rules instead. For example, a section-action
normal form should reduce through `piapp0`, `tapp0_fapp0`, and the named
displayed-action heads that express the component being consumed. If a theorem
needs an ordinary functor view of a terminal-source section, add a focused
assertion or a deliberately named bridge after probing, rather than adding a
global `1 -> X = X` rewrite.

The old terminal-source transformation collapse

```text
Transf_cat Terminal_cat Y (Const_func Terminal_cat Y u)
  (Const_func Terminal_cat Y v)
  -> Hom_cat Y u v
```

was removed from `emdash3_2.lp` after a probe showed the current development
typechecks without it.

## SOP: Dosen Cut-Elimination Precomposition/Postcomposition Heads

When a theorem wants a composite to normalize by "absorbing a cut", choose the
normal form that exposes the reusable action, not a one-off composite hidden in
an ad hoc arrow symbol.

The basic pattern is:

```text
g o f
  -> fapp0 (precompose_by f) g

f o h
  -> fapp0 (postcompose_by f) h
```

The exact orientation depends on the theorem. The important point is that the
normal form should be the action of a stable functorial operation whenever that
operation will be reused by Sigma maps, laxity cells, naturality, or strictness
collapses.

Use this technique when all of the following hold:

- the raw mathematical formula is a composite such as
  `comp_fapp0(g,f)`;
- putting the raw composite directly in a large rewrite RHS is expensive,
  brittle, or hides useful structure;
- the composite is really the action of a reusable precomposition or
  postcomposition operation;
- the existing library helper has the wrong computational orientation for the
  current cut-elimination normal form.

For example, the Sigma-map lax-prefix action should not ultimately be hidden
behind a one-off head:

```text
sigma_map_fibre_arrow(FF,p,u,alpha)
  ~= FF[y][alpha] o laxity(FF,p)[u].
```

The first semantic decomposition is:

```text
fapp0
  (functord_laxity_precomp_func(FF,p,u,FF[y]v))
  (FF[y][alpha]).
```

The active v3.2 implementation now exposes this standalone precomposition
functor again, together with a stable transported-source fibre-action head:

```text
functord_transport_fibre_fapp1_fapp0(FF,p,u,alpha)
  ~= FF[y][alpha].
```

The current Sigma-map normal form is:

```text
Sigma(FF)(p,alpha)
  = (p,
     fapp0
       (functord_laxity_precomp_func(FF,p,u,FF[y]v))
       (functord_transport_fibre_fapp1_fapp0(FF,p,u,alpha))).
```

The older composite fibre functor surface has been deleted from the active
file. It bundled the `FF[y]` action and precomposition into one head, but the
standalone normal form above is clearer and keeps the post-action projection
visible to focused consumer rules.

The semantic raw-composite fold is not active yet:

```text
FF[y][alpha] o laxity(FF,p)[u]
  -> fapp0
       (functord_laxity_precomp_func(FF,p,u,FF[y]v))
       (functord_transport_fibre_fapp1_fapp0(FF,p,u,alpha)).
```

Endpoint-convertibility probes confirm that the middle object
`FF[y](E[p]u)` joins with `(FF[y] o E[p])(u)`. The remaining issue is rewrite
rule engineering: a direct `comp_fapp0` rule for this fold currently makes
Lambdapi's subject-reduction/critical-pair checking search through too much
composition and projection structure. The transported-source fibre-action head
now exists; any future raw-composite bridge should use an even smaller
route-object or composition-specific projection surface.

This records the same factorization while keeping the original source arrow
`alpha` visible inside the stable post-action head. The canonical identity case
now computes through:

```text
id(E[y],E[p]u)
  -> homd_id_canonical_triangle(E,p,u)
  -> functord_transport_fibre_fapp1_fapp0(FF,p,u,homd_id_canonical_triangle(E,p,u))
  -> functord_laxity_fdapp1_cell(FF,p,u).
```

The active standalone head
`functord_laxity_precomp_func(FF,p,u,w)` represents precomposition by the
displayed laxity component alone:

```text
laxity(FF,p)[u]
  : D[p](FF[x]u) -> FF[y](E[p]u).
```

So its source and target are:

```text
Hom_D[y](FF[y](E[p]u), w)
  -> Hom_D[y](D[p](FF[x]u), w).
```

Do not make such a head a transparent alias for an existing helper if that
helper computes in the opposite direction. In particular, the current
`hom_precomp_func` rule expands an application to a raw composite:

```text
fapp0 (hom_precomp_func(f)) g
  -> g o f.
```

That is useful in some contexts, but it is not the desired normal form when the
cut-elimination direction is:

```text
g o f
  -> fapp0 (precompose_by f) g.
```

In that case introduce a stable projection head for the intended normal form and
add only focused folds after probing. Possible future folds around the active
standalone precomposition head include:

```text
hom_precomp_func(laxity(FF,p)[u])
  -> functord_laxity_precomp_func(FF,p,u,w)

comp_fapp0(g,laxity(FF,p)[u])
  -> fapp0 (functord_laxity_precomp_func(FF,p,u,w)) g.
```

Do not add those folds globally by default. First check critical pairs with
identity and composition rules, and prefer consumer-local rules when the theorem
only needs one canonical case.

In particular, a functor-level fold of the form

```text
hom_precomp_func(laxity(FF,p)[u]) o FF[y]_1
  -> <a named composite fibre functor>
```

was considered but is not active yet. The first probe could not prove
preservation with the target object hidden in the composed hom-action, and the
stable-source-action variant timed out because it interacted too broadly with
strict functoriality. Revisit this only with a smaller projection surface or a
concrete downstream theorem requiring the functor-level composite itself. If
that need returns, reintroduce a fresh name deliberately rather than reviving
the deleted temporary wrapper by default.

Implementation checklist for this style:

1. Write the mathematical formula in a comment near the symbol.
2. Identify whether the desired normal form is precomposition, postcomposition,
   or another functorial action.
3. If an existing helper has the wrong orientation, add a new stable head rather
   than redefining the helper or forcing a global opposite rewrite.
4. Make large rules produce `fapp0(stable_action)(argument)` instead of a raw
   `comp_fapp0(...)`.
5. Add canonical consumer rules, such as identity/canonical-triangle cases,
   only after a temporary probe shows the syntactic normal form.
6. Keep source/target and endpoint slots implicit on rewrite LHSs unless they
   are the actual discriminator.
7. Add assertions for both the reusable action form and the downstream theorem
   normal form.
8. Record failed orientations in the implementation report when they influence
   the design.

## SOP: Identity Normal Forms

Identity terms can normalize into different specialized heads depending on the
category visible at the moment of reduction. Examples include plain `@id`,
`id_func`, `id_funcd`, and future higher identity heads, as well as
constructor-specific identities for categories such as `Cat_cat`, `Catd_cat`,
`Functor_cat`, and `Transf_cat`.

Do not assume that a rule which consumes plain `@id` will also consume all
semantically equal identity presentations. If a computation involving a
canonical/cartesian triangle fails unexpectedly, first inspect whether the
identity normalized past the primitive shape into a specialized identity head.

Prefer narrow, typed bridges over broad global identity rewrites. A good bridge
matches the semantic consumer context and only accepts the identity presentation
when the endpoints force the intended source shape. For example, the
`homd_id_canonical_triangle` bridge is restricted to the transported
dependent-hom source:

```text
id(E[y], E[p](u))
  -> homd_id_canonical_triangle(E,p,u)
```

where the rule LHS uses the primitive projection shape:

```text
@id
  (@fapp0 K Cat_cat E y)
  (fapp0 (@fapp1_fapp0 K Cat_cat E x y p) u)
```

Do not install global rewrites from all identities or all specialized identity
heads back into a local canonical-triangle head. If a specialized identity head
must be accepted, probe a consumer-local simulation/fold rule and add a focused
assertion showing the intended normal form.

## Stable Heads Policy

Stable heads are justified when later rules need a visible constructor or when a
focused probe shows that a semantic definition causes conversion blowups that
cannot be fixed by smaller projection rules or canonical endpoints.

Do not add a stable head merely because a readable alias appears in the surface
syntax. Readable aliases should normally be definitions.

Notation-only heads such as `Fibre_cat` should not receive broad injectivity or
unification helpers. `Fibre_cat E k` is notation for `fapp0 E k`; equality of
fibre categories should not generally recover the whole family and index.

## Completed Retirement

Completed on 2026-05-26:

1. This report and the current path-induction reports contain the actively
   useful SOP from the older HOM/FAM/PI/CONST plan and implementation log.
2. `scripts/check.sh`, `Makefile`, `README.md`, and `AGENTS.md` no longer put
   `emdash3_1.lp` in the ordinary check path.
3. The historical files were moved to
   `.scratchpad/retired/2026-05-26_v3_1_hom_fam_pi_const/`:

   ```text
   emdash3_1.lp
   reports/REPORT_EMDASH_V3_HOM_FAM_PI_CONST_PLAN.md
   reports/REPORT_EMDASH_V3_HOM_FAM_PI_CONST_IMPLEMENTATION_REPORT_2026-05-20.md
   ```

4. Validation after the move:

   ```bash
   EMDASH_TYPECHECK_TIMEOUT=60s make check
   ```
