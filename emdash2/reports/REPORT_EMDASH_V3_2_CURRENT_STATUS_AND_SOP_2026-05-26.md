# EMDASH v3.2 Current Status And SOP

Date: 2026-05-26
Last consolidated: 2026-06-18

This report is the current orientation point for `emdash3_2.lp`. It consolidates
the useful implementation lessons from the older HOM/FAM/PI/CONST plan and
implementation log, plus the later Pi-alias, Sigma-projection,
Product/curry, internal-action, Sigma-laxity, notation, and reorganization
work.

## Current Source Of Truth

- Active implementation: `emdash3_2.lp`.
- Active diagnostic/regression checks: `emdash3_2_checks.lp`.
- Current notation authority:
  `reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`.
- Current mathematical reading guide: `reports/EMDASH_FOUNDATIONS.md`.
- Current open structural-logic implementation plan:
  `reports/REPORT_EMDASH_V3_2_FUNCTOR_STRUCTURAL_LOGIC_PRELIM_PLAN_2026-06-04.md`.
- Current open Pi-along-functor implementation plan:
  `reports/REPORT_EMDASH_V3_2_PI_ALONG_FUNCTOR_IMPLEMENTATION_PLAN_2026-06-11.md`.
- Current notation/reorganization subplan:
  `reports/REPORT_EMDASH_V3_2_NOTATION_MIGRATION_AND_REORG_IMPLEMENTATION_PLAN_2026-06-05.md`.
- v2 retirement audit:
  `reports/REPORT_EMDASH_V2_RETIREMENT_AUDIT_2026-06-16.md`.
- Reports index:
  `reports/INDEX.md`.
- MathOps/DevOps implementation plan:
  `reports/REPORT_EMDASH_MATHOPS_DEVOPS_IMPLEMENTATION_PLAN_2026-06-16.md`.

Reports retired by the 2026-06-05 consolidation have been archived under:

```text
.scratchpad/retired/2026-06-05_reports_consolidation/
```

Do not consult archived reports during normal v3.2 work. Their surviving
design facts have been folded into this report, `EMDASH_FOUNDATIONS.md`, the
canonical syntax report, or the structural-logic plan.

Retired historical references:

- The old v3.1 baseline and superseded HOM/FAM/PI/CONST plan/report have been
  moved to ignored `.scratchpad/retired/2026-05-26_v3_1_hom_fam_pi_const/`.
- The obsolete v2 baseline and consolidated v2 report have been moved to
  ignored `.scratchpad/retired/2026-06-16_v2_reference/`; use
  `REPORT_EMDASH_V2_RETIREMENT_AUDIT_2026-06-16.md` for the retained audit.
- Do not consult those archived files during normal v3.2 work. Recover them
  only for explicitly requested historical comparison.

## Current Orientation Snapshot

Review snapshot: 2026-06-05.

`emdash3_2.lp` remains the active v3.2 source. The current architecture is
centered on directed Cat-valued families, with `Catd_cat K` as the canonical
normal form of `Functor_cat K Cat_cat`, and with `Functord`/`Transfd` carrying
the displayed or natural family layers.

Top-level implementation sections now have this active order:

```text
0-2. Kernel foundations
3-7. Ordinary category calculus
8-10. Directed family calculus
11-13. Representable and dependent-hom infrastructure
14-16. Displayed hom-action and laxity extraction
17. Structural logic and bridges
18. Cat-valued profunctors
19. Applications
20. Check catalog
```

The primary path-induction theorem is `PathInd_transfd(Z)`. The Sigma-total
presentation `PathInd_funcd(Z)` is derived by
`Sigma_transfd_funcd(PathInd_transfd Z)` and should not be treated as the
primitive theorem.

`Pi_cat(E)` is a defined section-category alias through
`Functord_cat(Const_catd K Terminal_cat, E)`, not a primitive kernel
discriminator. Sigma maps now use the internal displayed-hom projection owner:
the capped fibre component is `fdapp1_int_hom_fapp0`, the fixed-endpoint
hom-action is induced by `fdapp1_int_presheaf_arrow`, and the canonical
cartesian/laxity cell is `fdapp1_int_cell`. The old
`functord_laxity_precomp_*`, `functord_transport_fibre_*`, and
`homd_id_canonical_triangle` heads are not active guidance.

Arbitrary Sigma maps do not strictly preserve canonical transport without an
additional strict/cartesian specialization. Known strict cases should get
focused collapses keyed on the specific strict constructor, as with
`Rep_transport_func`.

The Product/curry layer is partly rearchitected around semantic owners:
product-valued functors reduce to products of functor categories,
`Product_pair_tele_func` owns pairing, `curry_func_func` routes through the pair
telescope, and semantic uncurry routes through right-ordered `Eval_func` plus
the `Product_cat_func` stable projection ladder. The transfor action of
semantic uncurry remains deferred.

The first Cat-valued profunctor slice is now active. `Prof_base`, `Prof_cat`,
and `Prof` are transparent aliases for families on `A^op × B`.
`Hom_prof_along(F,G)` is the sole stable representable head, with direct fibre
computation and a full base-arrow action computing as postcomposition after
precomposition. `Hom_prof(G)` and `Unit_prof(X)` are transparent identity-left
specializations. The general `Product_map_func(F,G)` is a transparent paired
map. `Prof_reindex(R,F,G)` is a stable non-injective head whose projections
compute as pullback along `Op_func(F) × G`; representable reindexing accumulates
both endpoint functors. `Prof_transf_cat(R',F,R,G)` is the transparent category
of natural family morphisms from `R'` to `Prof_reindex(R,F,G)`.
`Prof_hom_cat(F,R,G)` specializes its source to `Unit_prof(I)`, and
`Prof_hom(F,R,G)` is its object classifier. In the representable case the
target computes to `Hom_prof_along(F,G)`. Comparison with ordinary
`Transf_cat(F,G)` and curry/internalized endpoint packages remain deferred;
the first shaped-element checks do not require them.

The first tensor/co-Yoneda calculus is also active. `Prof_tensor(R,S)` is an
opaque primitive composition of Cat-valued profunctors because the kernel has
no general coend/coinserter quotient. Reindexing a tensor distributes across
its two exposed endpoints and keeps the middle category fixed; the newly
active identity-reindex fold removes the unchanged middle reindexings.
`Prof_tensor_transf` tensors two general cells over one shared middle functor,
subsuming the old draft's separate covariant/contravariant constructors.
`Prof_tensor_hom_hom` and `Prof_tensor_hom_transf` provide shaped introduction
forms. The left and right named co-Yoneda cells are
`Prof_coyoneda_unit_tensor_con_transf` and
`Prof_coyoneda_unit_tensor_cov_transf`. Unit type collapses, associativity,
and co-Yoneda beta rules remain deferred; beta needs a general operation for
composing/applying cells across reindexed bases.

The canonical surface syntax is a presentation layer over this kernel, not a
replacement for it. The current binder convention uses one indexed binder
`:^n`; mixed variance is shown on the family occurrence, for example
`A[z^-] ⊢_[z] B[z]` for `Functor_catd A B` and
`aa[z^-] ->_[z]^R bb[z]` for `Hom_catd R aa bb`. Kernel/debug mode should
preserve stable rewrite heads such as `homd_src_func`, `tdapp0_fapp0`,
`fdapp1_int_hom_fapp0`, and `fdapp1_int_cell`.

Current validation observed during this review:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

checks `emdash3_2.lp` and `emdash3_2_checks.lp`.

### Maintenance Review 2026-06-05

The current maintenance scan found the active v3.2 source coherent against its
documentation:

- `emdash3_2.lp` contains the implementation and human-readable normal-form
  catalog; executable diagnostic assertions live in `emdash3_2_checks.lp`.
- The main file has no active `assert` commands.
- The section order in `emdash3_2.lp` matches the orientation snapshot above.
- Direct bounded checks pass for both `emdash3_2.lp` and
  `emdash3_2_checks.lp`; the full bounded `make check` path also passes.

Known incomplete or intentionally deferred items are documented rather than
left implicit:

- ordinary structural functor logic has a first implementation slice
  (`Const_func_func`, `sym_func_func`, `diag_func_func`), while displayed
  structural logic and product/curry compatibility checks remain proposed in
  `REPORT_EMDASH_V3_2_FUNCTOR_STRUCTURAL_LOGIC_PRELIM_PLAN_2026-06-04.md`;
- dependent products along arbitrary functors (`Pi_f`) remain proposed in
  `REPORT_EMDASH_V3_2_PI_ALONG_FUNCTOR_IMPLEMENTATION_PLAN_2026-06-11.md`;
- semantic uncurry transfor action is deferred pending the higher
  `Product_cat_func` action on transfors;
- the whole-transfor displayed laxity interface is deferred; current rules stop
  at component-level helpers such as `fdapp1_int_cell`;
- the arrow action of `sigma_intro_tapp0_func` is deferred until the relevant
  identity/fibre-transport normal forms for Sigma homs are clean;
- deeper definition-level file splitting remains deferred until the current
  assertion split and reorganization layout have settled.

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
  `hom_postcomp_tele_fapp1_func`, `hom_postcomp_tele_fapp1_fapp0`,
  `hom_postcomp_fapp1_func`, `hom_postcomp_fapp1_fapp0`,
  `hom_precomp_along_tele_func`, `hom_precomp_along_func`,
  `hom_precomp_along_tele_fapp1_func`,
  `hom_precomp_along_tele_fapp1_fapp0`,
  `hom_precomp_along_fapp1_func`, `hom_precomp_along_fapp1_fapp0`,
  `comp_cat_cov_fapp1_func`, `comp_cat_cov_transf`,
  `comp_cat_cov_func_func_fapp1_func`, `comp_cat_cov_func_func_transf`,
  `comp_cat_cov_func_func_tapp1_func`,
  `comp_cat_cov_func_func_tapp1_fapp0`, `comp_cat_con_func_func`,
  `comp_cat_con_func_func_fapp1_func`, `comp_cat_con_func_func_transf`,
  `comp_cat_con_fapp1_func`, and `comp_cat_con_transf`, giving
  functor-level off-diagonal transfor components,
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
- ordinary structural functor logic:
  `Const_func_func(A,B)` is a semantic alias through `const_section_func(A,B)`;
  `sym_func_func(A,B,C)` exposes exchange
  `(A ⊢ (B ⊢ C)) ⊢ (B ⊢ (A ⊢ C))`; `diag_func_func(A,C)` exposes
  contraction `(A ⊢ (A ⊢ C)) ⊢ (A ⊢ C)`. Their checked normal forms include
  `sym(H)[b][a] = H[a][b]`, `sym(H)[b][p] = H[p][b]`,
  `sym(H)[q][a] = H[a][q]`, `sym(eta)[b][a] = eta[a][b]`,
  `diag(H)[a] = H[a][a]`, `diag(H)[p] = tapp1_fapp0(H[p],p)`, and
  `diag(eta)[a] = eta[a][a]`. Product/curry compatibility and displayed
  analogues remain deferred;
- a first-class ordinary functor adjunction interface:
  `Adjunction(R,L)`, with stable projections `left_adj_func`,
  `right_adj_func`, `unit_adj_transf`, and `counit_adj_transf`, plus checked
  left and right component-level triangle cut-elimination rules. This replaces
  the draft v2 parameterized `adj` interface for v3.2; the v2
  evidence-irrelevance/projection unification rules are intentionally not
  installed unless a future focused probe shows a concrete need;
- a first Cat-valued profunctor facade:
  `Prof_base(A,B) = A^op × B`, `Prof_cat(A,B) = Catd_cat(Prof_base(A,B))`,
  and `Prof(A,B) = Obj(Prof_cat(A,B))` are transparent aliases;
  `Product_map_func(F,G)` is the semantic pair of projected composites;
  `Prof_reindex(R,F,G)` and `Prof_reindex_fapp1_func` expose object, full,
  and capped pullback action along `Op_func(F) × G`;
  `Hom_prof_along(F,G)` is the single stable representable constructor;
  `Hom_prof_along_fapp1_func` exposes its full action over product homs; and
  the checked action sends `(p,q,h)` to `G[q] o h o F[p]`.
  reindexing a representable folds to endpoint composition;
  `Hom_prof(G)` and `Unit_prof(X)` are transparent specializations;
  `Prof_transf_cat(R',F,R,G)`, `Prof_hom_cat(F,R,G)`, and
  `Prof_hom(F,R,G)` provide the transparent shaped-cell and shaped-element
  layer through `Functord_cat`; ordinary-transformation and curry comparisons
  remain deferred;
  `Prof_tensor(R,S)` is the primitive profunctor composite;
  tensor reindexing distributes across exposed endpoints;
  `Prof_tensor_transf`, `Prof_tensor_hom_hom`, and
  `Prof_tensor_hom_transf` provide the first cell/element introduction layer;
  named left/right co-Yoneda cells are active, while their beta laws await
  general equipment-cell composition/application;
- `Pi_cat` as a section-category alias through `Functord_cat`;
- Sigma categories and `Sigma_proj1_pullback_catd` for projection pullbacks;
- the fundamental `Hom(Sigma)` characterization in the Sigma section, plus
  `sigma_arrow` as the base-arrow/fibre-arrow constructor for total arrows;
- Sigma-map fibre action through the neutral internal-hom projection heads:
  `fdapp1_int_presheaf_arrow` gives the fixed-endpoint hom-action,
  `fdapp1_int_hom_func` projects at a base arrow, `fdapp1_int_hom_fapp0`
  gives the capped fibre arrow, and the transported-identity case folds to
  `fdapp1_int_cell`;
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
- derived `Catd_catd_con(K) := Catd_cat_func o Op_func(K)` classifier for
  fibrewise displayed categories over `K`, with checked fibre and pullback
  action laws;
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

The local CI gate is:

```bash
make ci
```

Use it before handoff or after broad edits. For the ordinary agentic inner
loop, prefer focused probes and `make check`; `make ci` also checks examples,
script syntax, active-reference lint, strict check-catalog freshness, and
compact source metrics.

Reviewer-facing examples can be checked with:

```bash
make examples
```

The check catalog is refreshed with:

```bash
make catalog
```

`make catalog` is intentionally non-strict during exploration: it can write a
catalog with an unclassified-check warning. `make ci` uses the strict catalog
check and fails if any diagnostic assertion is not mapped to a reviewer-facing
area.

The health/metrics report is refreshed with:

```bash
make health
```

At the time of this report it checks:

```text
emdash3_2.lp
emdash3_2_checks.lp
examples/*.lp
```

For focused probes, use:

```bash
scripts/probe.sh tmp/probes/name.lp
```

For compact failure extraction from a watcher or probe log, use:

```bash
scripts/explain_failure.py logs/typecheck.log
```

The old v3.1 baseline and obsolete v2 baseline are no longer part of the
ordinary check path.

## Before Editing `emdash3_2.lp`

Treat the file as a kernel specification, not as a surface-language document.
Mathematical comments should explain the intended categorical operation, but
rewrite rules should stay close to the stable heads that Lambdapi actually
matches.

Before proposing or implementing a nontrivial change, check these points:

1. Identify the semantic owner of the operation.

   Do not add a parallel helper if an internalized functor or transfor already
   owns the action. Prefer a projection rule or a defined alias through the
   owner. Examples: `Product_cat_func` owns product functoriality,
   `homd_int` owns dependent-hom projections, and `fdapp1_int_presheaf_arrow`
   owns the fixed-endpoint Sigma-map hom-action.

2. Decide whether the new computation needs a stable head.

   Add primitive/stable heads only when a focused probe shows a real
   discrimination or performance boundary. If the problem is only a missing
   projection, add the smaller projection instead of introducing a new semantic
   layer.

3. Keep rule left-hand sides minimal.

   Inferred source/target categories and endpoint-family slots should usually
   be `_`. Spell them out only when that slot is the actual discriminator.
   Reducible terms such as `fapp0 F x`, `comp_cat_fapp0 F G`,
   `Functor_catd ...`, `HomPresheaf_catd_func ...`, `Homd_target_catd ...`,
   or `Op_cat (Hom_cat ...)` are common causes of brittle rules.

4. Use canonical endpoint forms in assertions and symbol types.

   Prefer `Hom_cat ...` and `Functord_cat ...` when conversion search matters.
   Readability wrappers such as `Fibre_cat (DefinedAlias ...) k` are useful in
   prose but can make nested `fapp0` assertions harder for Lambdapi.

5. Preserve omega-friendly functor-level structure.

   Prefer functor-level folds over capped pointwise rewrites when the result
   must support another hom-action. A RHS that immediately computes one cell
   may lose the functor object needed for higher-dimensional iteration.

6. Do not stop at pointwise formulas for varying variables.

   A formula such as `A[x] = ...` is only the object law of a would-be
   functorial family when `x` varies in a category. Likewise, a pointwise
   formula such as `eta[x] = ...` is only the component law of a natural
   transformation until its naturality/hom-action is accounted for. Before
   turning such a sketch into a constructor, stable head, or rewrite rule,
   identify the arrow action for `p : x -> y`, for example `F[p]` for a functor
   or `eta[p]` / `tapp1_func eta` for a transfor, and any higher/family-argument
   action the surrounding API will need. Capped projections such as
   `fapp1_fapp0`/`tapp1_fapp0`, or constructor-specific action helpers, may be
   the practical probe surface, but they do not replace the full arrow-action
   obligation. If the arrow action is not yet available, document the formula as
   a pointwise sketch and do not let it masquerade as the full definition.

   Validation should keep these probes separate:

   ```text
   object law
   base-arrow action law
   transfor naturality / hom-action law, when relevant
   action on family morphisms / transfors, when relevant
   ```

   A rule that works pointwise can still have the wrong variance, endpoints,
   or performance behavior at arrow-action or naturality level.

7. Use hom-indexed family owners for functor-shaped endpoints.

   When a formula contains `Hom_A(W,F[-])`, `Hom_A(F[-],W)`, or the displayed
   analogue, prefer the classifier that takes the functor/displayed functor as
   an argument: `hom_int`, `hom_con`, or `homd_int(FF)`. Do not first encode the
   same idea as a raw `comp_cat*` pipeline unless the comparison with that raw
   pipeline is the theorem being studied. This keeps post/precomposition
   actions under a semantic owner and avoids an extra explicit cut before
   cut-elimination can fire.

8. Probe before committing rules.

   Use a temporary copy plus a focused assertion for the intended normal form.
   A rule that typechecks but fails or times out on the assertion is not ready
   for the active file.

9. Document failed orientations when they affect the design.

   If a tempting rule is rejected because it creates conversion blowups,
   circularity, or misleading ownership, record that in this SOP report or the
   relevant implementation report. Do not leave the lesson only in a local
   comment near a later symbol.

## SOP: Rewrite And Conversion Hygiene

Probe before committing nontrivial rewrite changes:

```bash
mkdir -p tmp/probes
cp emdash3_2.lp tmp/probes/rule_probe.lp
scripts/probe.sh tmp/probes/rule_probe.lp
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

### Cat-Specialized Semantic Head SOP

Cat-specialized semantic heads package extra structure exposed only when the
ambient category is `Cat_cat`.

The generic owner may already express the Cat case as an arrow in a hom
category. For example, a generic `hom_postcomp_*` or
`hom_precomp_along_*` head can specialize to `Cat_cat`. The reason to keep a
separate Cat-specialized head is that the specialized result is then known to be
a transfor, so additional projections become meaningful:

```text
tapp0_fapp0(...)
tapp1_func(...)
tapp1_fapp0(...)
```

Do not add a Cat-specialized head merely to rename a generic construction. Add
or keep it when it gives a stable projection ladder, packages Cat-only transfor
structure, or avoids long brittle Cat-specialized LHS patterns. When a generic
owner and a Cat-specialized head coexist, document the orientation and add
focused diagnostics for the overlap/join. The current model is the
postcomposition ladder:

```text
hom_postcomp_fapp1_fapp0(Cat,Cat,E,...)
  -> comp_cat_cov_transf(...)

hom_postcomp_tele_fapp1_fapp0(Cat,Cat,E,...,alpha)
  -> comp_cat_cov_func_func_transf(..., E[alpha])
```

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

### Layout And Vertical Formatting SOP

Most one-argument-per-line rule blocks are a debugging convenience, not a
Lambdapi requirement. They are useful while diagnosing hidden arity,
stable-head discriminators, and failing conversion goals, because they make the
argument spine visible. After a construction has stabilized, prefer mostly
horizontal presentation for simple rules.

Prefer compact/horizontal layout for:

- rewrite rules whose left-hand side is just a stable head plus variables;
- identity/specialization folds;
- short projection rules where the discriminator is obvious;
- short symbol declarations whose type is not a nested endpoint formula.

Keep vertical layout for:

- nested `Hom_cat`, `Functor_cat`, `Fibre_cat`, `Sigma_cat`, `Product_cat`, or
  `Functor_catd` endpoints;
- long dependent symbol types;
- rules where source/target categories are deliberately explicit;
- RHSs with nested composition or transport where indentation reflects the
  computation path;
- diagnostic assertions whose purpose is to expose canonical endpoints.

Do presentation cleanup section by section and run a bounded check after each
batch. Do not use a blind formatter: a compact rule should still reveal the
stable discriminator and should not hide endpoint data that was intentionally
left visible for conversion or review.

### Canonical Type-Shape SOP

Declared symbol types should normally be written in their reduced/canonical
form, even when the symbol itself is a primitive stable head or a defined
readability alias. Prefer:

```text
sym : τ (Functord E D)
```

over unreduced but convertible forms such as:

```text
sym : τ (@Transf K Cat_cat E D)
```

because `Transf_cat K Cat_cat E D` reduces to `Functord_cat E D`. The reduced
form is easier for both humans and Lambdapi: it avoids forcing later rules and
assertions to rely on a reducible classifier path.

Use an unreduced type only when that exact shape is intentionally needed, for
example to expose a projection route, preserve a stable diagnostic endpoint, or
probe a rewrite interaction. In that case, document the reason near the symbol
or assertion.

Do not introduce decoded `*_TYPE` heads or extra classifier heads merely to
shorten frequent binders. Such heads create a parallel semantic layer. For
example, a classifier-level head for transformations would need to join with
all existing category-level reductions:

```text
Transf_cat K Cat_cat E D -> Functord_cat E D
Transf_cat X (Product_cat A B) F G
  -> Product_cat (Transf_cat X A ...) (Transf_cat X B ...)
```

A decoded type rule alone, such as:

```text
τ (Obj (Transf_cat F G)) -> Transf_TYPE F G
```

would not replace unification rules about `Obj (Transf_cat ...)`, because those
goals do not contain `τ`. Replacing such an `Obj`-level unification rule would
require an injective classifier-level head, e.g. `Transf_grpd`, plus all
corresponding reductions and confluence checks. That is usually more theory
surface than the saved binder verbosity is worth.

Current policy: keep the semantic owner at the category/classifier level
(`Transf_cat`, `Functord_cat`, `Product_cat`, etc.), use reduced canonical
types in declarations, and keep narrow `Obj(...)` unification rules only where
they are proven useful for elaboration and rewrite stability.

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

## SOP: Dosen Cut-Elimination And Sigma/Laxity Ownership

When a theorem wants a composite to normalize by "absorbing a cut", choose the
normal form that exposes the reusable action, not a one-off composite hidden in
an ad hoc arrow symbol. The basic patterns are:

```text
g ∘ f  -> fapp0 (precompose_by f) g
f ∘ h  -> fapp0 (postcompose_by f) h
```

Use such a head only when the composite is genuinely a reusable functorial
operation and the existing helper has the wrong computational orientation for
the theorem. Otherwise prefer the already-owned semantic projection.

The current Sigma-map fibre component is owned by the internal displayed
hom-action projection ladder, not by a separate precomposition wrapper:

```text
fdapp1_int_transfd(FF)
  -> fdapp1_int_section_arrow(FF,x,u)
  -> fdapp1_int_tgt_arrow(FF,x,u,y)
  -> fdapp1_int_presheaf_arrow(FF,x,u,y,v)
  -> fdapp1_int_hom_func(FF,p,u,v)
  -> fdapp1_int_hom_fapp0(FF,p,u,alpha).
```

The mathematical reading of the final capped component is:

```text
fdapp1_int_hom_fapp0(FF,p,u,alpha)
  : D[p](FF[x]u) ->^(D[y]) FF[y]v
  morally FF[y][alpha] ∘ laxity(FF,p)[u].
```

The Sigma-map capped action is:

```text
Sigma(FF)(p,alpha)
  = (p, fdapp1_int_hom_fapp0(FF,p,u,alpha)).
```

The fixed-endpoint hom-action of `sigma_map_func` is the opposite of the
dependent Sigma map induced by `fdapp1_int_presheaf_arrow`. Do not reconstruct
it as a product functor plus an independent uncurry wrapper unless a focused
future theorem proves that such a surface is necessary.

The canonical/cartesian identity case is consumed directly by
`fdapp1_int_hom_fapp0`:

```text
fdapp1_int_hom_fapp0(FF,p,u,id_{E[p]u})
  -> fdapp1_int_cell(FF,p,u).
```

`homd_id_canonical_triangle`, `functord_laxity_precomp_func`,
`functord_laxity_precomp_fapp0`, and
`functord_transport_fibre_fapp1_fapp0` were probe-era names. They should not be
used in new plans for the active file.

Simplicial ω-iteration should be documented through the existing
`hom_int`/Sigma-hom/`homd_int`/`fdapp1_int_*` pipeline. Do not reintroduce old
v2-style simplicial stable heads merely to name triangle/surface or
cell-over-cell intuitions; add a new head only after a focused theorem proves a
real computational need.

Implementation checklist for this style:

1. Write the mathematical formula in a comment near the symbol.
2. Identify the owner of the reusable action before adding a new head.
3. Separate object laws from arrow-action laws before choosing rewrites.
4. When one endpoint varies by a functor, try the hom-indexed-family owner
   first: `hom_int(F)`, `hom_con`, or the displayed `homd_int(FF)`.
5. If an existing helper has the wrong orientation, add a new stable head only
   after proving that a smaller projection rule is insufficient.
6. Prefer `fapp0(stable_action)(argument)` over raw `comp_fapp0(...)` only when
   the stable action will be reused.
7. Add canonical consumer rules, such as identity/cartesian cases, only after a
   temporary probe shows the syntactic normal form.

### Functorial Variation SOP

Pointwise equations are often useful sketches, but in v3.2 they are not
complete definitions when an index varies in a directed category.

For a proposed family:

```text
X[x] = Formula(x)
```

also ask for:

```text
X[p] : X[x] ⊢ X[y]
```

for every base arrow:

```text
p : x -> y.
```

For a proposed natural transformation or transfor:

```text
eta[x] = ComponentFormula(x)
```

also ask for the naturality/hom-action package:

```text
eta[p]      // capped reading
tapp1_func eta x y
```

for every base arrow `p : x -> y`. In a focused assertion this may project
through `tapp1_fapp0 eta p` or a constructor-specific `*_tapp1_*` helper, but
the design obligation is still the naturality/hom-action represented by
`tapp1_func`. If this action is deferred, say so in the implementation
comment/report rather than leaving only the component equation.

For a proposed functor between family categories, also ask how the construction
acts on displayed functors and transfors if later consumers will need that
level. This prevents a pointwise normal form from becoming a misleading
stable head.

The `Pi_f` plan is the current model. The fibre formula:

```text
(Pi_f E)[b] = Pi_cat(Pullback_catd(E, CommaOut_proj(f,b)))
```

is useful but incomplete until the base-arrow action along `h : b -> b'` is
specified through `CommaOut_precomp(f,h)` and `section_pullback_func`.

### Hom-Indexed Family SOP

The category-theoretic idiom:

```text
Hom_B(b, f[-])
```

should normally enter the kernel through the internal hom-family package:

```text
hom_int B A f : Op_cat B ⊢ Catd_cat A
hom_int(f)[b][a] = Hom_B(b, f[a])
```

and not by first expanding all functor composition around the endpoint. This is
why `hom_int` carries the functor argument `f`: the action in `b` is
precomposition, the action in `a` is postcomposition by `f`, and both actions
are owned by the hom projection heads.

For the proposed `Pi_f` comma infrastructure, this means the semantic
expression:

```text
CommaOut_catd(f) ≃ Sigma_func(A) o hom_int B A f
```

is the right starting point for the internal family:

```text
b ↦ Σ (a :^n A), b ->^B f[a].
```

If a stable `CommaOut_catd(f)` head is later introduced, it should fold from
this hom-indexed-family expression after a focused probe, rather than duplicate
the object formula by hand.

The displayed analogue is the same rule:

```text
homd_int(FF)
```

should be preferred when the target endpoint varies through a displayed
functor `FF`. Expressions like:

```text
homd_int(id_D) o Op_funcd(FF)
```

are useful comparison surfaces, but they should not become the primary owner of
dependent hom-action unless a theorem specifically concerns that comparison.
6. Keep source/target and endpoint slots implicit on rewrite LHSs unless they
   are the actual discriminator.
7. Add assertions for both the reusable action form and the downstream theorem
   normal form.
8. Record failed orientations in an implementation report when they influence
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

Prefer narrow, typed consumer rules over broad global identity rewrites. In the
current Sigma/laxity path, the consumer rule is deliberately attached to
`fdapp1_int_hom_fapp0` and accepts the transported endpoint identity directly:

```text
fdapp1_int_hom_fapp0(FF,p,u,id)
  -> fdapp1_int_cell(FF,p,u).
```

Do not reinstall a global canonical-triangle identity head merely to make one
consumer compute. If a specialized identity head must be accepted, probe a
consumer-local simulation/fold rule and add a focused assertion showing the
intended normal form.

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
