# EMDASH v3.2 Product Composition Function And Unit Prof Action Subplan

Date: 2026-07-07
Last reviewed: 2026-07-08
Plan-ID: EMDASH-V3-2-COMP-PROD-FUNC-UNIT-PROF-ACTION-2026-07-07
Depends-On: EMDASH-V3-2-PROF-CAT-PRIMITIVE-REDESIGN-2026-07-06; EMDASH-V3.2-DEFISO-HOM-ACTION-PROFCOMP-MIGRATION-2026-06-28; EMDASH-V3-2-CAT-CATD-SPECIALIZATION-ALIAS-MIGRATION-2026-07-04; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Parent-Plan: REPORT_EMDASH_V3_2_PROF_CAT_PRIMITIVE_REDESIGN_PLAN_2026-07-06.md
Supersedes: no whole report; refines the promoted `Unit_prof` action slice by replacing the residual `Unit_prof_fapp1_func` stable head with a general product-composition owner
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-analysis-2026-07-07
Infinity-Codex-Decision-Responses: infinity-codex:019f3811-100c-7ea0-8c38-5534271c1cde:019f3ac2-9e29-7d83-be19-be1915b79d1c
Status: proposed active subtask for the next implementation slice

## Active Goal

The next active goal is to remove the residual `Unit_prof_fapp1_func` owner by
introducing a general product/uncurried composition functor for ordinary homs.
This new owner is the product-form counterpart of the existing object-level
`comp_fapp0`, and the proof-time counterpart of the existing curried/telescope
hom-action owners such as `hom_precomp_along_tele_func` and
`hom_postcomp_tele_func`.

The intended ownership boundary is:

```text
comp_fapp0        : less-internalized object-level composition
comp_prod_func    : product/uncurried functorial composition owner
hom_*_tele_func   : curried/telescope hom-action owners
Unit_prof         : profunctor whose action should use the generic owner
```

The earlier working name `hom_uncurry_func` is now only explanatory. The
preferred kernel-facing name for the new general owner is `comp_prod_func`.
The shorter name `comp_func` remains possible, but `comp_prod_func` better
signals that the domain is a product of hom categories and avoids confusion
with the existing object-level `comp_fapp0`.

## Source Review

The current source has:

- `comp_fapp0`, the core object-level composition operation.
- `hom_precomp_along_tele_func`, the curried/telescope precomposition owner
  with an extra functor argument.
- `hom_postcomp_tele_func`, the dual curried/telescope postcomposition owner.
- `hom_int_precomp_tele_func`, already the internalized represented-object
  action that was being sketched under the possible future name
  `hom_int_precomp_along_tele_func`.
- `comp_cat_func_func_tapp1_fapp0`, the Cat-specialized horizontal composite
  of ordinary transfors.
- `Unit_prof_fapp1_func`, a residual profunctor-specific stable head whose
  object action is just "precompose, postcompose, then compose".
- Cat-specialized telescope-transfor heads
  `hom_precomp_along_cat_tele_transf` and
  `hom_postcomp_cat_tele_transf`, whose `tapp*` projection rules are better
  understood as future generic projection rules on unspecialized
  `hom_*_tele_transf` heads.

The existing object-level proof-time bridges already identify the stable
hom-action object actions with ordinary `comp_fapp0` readings:

```text
hom_precomp_along_fapp0(F,h,g) == comp_fapp0(g,F[h])
hom_postcomp_fapp0(F,h,g)      == comp_fapp0(F[h],g)
```

The next slice should extend this architecture by adding the missing
product-form composition owner, not by adding a representable-specific or
Cat-specific owner.

## Core Owner

Proposed general owner:

```text
symbol comp_prod_func [A : Cat]
  [W X Z : tau (Obj A)]
  : tau (Functor
      (Product_cat (Hom_cat A W X) (Hom_cat A X Z))
      (Hom_cat A W Z));
```

Object action:

```text
rule fapp0 (@comp_prod_func $A $W $X $Z) $pg
  -> @comp_fapp0 $A $W $X $Z (sigma_Snd $pg) (sigma_Fst $pg);
```

This object rule is a runtime projection from the product-level owner to the
existing object-level composition primitive. It does not replace the existing
proof-time bridges between `hom_*_fapp0` and `comp_fapp0`; those bridges remain
the compatibility layer between the curried/telescope hom-action owners and
ordinary composition readings.

## Arrow Action

The new product owner must also expose full and capped arrow actions. The
minimum projection ladder should be:

```text
symbol comp_prod_fapp1_func [A : Cat]
  [W X Z : tau (Obj A)]
  [pg pg' : tau (Obj
    (Product_cat (Hom_cat A W X) (Hom_cat A X Z)))]
  : tau (Functor
      (Hom_cat
        (Product_cat (Hom_cat A W X) (Hom_cat A X Z))
        pg
        pg')
      (Hom_cat
        (Hom_cat A W Z)
        (@comp_fapp0 A W X Z (sigma_Snd pg) (sigma_Fst pg))
        (@comp_fapp0 A W X Z (sigma_Snd pg') (sigma_Fst pg'))));

symbol comp_prod_fapp1_fapp0 [A : Cat] ...
  : tau (Hom
      (Hom_cat A W Z)
      (@comp_fapp0 A W X Z (sigma_Snd pg) (sigma_Fst pg))
      (@comp_fapp0 A W X Z (sigma_Snd pg') (sigma_Fst pg')));

rule @fapp1_func _ _ (@comp_prod_func $A $W $X $Z) $pg $pg'
  -> @comp_prod_fapp1_func $A $W $X $Z $pg $pg';

rule fapp0 (@comp_prod_fapp1_func $A $W $X $Z $pg $pg') $alpha
  -> @comp_prod_fapp1_fapp0 $A $W $X $Z $pg $pg' $alpha;

rule @fapp1_fapp0 _ _ (@comp_prod_func $A $W $X $Z) $pg $pg' $alpha
  -> @comp_prod_fapp1_fapp0 $A $W $X $Z $pg $pg' $alpha;
```

For arbitrary `A`, `comp_prod_fapp1_fapp0` is the neutral generic horizontal
composition head for 2-cells in the hom-categories of `A`. Do not attempt to
force the Cat-specialized transfor helper into this general layer.

The immediate `Unit_prof` migration only needs the object action of
`comp_prod_func`. The full/capped arrow-action heads should be added only as
the stable projection ladder for the new owner, not as a reason to add a
Cat-specific rewrite immediately.

Identity and composition folds for `comp_prod_fapp1_fapp0` should be probed
only if a concrete projection check or consumer needs them. If added, they
must follow the stable-head projection-ladder exception in the SOP: they join
owner-first and projection-first paths and must not become a second statement
of generic functoriality.

## Cat Specialization

The ordinary functor-composition-pair view should be transparent:

```text
symbol Functor_comp_pair_func [A B C : Cat]
  : tau (Functor
      (Product_cat (Functor_cat A B) (Functor_cat B C))
      (Functor_cat A C))
≔ @comp_prod_func Cat_cat A B C;
```

Its object action computes to ordinary functor composition because
`Hom_cat Cat_cat A B` computes to `Functor_cat A B`.

Do not add a default rewrite from `comp_prod_fapp1_fapp0 Cat_cat` to the
existing Cat-specific horizontal composite head in the immediate `Unit_prof`
slice. The correct longer-term owner is still `comp_prod_fapp1_fapp0`; the
warning is only that the Cat-specialized reductions should be probed as a
separate telescope-transfor/action slice because they overlap with identity
specializations.

The deferred target is:

```text
comp_cat_func_func_tapp1_fapp0(eta,alpha)
  := comp_prod_fapp1_fapp0 Cat_cat (alpha,eta)
```

where `(alpha,eta)` is the product arrow from `(F,G)` to `(K,H)`. Whether the
current body of `comp_cat_func_func_tapp1_fapp0` is judgmentally recovered from
the Cat instance of `comp_prod_fapp1_fapp0` depends on later Cat-specific
projection rules for `comp_prod_fapp1_fapp0`; this is a follow-up probe, not
part of the immediate `Unit_prof` migration.

## Unit Prof Migration

After `comp_prod_func` exists, `Unit_prof_fapp1_func` should be deleted.

For `xy xy' : Obj(Product_cat(Op_cat X) X)`, define:

```text
A0 = Hom_cat X (sigma_Fst xy)  (sigma_Snd xy)
A1 = Hom_cat X (sigma_Fst xy') (sigma_Snd xy)
A2 = Hom_cat X (sigma_Fst xy') (sigma_Snd xy')

preTele =
  hom_precomp_along_tele_func X X id_X
    (sigma_Snd xy)
    (sigma_Fst xy')
    (sigma_Fst xy)

postTele =
  hom_postcomp_tele_func X X id_X
    (sigma_Fst xy')
    (sigma_Snd xy)
    (sigma_Snd xy')
```

Then the full action of `Unit_prof` should be the composite:

```text
Functor_comp_pair_func A0 A1 A2
  o Product_map_func preTele postTele
```

Equivalently, it is `comp_prod_func Cat_cat A0 A1 A2` after pairing the
precomposition and postcomposition functors. Applying this to a product arrow
`(p,q)` should compute to the current capped normal form:

```text
hom_postcomp_func(id_X,q) o hom_precomp_along_func(id_X,p)
```

The direct capped `@fapp1_fapp0 _ Cat_cat (@Unit_prof X)` rule should remain
as a join for the full-action projection path unless a focused probe shows the
generic projection path is sufficient in every active consumer. Its RHS should
be either the existing capped normal form or the corresponding `fapp0` of the
new composite, whichever gives the cleaner stable normal form after probing.

## Bridge Policy

The product owner is the uncurried/product counterpart of `comp_fapp0`.
The curried/telescope hom-action owners remain the runtime owners for their
own projection ladders.

At object level, the existing proof-time bridge pattern should be preserved
with the current pre/post orientation:

```text
hom_precomp_along_fapp0(F,h,g) == comp_fapp0(g,F[h])
hom_postcomp_fapp0(F,h,g)      == comp_fapp0(F[h],g)
```

The new product owner adds the product-form expression:

```text
fapp0(comp_prod_func)(h,g) -> comp_fapp0(g,h)
```

Additional proof-time bridges may be useful, but should be narrow and probed.
The generic telescope-transfor projection rules should eventually have this
shape. For precomposition, with
`theta = hom_precomp_along_tele_transf(F,alpha)` and
`Falpha = F[alpha]`:

```text
tapp0_fapp0 theta g
  -> comp_prod_fapp1_fapp0 (Falpha,id_g)

tapp1_func theta g g'
  -> functor obtained by pairing constant Falpha with the varying second
     component, then applying comp_prod_fapp1_func

tapp1_fapp0 theta beta
  -> comp_prod_fapp1_fapp0 (Falpha,beta)
```

For postcomposition, with
`theta = hom_postcomp_tele_transf(F,alpha)` and `Falpha = F[alpha]`:

```text
tapp0_fapp0 theta u
  -> comp_prod_fapp1_fapp0 (id_u,Falpha)

tapp1_func theta u u'
  -> functor obtained by pairing the varying first component with constant
     Falpha, then applying comp_prod_fapp1_func

tapp1_fapp0 theta beta
  -> comp_prod_fapp1_fapp0 (beta,Falpha)
```

These are arrow-level analogues of the existing object-level bridges. They
require generic `hom_precomp_along_tele_transf` and
`hom_postcomp_tele_transf` heads, described below. Do not promote broad
arrow-level bridges until a concrete check requires them and the
warning-enabled interaction has been classified.

## Clarified Cat-Specialization Ownership

The agreed longer-term factorization is:

```text
hom_*_tele_transf owns generic telescope projection.
comp_prod* owns product-composition arrow action.
comp_cat_* owns Cat_cat-specialized transfor normal forms.
```

In particular, Cat-specific computation should move away from the
`hom_precomp_along_cat_tele_transf` and `hom_postcomp_cat_tele_transf` heads.
Those heads currently exist because the generic telescope-transfor projection
ladder is missing. Once the unspecialized heads exist, their projections
should be generic and should target `comp_prod*` first.

For precomposition, with
`theta = hom_precomp_along_tele_transf(F,alpha)` and
`Falpha = F[alpha]`, the generic projection rules should have the schematic
shape:

```text
tapp0_fapp0 theta g
  -> comp_prod_fapp1_fapp0 (Falpha,id_g)

tapp1_func theta g g'
  -> comp_prod_fapp1_func after pairing constant Falpha with the varying
     second component

tapp1_fapp0 theta beta
  -> comp_prod_fapp1_fapp0 (Falpha,beta)
```

For postcomposition, with
`theta = hom_postcomp_tele_transf(F,alpha)` and `Falpha = F[alpha]`, the
orientation is dual:

```text
tapp0_fapp0 theta u
  -> comp_prod_fapp1_fapp0 (id_u,Falpha)

tapp1_func theta u u'
  -> comp_prod_fapp1_func after pairing the varying first component with
     constant Falpha

tapp1_fapp0 theta beta
  -> comp_prod_fapp1_fapp0 (beta,Falpha)
```

After those generic rules, the Cat-specific computation belongs downstream at
the Cat instance of `comp_prod*`. The intended Cat reductions are schematic:

```text
comp_prod_fapp1_fapp0 Cat_cat (Ealpha,id_G)
  -> comp_cat_cov_transf ...

comp_prod_fapp1_fapp0 Cat_cat (id_F,Ealpha)
  -> comp_cat_con_transf ...

comp_prod_fapp1_fapp0 Cat_cat (alpha,eta)
  -> comp_cat_func_func_tapp1_fapp0 eta alpha
```

The whole-functor projections should similarly factor through
`comp_prod_fapp1_func` first:

```text
precomposition tapp1_func
  -> comp_prod_fapp1_func after pairing constant Ealpha with the varying
     second component
  -> comp_cat_con_func_func_tapp1_func ...   // Cat_cat specialization

postcomposition tapp1_func
  -> comp_prod_fapp1_func after pairing the varying first component with
     constant Ealpha
  -> comp_cat_cov_func_func_tapp1_func ...   // Cat_cat specialization
```

This means the old direct rules of the form:

```text
tapp*_projection (hom_*_cat_tele_transf ...)
  -> comp_cat_* ...
```

should eventually be replaced by two steps:

```text
tapp*_projection (hom_*_tele_transf ...)
  -> comp_prod* ...

comp_prod* Cat_cat ...
  -> comp_cat_* ...
```

The broad arbitrary-pair Cat rule and the focused identity-slot Cat rules
overlap. For example, `(alpha,id)` can match both the arbitrary
`comp_cat_func_func_tapp1_fapp0` route and the focused `comp_cat_cov_transf`
route. This does not invalidate the architecture, but it makes the
implementation a separate probe-first task. The eventual orientation must make
the identity-slot cases either reduce directly to the existing covariant or
contravariant transfor normal forms, or join cleanly through the arbitrary
horizontal-composite head.

## Non-Goals

Do not add kernel symbols such as:

```text
hom_precomp_along_uncurry_func
hom_postcomp_along_uncurry_func
```

The extra-functor-argument variants belong to the curried/telescope layer,
where the functor can be pre-supplied before the inner action is applied. The
product/uncurried kernel owner should be the no-extra-functor composition
owner `comp_prod_func`.

The `hom_int_precomp_tele_func` question is closed for this slice. The current
symbol already represents the internalized represented-object action that was
being considered under the possible future name
`hom_int_precomp_along_tele_func`. A future rename can be considered as a
separate naming cleanup.

## Deferred Telescope-Transfor Unspecialization

The current Cat-specific heads should be understood as temporary compatibility
surfaces:

```text
hom_precomp_along_cat_tele_transf
hom_postcomp_cat_tele_transf
```

The correct long-term owners are unspecialized heads:

```text
hom_precomp_along_tele_transf
  : Transf
      (hom_precomp_along_func F Z h)
      (hom_precomp_along_func F Z k)

hom_postcomp_tele_transf
  : Transf
      (hom_postcomp_func F W f)
      (hom_postcomp_func F W g)
```

These generic transfor heads are meaningful because
`hom_precomp_along_tele_fapp1_fapp0` and
`hom_postcomp_tele_fapp1_fapp0` already land in a hom of a `Functor_cat`, and
`Hom_cat(Functor_cat D E,F,G)` computes to `Transf_cat F G`. Therefore
`tapp0_fapp0`, `tapp1_func`, and `tapp1_fapp0` projections are not inherently
Cat-specific.

After the generic heads exist, the current Cat-specific names should become
aliases or compatibility views:

```text
hom_precomp_along_cat_tele_transf
  := hom_precomp_along_tele_transf ... Cat_cat ...

hom_postcomp_cat_tele_transf
  := hom_postcomp_tele_transf Cat_cat ...
```

The existing `tapp0_fapp0`, `tapp1_func`, and `tapp1_fapp0` rules currently
attached to the Cat-specific heads should then move to the generic heads and
be expressed through `comp_prod_fapp1_func` / `comp_prod_fapp1_fapp0` where
appropriate. The Cat-specific normal forms that the old rules currently
return should not remain attached to the generic `hom_*_tele_transf` heads;
they should be reattached downstream as Cat-instance reductions of
`comp_prod_fapp1_func` / `comp_prod_fapp1_fapp0`. This is one linked follow-up
with the future demotion of `comp_cat_func_func_tapp1_fapp0` to a Cat-specific
view of `comp_prod_fapp1_fapp0`.

This unspecialization is not part of the immediate `Unit_prof` migration. It
is recorded because it is the coherent future owner of the arrow-level bridge
story for `comp_prod_func`.

## Cleanup Slice

Delete these historical named equality wrappers:

```text
hom_postcomp_func_id_eq
hom_postcomp_fapp0_id_eq
hom_postcomp_func_comp_eq
hom_postcomp_func_comp_fold_eq
hom_postcomp_fapp0_comp_eq
hom_postcomp_fapp0_comp_fold_eq
hom_postcomp_fapp0_source_accumulation_eq

hom_precomp_along_func_id_eq
hom_precomp_along_fapp0_id_eq
hom_precomp_along_func_comp_eq
hom_precomp_along_func_comp_fold_eq
hom_precomp_along_fapp0_comp_eq
hom_precomp_along_fapp0_comp_fold_eq
```

Keep the runtime rewrite rules and proof-time unification rules. Only the
historical proof-symbol wrappers are cleanup targets.

## Implementation Order

1. Delete the named equality-wrapper cleanup slice and update checks/catalog
   only if references exist.
2. Add `comp_prod_func` with object, full-action, and capped-action projection
   heads.
3. Add the transparent `Functor_comp_pair_func` Cat specialization.
4. Do not add Cat-specific `comp_prod*` reductions in the immediate slice;
   record them as the deferred owner for the later telescope-transfor
   unspecialization.
5. Replace `Unit_prof_fapp1_func` with the generic
   `Functor_comp_pair_func o Product_map_func(preTele,postTele)` full action.
6. Keep or reorient the direct capped `Unit_prof` action only as a projection
   join, based on focused checks.
7. Add focused checks for:
   - object action of `comp_prod_func`;
   - Cat object action as ordinary functor composition;
   - full and capped `Unit_prof` action;
   - `Hom_prof_along` action through `Prof_reindex/Product_map_func/Unit_prof`.
8. Run bounded `make check`, refresh catalog/health if checks changed, and run
   warning summary before promotion.

## Side-Task Ledger

- Active: implement `comp_prod_func` and migrate `Unit_prof` action away from
  `Unit_prof_fapp1_func`.
- Active cleanup: delete historical hom-action named equality wrappers listed
  above.
- Deferred: possible rename `hom_int_precomp_tele_func` to
  `hom_int_precomp_along_tele_func`.
- Deferred: add unspecialized `hom_precomp_along_tele_transf` and
  `hom_postcomp_tele_transf`, move Cat-specific `tapp*` projections to those
  generic heads as generic `comp_prod*` projections, move the Cat-specific
  normal forms downstream to Cat-instance `comp_prod*` reductions, and demote
  `hom_*_cat_tele_transf` to aliases or delete them.
- Deferred: recast `comp_cat_func_func_tapp1_fapp0` as the Cat instance of
  `comp_prod_fapp1_fapp0`, after probing whether its current body is
  judgmentally recovered from the generic owner plus Cat projections.
