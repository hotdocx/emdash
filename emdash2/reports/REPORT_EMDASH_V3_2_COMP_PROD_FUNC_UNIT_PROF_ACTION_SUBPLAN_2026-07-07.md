# EMDASH v3.2 Product Composition Function And Unit Prof Action Subplan

Date: 2026-07-07
Last reviewed: 2026-07-07
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

For the capped arrow action, the `Cat_cat` specialization should route to the
existing horizontal transfor-composite head:

```text
rule @comp_prod_fapp1_fapp0
      Cat_cat
      $A $B $C
      $FG
      $F'G'
      $alpha_eta
  -> @comp_cat_func_func_tapp1_fapp0
      $A $B $C
      (sigma_Snd $FG)
      (sigma_Snd $F'G')
      (sigma_Snd $alpha_eta)
      (sigma_Fst $FG)
      (sigma_Fst $F'G')
      (sigma_Fst $alpha_eta);
```

Here `FG` represents `(F,G)`, `F'G'` represents `(F',G')`, and `alpha_eta`
represents `(alpha,eta)`. The target is the usual horizontal composite
`(G' alpha) o (eta F)`, already packaged by
`comp_cat_func_func_tapp1_fapp0`.

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
Schematic precomposition-in-the-first-slot examples are:

```text
hom_precomp_along_tele action on alpha at g
  == comp_prod action (F[alpha], id_g)

hom_precomp_along_tele action on alpha and beta
  == comp_prod action (F[alpha], beta)
```

Postcomposition-in-the-second-slot has the dual orientation. These are
arrow-level analogues of the existing object-level bridges. They may require
extending the projection ladder beyond the current
`hom_precomp_along_tele_fapp1_fapp0` / `hom_postcomp_tele_fapp1_fapp0` level.
Do not promote broad arrow-level bridges until a concrete check requires them
and the warning-enabled interaction has been classified.

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

## Possible Follow-Up

The Cat-specialized `hom_precomp_along_cat_tele_transf` may be a temporary
specialization of a more general projection ladder for
`hom_precomp_along_tele_fapp1_fapp0`. In a later task, consider whether the
`tapp0_*` and `tapp1_*` projection rules currently attached to the Cat-specific
head should instead be available directly at the generic
`hom_precomp_along_tele_fapp1_fapp0` and
`hom_postcomp_tele_fapp1_fapp0` heads.

This is not part of the immediate `Unit_prof` migration. It is recorded only
because the arrow-level bridge story for `comp_prod_func` may eventually need
the same generalized projection ladder.

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
4. Add the Cat-specialized capped arrow-action bridge to
   `comp_cat_func_func_tapp1_fapp0`.
5. Replace `Unit_prof_fapp1_func` with the generic
   `Functor_comp_pair_func o Product_map_func(preTele,postTele)` full action.
6. Keep or reorient the direct capped `Unit_prof` action only as a projection
   join, based on focused checks.
7. Add focused checks for:
   - object action of `comp_prod_func`;
   - Cat object action as ordinary functor composition;
   - Cat capped arrow action as `comp_cat_func_func_tapp1_fapp0`;
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
- Deferred: possible unspecialization of `hom_precomp_along_cat_tele_transf`
  and related Cat-specific `tapp*` projections into generic
  `hom_*_tele_fapp1_fapp0` projection ladders.
