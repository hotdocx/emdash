# EMDASH v3.2 Product Composition Function And Unit Prof Action Subplan

Date: 2026-07-07
Last reviewed: 2026-07-08
Plan-ID: EMDASH-V3-2-COMP-PROD-FUNC-UNIT-PROF-ACTION-2026-07-07
Depends-On: EMDASH-V3-2-PROF-CAT-PRIMITIVE-REDESIGN-2026-07-06; EMDASH-V3.2-DEFISO-HOM-ACTION-PROFCOMP-MIGRATION-2026-06-28; EMDASH-V3-2-CAT-CATD-SPECIALIZATION-ALIAS-MIGRATION-2026-07-04; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Parent-Plan: REPORT_EMDASH_V3_2_PROF_CAT_PRIMITIVE_REDESIGN_PLAN_2026-07-06.md
Supersedes: no whole report; refines the promoted `Unit_prof` action slice by replacing the residual profunctor-specific `Unit_prof_fapp1_func` stable head with a general hom-bifunctor action owner, using `comp_prod_func` as the product-composition layer underneath
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-analysis-2026-07-07
Infinity-Codex-Decision-Responses: infinity-codex:019f3811-100c-7ea0-8c38-5534271c1cde:019f3ac2-9e29-7d83-be19-be1915b79d1c
Status: active subtask; cleanup and `comp_prod_func` core have been promoted, next phase is the general `Hom_*` action-owner correction before Cat-horizontal-action migration

## Active Goal

The active goal has two layers.

The first layer, already promoted, removes the residual profunctor-specific
`Unit_prof_fapp1_func` owner by introducing a general product/uncurried
composition functor for ordinary homs. This new owner is the product-form
counterpart of the existing object-level `comp_fapp0`, and the proof-time
counterpart of the existing curried/telescope hom-action owners such as
`hom_precomp_along_tele_func` and `hom_postcomp_tele_func`.

The second layer is the correction discovered after reviewing the promoted
`fapp1_func(Unit_prof)` rule: the kernel still needs a stable general owner for
the two-endpoint arrow action of `Hom_cat` itself. The deleted
`Unit_prof_fapp1_func` was too profunctor-specific, but the underlying stable
head should reappear as a general hom-bifunctor action owner, tentatively
named `Hom_tele_func` / `Hom_func` / `Hom_fapp0`. The `comp_prod_func` and
`Product_map_func` composite should fold into this `Hom_*` owner rather than
remain the public normal form of `Unit_prof` base-arrow action.

The intended ownership boundary is:

```text
comp_fapp0        : less-internalized object-level composition
comp_prod_func    : product/uncurried functorial composition owner
Hom_*             : general two-endpoint action owner of Hom_cat
hom_*_tele_func   : curried/telescope hom-action owners
Unit_prof         : profunctor whose action should use the generic owner
```

The earlier working name `hom_uncurry_func` is now only explanatory. The
preferred kernel-facing name for the new general owner is `comp_prod_func`.
The shorter name `comp_func` remains possible, but `comp_prod_func` better
signals that the domain is a product of hom categories and avoids confusion
with the existing object-level `comp_fapp0`. The `Hom_*` names are separate:
they are not a replacement for `comp_prod_func`; they package the specific
bifunctorial action of `Hom_cat` on both endpoints.

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
- `comp_cat_cov_transf` and `comp_cat_con_transf`, current Cat-specialized
  one-slot horizontal-action heads. They presently own real
  `tapp0_fapp0`, `tapp1_func`, `tapp1_fapp0`, and identity-collapse rules,
  so deleting them requires moving those projection ladders to the
  corresponding identity-slot instances of `comp_prod_fapp1_fapp0 Cat_cat`.
- `Unit_prof_fapp1_func`, a residual profunctor-specific stable head whose
  object action is just "precompose, postcompose, then compose". The first
  promoted slice deleted this name, but the corrected plan restores the
  concept as a general `Hom_cat` action owner, not as a `Unit_prof`-specific
  owner.
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

The first slice extended this architecture by adding the missing product-form
composition owner. The next slice should add the missing `Hom_cat`-specific
two-endpoint action owner. That owner is general in the ambient category `A`
and should be used by `Unit_prof`; it should not be a representable-specific or
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
composition head for 2-cells in the hom-categories of `A`. In the Cat
instance, it should also become the public horizontal-action normal form for
ordinary transfors. The current Cat-specific helper names should not remain
upstream targets of `comp_prod_fapp1_fapp0`.

The immediate `Unit_prof` migration only needs the object action of
`comp_prod_func`. The full/capped arrow-action heads should be added only as
the stable projection ladder for the new owner, not as a reason to add a
Cat-specific rewrite immediately.

Identity and composition folds for `comp_prod_fapp1_fapp0` should be probed
as stable-head projection-ladder folds. They are not generic functoriality
restated for every constructor; they join paths where the stable capped owner
would otherwise hide the literal `fapp1_fapp0(comp_prod_func,...)` expression
from the global functoriality rules. The expected composition fold is:

```text
comp_fapp0
  (comp_prod_fapp1_fapp0 q)
  (comp_prod_fapp1_fapp0 p)
    -> comp_prod_fapp1_fapp0 (q o p)
```

where `p` and `q` are product-category arrows between the product inputs.
For explicit paired arrows, the existing product-category composition rule
reduces `q o p` componentwise.

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

Do not add a rewrite from `comp_prod_fapp1_fapp0 Cat_cat` to an old
Cat-specific helper. That direction would preserve the stale owner. The
correct Cat instance is:

```text
comp_prod_fapp1_fapp0 Cat_cat (alpha,eta)
```

where `(alpha,eta)` is the product arrow from `(F,G)` to `(K,H)` in
`Product_cat(Functor_cat X Y,Functor_cat Y Z)`.

The old Cat-specific names should be deleted after their projection ladders
are moved, or temporarily demoted to transparent compatibility aliases during
the migration:

```text
comp_cat_cov_transf(G,alpha) := comp_prod_fapp1_fapp0 Cat_cat (alpha,id_G)
comp_cat_con_transf(F,eta)   := comp_prod_fapp1_fapp0 Cat_cat (id_F,eta)

comp_cat_func_func_tapp1_fapp0(eta,alpha)
  := comp_prod_fapp1_fapp0 Cat_cat (alpha,eta)
```

The current body of `comp_cat_func_func_tapp1_fapp0` is the composite of two
one-slot actions:

```text
comp_prod_fapp1_fapp0 Cat_cat (alpha,id_H)
  o comp_prod_fapp1_fapp0 Cat_cat (id_F,eta)
```

with the endpoint order determined by the current body
`(H alpha) o (eta F)`. The new owner should fold that composite to:

```text
comp_prod_fapp1_fapp0 Cat_cat (alpha,eta)
```

This is a concrete Cat instance of the general `comp_prod_fapp1_fapp0`
composition fold above. It should be probed together with the projection
ladder migration because the old one-slot helper heads currently own the
component and off-diagonal transfor projections.

## Unit Prof Migration

After `comp_prod_func` exists, the profunctor-specific
`Unit_prof_fapp1_func` name should be deleted, but the stable owner concept
should not disappear. The corrected target is a general `Hom_cat`
two-endpoint action owner, described in the next section. The first promoted
slice temporarily routed constructed-endpoint `Unit_prof` full action directly
through the product-composition composite below; the corrected plan makes that
composite fold into the general `Hom_*` owner.

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

The intermediate product-composition presentation of the full action is:

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
generic projection path is sufficient in every active consumer. Under the
corrected plan, its RHS should become the capped `Hom_func` owner rather than
the explicit composite of one-slot pre/postcomposition functors.

### Implementation Note 2026-07-08

The first promoted slice found a useful source-presentation boundary. The
generic composite above typechecks and works as the full-action normal form
for constructed product endpoints:

```text
fapp1_func(Unit_prof X,(x,y),(x',y'))
  -> Functor_comp_pair_func(A0,A1,A2)
       o Product_map_func(preTele,postTele)
```

where:

```text
A0 = Hom_X(x,y)
A1 = Hom_X(x',y)
A2 = Hom_X(x',y')
preTele  : Hom_X(x',x) -> (A0 -> A1)
postTele : Hom_X(y,y') -> (A1 -> A2)
```

The fully opaque endpoint rule:

```text
fapp1_func(Unit_prof X,xy,xy')
```

did not promote directly. The composite term naturally has source:

```text
Product_cat
  (Hom_cat X (sigma_Fst xy') (sigma_Fst xy))
  (Hom_cat X (sigma_Snd xy)  (sigma_Snd xy'))
```

while the generic `fapp1_func` type presents the source as:

```text
Hom_cat (Product_cat (Op_cat X) X) xy xy'
```

The categories convert, and the corresponding `Functor` classifiers convert,
but Lambdapi still does not accept the whole composite as a term across this
boundary in the opaque-endpoint rewrite. A transparent alias with the old
opaque full-action type failed for the same reason. The promoted rule is
therefore the constructed-endpoint rule, and the arbitrary capped
`fapp1_fapp0(Unit_prof X,xy,xy',pq)` rule remains the join for active
consumers.

This also clarifies the `comp_prod_fapp1_func` level: the full
`fapp1_func(Unit_prof X,...)` projection is not itself literally
`comp_prod_fapp1_func`. It is the functor obtained by composing
`Product_map_func(preTele,postTele)` with `Functor_comp_pair_func`, i.e. with
`comp_prod_func Cat_cat` at object level. `comp_prod_fapp1_func` belongs one
projection later, to the arrow action of that product-composition functor on
2-cells between paired pre/postcomposition functors, and to the later
Cat-horizontal-action migration.

### Correction 2026-07-08: General Hom Action Owner

The promoted composite-based `Unit_prof` rule exposed a missing owner. The old
`Unit_prof_fapp1_func` should not return as a profunctor-specific symbol, but
the kernel does need a stable general action owner for `Hom_cat` itself. This
owner packages the action of `Hom_A(-,-)` on a pair of endpoint arrows:

```text
g : Hom_A(x',x)
f : Hom_A(y,y')
h : Hom_A(x,y)

Hom_A(g,f)(h) = f o h o g
```

Tentative kernel names:

```text
symbol Hom_tele_func [A : Cat]
  [x x' y y' : tau (Obj A)]
  : tau (Functor
      (Product_cat (Hom_cat A x' x) (Hom_cat A y y'))
      (Functor_cat (Hom_cat A x y) (Hom_cat A x' y')));

symbol Hom_func [A : Cat]
  [x x' y y' : tau (Obj A)]
  (g : tau (Hom A x' x))
  (f : tau (Hom A y y'))
  : tau (Functor
      (Hom_cat A x y)
      (Hom_cat A x' y'));

symbol Hom_fapp0 [A : Cat]
  [x x' y y' : tau (Obj A)]
  (g : tau (Hom A x' x))
  (f : tau (Hom A y y'))
  (h : tau (Hom A x y))
  : tau (Hom A x' y');
```

The exact names can still be adjusted during probing. `Hom_func` is the
shortest name and matches the user-facing intent, but it is close to the
existing classifier name `Hom`; if this reads too ambiguously in the kernel,
`Hom_action_func` / `Hom_action_fapp0` would be the conservative fallback.

The projection ladder should be:

```text
rule fapp0 (@Hom_tele_func A x x' y y') (Struct_sigma g f)
  -> @Hom_func A x x' y y' g f

rule fapp0 (@Hom_func A x x' y y' g f) h
  -> @Hom_fapp0 A x x' y y' g f h
```

Add the corresponding full/capped `fapp1_*` projections only after the
object-level and functor-level owner has stabilized. The immediate
`Unit_prof` correction needs `Hom_tele_func`, `Hom_func`, and `Hom_fapp0`;
the higher-arrow projections can be introduced as the concrete checks demand
them.

The `Unit_prof` rules should then become:

```text
rule @fapp1_func
      (Product_cat (Op_cat A) A)
      Cat_cat
      (@Unit_prof A)
      (Struct_sigma x y)
      (Struct_sigma x' y')
  -> @Hom_tele_func A x x' y y'

rule @fapp1_fapp0
      _
      Cat_cat
      (@Unit_prof A)
      xy
      xy'
      pq
  -> @Hom_func
       A
       (sigma_Fst xy)
       (sigma_Fst xy')
       (sigma_Snd xy)
       (sigma_Snd xy')
       (sigma_Fst pq)
       (sigma_Snd pq)
```

For opaque endpoints, the same source-presentation issue found in the first
slice may still appear. If so, start with constructed endpoints for
`fapp1_func(Unit_prof)` and keep the opaque capped `fapp1_fapp0(Unit_prof)`
join, exactly as the first slice did.

The composite product presentation should fold to `Hom_tele_func`. Per SOP,
the LHS should use the unfolded `Functor_comp_pair_func` body, i.e.
`@comp_prod_func Cat_cat A0 A1 A2`, rather than relying on the transparent
alias as the discriminator:

```text
@comp_cat_fapp0
  (Product_cat (Hom_cat A x' x) (Hom_cat A y y'))
  (Product_cat
    (Functor_cat A0 A1)
    (Functor_cat A1 A2))
  (Functor_cat A0 A2)
  (@comp_prod_func Cat_cat A0 A1 A2)
  (@Product_map_func
    (Hom_cat A x' x)
    (Functor_cat A0 A1)
    (Hom_cat A y y')
    (Functor_cat A1 A2)
    preTele
    postTele)
  -> @Hom_tele_func A x x' y y'
```

where:

```text
A0 = Hom_cat A x  y
A1 = Hom_cat A x' y
A2 = Hom_cat A x' y'
preTele  = hom_precomp_along_tele_func A A id_A y  x' x
postTele = hom_postcomp_tele_func       A A id_A x' y  y'
```

The capped one-slot composite should fold to `Hom_func`:

```text
post_f o pre_g
  -> Hom_func(g,f)

pre_g_at_y' o post_f
  -> Hom_func(g,f)
```

In kernel-shaped notation, the first fold is the current normal form:

```text
@comp_cat_fapp0
  (Hom_cat A x y)
  (Hom_cat A x' y)
  (Hom_cat A x' y')
  (@hom_postcomp_func A A id_A x' y y' f)
  (@hom_precomp_along_func A A id_A y x' x g)
  -> @Hom_func A x x' y y' g f
```

The second fold is the alternate order that solves the associativity problem:

```text
@comp_cat_fapp0
  (Hom_cat A x y)
  (Hom_cat A x y')
  (Hom_cat A x' y')
  (@hom_precomp_along_func A A id_A y' x' x g)
  (@hom_postcomp_func A A id_A x y y' f)
  -> @Hom_func A x x' y y' g f
```

At object level, both one-slot paths should join:

```text
hom_postcomp_fapp0(f, hom_precomp_along_fapp0(g,h))
  -> Hom_fapp0(g,f,h)

hom_precomp_along_fapp0(g, hom_postcomp_fapp0(f,h))
  -> Hom_fapp0(g,f,h)
```

Raw associativity folds may also be desirable:

```text
f o (h o g) -> Hom_fapp0(g,f,h)
(f o h) o g -> Hom_fapp0(g,f,h)
```

but those raw `comp_fapp0` folds should be treated as higher-risk
associativity joins. Probe the stable hom-action folds first. Promote raw
folds only if a concrete check needs them and a warning-enabled probe
classifies the interaction.

This correction means `comp_prod_func` remains part of the architecture, but
it is not the final public normal form for the `Unit_prof` endpoint action.
The public normal form should be the general `Hom_*` owner. This should be
implemented before continuing the planned migration of `comp_cat_cov_transf`,
`comp_cat_con_transf`, and `comp_cat_func_func_tapp1_fapp0` to
`comp_prod_fapp1_fapp0 Cat_cat` forms.

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
old comp_cat_* names are compatibility surfaces to delete or alias away.
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
the Cat instance of `comp_prod*`. The corrected target is not a reduction from
`comp_prod*` to the old Cat-specific names. The old names should be replaced
by the relevant `comp_prod_fapp1_fapp0 Cat_cat` forms:

```text
comp_cat_cov_transf(...)
  := comp_prod_fapp1_fapp0 Cat_cat (Ealpha,id_G)

comp_cat_con_transf(...)
  := comp_prod_fapp1_fapp0 Cat_cat (id_F,Ealpha)

comp_cat_func_func_tapp1_fapp0(eta,alpha)
  := comp_prod_fapp1_fapp0 Cat_cat (alpha,eta)
```

The whole-functor projections should similarly factor through
`comp_prod_fapp1_func` first:

```text
precomposition tapp1_func
  -> comp_prod_fapp1_func after pairing constant Ealpha with the varying
     second component
  -> old comp_cat_con_func_func_tapp1_func only as a temporary alias, if kept

postcomposition tapp1_func
  -> comp_prod_fapp1_func after pairing the varying first component with
     constant Ealpha
  -> old comp_cat_cov_func_func_tapp1_func only as a temporary alias, if kept
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

old comp_cat_* names, if still present
  -> transparent aliases to comp_prod* Cat_cat ...
```

The old `comp_cat_cov_transf` and `comp_cat_con_transf` heads currently own
component and off-diagonal projection ladders. Deleting them is therefore not
a textual rename: the `tapp0_fapp0`, `tapp1_func`, `tapp1_fapp0`, and
identity-collapse rules must move to the identity-slot `comp_prod_fapp1_fapp0
Cat_cat` forms. After that move, the arbitrary-pair form
`comp_prod_fapp1_fapp0 Cat_cat (alpha,eta)` is the neutral Cat horizontal
action, and the old `comp_cat_func_func_tapp1_fapp0` body should be joined by
the stable-head composition fold:

```text
comp_prod_fapp1_fapp0 Cat_cat (alpha,id_H)
  o comp_prod_fapp1_fapp0 Cat_cat (id_F,eta)
    -> comp_prod_fapp1_fapp0 Cat_cat (alpha,eta)
```

The endpoint labels matter: after the first one-slot action `(id_F,eta)`, the
second functor slot has moved from `G` to `H`, so the second one-slot action is
`(alpha,id_H)`, not `(alpha,id_G)`.

## Identity-Slot Projection Ladder Formulation

The SOP-first formulation is not to match explicit product constructors on the
rule LHS. Prefer an opaque product input and project its components on the RHS
with `sigma_Fst` / `sigma_Snd`. This keeps the product-arrow action generic,
lets authored `Product_pair` / `Struct_sigma` inputs compute into the same
owner, and avoids making constructor shape an accidental discriminator.

The following `HComp`, `CovProd`, and `ConProd` names are report-level
abbreviations only. Do not add kernel symbols with these names unless a
focused probe shows that direct `comp_prod_fapp1_fapp0` LHSs are infeasible.
`Product_pair` remains useful in examples and temporary aliases, but promoted
projection rules should first try the generic sigma-projection LHS.

Readable product notation:

```text
PairObj(A,B,x,y)
  := Product_pair x y

PairArr(A,B,x,x',y,y',alpha,beta)
  := Product_pair alpha beta
```

### Generic Arbitrary-Pair Cat Action

Use current file-style abbreviations:

```text
FG FG' : Obj(Product_cat (Functor_cat X Y) (Functor_cat Y Z))
theta  : Hom(Product_cat (Functor_cat X Y) (Functor_cat Y Z)) FG FG'

F      := sigma_Fst FG
G      := sigma_Snd FG
F'     := sigma_Fst FG'
G'     := sigma_Snd FG'
alpha  := sigma_Fst theta
eta    := sigma_Snd theta
```

The preferred Cat horizontal-action normal form is:

```text
HComp(X,Y,Z,FG,FG',theta)
  := @comp_prod_fapp1_fapp0 Cat_cat X Y Z FG FG' theta
```

The preferred generic projection ladder is:

```text
tapp0_fapp0 HComp i
  -> @tapp1_fapp0
       Y Z G G'
       (@fapp0 X Y F i)
       (@fapp0 X Y F' i)
       eta
       (@tapp0_fapp0 X Y F F' i alpha)

tapp1_func HComp i j
  -> @comp_cat_fapp0
       (Hom_cat X i j)
       (Hom_cat Y
         (@fapp0 X Y F i)
         (@fapp0 X Y F' j))
       (Hom_cat Z
         (@fapp0 Y Z G  (@fapp0 X Y F i))
         (@fapp0 Y Z G' (@fapp0 X Y F' j)))
       (@tapp1_func
         Y Z G G'
         (@fapp0 X Y F i)
         (@fapp0 X Y F' j)
         eta)
       (@tapp1_func
         X Y F F'
         i j
         alpha)

tapp1_fapp0 HComp p
  -> @tapp1_fapp0
       Y Z G G'
       (@fapp0 X Y F i)
       (@fapp0 X Y F' j)
       eta
       (@tapp1_fapp0 X Y F F' i j alpha p)
```

This formulation makes the old covariant and contravariant one-slot cases
ordinary specializations:

```text
CovProd = HComp with FG=(P,L), FG'=(Q,L), theta=(eta,id_L)
ConProd = HComp with FG=(L,R), FG'=(L,S), theta=(id_L,eta)
```

The existing generic transfor rules then recover the old one-slot component
formulas:

```text
tapp1_fapp0 id_L (eta[i])  -> L[eta[i]]
tapp1_fapp0 eta (id)       -> eta[L[i]]
tapp1_func id_L            -> fapp1_func L
```

If this arbitrary-pair ladder proves too broad or creates unmanageable
overlaps, the identity-slot rules below are the fallback shape to probe. They
are explanatory special cases, not the preferred first implementation.

### Covariant One-Slot Action

This replaces current `comp_cat_cov_transf`.

Use current file-style abbreviations:

```text
EX := @fapp0 K Cat_cat E X
EY := @fapp0 K Cat_cat E Y
L  := @fapp1_fapp0 K Cat_cat E X Y f

P Q : Functor W EX
eta : Transf P Q
```

Here `L : Functor EX EY`, so the old postcomposition-by-`L` transfor
`comp_cat_cov_transf(K,E,W,X,Y,f,P,Q,eta)` should become the identity-second
slot Cat instance:

```text
CovProd(K,E,W,X,Y,f,P,Q,eta)
  := @comp_prod_fapp1_fapp0
       Cat_cat
       W EX EY
       (@Product_pair
          (Functor_cat W EX)
          (Functor_cat EX EY)
          P L)
       (@Product_pair
          (Functor_cat W EX)
          (Functor_cat EX EY)
          Q L)
       (@Product_pair
          (Hom_cat (Functor_cat W EX) P Q)
          (Hom_cat (Functor_cat EX EY) L L)
          eta
          (@id (Functor_cat EX EY) L))
```

The old `comp_cat_cov_transf` projection ladder should move to LHSs headed by
this identity-second-slot `comp_prod_fapp1_fapp0 Cat_cat` form:

```text
tapp0_fapp0 CovProd i
  -> @fapp1_fapp0
       EX EY L
       (@fapp0 W EX P i)
       (@fapp0 W EX Q i)
       (@tapp0_fapp0 W EX P Q i eta)

tapp1_func CovProd i j
  -> @comp_cat_fapp0
       (Hom_cat W i j)
       (Hom_cat EX
         (@fapp0 W EX P i)
         (@fapp0 W EX Q j))
       (Hom_cat EY
         (@fapp0 EX EY L (@fapp0 W EX P i))
         (@fapp0 EX EY L (@fapp0 W EX Q j)))
       (@fapp1_func
         EX EY L
         (@fapp0 W EX P i)
         (@fapp0 W EX Q j))
       (@tapp1_func W EX P Q i j eta)

tapp1_fapp0 CovProd p
  -> @fapp1_fapp0
       EX EY L
       (@fapp0 W EX P i)
       (@fapp0 W EX Q j)
       (@tapp1_fapp0 W EX P Q i j eta p)
```

The identity collapse should also move:

```text
CovProd(K,E,W,X,Y,f,P,P,@id (Functor_cat W EX) P)
  -> @id
       (Functor_cat W EY)
       (@comp_cat_fapp0 W EX EY L P)
```

### Contravariant One-Slot Action

This replaces current `comp_cat_con_transf`.

Use current file-style abbreviations:

```text
EX := @fapp0 K Cat_cat E X
EY := @fapp0 K Cat_cat E Y
L  := @fapp1_fapp0 K Cat_cat E X Y F

R S : Functor EY Z
eta : Transf R S
```

Here `L : Functor EX EY`, so the old precomposition-by-`L` transfor
`comp_cat_con_transf(K,E,Z,X,Y,F,R,S,eta)` should become the identity-first
slot Cat instance:

```text
ConProd(K,E,Z,X,Y,F,R,S,eta)
  := @comp_prod_fapp1_fapp0
       Cat_cat
       EX EY Z
       (@Product_pair
          (Functor_cat EX EY)
          (Functor_cat EY Z)
          L R)
       (@Product_pair
          (Functor_cat EX EY)
          (Functor_cat EY Z)
          L S)
       (@Product_pair
          (Hom_cat (Functor_cat EX EY) L L)
          (Hom_cat (Functor_cat EY Z) R S)
          (@id (Functor_cat EX EY) L)
          eta)
```

The old `comp_cat_con_transf` projection ladder should move to LHSs headed by
this identity-first-slot `comp_prod_fapp1_fapp0 Cat_cat` form:

```text
tapp0_fapp0 ConProd i
  -> @tapp0_fapp0
       EY Z R S
       (@fapp0 EX EY L i)
       eta

tapp1_func ConProd i j
  -> @comp_cat_fapp0
       (Hom_cat EX i j)
       (Hom_cat EY
         (@fapp0 EX EY L i)
         (@fapp0 EX EY L j))
       (Hom_cat Z
         (@fapp0 EY Z R (@fapp0 EX EY L i))
         (@fapp0 EY Z S (@fapp0 EX EY L j)))
       (@tapp1_func
         EY Z R S
         (@fapp0 EX EY L i)
         (@fapp0 EX EY L j)
         eta)
       (@fapp1_func EX EY L i j)

tapp1_fapp0 ConProd p
  -> @tapp1_fapp0
       EY Z R S
       (@fapp0 EX EY L i)
       (@fapp0 EX EY L j)
       eta
       (@fapp1_fapp0 EX EY L i j p)
```

The identity collapse should also move:

```text
ConProd(K,E,Z,X,Y,F,R,R,@id (Functor_cat EY Z) R)
  -> @id
       (Functor_cat EX Z)
       (@comp_cat_fapp0 EX EY Z R L)
```

This section deliberately does not restate the entry-point rules from
`hom_postcomp_fapp1_fapp0`, `hom_precomp_along_fapp1_fapp0`, or the future
generic telescope-transfor heads. Those are covered by the surrounding
ownership plan and should be formulated against the exact checked
`comp_prod_fapp1_fapp0` term after the core owner exists. The point here is
only the one-slot projection-ladder migration:

```text
old comp_cat_cov_transf / comp_cat_con_transf projection ladders
  -> identity-slot comp_prod_fapp1_fapp0 Cat_cat projection ladders
```

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
appropriate. The one-slot Cat projection rules currently owned by
`comp_cat_cov_transf` and `comp_cat_con_transf` should move to the identity
slots of `comp_prod_fapp1_fapp0 Cat_cat`. The old Cat names should not remain
normal forms; they should be deleted or kept only as transparent aliases while
call sites migrate.

This is one linked follow-up with the deletion or demotion of
`comp_cat_func_func_tapp1_fapp0` to a compatibility alias for the arbitrary
pair Cat instance of `comp_prod_fapp1_fapp0`.

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

Updated order after the 2026-07-08 `Hom_*` correction:

1. Completed: delete the named equality-wrapper cleanup slice and update
   checks/catalog only if references exist.
2. Completed: add `comp_prod_func` with object, full-action, and capped-action
   projection heads.
3. Completed: add the transparent `Functor_comp_pair_func` Cat
   specialization.
4. Completed: add focused checks for the product owner:
   - object action of `comp_prod_func`;
   - capped action through `comp_prod_fapp1_fapp0`;
   - Cat object action as ordinary functor composition.
5. Completed as an interim slice, now corrected by the next phase: replace the
   old profunctor-specific `Unit_prof_fapp1_func` with the generic
   `Functor_comp_pair_func o Product_map_func(preTele,postTele)` full action
   for constructed endpoints, and keep the direct capped `Unit_prof` join.
6. Next active phase: introduce the general `Hom_cat` endpoint-action owner:
   - choose final names, starting from `Hom_tele_func`, `Hom_func`,
     `Hom_fapp0`;
   - add object/projection rules from `Hom_tele_func` to `Hom_func` and from
     `Hom_func` to `Hom_fapp0`;
   - add focused checks for the endpoint action on `g : x' -> x`,
     `f : y -> y'`, and `h : x -> y`;
   - probe whether constructed endpoints are sufficient or whether an opaque
     endpoint source bridge is needed.
7. In the same active phase, reorient `Unit_prof` action to the new owner:
   - `fapp1_func(Unit_prof A,(x,y),(x',y')) -> Hom_tele_func(A,x,x',y,y')`;
   - `fapp1_fapp0(Unit_prof A,xy,xy',pq) -> Hom_func(A,...)`;
   - add folds from the product-composition presentation, using unfolded
     `@comp_prod_func Cat_cat ...` instead of `Functor_comp_pair_func` on the
     LHS, to `Hom_tele_func`;
   - add capped folds from both one-slot compositions
     `post_f o pre_g` and `pre_g_at_y' o post_f` to `Hom_func`;
   - add object-level stable hom-action folds to `Hom_fapp0`, and only then
     consider raw associativity folds if concrete checks require them.
8. Add focused checks for:
   - full and capped `Unit_prof` action through `Hom_*`;
   - the product-composition presentation folding into `Hom_*`;
   - both pointwise orders `(f o h) o g` and `f o (h o g)` joining through
     `Hom_fapp0` when the corresponding folds are promoted;
   - `Hom_prof_along` action through `Prof_reindex/Product_map_func/Unit_prof`.
9. Run bounded `make check`, refresh catalog if checks changed, and run warning
   summary after the `Hom_*` correction.
10. Only after the `Hom_*` correction is stable, start the Cat-horizontal-action
    slice: move uses of `comp_cat_cov_transf` and `comp_cat_con_transf` to
    identity-slot `comp_prod_fapp1_fapp0 Cat_cat` forms, move their projection
    ladders to those forms, and delete or temporarily alias the old names.
11. In the same Cat-horizontal-action slice, demote or delete
    `comp_cat_func_func_tapp1_fapp0` by making the arbitrary pair
    `comp_prod_fapp1_fapp0 Cat_cat (alpha,eta)` the normal form and adding the
    probed composition fold that joins the old two one-slot action body.
12. Run bounded `make check`, refresh catalog/health if checks changed, and run
    warning summary before promotion.

## Side-Task Ledger

- Completed 2026-07-08: deleted the historical hom-action named equality
  wrappers listed above.
- Completed 2026-07-08: promoted `comp_prod_func`,
  `comp_prod_fapp1_func`, `comp_prod_fapp1_fapp0`, and the transparent
  `Functor_comp_pair_func` Cat specialization with focused checks.
- Completed 2026-07-08: deleted `Unit_prof_fapp1_func` from the kernel and
  routed constructed-endpoint `Unit_prof` full action through
  `Functor_comp_pair_func o Product_map_func(preTele,postTele)`.
- Correction 2026-07-08: the preceding route is now understood as an interim
  product-composition presentation, not the final public normal form. The next
  active implementation phase is to introduce a general `Hom_cat` endpoint
  action owner (`Hom_tele_func` / `Hom_func` / `Hom_fapp0`, names tentative),
  fold the product-composition presentation into it, and make `Unit_prof`
  full/capped action project to it.
- Validation 2026-07-08: `EMDASH_TYPECHECK_TIMEOUT=60s make check` passes
  after the cleanup/core migration; `make catalog` regenerates the check
  catalog without unclassified checks; `make warning-summary` reports 1,306
  warnings (1,141 unjoinable critical pairs and 165 replaceable-pattern
  warnings), still dominated by the broad `comp_fapp0`,
  `hom_postcomp_fapp0`, and `tapp0_fapp0` overlap families.
- Active follow-up in the `Hom_*` phase: investigate a generic product-hom
  source bridge only if a concrete consumer needs opaque-endpoint
  `fapp1_func(Unit_prof X,xy,xy')` to normalize directly to the same
  `Hom_tele_func` owner rather than relying on constructed endpoints and the
  arbitrary capped action join.
- Active follow-up after the initial product-owner promotion: replace
  `comp_cat_cov_transf` and `comp_cat_con_transf` by identity-slot
  `comp_prod_fapp1_fapp0 Cat_cat` forms, moving their projection ladders before
  deleting or aliasing the old names.
- Active follow-up after the initial product-owner promotion: replace
  `comp_cat_func_func_tapp1_fapp0` by the arbitrary-pair
  `comp_prod_fapp1_fapp0 Cat_cat` form and add the probed stable-head
  composition fold joining the old body.
- Deferred: possible rename `hom_int_precomp_tele_func` to
  `hom_int_precomp_along_tele_func`.
- Deferred: add unspecialized `hom_precomp_along_tele_transf` and
  `hom_postcomp_tele_transf`, move Cat-specific `tapp*` projections to those
  generic heads as generic `comp_prod*` projections, and demote
  `hom_*_cat_tele_transf` to aliases or delete them once equivalent generic
  projection ladders exist.
