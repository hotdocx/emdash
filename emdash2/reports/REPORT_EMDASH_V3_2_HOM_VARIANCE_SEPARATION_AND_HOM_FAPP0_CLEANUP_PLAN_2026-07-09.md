# EMDASH v3.2 Hom Variance Separation And Hom_fapp0 Cleanup Plan

Date: 2026-07-09
Last reviewed: 2026-07-09
Plan-ID: EMDASH-V3-2-HOM-VARIANCE-SEPARATION-HOM-FAPP0-2026-07-09
Depends-On: EMDASH-V3-2-COMP-PROD-FUNC-UNIT-PROF-ACTION-2026-07-07; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Parent-Plan: REPORT_EMDASH_V3_2_COMP_PROD_FUNC_UNIT_PROF_ACTION_SUBPLAN_2026-07-07.md
Supersedes: no whole report; extracts and expands the deferred `Hom_fapp0` object-action cleanup from the parent subplan
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: infinity-codex:019f3811-100c-7ea0-8c38-5534271c1cde:019f48a6-337d-78a1-8135-c6b85220f69e
Infinity-Codex-Decision-Responses: infinity-codex:019f3811-100c-7ea0-8c38-5534271c1cde:019f48a6-337d-78a1-8135-c6b85220f69e; infinity-codex:019f3811-100c-7ea0-8c38-5534271c1cde:019f4964-f896-74c0-85dc-062f1d01cff7; infinity-codex:019f3811-100c-7ea0-8c38-5534271c1cde:019f49b8-33d5-7e72-8128-dcbf40a9d7d4
Status: completed and closed; Phases 0-7 promoted and validated

## Active Goal

Complete the deferred object-level action of the general `Hom_cat`
two-endpoint owner:

```text
Hom_fapp0(g,f,h) = f o h o g.
```

The final runtime folds should identify both one-slot evaluation orders with
the same stable two-endpoint owner:

```text
hom_postcomp_fapp0(f, hom_precomp_along_fapp0(g,h))
  -> Hom_fapp0(g,f,h)

hom_precomp_along_fapp0(g, hom_postcomp_fapp0(f,h))
  -> Hom_fapp0(g,f,h).
```

This is not treated as an isolated pair of rewrite rules. The current kernel
first rewrites identity-functor precomposition into postcomposition, erasing
the contravariant head before either fold can become the normal form. The
active design goal is therefore a staged variance-separation migration:

```text
primitive covariant owner        hom_ / hom_postcomp_*
primitive contravariant owner    hom_con / hom_precomp_along_*
source-internalized owner        hom_int / hom_int_precomp_*
target-internalized owner        hom_con_int / hom_con_int_postcomp_*
two-endpoint owner               Hom_tele_func / Hom_func / Hom_fapp0
uncurried hom bifunctor          Unit_prof

runtime                         preserves the variance owner
proof time                      relates dual/opposite presentations
```

The architecture is settled enough to begin phased probe-first execution. The
remaining proof-time bridge inventory, inferred-slot spelling, and downstream
consumer classification are implementation-phase discoveries with explicit
gates below; they do not require reopening the owner hierarchy before Phase 0
and Phase 1 begin.

## Parent-Plan Status

The parent product-composition and `Unit_prof` action subplan is otherwise
promoted and validated. It has completed:

- `comp_prod_func`, `comp_prod_fapp1_func`, and
  `comp_prod_fapp1_fapp0`;
- `Hom_tele_func`, `Hom_func`, and `Hom_fapp0`;
- `Unit_prof` action through the general `Hom_*` owner;
- deletion of the old Cat covariant/contravariant compatibility heads;
- generic telescope-transfor owners and arbitrary-ambient off-diagonal
  projections through the `comp_prod*` owners.

The deferred `Hom_fapp0` object-action cleanup is the primary remaining item
from that subplan. This report is now the dedicated design authority for that
item.

## Current Obstruction

The immediate obstructing rule is:

```text
rule @hom_precomp_along_fapp0
      $A $A (@id Cat_cat $A) $Z $W $X $h $g
  -> @hom_postcomp_fapp0
       $A $A (@id Cat_cat $A) $W $X $Z $g $h;
```

It currently makes identity-functor postcomposition the runtime presentation
of ordinary precomposition. Consequently:

```text
post_f(pre_g(h))
```

reduces its inner `pre_g(h)` to a postcomposition head before the intended
two-slot fold can fire, while:

```text
pre_g(post_f(h))
```

can reduce its outer precomposition head before the second fold can fire.
The earlier object-fold probes therefore failed because of a competing
normal-form decision, not because the proposed `Hom_fapp0` equations were
ill-typed or mathematically false.

The same architectural shortcut appears more broadly in the runtime ladder
which rewrites opposite-specialized postcomposition to precomposition when
the functor argument has head `Op_func`:

```text
hom_postcomp_tele_func(Op_func F)          -> hom_precomp_along_tele_func(F)
hom_postcomp_func(Op_func F)               -> hom_precomp_along_func(F)
hom_postcomp_fapp0(Op_func F)              -> hom_precomp_along_fapp0(F)
hom_postcomp_fapp1_func(Op_func F)         -> hom_precomp_along_fapp1_func(F)
hom_postcomp_fapp1_fapp0(Op_func F)        -> hom_precomp_along_fapp1_fapp0(F)
hom_postcomp_tele_fapp1_func(Op_func F)    -> hom_precomp_along_tele_fapp1_func(F)
hom_postcomp_tele_fapp1_fapp0(Op_func F)   -> hom_precomp_along_tele_fapp1_fapp0(F)
hom_postcomp_tele_transf(Op_func F)        -> hom_precomp_along_tele_transf(F).
```

Those rules make a reducible semantic presentation, `Op_func`, a runtime
variance discriminator. This is the larger ownership issue exposed by the
local `Hom_fapp0` failure.

## Mathematical Assessment

For a category `A`, endpoint arrows

```text
g : Hom_A(x',x)
f : Hom_A(y,y')
```

act on a middle arrow

```text
h : Hom_A(x,y)
```

by:

```text
Hom_A(g,f)(h) = f o h o g : Hom_A(x',y').
```

The two proposed folds are the two factorizations of this bifunctorial
action:

```text
f_*(g^*(h)) = Hom_A(g,f)(h)
g^*(f_*(h)) = Hom_A(g,f)(h).
```

They are therefore semantically justified runtime folds into the stable
two-endpoint owner. They are not merely proof-time equalities between two
arbitrary semantic presentations: the public computational intent is that the
combined two-slot cut normalizes to `Hom_fapp0`.

By contrast, the equivalence between a covariant hom action over opposite
categories and a contravariant hom action is semantic duality. It should not
choose one variance as the other's runtime normal form. In the intended
Došen-style reading, antecedential/contravariant and
consequential/covariant operations remain distinct syntax during
normalization even though they are related mathematically through opposite
categories.

## Selected Design Direction

Ordinary mathematical exposition usually suppresses this mirror
infrastructure by defining one variance through opposites. That semantic
shortcut is appropriate for concise statements but is not automatically an
appropriate computational normal form. Rewrite discrimination on reducible
`Op_cat` / `Op_func` presentations makes cut ownership depend on which
semantic wrapper normalized first.

This plan therefore selects explicit mirrored runtime infrastructure as the
preferred design direction:

```text
covariant syntax       contravariant syntax
hom_                    hom_con
hom_postcomp_*          hom_precomp_along_*
hom_int                 hom_con_int
hom_int_precomp_*       hom_con_int_postcomp_*
```

The duplication is intentional proof-theoretic syntax, not a claim that the
two sides are mathematically unrelated. Their semantic duality belongs in
narrow proof-time unification rules and comparison checks.

A radically different implementation remains admissible only if it provides
all of the same computational guarantees without this explicit mirror:

- stable antecedential and consequential heads which survive normalization;
- no runtime discrimination on reducible opposite wrappers;
- complete component and off-diagonal projection ladders;
- a unique combined normal form through `Hom_func` / `Hom_fapp0`;
- bounded, joinable rewrite behavior in the active consumers.

No such alternative is currently identified. Consequently, semantic brevity
alone is not a reason to keep the current mixed architecture.

## Current Source Architecture

The source already contains most of the required separation:

- `hom_` is the represented covariant family
  `y |-> Hom_A(W,F[y])` and projects to `hom_postcomp_*`;
- `hom_precomp_along_tele_func`, `hom_precomp_along_func`,
  `hom_precomp_along_fapp0`, and their higher-action heads are already
  primitive contravariant runtime owners;
- `hom_int : Op_cat A -> Catd_cat B` is already a primitive mixed internal-hom
  package, and `hom_int_precomp_tele_func` /
  `hom_int_precomp_func` expose its contravariant endpoint action;
- `Hom_tele_func`, `Hom_func`, and `Hom_fapp0` now own simultaneous movement
  of both endpoints.

The source is incomplete at two linked levels:

- `hom_int_precomp_func` currently exposes only its point component through
  `tapp0_fapp0`; it has no dedicated `tapp1_func` / `tapp1_fapp0` projection
  rules exposing simultaneous movement in the represented endpoint and in the
  base of `F`;
- the mirror internalized owner `hom_con_int`, which varies the fixed target
  covariantly and returns a contravariant represented family, does not yet
  exist.

A third incomplete boundary is upstream `hom_con`:

```text
hom_con(W,F)
  := hom_(Op_cat A, Op_cat B, Op_func F, W).
```

Although its public name is contravariant, its implementation is still a
semantic alias through opposites. Its arrow action reaches precomposition only
after generic `hom_` postcomposition and the `Op_func`-keyed runtime bridge.
The kernel therefore has separate downstream pre/post heads without yet
having a fully separate upstream represented-family owner.

## Proposed Ownership Boundary

### Covariant represented family

Keep:

```text
hom_(F,W) : B -> Cat
hom_(F,W)[y] = Hom_A(W,F[y]).
```

Its runtime arrow action remains owned by the `hom_postcomp_*` hierarchy.

### Contravariant represented family

Promote `hom_con` from an opposite-based semantic alias to an injective
primitive owner with its current public type:

```text
injective symbol hom_con [A : Cat]
  (W : tau (Obj A))
  [B : Cat]
  (F : tau (Functor B A))
  : tau (Functor (Op_cat B) Cat_cat);
```

Its direct object projection should remain computational:

```text
rule @fapp0 (Op_cat $B) Cat_cat (@hom_con $A $W $B $F) $x
  -> Hom_cat $A (@fapp0 $B $A $F $x) $W;
```

The explicit category slots above are schematic. The promoted rule must apply
the inferred-slot SOP after a focused probe.

The capped projection routes directly to the existing precomposition owner,
without matching an `Op_func` subterm. The promoted full projection retains
one source-presentation owner because its literal domain is
`Hom_cat(Op_cat B,X,Y)`:

```text
fapp1_func(hom_con(W,F),X,Y)
  -> hom_con_precomp_tele_func(F,W,X,Y)

fapp0(hom_con_precomp_tele_func(F,W,X,Y),h)
  -> hom_precomp_along_func(F,W,Y,X,h)

fapp1_fapp0(hom_con(W,F),X,Y,h)
  -> hom_precomp_along_func(F,W,Y,X,h).
```

The endpoint reversal `Y,X` accounts for
`Hom_(Op B)(X,Y) = Hom_B(Y,X)`. The Phase 2 probe showed that a homogeneous
whole-functor assertion cannot directly elaborate the existing
`hom_precomp_along_tele_func` presentation even though the raw rewrite passes
subject reduction. The minimal `hom_con_precomp_tele_func` owner preserves the
literal opposite source category; its object and direct capped projections
immediately reuse `hom_precomp_along_func`, so it does not duplicate the lower
precomposition ladder.

### Paired internal-hom owners

The two internalized owners are distinct curryings of the same hom bifunctor.
They should be treated symmetrically:

| Layer | Source endpoint internalized | Target endpoint internalized |
|---|---|---|
| Fixed family | `hom_(F,W) : B -> Cat` | `hom_con(W,F) : Op(B) -> Cat` |
| Internalized family | `hom_int(F) : Op(A) -> Catd(B)` | `hom_con_int(F) : A -> Catd(Op(B))` |
| Endpoint action | `hom_int_precomp_*` | `hom_con_int_postcomp_*` |
| Off-diagonal result | `Hom_func(p,F[q])` | `Hom_func(F[q],f)` |

#### Source endpoint internalized

Retain:

```text
hom_int(F) : Op_cat A -> Catd_cat B
hom_int(F)[W][y] = Hom_A(W,F[y]).
```

Its existing arrow-action owners are:

```text
hom_int_precomp_tele_func(F)
hom_int_precomp_func(F,p).
```

The component rule already computes as expected:

```text
tapp0_fapp0(hom_int_precomp_func(F,p),b)
  -> hom_precomp_along_func(id_A,F[b],p).
```

The missing off-diagonal ladder should express the simultaneous source and
target action. For:

```text
p : Hom_A(X,Y)
q : Hom_B(b,c)
h : Hom_A(Y,F[b]),
```

the resulting action is:

```text
h |-> F[q] o h o p.
```

Therefore the capped off-diagonal projection should be approximately:

```text
tapp1_fapp0(hom_int_precomp_func(F,p),q)
  -> Hom_func(p,F[q]).
```

This projection returns `Hom_func`, not `Hom_fapp0`: its result is a functor
between hom-categories. Applying that functor to `h` then reaches the point
owner through the existing projection:

```text
fapp0(Hom_func(p,F[q]),h)
  -> Hom_fapp0(p,F[q],h).
```

The full `tapp1_func` projection must internalize the varying `q`:

```text
q |-> Hom_func(p,F[q]).
```

This design is now settled at the current projection level: its runtime RHS
should be the semantic composite through `Hom_tele_func`, with no new named
`hom_int_precomp_tapp1_func` intermediary. Let:

```text
Fb = fapp0(F,b)
Fc = fapp0(F,c).
```

Then the mathematical composite is:

```text
Hom_B(b,c)
  -- q |-> (p,F[q]) -->
Product(Hom_A(X,Y),Hom_A(Fb,Fc))
  -- Hom_tele_func(A,Y,X,Fb,Fc) -->
Functor(Hom_A(Y,Fb),Hom_A(X,Fc)).
```

A kernel-shaped RHS is approximately:

```text
@comp_fapp0
  Cat_cat
  (Hom_cat B b c)
  (Product_cat
    (Hom_cat A X Y)
    (Hom_cat A Fb Fc))
  (Functor_cat
    (Hom_cat A Y Fb)
    (Hom_cat A X Fc))
  (@Hom_tele_func A Y X Fb Fc)
  (Struct_sigma
    (@Const_func
      (Hom_cat B b c)
      (Hom_cat A X Y)
      p)
    (@fapp1_func B A F b c)).
```

The exact promoted spelling must still apply inferred-slot hygiene, but no
missing general constructor is apparent: `Const_func` supplies the fixed
component, `Struct_sigma` is the canonical product-valued-functor encoding,
`fapp1_func(F,b,c)` supplies the varying component, and generic
`comp_fapp0 Cat_cat` composes with `Hom_tele_func`.

The direct capped rule remains necessary as a projection-order join:

```text
tapp1_fapp0(hom_int_precomp_func(F,p),q)
  -> Hom_func(p,F[q]).
```

The owner-first path reduces `tapp1_func` to the semantic composite and then
applies it to `q`; the projection-first path uses the generic
`fapp0(tapp1_func(...),q) -> tapp1_fapp0(...,q)` rule. The direct capped rule
makes both paths reach `Hom_func`. Applying that result to `h` then uses the
existing generic `fapp0(Hom_func(...),h) -> Hom_fapp0(...)` projection; do not
add another constructor-specific point rule.

#### Target endpoint internalized

The mirror is not supplied by `hom_int`; it has a distinct type and should be
added as a primitive owner:

```text
injective symbol hom_con_int [A B : Cat]
  (F : tau (Functor B A))
  : tau (Functor A (Catd_cat (Op_cat B)));
```

Its object projection should expose the contravariant represented family:

```text
rule fapp0 (@hom_con_int $A $B $F) $W
  -> @hom_con $A $W $B $F;
```

The mirror endpoint-action owners should be:

```text
hom_con_int_postcomp_tele_func(F)
hom_con_int_postcomp_func(F,f).
```

Their full planned declarations are:

```text
symbol hom_con_int_postcomp_tele_func [A B : Cat]
  (F : tau (Functor B A))
  [W X : tau (Obj A)]
  : tau (Functor
      (Hom_cat A W X)
      (Hom_cat
        (@Catd_cat (Op_cat B))
        (@hom_con A W B F)
        (@hom_con A X B F)));

symbol hom_con_int_postcomp_func [A B : Cat]
  (F : tau (Functor B A))
  [W X : tau (Obj A)]
  (f : tau (Hom A W X))
  : tau (Hom
      (@Catd_cat (Op_cat B))
      (@hom_con A W B F)
      (@hom_con A X B F));
```

The projection ladder should be:

```text
rule @fapp1_func _ _ (@hom_con_int $A $B $F) $W $X
  -> @hom_con_int_postcomp_tele_func $A $B $F $W $X;

rule @fapp1_fapp0 _ _ (@hom_con_int $A $B $F) $W $X $f
  -> @hom_con_int_postcomp_func $A $B $F $W $X $f;

rule fapp0 (@hom_con_int_postcomp_tele_func $A $B $F $W $X) $f
  -> @hom_con_int_postcomp_func $A $B $F $W $X $f;
```

The explicit slots are the type-level contract, not a final LHS decision;
focused probes must replace reconstructible slots by `_` where permitted by
the SOP.

For `f : Hom_A(W,X)`, their component should be ordinary postcomposition:

```text
tapp0_fapp0(hom_con_int_postcomp_func(F,f),b)
  -> hom_postcomp_func(id_A,F[b],f).
```

For an arrow `q^op : b -> c` in `Op(B)`, equivalently
`q : c -> b` in `B`, the off-diagonal projection should expose:

```text
tapp1_fapp0(hom_con_int_postcomp_func(F,f),q^op)
  -> Hom_func(F[q],f).
```

Applying the resulting functor to `h : Hom_A(F[b],W)` then computes to:

```text
Hom_fapp0(F[q],f,h) = f o h o F[q].
```

The full `tapp1_func` mirror should internalize
`q^op |-> Hom_func(F[q],f)` by pairing the varying first component with the
constant second component `f`, then using `Hom_tele_func`. This semantic
composite is also the settled design; no separate named full-action owner is
planned. For `q^op : b -> c` in `Op(B)`, equivalently `q : c -> b` in `B`, the
mathematical composite is:

```text
Hom_Op(B)(b,c)
  -- q^op |-> (F[q],f) -->
Product(Hom_A(F[c],F[b]),Hom_A(W,X))
  -- Hom_tele_func(A,F[b],F[c],W,X) -->
Functor(Hom_A(F[b],W),Hom_A(F[c],X)).
```

Its pairing functor is approximately:

```text
Struct_sigma
  (@fapp1_func B A F c b)
  (@Const_func
    (Hom_cat (Op_cat B) b c)
    (Hom_cat A W X)
    f).
```

Writing `Fb = fapp0(F,b)` and `Fc = fapp0(F,c)`, the full kernel-shaped mirror
RHS is approximately:

```text
@comp_fapp0
  Cat_cat
  (Hom_cat (Op_cat B) b c)
  (Product_cat
    (Hom_cat A Fc Fb)
    (Hom_cat A W X))
  (Functor_cat
    (Hom_cat A Fb W)
    (Hom_cat A Fc X))
  (@Hom_tele_func A Fb Fc W X)
  (Struct_sigma
    (@fapp1_func B A F c b)
    (@Const_func
      (Hom_cat (Op_cat B) b c)
      (Hom_cat A W X)
      f)).
```

The conversion `Hom_Op(B)(b,c) = Hom_B(c,b)` supplies the common source of
the two paired components. The direct capped mirror is:

```text
tapp1_fapp0(hom_con_int_postcomp_func(F,f),q^op)
  -> Hom_func(F[q],f),
```

again followed generically by `fapp0(Hom_func(...),h) -> Hom_fapp0(...)`.

This base-level `hom_con_int` should not be confused with the separately
discussed future `hom_con_int_func(G)` from the profunctor/weighted-limit
plans, which varies an entire endpoint functor. Their naming and dependency
relationship must be reviewed, but their proposed types are different.

### Two-endpoint hom action

Keep the promoted public owners:

```text
Hom_tele_func
Hom_func
Hom_fapp0.
```

They own the simultaneous contravariant/covariant action and are the intended
normal form after both endpoint cuts are present.

`Unit_prof(A)` is already the uncurried/product hom bifunctor
`Hom_A(-,-) : Op(A) x A -> Cat` in the profunctor layer. Its object and arrow
projections already target `Hom_cat`, `Hom_tele_func`, and `Hom_func`.
Therefore this plan should not add separate `Hom_bifunctor`, `Hom_`, or
`Hom_con_` symbols. The earlier mention of such a possible parent was a naming
ambiguity, not a missing mathematical construction.

The current projection ladder is intentionally staged:

```text
fapp1_func(Unit_prof) -> Hom_tele_func
fapp0(Hom_tele_func)  -> Hom_func
fapp0(Hom_func)       -> Hom_fapp0.
```

This is the usual lower-dimensional prototype used throughout v3.2 before
promoting the next full omega-categorical projection rung. `Hom_tele_func`
does not yet have specialized `fapp1_func` / `fapp1_fapp0` rules of its own,
so the arrow action of the new semantic composites on higher arrows between
`q`s remains abstract. Nothing exceptional is happening: the functor is
well-typed and its object/capped action computes completely at the level
needed here. Promote the next `Hom_tele_func` higher-action ladder only when a
concrete higher-cell consumer requires it; it is not a prerequisite for the
current `tapp1_func` / `tapp1_fapp0` implementation.

## Runtime And Proof-Time Policy

Runtime reduction should preserve variance:

```text
hom_postcomp_*         stays covariant
hom_precomp_along_*    stays contravariant
Hom_*                  owns combined endpoint action.
```

Proof-time unification may identify opposite or identity-functor
presentations when elaboration needs the mathematical duality:

```text
hom_precomp_along_fapp0(id,h,g)
  == hom_postcomp_fapp0(id,g,h)

hom_postcomp_*(F,...)
  == hom_precomp_along_*(F0,...)
  subject to F == Op_func(F0) and opposite endpoint constraints.
```

For example, the old runtime rule headed by
`hom_postcomp_tele_func(Op_func F0)` may be better replaced by a proof-time
rule whose two compared terms retain generic stable heads and whose side
constraints reconstruct the opposite presentation:

```text
unif_rule @hom_postcomp_tele_func
      $B $A $F
      $Z $X $W
  ≡ @hom_precomp_along_tele_func
      $A0 $B0 $F0
      $Z $W $X
  ↪ [
      (Op_cat $B) ≡ $B0;
      (Op_cat $A) ≡ $A0;
      $F ≡ (@Op_func $A0 $B0 $F0)
    ];
```

This is schematic and must be checked against the inferred parameter order.
Its architectural advantage is that `Op_func` occurs in a proof-time side
constraint instead of acting as a runtime LHS discriminator. Variants may need
the opposite equations rearranged or some category slots inferred, but the
intended shape is two rigid semantic heads plus explicit duality constraints.

Unification rules are experimental and not automatically transitive, so the
implementation must not install a mechanical one-for-one copy of every old
rewrite. Each bridge must be required by a typed consumer or compatibility
check and be tested with an explicit typed `eq_refl` term rather than only an
`assert t ≡ u` conversion check. The old runtime ladder should first be
classified by projection level; only the needed proof-time bridges should be
promoted.

Do not replace the desired `Hom_fapp0` runtime folds by a broad unification
rule such as:

```text
Hom_fapp0(g,f,h) == f o (h o g).
```

That would hide the missing runtime owner rather than complete it. Retain the
existing narrow identity-slot proof-time bridges:

```text
Hom_fapp0(id_x,f,h) == comp_fapp0(f,h)
Hom_fapp0(g,id_y,h) == comp_fapp0(h,g).
```

## Downstream Retargeting

Removing the identity-functor cross-variance rewrite will change runtime
normal forms. Every consumer which currently relies on precomposition becoming
postcomposition must be classified.

The first known targets are the representable-precomposition strictness rules
for:

```text
fdapp1_int_cell
fdapp1_int_hom_fapp0.
```

They currently produce identities at:

```text
hom_postcomp_fapp0(id,q,p),
```

even though their semantic owner is `hom_int_precomp_func`. Their intended
contravariant runtime endpoint should be reviewed as:

```text
hom_precomp_along_fapp0(id,p,q).
```

The audit must also cover:

- the component and higher-action rules around
  `hom_postcomp_tele_fapp1_fapp0` and
  `hom_precomp_along_tele_fapp1_fapp0`;
- diagnostics that explicitly exercise the old `Op_func` runtime bridge;
- representable and path-induction checks whose expected normal form is
  currently `hom_postcomp_fapp0(id,q,p)`;
- profunctor/DefIso consumers which genuinely require covariant
  postcomposition and therefore should not be changed;
- `fdapp1_int_cell` / `fdapp1_int_hom_fapp0` consumers whose strictness type
  endpoints may need a direct proof-time bridge after their runtime target is
  retargeted.

Classification principle:

```text
semantic operation is covariant       keep hom_postcomp_*
semantic operation is contravariant   retarget to hom_precomp_along_*
both endpoint actions are present     fold to Hom_*
only equality of presentations needed use a narrow unif_rule.
```

## Intended Hom_fapp0 Folds

After the cross-variance runtime rule has been removed or demoted and its
consumers retargeted, probe these exact identity-family folds.

Postcomposition after precomposition:

```text
rule @hom_postcomp_fapp0
      $A $A (@id Cat_cat $A)
      $x' $y $y' $f
      (@hom_precomp_along_fapp0
        $A $A (@id Cat_cat $A)
        $y $x' $x $g $h)
  -> @Hom_fapp0 $A $x $x' $y $y' $g $f $h;
```

Precomposition after postcomposition:

```text
rule @hom_precomp_along_fapp0
      $A $A (@id Cat_cat $A)
      $y' $x' $x $g
      (@hom_postcomp_fapp0
        $A $A (@id Cat_cat $A)
        $x $y $y' $f $h)
  -> @Hom_fapp0 $A $x $x' $y $y' $g $f $h;
```

These are preliminary full spellings. The probes must test whether inferred
source/target slots can be replaced by `_` and whether the identity functor is
a genuine discriminator or can be recovered from the endpoints. Keep an
explicit compound LHS slot only when it is a measured guard and annotate it
with `lhs-audit` reasoning.

## Proposed Implementation Order

### Phase 0: baseline and inventory

1. Run a bounded quiet baseline and preserve the warning inventory.
2. Inventory all uses of `hom_con`, `hom_int_precomp_func`,
   `hom_postcomp_*` over `Op_func`, and the identity-functor
   precomposition-to-postcomposition rule.
3. Classify expected normal forms in `emdash3_2_checks.lp` as covariant,
   contravariant, combined, or proof-time compatibility.
4. Verify the planned types of `hom_con_int`,
   `hom_con_int_postcomp_tele_func`, and
   `hom_con_int_postcomp_func`, including all endpoint orientations, in a
   declaration-only focused probe.
5. Record any correction to this architecture before editing the kernel.

### Phase 1: complete the hom_int higher projection ladder

1. Probe `tapp1_fapp0(hom_int_precomp_func(F,p),q)` with target
   `Hom_func(p,F[q])`.
2. Add the point projection check through `fapp0` to
   `Hom_fapp0(p,F[q],h)`.
3. Probe the settled full `tapp1_func` semantic composite which pairs constant
   `p` with `fapp1_func(F)` and applies `Hom_tele_func`.
4. Do not add a named full-action intermediary unless the settled composite
   fails a concrete typed consumer after inferred-slot/source-presentation
   adjustments.
5. Check both owner-first and projection-first reductions to the direct capped
   `Hom_func` join.
6. Validate the existing `tapp0_fapp0` component and the new off-diagonal
   ladder together.

This additive phase is deliberately first. It validates the settled
`Hom_tele_func` semantic-composite pattern against an existing owner before
the plan changes the runtime status of `hom_con` or introduces its mirror.

#### Phase 1 implementation record (2026-07-09)

Phase 1 is promoted and validated.

- The bounded pre-edit baseline passed `make check`. Its warning inventory was
  1,317 total: 1,152 unjoinable critical-pair reports and 165 replaceable
  pattern-variable reports.
- A minimal LHS with inferred outer functor endpoints failed subject reduction.
  The promoted `tapp1_func` and `tapp1_fapp0` rules therefore retain the two
  explicit `@hom_ A B F Y` / `@hom_ A B F X` endpoint slots. They are measured
  subject-reduction guards and are annotated for the strict LHS audit.
- The full rule computes through
  `comp_fapp0 Cat_cat`, `Struct_sigma(Const_func(p),fapp1_func(F))`, and
  `Hom_tele_func`. No new full-action stable head was needed.
- The capped rule computes directly to `Hom_func(p,F[q])` as the required
  projection-order join. Focused diagnostics cover the full rule, the direct
  cap, explicit owner-first evaluation of the semantic composite, the generic
  projection-first path, and the final generic point projection to
  `Hom_fapp0(p,F[q],h)`.
- The promoted active kernel and diagnostics pass bounded `make check`; the
  strict rule-LHS audit reports zero unreviewed clauses.
- The warning-enabled full-file probe measured 1,325 total warnings: 1,160
  unjoinable critical-pair reports and the unchanged 165 replaceable-pattern
  reports. The +8 critical-pair delta is localized to the new `tapp1_*`
  branches interacting with the generic projection, identity, and naturality
  ladders; the probe terminates promptly and all intended typed nondegenerate
  paths compute.

The probe exposed one important dependency which was implicit in the original
Phase 1 wording. At an identity base arrow, the generic rule

```text
tapp1_fapp0(eta,id_b) -> tapp0_fapp0(eta,b)
```

reaches the existing one-slot `hom_precomp_along_func` presentation, while the
new direct branch reaches `Hom_func(p,id)`. These functors are mathematically
the same but are not currently runtime-convertible. A candidate degeneration

```text
Hom_func(p,id) -> hom_precomp_along_func(p)
```

typechecked and closed that isolated typed comparison, but increased the
warning inventory to 1,330 by creating fresh overlaps with
`fapp0(Hom_func) -> Hom_fapp0` and the legacy object-action normal form. It was
not promoted. Orienting the one-slot owner toward `Hom_func` would likewise be
a broader normal-form migration and cannot be done coherently while the
identity-functor precomposition-to-postcomposition object rule remains.

Accordingly, Phase 1's arbitrary-arrow owner-first and projection-first join
is complete, while its identity degeneration is now an explicit dependency of
Phases 5 and 6. Those phases must settle the one-slot/two-endpoint degeneration
at functor and object levels together. This is not a reason to weaken the new
runtime action to a proof-time comparison, but it must remain a tracked
temporary overlap family during the staged migration. The Phase 3 mirror must
apply the same identity-arrow audit.

### Phase 2: primitive contravariant represented family

1. In a temporary full-file probe, remove the definitional body of `hom_con`
   and retain it as an injective primitive.
2. Add its direct object projection.
3. Add direct full and capped arrow projections to
   `hom_precomp_along_tele_func` / `hom_precomp_along_func`.
4. Add focused object, functor, and capped-action assertions.
5. Classify whether a distinct `hom_con_*` stable projection head is actually
   required. Do not add one speculatively.

#### Phase 2 implementation record (2026-07-09)

Phase 2 is promoted and validated.

- `hom_con` is now an injective primitive with direct object computation to
  `Hom_cat A (F[x]) W`; it no longer unfolds through `hom_`, `Op_cat`, and
  `Op_func`.
- All three projection LHSs infer their source category. This is required for
  the active `FibCov_target_catd` instance where `B = Op_cat K` and the literal
  source `Op_cat(Op_cat K)` may normalize before projection.
- The full arrow projection required one new stable source-presentation owner,
  `hom_con_precomp_tele_func`. Its domain remains literally
  `Hom_cat(Op_cat B,X,Y)`, and its object projection reaches
  `hom_precomp_along_func B A F W Y X`. The direct capped projection of
  `hom_con` reaches the same existing precomposition owner. No separate capped
  or point owner was added.
- Removing the old semantic body exposed two genuine whole-family beta laws
  used by existing code: a constant diagram gives
  `Const_catd(Op B,Hom_A(u,W))`, and any contravariant representable into
  `Terminal_cat` gives the constant terminal family. These narrow rules restore
  the existing constant dependent-hom and terminal-source section pipelines;
  no broad alias-compatibility rule was needed.
- Focused diagnostics cover object, full owner, full-owner evaluation, direct
  cap, point action, constant-diagram degeneration, and terminal degeneration.
  The complete pre-existing diagnostic suite also passes.
- Bounded `make check` and the strict rule-LHS audit pass. The post-Phase 2
  warning inventory is 1,341 total: 1,176 unjoinable critical-pair reports and
  the unchanged 165 replaceable-pattern reports. Relative to the Phase 1
  baseline this is a +16 critical-pair delta, localized to primitive
  `hom_con` projection identity/functoriality paths, generic projections of
  the new full owner, and the two whole-family degenerations. Checks terminate
  promptly; the later opposite-duality and identity-variance phases are
  expected to retarget part of this overlap family.

### Phase 3: add the mirror hom_con_int owner

1. Probe primitive `hom_con_int(F) : A -> Catd(Op(B))` and its object
   projection to `hom_con(W,F)`.
2. Add `hom_con_int_postcomp_tele_func` and
   `hom_con_int_postcomp_func` as the covariant target-endpoint action owners.
3. Add the `tapp0_fapp0` component to `hom_postcomp_func`.
4. Probe the capped off-diagonal projection to `Hom_func(F[q],f)` and its
   point projection to `Hom_fapp0(F[q],f,h)`.
5. Probe the settled full `tapp1_func` semantic composite by pairing the
   varying `F[q]` component with constant `f` before applying
   `Hom_tele_func`.
6. Check both owner-first and projection-first reductions to the direct capped
   `Hom_func` join; do not add a separate named full-action owner by default.
7. Reconcile the name with the distinct future `hom_con_int_func(G)` package
   documented by the profunctor plans.

#### Phase 3 implementation record (2026-07-09)

Phase 3 is promoted and validated.

- Added primitive `hom_con_int(F) : A -> Catd_cat(Op_cat B)` with object
  projection `hom_con_int(F)[W] -> hom_con(W,F)`.
- Added `hom_con_int_postcomp_tele_func` and
  `hom_con_int_postcomp_func`, with the complete generic `fapp1_func`,
  `fapp1_fapp0`, and telescope-evaluation ladder. No additional
  source-presentation intermediary was needed at this layer.
- The component at `b` computes to ordinary
  `hom_postcomp_func(id_A,F[b],f)`.
- The full off-diagonal action computes through
  `comp_fapp0 Cat_cat`, the pair `(fapp1_func(F,c,b),Const_func(f))`, and
  `Hom_tele_func(A,F[b],F[c],W,X)`. The direct cap computes to
  `Hom_func(F[q],f)`, and generic `fapp0(Hom_func)` reaches
  `Hom_fapp0(F[q],f,h)`.
- Focused diagnostics cover owner declarations, component action, full action,
  direct cap, explicit owner-first evaluation, generic projection-first
  evaluation, and point action. The two off-diagonal LHSs pass subject
  reduction with all family endpoints inferred, so no new LHS-audit exception
  was introduced.
- Bounded `make check`, catalog generation, and the strict rule-LHS audit pass.
  The post-Phase 3 warning inventory is 1,356 total: 1,191 unjoinable
  critical-pair reports and the unchanged 165 replaceable-pattern reports.
  This is a +15 critical-pair delta over Phase 2, concentrated in the expected
  new owner identity/functoriality, generic projection, component, and
  off-diagonal naturality interactions. The full-file warning probe and active
  check terminate promptly.

As on the Phase 1 side, identity arrows expose a temporary stable-owner versus
generic-identity overlap. The coordinated Phase 5/6 degeneration cleanup must
audit both `Hom_func(p,id)` and its mirror `Hom_func(id,f)`; no isolated
identity fold is promoted during Phase 3.

The short name `hom_con_int` denotes the base-level target-internalized hom
classifier added here. It remains distinct from the future
`hom_con_int_func(G)` package discussed in the profunctor/weighted-limit plans,
which varies an entire endpoint functor.

### Phase 4: opposite-duality runtime demotion

1. Probe removal of the `Op_func`-keyed postcomposition-to-precomposition
   rewrite ladder.
2. Retarget direct `hom_con` consumers through its new projections.
3. Probe constrained two-rigid-head `unif_rule`s which recover `Op_cat` and
   `Op_func` relationships in side equations, beginning with the telescope
   functor level.
4. Add only the narrow proof-time bridges needed by typed compatibility
   checks.
5. Validate both visible opposite presentations and their already-normalized
   category endpoints.
6. Promote this phase separately if it is coherent; do not combine an
   unresolved opposite-duality migration with the final object folds.

#### Phase 4 implementation record (2026-07-09)

Phase 4 is promoted and validated.

- Deleted all eight runtime rewrites whose postcomposition LHS discriminated
  on an `Op_func` argument: telescope, capped functor, object action, capped
  higher action, telescope higher action, and transfor rungs.
- The bridge-free kernel typechecked immediately, confirming that the
  primitive `hom_con` / `hom_con_int` ownership introduced in Phases 2 and 3
  removed every runtime dependency on this semantic shortcut.
- Added generic constrained `unif_rule`s only for the three actively consumed
  rungs: `hom_postcomp_tele_func`, `hom_postcomp_func`, and
  `hom_postcomp_fapp0`. Each compares two rigid semantic heads and reconstructs
  the opposite categories and `Op_func` relationship in side equations; no
  unification rule uses `Op_func` as a runtime discriminator.
- Converted the corresponding direct and projected compatibility diagnostics
  from conversion assertions to typed `eq_refl` proofs. The checks cover the
  telescope head, capped functor head, object head, projection through
  `fapp0`, and an already-double-op-normalized functor presentation.
- No kernel consumer uses the five higher bridge rungs. A direct higher-cell
  `eq_refl` probe was blocked by dependent endpoint types before the outer
  unification rule could solve the comparison. Those speculative unification
  rules and their historical compatibility-only checks were therefore not
  promoted.
- Removed the historical raw `postcomp(Op hom_int)` helper. Its desired target
  required transitivity from the generic object bridge through the separate
  identity precomposition projection to `hom_int_precomp_func`, while
  unification is not transitive. The primitive `hom_int_precomp_func` is now
  the public runtime action, so no compound special-case bridge is justified.
- Retargeted the old opposite-encoded `hom_` projection diagnostic to the new
  primitive `hom_con` surface.
- Bounded `make check`, catalog generation, and the strict LHS audit pass. The
  warning inventory falls from 1,356 to 1,296 total: 1,131 unjoinable
  critical-pair reports and the unchanged 165 replaceable-pattern reports.
  Removing the runtime bridge ladder therefore eliminates 60 critical-pair
  reports while preserving the required typed proof-time compatibility.

### Phase 5: identity-family variance separation

1. Probe deletion of the runtime rule
   `hom_precomp_along_fapp0(id,h,g) -> hom_postcomp_fapp0(id,g,h)`.
2. Add or retain a narrowly typed proof-time bridge between the two rigid
   stable heads.
3. Retarget known contravariant consumers, beginning with
   `fdapp1_int_cell` and `fdapp1_int_hom_fapp0`.
4. Update diagnostics so covariant consumers still expect postcomposition and
   contravariant consumers expect precomposition.
5. Confirm that the active kernel and checks terminate before introducing the
   `Hom_fapp0` folds.

#### Phase 5 implementation record (2026-07-10)

Phase 5 is promoted and validated.

- Deleted the runtime rule which rewrote
  `hom_precomp_along_fapp0(id,h,g)` to
  `hom_postcomp_fapp0(id,g,h)`. Identity-family precomposition now retains its
  contravariant stable head at runtime.
- Added two direct proof-time bridges. The first relates a general
  postcomposition endpoint to the corresponding identity-family
  precomposition endpoint after applying the indexing functor. It is required
  by the component type of `hom_postcomp_tele_fapp1_fapp0`. The second relates
  the already-normalized identity-family pre/post heads. Both are needed
  because unification is head-sensitive and not transitive; neither changes
  runtime reduction.
- Retargeted the strict representable rules for `fdapp1_int_cell` and
  `fdapp1_int_hom_fapp0` to identities at
  `hom_precomp_along_fapp0(id,p,q)`.
- Classified and retargeted diagnostics which had encoded the old normal
  form: strict pre/right naturality and functoriality, the path-composition and
  path-induction transitivity benchmark, `PathOut` source transport, and the
  precomposition endpoint layer of semantic curry. Genuinely covariant inner
  postcomposition actions, including evaluation and target-side accumulation,
  remain unchanged.
- Added a typed `eq_refl` diagnostic for identity-family pre/post proof-time
  compatibility, separate from the runtime projection assertion which now
  expects the precomposition owner.
- One staged reduction artifact is now explicit in the `PathOut` reflexive
  arrow coherence check: its fibre proof is temporarily a composition of an
  identity at the old postcomposition endpoint with an identity at the new
  precomposition endpoint. This is not a new semantic normal form. It is a
  concrete Phase 6 join target for the one-slot/two-endpoint identity
  degeneration; do not restore the deleted cross-variance runtime rule to hide
  it.
- Bounded `make check`, the strict LHS audit, catalog generation, and the
  warning-enabled kernel check pass. The warning inventory is now 1,289 total:
  1,124 unjoinable critical-pair reports and the unchanged 165 replaceable
  pattern-variable reports. This is seven fewer critical-pair reports than the
  post-Phase 4 baseline.

### Phase 6: Hom_fapp0 object-action completion

1. Probe the two intended runtime folds in an owning-position temporary copy.
2. Add ordinary conversion assertions for both evaluation orders.
3. Add typed identity-slot `eq_refl` checks confirming compatibility with the
   existing narrow `Hom_fapp0` unification rules.
4. Inspect both reduction orders and the warning-enabled overlap family.
5. Promote only when `Hom_fapp0` is the actual runtime normal form in both
   assertions.

#### Phase 6 implementation record (2026-07-10)

Phase 6 is promoted and validated.

- Added both direct pointwise folds:

  ```text
  hom_postcomp_fapp0(f,hom_precomp_along_fapp0(g,h))
    -> Hom_fapp0(g,f,h)

  hom_precomp_along_fapp0(g,hom_postcomp_fapp0(f,h))
    -> Hom_fapp0(g,f,h).
  ```

  Directly nested point actions cannot reconstruct the already-promoted
  functor-level composition folds, so these object rules are genuine missing
  projection joins rather than duplicates.
- Settled the Phase 1/3 identity dependency by adding the coherent inactive
  endpoint package:

  ```text
  Hom_func(id,f)     -> hom_postcomp_func(f)
  Hom_func(g,id)     -> hom_precomp_along_func(g)
  Hom_fapp0(id,f,h)  -> hom_postcomp_fapp0(f,h)
  Hom_fapp0(g,id,h)  -> hom_precomp_along_fapp0(g,h).
  ```

  This does not identify covariance and contravariance. It removes an
  identity endpoint from the simultaneous two-endpoint owner and returns the
  surviving one-slot owner.
- Added runtime diagnostics for both object evaluation orders, all four
  identity degenerations, and the object/functor identity-first versus
  fold-first joins. The existing typed `eq_refl` checks continue to exercise
  the proof-time raw-composition readings separately.
- Quiet full-kernel and diagnostic probes, promoted `make check`, catalog
  generation, and the strict LHS audit pass. The explicit tests establish that
  both nondegenerate folds reach `Hom_fapp0`, while identity cases reach the
  corresponding one-slot owner regardless of reduction order.
- The warning inventory is now 1,341 total: 1,176 unjoinable critical-pair
  reports and the unchanged 165 replaceable pattern-variable reports. This is
  a +52 critical-pair delta over Phase 5: +31 after the two object folds and a
  further +21 after the four inactive-endpoint rules. The reported family
  includes identity, existing pre/post accumulation, DefIso cancellation, and
  deeper nested associativity paths. The concrete owner and identity paths
  required by this phase are checked to join; broader arbitrary nesting is not
  closed by mechanically generating an associativity theory for `Hom_fapp0`.
- The temporary composite-of-identities exposed by the Phase 5 `PathOut`
  reflexive-arrow coherence diagnostic is unaffected by the `Hom_*` rules: its
  normal form contains no `Hom_func` or `Hom_fapp0` head. It is therefore
  reclassified as a separate `PathOut`/Sigma transport coherence follow-up,
  not a blocker or an appropriate target for a Hom-specific bridge.

### Phase 7: validation and documentation

1. Run `EMDASH_TYPECHECK_TIMEOUT=60s make check`.
2. Run `make catalog` after changing diagnostics.
3. Run `make warning-summary` and compare the classified delta.
4. Run `make ci` and `make health` after promotion.
5. Update this report, the parent subplan, and the foundations/SOP only where
   the promoted architecture changes current guidance.

#### Phase 7 implementation record (2026-07-10)

Phase 7 is complete.

- Retargeted the reviewer milestones
  `examples/path_induction_transitivity.lp` and
  `examples/products_eval_curry.lp` from the former identity-family
  postcomposition spelling to the promoted precomposition owner. Their
  genuinely covariant inner actions remain postcomposition.
- Updated `EMDASH_FOUNDATIONS.md` with the primitive covariant/contravariant
  owner split, paired `hom_int` / `hom_con_int` internalizations, combined
  `Hom_*` action, identity-endpoint behavior, and current generic
  `comp_prod_fapp1_*` Cat-horizontal-action owner.
- Updated the current SOP/status report, the parent product/Unit-prof subplan,
  and `reports/INDEX.md`; the delegated object-action task is now closed.
- Final `make check`, `make examples`, strict LHS audit, catalog freshness,
  and `git diff --check` pass. `make ci` passes all eight Lambdapi targets,
  Python and Infinity Codex tests, shell syntax, active-reference and report
  header lints, strict LHS audit, and strict catalog freshness.
- `make health` was refreshed on 2026-07-10. The active kernel, diagnostics,
  and all six reviewer examples report exit 0.
- Final warning inventory remains 1,341 total: 1,176 unjoinable critical-pair
  reports and 165 replaceable pattern-variable reports. The Phase 6 delta and
  its consumer-driven deferred associativity boundary are recorded above.

The plan's original intended result is achieved: runtime preserves hom
variance, proof-time bridges own semantic duality, both internalized endpoint
directions expose their off-diagonal action, and both direct pointwise
evaluation orders compute through the general `Hom_fapp0` owner.

## Feasibility Assessment

### Semantic feasibility

High. The covariant, contravariant, and two-endpoint actions are standard
parts of the hom bifunctor. The proposed runtime ownership reflects their
actual variances, and the desired `Hom_fapp0` folds are the two canonical
factorizations of the same bifunctorial action.

### Syntactic expressibility

High. The required types and most projection heads already exist:

```text
hom_postcomp_*
hom_precomp_along_*
hom_int_precomp_*
hom_con_int_postcomp_*
Hom_*.
```

The principal declaration-level changes are making `hom_con` genuinely
primitive, adding the distinct `hom_con_int` mirror and its postcomposition
action owners, and completing the off-diagonal projections of both
internalized sides through `Hom_func` / `Hom_fapp0`. No new category former or
generic higher-cell calculus is presently indicated.

### Computational feasibility

Moderate to high, but migration-sensitive. The failed object folds identify a
specific competing runtime rule rather than a fundamental normalization
obstruction. The main risk is the breadth of downstream code which currently
expects postcomposition as the normal form for semantically contravariant
operations.

The `Op_func` bridge ladder remains the highest-risk portion because it spans
telescope, functor, capped, and higher-action levels. The new
`tapp1_func` projections have a settled semantic formulation using existing
product-valued functor and composition infrastructure; their remaining risk is
ordinary Lambdapi endpoint inference and reduction-order validation rather
than a missing architectural owner. These areas should still be developed in
separate phases with focused typed consumers. The
identity-family rule is narrower and likely easier, but should still follow
the upstream ownership decision so the migration does not leave two competing
architectural stories.

The absent specialized `fapp1_*` ladder of `Hom_tele_func` concerns the next
higher-cell projection rung. It is the expected continuation of the current
lower-dimensional prototype, not a feasibility problem for the object/capped
off-diagonal rules in this plan.

### Normalization and confluence risk

Moderate. Preserving distinct pre/post stable heads increases the number of
runtime normal forms by design, while the final `Hom_fapp0` folds reconverge
only the true two-endpoint cut. This should reduce accidental competition at
the variance boundary, but the full-file warning inventory must classify:

- existing postcomposition accumulation rules;
- precomposition accumulation rules;
- `tapp1_func` / `tapp1_fapp0` projections of both internalized owners;
- `Hom_fapp0` identity and object folds;
- higher telescope projections whose endpoints mention the old normal form.

Warning counts are diagnostic evidence, not a veto. The acceptance condition
is that the intended reduction orders join and checked consumers normalize to
their semantic owners.

## Probe-Time Implementation Decisions

No remaining item in this section blocks the selected architecture. Resolve
these questions empirically in the owning implementation phase and record the
result before promotion:

1. Do the direct `fapp1_func` / `fapp1_fapp0` projections from primitive
   `hom_con` to
   existing `hom_precomp_along_*` heads typecheck cleanly, or is one
   contravariant projection intermediary required by source presentation?
   Default: reuse the existing heads without a new intermediary.
2. Which members of the old `Op_func` runtime ladder need explicit
   proof-time replacements? Current recommendation: only those required by
   typed consumers, using two rigid semantic heads and side constraints where
   feasible, because unification is not transitive.
3. Which existing path-induction and representable checks are genuinely
   covariant and should retain `hom_postcomp_fapp0(id,q,p)`, versus
   contravariant and should move to `hom_precomp_along_fapp0(id,p,q)`?
4. After variance separation, are both `Hom_fapp0` folds needed as runtime
   joins, or does one follow reliably through the promoted functor-level
   `Hom_func` fold and generic projection? Current expectation: probe both;
   keep each only if it owns a distinct reduction path.

## Non-Goals

- Do not remove or weaken the core `Op_cat` / `Op_func` calculus itself.
- Do not make all semantic dualities runtime rewrite rules in the reverse
  direction.
- Do not add separate `Hom_bifunctor`, `Hom_`, or `Hom_con_` owners;
  `Unit_prof` already owns the uncurried/product hom bifunctor.
- Do not conflate the required base-level `hom_con_int(F)` with the distinct
  future `hom_con_int_func(G)` package over endpoint functors.
- Do not replace generic functoriality or naturality with constructor-specific
  identity/composition rules.
- Do not add a broad proof-time equation from arbitrary `Hom_fapp0(g,f,h)` to
  raw nested `comp_fapp0` as a substitute for runtime ownership.
- Do not disturb genuinely covariant postcomposition consumers merely to make
  the source text use precomposition uniformly.
- Do not promote the `Hom_fapp0` folds before the cross-variance normal-form
  rule and its consumers have been addressed.

## Acceptance Criteria

The architecture passed the following promotion gates during implementation:

1. focused probes confirm the planned primitive status and direct projection
   ladder of `hom_con`;
2. declaration and projection probes confirm the planned types of
   `hom_con_int` and its `hom_con_int_postcomp_*` actions;
3. focused checks confirm the specified `tapp1_func` / `tapp1_fapp0` normal
   forms for both internalized owners through
   `Hom_tele_func` / `Hom_func` / `Hom_fapp0`;
4. the runtime/proof-time disposition of every old `Op_func` bridge family is
   listed explicitly;
5. known consumers of the identity-functor precomposition-to-postcomposition
   rule are classified and assigned target normal forms;
6. the exact intended `Hom_fapp0` fold LHSs and discriminators are agreed;
7. focused checks are specified for runtime conversion and proof-time
   `eq_refl` separately;
8. each implementation phase has an independent rollback/debug boundary and
   bounded validation command.

Items 4 and 5 above intentionally finish during the probe-first phases: the
plan fixes their policy and classification criteria, while the active source
and typed diagnostics determine the minimal concrete inventory. They are not
preconditions for beginning Phase 0 or Phase 1.

The implementation is complete when:

1. covariant and contravariant represented families retain distinct runtime
   owners;
2. both internalized endpoint directions have complete component and
   off-diagonal projection ladders;
3. `Unit_prof` remains the single uncurried/product hom-bifunctor owner;
4. opposite/identity semantic duality remains available through the required
   narrow proof-time bridges;
5. contravariant downstream consumers no longer depend on postcomposition as
   their runtime normal form;
6. both required two-endpoint evaluation orders normalize to `Hom_fapp0`;
7. active checks, catalog, CI, health, and the warning inventory pass with any
   warning delta classified in this report.

## Final Architecture Review

Review conclusion updated 2026-07-10: the owner hierarchy remains globally
coherent. Phases 0 through 6 are promoted; Phase 7 validation and current
guidance updates are active. The promoted variance separation and two-endpoint
completion join the identity one-slot/two-endpoint degeneration without
restoring runtime conversion between precomposition and postcomposition.

- The covariant/contravariant owner square has distinct, well-motivated types;
  `hom_con_int` is not a duplicate of `hom_int`.
- The endpoint orientations of both off-diagonal actions produce exactly
  `Hom_func(p,F[q])` and `Hom_func(F[q],f)`.
- Existing `Const_func`, product-valued `Struct_sigma`, generic
  `comp_fapp0 Cat_cat`, and `Hom_tele_func` infrastructure express both full
  `tapp1_func` terms; no new general pairing or composition primitive is
  indicated.
- Direct capped `tapp1_fapp0 -> Hom_func` rules are justified projection-order
  joins, while the point action continues through generic
  `fapp0(Hom_func) -> Hom_fapp0`.
- `Unit_prof` remains the sole uncurried/product hom-bifunctor owner.
- The absent specialized higher action of `Hom_tele_func` is the ordinary next
  omega-categorical projection rung and is not a blocker for this plan.
- The constrained proof-time treatment of opposite presentations preserves
  the intended duality without retaining `Op_func` as a runtime discriminator.
- The final nested object folds remain correctly ordered after variance
  separation and downstream retargeting.

Remaining uncertainty is deliberately empirical: inferred LHS slots,
Lambdapi source-presentation conversion, the minimal unification bridge set,
and the concrete downstream consumer inventory. The probe-first phases own
those questions and have independent promotion gates.

## Side-Task Ledger

- Completed 2026-07-09, Phase 1: promoted the specified `tapp1_func` /
  `tapp1_fapp0` projections of `hom_int_precomp_func` through the `Hom_*`
  owners, with full/capped/point diagnostics and bounded validation.
- Tracked Phase 5/6 dependency discovered by Phase 1: settle the identity
  degeneration `Hom_func(p,id)` versus `hom_precomp_along_func(p)` together
  with the object-level variance boundary. Do not promote the isolated
  `Hom_func -> precomp` candidate, which creates additional projection
  overlaps under the current legacy object normal form.
- Completed 2026-07-09, Phase 2: promoted primitive `hom_con`, the minimal
  `hom_con_precomp_tele_func` source-presentation intermediary, direct capped
  projection to `hom_precomp_along_func`, and the required constant/terminal
  whole-family degenerations.
- Completed 2026-07-09, Phase 3: promoted `hom_con_int` and the complete mirror
  `hom_con_int_postcomp_*` component/full/capped projection ladder through the
  `Hom_*` owners.
- Settled design clarification: `Unit_prof` is the existing uncurried hom
  bifunctor; no separate `Hom_bifunctor`, `Hom_`, or `Hom_con_` symbol is
  planned.
- Settled design decision: the two full internalized `tapp1_func` projections
  are semantic composites through paired `Const_func` / `fapp1_func`
  components and `Hom_tele_func`; their direct capped joins target
  `Hom_func`, and generic `fapp0(Hom_func)` reaches `Hom_fapp0`. No new named
  full-action owner is planned.
- Deferred only on concrete higher-cell demand: specialized
  `fapp1_func` / `fapp1_fapp0` projections of `Hom_tele_func`, the next rung
  after the current `Unit_prof -> Hom_tele_func -> Hom_func -> Hom_fapp0`
  prototype ladder.
- Completed 2026-07-09, Phase 4: deleted all eight `Op_func` runtime bridges,
  promoted the minimum three two-rigid-head constrained proof-time bridges,
  and removed/retargeted compatibility-only diagnostics which depended on
  runtime variance collapse.
- Completed 2026-07-10, Phase 5: removed identity-family runtime variance
  collapse, promoted the two required direct proof-time endpoint bridges, and
  retargeted contravariant strictness, path, and curry diagnostics.
- Completed 2026-07-10, Phase 6: promoted both pointwise `Hom_fapp0` folds and
  the four coherent inactive-endpoint reductions for `Hom_func` /
  `Hom_fapp0`, with explicit nondegenerate and identity reduction-order
  diagnostics.
- Deferred as a separate path-transport coherence task: replace the temporary
  `PathOut` composite of proof-time-compatible identities by a semantic
  `PathOut`/Sigma coherence owner. The normalized term contains no `Hom_*`
  head, so a Hom-specific rewrite would be misplaced.
- Deferred until a concrete consumer requires it: broader accumulation laws
  for arbitrarily nested `Hom_fapp0` with additional pre/post actions. Do not
  generate them mechanically from the warning inventory.
- Conditional future naming cleanup: consider whether
  `hom_int_precomp_tele_func` should be renamed
  `hom_int_precomp_along_tele_func`; this is not required by the variance
  migration.
