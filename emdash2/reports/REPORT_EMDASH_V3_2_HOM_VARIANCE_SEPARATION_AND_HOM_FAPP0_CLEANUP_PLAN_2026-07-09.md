# EMDASH v3.2 Hom Variance Separation And Hom_fapp0 Cleanup Plan

Date: 2026-07-09
Last reviewed: 2026-07-09
Plan-ID: EMDASH-V3-2-HOM-VARIANCE-SEPARATION-HOM-FAPP0-2026-07-09
Depends-On: EMDASH-V3-2-COMP-PROD-FUNC-UNIT-PROF-ACTION-2026-07-07; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Parent-Plan: REPORT_EMDASH_V3_2_COMP_PROD_FUNC_UNIT_PROF_ACTION_SUBPLAN_2026-07-07.md
Supersedes: no whole report; extracts and expands the deferred `Hom_fapp0` object-action cleanup from the parent subplan
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: infinity-codex:019f3811-100c-7ea0-8c38-5534271c1cde:019f48a6-337d-78a1-8135-c6b85220f69e
Infinity-Codex-Decision-Responses: infinity-codex:019f3811-100c-7ea0-8c38-5534271c1cde:019f48a6-337d-78a1-8135-c6b85220f69e; infinity-codex:019f3811-100c-7ea0-8c38-5534271c1cde:019f4964-f896-74c0-85dc-062f1d01cff7
Status: proposed design/refinement plan; no implementation or probe from this plan has been promoted

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

The plan remains in refinement status. The exact proof-time bridge inventory,
the full higher projection ladders for both internalized owners, and the scope
of the first promoted implementation slice must be settled before code changes
begin.

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

The preferred first design is to route its arrow projections directly to the
existing precomposition owners, without matching an `Op_func` subterm:

```text
fapp1_func(hom_con(W,F),X,Y)
  -> hom_precomp_along_tele_func(F,W,Y,X)

fapp1_fapp0(hom_con(W,F),X,Y,h)
  -> hom_precomp_along_func(F,W,Y,X,h).
```

The endpoint reversal `Y,X` accounts for
`Hom_(Op B)(X,Y) = Hom_B(Y,X)`. Exact Lambdapi terms and whether an additional
stable `hom_con_*` projection head is needed remain probe questions. The
default recommendation is to reuse `hom_precomp_along_*`, because those heads
already own the full telescope, capped, object, and higher-arrow projection
ladder.

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

Its likely semantic body is `Hom_tele_func` after pairing the constant first
component `p` with `fapp1_func(F,b,c)`. A primitive stable intermediary should
be added only if the semantic composite does not expose the required
projection ladder or fails the opaque-endpoint/source-presentation boundary.

#### Target endpoint internalized

The mirror is not supplied by `hom_int`; it has a distinct type and should be
added as a candidate primitive owner:

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
constant second component `f`, then using `Hom_tele_func`.

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
4. Write the exact types of `hom_con_int`,
   `hom_con_int_postcomp_tele_func`, and
   `hom_con_int_postcomp_func`, including all endpoint orientations.
5. Record any correction to this architecture before editing the kernel.

### Phase 1: primitive contravariant represented family

1. In a temporary full-file probe, remove the definitional body of `hom_con`
   and retain it as an injective primitive.
2. Add its direct object projection.
3. Add direct full and capped arrow projections to
   `hom_precomp_along_tele_func` / `hom_precomp_along_func`.
4. Add focused object, functor, and capped-action assertions.
5. Classify whether a distinct `hom_con_*` stable projection head is actually
   required. Do not add one speculatively.

### Phase 2: complete the hom_int higher projection ladder

1. Probe `tapp1_fapp0(hom_int_precomp_func(F,p),q)` with target
   `Hom_func(p,F[q])`.
2. Add the point projection check through `fapp0` to
   `Hom_fapp0(p,F[q],h)`.
3. Probe the full `tapp1_func` as the semantic composite which pairs constant
   `p` with `fapp1_func(F)` and applies `Hom_tele_func`.
4. Introduce a stable intermediary only if the semantic composite cannot
   support the required projections or source presentation.
5. Validate the existing `tapp0_fapp0` component and the new off-diagonal
   ladder together.

### Phase 3: add the mirror hom_con_int owner

1. Probe primitive `hom_con_int(F) : A -> Catd(Op(B))` and its object
   projection to `hom_con(W,F)`.
2. Add `hom_con_int_postcomp_tele_func` and
   `hom_con_int_postcomp_func` as the covariant target-endpoint action owners.
3. Add the `tapp0_fapp0` component to `hom_postcomp_func`.
4. Probe the capped off-diagonal projection to `Hom_func(F[q],f)` and its
   point projection to `Hom_fapp0(F[q],f,h)`.
5. Probe the full `tapp1_func` by pairing the varying `F[q]` component with
   constant `f` before applying `Hom_tele_func`.
6. Reconcile the name with the distinct future `hom_con_int_func(G)` package
   documented by the profunctor plans.

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

### Phase 6: Hom_fapp0 object-action completion

1. Probe the two intended runtime folds in an owning-position temporary copy.
2. Add ordinary conversion assertions for both evaluation orders.
3. Add typed identity-slot `eq_refl` checks confirming compatibility with the
   existing narrow `Hom_fapp0` unification rules.
4. Inspect both reduction orders and the warning-enabled overlap family.
5. Promote only when `Hom_fapp0` is the actual runtime normal form in both
   assertions.

### Phase 7: validation and documentation

1. Run `EMDASH_TYPECHECK_TIMEOUT=60s make check`.
2. Run `make catalog` after changing diagnostics.
3. Run `make warning-summary` and compare the classified delta.
4. Run `make ci` and `make health` after promotion.
5. Update this report, the parent subplan, and the foundations/SOP only where
   the promoted architecture changes current guidance.

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
`tapp1_func` projections are also nontrivial: their result must internalize a
varying base arrow and may encounter the same opaque endpoint/source
presentation boundary previously seen around `Unit_prof`. Both should be
developed in separate phases with focused typed consumers. The
identity-family rule is narrower and likely easier, but should still follow
the upstream ownership decision so the migration does not leave two competing
architectural stories.

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

## Open Design Decisions

These questions remain intentionally open for the next refinement turns:

1. Should the existing `hom_con` name remain the primitive public owner, or
   should a more explicit name be introduced with `hom_con` as a transparent
   surface alias? Current recommendation: retain `hom_con`.
2. Do the direct `fapp1_func` / `fapp1_fapp0` projections from `hom_con` to
   existing `hom_precomp_along_*` heads typecheck cleanly, or is one
   contravariant projection intermediary needed?
3. Can the full `tapp1_func(hom_int_precomp_func(F,p))` and its
   `hom_con_int_postcomp_func` mirror remain semantic composites through
   `Hom_tele_func`, or do they need named stable projection owners?
4. What is the final exact argument order and kernel name for
   `hom_con_int_postcomp_tele_func` / `hom_con_int_postcomp_func`, and how
   should this base-level owner be distinguished from the future
   `hom_con_int_func(G)` package which varies an endpoint functor?
5. Which members of the old `Op_func` runtime ladder need explicit
   proof-time replacements? Current recommendation: only those required by
   typed consumers, using two rigid semantic heads and side constraints where
   feasible, because unification is not transitive.
6. Which existing path-induction and representable checks are genuinely
   covariant and should retain `hom_postcomp_fapp0(id,q,p)`, versus
   contravariant and should move to `hom_precomp_along_fapp0(id,p,q)`?
7. After variance separation, are both `Hom_fapp0` folds needed as runtime
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

The design is implementation-ready when:

1. the primitive status and direct projection ladder of `hom_con` are settled;
2. the exact types and projection ladders of `hom_con_int` and its
   `hom_con_int_postcomp_*` actions are settled;
3. the `tapp1_func` / `tapp1_fapp0` normal forms for both internalized owners
   are specified through `Hom_tele_func` / `Hom_func` / `Hom_fapp0`;
4. the runtime/proof-time disposition of every old `Op_func` bridge family is
   listed explicitly;
5. known consumers of the identity-functor precomposition-to-postcomposition
   rule are classified and assigned target normal forms;
6. the exact intended `Hom_fapp0` fold LHSs and discriminators are agreed;
7. focused checks are specified for runtime conversion and proof-time
   `eq_refl` separately;
8. each implementation phase has an independent rollback/debug boundary and
   bounded validation command.

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

## Side-Task Ledger

- Active design task: refine primitive `hom_con` and its direct projection
  ladder.
- Active design task: specify the missing `tapp1_func` / `tapp1_fapp0`
  projections of `hom_int_precomp_func` through the `Hom_*` owners.
- Active design task: specify `hom_con_int` and the complete mirror
  `hom_con_int_postcomp_*` projection ladder.
- Settled design clarification: `Unit_prof` is the existing uncurried hom
  bifunctor; no separate `Hom_bifunctor`, `Hom_`, or `Hom_con_` symbol is
  planned.
- Active design task: inventory the old `Op_func` runtime bridge ladder and
  decide the minimum two-rigid-head, constraint-based proof-time replacement
  set.
- Active design task: classify downstream consumers of identity-functor
  precomposition-to-postcomposition normalization.
- Deferred until those decisions are complete: probe and promote the two
  `Hom_fapp0` object folds.
- Conditional future naming cleanup: consider whether
  `hom_int_precomp_tele_func` should be renamed
  `hom_int_precomp_along_tele_func`; this is not required by the variance
  migration.
