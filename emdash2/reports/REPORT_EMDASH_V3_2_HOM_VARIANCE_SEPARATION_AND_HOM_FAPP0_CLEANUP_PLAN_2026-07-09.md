# EMDASH v3.2 Hom Variance Separation And Hom_fapp0 Cleanup Plan

Date: 2026-07-09
Last reviewed: 2026-07-09
Plan-ID: EMDASH-V3-2-HOM-VARIANCE-SEPARATION-HOM-FAPP0-2026-07-09
Depends-On: EMDASH-V3-2-COMP-PROD-FUNC-UNIT-PROF-ACTION-2026-07-07; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Parent-Plan: REPORT_EMDASH_V3_2_COMP_PROD_FUNC_UNIT_PROF_ACTION_SUBPLAN_2026-07-07.md
Supersedes: no whole report; extracts and expands the deferred `Hom_fapp0` object-action cleanup from the parent subplan
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: infinity-codex:019f3811-100c-7ea0-8c38-5534271c1cde:019f48a6-337d-78a1-8135-c6b85220f69e
Infinity-Codex-Decision-Responses: infinity-codex:019f3811-100c-7ea0-8c38-5534271c1cde:019f48a6-337d-78a1-8135-c6b85220f69e
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
primitive covariant owner       hom_ / hom_postcomp_*
primitive contravariant owner   hom_con / hom_precomp_along_*
mixed internal owner            hom_int / hom_int_precomp_*
two-endpoint owner              Hom_tele_func / Hom_func / Hom_fapp0

runtime                         preserves the variance owner
proof time                      relates dual/opposite presentations
```

The plan remains in refinement status. The exact proof-time bridge inventory
and the scope of the first promoted implementation slice must be settled
before code changes begin.

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

The incomplete part is upstream `hom_con`:

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

### Mixed internal hom

Retain:

```text
hom_int(F) : Op_cat A -> Catd_cat B
hom_int(F)[W][y] = Hom_A(W,F[y]).
```

`hom_int` already fills most of the role tentatively described as
`hom_con_int`: it internalizes variation of the represented source endpoint,
and its `hom_int_precomp_*` heads preserve that contravariant action.

The initial recommendation is therefore not to introduce a duplicate
`hom_con_int` symbol. A later refinement may rename or document `hom_int` more
explicitly, but a second primitive should be added only if a distinct type or
projection ladder is identified.

### Two-endpoint hom action

Keep the promoted public owners:

```text
Hom_tele_func
Hom_func
Hom_fapp0.
```

They own the simultaneous contravariant/covariant action and are the intended
normal form after both endpoint cuts are present.

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

hom_postcomp_*(Op_func F,...)
  == hom_precomp_along_*(F,...).
```

The second family is schematic. Unification rules are experimental and not
automatically transitive, so the implementation must not install a mechanical
one-for-one copy of every old rewrite. Each bridge must have two rigid heads,
be required by a typed consumer or compatibility check, and be tested with an
explicit typed `eq_refl` term rather than only an `assert t ≡ u` conversion
check.

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
2. Inventory all uses of `hom_con`, `hom_postcomp_*` over `Op_func`, and the
   identity-functor precomposition-to-postcomposition rule.
3. Classify expected normal forms in `emdash3_2_checks.lp` as covariant,
   contravariant, combined, or proof-time compatibility.
4. Record any correction to this architecture before editing the kernel.

### Phase 1: primitive contravariant represented family

1. In a temporary full-file probe, remove the definitional body of `hom_con`
   and retain it as an injective primitive.
2. Add its direct object projection.
3. Add direct full and capped arrow projections to
   `hom_precomp_along_tele_func` / `hom_precomp_along_func`.
4. Add focused object, functor, and capped-action assertions.
5. Classify whether a distinct `hom_con_*` stable projection head is actually
   required. Do not add one speculatively.

### Phase 2: opposite-duality runtime demotion

1. Probe removal of the `Op_func`-keyed postcomposition-to-precomposition
   rewrite ladder.
2. Retarget direct `hom_con` consumers through its new projections.
3. Add only the narrow proof-time bridges needed by typed compatibility
   checks.
4. Validate both visible opposite presentations and their already-normalized
   category endpoints.
5. Promote this phase separately if it is coherent; do not combine an
   unresolved opposite-duality migration with the final object folds.

### Phase 3: identity-family variance separation

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

### Phase 4: Hom_fapp0 object-action completion

1. Probe the two intended runtime folds in an owning-position temporary copy.
2. Add ordinary conversion assertions for both evaluation orders.
3. Add typed identity-slot `eq_refl` checks confirming compatibility with the
   existing narrow `Hom_fapp0` unification rules.
4. Inspect both reduction orders and the warning-enabled overlap family.
5. Promote only when `Hom_fapp0` is the actual runtime normal form in both
   assertions.

### Phase 5: validation and documentation

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
Hom_*.
```

The principal new declaration-level change is making `hom_con` genuinely
primitive and giving it direct projection rules. No new category former or
higher-cell infrastructure is presently indicated.

### Computational feasibility

Moderate to high, but migration-sensitive. The failed object folds identify a
specific competing runtime rule rather than a fundamental normalization
obstruction. The main risk is the breadth of downstream code which currently
expects postcomposition as the normal form for semantically contravariant
operations.

The `Op_func` bridge ladder is the highest-risk portion because it spans
telescope, functor, capped, and higher-action levels. It should be demoted in a
separate phase with focused typed consumers. The identity-family rule is
narrower and likely easier, but should still follow the upstream ownership
decision so the migration does not leave two competing architectural stories.

### Normalization and confluence risk

Moderate. Preserving distinct pre/post stable heads increases the number of
runtime normal forms by design, while the final `Hom_fapp0` folds reconverge
only the true two-endpoint cut. This should reduce accidental competition at
the variance boundary, but the full-file warning inventory must classify:

- existing postcomposition accumulation rules;
- precomposition accumulation rules;
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
3. Which members of the old `Op_func` runtime ladder need explicit
   proof-time replacements? Current recommendation: only those required by
   typed consumers, because unification is not transitive.
4. Is `hom_int` sufficient as the mixed internalized contravariant owner, or
   does a distinct future `hom_con_int` have a mathematically different type?
   Current recommendation: retain `hom_int` and do not duplicate it.
5. Which existing path-induction and representable checks are genuinely
   covariant and should retain `hom_postcomp_fapp0(id,q,p)`, versus
   contravariant and should move to `hom_precomp_along_fapp0(id,p,q)`?
6. After variance separation, are both `Hom_fapp0` folds needed as runtime
   joins, or does one follow reliably through the promoted functor-level
   `Hom_func` fold and generic projection? Current expectation: probe both;
   keep each only if it owns a distinct reduction path.

## Non-Goals

- Do not remove or weaken the core `Op_cat` / `Op_func` calculus itself.
- Do not make all semantic dualities runtime rewrite rules in the reverse
  direction.
- Do not add a duplicate `hom_con_int` without a distinct type or projection
  need.
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
2. the runtime/proof-time disposition of every old `Op_func` bridge family is
   listed explicitly;
3. known consumers of the identity-functor precomposition-to-postcomposition
   rule are classified and assigned target normal forms;
4. the exact intended `Hom_fapp0` fold LHSs and discriminators are agreed;
5. focused checks are specified for runtime conversion and proof-time
   `eq_refl` separately;
6. each implementation phase has an independent rollback/debug boundary and
   bounded validation command.

The implementation is complete when:

1. covariant and contravariant represented families retain distinct runtime
   owners;
2. opposite/identity semantic duality remains available through the required
   narrow proof-time bridges;
3. contravariant downstream consumers no longer depend on postcomposition as
   their runtime normal form;
4. both required two-endpoint evaluation orders normalize to `Hom_fapp0`;
5. active checks, catalog, CI, health, and the warning inventory pass with any
   warning delta classified in this report.

## Side-Task Ledger

- Active design task: refine primitive `hom_con` and its direct projection
  ladder.
- Active design task: inventory the old `Op_func` runtime bridge ladder and
  decide the minimum rigid-head proof-time replacement set.
- Active design task: classify downstream consumers of identity-functor
  precomposition-to-postcomposition normalization.
- Deferred until those decisions are complete: probe and promote the two
  `Hom_fapp0` object folds.
- Conditional future naming cleanup: consider whether
  `hom_int_precomp_tele_func` should be renamed
  `hom_int_precomp_along_tele_func`; this is not required by the variance
  migration.

