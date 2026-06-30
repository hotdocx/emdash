# EMDASH v3.2 Equipment-Shadow, Tensor, Co-Yoneda, And Join Redesign Plan

Date: 2026-06-28
Last reviewed: 2026-07-01

Plan-ID: EMDASH-V3-2-EQUIPMENT-SHADOW-TENSOR-JOIN-REDESIGN-2026-06-28
Depends-On: EMDASH-V3-2-PROFUNCTOR-REPRESENTABILITY-2026-06-19; EMDASH-V3.2-DEFISO-HOM-ACTION-PROFCOMP-MIGRATION-2026-06-28; EMDASH-V3-2-PROFUNCTOR-WEIGHTED-LIMITS-2026-06-17
Supersedes: no whole report; refines the remaining equipment-cell route for tensor/co-Yoneda and primitive join in REPORT_EMDASH_V3_2_PROFUNCTOR_WEIGHTED_LIMITS_PRELIM_PLAN_2026-06-17.md
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: active-codex-session-2026-06-28
Infinity-Codex-Decision-Responses: none
Status: join, shaped co-Yoneda, fixed-endpoint tensor-map,
`Prof_tensor_func` / transparent tensor-unit functor consolidation, stable
`Op_prof` semantic owner, internal fixed co-Yoneda naturality-owner, shaped
`Prof_func_hom`, generic identity-normal-form, generic `Prof_comp_transf`
retirement, and transparent compatibility-alias retirement slices landed;
`Prof_func_hom` uncurried internal-action projection slice landed; broad
endpoint-changing/general-cell co-Yoneda runtime rules and obsolete
equipment-style compatibility symbols have been retired from active source and
checks

## Purpose

This report records the post-DefIso architecture decision for the remaining
`Prof_comp_transf` and equipment-style profunctor-cell surface.

The immediate correction already landed elsewhere:

- `Adjunction_hom_prof_comparison` is the strict `ProfComparison`/`DefIso`
  owner for the adjunction mate.
- `Adjunction_prof_transpose` and `Adjunction_prof_untranspose` are now
  transparent selected-arrow views of `defiso_to` and `defiso_from`.
- The adjunction-specific `Prof_comp_transf` cancellation rules were removed.

That correction did not mean `Prof_comp_transf` could be deleted immediately.
The earlier tensor/co-Yoneda and primitive join slices still used it at the
start of this plan. Those core consumers have now migrated to narrower owners.
The generic facade and the leftover transparent compatibility aliases have
now also been removed from active source/checks; their former role remains
documented only in this report.

## Decision Summary

1. Keep `Prof_reindex`.

   Reindexing is mathematically standard and semantically justified. A
   profunctor over `(A,B)` can be changed along endpoint functors. This is the
   right change-of-base operation:

   ```text
   Prof_reindex(R,F,G).
   ```

2. Do not use the full equipment-cell calculus as the default primitive
   language.

   The formula

   ```text
   ProfCell(R',F,R,G) := ProfMap(R', Prof_reindex(R,F,G))
   ```

   is a legitimate derived reading. It does not justify making every tensor,
   co-Yoneda, join, or universal-property computation reduce through a general
   endpoint-changing composition head.

3. For weighted-limit runtime computation, nested hom-action cancellation is
   the correct owner.

   The required beta/eta shape is:

   ```text
   from . (to . f) -> f
   to . (from . g) -> g
   ```

   where `f` and `g` are arbitrary incoming maps into the represented
   profunctor classifiers. This is stronger and more useful for runtime
   universal-property computation than only reducing the selected composite:

   ```text
   from . to -> id
   to . from -> id.
   ```

4. Direct selected-arrow inverse laws are still useful, but they are not the
   primary runtime owner for representability.

   They package ordinary `IsoEvidence` and prove that selected arrows are
   inverse. They do not, by themselves, make an arbitrary incoming map through
   a universal property compute unless the kernel also adds broad
   reassociation and identity cleanup. That broader composition surface is not
   the desired architecture.

5. Accumulation-style cancellation was needed for shaped universal-property
   computation, not because equipment composition is intrinsically preferred.

   Rules of the form:

   ```text
   push(i,r) . h -> push(i, r . h)
   pull(i,s) . h -> pull(i, s . h)
   ```

   express naturality of postcomposition over arbitrary incoming maps and
   shaped/reindexed probes. They should be owned by DefIso/hom-action or by a
   narrow semantic operation, not by generic equipment composition unless the
   statement is genuinely about endpoint-changing equipment cells.

6. Tensor/co-Yoneda and join are separate migrations.

   The adjunction mate no longer depends on `Prof_comp_transf`; join and the
   fixed shaped co-Yoneda beta/fusion core have also moved to narrower owners.
   The remaining broad endpoint-changing/general-cell co-Yoneda expressions
   are compatibility/deferred equipment surfaces. They should not drive new
   core implementation unless a concrete consumer requires that fuller arity.

7. No collage implementation is planned in this migration.

   `Join_cat(A,B)` remains a primitive directed-inductive stress test. It is
   not currently defined as a semantic collage of `Terminal_prof(A,B)`, and
   the redesign below must not smuggle in collage hom decomposition.

## Further Review, 2026-06-28

Reassessment verdict:

- The plan is globally coherent and mathematically points in the right
  direction.
- The weighted-limit and adjunction decisions are already aligned with the
  active `DefIso` / `ProfComparison` owner.
- The plan still needs one explicit missing layer before it is
  implementation-complete: a narrow cell-application/evaluation operation.

The main risk is not that `Prof_reindex` is semantically wrong. It is not. The
main risk is that some current `Prof_comp_transf` uses are really two
operations collapsed into one:

```text
1. endpoint-changing composition of profunctor cells;
2. application/evaluation of an internally natural profunctor cell at a
   shaped element.
```

If the second operation is not named directly, an implementation can easily
reintroduce `Prof_comp_transf` under another name. Therefore the plan should
treat the narrow cell-application/evaluation layer as a prerequisite for the
join migration and as a likely helper for endpoint-changing co-Yoneda
wrappers.

Refined target stack:

```text
fixed-endpoint ProfMap core
  -> Prof_reindex as legitimate change of base
  -> narrow shaped/cell application/evaluation APIs
  -> optional endpoint-changing wrappers
  -> future explicit equipment coherence, only if needed
```

This is the intended distinction between ordinary profunctor mathematics and
the old over-generalized equipment-style runtime story.

## Final Review, 2026-06-29

Verdict: the plan is coherent, mathematically justified, and feasible as a
staged implementation. It is almost decision-complete for the next code pass
provided the first migration uses the concrete owner choices below. It does
not justify deleting all of `Prof_comp_transf` in one step.

Goal:

```text
Remove `Prof_comp_transf` as the runtime owner for join cross projection,
join cross beta, and co-Yoneda beta, while retaining semantically justified
`Prof_reindex` and preserving the existing weighted-limit / adjunction
DefIso architecture.
```

Required constraints:

1. Keep `Prof_reindex` as the canonical endpoint-change operation.
2. Do not introduce collage semantics for `Join_cat`.
3. Do not add general coend/coinserter reductions for `Prof_tensor`.
4. Do not replace `Prof_comp_transf` by an equally broad renamed equipment
   composition head.
5. Route shaped application of profunctor cells through a narrow owner.
6. Let ordinary functoriality, naturality, and later arrow-action levels be
   inherited from generic `fapp*`/`tapp*` owners when internalized.
7. Keep `Prof_comp_transf` only as a compatibility/generic equipment layer
   until join and tensor/co-Yoneda no longer consume it.

Concrete first implementation decision:

1. Add object-level `Prof_cell_apply` as the general narrow operation.

   It should be declared near `Prof_hom`, before tensor/co-Yoneda, with no
   general identity, associativity, or equipment-composition rewrite rules:

   ```text
   Prof_cell_apply(c,r)
     : Prof_hom(I,A,B,F . a,R,G . b)

   where
   c : ProfCell(R',F,R,G)
   r : Prof_hom(I,A',B',a,R',b).
   ```

2. Add `Prof_cell_eval` as the terminal-source specialization.

   It can be introduced after `Terminal_prof` and `Prof_terminal_hom`:

   ```text
   Prof_cell_eval(c,a,b)
     := Prof_cell_apply(c, Prof_terminal_hom(a,b)).
   ```

3. Route join through `Prof_cell_eval`.

   The first join migration should make:

   ```text
   join_cross_hom(a,b)
     := Prof_cell_eval(join_cross_transf,a,b).
   ```

   Then add the direct primitive join recursor cross beta:

   ```text
   join_elim_cross_transf(first,second,cross) -> cross
   ```

   This is not a rebranded general equipment composition law. It is the
   primitive third beta law for the join recursor: the eliminator sends the
   generating cross-cell to the supplied cross-cell.

   `hom_postcomp_*` / `hom_precomp_*` may be relevant when probing internal
   representable-action projections or future factoring of `Prof_func_transf`,
   but they are not prerequisites for this top-level join beta. Pointwise, the
   semantic action is ordinary functor action on the cross arrow; the recursor
   beta itself belongs to the primitive `Join_cat` eliminator.

   The old equipment-style expression remains a valid derived reading, but it
   is deferred and should not be kept as the canonical computation rule:

   ```text
   Prof_comp_transf(
     Prof_func_transf(join_elim_func(first,second,cross)),
     join_cross_transf)
   ```

   After `Prof_comp_transf` is removed, any computational compatibility for
   this reading should be join-specific and should expand through
   `Prof_reindex_transf` plus fixed vertical composition, with
   `hom_precomp_along_*` / `hom_postcomp_*` appearing only inside the
   `Hom_prof_along` projection ladder.

   The shaped computation should be obtained by applying `Prof_cell_eval` to
   that cell-level beta:

   ```text
   Prof_cell_eval(
     join_elim_cross_transf(first,second,cross),a,b)
   -> Prof_cell_eval(cross,a,b).
   ```

   A public `join_elim_cross_hom(first,second,cross,a,b)` head may be added as
   a transparent readability alias or as a fallback stable projection if a
   focused probe shows the kernel needs it. It is not independent
   mathematical data.

   After diagnostics are migrated to those heads, remove the two
   join-specific `Prof_comp_transf` beta rules.

4. Migrate tensor/co-Yoneda after join.

   Introduce fixed-endpoint one-way co-Yoneda maps first, as transparent
   aliases of the existing endpoint-changing names at identity endpoints. Use
   `Prof_cell_apply` for shaped RHSs that still mean "apply this cell to this
   shaped element", and preserve the current arbitrary-`pp` shaped beta. Do not
   promote co-Yoneda to `ProfComparison` in the first pass; add a comparison
   only when a consumer needs reverse beta/eta or ordinary inverse evidence.

5. Retire generic `Prof_comp_transf` last.

   Generic equipment checks and any remaining endpoint-changing public wrappers
   are not blockers for the join migration. They are blockers only for
   wholesale deletion of the generic composition head.

Residual decisions are probe-local rather than architectural:

- exact implicit-argument layout of `Prof_cell_apply`;
- whether later `Prof_cell_apply` should be internalized as a functor after the
  first stable checks;
- warning-enabled overlap deltas after the join-specific rules are removed.

The first code pass should use an uninterpreted `symbol` for
`Prof_cell_apply`, not a `constant`, because the shaped beta rules must be
headed by this narrow application owner.

## Implementation Checkpoint, 2026-06-29

The first join-focused implementation slice has landed in `emdash3_2.lp` and
`emdash3_2_checks.lp`.

Implemented:

- `Prof_cell_apply` was added near `Prof_hom` as a narrow shaped application
  head for one profunctor cell applied to one shaped profunctor element. It has
  no identity, associativity, or generic equipment-composition rewrite rules.
- `Prof_cell_eval` was added after `Terminal_prof` and `Prof_terminal_hom` as
  the transparent terminal-source specialization through
  `Prof_terminal_hom`.
- `join_cross_hom(a,b)` now routes through `Prof_cell_eval` instead of
  `Prof_comp_transf`.
- `join_elim_cross_transf(first,second,cross)` was added as the primitive
  join-recursion cross-cell projection, with direct beta
  `join_elim_cross_transf(first,second,cross) -> cross`.
- The two join-specific `Prof_comp_transf` beta rules were removed.
- Diagnostics now cover `Prof_cell_apply`, `Prof_cell_eval`, the
  `join_cross_hom` evaluation route, the cell-level join cross beta, and the
  shaped `Prof_cell_eval` consequence.

Deliberately not implemented in this slice:

- no optional `join_elim_cross_hom` alias, because the transparent
  `Prof_cell_eval` route checks;
- no tensor/co-Yoneda migration;
- no demotion or deletion of generic `Prof_comp_transf`; at that checkpoint,
  tensor/co-Yoneda compatibility rules still consumed it. Later checkpoints
  retire those tensor/co-Yoneda consumers from active code;
- no derived `join_equipment_cross` compatibility view for the old equipment
  reading.

Validation:

```text
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/equipment_join_probe.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
python3 scripts/audit_rule_lhs.py --show-kept
EMDASH_TYPECHECK_TIMEOUT=60s make warning-summary
EMDASH_TYPECHECK_TIMEOUT=60s make ci
```

The warning-enabled check succeeded with 1,417 warnings. The first warning is
the pre-existing strict-functor identity/opposite overlap, and the warning log
contains no entries headed by `Prof_cell_apply`, `Prof_cell_eval`, or
`join_elim_cross_transf`. Remaining `Prof_comp_transf` warnings are in the
generic equipment/duality compatibility families, not in the removed
join-specific rules.

## Implementation Checkpoint, 2026-06-29, Shaped Co-Yoneda

The first tensor/co-Yoneda implementation slice has landed for shaped-element
beta only.

Implemented:

- `Prof_coyoneda_cov_map(P)` was added as a transparent fixed-endpoint alias
  for `Prof_coyoneda_unit_tensor_cov_transf(Prof_id_transf(P),id_B)`.
- `Prof_coyoneda_con_map(P)` was added as a transparent fixed-endpoint alias
  for `Prof_coyoneda_unit_tensor_con_transf(Prof_id_transf(P),id_A)`.
- The right and left shaped co-Yoneda beta rules now reduce under
  `Prof_cell_apply(CoyR/CoyL, Prof_tensor_hom_hom(...))`.
- The two shaped co-Yoneda beta rules headed by `Prof_comp_transf` were
  removed.
- Diagnostics now cover the fixed one-way map aliases and the new
  `Prof_cell_apply` shaped beta normal forms.

Deliberately not implemented in this slice:

- no `ProfComparison` owner for co-Yoneda;
- no generalized co-Yoneda-along-a-functor beta;
- no replacement yet for the general-cell identity-unit naturality pair using
  `Prof_tensor_hom_transf` / `Prof_tensor_transf_hom`;
- no generic `Prof_comp_transf` demotion or deletion.

Validation:

```text
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/equipment_coyoneda_probe.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
python3 scripts/audit_rule_lhs.py --show-kept
EMDASH_TYPECHECK_TIMEOUT=60s make warning-summary
EMDASH_TYPECHECK_TIMEOUT=60s make ci
```

The warning-enabled check succeeded with 1,415 warnings, down two from the
join checkpoint. The warning log contains no entries headed by
`Prof_cell_apply`, `Prof_cell_eval`, `Prof_coyoneda_cov_map`,
`Prof_coyoneda_con_map`, or `join_elim_cross_transf`.

## Implementation Checkpoint, 2026-06-29, Fixed Tensor Map

The next tensor/co-Yoneda prerequisite slice has landed.

Implemented:

- `Prof_tensor_map(r,s)` was added as the fixed-endpoint vertical tensor-map
  head.
- After reassessment, `Prof_tensor_map` was corrected from a transparent
  identity-endpoint alias of `Prof_tensor_transf` to an independent narrow
  fixed-endpoint owner.
- Diagnostics now cover the fixed-endpoint map type, without asserting
  definitional equality to `Prof_tensor_transf`.

Deliberately not implemented in this slice:

- no `Prof_tensor_func` bifunctor object;
- no tensor identity or composition rules;
- no derived definition of the endpoint-changing `Prof_tensor_transf` wrapper
  from `Prof_tensor_map` plus `Prof_reindex`;
- no replacement yet for the general-cell identity-unit naturality pair using
  `Prof_tensor_hom_transf` / `Prof_tensor_transf_hom`;
- no generic `Prof_comp_transf` demotion or deletion.

Validation:

```text
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/equipment_tensor_map_core_probe.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
python3 scripts/audit_rule_lhs.py --show-kept
EMDASH_TYPECHECK_TIMEOUT=60s make warning-summary
EMDASH_TYPECHECK_TIMEOUT=60s make ci
```

The warning-enabled check stayed at 1,415 warnings. The warning log contains
no entries headed by `Prof_tensor_map`, `Prof_cell_apply`, `Prof_cell_eval`,
`Prof_coyoneda_cov_map`, `Prof_coyoneda_con_map`, or
`join_elim_cross_transf`.

This checkpoint intentionally records only the fixed-endpoint tensor-map
owner needed by later co-Yoneda naturality work. At this checkpoint, the older
`Prof_tensor_transf` still remained as a temporary endpoint-changing
primitive; the later compatibility-symbol retirement checkpoint supersedes
that state and removes it from active code. The intended future direction
remains to derive any endpoint-changing tensor cells from `Prof_tensor_map`,
`Prof_reindex_transf`, and a settled vertical-composition view, not to define
the fixed-endpoint owner through an endpoint-changing primitive. The
general-cell identity-unit naturality rules that were still under
`Prof_comp_transf` at this checkpoint were later demoted from active runtime
computation after the fixed-endpoint naturality and fixed beta/fusion route
had been implemented and checked.

## Implementation Checkpoint, 2026-06-30, Generic Identity Normal Form

At this intermediate checkpoint, `Prof_id_transf` and `Prof_id_hom` were
demoted from stable identity heads to transparent views of the generic family
identity:

```text
Prof_id_transf(A,B,R)
  := id_funcd(Product_cat(Op_cat A,B),R)

Prof_id_hom(B)
  := id_funcd(Product_cat(Op_cat B,B),Unit_prof(B)).
```

The earlier source-only probes were mathematically correct but incomplete:
the remaining `Prof_comp_transf` identity rules still matched the stable
`Prof_id_transf` head. The promoted pass added coherent compatibility sibling
rules that match the actual generic identity owner instead:

```text
Prof_comp_transf(id_funcd(R1), r) -> r
Prof_comp_transf(s, id_funcd(R0)) -> s.
```

In the active Lambdapi rules, the source category argument of `id_funcd` is
written as `_`:

```text
id_funcd _ R
```

This is intentional LHS hygiene. An explicit
`Product_cat(Op_cat A,B)` source typechecks, but it exposes avoidable
critical-pair diagnostics in a reconstructible implicit slot. Replacing that
slot by `_` preserves the intended discrimination on the generic identity
head and keeps the warning-enabled inventory unchanged.

At the identity-normal-form checkpoint, promoted checks covered:

```text
Prof_id_transf(A,B,R) == id_funcd(Product_cat(Op_cat A,B),R)
Prof_id_hom(A) == id_funcd(Product_cat(Op_cat A,A),Unit_prof(A))
Prof_func_hom(id_A) == Prof_id_hom(A)
Prof_comp_transf(Prof_id_transf(R),Prof_id_transf(R)) == Prof_id_transf(R).
```

The last check in that list was removed during the later
`Prof_comp_transf` retirement checkpoint because its only purpose was to pin
the temporary generic facade.

Validation:

```text
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/equipment_prof_id_transparent_with_idfuncd_siblings_probe.lp
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/equipment_prof_id_idfuncd_underscore_probe.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
EMDASH_TYPECHECK_TIMEOUT=60s make warning-summary
```

The warning-enabled active summary stayed at 1,434 warnings: 1,257
unjoinable critical-pair reports and 177 replaceable-pattern reports. This is
the SOP-correct outcome: warnings were used to improve the LHS shape, not as a
semantic veto on the identity-normal-form migration.

Conclusion:

- `Prof_id_transf` is no longer a primitive/stable identity equipment head;
- `Prof_id_hom` is no longer routed through `Prof_id_transf`;
- the remaining generic `Prof_comp_transf` facade no longer blocks identity
  demotion;
- the next cleanup target is retirement or demotion of `Prof_comp_transf`
  itself, not another identity workaround.

Later alias retirement removed `Prof_id_transf` entirely from active code.
The current active identity owners are:

```text
id_funcd(Product_cat(Op_cat A,B),R)
Prof_id_hom(B) := id_funcd(Product_cat(Op_cat B,B),Unit_prof(B)).
```

## Final Architecture Decision, 2026-06-29, Opposite And Endpoint-Changing Cells

The remaining design is now implementation-decision complete enough to guide
the next code passes. The guiding rule is:

```text
fixed-endpoint structure first;
endpoint-changing cells only as derived compatibility views;
generic equipment composition last, and only if still needed.
```

### Opposite Profunctors

`Op_prof(R)` should remain defined, not primitive:

```text
Op_prof(R) := Pullback_catd(R, Product_swap_func).
```

This is mathematically correct for Cat-valued profunctors. A profunctor
`R : A^op x B -> Cat` dualizes to a profunctor over
`B x A^op = Prof_base(Op B, Op A)` by swapping the two base factors. It should
not apply `Op_catd` to the fibres; doing so would add an unintended fibrewise
opposite.

The next promoted owner should be the fixed-endpoint functor:

```text
Op_prof_func(A,B)
  : Prof_cat(A,B) -> Prof_cat(Op B, Op A)
```

defined transparently through the existing pullback functor:

```text
Op_prof_func(A,B)
  := Pullback_catd_func(Product_swap_func(B,Op A)).
```

Its object action computes to `Op_prof(R)` through the existing
`Pullback_catd_func` object rule. A readability alias may be added:

```text
Op_prof_map(r)
  := fapp1_fapp0(Op_prof_func(A,B),r)
```

but identity and composition for fixed-endpoint opposite maps should be
inherited from the generic functor calculus, not restated by profunctor-specific
rules.

### Endpoint-Changing `Op_prof_transf`

The former primitive `Op_prof_transf` was too broad. It combined:

1. fixed-endpoint action of opposite on vertical profunctor maps;
2. compatibility between opposite and endpoint reindexing.

A focused probe established the replacement stack:

```text
Op_prof_func(A',B') on the input cell
  + a narrow reindex/swap bridge
```

The required bridge is:

```text
Prof_reindex(Op_prof(R), Op_func(G), Op_func(F))
  -> Op_prof(Prof_reindex(R,F,G)).
```

Because `Op_prof` is a transparent pullback alias, the kernel-visible promoted
rule is the normalized pullback-by-swap form:

```text
Prof_reindex(
  Pullback_catd(R, Product_swap_func(B,Op A)),
  Op_func(G), Op_func(F))
->
Pullback_catd(
  Prof_reindex(R,F,G),
  Product_swap_func(B',Op A')).
```

This is a focused compatibility bridge between two standard presentations of
the same base substitution. It is not a new general equipment composition
rule. It was probed at the owning position with warning-enabled checking
before promotion and is documented as the single owner of opposite/reindex
commutation.

At the intermediate opposite checkpoint, endpoint-changing opposite cells were
exposed as a transparent compatibility view:

```text
Op_prof_transf(r)
  := fapp1_fapp0(Op_prof_func(A',B'), r)
```

with the target type converted through the bridge above. The former
primitive/injective `Op_prof_transf` and its direct involution, identity, and
composition rules were retired/demoted. Diagnostics moved to:

- fixed `Op_prof_func` object/map checks;
- the narrow reindex/swap bridge;
- any still-needed endpoint-changing view checks.

Later alias retirement removed even the transparent `Op_prof_transf` view from
active source/checks. The active opposite surface is now `Op_prof`,
`Op_prof_func`, `Op_prof_map`, and the opposite/reindex bridge.

### Tensor Endpoint-Changing Cells

`Prof_tensor_map` is the fixed-endpoint vertical owner:

```text
r : ProfMap(P,P')
s : ProfMap(Q,Q')
--------------------------------
Prof_tensor_map(r,s)
  : ProfMap(P tensor Q, P' tensor Q')
```

The former `Prof_tensor_transf` should not be the owner of fixed-endpoint
tensor functoriality. It is now absent from active code and retained only as a
documented future endpoint-changing compatibility idea.

A full derived replacement for the former most-general `Prof_tensor_transf`
needs more than `Prof_tensor_map` and exposed-endpoint `Prof_reindex`: it also
needs a middle-change/coend compatibility map comparing

```text
Prof_tensor(Prof_reindex(R,F,M), Prof_reindex(S,M,G))
```

with

```text
Prof_reindex(Prof_tensor(R,S), F, G).
```

The current kernel has no general coend/coinserter semantics, so this
middle-change operation should not be invented as broad infrastructure during
this migration. For the current co-Yoneda task, the fixed beta/fusion core is
already expressed through `Prof_tensor_map`, fixed co-Yoneda maps, and
`Prof_cell_apply`. The former endpoint-changing compatibility heads have been
removed from active code rather than generalized further.

### Identity And Generic Composition

`Prof_id_transf` is not active code. Vertical identity is owned directly by
the generic `id_funcd` normal form, and the shaped unit case is owned by
`Prof_id_hom(B) := id_funcd(Product_cat(Op_cat B,B),Unit_prof(B))`. The
temporary `Prof_comp_transf` identity bridge existed only during migration and
was removed with the facade.

`Prof_comp_transf` should not be replaced by a renamed composition primitive.
Any derived endpoint-changing compatibility view must specify the exact fixed
operation, the exact `Prof_reindex_transf` step, and the exact vertical
composition/postcomposition owner it uses.

## Implementation Checkpoint, 2026-06-29, Opposite Fixed Functor And Bridge

The opposite-duality slice has been promoted.

Implemented in `emdash3_2.lp`:

- `Op_prof_func(A,B)` is now the fixed-endpoint functor
  `Prof_cat(A,B) -> Prof_cat(Op B,Op A)`, defined through
  `Pullback_catd_func(Product_swap_func(B,Op A))`.
- `Op_prof_map(r)` is a transparent readability alias for the generic
  `fapp1_fapp0(Op_prof_func(A,B),r)` action.
- the normalized opposite/reindex bridge is active at the `Prof_reindex`
  owner:

  ```text
  Prof_reindex(Op_prof(R),Op_func(G),Op_func(F))
    -> Op_prof(Prof_reindex(R,F,G)).
  ```

  The promoted LHS uses the kernel-visible pullback-by-swap shape because
  `Op_prof` is transparent.

- `Op_prof_transf` is no longer an injective primitive and no longer owns
  involution, identity, or composition rewrite rules. It was briefly a
  transparent endpoint-changing view through `Op_prof_func` plus the bridge,
  then was removed from active code during alias retirement.

Diagnostics in `emdash3_2_checks.lp` were migrated accordingly:

- fixed object action of `Op_prof_func`;
- fixed type of `Op_prof_map`;
- opposite/reindex bridge conversion;
- endpoint-changing view type for `Op_prof_transf` at the intermediate
  checkpoint; this check was later removed with the alias;
- fixed-functor identity and composition checks for `Op_prof_map`.

Validation:

```text
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
python3 scripts/audit_rule_lhs.py --show-kept
EMDASH_TYPECHECK_TIMEOUT=60s make warning-summary
EMDASH_TYPECHECK_TIMEOUT=60s make ci
```

The warning-enabled active summary after this slice reports 1,390 warnings:
1,215 unjoinable critical-pair reports and 175 replaceable-pattern reports.
The new bridge accounts for a visible `Prof_reindex` overlap family at the
bridge owner, but the overall warning count is lower than the previous 1,415
inventory because the direct `Op_prof_transf` primitive rewrite rules were
removed.

## Implementation Checkpoint, 2026-06-29, Internal Fixed Co-Yoneda Naturality

The first internal fixed co-Yoneda naturality-owner slice has been promoted.

Implemented in `emdash3_2.lp`:

- `Prof_tensor_right_unit_func(A,B)` internalizes the fixed-endpoint functor
  `P |-> P tensor Unit_B`.
- `Prof_tensor_left_unit_func(A,B)` internalizes the fixed-endpoint functor
  `P |-> Unit_A tensor P`.
- the object projections of those functors compute to the corresponding
  `Prof_tensor` objects.
- their capped arrow projections compute through the existing independent
  `Prof_tensor_map` owner with a generic `id_funcd` on the unit profunctor.
- `Prof_coyoneda_cov_transf(A,B)` is a natural transformation from
  `Prof_tensor_right_unit_func(A,B)` to `id_(Prof(A,B))`.
- `Prof_coyoneda_con_transf(A,B)` is a natural transformation from
  `Prof_tensor_left_unit_func(A,B)` to `id_(Prof(A,B))`.
- `Prof_coyoneda_cov_map(P)` and `Prof_coyoneda_con_map(P)` are now
  transparent diagonal components of those transformations via
  `tapp0_fapp0`.

Diagnostics in `emdash3_2_checks.lp` now cover:

- object and arrow action of both unit tensor functors;
- type of both fixed co-Yoneda transformations;
- fixed map aliases as diagonal `tapp0_fapp0` components;
- the off-diagonal `tapp1_fapp0` component as the internal naturality arrow
  for an arbitrary fixed-endpoint map `r : ProfMap(P,P')`.

Important correction:

- no external commuting-square rewrite rule was added for co-Yoneda
  naturality;
- the failed probe direction of rewriting
  `epsilon_P' . (r tensor id)` to `r . epsilon_P` is rejected as the wrong
  owner under the project SOP;
- the naturality datum is represented internally by generic `tapp1_fapp0`
  for `Prof_coyoneda_cov_transf` and `Prof_coyoneda_con_transf`.

At this checkpoint, the older endpoint-changing
`Prof_coyoneda_unit_tensor_cov_transf` and
`Prof_coyoneda_unit_tensor_con_transf` constants remained active compatibility
and shaped-cell constructors. They no longer owned the fixed-endpoint
`Prof_coyoneda_*_map` aliases, and a later checkpoint retires them from active
code.

Validation so far:

```text
focused source/check probes
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
python3 scripts/audit_rule_lhs.py --show-kept
EMDASH_TYPECHECK_TIMEOUT=60s make warning-summary
```

The warning-enabled active summary after this slice reports 1,406 warnings:
1,231 unjoinable critical-pair reports and 175 replaceable-pattern reports.
The increase from the opposite-duality checkpoint is currently attributable to
new internal functor/transformation projection heads, not to an external
co-Yoneda commuting-square rule.

The remaining general-cell identity-unit co-Yoneda rules headed by
`Prof_comp_transf` had not yet been removed at this checkpoint. The later
fixed beta/fusion slice establishes the minimal core, so these broad
general-cell rules are now classified as deferred equipment compatibility
rather than a required next implementation target.

## Implementation Checkpoint, 2026-06-30, Fixed Co-Yoneda Beta/Fusion

The fixed co-Yoneda shaped beta/fusion slice has been promoted.

Implemented in `emdash3_2.lp`:

- `Prof_func_transf` / `Prof_func_hom` moved earlier, immediately after
  `Prof_comp_transf`, so tensor/co-Yoneda rules can use the existing
  representable functor-induced unit element without adding a new primitive.
- fixed right and left beta rules now reduce
  `Prof_cell_apply(tapp0_fapp0(Prof_coyoneda_*_transf,P),
  Prof_tensor_hom_hom(...,Prof_func_transf(...)))` to the shaped element.
- fixed right and left arbitrary-`pp` fusion rules now reduce
  `Prof_cell_apply(tapp1_fapp0(Prof_coyoneda_*_transf,pp),
  Prof_tensor_hom_hom(...,Prof_func_transf(...)))` to
  `Prof_cell_apply(pp,p)`.
- the older shaped rules headed by
  `Prof_coyoneda_unit_tensor_cov_transf` /
  `Prof_coyoneda_unit_tensor_con_transf` were removed. At this checkpoint,
  those names were only endpoint-changing compatibility/documentation
  surfaces; the later compatibility-symbol retirement checkpoint removes them
  from active code.

Implementation detail:

- the promoted LHSs use canonical
  `Catd_cat(Product_cat(Op_cat A,B))` component categories and normalized
  `Hom_prof_along(id,id)` / `Prof_func_transf` heads. A focused probe showed
  that the readable `Prof_cat`, `Unit_prof`, and `Prof_func_hom` surfaces were
  too transparent for these beta rules to serve as reliable runtime
  discriminators.

Diagnostics in `emdash3_2_checks.lp` now cover:

- direct fixed right/left beta under `Prof_cell_apply`;
- arbitrary fixed-endpoint `pp` right/left fusion through
  `tapp1_fapp0(Prof_coyoneda_*_transf,pp)`;
- the existing general-cell `Prof_comp_transf` identity-unit compatibility
  rules, which are now slated for demotion/removal unless a current concrete
  consumer requires their fuller endpoint-changing arity.

Validation so far:

```text
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/equipment_coyoneda_fixed_beta_probe.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
python3 scripts/audit_rule_lhs.py --show-kept
make catalog
EMDASH_TYPECHECK_TIMEOUT=60s make warning-summary
```

The warning-enabled active summary after this slice reports 1,434 warnings:
1,257 unjoinable critical-pair reports and 177 replaceable-pattern reports.
The remaining `Prof_cell_apply` warning family is expected evidence that the
old compatibility and new fixed beta surfaces overlap during the migration; it
should be reassessed as part of demoting/removing the broad general-cell
`Prof_comp_transf` co-Yoneda pair.

## Implementation Checkpoint, 2026-06-30, Broad Co-Yoneda Compatibility Demotion

The broad endpoint-changing/general-cell co-Yoneda beta pair has been demoted
from active runtime computation.

Implemented in `emdash3_2.lp`:

- removed the right-unit `Prof_comp_transf` rule that reduced
  `Prof_coyoneda_unit_tensor_cov_transf(...,id_B)` composed with
  `Prof_tensor_hom_transf(...,Prof_id_transf(Unit_B))`;
- removed the left-unit `Prof_comp_transf` rule that reduced
  `Prof_coyoneda_unit_tensor_con_transf(...,id_A)` composed with
  `Prof_tensor_transf_hom(...,Prof_id_transf(Unit_A))`;
- initially kept the old endpoint-changing co-Yoneda and mixed
  tensor-introduction symbols as typeable compatibility/documentation surfaces;
  the later compatibility-symbol retirement checkpoint removes them from
  active code;
- kept the fixed co-Yoneda beta/fusion rules under `Prof_cell_apply` as the
  runtime core.

Diagnostics in `emdash3_2_checks.lp` were updated by removing only the two
assertions whose purpose was to require those broad `Prof_comp_transf`
reductions. Type checks for the compatibility symbols remained only until the
later active-code retirement checkpoint.

Validation:

```text
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/equipment_coyoneda_demote_general_cell_probe.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
python3 scripts/audit_rule_lhs.py --show-kept
EMDASH_TYPECHECK_TIMEOUT=60s make warning-summary
```

The warning-enabled active summary stayed at 1,434 warnings: 1,257
unjoinable critical-pair reports and 177 replaceable-pattern reports. The
demotion did not change the current warning inventory.

## Implementation Checkpoint, 2026-06-30, Tensor Compatibility Symbol Retirement

The obsolete endpoint-changing tensor/co-Yoneda compatibility symbols have
been removed from active code.

Removed from `emdash3_2.lp`:

- `Prof_tensor_transf`;
- `Prof_tensor_hom_transf`;
- `Prof_tensor_transf_hom`;
- `Prof_coyoneda_unit_tensor_cov_transf`;
- `Prof_coyoneda_unit_tensor_con_transf`.

Removed from `emdash3_2_checks.lp`:

- the type-only diagnostics for those five symbols.

Kept:

- `Prof_tensor`;
- `Prof_tensor_map`;
- `Prof_tensor_hom_hom`;
- `Prof_tensor_right_unit_func` / `Prof_tensor_left_unit_func`;
- `Prof_coyoneda_cov_transf` / `Prof_coyoneda_con_transf`;
- the fixed `Prof_cell_apply` beta/fusion rules.

The fuller endpoint-changing/equipment reading remains documented in this
report as deferred compatibility. It is no longer an active kernel API.

Validation:

```text
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/equipment_tensor_compat_retire_probe.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
python3 scripts/audit_rule_lhs.py --show-kept
EMDASH_TYPECHECK_TIMEOUT=60s make warning-summary
```

The warning-enabled active summary stayed at 1,434 warnings: 1,257
unjoinable critical-pair reports and 177 replaceable-pattern reports.

## Implementation Checkpoint, 2026-06-30, `Prof_func_hom` Core Owner

The first `Prof_func_transf` audit slice promoted `Prof_func_hom` as the
core owner.

Implemented in `emdash3_2.lp`:

- `Prof_func_hom(F)` is now the primary shaped representable unit element;
- `Prof_func_hom(id)` reduces to `Prof_id_hom`;
- at this checkpoint, a temporary representable functor-composition
  compatibility rule reduced
  `Prof_comp_transf(Prof_func_hom(G),Prof_func_hom(F))` to
  `Prof_func_hom(G . F)`; that temporary rule was later removed during
  `Prof_comp_transf` retirement;
- at this checkpoint, `Prof_func_transf(F)` became a transparent view of
  `Prof_func_hom(F)`; the later alias-retirement checkpoint deleted that view
  from active code;
- fixed co-Yoneda beta/fusion rules now key on `Prof_func_hom`, not on the
  broader equipment-style name.

The lasting active-code result is `Prof_func_hom`; old public/equipment
readings that mention `Prof_func_transf` are report-level historical/deferred
formulas, not active kernel API.

## Design Checkpoint, 2026-07-01, `Prof_func_hom` Uncurried Action

`Prof_func_hom(F)` should compute as the product/uncurried presentation of the
existing ordinary internal hom-action:

```text
fapp1_int_transf(F)
  : Transf
      (hom_int(A,A,id_A))
      (hom_int(B,A,F) o Op_func(F)).
```

The object component of `Prof_func_hom(F)` at a product object `(x,y)` is:

```text
tapp0_fapp0(Prof_func_hom(F),(x,y))
  -> fapp1_func(F,x,y).
```

For the base-arrow action, do not make the runtime owner a raw formula such
as `F(k) o F(h) o F(l)` and do not add a commuting-square naturality rule.
The canonical owner is the nested `tapp1_fapp0` projection already exposed by
`fapp1_int_transf(F)`.

Let:

```text
F : Functor A B
x,y,x',y' : Obj A
l : Hom_(Op_cat A)(x,x')    // equivalently Hom_A(x',x)
k : Hom_A(y,y')
```

Then:

```text
tapp1_fapp0(fapp1_int_transf(F),l)
  : Hom_(Catd_cat A)
      (hom_ A A id_A x)
      (hom_ B A F (F x')).
```

Since `Hom_cat(Catd_cat A)` reduces to `Functord_cat`, this is a Cat-valued
natural family morphism over the target variable `y`:

```text
y : A ;
  Hom_A(x,y) -> Hom_B(F x', F y).
```

The second projection along `k : Hom_A(y,y')` is therefore well-typed:

```text
tapp1_fapp0(
  tapp1_fapp0(fapp1_int_transf(F),l),
  k)
  : Functor
      (Hom_cat A x y)
      (Hom_cat B (F x') (F y')).
```

Applied to `h : Hom_A(x,y)`, its semantic reading is:

```text
F(k o h o l)
```

and, after ordinary functoriality is observed, the same arrow may be read as:

```text
F(k) o F(h) o F(l).
```

The nested `tapp1_fapp0` term is the implementation owner; the composed-arrow
form is only the ordinary mathematical reading.

For a product arrow

```text
pq : Hom_(Product_cat (Op_cat A) A) (x,y) (x',y')
```

the intended capped off-diagonal projection is:

```text
tapp1_fapp0(Prof_func_hom(F),pq)
  -> tapp1_fapp0(
       tapp1_fapp0(fapp1_int_transf(F), sigma_Fst pq),
       sigma_Snd pq).
```

The promoted implementation should probably introduce a small readable helper
or stable projection head, for example:

```text
Prof_func_hom_fapp1_fapp0(F,pq)
```

whose body or projection rule is the nested `tapp1_fapp0` expression above.
This keeps the large internal-action expression out of later tensor/co-Yoneda
rules while preserving the correct semantic owner. A full transparent
definition of `Prof_func_hom` through semantic uncurrying remains deferred
until the currently missing transfor action of `uncurry_func_func` is added.

## Implementation Checkpoint, 2026-07-01, `Prof_func_hom` Uncurried Action

The first uncurried-action slice has been promoted.

Implemented in `emdash3_2.lp`:

- object projection of a functor-induced shaped unit:

  ```text
  tapp0_fapp0(Prof_func_hom(F),ab)
    -> fapp1_func(F,sigma_Fst(ab),sigma_Snd(ab));
  ```

- capped product-base arrow projection through the nested internal ordinary
  hom-action owner:

  ```text
  tapp1_fapp0(Prof_func_hom(F),pq)
    -> tapp1_fapp0(
         tapp1_fapp0(fapp1_int_transf(F), sigma_Fst(pq)),
         sigma_Snd(pq)).
  ```

The promoted rules keep the product/opposite base and the normalized
representable source/target families explicit on the LHS. The fully
underscored probe failed subject-reduction checking, while the source/target
underscored probe introduced an unrelated Cat-valued projection overlap. The
current guarded rules are therefore intentional LHS-audit exceptions.

No helper head was needed in the first pass: the RHS can point directly at the
nested `tapp1_fapp0` owner without reviving broad equipment-cell syntax. A
later helper remains reasonable if a concrete consumer needs a shorter stable
surface.

Added diagnostics in `emdash3_2_checks.lp`:

- component projection to `fapp1_func`;
- capped product-base projection to the nested `tapp1_fapp0` expression.

Validation:

```text
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/prof_func_hom_uncurried_action_probe.lp
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/prof_func_hom_uncurried_action_specific_probe.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
python3 scripts/audit_rule_lhs.py --show-kept
EMDASH_TYPECHECK_TIMEOUT=60s make warning-summary
```

The warning-enabled active summary after this slice reports 1,366 warnings:
1,199 unjoinable critical-pair reports and 167 replaceable-pattern reports.
The delta is localized to the new `Prof_func_hom` projection family, mainly
overlaps with existing `Op_cat` / special-category normalization and the
identity specialization `Prof_func_hom(id) -> Prof_id_hom`.

Validation so far:

```text
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/equipment_prof_func_hom_owner_probe.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
python3 scripts/audit_rule_lhs.py --show-kept
EMDASH_TYPECHECK_TIMEOUT=60s make warning-summary
```

The warning-enabled active summary stayed at 1,434 warnings: 1,257
unjoinable critical-pair reports and 177 replaceable-pattern reports.

## Current Active `Prof_comp_transf` Consumers

There are no active source or diagnostic consumers of `Prof_comp_transf`.
The deleted active pieces were:

```text
symbol Prof_comp_transf
comp_catd_fapp0(Prof_reindex_transf(...), r) -> Prof_comp_transf(...)
Prof_comp_transf(id_funcd(R1), r) -> r
Prof_comp_transf(s, id_funcd(R0)) -> s
Prof_comp_transf(Prof_func_hom(G), Prof_func_hom(F)) -> Prof_func_hom(G.F)
```

The corresponding diagnostics that only typed or normalized the retired
facade were removed. The surviving computational owners are the narrower
ones already listed in this report: `Prof_cell_apply`, `Prof_cell_eval`,
fixed co-Yoneda transformations and their `tapp1_fapp0` action,
`Prof_tensor_map`, `Prof_reindex`, `Prof_reindex_transf`, `Op_prof_func`, and
the generic family/hom-action calculus.

## Implementation Checkpoint, 2026-06-30, `Prof_comp_transf` Retirement

The generic equipment-composition facade has been removed from active code.

Removed from `emdash3_2.lp`:

- the `Prof_comp_transf` symbol;
- the semantic fold from
  `comp_catd_fapp0(Prof_reindex_transf(...),r)` to `Prof_comp_transf`;
- the temporary `id_funcd` left/right identity sibling rules;
- the representable composition compatibility rule for
  `Prof_func_hom(G)` and `Prof_func_hom(F)`.

Removed from `emdash3_2_checks.lp`:

- the type assertion for `Prof_comp_transf`;
- the semantic-fold assertion to `Prof_comp_transf`;
- the identity assertion for
  `Prof_comp_transf(Prof_id_transf(R),Prof_id_transf(R))`;
- the representable-composition assertion through `Prof_comp_transf`.

The deletion was intentionally not replaced by another broad endpoint-changing
composition primitive. Deferred equipment readings must be documented as
readings or rebuilt from fixed owners only when a concrete future consumer
requires them.

Validation:

```text
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/equipment_prof_comp_retire_probe.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
python3 scripts/audit_rule_lhs.py --show-kept
EMDASH_TYPECHECK_TIMEOUT=60s make warning-summary
make health
EMDASH_TYPECHECK_TIMEOUT=60s make ci
```

The warning-enabled active summary dropped to 1,413 warnings: 1,246
unjoinable critical-pair reports and 167 replaceable-pattern reports. This
drop is useful diagnostic evidence that the broad facade was a real overlap
source, but it is not the mathematical reason for the deletion. The
mathematical reason is that join, tensor/co-Yoneda, opposite, and identity now
have narrower owners.

An active source/check scan now finds no `Prof_comp_transf` symbol or
diagnostic assertion.

## Implementation Checkpoint, 2026-06-30, Compatibility Alias Retirement

The last transparent equipment-style aliases have been removed from active
source and checks.

Removed from `emdash3_2.lp`:

- `Prof_id_transf`;
- `Prof_func_transf`;
- `Op_prof_transf`;
- code comments that named retired endpoint-changing tensor/co-Yoneda
  compatibility symbols.

Removed from `emdash3_2_checks.lp`:

- the endpoint-changing type assertion for `Op_prof_transf`;
- the type assertion for `Prof_func_transf`;
- the conversion assertion for `Prof_id_transf`.

The active source now uses only the core owners:

```text
id_funcd
Prof_id_hom
Prof_func_hom
Op_prof
Op_prof_func
Op_prof_map
Prof_reindex
Prof_reindex_transf
Prof_cell_apply
Prof_cell_eval
Prof_tensor_map
Prof_tensor_hom_hom
Prof_coyoneda_*_transf / Prof_coyoneda_*_map
```

Former names may still occur in historical/deferred formulas in this report,
but they are no longer active kernel API.

Validation:

```text
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/equipment_alias_retire_probe.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
python3 scripts/audit_rule_lhs.py --show-kept
EMDASH_TYPECHECK_TIMEOUT=60s make warning-summary
make health
EMDASH_TYPECHECK_TIMEOUT=60s make ci
```

The warning-enabled active summary stayed at 1,413 warnings: 1,246
unjoinable critical-pair reports and 167 replaceable-pattern reports. The
cleanup reduced active source size and public API surface without changing the
remaining warning families.

## Implementation Checkpoint, 2026-06-30, Tensor Bifunctor And Unit-Functor Consolidation

The deferred `Prof_tensor_func` cleanup has been promoted.

Implemented in `emdash3_2.lp`:

- `Prof_tensor_func(A,B,X)` is now the fixed-endpoint tensor bifunctor:

  ```text
  Prof_tensor_func(A,B,X)
    : Functor(
        Product_cat(Prof_cat A B, Prof_cat B X),
        Prof_cat A X).
  ```

- its object projection computes to the opaque tensor object:

  ```text
  fapp0(Prof_tensor_func(A,B,X),(P,Q))
    -> Prof_tensor(A,B,X,P,Q).
  ```

- its capped arrow projection computes to the existing fixed-endpoint
  vertical owner:

  ```text
  fapp1_fapp0(Prof_tensor_func(A,B,X),(r,s))
    -> Prof_tensor_map(r,s).
  ```

- `Prof_tensor_right_unit_pair_func(A,B)` and
  `Prof_tensor_left_unit_pair_func(A,B)` insert the fixed unit profunctor on
  the right or left.
- `Prof_tensor_right_unit_func(A,B)` and
  `Prof_tensor_left_unit_func(A,B)` are now transparent composites through
  `Prof_tensor_func` and the corresponding pair-insertion functor. Their
  previous direct primitive projection rules were removed.
- `Prof_coyoneda_cov_map(P)` and `Prof_coyoneda_con_map(P)` are now stable
  diagonal projection heads rather than transparent aliases. The diagonal
  components of `Prof_coyoneda_cov_transf` and
  `Prof_coyoneda_con_transf` fold to those stable map heads through
  `tapp0_fapp0`.
- the direct co-Yoneda beta rules under `Prof_cell_apply` now discriminate on
  `Prof_coyoneda_cov_map(P)` and `Prof_coyoneda_con_map(P)`.
- the arbitrary-`pp` co-Yoneda fusion rules still use internal
  `tapp1_fapp0` naturality components, but their source/target functor slots
  are inferred. This keeps the rule keyed on the co-Yoneda transformation
  head instead of on the transparent tensor-unit functor presentation.

This is a projection-ladder repair, not a return to the former
endpoint-changing equipment surface. No `Prof_comp_transf`,
`Prof_tensor_transf`, `Prof_tensor_hom_transf`, or
`Prof_tensor_transf_hom` owner was reintroduced. Co-Yoneda naturality remains
internalized by `Prof_coyoneda_*_transf` and generic `tapp1_fapp0`; there is
still no external commuting-square naturality rewrite.

Diagnostics in `emdash3_2_checks.lp` now include:

- type, object-action, and capped-arrow-action checks for
  `Prof_tensor_func`;
- inherited right/left unit-functor object and arrow computations through the
  transparent `Prof_tensor_func` pipeline;
- diagonal co-Yoneda component checks through the stable
  `Prof_coyoneda_*_map` heads;
- the existing direct beta and arbitrary-`pp` fusion checks through
  `Prof_cell_apply`.

Validation:

```text
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/prof_tensor_func_unit_probe.lp
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/prof_tensor_func_unit_tiny_checks.lp
EMDASH_PROBE_TIMEOUT=60s scripts/probe.sh tmp/probes/prof_tensor_func_coyoneda_stable_map_probe.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
python3 scripts/audit_rule_lhs.py --show-kept
EMDASH_TYPECHECK_TIMEOUT=60s make warning-summary
```

The warning-enabled active summary after this slice reports 1,357 warnings:
1,190 unjoinable critical-pair reports and 167 replaceable-pattern reports.
The warning log contains generic functor hom-action overlap families involving
the new `Prof_tensor_func` projections; these are diagnostic evidence about
the new internal functor head, not a semantic blocker. The overall warning
inventory decreased from the alias-retirement checkpoint's 1,413 reports.

### Opposite And Duality

Current declarations:

```text
Op_prof
Op_prof_func
Op_prof_map
```

Current role:

- `Op_prof` is already a transparent pullback-by-swap definition on
  profunctor objects;
- `Op_prof_func` owns the fixed-endpoint vertical action of opposite;
- `Op_prof_map` is a transparent readability alias for the generic action of
  `Op_prof_func`;
- the opposite/reindex bridge converts the endpoint-changing target when a
  proof or future theorem needs that comparison.

Target role:

- keep this fixed-functor/bridge presentation;
- do not reintroduce direct identity, composition, or involution rewrite rules
  for an endpoint-changing opposite alias;
- add further opposite diagnostics only at the fixed functor or bridge.

Deletion status:

- `Op_prof` should remain as a defined object-level operation;
- `Op_prof_transf` has been deleted from active source/checks.

### Tensor And Co-Yoneda

Current declarations:

```text
Prof_tensor
Prof_tensor_map
Prof_tensor_func
Prof_tensor_hom_hom
Prof_tensor_right_unit_pair_func
Prof_tensor_left_unit_pair_func
Prof_tensor_right_unit_func
Prof_tensor_left_unit_func
Prof_coyoneda_cov_transf
Prof_coyoneda_con_transf
shaped co-Yoneda beta rules headed by Prof_cell_apply
deferred general-cell/equipment compatibility surfaces
```

Current role:

- `Prof_tensor` is an opaque coend-like profunctor composite;
- tensor introduction is currently exposed only for shaped elements through
  `Prof_tensor_hom_hom`;
- `Prof_tensor_map` exposes the fixed-endpoint vertical tensor action as a
  narrow owner independent from any endpoint-changing tensor wrapper;
- `Prof_tensor_func` internalizes fixed-endpoint tensor bifunctoriality and
  owns the object/action projections to `Prof_tensor` and
  `Prof_tensor_map`;
- the right and left tensor-unit functors are transparent composites through
  `Prof_tensor_func` and pair-insertion functors;
- fixed one-way co-Yoneda maps are stable diagonal projection heads for
  internal natural transformations;
- fixed co-Yoneda naturality is represented by generic `tapp1_fapp0`
  off-diagonal components, not by external commuting-square rewrites;
- shaped co-Yoneda beta rules cancel a tensor-introduced shaped element
  through `Prof_cell_apply`;
- the old general-cell identity-unit rules under `Prof_comp_transf` are
  compatibility scaffolding for a broader endpoint-changing/equipment arity,
  not part of the minimal fixed-endpoint core.

The co-Yoneda beta/naturality rules split into two different arities:

```text
shaped-element beta:
  Prof_tensor_hom_hom(..., p, unit)

general-cell identity-unit naturality:
  Prof_tensor_hom_transf(..., qq, unit)
  Prof_tensor_transf_hom(..., unit, qq)
```

The second pair is an endpoint-changing/general-cell compatibility reading of
identity-unit co-Yoneda. It is not the minimal fixed-endpoint mathematics
needed for the current tensor/co-Yoneda core, and it should not be rebuilt as
another most-general equipment endpoint-changing primitive. If a later
consumer really needs this fuller arity, it should be reintroduced as a
documented compatibility theorem derived from fixed-endpoint tensor/co-Yoneda
owners plus explicit reindexing/coherence data.

Target role:

- keep `Prof_tensor` opaque until coend/coinserter semantics exists;
- put fixed-endpoint tensor and co-Yoneda structure first;
- preserve fixed co-Yoneda naturality through internal `Transf` symbols and
  generic `tapp*` projections;
- expose endpoint-changing variants only as transparent reindexed views or
  narrowly justified wrappers;
- avoid using general equipment composition as the semantic owner of
  co-Yoneda beta;
- migrate shaped beta first through `Prof_cell_apply`;
- remove or demote broad general-cell `Prof_comp_transf` co-Yoneda runtime
  rules once the fixed `Prof_cell_apply` beta/fusion checks are stable;
- document the broader general-cell/equipment formula as deferred compatibility
  rather than treating it as an immediate implementation prerequisite.

Deletion status:

- the shaped co-Yoneda pair no longer consumes `Prof_comp_transf`;
- the fixed-endpoint co-Yoneda maps now have internal naturality owners;
- the fixed tensor bifunctor and transparent unit-functor pipeline have
  landed; the former duplicated primitive unit-functor projection rules have
  been removed;
- the general-cell identity-unit `Prof_comp_transf` pair is not a blocker for
  the minimal core and should be demoted from active runtime computation unless
  a concrete current consumer requires it;
- the old endpoint-changing tensor/co-Yoneda compatibility symbols have been
  removed from active code; any future compatibility theorem should be added
  under a new explicit plan and should target fixed-endpoint
  `Prof_tensor_map`, `Prof_coyoneda_*_transf`, `tapp*` projections, and
  `Prof_cell_apply` as its core ingredients.

### Shaped Cell Application / Evaluation

Current implicit role:

- `join_cross_hom(a,b)` was previously implemented by composing
  `join_cross_transf` with `Prof_terminal_hom(a,b)` through
  `Prof_comp_transf`; it now routes through `Prof_cell_eval`;
- endpoint-changing tensor and co-Yoneda wrappers also often need to apply a
  natural profunctor cell to a shaped element.

Target role:

- keep `Prof_cell_apply` / `Prof_cell_eval` as the narrow first-pass owner for
  evaluating an internally natural profunctor cell on shaped endpoint data;
- do not use arbitrary equipment-cell composition merely to obtain this
  shaped application.

This operation is not specific to `Join_cat`. Join is the first place where
the missing operation becomes unavoidable, because `join_cross_hom(a,b)` is
just the generating cross cell applied to the shaped endpoint probe `(a,b)`.

General mathematical shape:

```text
R  : Prof(A,B)
R' : Prof(A',B')
F  : A' -> A
G  : B' -> B
c  : ProfCell(R',F,R,G)
   := ProfMap(R', Prof_reindex(R,F,G))

a : I -> A'
b : I -> B'
r : Prof_hom(I,A',B',a,R',b)
-------------------------------------------
Prof_cell_apply(c,r)
  : Prof_hom(I,A,B,F . a,R,G . b)
```

Semantically:

```text
Prof_cell_apply(c,r) := ((a,b)^* c) . r.
```

That is, first reindex the natural profunctor cell `c` along the shaped
probe `(a,b)`, then apply it to the shaped element `r`.

The terminal-source specialization is:

```text
R' = Terminal_prof(A',B')
!_{a,b} : Prof_hom(I,A',B',a,Terminal_prof(A',B'),b)

Prof_cell_eval(c,a,b)
  := Prof_cell_apply(c,!_{a,b})
```

So for:

```text
c : ProfCell(Terminal_prof(A,B), f, R, g)
a : I -> A
b : I -> B
-------------------------------------------
c[a,b] : Prof_hom(I, X, Y, f . a, R, g . b)
```

For the join cross cell this specializes to:

```text
join_cross_transf(A,B)[a,b]
  : Unit_I -> Hom_prof_along(join_fst_func . a, join_snd_func . b).
```

Equipment-style presentation:

```text
Prof_cell_apply(c,r)
  = Prof_comp_transf(c,r)

Prof_cell_eval(c,a,b)
  = Prof_comp_transf(c, Prof_terminal_hom(a,b)).
```

This is mathematically legitimate double-category/equipment composition. The
design problem is that it makes the broad endpoint-changing composition head
the runtime owner of a much narrower operation: applying one natural family
map to one shaped element. The narrow operation is the one that should own
join cross projection and likely several tensor/co-Yoneda shaped cuts.

Usual mathematical reading:

```text
restriction / pullback / whiskering of a natural transformation,
then evaluation at a generalized element.
```

For a Cat-valued profunctor `R : X^op x Y -> Cat`, a family:

```text
c_{a,b} : 1 -> R(fa,gb)
```

reindexed along `a : I -> A` and `b : I -> B` gives the shaped family:

```text
i |-> c_{a(i),b(i)}
```

with arrow action supplied by the naturality of `c`.

Internalization target:

```text
Prof_cell_apply_func :
  Prof_transf_cat(A,A',B,B',R',F,R,G)
  x Prof_hom_cat(I,A',B',a,R',b)
  -> Prof_hom_cat(I,A,B,F . a,R,G . b)
```

The exact product/telescope presentation is not settled. The architectural
point is that, once this is internalized as a functor, arrow-action between
cells and between shaped elements should be inherited from the generic
`fapp*` calculus rather than restated by hand. Until then, a stable
application/evaluation head may be justified as a narrow projection owner.

Selected kernel names for the first migration:

```text
Prof_cell_apply
Prof_cell_eval
```

The first declaration should be a plain rewrite-owning `symbol`, placed near
`Prof_hom`, before tensor/co-Yoneda:

```text
symbol Prof_cell_apply
  [I A' B' A B : Cat]
  [R' : Prof(A',B')]
  [R  : Prof(A,B)]
  [F  : A' -> A]
  [G  : B' -> B]
  [a  : I -> A']
  [b  : I -> B']
  (c : ProfCell(R',F,R,G))
  (r : Prof_hom(I,A',B',a,R',b))
  : Prof_hom(I,A,B,F . a,R,G . b).
```

Kernel spelling:

```text
symbol Prof_cell_apply
  [I A' B' A B : Cat]
  [R' : τ (Prof A' B')]
  [R : τ (Prof A B)]
  [F : τ (Functor A' A)]
  [G : τ (Functor B' B)]
  [a : τ (Functor I A')]
  [b : τ (Functor I B')]
  (c : τ (Obj (@Prof_transf_cat A A' B B' R' F R G)))
  (r : τ (@Prof_hom I A' B' a R' b))
  : τ (@Prof_hom
      I A B
      (@comp_cat_fapp0 I A' A F a)
      R
      (@comp_cat_fapp0 I B' B G b));
```

Do not add identity, associativity, or general equipment-composition rules for
`Prof_cell_apply` in the first pass.

The terminal-source specialization should be a transparent definition after
`Terminal_prof` and `Prof_terminal_hom`:

```text
Prof_cell_eval(c,a,b)
  := Prof_cell_apply(c, Prof_terminal_hom(a,b)).
```

Kernel spelling:

```text
symbol Prof_cell_eval
  [I A' B' A B : Cat]
  [R : τ (Prof A B)]
  [F : τ (Functor A' A)]
  [G : τ (Functor B' B)]
  [a : τ (Functor I A')]
  [b : τ (Functor I B')]
  (c : τ (Obj
      (@Prof_transf_cat A A' B B'
        (@Terminal_prof A' B') F R G)))
  : τ (@Prof_hom
      I A B
      (@comp_cat_fapp0 I A' A F a)
      R
      (@comp_cat_fapp0 I B' B G b))
≔ @Prof_cell_apply
    I A' B' A B
    (@Terminal_prof A' B')
    R
    F G a b
    c
    (@Prof_terminal_hom I A' B' a b);
```

Deferred or fallback names, to use only if a focused probe shows a real
typing or performance need:

```text
Prof_cell_hom
Prof_transf_eval_hom
join_cross_hom(A,B,I,a,b) as a primitive-only fallback
```

Decision status:

- this layer is required for a clean join migration;
- `Prof_cell_apply` is the mathematically natural general target;
- `Prof_cell_eval` is the terminal-source specialization most directly
  visible in join;
- the first implementation should introduce `Prof_cell_apply`, define
  `Prof_cell_eval` through `Prof_terminal_hom`, and route `join_cross_hom`
  through `Prof_cell_eval`;
- the exact implicit-argument layout and later functor-internalized
  presentation are probe-local details, but the first promoted head should be
  a plain `symbol`;
- it must remain narrower than `Prof_comp_transf`.

### Functor-Induced Representable Cell

Current declarations:

```text
Prof_func_hom(F)
Prof_func_hom(id) -> Prof_id_hom
```

The former `Prof_comp_transf(Prof_func_hom(G),Prof_func_hom(F))` compatibility
rule is retired with the generic equipment-composition facade. If
representable functor composition needs a future runtime owner, it should be a
fixed/generic functorial owner, not a revival of broad endpoint-changing
equipment composition.

Current role:

- packages the hom-action of an ordinary functor as a shaped representable
  unit element;
- its object projection should expose the ordinary hom-action component
  `fapp1_func(F,x,y)`.

Target role:

- keep `Prof_func_hom` as the fixed shaped owner;
- add the uncurried/product-base projection ladder:

  ```text
  tapp0_fapp0(Prof_func_hom(F),(x,y))
    -> fapp1_func(F,x,y)

  tapp1_fapp0(Prof_func_hom(F),pq)
    -> tapp1_fapp0(
         tapp1_fapp0(fapp1_int_transf(F), sigma_Fst pq),
         sigma_Snd pq)
  ```

- use a narrow helper/stable projection head if needed for the second rule,
  but do not replace it by a raw `F(k) o F(h) o F(l)` naturality-square rule.

Deletion status:

- `Prof_func_hom` is active core and should not be deleted;
- `Prof_func_transf` has been deleted from active source/checks. Deferred
  formulas may mention the old name only as historical notation.

### Primitive Join

Current declarations:

```text
Join_cat(A,B)
join_fst_func : A -> Join_cat(A,B)
join_snd_func : B -> Join_cat(A,B)
join_cross_transf
join_cross_hom(a,b) := Prof_cell_eval(join_cross_transf,a,b)
join_elim_func(first,second,cross)
join_elim_cross_transf(first,second,cross) -> cross
```

Current role:

- primitive directed-inductive example;
- `join_cross_transf` is an internally natural family of cross arrows;
- shaped cross arrows are derived from the internally natural cell;
- the recursor maps the primitive cross cell to the supplied `cross`.

Target role:

- keep join primitive;
- do not define it by collage in this migration;
- make the cross-arrow and cross-beta API narrower than general equipment
  composition.

Deletion status:

- first-pass join migration is complete;
- no active join-specific `Prof_comp_transf` beta rules remain;
- the old equipment-style reading is deferred to a future compatibility head
  if a concrete consumer needs it.

## Weighted-Limit Runtime Computation

The right-adjoint weighted-limit theorem and its dual require runtime
universal-property computation, not merely ordinary inverse evidence.

A weighted limit states that a cone/probe classifier is represented. The
computational theorem must act on arbitrary incoming maps:

```text
f : R -> WeightedCone_prof(F,W)
g : R -> Hom_prof(L)
```

The runtime operations are eliminators:

```text
push(i,f)
pull(i,g)
```

and the beta/eta laws must compute:

```text
pull(i, push(i,f)) -> f
push(i, pull(i,g)) -> g.
```

This is why the implementation uses nested cancellation:

```text
from . (to . f) -> f
to . (from . g) -> g.
```

The selected-arrow special cases:

```text
to := push(i,id)
from := pull(i,id)
```

then produce ordinary inverse evidence, but the universal-property computation
is not reducible to those selected-arrow laws alone. Without nested
cancellation, one would need broad runtime reassociation and identity cleanup
to reduce:

```text
(from . to) . f
```

back to `f`. That is exactly the kind of global composition surface this
development avoids.

Design consequence:

- `DefIso` and `ProfComparison` own arbitrary-map push/pull cancellation.
- `defiso_iso_evidence` owns ordinary selected-arrow evidence.
- `right_adjoint_preserves_weighted_limit_cov_comp` consumes the strict
  computational layer.
- `right_adjoint_preserves_weighted_limit_cov_iso` consumes ordinary
  `IsoEvidence`; it is not derivable from an arbitrary ordinary input because
  there is no general `IsoEvidence -> DefIso`.

For a strict input, however, the ordinary theorem should be the evidence
projection of the strict theorem. That is the intended bridge:

```text
prof_comparison_evidence(
  right_adjoint_preserves_weighted_limit_cov_comp(isl,adj))
= right_adjoint_preserves_weighted_limit_cov_iso(
  prof_comparison_evidence(isl), adj).
```

## Tensor And Co-Yoneda Target Design

Mathematical baseline:

```text
Prof(A,B) := [A^op x B, Cat]
ProfMap(P,Q) := Nat(P,Q)
P[F,G] := Prof_reindex(P,F,G)
P[F,G](a',b') = P(F a', G b')
```

For:

```text
P : Prof(A,B)
Q : Prof(B,C)
```

the tensor is the coend-like composite:

```text
P tensor_B Q : Prof(A,C)
(P tensor_B Q)(a,c) ~= integral^b P(a,b) x Q(b,c)
```

The coend formula is semantic intent only. The current kernel has no general
coend/coinserter quotient, so the object remains opaque.

### Semantic Layers

Use four layers and do not collapse them.

Level 0: profunctor objects.

```text
Prof_tensor(P,Q) : Prof(A,X)
```

This remains opaque. There is no current kernel coend or coinserter quotient
that would justify reducing the object itself more aggressively.

Level 1: fixed-endpoint maps.

```text
ProfMap(P,Q)
ProfMap(Prof_tensor(P,Q), O)
ProfMap(P, Prof_imply_cov(O,Q))
```

Fixed-endpoint maps are the primitive vertical layer. Tensor/closed
eval-lambda already follows this pattern:

```text
Prof_eval_cov_map
Prof_lambda_cov_map
Prof_eval_con_map
Prof_lambda_con_map
```

Co-Yoneda should follow the same discipline.

Level 2: fixed-endpoint functoriality.

Tensor now has the fixed-base bifunctor:

```text
Prof_tensor_func(A,B,X)
  : Functor(
      Product_cat(Prof_cat A B, Prof_cat B X),
      Prof_cat A X)
```

Its object and capped-arrow actions should compute to:

```text
fapp0(Prof_tensor_func(A,B,X), (P,Q))
  -> Prof_tensor(A,B,X,P,Q)

fapp1_fapp0(Prof_tensor_func(A,B,X), (r,s))
  -> Prof_tensor_map(r,s).
```

This is the unified fixed-endpoint owner for tensor functoriality.
Identity/composition should come from the global functor calculus.

Expected fixed-endpoint map action:

```text
r : ProfMap(P,P')
s : ProfMap(Q,Q')
-------------------------------
Prof_tensor_map(r,s) : ProfMap(P tensor Q, P' tensor Q')
```

Since this is internalized as a functor, local identity and composition laws
should be inherited from the generic `fapp*` calculus.

The current unit tensor functors:

```text
Prof_tensor_right_unit_func(A,B)
  : Functor(Prof_cat A B, Prof_cat A B)

Prof_tensor_left_unit_func(A,B)
  : Functor(Prof_cat A B, Prof_cat A B)
```

are the source functors of the fixed co-Yoneda transformations. They are now
derived uniformly by pairing with the unit profunctor:

```text
Prof_tensor_right_unit_pair_func(A,B)
  : P |-> (P, Unit_prof(B))

Prof_tensor_right_unit_func(A,B)
  := Prof_tensor_func(A,B,B)
       . Prof_tensor_right_unit_pair_func(A,B)

Prof_tensor_left_unit_pair_func(A,B)
  : P |-> (Unit_prof(A), P)

Prof_tensor_left_unit_func(A,B)
  := Prof_tensor_func(A,A,B)
       . Prof_tensor_left_unit_pair_func(A,B).
```

This `Prof_tensor_func` route reduces duplicated primitive surface in the
types of `Prof_coyoneda_cov_transf` and `Prof_coyoneda_con_transf`. It is not
the same proposal as the separate, deferred unit-intro maps discussed below.
The promoted implementation uses stable diagonal co-Yoneda map heads as the
projection ladder needed after the tensor-unit functors became transparent
composites.

Level 3: endpoint-changing wrappers.

Endpoint-changing tensor cells are allowed only as derived views:

```text
Prof_tensor_transf(r,s)
```

would need to be a wrapper around reindexing plus fixed-endpoint tensor
functoriality, but only after the necessary middle-change/coend compatibility
map is explicitly available. That full wrapper is a future equipment/coend
compatibility theorem, not part of this migration. The former
`Prof_tensor_transf` stable head has been retired from active code; new code
should target fixed-endpoint `Prof_tensor_map` plus fixed co-Yoneda
transformations instead.

Expected shaped tensor introduction:

```text
p : Unit_I -> P[F,M]
q : Unit_I -> Q[M,G]
-------------------------------
p tensor_M q : Unit_I -> (P tensor Q)[F,G]
```

This is the mathematical content currently carried by names like
`Prof_tensor_hom_hom`. Its computation should be owned by tensor/co-Yoneda
heads or by the narrow cell-application/evaluation layer, not by generic
`Prof_comp_transf`.

### Co-Yoneda API

The fixed-endpoint co-Yoneda transformations are the current semantic owners:

```text
Prof_coyoneda_cov_transf(A,B)
  : Transf(
      Prof_tensor_right_unit_func(A,B),
      id_func(Prof_cat A B))

Prof_coyoneda_con_transf(A,B)
  : Transf(
      Prof_tensor_left_unit_func(A,B),
      id_func(Prof_cat A B)).
```

Their components are the one-way co-Yoneda maps:

```text
Prof_coyoneda_cov_map(P)
  : ProfMap(Prof_tensor(P, Unit_prof(B)), P)

Prof_coyoneda_con_map(P)
  : ProfMap(Prof_tensor(Unit_prof(A), P), P).
```

In kernel spelling these maps are components of the transformations:

```text
Prof_coyoneda_cov_map(P)
  := tapp0_fapp0(Prof_coyoneda_cov_transf(A,B), P)

Prof_coyoneda_con_map(P)
  := tapp0_fapp0(Prof_coyoneda_con_transf(A,B), P).
```

The older endpoint-changing names:

```text
Prof_coyoneda_unit_tensor_cov_transf(pp,N)
Prof_coyoneda_unit_tensor_con_transf(pp,M)
```

remain temporary compatibility surfaces. New core computation should be stated
through the fixed transformations and their `tapp0_fapp0`/`tapp1_fapp0`
projections, not through those endpoint-changing names.

### Unit-Shaped Identity Elements

The identity input for co-Yoneda tensor beta is not a new mathematical object.
The canonical shaped identity element of the unit profunctor is the existing:

```text
Prof_func_hom(M)
  : Prof_hom(I,B,B,M,Unit_prof(B),M).
```

This is not merely a collection of identity arrows at objects of `I`.
`Prof_hom(I,A,B,F,P,G)` is indexed over `Unit_prof(I)`, so it already contains
the action over arrows of `I`. Semantically, for an arrow `u : i -> j`, the
right-unit element above carries `M[u] : M[i] -> M[j]`.

A readability alias may be added if useful, but it must be transparent:

```text
Unit_prof_id_hom(M) := Prof_func_hom(M).
```

For endpoint-changing co-Yoneda along a functor `G : B -> B'`, the corresponding
identity element in the represented hom profunctor may be documented as:

```text
eta_{G,M}
  : Prof_hom(I,B,B,M,Hom_prof_along(G,G),M)
```

morally obtained from `Prof_func_hom(G . M)` after representable reindexing.
This belongs to a later generalized co-Yoneda-along-a-functor pass and should
not be introduced as an independent primitive in the identity-unit cleanup.

### Co-Yoneda Beta Target

The core right-unit beta is:

```text
p : Prof_hom(I,A,B,F,P,M)

Prof_cell_apply(
  Prof_coyoneda_cov_map(P),
  Prof_tensor_hom_hom(M,p,Prof_func_hom(M)))
-> p.
```

Pointwise this represents the usual formula:

```text
epsilon^R_P(p,f) = P(id,f)(p)
```

but at the `Prof_hom` level the action by `f` is already packaged inside the
shaped element `p`. Therefore the RHS is just `p`.

The core left-unit beta is:

```text
p : Prof_hom(I,A,B,F,P,G)

Prof_cell_apply(
  Prof_coyoneda_con_map(P),
  Prof_tensor_hom_hom(F,Prof_func_hom(F),p))
-> p.
```

For arbitrary fixed-endpoint:

```text
pp : ProfMap(P,P')
```

the generic naturality component is already internalized as:

```text
tapp1_fapp0(Prof_coyoneda_cov_transf(A,B), pp)
  : ProfMap(Prof_tensor(P,Unit_prof(B)), P')
```

and dually for `Prof_coyoneda_con_transf`. Because `Prof_cell_apply` does not
currently have a generic accumulation rule through `tapp1_fapp0`, the next
computational target should include the derived fusion beta:

```text
Prof_cell_apply(
  tapp1_fapp0(Prof_coyoneda_cov_transf(A,B), pp),
  Prof_tensor_hom_hom(M,p,Prof_func_hom(M)))
-> Prof_cell_apply(pp,p)
```

and dually:

```text
Prof_cell_apply(
  tapp1_fapp0(Prof_coyoneda_con_transf(A,B), pp),
  Prof_tensor_hom_hom(F,Prof_func_hom(F),p))
-> Prof_cell_apply(pp,p).
```

These arbitrary-`pp` fusion rules are not new mathematics. They are
cut-elimination rules for the already-internalized naturality of
`Prof_coyoneda_*_transf` combined with the direct beta.

The current old presentation:

```text
Prof_comp_transf(
  Prof_coyoneda_unit_tensor_cov_transf(pp,id),
  Prof_tensor_hom_transf(id,qq,Prof_id_hom))
-> Prof_comp_transf(pp,qq)
```

is therefore compatibility scaffolding for a broader general-cell arity. The
core shaped owner is `Prof_cell_apply`, not `Prof_comp_transf`.

There is no separate `I tensor I` shape: `Prof_tensor_hom_hom` composes two
shaped elements over the same shape `I` and the same middle probe `M`. The
shape is a context category, not a tensor factor.

### Deferred Unit Intro And Tensor Intro Extensions

Possible unit-intro maps:

```text
Prof_tensor_right_unit_intro_map(P)
  : ProfMap(P, Prof_tensor(P,Unit_prof(B)))

Prof_tensor_left_unit_intro_map(P)
  : ProfMap(P, Prof_tensor(Unit_prof(A),P))
```

are separate from the `Prof_tensor_func` implementation above. They may be useful
later as unitor/section data, possibly via `DefIso` or `ProfComparison`, but
they are not required for the immediate core beta. A full inverse/eta law would
be stronger than the current exposed tensor theory and may require tensor
extensionality or coend-like structure.

Likewise, one-shaped-side intro cells such as:

```text
Prof_tensor_right_hom_intro_transf(M,s)
Prof_tensor_left_hom_intro_transf(M,r)
```

may help later to demote `Prof_tensor_hom_transf` and
`Prof_tensor_transf_hom`, but the identity-unit cleanup should use
`Prof_tensor_hom_hom` directly.

A general tensor-map intro beta is also deferred:

```text
Prof_cell_apply(
  Prof_tensor_map(r,s),
  Prof_tensor_hom_hom(M,p,q))
-> Prof_tensor_hom_hom(
     M,
     Prof_cell_apply(r,p),
     Prof_cell_apply(s,q)).
```

This is useful tensor-intro functoriality, but broader than the right/left unit
co-Yoneda cleanup.

### Deferred General-Cell Identity-Unit Compatibility

The old co-Yoneda compatibility rules using:

```text
Prof_tensor_hom_transf
Prof_tensor_transf_hom
```

are a different, broader arity of the identity-unit co-Yoneda story. They are
not the minimal fixed-endpoint core implemented by
`Prof_coyoneda_*_transf`, `Prof_tensor_hom_hom`, and `Prof_cell_apply`. They
also are not the later generalized co-Yoneda-along-a-functor task.

The ordinary equipment-style reading is:

Right-unit ordinary notation:

```text
qq : ProfCell(Q,H,P,id_B)
pp : ProfCell(P,F,P',id_B)

CoyR(pp,id_B) . (qq tensor id_{Unit_B})
  -> pp . qq.
```

The special case `pp = id_P` is:

```text
epsilon^R_P[H,id_B] . (qq tensor id_{Unit_B})
  -> qq.
```

Left-unit ordinary notation:

```text
qq : ProfCell(Q,id_A,P,K)
pp : ProfCell(P,id_A,P',G)

CoyL(pp,id_A) . (id_{Unit_A} tensor qq)
  -> pp . qq.
```

The special case `pp = id_P` is:

```text
epsilon^L_P[id_A,K] . (id_{Unit_A} tensor qq)
  -> qq.
```

This is a coherent full-equipment formula, but it is not required for the
current core implementation. The current migration should not rebuild this
whole endpoint-changing/general-cell arity merely because the old code had it.
It may be documented as a future compatibility theorem, to be implemented only
when a concrete consumer needs it.

The fixed-endpoint mathematics required for the tensor side is only:

```text
P,P' : Prof(A,B)
Q,Q' : Prof(B,X)

r : ProfMap(P,P')
s : ProfMap(Q,Q')

r tensor s : ProfMap(P tensor Q, P' tensor Q')
```

For right co-Yoneda, the fixed-endpoint map is:

```text
epsilon^R_P : ProfMap(P tensor Unit_B, P)
```

with naturality:

```text
r . epsilon^R_P
  =
epsilon^R_P' . (r tensor id_Unit_B).
```

Thus for an incoming map `q : ProfMap(Q,P)` the computational beta target is:

```text
epsilon^R_P' . (r tensor id_Unit_B) . (q tensor id_Unit_B)
  -> r . q.
```

The left map is dual:

```text
epsilon^L_P : ProfMap(Unit_A tensor P, P)

r . epsilon^L_P
  =
epsilon^L_P' . (id_Unit_A tensor r).
```

The old general-cell rules are endpoint-changing identity-unit specializations
of these formulas. Their current syntax uses
`Prof_tensor_hom_transf` and `Prof_tensor_transf_hom`, but the co-Yoneda
consumers instantiate those mixed constructors only as:

```text
qq tensor id_Unit_B
id_Unit_A tensor qq.
```

Therefore `Prof_tensor_hom_transf` and `Prof_tensor_transf_hom` are, at most,
semantically admissible compatibility shims. They are not evidence that the
final architecture needs their full mixed "general cell plus shaped element"
generality as a primitive owner.

If a later compatibility theorem is required, its owner should be built from:

- fixed-endpoint co-Yoneda owner, using a one-way map first and a
  `ProfComparison` only for later reverse beta/eta or ordinary evidence needs;
- fixed-endpoint tensor functoriality through the active `Prof_tensor_func`
  owner and its `Prof_tensor_map` arrow projection;
- `Prof_reindex_transf` for endpoint changes;
- `hom_postcomp_fapp0` or the corresponding `ProfComparison` push/pull;
- a derived/compatibility expression for the final composed cell, until a
  narrower public cell-composition story is settled.

The immediate tensor/co-Yoneda implementation should not pursue that fuller
replacement. Once fixed beta/fusion checks are stable, the old broad
`Prof_comp_transf` runtime rules may be removed or demoted, with this section
recording the deferred compatibility reading.

### Endpoint-Changing Co-Yoneda Wrappers

The existing endpoint-changing right wrapper has the semantic type:

```text
P  : Prof(A,B)
P' : Prof(A',B')
F  : A -> A'
G  : B -> B'
N  : J -> B'

pp : ProfCell(P,F,P',G)

CoyR(pp,N)
  : ProfCell(P tensor_B Hom_{B'}(G,N), F, P', N)
```

with pointwise action:

```text
CoyR(pp,N)([x,u]) = P'(1,u)(pp(x))

x : P(a,b)
u : Hom_{B'}(G b, N j).
```

The left wrapper is dual:

```text
M : I -> A'

CoyL(pp,M)
  : ProfCell(Hom_{A'}(M,F) tensor_A P, M, P', G)
```

with pointwise action:

```text
CoyL(pp,M)([u,x]) = P'(u,1)(pp(x))

u : Hom_{A'}(M i, F a)
x : P(a,b).
```

### General Co-Yoneda Along A Functor

The old deferred task was to generalize identity-representable beta using:

```text
Prof_func_hom(F)
```

The refined target is:

```text
pp : ProfCell(P,F0,P',G0)
p  : Prof_hom(I,A,B,H,P,M)

eta_{G0,M}
  : Prof_hom(I,B,B,M,Hom_prof_along(G0,G0),M)

Prof_cell_apply(
  CoyR(pp,G0),
  Prof_tensor_hom_hom(M,p,eta_{G0,M}))
-> Prof_cell_apply(pp,p).
```

The fixed-endpoint right beta is the special case `F0 = id`, `G0 = id`, and
`pp = id_P`.

The left generalized beta is:

```text
pp : ProfCell(P,F0,P',G0)
p  : Prof_hom(I,A,B,H,P,K)

eta_{F0,H}
  : Prof_hom(I,A,A,H,Hom_prof_along(F0,F0),H)

Prof_cell_apply(
  CoyL(pp,F0),
  Prof_tensor_hom_hom(H,eta_{F0,H},p))
-> Prof_cell_apply(pp,p).
```

Do not implement these by adding more `Prof_comp_transf` laws. The design
question for every consumer remains:

```text
Is the consumer fixed-endpoint after reindexing?
```

If yes, use `Prof_reindex` to put the target in a fixed endpoint and apply the
fixed co-Yoneda owner: component map for the direct beta,
`tapp1_fapp0(Prof_coyoneda_*_transf, pp)` for arbitrary fixed-endpoint `pp`,
and `ProfComparison` only when a reverse/eta or inverse-evidence consumer
actually requires it.

If no, the task is not merely "general co-Yoneda"; it is a real
endpoint-changing naturality theorem. That theorem may deserve a narrow
public wrapper, but it should still be derived from:

- `Prof_reindex`;
- fixed-endpoint `ProfMap`;
- fixed-endpoint tensor functoriality;
- the fixed co-Yoneda transformation, and only later a comparison if reverse
  or eta data is needed;
- generic functor/transfor action.

### Tensor/Co-Yoneda Migration Phases

1. Inventory active diagnostics.

   Classify each co-Yoneda check as one of:

   - fixed-endpoint map computation;
   - shaped element computation;
   - deferred general-cell/equipment compatibility;
   - endpoint-changing wrapper;
   - genuine unresolved naturality theorem.

2. Confirm unit-shaped identity elements in a probe.

   First use `Prof_func_hom(M)` directly as `eta_M`. Add only transparent
   readability aliases, if useful. In particular, do not make
   `Unit_prof_id_hom(M)` or `Hom_prof_along_id_hom(G,M)` independent
   primitives.

3. Keep first-pass fixed co-Yoneda owner names.

   Start with map/cell owners, not `ProfComparison`.
   `Prof_coyoneda_cov_map(P)` and `Prof_coyoneda_con_map(P)` are stable
   diagonal projection heads for components of `Prof_coyoneda_cov_transf` and
   `Prof_coyoneda_con_transf`, not aliases of the older endpoint-changing
   names. The former
   `Prof_coyoneda_unit_tensor_cov_transf` and
   `Prof_coyoneda_unit_tensor_con_transf` compatibility surfaces have been
   retired from active code; shaped beta checks have migrated to fixed owners.

   Do not add `Prof_coyoneda_*_comparison` in the first pass. Add a comparison
   later only when a concrete consumer needs reverse beta/eta or ordinary
   inverse evidence.

4. Migrate public endpoint-changing names to wrappers.

   If endpoint-changing readable names are reintroduced later, route them
   through fixed-endpoint owners and `Prof_reindex` where possible. In the
   report notation, these wrappers are `CoyR(pp,N)` and `CoyL(pp,M)`, formerly
   represented by `Prof_coyoneda_unit_tensor_cov_transf` and
   `Prof_coyoneda_unit_tensor_con_transf`.

5. Replace shaped co-Yoneda beta checks first.

   The checks should mention `Prof_cell_apply` on shaped inputs, not direct
   `Prof_comp_transf` cancellation. Use the fixed co-Yoneda maps for the core
   beta:

   ```text
   Prof_cell_apply(
     Prof_coyoneda_cov_map(P),
     Prof_tensor_hom_hom(M,p,Prof_func_hom(M)))
   -> p

   Prof_cell_apply(
     Prof_coyoneda_con_map(P),
     Prof_tensor_hom_hom(H,Prof_func_hom(H),p))
   -> p.
   ```

   Preserve arbitrary fixed-endpoint `pp` through `tapp1_fapp0`, not through the
   old endpoint-changing `CoyR/CoyL` surfaces:

   ```text
   Prof_cell_apply(
     tapp1_fapp0(Prof_coyoneda_cov_transf(A,B), pp),
     Prof_tensor_hom_hom(M,p,Prof_func_hom(M)))
   -> Prof_cell_apply(pp,p)

   Prof_cell_apply(
     tapp1_fapp0(Prof_coyoneda_con_transf(A,B), pp),
     Prof_tensor_hom_hom(H,Prof_func_hom(H),p))
   -> Prof_cell_apply(pp,p).
   ```

   These arbitrary-`pp` rules are derived cut-elimination/fusion rules for
   fixed co-Yoneda naturality plus the direct beta, not new semantic principles.

6. Demote the broad general-cell compatibility checks.

   The checks using `Prof_tensor_hom_transf` and `Prof_tensor_transf_hom`
   belong to the old endpoint-changing/equipment presentation. They should not
   remain active beta requirements for the minimal fixed co-Yoneda core.
   Preserve their ordinary reading in the report, but remove or demote their
   runtime rewrite checks unless a current concrete consumer still needs them.

7. Remove old co-Yoneda `Prof_comp_transf` beta rules after replacement.

   The shaped pair has already moved to `Prof_cell_apply`. The remaining broad
   general-cell pair may be removed/demoted as compatibility after the fixed
   beta/fusion checks pass; do not replace it with another most-general
   endpoint-changing rule.

8. Defer any fuller general-cell theorem.

   If a later concrete consumer needs the broader equipment theorem, its
   replacement should route through fixed-endpoint co-Yoneda,
   tensor-map/naturality, `Prof_reindex_transf`, and `hom_postcomp_fapp0` or
   `ProfComparison` push/pull. The intended fixed-endpoint ingredient is
   morally:

   ```text
   Prof_tensor_map(r,s)
   epsilon^R_naturality(r)
   epsilon^L_naturality(r)
   ```

   Endpoint-changing presentations should be obtained by reindexing these
   fixed-endpoint constructions. If the replacement still requires a named
   cell-composition expression on the RHS, that name must be documented as
   derived compatibility or as a future explicit equipment theorem, not as the
   owner of co-Yoneda computation.

   This fuller theorem is no longer an immediate implementation target. It is
   a deferred compatibility/equipment task, separate from the current fixed
   co-Yoneda beta/fusion core.

   Run:

   ```text
   EMDASH_TYPECHECK_TIMEOUT=60s make check
   make warning-summary
   make ci
   ```

   Compare the warning inventory and inspect any new unresolved consumers.

## Join Target Design

### Non-Goal: No Collage Yet

This migration does not implement a semantic collage.

A collage route would require a full hom decomposition for:

```text
Collage_prof(R)
```

including same-side homs, forward cross homs from `A` to `B`, and reverse
cross homs from `B` to `A`. For `Terminal_prof(A,B)`, the reverse direction
would require an explicit empty/initial hom story or a different primitive
category presentation. That is a separate design checkpoint.

Therefore:

- do not define `Join_cat(A,B)` as a collage;
- do not claim its homs are decomposed by a collage universal property;
- do not add collage-specific beta rules as hidden implementation details.

### Primitive Join Semantics

For now, join is a primitive directed-inductive category with:

```text
Join_cat(A,B)
join_fst_func : A -> Join_cat(A,B)
join_snd_func : B -> Join_cat(A,B)
```

and a primitive internally natural family of cross arrows:

```text
join_cross_transf(A,B)
  : Terminal_prof(A,B)
    -> Hom_prof_along(join_fst_func, join_snd_func).
```

This use of a profunctor map is semantically appropriate: a natural family of
cross arrows indexed by `(a,b)` is exactly a map from the terminal profunctor
to the relevant hom profunctor.

The architecture problem is not the type of `join_cross_transf`. The problem
is making arbitrary general equipment composition the runtime owner of join's
primitive beta laws.

Ordinary mathematical notation:

```text
Join(A,B) : Cat
i_A : A -> Join(A,B)
i_B : B -> Join(A,B)
chi_{a,b} : i_A(a) -> i_B(b)
```

Internal naturality of the cross arrows is represented by one profunctor
cell:

```text
chi : Terminal_prof(A,B)
      -> Hom_prof_along(i_A,i_B).
```

For shaped probes:

```text
a : I -> A
b : I -> B
```

the desired shaped projection is:

```text
chi[a,b]
  : Unit_I -> Hom_prof_along(i_A . a, i_B . b).
```

This is the role of `join_cross_hom(a,b)`.

### Meaning Of "Narrower Than Equipment"

The target join primitive is narrower than the existing general equipment cell
even if its cross data is typed using `ProfMap`/`Prof_transf_cat`.

Existing general equipment surface:

```text
Prof_comp_transf(s,r)
```

allows arbitrary endpoint changes and arbitrary profunctor-cell composition.

Target join surface:

```text
join_cross_transf(A,B)
join_cross_hom(a,b)
join_elim_func(first,second,cross)
join_elim_cross_transf(first,second,cross)
optional join_elim_cross_hom(first,second,cross,a,b)
```

only exposes the operations required by the primitive join recursor. It should
not expose arbitrary composition of the cross cell with unrelated equipment
cells as part of the primitive join API.

In other words:

- `Prof_reindex` may still type or derive shaped projections;
- `Prof_transf_cat` may still express internal naturality;
- `Prof_comp_transf` should not own the join recursor beta law.

This is the requested stronger/narrower design.

### Join Cross Projection

Before the first implementation slice, the definition was:

```text
join_cross_hom(a,b)
  := Prof_comp_transf(join_cross_transf, Prof_terminal_hom(a,b)).
```

Implemented target:

```text
join_cross_hom(a,b) := join_cross_transf[a,b]
```

where `[-,-]` denotes the narrow terminal-source cell-evaluation operation,
not general equipment-cell composition.

Target options, in priority order:

1. Transparent projection through `Prof_cell_eval`.

   Keep the public shaped name:

   ```text
   join_cross_hom(A,B,I,a,b)
   ```

   but make it route through the narrow terminal-source evaluator:

   ```text
   join_cross_hom(a,b)
     := Prof_cell_eval(join_cross_transf,a,b).
   ```

   This keeps the current type while making `Prof_cell_eval`, not
   `Prof_comp_transf`, the runtime owner of shaped cell evaluation.

2. Direct stable shaped projection fallback.

   If the transparent `Prof_cell_eval` route fails for a concrete kernel
   reason, introduce a stable `join_cross_hom(A,B,I,a,b)` head with its
   current type and document it as the primitive shaped projection of
   `join_cross_transf`.

   Add only the projection rules actually required by join diagnostics. Do
   not add general equipment associativity to make the old definition reduce.

3. Temporary compatibility definition.

   Keep the current `Prof_comp_transf` definition only until the recursor beta
   rule is migrated. Mark it as a compatibility shim in comments and do not
   add new rules depending on this shape.

Probe order:

- first introduce `Prof_cell_apply` and transparent `Prof_cell_eval` in a
  focused probe;
- route `join_cross_hom` through `Prof_cell_eval`;
- check whether existing `join_cross_transf` and `join_cross_hom` typing
  diagnostics still cover the naturality and shaped-projection claims;
- add the direct primitive join recursor cross beta and check the shaped beta
  through `Prof_cell_eval`;
- only if that route fails, try a direct stable `join_cross_hom` fallback.

### Join Recursor Beta

Current cross beta:

```text
Prof_comp_transf(
  Prof_func_transf(join_elim_func(first,second,cross)),
  join_cross_transf)
-> cross.
```

Mathematical recursor:

```text
F : A -> E
G : B -> E
kappa : Terminal_prof(A,B) -> Hom_E(F,G)

[F,G,kappa] : Join(A,B) -> E
```

with inclusion computation:

```text
[F,G,kappa] . i_A -> F
[F,G,kappa] . i_B -> G
```

and cross-cell computation:

```text
[F,G,kappa]_*(chi) -> kappa.
```

This third beta law is necessary ordinary join-recursion semantics. It says
that the recursor sends the primitive internally natural cross-arrow family
`chi` to the supplied internally natural family `kappa`.

Kernel target:

```text
join_elim_cross_transf(F,G,kappa)
  : Obj(Prof_transf_cat E A E B Terminal_prof F Unit_prof G)

rule join_elim_cross_transf(F,G,kappa)
-> kappa.
```

This is the primitive join-eliminator cross beta. It replaces the current
expression:

```text
Prof_comp_transf(
  Prof_func_transf(join_elim_func(F,G,kappa)),
  join_cross_transf)
-> kappa
```

without preserving arbitrary equipment composition as the runtime owner. The
rule should discriminate on the primitive join recursor and the primitive
cross-cell, not on arbitrary `Prof_comp_transf`.

Why this does not require `hom_postcomp_*` / `hom_precomp_*` as the top-level
owner:

- Pointwise, the eliminated cross arrow is sent by ordinary functorial action:

  ```text
  chi_{a,b} : i_A(a) -> i_B(b)
  (J-rec(F,G,kappa))(chi_{a,b})
    : F(a) -> G(b).
  ```

- The beta law asserts that this arrow is the supplied component
  `kappa_{a,b}`. That assertion is part of the primitive join recursor, just
  as the inclusion beta laws are.
- Existing `Hom_prof_along` action already uses precomposition followed by
  postcomposition for naturality in the profunctor endpoints. The join beta
  should respect that projection ladder in shaped/naturality probes, but it
  should not be expressed by adding a broad new post/precomposition cut.
- A future reusable functor-induced representable-action owner may factor the
  pointwise action of a functor on hom profunctor cells. If such an owner is
  already easy to expose, `join_elim_cross_transf` may be a transparent view
  of its join specialization. This is a factoring option, not a prerequisite
  for the first join migration.

For shaped elements:

```text
chi[a,b]   := Prof_cell_eval(chi,a,b)
kappa[a,b] := Prof_cell_eval(kappa,a,b)

[F,G,kappa]_*(chi[a,b]) -> kappa[a,b].
```

Kernel target, using the readable view:

```text
Prof_cell_eval(
  join_elim_cross_transf(first,second,cross),a,b)
-> Prof_cell_eval(cross,a,b).
```

Therefore `join_elim_cross_hom(first,second,cross,a,b)` is not independent
mathematics. It is the component/generalized-element projection of the
cell-level beta. Prefer defining it transparently as:

```text
join_elim_cross_hom(first,second,cross,a,b)
  := Prof_cell_eval(
       join_elim_cross_transf(first,second,cross),a,b)
```

so it reduces to `Prof_cell_eval(cross,a,b)`. Add it as an independent stable
head only if a focused probe shows that the transparent term is too hard for
the kernel. The RHS must not be a final-form
`Prof_comp_transf(cross, Prof_terminal_hom(a,b))`; that expression is only a
temporary compatibility view.

### Former `Prof_func_transf` Reading In Join

Earlier checkpoints used `Prof_func_transf(F)` because applying a functor to
hom arrows was represented as a functor-induced equipment cell. That was a
reasonable temporary encoding, but it did not justify forcing the whole join
recursor through general equipment composition. The active code now uses
`Prof_func_hom` directly and has no `Prof_func_transf` symbol.

Target:

- keep former `Prof_func_transf` formulas report-level only unless a future
  theorem-specific owner is justified;
- make the primitive join beta the first-pass owner:

  ```text
  join_elim_cross_transf(first,second,cross) -> cross
  ```

- if a focused probe finds that a reusable functor-induced representable-action
  owner is already available and cheap, define `join_elim_cross_transf` as a
  transparent view of its join specialization;
- otherwise keep `join_elim_cross_transf` as the narrow primitive recursor
  projection, because `Join_cat` itself is primitive;
- use the existing `Hom_prof_along` projection ladder, including
  `hom_precomp_along_*` / `hom_postcomp_*`, only for shaped/naturality
  behavior where those heads are already the semantic owners.

### Deferred Derived Equipment Reading

The old formulation:

```text
Prof_comp_transf(
  Prof_func_transf(join_elim_func(F,G,kappa)),
  join_cross_transf)
```

was semantically meaningful. It expressed the equipment/double-category
reading of the primitive cross beta:

```text
rec(F,G,kappa)_*(chi).
```

That content is ordinary and useful as a documented derived interpretation,
but it is not needed as the primitive runtime owner. It is over-generalized
only because it makes the broad endpoint-changing composition head own a join
recursor beta.

If a future consumer needs this derived equipment reading after
`Prof_comp_transf` is deleted or demoted, do not reintroduce a broad
replacement composition head. The computational route should be a narrow
join-specific view, schematically:

```text
join_equipment_cross(F,G,kappa)
  := comp_catd_fapp0(
       Prof_reindex_transf(
         Prof_func_transf(join_elim_func(F,G,kappa)),
         join_fst_func,
         join_snd_func),
       join_cross_transf)
```

with the expected narrow reduction or proof-time comparison:

```text
join_equipment_cross(F,G,kappa)
  -> join_elim_cross_transf(F,G,kappa)
  -> kappa.
```

The exact kernel spelling must supply the product base, endpoint functors, and
inferred profunctor arguments, and must be established in a focused probe. The
important owner stack is:

```text
Prof_reindex_transf
  for endpoint change of a profunctor cell;

comp_catd_fapp0 or a narrower fixed vertical-composition view
  for vertical composition of displayed profunctor maps;

Hom_prof_along_fapp1_func
  for representable profunctor arrow action;

hom_precomp_along_* and hom_postcomp_*
  inside the Hom_prof_along projection ladder;

join_elim_cross_transf
  for the primitive join recursor beta.
```

`hom_precomp_along_*` and `hom_postcomp_*` are therefore relevant but not
sufficient by themselves: they act on ordinary hom arrows inside the
representable profunctor. The profunctor-cell-level equipment reading also
needs endpoint reindexing and vertical composition. A future reusable
functor-induced representable-action owner may replace `Prof_func_transf` in
this view, but that is a factoring improvement, not a prerequisite for the
first join migration.

Do not install a rewrite that recognizes arbitrary
`comp_catd_fapp0(Prof_reindex_transf(...),...)` as a new global equipment
composition. If computation is needed, orient only the narrow
join-equipment view above, or keep the comparison proof-time if no runtime
consumer needs it.

### Join Migration Phases

1. Introduce the narrow shaped cell-application/evaluation API.

   ```text
   Prof_cell_apply(c,r)
   ```

   Then define the terminal-source specialization:

   ```text
   Prof_cell_eval(c,a,b)
     := Prof_cell_apply(c, Prof_terminal_hom(a,b)).
   ```

   The owner must be narrower than `Prof_comp_transf`: add no general
   associativity, identity, or equipment-composition rewrite rules for
   `Prof_cell_apply`.

2. Route `join_cross_hom` through `Prof_cell_eval`.

   ```text
   join_cross_hom(a,b)
     := Prof_cell_eval(join_cross_transf,a,b).
   ```

   Keep the existing type of `join_cross_hom`.

3. Add a focused probe for the new shaped projection path.

   Keep active source unchanged. Reproduce current shaped typing checks.

4. Add the primitive join cross beta head.

   First probe whether an existing reusable representable-action owner can
   expose the needed special case without broad equipment composition. If that
   is not already available, introduce the direct join recursor projection:

   ```text
   join_elim_cross_transf(first,second,cross) -> cross
   ```

   This is not a failure to factor through hom-action infrastructure; it is
   the primitive cross beta for the primitive join eliminator.

   Then test the shaped consequence through `Prof_cell_eval`:

   ```text
   Prof_cell_eval(
     join_elim_cross_transf(first,second,cross),a,b)
   -> Prof_cell_eval(cross,a,b).
   ```

   Add `join_elim_cross_hom` only as a transparent alias or fallback stable
   head:

   ```text
   join_elim_cross_hom(first,second,cross,a,b)
     := Prof_cell_eval(
          join_elim_cross_transf(first,second,cross),a,b).
   ```

5. Migrate diagnostics.

   Replace checks whose only purpose is current `Prof_comp_transf` join beta
   with checks over the primitive join cross beta and the shaped
   `Prof_cell_eval` consequence.

   Add explicit checks that are currently missing:

   ```text
   join_elim_cross_transf(first,second,cross) ≡ cross

   Prof_cell_eval(
     join_elim_cross_transf(first,second,cross),a,b)
   ≡ Prof_cell_eval(cross,a,b)
   ```

   If the optional shaped alias is introduced, also check:

   ```text
   join_elim_cross_hom(first,second,cross,a,b)
   ≡ Prof_cell_eval(cross,a,b).
   ```

6. Remove join-specific `Prof_comp_transf` beta rules.

   Do not remove generic `Prof_comp_transf` yet. The tensor/co-Yoneda slice may
   still depend on it.

7. Defer the derived equipment reading.

   Do not try to preserve old terms of the form:

   ```text
   Prof_comp_transf(
     Prof_func_transf(join_elim_func(first,second,cross)),
     join_cross_transf)
   ```

   as canonical runtime normal forms. If a consumer later needs this view,
   add a narrow `join_equipment_cross`-style compatibility head routed through
   `Prof_reindex_transf`, fixed vertical composition, and then
   `join_elim_cross_transf`.

8. Audit whether `join_cross_hom` can remain transparent.

   Only do this if the transparent body uses a narrow application/evaluation
   owner. Do not revert to `Prof_comp_transf` as the canonical body.

## Retiring `Prof_comp_transf`

`Prof_comp_transf` has now been deleted from active runtime code. The
preconditions for that deletion were:

1. No active theorem or diagnostic uses it for weighted-limit, adjunction,
   tensor/co-Yoneda, or join beta/eta.

2. Any remaining use is either:

   - a readability wrapper around `ProfMap` and `Prof_reindex`; or
   - a genuine future equipment theorem explicitly owned by a separate plan.

3. The active checks still cover:

   - `Prof_reindex` object and arrow computation;
   - nested reindex accumulation;
   - fixed-endpoint tensor/closed beta/eta;
   - co-Yoneda beta in its fixed-endpoint owner;
   - join inclusion beta;
   - join cross beta.

4. Warning-enabled checking does not reveal a new broad composition overlap
   replacing the old one.

The active end state is:

```text
no `Prof_comp_transf` symbol in active code
```

There is no transparent compatibility alias and no narrow replacement stable
head. A future explicit equipment coherence layer may introduce new names only
under a separate plan and only for concrete consumers.

It is no longer a hidden prerequisite for the ordinary right-adjoint
weighted-limit theorem, its dual, join beta, fixed co-Yoneda beta/fusion, or
identity-normal-form computation.

## Feasibility

High feasibility:

- documenting the weighted-limit cancellation owner;
- keeping `Prof_reindex`;
- keeping the already-landed narrow `Prof_cell_apply` / `Prof_cell_eval` and
  join-recursion slices as the join runtime owners;
- keeping the already-landed fixed-endpoint `Prof_tensor_map` as the tensor
  vertical map owner;
- keeping the already-landed `Op_prof_func(A,B)` as a fixed-endpoint functor
  `Prof_cat(A,B) -> Prof_cat(Op B,Op A)`, because a focused source probe showed
  that the existing `Pullback_catd_func(Product_swap_func(B,Op A))` presentation
  makes the object action compute to `Op_prof(R)`;
- keeping `Op_prof_map(r)` as a transparent readability alias through
  `fapp1_fapp0(Op_prof_func(A,B),r)`;
- keeping the landed identity-normal-form pass: generic identity is direct
  `id_funcd`, and `Prof_id_hom` is the shaped unit identity owner;
- keeping `Prof_comp_transf` absent from active code after its successful
  deletion probe, while preserving deferred equipment readings as
  documentation-only formulas;
- keeping `Prof_id_transf`, `Prof_func_transf`, and `Op_prof_transf` absent
  from active code after their alias-retirement probe.

Medium feasibility:

- migrating endpoint-changing public co-Yoneda names to fixed-endpoint maps,
  identity-middle tensor naturality, or comparisons without reintroducing broad
  equipment composition.
- demoting the remaining broad general-cell co-Yoneda compatibility rules
  headed by `Prof_comp_transf`, while preserving only documented/deferred
  equipment readings for their fuller endpoint-changing arity. This active-code
  cleanup is now complete for the removed runtime pair and obsolete
  compatibility symbols.

Medium risk:

- `Prof_func_hom` remains the shaped representable unit owner. Historical or
  deferred formulas that mention `Prof_func_transf` should be read as report
  notation only, not as a request to restore the alias.
- `join_elim_cross_transf` must remain the primitive join recursor cross beta
  or a transparent view of an already-feasible representable-action owner. It
  must not become an arbitrary hidden equipment composite. Existing
  `hom_precomp_along_*` and `hom_postcomp_*` infrastructure should be reused
  for shaped/naturality projections where those heads are already the semantic
  owners, but they are not prerequisites for the top-level join beta.
- the deferred equipment reading of the join cross beta should use
  `Prof_reindex_transf` plus fixed vertical composition at profunctor-cell
  level, and only then the existing `Hom_prof_along` /
  `hom_precomp_along_*` / `hom_postcomp_*` projection ladder at
  representable-arrow level. It must not recreate a broad
  `Prof_comp_transf` replacement.
- `Prof_cell_apply` must stay narrow: the first implementation should add no
  general associativity, identity, or equipment-composition rewrite rules for
  it.
- retiring `Prof_id_transf` into `id_funcd` is complete. The accepted rule
  shape in the temporary bridge kept the `id_funcd` source category
  reconstructible on the LHS. That bridge and `Prof_id_transf` itself are now
  removed.
- any future endpoint-changing tensor wrapper still needs middle-change/coend
  compatibility and is outside this migration. The old `Prof_tensor_transf`
  compatibility symbol is no longer active code.
- the deleted `Prof_comp_transf` facade must not be reintroduced under a new
  name. Any future equipment-composition theorem needs a separate plan and a
  concrete consumer, and must be derived from fixed owners rather than owning
  core runtime beta laws.
- the deleted transparent aliases must not be reintroduced merely for
  readability. If a future theorem needs an endpoint-changing presentation, it
  should introduce a theorem-specific owner with a concrete consumer.

Known non-goals:

- no tensor associator/unitor coherence in this migration;
- no general coend/coinserter semantics for `Prof_tensor`;
- no semantic collage implementation for `Join_cat`;
- no full bicategory/equipment coherence layer;
- no new most-general endpoint-changing tensor primitive replacing
  `Prof_tensor_transf`.

## Implementation Order

1. Documentation and indexing.

   Promote this report and cross-link it from the DefIso migration report and
   report index. This is complete for the first pass; keep this report updated
   whenever an architectural conclusion changes.

2. Narrow cell application/evaluation first.

   Add general object-level `Prof_cell_apply`, then terminal-source
   `Prof_cell_eval`. Do not add broad equipment-style rewrite rules to either
   owner. This is the missing layer identified by the 2026-06-28
   reassessment. This first pass is complete.

3. Join migration.

   Join has the smallest semantic surface and the clearest non-collage target.
   Routing `join_cross_hom` through `Prof_cell_eval`, adding the direct
   primitive `join_elim_cross_transf` beta, and deriving the shaped beta
   through `Prof_cell_eval` should let the code remove the join-specific
   `Prof_comp_transf` rules without touching tensor. This first pass is
   complete.

4. Tensor/co-Yoneda.

   Confirm `Prof_func_hom(M)` as the canonical unit-shaped identity element,
   keep fixed-endpoint one-way co-Yoneda maps as components of
   `Prof_coyoneda_*_transf`, then migrate diagnostics for tensor-introduced
   shaped elements to `Prof_cell_apply`. Do not add co-Yoneda `ProfComparison`
   owners in the first pass. Treat broad general-cell/equipment co-Yoneda
   rules as deferred compatibility, not as core beta requirements. The first
   internal naturality-owner pass is complete: fixed unit tensor functors and
   fixed co-Yoneda transformations are active, and naturality is represented
   by generic `tapp1_fapp0` rather than external commuting-square rewrites. The
   direct fixed-map beta plus arbitrary-`pp` `tapp1_fapp0` fusion under
   `Prof_cell_apply` has landed.

5. Fixed tensor map.

   Keep `Prof_tensor_map` as the independent fixed-endpoint tensor-map owner.
   Do not define it through the former `Prof_tensor_transf`, and do not use an
   endpoint-changing tensor wrapper as the owner of fixed tensor functoriality.
   This prerequisite slice is complete.

6. Opposite fixed functor and bridge.

   Add `Op_prof_func`, add `Op_prof_map` only as a transparent alias if useful,
   then promote the normalized opposite/reindex bridge after an active-file
   warning-enabled check. Migrate diagnostics from the primitive
   `Op_prof_transf` rules to the fixed functor, the bridge, and a transparent
   endpoint-changing view. Only then demote or retire the current
   `Op_prof_transf` primitive/rules. This pass is complete:
   `Op_prof_transf` has been removed from active code after the fixed-functor
   and bridge checks landed.

7. Demote broad co-Yoneda compatibility.

   Remove or document-only demote the remaining `Prof_comp_transf`
   co-Yoneda identity-unit pair unless an active consumer requires it. Do not
   introduce a general middle-change tensor wrapper in this pass, and do not
   add a direct square rewrite for this pair. Any future fuller compatibility
   theorem must route through the internal co-Yoneda transformations, fixed
   unit tensor functors, `Prof_tensor_map`, and explicit reindexing/coherence
   data. This active-code cleanup is complete: the broad runtime pair and the
   obsolete endpoint-changing tensor/co-Yoneda compatibility symbols have been
   removed from active code.

8. `Prof_func_transf` audit.

   First pass complete: `Prof_func_hom` is the shaped hom-action owner and
   `Prof_func_transf` was temporarily a transparent compatibility view. The
   alias-retirement pass has now deleted it from active code.

9. `Prof_id_transf` normal-form pass.

   Complete. `Prof_id_transf` was temporarily a transparent `id_funcd` view
   during the bridge phase. The bridge rules, `Prof_comp_transf`, and
   `Prof_id_transf` itself have all been removed; `Prof_id_hom` remains as the
   shaped unit identity owner.

10. Generic `Prof_comp_transf` retirement.

   Complete. The generic facade, its runtime rules, and diagnostics whose only
   target was that facade have been removed from active code.

11. Transparent compatibility-alias retirement.

   Complete. `Prof_id_transf`, `Prof_func_transf`, and `Op_prof_transf` have
   been removed from active source/checks. Former endpoint-changing/equipment
   readings remain report-level historical/deferred formulas only.

## Validation Gates

For every promoted code migration:

```text
EMDASH_TYPECHECK_TIMEOUT=60s make check
python3 scripts/audit_rule_lhs.py --show-kept
EMDASH_TYPECHECK_TIMEOUT=60s make warning-summary
EMDASH_TYPECHECK_TIMEOUT=60s make ci
```

For documentation-only changes:

```text
python3 scripts/lint_report_headers.py
git diff --check
```

If diagnostics in `emdash3_2_checks.lp` are added or reorganized:

```text
make catalog
```

## Side-Task Ledger

| ID | Status | Owner | Decision / Trigger |
| --- | --- | --- | --- |
| `EQUIP-WL-DOC` | complete in this plan | DefIso/weighted-limit reports | Explicitly document that nested hom-action cancellation is required for weighted-limit beta/eta and runtime universal-property computation. |
| `EQUIP-INVENTORY` | updated by current implementation slice | this report | Active code has no `Prof_comp_transf`, `Prof_id_transf`, `Prof_func_transf`, `Op_prof_transf`, or endpoint-changing tensor/co-Yoneda compatibility symbols. Former equipment readings remain report-level historical/deferred formulas only. |
| `EQUIP-CELL-EVAL` | complete first pass | active implementation | Added general object-level `Prof_cell_apply`, defined terminal-source `Prof_cell_eval`, and routed `join_cross_hom` through `Prof_cell_eval`. |
| `EQUIP-JOIN-NARROW` | complete first pass | active implementation | Replaced join-specific `Prof_comp_transf` shaped cross and cross beta with `Prof_cell_eval` plus direct primitive `join_elim_cross_transf` beta; no `join_elim_cross_hom` alias was needed. |
| `EQUIP-JOIN-EQUIP-READING` | deferred outside active code | future compatibility probe | The old `Prof_comp_transf(Prof_func_transf(join_elim_func),join_cross_transf)` expression is historical notation only. If a later consumer needs an equipment reading, it must be rebuilt from `Prof_reindex_transf`, fixed vertical composition, `Hom_prof_along` projection, and narrow join beta under a separate theorem-specific owner. |
| `EQUIP-TENSOR-COYONEDA` | fixed beta/fusion, tensor-unit consolidation, and compatibility retirement landed | active implementation plus future cleanup | Fixed-endpoint one-way co-Yoneda maps are stable diagonal projection heads for `Prof_coyoneda_*_transf`, independent fixed-endpoint `Prof_tensor_map` is available, and fixed co-Yoneda naturality is internalized through unit tensor functors plus generic `tapp1_fapp0`. Old shaped `CoyR/CoyL` beta surfaces have been replaced by direct fixed beta and arbitrary-`pp` `tapp1_fapp0` fusion under `Prof_cell_apply`. The broad general-cell `Prof_comp_transf` co-Yoneda runtime pair and obsolete endpoint-changing tensor/co-Yoneda compatibility symbols have been removed from active code; the corresponding equipment reading is deferred documentation only. |
| `EQUIP-TENSOR-FUNC` | complete in active code | active implementation | Added `Prof_tensor_func(A,B,X)` as the fixed tensor bifunctor with projections to `Prof_tensor` and `Prof_tensor_map`. Right/left tensor-unit functors are now transparent composites through pair-insertion functors and `Prof_tensor_func`; stable `Prof_coyoneda_*_map` projection heads preserve beta/fusion runtime computation. |
| `EQUIP-OP-DUALITY` | stable primitive owner landed; alias retired | active implementation | `Op_prof` and `Op_prof_func` are stable semantic owners with object/full-arrow/capped-arrow projection rules, semantic involution, fixed-functor object action, and proof-time pullback/swap compatibility. `Op_prof_map` remains a transparent fixed-functor action view. `Op_prof_transf` has been removed from active code. |
| `EQUIP-TENSOR-TRANSF-RETIRE` | complete in active code | this report | `Prof_tensor_transf`, `Prof_tensor_hom_transf`, `Prof_tensor_transf_hom`, and the old endpoint-changing co-Yoneda constants have been removed from active code. A fuller endpoint-changing tensor theorem remains deferred because it needs middle-change/coend compatibility. |
| `EQUIP-ID-TRANSF` | complete and alias retired | identity-normal-form pass | Generic identity is direct `id_funcd`; `Prof_id_hom` remains the shaped unit identity owner. `Prof_id_transf` and the temporary `Prof_comp_transf` identity bridge have been removed from active code. |
| `EQUIP-PROF-FUNC` | core owner and uncurried projection ladder landed | active implementation | `Prof_func_hom` is now the core shaped representable unit owner, with identity computation. `Prof_func_transf` and the former representable-composition rule through `Prof_comp_transf` have been removed from active code. Object projection now exposes `fapp1_func(F,x,y)`, and product-base arrow projection is owned by nested `tapp1_fapp0` projections of `fapp1_int_transf(F)`, not by a raw naturality-square formula. |
| `EQUIP-REINDEX-PRODUCT-FOLD` | primitive `Op_prof` slice complete; raw swap naturality deferred | active implementation plus future raw-product probe | The one-off unfolded opposite/reindex bridge has been replaced by the direct semantic computation `Prof_reindex(Op_prof(...)) -> Op_prof(Prof_reindex(...))`. Broader `Product_swap_transf` / `Product_swapped_map_func` naturality remains deferred unless raw pullback/swap syntax becomes a concrete runtime consumer. |
| `EQUIP-COMP-RETIRE` | complete in active code | current implementation | `Prof_comp_transf`, its runtime rules, and checks whose sole purpose was the generic equipment-composition facade have been removed. There is no active source/check occurrence; deferred equipment readings remain report-level historical/deferred material. |
| `EQUIP-ALIAS-RETIRE` | complete in active code | current implementation | Removed transparent compatibility aliases `Prof_id_transf`, `Prof_func_transf`, and `Op_prof_transf`, plus direct checks for those aliases. Active code now implements the minimal fixed-owner design; former names remain only in reports as historical/deferred notation. |

### Reindex Product-Fold Core Review, 2026-06-29

Fresh probes after the internal fixed co-Yoneda naturality slice split the
`EQUIP-REINDEX-PRODUCT-FOLD` question into core theory and compatibility
views. Endpoint-changing equipment-style views, including `Op_prof_transf`,
should not constrain the core design; they may be deleted, retired, or kept
only as documented compatibility after the core normal forms are settled.

The broad product-map pullback folds

```text
Pullback_catd(R, Product_map_func(F,G)) -> Prof_reindex(...)
Pullback_catd_func(Product_map_func(F,G)) -> Prof_reindex_func(...)
```

can plausibly become proof-time `unif_rule`s. The temporary probe
`tmp/probes/reindex_product_unif_only_probe.lp` checked with and without
warnings, and explicit `eq_refl` witnesses elaborated across both product-map
comparisons. This would be a real normal-form-policy change: direct-authored
`Pullback_catd(Product_map_func(...))` syntax would no longer runtime-reduce to
`Prof_reindex`, so diagnostics and consumers expecting the stable runtime head
must be migrated to write `Prof_reindex` directly or use proof-time equality.

The clarified goal of this side task is stronger than merely changing the
opposite normal form. The existing specialized bridge

```text
Prof_reindex(Op_prof(R), Op_func(G), Op_func(F))
  -> Op_prof(Prof_reindex(R,F,G))
```

is currently implemented by a kernel-visible `Pullback_catd` RHS because
`Op_prof` is transparent. This comparison should remain available by ordinary
computation / `eq_refl`, but it should not be owned by a one-off rewrite rule
whose LHS repeats opposite endpoint structure in several independent
arguments.

The first general rule needed by the core layer uses the existing source
symbols directly:

```text
Prof_reindex_base_func(F,G)
  := Product_map_func(Op_func(F),G)

Prof_reindex(Pullback_catd(E,H),F,G)
  -> Pullback_catd(E, H o Prof_reindex_base_func(F,G)).
```

Its single mathematical discriminator is the profunctor argument
`Pullback_catd(E,H)`; it should not pattern-match on opposite endpoints as the
special current rule does. But this rule alone is not yet a full replacement
for the existing opposite bridge, because in the opposite case it first
computes to an accumulated base-map presentation.

For the opposite case, `Op_prof(R)` is just:

```text
Pullback_catd(R, Product_swap_func(B,Op_cat A)).
```

Therefore the general rule should compute:

```text
Prof_reindex(Op_prof(R), Op_func(G), Op_func(F))
  -> Pullback_catd(
       R,
       Product_swap_func(B,Op_cat A) o
       Prof_reindex_base_func(Op_func(G),Op_func(F))).
```

To recover the current unfolded target

```text
Op_prof(Prof_reindex(R,F,G))
```

by computation, the core calculus also needs an internal owner that normalizes
the composed base map

```text
Product_swap_func(B,Op_cat A)
  o Prof_reindex_base_func(Op_func(G),Op_func(F))
```

to the base map used by

```text
Op_prof(Prof_reindex(R,F,G)).
```

This owner must not be an external commutative-square/naturality rewrite. The
current target owner is a product-level swapped map, provisionally named:

```text
Product_swapped_map_func(F,G) : B x A -> A' x B'
Product_swapped_map_func(F,G)[b,a] = (F[a],G[b]).
```

Here `F : A -> A'` and `G : B -> B'`. This head is just the product-map
normal form for a componentwise product map whose source factors are swapped.
It is not profunctor-specific and does not mention `Op_prof` or
endpoint-changing equipment cells.

Required object and arrow projections:

```text
sigma_Fst(Product_swapped_map_func(F,G))
  -> F o Product_projR_func(B,A)

sigma_Snd(Product_swapped_map_func(F,G))
  -> G o Product_projL_func(B,A)

Product_swapped_map_func(F,G)[(b,a)]
  -> (F[a],G[b])

Product_swapped_map_func(F,G)[(q,p)]
  -> (F[p],G[q]).
```

Required product-cut accumulation rules:

```text
Product_map_func(K,L) o Product_swapped_map_func(F,G)
  -> Product_swapped_map_func(K o F, L o G)

Product_swapped_map_func(F,G) o Product_map_func(L,K)
  -> Product_swapped_map_func(F o K, G o L).
```

The second rule uses `Product_map_func(L,K)` because its source order is
`B0 x A0 -> B x A`; after the swapped map, the normalized target order is
again `A' x B'`.

Required swap/product-map cuts:

```text
Product_map_func(F,G) o Product_swap_func(B,A)
  -> Product_swapped_map_func(F,G)

Product_swap_func(B',A') o Product_map_func(G,F)
  -> Product_swapped_map_func(F,G).
```

These two rules are not a product-swap naturality square. They orient both
raw composites into the same internal product-map normal form, whose
projections, object action, arrow action, and accumulation are owned by the
product calculus itself.

Possible implementation route:

- The first probe should use `Product_swapped_map_func` as a stable product
  head, parallel to `Product_map_func`, because this is the clearest way to
  test the normal form and the two required mixed pullback/reindex rules.
- A later cleanup may instead route the same concept through a rigid
  `Product_swap_func` instance of `hom_precomp_along_fapp0` or its
  `Cat_cat` specialization, for example as the specialized presentation of
  precomposing a product map along `Product_swap_func(B,A)`. That route is
  attractive because some accumulation laws may already exist at the
  hom-action layer. It is deferred until a probe confirms that the rigid
  product-swap specialization remains visible before the current
  identity-functor precomposition rule rewrites to `hom_postcomp_fapp0`, or
  that a thin stable wrapper preserves the desired normal form.

Do not promote the migration until a focused full-source probe shows the
general pullback/reindex assertion, the mixed `Pullback_catd(Prof_reindex(...))`
assertion, the old unfolded opposite target by `eq_refl`, the product-map
proof-time equality, warning delta, and LHS audit all pass.

#### Expanded Correctness And Feasibility Assessment

Correctness:

- `Prof_reindex(R,F,G)` already means pulling `R` back along
  `Prof_reindex_base_func(F,G)`, and `Prof_reindex_base_func(F,G)` is already
  the source-level alias for `Product_map_func(Op_func(F),G)`.
- Therefore, when the profunctor argument is itself a pullback
  `Pullback_catd(E,H)`, the standard categorical computation is ordinary
  pullback accumulation:

  ```text
  Prof_reindex(Pullback_catd(E,H),F,G)
    -> Pullback_catd(E, H o Prof_reindex_base_func(F,G)).
  ```

- This is not a naturality square and not an equipment-cell law. It is the
  same Došen-style cut already used by the generic pullback accumulation rule,
  specialized to the profunctor reindexing owner.
- In kernel spelling, the expected RHS is:

  ```text
  @Pullback_catd
    (Product_cat (Op_cat A') B')
    C
    E
    (@comp_cat_fapp0
      (Product_cat (Op_cat A') B')
      (Product_cat (Op_cat A) B)
      C
      H
      (@Prof_reindex_base_func A A' B B' F G))
  ```

  where `H : Functor (Product_cat (Op_cat A) B) C` and
  `E : Catd(C)`.

Completeness:

- This rule covers the mathematical content of the current opposite/reindex
  bridge because `Op_prof(R)` is a defined pullback:

  ```text
  Op_prof(R)
    := Pullback_catd(R, Product_swap_func(B,Op_cat A)).
  ```

  Applying the general rule gives the accumulated base-map presentation of
  the same pullback.
- This is not complete by itself. The clarified goal is to remove the existing
  specialized opposite/reindex bridge while preserving the same unfolded
  target by computation / `eq_refl`. That requires a second, core owner for
  the relevant composed base map.
- The second owner must not be phrased as an external product-swap naturality
  square. It should be the product-level `Product_swapped_map_func` owner,
  with its own projections, object and arrow computation, and accumulation
  laws for composition with ordinary `Product_map_func`.
- The complete mixed accumulation calculus for this pass is:

  ```text
  Pullback_catd(Pullback_catd(E,H),K)
    -> Pullback_catd(E, H o K)

  Prof_reindex(Prof_reindex(R,F,G),F',G')
    -> Prof_reindex(R, F o F', G o G')

  Prof_reindex(Pullback_catd(E,H),F,G)
    -> Pullback_catd(E, H o Prof_reindex_base_func(F,G))

  Pullback_catd(Prof_reindex(R,F,G),H)
    -> Pullback_catd(R, Prof_reindex_base_func(F,G) o H).
  ```

  The first two rules are already active. The last two are the new core
  mixed rules needed to make the old opposite/reindex target compute without
  the specialized bridge.
- In the opposite case, both computation paths should normalize to:

  ```text
  Pullback_catd(
    R,
    Product_swapped_map_func(Op_func(F),G)).
  ```

  More explicitly:

  ```text
  Prof_reindex(Op_prof(R), Op_func(G), Op_func(F))
    -> Pullback_catd(
         R,
         Product_swap_func(B,Op_cat A)
           o Product_map_func(G,Op_func(F)))
    -> Pullback_catd(R, Product_swapped_map_func(Op_func(F),G))

  Op_prof(Prof_reindex(R,F,G))
    -> Pullback_catd(
         Prof_reindex(R,F,G),
         Product_swap_func(B',Op_cat A'))
    -> Pullback_catd(
         R,
         Product_map_func(Op_func(F),G)
           o Product_swap_func(B',Op_cat A'))
    -> Pullback_catd(R, Product_swapped_map_func(Op_func(F),G)).
  ```

  This is the regression target that replaces the existing one-off
  `Prof_reindex(Op_prof(...))` rule.
- If a later proof or API needs endpoint-changing equipment syntax, it should
  be rebuilt on top of this core computation or kept as documented-only
  compatibility; it should not determine the core normal form.
- The object-level rule should have a functor-level migration story:
  direct-authored `Pullback_catd_func(Product_map_func(...))` should become
  proof-time comparison against `Prof_reindex_func(...)`, while consumers that
  need runtime `Prof_reindex` must write `Prof_reindex` or go through
  `Prof_reindex_func`.

Rewrite hygiene:

- The intended LHS discriminator is the profunctor argument headed by
  `Pullback_catd`, not endpoint expressions such as `Op_cat B` or
  `Product_cat B (Op_cat A)`.
- A probe should first try the minimally discriminating shape:

  ```text
  rule @Prof_reindex
        $A $A' $B $B'
        (@Pullback_catd
          (Product_cat (Op_cat $A) $B)
          $C
          $E
          $H)
        $F
        $G
    ↪ ...
  ```

  The explicit `Product_cat (Op_cat A) B` source may be needed only because it
  is the source category of a profunctor over `(A,B)`, not because it is an
  independent semantic case split. If Lambdapi can infer it with `_` in a
  focused probe, prefer `_`; otherwise keep the explicit source and document
  it as a type guard, not an endpoint-shape discriminator.
- Do not add a rule whose LHS repeats opposite endpoint structure in several
  independent arguments just to recover the old opposite bridge. That is the
  pattern being retired.

Computation feasibility:

- Locally feasible part already probed: turning the broad
  `Pullback_catd(Product_map_func(...)) -> Prof_reindex(...)` and
  `Pullback_catd_func(Product_map_func(...)) -> Prof_reindex_func(...)`
  folds into `unif_rule`s checked in the source probe with warning-enabled
  checking.
- Not yet promoted: the general
  `Prof_reindex(Pullback_catd(...),F,G)` runtime rule, the mixed
  `Pullback_catd(Prof_reindex(...),H)` runtime rule, and the
  `Product_swapped_map_func` product owner with the projection/object/arrow
  and accumulation rules listed above.
- Expected fallout: checks that currently assert conversion to
  `Op_prof(Prof_reindex(...))` should remain as regression targets for the
  final replacement; checks for direct conversion from
  `Pullback_catd(Product_map_func(...))` to `Prof_reindex(...)` may need to
  become proof-time equality witnesses.
- Feasibility verdict: implementation-decision complete enough for a probe.
  The main risk is not mathematical correctness but rewrite interaction:
  `Product_swapped_map_func` must accumulate with ordinary product maps without
  creating a competing product-map/swap loop, and the mixed
  pullback/reindex rules must be checked against existing pullback,
  product-map, identity, and opposite specializations.

#### Revision: Primitive `Op_prof` First, 2026-06-30

The 2026-06-30 review refines the immediate implementation order. The
product-swap naturality problem is real: if the comparison is phrased in raw
syntax as

```text
Prof_reindex(Pullback_catd(R, Product_swap_func(...)), ...)
  =
Pullback_catd(Prof_reindex(R,...), Product_swap_func(...)),
```

then the computation necessarily involves functoriality/naturality of
`Product_swap_func`. The plan should not pretend that this question can be
avoided in the raw pullback/swap presentation.

However, the immediate profunctor-duality runtime path does not have to expose
that raw presentation. The root implementation friction is that `Op_prof` is
currently transparent:

```text
Op_prof(R) := Pullback_catd(R, Product_swap_func(B,Op_cat A)).
```

This makes every `Op_prof` computation leak into the `Pullback_catd` and
`Product_swap_func` calculus, which in turn forced the current specialized
opposite/reindex rule to recognize the unfolded pullback/swap shape.

The next implementation probe should therefore make `Op_prof` the stable
semantic owner first:

```text
Op_prof(A,B,R) : Prof(Op_cat B, Op_cat A).
```

Keep the existing `Prof`, `Prof_cat`, and `Prof_base` aliases unchanged for
this pass. Making `Prof` itself primitive, with proof-time comparison to
`Catd_cat(Product_cat(Op_cat A) B)`, is coherent long-term but is a separate
foundation-level migration, closer to the existing `Catd_cat` versus
`Functor_cat K Cat_cat` boundary. It should not be bundled into the `Op_prof`
probe.

The stable `Op_prof` probe should provide direct projection rules sufficient
to preserve existing object and arrow computations, for example:

```text
Op_prof(R)[b,a] -> R[a,b]
Op_prof(R)[q,p] -> R[p,q]
```

in kernel syntax via the existing `fapp0`, `fapp1_func`, and `fapp1_fapp0`
projection surfaces. `Op_prof_func(A,B)` should likewise become, or be probed
as, the stable fixed-endpoint functor whose object action is:

```text
fapp0(Op_prof_func(A,B), R) -> Op_prof(A,B,R).
```

`Op_prof_map(r)` should remain a transparent readability alias for the generic
action of that fixed functor:

```text
Op_prof_map(r) := fapp1_fapp0(Op_prof_func(A,B), r).
```

The semantic opposite/reindex computation should then be owned directly by
`Op_prof`:

```text
Prof_reindex(Op_prof(A,B,R), Op_func(G), Op_func(F))
  -> Op_prof(A',B', Prof_reindex(A,A',B,B',R,F,G)).
```

The promoted rule should make the main visible discriminator the profunctor
argument headed by `Op_prof`, not a pullback whose base map is headed by
`Product_swap_func`. Endpoint and `Op_func` arguments may still be needed as
type guards or to recover `F` and `G`; the probe should try `_` for
reconstructible endpoint slots first and keep explicit arguments only when
Lambdapi needs them for typing or rule compilation.

Compatibility with the old semantic presentation should be proof-time first:

```text
unif_rule
  Op_prof(A,B,R)
  ≡ Pullback_catd(R, Product_swap_func(B,Op_cat A)).
```

If the functor-level comparison is consumed, add the analogous proof-time
comparison:

```text
unif_rule
  Op_prof_func(A,B)
  ≡ Pullback_catd_func(Product_swap_func(B,Op_cat A)).
```

Both unification rules must be validated with explicit typed `eq_refl`
witnesses; a bare conversion assertion is not enough to test unification-rule
behavior. If proof-time comparison is unreliable, keep a documented
compatibility lemma/view rather than reintroducing the old unfolded runtime
rule.

If the stable `Op_prof` rule succeeds, the current specialized unfolded rule

```text
Prof_reindex(
  Pullback_catd(R, Product_swap_func(B,Op_cat A)),
  Op_func(G), Op_func(F))
->
Pullback_catd(
  Prof_reindex(R,F,G),
  Product_swap_func(B',Op_cat A'))
```

should be removed. The replacement regression target is:

```text
Prof_reindex(Op_prof(R), Op_func(G), Op_func(F))
  ≡ Op_prof(Prof_reindex(R,F,G)).
```

This is not an external product-swap naturality square. It is the internal
runtime law for the semantic opposite-profunctor operation. Direct-authored
raw pullback/swap syntax should elaborate against `Op_prof` by proof-time
compatibility where possible, but it should not determine the profunctor
duality normal form.

The broader product-swap naturality owner remains the correct general design
for raw product syntax. It should be documented and deferred unless raw
pullback/swap expressions remain concrete runtime consumers after the stable
`Op_prof` migration:

```text
Product_swap_transf
  : product formation => swapped product formation

tapp0_fapp0(Product_swap_transf,(A,B))
  = Product_swap_func(A,B)

tapp1_fapp0(Product_swap_transf,(F,G))
  = Product_swapped_map_func(F,G).
```

In this reading, `Product_swapped_map_func` is not arbitrary extra
infrastructure. It is the off-diagonal component of the internal natural
transformation expressing product symmetry. If stable heads such as
`Product_swap_func` and `Product_swapped_map_func` are retained for runtime
normal forms, their projection and accumulation rules may need to duplicate
the corresponding `tapp0_fapp0`/`tapp1_fapp0` computations as confluence
bridges, in the usual SOP style.

Immediate implementation order for the next code pass:

1. Probe stable primitive `Op_prof` and stable `Op_prof_func`.
2. Add direct object/full-arrow/capped-arrow projections for `Op_prof`.
3. Add the direct `Prof_reindex(Op_prof(...)) -> Op_prof(Prof_reindex(...))`
   computation, with the `Op_prof` argument as the real discriminator.
4. Add proof-time `Op_prof` and, if needed, `Op_prof_func` compatibility with
   the pullback/swap presentation.
5. Remove the current unfolded pullback/swap opposite/reindex rule only after
   the existing opposite/reindex diagnostic still passes by `eq_refl`.
6. Defer `Product_swap_transf` / `Product_swapped_map_func` implementation
   until a concrete raw product-swap runtime consumer remains after the
   `Op_prof` migration.

### Implementation Checkpoint, 2026-06-30, Stable `Op_prof` Owner

The primitive `Op_prof` first slice has landed.

Implemented in `emdash3_2.lp`:

- `Op_prof(A,B,R)` is now an injective stable semantic head, no longer a
  transparent definition through `Pullback_catd(R, Product_swap_func(...))`.
- `Op_prof` has direct `fapp0`, `fapp1_func`, and `fapp1_fapp0` projection
  rules. These projections compute by applying the product symmetry to the
  base argument, but the runtime owner remains `Op_prof`.
- `Op_prof(Op_prof(R)) -> R` is now owned by `Op_prof`, replacing the previous
  accidental double-swap pullback cancellation path.
- `Op_prof_func(A,B)` is now an injective stable fixed-endpoint functor, with
  object action:

  ```text
  fapp0(Op_prof_func(A,B),R) -> Op_prof(A,B,R).
  ```

- `Op_prof_map(r)` remains a transparent readability alias for
  `fapp1_fapp0(Op_prof_func(A,B),r)`.
- Proof-time compatibility identifies:

  ```text
  Op_prof(R)      == Pullback_catd(R, Product_swap_func(B,Op_cat A))
  Op_prof_func    == Pullback_catd_func(Product_swap_func(B,Op_cat A)).
  ```

- The old unfolded opposite/reindex rule over
  `Pullback_catd(R,Product_swap_func(...))` has been removed.
- The active runtime opposite/reindex computation is now:

  ```text
  Prof_reindex(Op_prof(R), Op_func(G), Op_func(F))
    -> Op_prof(Prof_reindex(R,F,G)).
  ```

Diagnostics in `emdash3_2_checks.lp` now cover:

- fixed object action of `Op_prof_func`;
- semantic involution `Op_prof(Op_prof(R)) -> R`;
- capped-arrow projection of `Op_prof`;
- explicit `eq_refl` witnesses for both proof-time pullback/swap
  compatibility rules;
- fixed type of `Op_prof_map`;
- opposite/reindex bridge conversion;
- fixed-functor identity and composition checks for `Op_prof_map`.

Validation:

```text
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
python3 scripts/audit_rule_lhs.py --show-kept
EMDASH_TYPECHECK_TIMEOUT=60s make warning-summary
```

The warning-enabled source check reports 1,382 warnings after this slice. A
HEAD snapshot of `emdash3_2.lp` reported 1,406 warnings under the same
summarizer, so the stable `Op_prof` migration removes the old high-overlap
unfolded `Prof_reindex(Pullback_catd(...Product_swap_func...))` family rather
than increasing the warning inventory.

Deferred:

- `Product_swap_transf` / `Product_swapped_map_func` remains the correct
  general owner for raw product-swap naturality, but it is not needed for the
  core profunctor-duality runtime path after this migration.
- Making `Prof`, `Prof_cat`, or `Prof_base` primitive remains a separate
  foundation-level design/probe, not part of this slice.
