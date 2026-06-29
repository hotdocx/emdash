# EMDASH v3.2 Equipment-Shadow, Tensor, Co-Yoneda, And Join Redesign Plan

Date: 2026-06-28
Last reviewed: 2026-06-29

Plan-ID: EMDASH-V3-2-EQUIPMENT-SHADOW-TENSOR-JOIN-REDESIGN-2026-06-28
Depends-On: EMDASH-V3-2-PROFUNCTOR-REPRESENTABILITY-2026-06-19; EMDASH-V3.2-DEFISO-HOM-ACTION-PROFCOMP-MIGRATION-2026-06-28; EMDASH-V3-2-PROFUNCTOR-WEIGHTED-LIMITS-2026-06-17
Supersedes: no whole report; refines the remaining equipment-cell route for tensor/co-Yoneda and primitive join in REPORT_EMDASH_V3_2_PROFUNCTOR_WEIGHTED_LIMITS_PRELIM_PLAN_2026-06-17.md
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: active-codex-session-2026-06-28
Infinity-Codex-Decision-Responses: none
Status: join, shaped co-Yoneda, and fixed-endpoint tensor-map prerequisite
slices landed; opposite fixed-functor/bridge/demotion slice landed;
`Prof_comp_transf` targeted for eventual removal but not yet safe to demote
wholesale

## Purpose

This report records the post-DefIso architecture decision for the remaining
`Prof_comp_transf` and equipment-style profunctor-cell surface.

The immediate correction already landed elsewhere:

- `Adjunction_hom_prof_comparison` is the strict `ProfComparison`/`DefIso`
  owner for the adjunction mate.
- `Adjunction_prof_transpose` and `Adjunction_prof_untranspose` are now
  transparent selected-arrow views of `defiso_to` and `defiso_from`.
- The adjunction-specific `Prof_comp_transf` cancellation rules were removed.

That correction does not mean `Prof_comp_transf` can be deleted immediately.
The active tensor/co-Yoneda and primitive join slices still use it. This plan
classifies those remaining consumers and gives the target redesign before any
further code migration.

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

   The adjunction mate no longer depends on `Prof_comp_transf`, but active
   co-Yoneda beta rules and join cross beta rules still do. Those consumers
   must be redesigned before `Prof_comp_transf` can be demoted or removed.

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
- no demotion or deletion of generic `Prof_comp_transf`, because the
  tensor/co-Yoneda compatibility rules still consume it;
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
owner needed by later co-Yoneda naturality work. The older
`Prof_tensor_transf` remains a temporary endpoint-changing primitive. The
intended future direction is to derive endpoint-changing tensor cells from
`Prof_tensor_map`, `Prof_reindex_transf`, and a settled vertical-composition
view, not to define the fixed-endpoint owner through the endpoint-changing
primitive. The remaining general-cell identity-unit naturality rules stay
under `Prof_comp_transf` until the fixed-endpoint naturality and derived
composition route has been implemented and checked.

## Reassessment Note, 2026-06-29, `Prof_id_transf`

`Prof_id_transf` was reviewed as a possible primitive shadow over the generic
`id_funcd` identity. A focused full-source probe showed that the declaration
can be made transparent:

```text
Prof_id_transf(A,B,R) := id_funcd(Prof_base(A,B),R).
```

That change was not ready to promote at this checkpoint. At the time, the
active diagnostics included the existing duality identity rule:

```text
Op_prof_transf(Prof_id_transf(R)) -> Prof_id_transf(Op_prof(R))
```

which depended on the stable `Prof_id_transf` head. Once the head unfolded to
`id_funcd`, the old rule no longer recognized the identity case. The
2026-06-29 opposite-duality slice later removed this `Op_prof_transf`
dependency by demoting `Op_prof_transf` to a transparent fixed-functor view.
The same issue remains for the `Prof_comp_transf` left/right identity rules,
which still discriminate on `Prof_id_transf`.

Conclusion:

- keep `Prof_id_transf` as a stable identity equipment head for now;
- do not treat it as the final architecture;
- migrate it only in a separate identity-normal-form pass that adds and probes
  coherent `id_funcd` sibling rules for remaining `Prof_comp_transf`
  consumers, or after those equipment heads have been demoted enough that the
  stable identity discriminator is no longer needed.

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

With that bridge, endpoint-changing opposite cells are exposed as a transparent
compatibility view:

```text
Op_prof_transf(r)
  := fapp1_fapp0(Op_prof_func(A',B'), r)
```

with the target type converted through the bridge above. The former
primitive/injective `Op_prof_transf` and its direct involution, identity, and
composition rules have been retired/demoted. Diagnostics moved to:

- fixed `Op_prof_func` object/map checks;
- the narrow reindex/swap bridge;
- any still-needed endpoint-changing view checks.

### Tensor Endpoint-Changing Cells

`Prof_tensor_map` is the fixed-endpoint vertical owner:

```text
r : ProfMap(P,P')
s : ProfMap(Q,Q')
--------------------------------
Prof_tensor_map(r,s)
  : ProfMap(P tensor Q, P' tensor Q')
```

`Prof_tensor_transf` should not be the owner of fixed-endpoint tensor
functoriality. Ultimately it should be absent from active runtime code, or kept
only as a documented future endpoint-changing compatibility view.

A full derived replacement for the current most-general `Prof_tensor_transf`
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
this migration. For the current co-Yoneda task, only identity-middle
specializations are needed. Therefore:

- keep `Prof_tensor_transf` as temporary compatibility only while existing
  general-cell co-Yoneda rules still consume it;
- do not build new code on `Prof_tensor_transf`;
- first express identity-middle co-Yoneda naturality through
  `Prof_tensor_map`, fixed co-Yoneda maps, and a narrow fixed vertical
  composition/postcomposition owner;
- after those consumers move, delete or demote `Prof_tensor_transf` rather
  than generalizing it further.

### Identity And Generic Composition

`Prof_id_transf` remains a stable head because current `Prof_comp_transf`
rules and remaining co-Yoneda compatibility consumers still discriminate on
it. The final direction is still to let `id_funcd` own vertical identity once
the remaining endpoint-changing equipment heads are demoted or have coherent
`id_funcd` normal-form sibling rules.

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
  involution, identity, or composition rewrite rules. It is a transparent
  endpoint-changing compatibility view through `Op_prof_func` plus the bridge.

Diagnostics in `emdash3_2_checks.lp` were migrated accordingly:

- fixed object action of `Op_prof_func`;
- fixed type of `Op_prof_map`;
- opposite/reindex bridge conversion;
- endpoint-changing view type for `Op_prof_transf`;
- fixed-functor identity and composition checks for `Op_prof_map`.

Validation:

```text
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog
python3 scripts/audit_rule_lhs.py --show-kept
EMDASH_TYPECHECK_TIMEOUT=60s make warning-summary
```

The warning-enabled active summary after this slice reports 1,390 warnings:
1,215 unjoinable critical-pair reports and 175 replaceable-pattern reports.
The new bridge accounts for a visible `Prof_reindex` overlap family at the
bridge owner, but the overall warning count is lower than the previous 1,415
inventory because the direct `Op_prof_transf` primitive rewrite rules were
removed.

## Current Remaining Consumers

After the first join implementation slice, the active source still has these
remaining `Prof_comp_transf` clusters.

### Generic Equipment Cell

Current declarations:

```text
Prof_comp_transf
Prof_id_transf
semantic fold from comp_catd_fapp0(Prof_reindex_transf(...), r)
left/right identity rules
```

Current role:

- provide a stable composition head for endpoint-changing cells;
- support tensor/co-Yoneda runtime cuts and generic equipment compatibility;
- expose a small amount of equipment-like syntax.

Target role:

- become a derived compatibility facade or a narrow temporary stable head;
- stop being the owner of weighted-limit, co-Yoneda, or join beta/eta when a
  better fixed-endpoint or join-specific owner exists.

Deletion status:

- not safe to delete yet;
- safe to demote only after tensor/co-Yoneda and generic compatibility
  consumers migrate.

### Opposite And Duality

Current declarations:

```text
Op_prof
Op_prof_func
Op_prof_map
Op_prof_transf
```

Current role:

- `Op_prof` is already a transparent pullback-by-swap definition on
  profunctor objects;
- `Op_prof_func` owns the fixed-endpoint vertical action of opposite;
- `Op_prof_map` is a transparent readability alias for the generic action of
  `Op_prof_func`;
- the opposite/reindex bridge converts the endpoint-changing target;
- `Op_prof_transf` is a transparent endpoint-changing compatibility view, not
  a primitive/injective rewrite owner.

Target role:

- keep this fixed-functor/bridge presentation;
- do not reintroduce direct identity, composition, or involution rewrite rules
  for `Op_prof_transf`;
- add further opposite diagnostics only at the fixed functor, bridge, or
  transparent view boundary.

Deletion status:

- `Op_prof` should remain as a defined object-level operation;
- `Op_prof_transf` has already been demoted from primitive to transparent
  compatibility view; deleting even the view is not necessary for this
  migration.

### Tensor And Co-Yoneda

Current declarations:

```text
Prof_tensor
Prof_tensor_transf
Prof_tensor_map
Prof_tensor_hom_hom
Prof_tensor_hom_transf
Prof_tensor_transf_hom
Prof_coyoneda_unit_tensor_cov_transf
Prof_coyoneda_unit_tensor_con_transf
general-cell co-Yoneda naturality rules headed by Prof_comp_transf
shaped co-Yoneda beta rules headed by Prof_cell_apply
```

Current role:

- `Prof_tensor` is an opaque coend-like profunctor composite;
- tensor introductions package either general equipment cells, shaped
  elements, or both;
- `Prof_tensor_map` exposes the fixed-endpoint vertical tensor action as a
  narrow owner independent from the endpoint-changing `Prof_tensor_transf`;
- fixed one-way co-Yoneda map aliases expose the identity-endpoint maps;
- shaped co-Yoneda beta rules cancel a tensor-introduced shaped element
  through `Prof_cell_apply`;
- the remaining general-cell identity-unit naturality rules still cancel a
  tensor-introduced general cell under `Prof_comp_transf` as temporary
  compatibility.

The co-Yoneda beta/naturality rules split into two different arities:

```text
shaped-element beta:
  Prof_tensor_hom_hom(..., p, unit)

general-cell identity-unit naturality:
  Prof_tensor_hom_transf(..., qq, unit)
  Prof_tensor_transf_hom(..., unit, qq)
```

The second pair is still identity-unit co-Yoneda, not the deferred
"general co-Yoneda along a functor" using `Prof_func_hom(F)` or
`Hom_prof_along(G,G)`. It is the ordinary naturality/functoriality form of the
unit law against a general profunctor cell. The mathematics should be
preserved, but the runtime owner should move away from generic
`Prof_comp_transf`.

Target role:

- keep `Prof_tensor` opaque until coend/coinserter semantics exists;
- put fixed-endpoint tensor and co-Yoneda structure first;
- expose endpoint-changing variants only as transparent reindexed views or
  narrowly justified wrappers;
- avoid using general equipment composition as the semantic owner of
  co-Yoneda beta;
- migrate shaped beta first through `Prof_cell_apply`;
- preserve the general-cell identity-unit naturality rules as compatibility
  until a fixed-endpoint map/naturality owner replaces their current
  `Prof_comp_transf` presentation.
- ultimately remove or demote the general-cell `Prof_comp_transf` co-Yoneda
  pair as well, but only after fixed-endpoint tensor-map/naturality and
  hom-action/postcomposition owners can express the same standard naturality.

Deletion status:

- the shaped co-Yoneda pair no longer consumes `Prof_comp_transf`;
- the general-cell identity-unit naturality pair remains a real active
  `Prof_comp_transf` consumer;
- do not delete the general-cell identity-unit naturality pair as
  mathematically unnecessary;
- replace or demote the general-cell pair only after a fixed-endpoint
  postcomposition/naturality owner exists.

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
Prof_func_transf(F)
Prof_func_hom(F) := Prof_func_transf(F)
Prof_func_transf(id) -> Prof_id_transf
Prof_comp_transf(Prof_func_transf(G), Prof_func_transf(F))
  -> Prof_func_transf(G . F)
```

Current role:

- packages the hom-action of an ordinary functor as a representable
  equipment cell;
- supports join cross beta and deferred general co-Yoneda beta.

Target role:

- audit independently from `Prof_comp_transf`;
- either replace by a fixed-endpoint representable/hom-action owner, or keep
  as a narrow compatibility cell only for consumers that genuinely require
  endpoint variation.

Deletion status:

- not safe to delete before co-Yoneda and generic compatibility consumers are
  redesigned. It is no longer a join-runtime-beta blocker.

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

Tensor should eventually have a fixed-base bifunctor:

```text
Prof_tensor_func(A,B,X)
  : Prof_cat(A,B) x Prof_cat(B,X) -> Prof_cat(A,X)
```

Its object action computes to `Prof_tensor(P,Q)`. Identity/composition should
come from the global functor calculus once this exists.

Expected fixed-endpoint map action:

```text
r : ProfMap(P,P')
s : ProfMap(Q,Q')
-------------------------------
Prof_tensor_map(r,s) : ProfMap(P tensor Q, P' tensor Q')
```

If the implementation internalizes this as a functor, the local identity and
composition laws should be inherited from the generic `fapp*` calculus.

Level 3: endpoint-changing wrappers.

Endpoint-changing tensor cells are allowed only as derived views:

```text
Prof_tensor_transf(r,s)
```

should eventually be a wrapper around reindexing plus fixed-endpoint tensor
functoriality, but only after the necessary middle-change/coend compatibility
map is explicitly available. That full wrapper is a future equipment/coend
compatibility theorem, not part of this migration. Until then,
`Prof_tensor_transf` may remain only as a temporary stable head with a clear
migration label. It should not be the primitive owner of the closed/tensor
theory, and new code should target fixed-endpoint `Prof_tensor_map` plus
identity-middle co-Yoneda naturality instead.

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

The current co-Yoneda maps are endpoint-changing:

```text
Prof_coyoneda_unit_tensor_cov_transf(pp,N)
Prof_coyoneda_unit_tensor_con_transf(pp,M)
```

In this section, write:

```text
CoyR(pp,N) := Prof_coyoneda_unit_tensor_cov_transf(pp,N)
CoyL(pp,M) := Prof_coyoneda_unit_tensor_con_transf(pp,M)
```

as mathematical aliases for the existing endpoint-changing symbols. These are
not proposed new primitives.

The fixed-endpoint co-Yoneda maps are the first one-way target owners. Use
these names in the first implementation pass:

```text
Prof_coyoneda_cov_map(P)
  : ProfMap(
      Prof_tensor(P, Unit_prof(B)),
      P)

Prof_coyoneda_con_map(P)
  : ProfMap(
      Prof_tensor(Unit_prof(A), P),
      P)
```

Ordinary mathematical notation:

```text
epsilon^R_P : P tensor_B Unit_B -> P
epsilon^L_P : Unit_A tensor_A P -> P
```

where the canonical rewrite-facing unit is:

```text
Unit_B = Unit_prof(B) = Hom_prof_along(id_B,id_B).
```

These fixed maps are the special cases:

```text
epsilon^R_P := CoyR(id_P,id_B)
epsilon^L_P := CoyL(id_P,id_A).
```

In kernel spelling these may be transparent aliases of the existing
endpoint-changing names at `pp = Prof_id_transf` and identity endpoint functor:

```text
Prof_coyoneda_cov_map(P)
  := Prof_coyoneda_unit_tensor_cov_transf(
       Prof_id_transf(A,B,P), id_B)

Prof_coyoneda_con_map(P)
  := Prof_coyoneda_unit_tensor_con_transf(
       Prof_id_transf(A,B,P), id_A).
```

The first co-Yoneda migration should use these one-way maps, not a comparison.
If inverse directions, arbitrary-map beta/eta, or ordinary inverse evidence are
later needed, introduce an explicit comparison rather than a pair of unrelated
maps:

```text
Prof_coyoneda_cov_comparison(P)
  : ProfComparison(..., Prof_tensor(P, Unit_prof), P)

Prof_coyoneda_con_comparison(P)
  : ProfComparison(..., Prof_tensor(Unit_prof, P), P)
```

A `DefIso`/`ProfComparison` owner is preferred when downstream code needs
arbitrary-map beta/eta. A plain map is enough only when the consumer needs a
single reduction direction. The first shaped co-Yoneda migration needs only the
single reduction direction.

### Unit-Shaped Identity Elements

The identity input for co-Yoneda tensor beta is not a new mathematical object.
The canonical shaped identity element of the unit profunctor is the existing:

```text
eta_M := Prof_func_hom(M)
  : Prof_hom(I,B,B,M,Unit_prof(B),M).
```

Semantically, for an arrow `u : i -> j` in the shape `I`, this element is
`M[u] : M[i] -> M[j]`. It is the shaped version of the identity element in
`Hom_B(Mi,Mi)`, with the correct action over `I`.

A readability alias may be added if it makes the implementation clearer, but
it must be transparent:

```text
Unit_prof_id_hom(M) := Prof_func_hom(M).
```

For endpoint-changing co-Yoneda along a functor `G : B -> B'`, the corresponding
identity element in the represented hom profunctor is:

```text
eta_{G,M}
  : Prof_hom(I,B,B,M,Hom_prof_along(G,G),M).
```

Semantically this is `id_{G(Mi)}` with arrow action `G[M[u]]`. After
representable reindexing, it is the same role as:

```text
Prof_func_hom(G . M)
  : Prof_hom(I,B',B',G . M,Unit_prof(B'),G . M).
```

The exact implementation may use a transparent alias such as:

```text
Hom_prof_along_id_hom(G,M) := Prof_func_hom(G . M)
```

provided a focused probe confirms the expected conversion. It should not be a
new primitive with independent computation rules.

### Co-Yoneda Beta Target

The current beta shape is:

```text
Prof_comp_transf(
  Prof_coyoneda_unit_tensor_cov_transf(pp,id),
  Prof_tensor_hom_transf(id,qq,Prof_id_hom))
-> Prof_comp_transf(pp,qq).
```

The first replacement should use the one-way map/cell owner and
`Prof_cell_apply`, preserving the current arbitrary-`pp` generality of the
shaped rules.

Right shaped beta:

```text
pp : ProfCell(P,F,P',id_B)
p  : Prof_hom(I,A,B,H,P,M)
eta_M := Prof_func_hom(M)

Prof_cell_apply(
  CoyR(pp,id_B),
  Prof_tensor_hom_hom(M,p,eta_M))
-> Prof_cell_apply(pp,p).
```

The fixed right beta is the special case `pp = id_P`, `F = id_A`:

```text
p     : Prof_hom(I,A,B,H,P,M)
eta_M : Prof_hom(I,B,B,M,Unit_prof(B),M)

Prof_cell_apply(
  epsilon^R_P,
  Prof_tensor_hom_hom(M,p,eta_M))
-> p.
```

Left shaped beta:

```text
pp : ProfCell(P,id_A,P',G)
p  : Prof_hom(I,A,B,H,P,K)
eta_H := Prof_func_hom(H)

Prof_cell_apply(
  CoyL(pp,id_A),
  Prof_tensor_hom_hom(H,eta_H,p))
-> Prof_cell_apply(pp,p).
```

The fixed left beta is the special case `pp = id_P`, `G = id_B`:

```text
p     : Prof_hom(I,A,B,H,P,K)
eta_H : Prof_hom(I,A,A,H,Unit_prof(A),H)

Prof_cell_apply(
  epsilon^L_P,
  Prof_tensor_hom_hom(H,eta_H,p))
-> p.
```

In kernel terms, the first pass should reduce through the rule owner:

```text
Prof_cell_apply(CoyR/CoyL, Prof_tensor_hom_hom(...))
```

not through `Prof_comp_transf`. A later `ProfComparison` variant may use
`prof_comparison_push/pull` or direct `hom_postcomp_fapp0` accumulation when
reverse beta/eta or arbitrary incoming-map cancellation becomes a concrete
consumer.

The ordinary pointwise formula for the right map remains:

```text
epsilon^R_P([x,u]) = P(1,u)(x)
```

The beta rule above is its identity/hom-action shaped specialization. There is
no separate `I tensor I` shape: `Prof_tensor_hom_hom` composes two shaped
elements over the same shape `I` and the same middle probe `M`. The shape is a
context category, not a tensor factor.

### General-Cell Identity-Unit Naturality

The active co-Yoneda rules using:

```text
Prof_tensor_hom_transf
Prof_tensor_transf_hom
```

are a different arity of the same identity-unit co-Yoneda story. They are not
the later generalized co-Yoneda-along-a-functor task. They express naturality of
the unit co-Yoneda map against a general profunctor cell.

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

This content is mathematically standard and should be preserved. The important
distinction is between the required mathematics and the current constructor
generality.

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

The active general-cell rules are exactly endpoint-changing identity-unit
specializations of these formulas. Their current syntax uses
`Prof_tensor_hom_transf` and `Prof_tensor_transf_hom`, but the co-Yoneda
consumers instantiate those mixed constructors only as:

```text
qq tensor id_Unit_B
id_Unit_A tensor qq.
```

Therefore `Prof_tensor_hom_transf` and `Prof_tensor_transf_hom` are
semantically admissible current shims, not evidence that the final architecture
needs their full mixed "general cell plus shaped element" generality as a
primitive owner.

What must change is the runtime owner. The current implementation owns these
reductions by broad `Prof_comp_transf` rules. The target owner should instead
be built from:

- fixed-endpoint co-Yoneda owner, using a one-way map first and a
  `ProfComparison` only for later reverse beta/eta or ordinary evidence needs;
- fixed-endpoint tensor functoriality, preferably `Prof_tensor_func`, or a
  narrow tensor map owner such as `Prof_tensor_map`;
- `Prof_reindex_transf` for endpoint changes;
- `hom_postcomp_fapp0` or the corresponding `ProfComparison` push/pull;
- a derived/compatibility expression for the final composed cell, until a
  narrower public cell-composition story is settled.

Therefore the first tensor/co-Yoneda migration should not delete these two
general-cell rules. It should mark them as compatibility rules and replace them
only after the fixed-endpoint map/naturality path is implemented and checked.

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
fixed co-Yoneda owner: one-way map first, `ProfComparison` only when a reverse
or arbitrary-map consumer actually requires it.

If no, the task is not merely "general co-Yoneda"; it is a real
endpoint-changing naturality theorem. That theorem may deserve a narrow
public wrapper, but it should still be derived from:

- `Prof_reindex`;
- fixed-endpoint `ProfMap`;
- fixed-endpoint tensor functoriality;
- the co-Yoneda comparison;
- generic functor/transfor action.

### Tensor/Co-Yoneda Migration Phases

1. Inventory active diagnostics.

   Classify each co-Yoneda check as one of:

   - fixed-endpoint map computation;
   - shaped element computation;
   - general-cell identity-unit naturality;
   - endpoint-changing wrapper;
   - genuine unresolved naturality theorem.

2. Confirm unit-shaped identity elements in a probe.

   First use `Prof_func_hom(M)` directly as `eta_M`. Add only transparent
   readability aliases, if useful. In particular, do not make
   `Unit_prof_id_hom(M)` or `Hom_prof_along_id_hom(G,M)` independent
   primitives.

3. Add first-pass one-way co-Yoneda owner names.

   Start with map/cell owners, not `ProfComparison`. Add
   `Prof_coyoneda_cov_map(P)` and `Prof_coyoneda_con_map(P)` as transparent
   fixed-endpoint aliases of the existing endpoint-changing co-Yoneda names at
   `pp = Prof_id_transf` and identity endpoint functor. Keep
   `Prof_coyoneda_unit_tensor_cov_transf` and
   `Prof_coyoneda_unit_tensor_con_transf` as the arbitrary-`pp` cell owners for
   the first shaped beta migration.

   Do not add `Prof_coyoneda_*_comparison` in the first pass. Add a comparison
   later only when a concrete consumer needs reverse beta/eta or ordinary
   inverse evidence.

4. Migrate public endpoint-changing names to wrappers.

   Preserve readable names, but route them through fixed-endpoint owners and
   `Prof_reindex` where possible. In the report notation, these wrappers are
   `CoyR(pp,N)` and `CoyL(pp,M)`, corresponding to the existing
   `Prof_coyoneda_unit_tensor_cov_transf` and
   `Prof_coyoneda_unit_tensor_con_transf` symbols.

5. Replace shaped co-Yoneda beta checks first.

   The checks should mention `Prof_cell_apply` on shaped inputs, not direct
   `Prof_comp_transf` cancellation. Preserve arbitrary `pp`:

   ```text
   Prof_cell_apply(
     CoyR(pp,id_B),
     Prof_tensor_hom_hom(M,p,Prof_func_hom(M)))
   -> Prof_cell_apply(pp,p)

   Prof_cell_apply(
     CoyL(pp,id_A),
     Prof_tensor_hom_hom(H,Prof_func_hom(H),p))
   -> Prof_cell_apply(pp,p).
   ```

   The fixed `epsilon` beta checks are special cases of these rules.

6. Preserve the general-cell identity-unit naturality checks as compatibility.

   The checks using `Prof_tensor_hom_transf` and `Prof_tensor_transf_hom` are
   standard co-Yoneda naturality content, but only in the narrow identity-unit
   specializations `qq tensor id_Unit_B` and `id_Unit_A tensor qq`. Do not delete
   them merely because their current owner is `Prof_comp_transf`; doing so would
   lose a real naturality theorem. Also do not promote their full current
   mixed-constructor generality as the final design. Mark their current
   presentation as temporary compatibility scaffolding and replace it only
   after a fixed-endpoint tensor-map/naturality owner is available.

7. Remove the shaped co-Yoneda `Prof_comp_transf` beta rules after replacement.

   Remove only the shaped pair in this first pass. Do not remove the
   general-cell pair yet.

8. Later replace the general-cell identity-unit naturality rules.

   The later replacement should route through fixed-endpoint co-Yoneda,
   tensor-map/naturality, `Prof_reindex_transf`, and `hom_postcomp_fapp0` or
   `ProfComparison` push/pull. The intended fixed-endpoint replacement is
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

   This is still part of the plan to delete or demote `Prof_comp_transf`
   ultimately. The instruction to leave the two general-cell co-Yoneda rules
   in place is temporary sequencing: they stay only until their standard
   naturality content is re-expressed via fixed-endpoint tensor-map/naturality,
   `Prof_reindex_transf`, and `hom_postcomp_fapp0` / DefIso-style
   cut-elimination owners.

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

### Prof_func_transf In Join

`Prof_func_transf(F)` currently appears because applying a functor to hom
arrows is represented as a functor-induced equipment cell. That is a
reasonable temporary encoding, but it should not force the whole join recursor
through general equipment composition.

Target:

- keep `Prof_func_transf` only as a compatibility cell while needed;
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

`Prof_comp_transf` can be deleted or demoted only when all of these are true:

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

A plausible end state is:

```text
Prof_comp_transf
```

is either:

- absent from active runtime code;
- a transparent compatibility alias that cannot head rewrite rules; or
- a narrowly documented stable head used only by a future explicit equipment
  coherence layer.

It should not be a hidden prerequisite for the ordinary right-adjoint
weighted-limit theorem or its dual.

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
- keeping `Op_prof_transf` as a transparent endpoint-changing view rather than
  a primitive rewrite owner.

Medium feasibility:

- migrating endpoint-changing public co-Yoneda names to fixed-endpoint maps,
  identity-middle tensor naturality, or comparisons without reintroducing broad
  equipment composition.
- replacing the remaining general-cell identity-unit co-Yoneda naturality
  rules headed by `Prof_comp_transf`, because their mathematical content is
  real but their current owner is temporary compatibility scaffolding.

Medium risk:

- `Prof_func_transf` may need a better representable hom-action owner before
  both general co-Yoneda and join can become clean.
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
- retiring `Prof_id_transf` into `id_funcd` is blocked by stable-head
  identity rules for the current `Prof_comp_transf` surface and remaining
  compatibility consumers. It should move only after those surfaces are
  demoted, or after coherent `id_funcd` sibling rules are probed.
- retiring `Prof_tensor_transf` is blocked by the remaining identity-middle
  co-Yoneda naturality consumers. A full endpoint-changing tensor wrapper also
  needs middle-change/coend compatibility and is outside this migration.
- demoting or deleting `Prof_comp_transf` remains the last cleanup pass,
  because it also supports generic equipment compatibility checks and current
  identity/composition normal forms.

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
   add fixed-endpoint one-way co-Yoneda map aliases, then migrate diagnostics
   for tensor-introduced shaped elements to `Prof_cell_apply`. Do not add
   co-Yoneda `ProfComparison` owners in the first pass. Preserve the
   general-cell identity-unit naturality rules as temporary compatibility until
   fixed-endpoint tensor/co-Yoneda naturality owners replace them.

5. Fixed tensor map.

   Keep `Prof_tensor_map` as the independent fixed-endpoint tensor-map owner.
   Do not define it through `Prof_tensor_transf`, and do not use
   `Prof_tensor_transf` as the owner of fixed tensor functoriality. This
   prerequisite slice is complete.

6. Opposite fixed functor and bridge.

   Add `Op_prof_func`, add `Op_prof_map` only as a transparent alias if useful,
   then promote the normalized opposite/reindex bridge after an active-file
   warning-enabled check. Migrate diagnostics from the primitive
   `Op_prof_transf` rules to the fixed functor, the bridge, and a transparent
   endpoint-changing view. Only then demote or retire the current
   `Op_prof_transf` primitive/rules. This first pass is complete:
   `Op_prof_transf` is now a transparent view and no direct rules remain.

7. Identity-middle co-Yoneda naturality.

   Replace the remaining `Prof_comp_transf` co-Yoneda identity-unit naturality
   pair through fixed-endpoint co-Yoneda maps, `Prof_tensor_map`, and a narrow
   fixed vertical composition/postcomposition owner. Do not introduce a general
   middle-change tensor wrapper in this pass.

8. `Prof_func_transf` audit.

   Decide whether it remains a narrow representable equipment compatibility
   cell or is replaced by a hom-action owner.

9. `Prof_id_transf` normal-form pass.

   Retry the transparent `id_funcd` migration only after enough
   `Prof_comp_transf` consumers have been demoted, or after coherent
   `id_funcd` sibling rules have passed focused probes.

10. Generic `Prof_comp_transf` retirement.

   Only after join, opposite, tensor/co-Yoneda, and identity-normal-form
   consumers no longer rely on it.

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
| `EQUIP-INVENTORY` | updated by first implementation slice | this report | Maintain the remaining `Prof_comp_transf` consumer classification before code deletion; join-specific runtime ownership has moved off `Prof_comp_transf`, while tensor/co-Yoneda and generic equipment compatibility remain. |
| `EQUIP-CELL-EVAL` | complete first pass | active implementation | Added general object-level `Prof_cell_apply`, defined terminal-source `Prof_cell_eval`, and routed `join_cross_hom` through `Prof_cell_eval`. |
| `EQUIP-JOIN-NARROW` | complete first pass | active implementation | Replaced join-specific `Prof_comp_transf` shaped cross and cross beta with `Prof_cell_eval` plus direct primitive `join_elim_cross_transf` beta; no `join_elim_cross_hom` alias was needed. |
| `EQUIP-JOIN-EQUIP-READING` | deferred | future compatibility probe | Preserve the old `Prof_comp_transf(Prof_func_transf(join_elim_func),join_cross_transf)` expression only as a derived equipment reading, routed through `Prof_reindex_transf`, fixed vertical composition, `Hom_prof_along` projection, and narrow join beta if a later consumer needs computation. |
| `EQUIP-TENSOR-COYONEDA` | partial first pass complete | active implementation plus future probe | Fixed-endpoint one-way co-Yoneda map aliases are active, arbitrary-`pp` shaped beta is expressed via `Prof_cell_apply`, and independent fixed-endpoint `Prof_tensor_map` is available as a prerequisite; general-cell identity-unit naturality remains temporary `Prof_comp_transf` compatibility until fixed-endpoint naturality plus hom-action cut-elimination owners replace it. |
| `EQUIP-OP-DUALITY` | complete first pass | active implementation | `Op_prof` remains defined by pullback/swap; fixed-endpoint `Op_prof_func`, transparent `Op_prof_map`, and the normalized opposite/reindex bridge are active; primitive `Op_prof_transf` has been demoted to a transparent endpoint-changing view with diagnostics migrated to fixed-functor/bridge checks. |
| `EQUIP-TENSOR-TRANSF-RETIRE` | decision complete, blocked by remaining consumers | future tensor/co-Yoneda pass | Treat `Prof_tensor_transf` as temporary compatibility only. Do not build new code on it. Remove or document-only demote it after identity-middle co-Yoneda naturality is expressed through `Prof_tensor_map`, fixed co-Yoneda maps, and narrow postcomposition/cut-elimination owners. |
| `EQUIP-ID-TRANSF` | deferred after probe | future identity-normal-form pass | Transparent `Prof_id_transf := id_funcd(Prof_base(A,B),R)` source probe succeeded; the opposite-duality dependency has been removed, but active `Prof_comp_transf` identity rules and remaining compatibility consumers still need a stable identity head. Migrate only with coherent `id_funcd` sibling rules or after those equipment heads are demoted. |
| `EQUIP-PROF-FUNC` | proposed | future implementation probe | Audit `Prof_func_transf` as representable hom-action compatibility, especially for general co-Yoneda and join; add only transparent aliases for `Unit_prof_id_hom` / `Hom_prof_along_id_hom` if probes justify them. |
| `EQUIP-COMP-RETIRE` | blocked on previous tasks | future cleanup | Demote or remove `Prof_comp_transf` only after join, opposite, tensor/co-Yoneda, and identity-normal-form consumers no longer consume it. |
