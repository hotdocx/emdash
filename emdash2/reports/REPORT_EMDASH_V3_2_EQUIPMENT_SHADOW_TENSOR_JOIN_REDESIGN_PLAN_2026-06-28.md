# EMDASH v3.2 Equipment-Shadow, Tensor, Co-Yoneda, And Join Redesign Plan

Date: 2026-06-28
Last reviewed: 2026-06-28

Plan-ID: EMDASH-V3-2-EQUIPMENT-SHADOW-TENSOR-JOIN-REDESIGN-2026-06-28
Depends-On: EMDASH-V3-2-PROFUNCTOR-REPRESENTABILITY-2026-06-19; EMDASH-V3.2-DEFISO-HOM-ACTION-PROFCOMP-MIGRATION-2026-06-28; EMDASH-V3-2-PROFUNCTOR-WEIGHTED-LIMITS-2026-06-17
Supersedes: no whole report; refines the remaining equipment-cell route for tensor/co-Yoneda and primitive join in REPORT_EMDASH_V3_2_PROFUNCTOR_WEIGHTED_LIMITS_PRELIM_PLAN_2026-06-17.md
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: active-codex-session-2026-06-28
Infinity-Codex-Decision-Responses: none
Status: proposed detailed redesign plan; documentation only, no `Prof_comp_transf` retirement promoted yet

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
  implementation-complete: a narrow cell-evaluation or shaped-projection
  operation.

The main risk is not that `Prof_reindex` is semantically wrong. It is not. The
main risk is that some current `Prof_comp_transf` uses are really two
operations collapsed into one:

```text
1. endpoint-changing composition of profunctor cells;
2. evaluation/projection of an internally natural profunctor cell at a shaped
   probe.
```

If the second operation is not named directly, an implementation can easily
reintroduce `Prof_comp_transf` under another name. Therefore the plan should
treat the narrow shaped-projection layer as a prerequisite for the join
migration and as a likely helper for endpoint-changing co-Yoneda wrappers.

Refined target stack:

```text
fixed-endpoint ProfMap core
  -> Prof_reindex as legitimate change of base
  -> narrow shaped/cell projection APIs
  -> optional endpoint-changing wrappers
  -> future explicit equipment coherence, only if needed
```

This is the intended distinction between ordinary profunctor mathematics and
the old over-generalized equipment-style runtime story.

## Current Remaining Consumers

The active source currently has these `Prof_comp_transf` clusters.

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
- support old co-Yoneda and join runtime cuts;
- expose a small amount of equipment-like syntax.

Target role:

- become a derived compatibility facade or a narrow temporary stable head;
- stop being the owner of weighted-limit, co-Yoneda, or join beta/eta when a
  better fixed-endpoint or join-specific owner exists.

Deletion status:

- not safe to delete yet;
- safe to demote only after tensor/co-Yoneda and join consumers migrate.

### Tensor And Co-Yoneda

Current declarations:

```text
Prof_tensor
Prof_tensor_transf
Prof_tensor_hom_hom
Prof_tensor_hom_transf
Prof_tensor_transf_hom
Prof_coyoneda_unit_tensor_cov_transf
Prof_coyoneda_unit_tensor_con_transf
co-Yoneda beta rules headed by Prof_comp_transf
```

Current role:

- `Prof_tensor` is an opaque coend-like profunctor composite;
- tensor introductions package either general equipment cells, shaped
  elements, or both;
- co-Yoneda beta rules cancel a tensor introduction against a named
  co-Yoneda unit map in the identity-representable case.

Target role:

- keep `Prof_tensor` opaque until coend/coinserter semantics exists;
- put fixed-endpoint tensor and co-Yoneda structure first;
- expose endpoint-changing variants only as transparent reindexed views or
  narrowly justified wrappers;
- avoid using general equipment composition as the semantic owner of
  co-Yoneda beta.

Deletion status:

- current `Prof_comp_transf` beta rules are real active consumers;
- replace them after fixed-endpoint co-Yoneda owners exist and diagnostics are
  migrated.

### Shaped Cell Evaluation / Projection

Current implicit role:

- `join_cross_hom(a,b)` is currently implemented by composing
  `join_cross_transf` with `Prof_terminal_hom(a,b)` through
  `Prof_comp_transf`;
- endpoint-changing tensor and co-Yoneda wrappers also often need to apply a
  natural profunctor cell to a shaped probe.

Target role:

- introduce or identify a narrow owner for evaluating an internally natural
  profunctor cell at shaped endpoint probes;
- do not use arbitrary equipment-cell composition merely to obtain this
  shaped projection.

Mathematical shape:

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

Possible kernel names are deliberately provisional:

```text
Prof_cell_eval
Prof_cell_hom
Prof_transf_eval_hom
```

or, for the first migration, a join-specific projection head:

```text
join_cross_hom(A,B,I,a,b).
```

Decision status:

- this layer is required for a clean join migration;
- its exact kernel name and generality are not yet decision-complete;
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

- not safe to delete before join and co-Yoneda are redesigned.

### Primitive Join

Current declarations:

```text
Join_cat(A,B)
join_fst_func : A -> Join_cat(A,B)
join_snd_func : B -> Join_cat(A,B)
join_cross_transf
join_cross_hom(a,b) := Prof_comp_transf(join_cross_transf, terminal)
join_elim_func(first,second,cross)
cross beta rules headed by Prof_comp_transf
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

- current shaped cross and cross beta still depend on `Prof_comp_transf`;
- migrate join before deleting the generic composition head.

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

should be a wrapper around reindexing plus fixed-endpoint tensor functoriality,
or remain a temporary stable head with a clear migration label. It should not
be the primitive owner of the closed/tensor theory.

Expected shaped tensor introduction:

```text
p : Unit_I -> P[F,M]
q : Unit_I -> Q[M,G]
-------------------------------
p tensor_M q : Unit_I -> (P tensor Q)[F,G]
```

This is the mathematical content currently carried by names like
`Prof_tensor_hom_hom`. Its computation should be owned by tensor/co-Yoneda
heads or by the narrow shaped-projection layer, not by generic
`Prof_comp_transf`.

### Co-Yoneda API

The current co-Yoneda maps are endpoint-changing:

```text
Prof_coyoneda_unit_tensor_cov_transf(pp,N)
Prof_coyoneda_unit_tensor_con_transf(pp,M)
```

The target design introduces fixed-endpoint co-Yoneda comparisons first. Use
names to be confirmed by probe, for example:

```text
Prof_coyoneda_cov_map(P)
  : ProfMap(
      Prof_tensor(P, Hom_prof_along(id,id)),
      P)

Prof_coyoneda_con_map(P)
  : ProfMap(
      Prof_tensor(Hom_prof_along(id,id), P),
      P)
```

Ordinary mathematical notation:

```text
epsilon^R_P : P tensor_B Unit_B -> P
epsilon^L_P : Unit_A tensor_A P -> P
```

where the canonical rewrite-facing unit is:

```text
Unit_B = Hom_prof_along(id_B,id_B).
```

If inverse directions are needed, introduce an explicit comparison rather
than a pair of unrelated maps:

```text
Prof_coyoneda_cov_comparison(P)
  : ProfComparison(..., Prof_tensor(P, Unit_prof), P)

Prof_coyoneda_con_comparison(P)
  : ProfComparison(..., Prof_tensor(Unit_prof, P), P)
```

A `DefIso`/`ProfComparison` owner is preferred when downstream code needs
arbitrary-map beta/eta. A plain map is enough only when the consumer needs a
single reduction direction.

### Co-Yoneda Beta Target

The current beta shape is:

```text
Prof_comp_transf(
  Prof_coyoneda_unit_tensor_cov_transf(pp,id),
  Prof_tensor_hom_transf(id,qq,Prof_id_hom))
-> Prof_comp_transf(pp,qq).
```

The target fixed-endpoint shape should instead be:

```text
prof_comparison_push(
  Prof_coyoneda_cov_comparison(P),
  Prof_tensor_intro(...))
-> ...
```

or, if only one direction is needed:

```text
hom_postcomp_fapp0(id, Prof_coyoneda_cov_map(P), tensor_intro(...))
-> ...
```

The important point is that the cancellation owner is the co-Yoneda
comparison or map, not a general equipment-cell composition law.

Expected shaped beta rules:

```text
epsilon^R_P(p tensor_M id_M) -> p
epsilon^L_P(id_M tensor_M p) -> p
```

In kernel terms, these should reduce through either:

```text
hom_postcomp_fapp0(id, Prof_coyoneda_*_map(P), ...)
```

or:

```text
prof_comparison_push(Prof_coyoneda_*_comparison(P), ...)
```

depending on whether the chosen owner is a one-way map or a
`ProfComparison`.

Endpoint-changing public names can then be definitions:

```text
Prof_coyoneda_unit_tensor_cov_transf(pp,N)
  := reindex/fmap/view of Prof_coyoneda_cov_map or comparison

Prof_coyoneda_unit_tensor_con_transf(pp,M)
  := reindex/fmap/view of Prof_coyoneda_con_map or comparison.
```

### General Co-Yoneda Along A Functor

The old deferred task was to generalize identity-representable beta using:

```text
Prof_func_hom(F)
```

Do not implement that by adding more `Prof_comp_transf` laws. The design
question is first:

```text
Is the consumer fixed-endpoint after reindexing?
```

If yes, use `Prof_reindex` to put the target in a fixed endpoint and apply the
fixed co-Yoneda comparison.

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
   - endpoint-changing wrapper;
   - genuine unresolved naturality theorem.

2. Add fixed-endpoint co-Yoneda owner names in a probe.

   Start with identity-representable cases only. Probe whether a map or
   `ProfComparison` is the better owner by checking the current beta
   assertions after rewriting them away from `Prof_comp_transf`.

3. Migrate public endpoint-changing names to wrappers.

   Preserve readable names, but route them through fixed-endpoint owners and
   `Prof_reindex` where possible.

4. Replace active co-Yoneda beta checks.

   The checks should mention `prof_comparison_push/pull` or
   `hom_postcomp_fapp0`, not direct `Prof_comp_transf` cancellation.

5. Remove the four co-Yoneda `Prof_comp_transf` beta rules.

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
join_elim_cross_beta(first,second,cross)
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

The current definition is:

```text
join_cross_hom(a,b)
  := Prof_comp_transf(join_cross_transf, Prof_terminal_hom(a,b)).
```

Refined target:

```text
join_cross_hom(a,b) := join_cross_transf[a,b]
```

where `[-,-]` denotes the narrow shaped cell-evaluation/projection operation,
not general equipment-cell composition.

Target options, in priority order:

1. Direct shaped projection head.

   Introduce a stable head:

   ```text
   join_cross_hom(A,B,I,a,b)
   ```

   with its current type. Treat it as the primitive shaped projection of
   `join_cross_transf`.

   Add only the projection rules actually required by join diagnostics. Do
   not add general equipment associativity to make the old definition reduce.

2. Transparent projection through a narrow `ProfMap`/`Prof_hom` owner.

   If existing projection infrastructure can extract a shaped element from
   `join_cross_transf` without using `Prof_comp_transf`, keep
   `join_cross_hom` transparent through that narrower owner.

3. Temporary compatibility definition.

   Keep the current `Prof_comp_transf` definition only until the recursor beta
   rule is migrated. Mark it as a compatibility shim in comments and do not
   add new rules depending on this shape.

Probe order:

- first try a direct stable `join_cross_hom` declaration with no definition;
- add the recursor shaped beta rule against that stable head;
- check whether existing `join_cross_transf` typing checks still cover the
  naturality claim;
- only then consider a transparent projection implementation.

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
join_elim(first,second,cross) : Join(A,B) -> E
```

with inclusion computation:

```text
join_elim(first,second,cross) . i_A -> first
join_elim(first,second,cross) . i_B -> second
```

Target beta should be join-specific:

```text
join_elim_cross_transf(first,second,cross)
  -> cross
```

or, if no public head is needed:

```text
join_cross_action(join_elim_func(first,second,cross), join_cross_transf)
  -> cross.
```

The name is less important than the ownership. The rule should discriminate
on `join_elim_func` and `join_cross_transf`, not on arbitrary
`Prof_comp_transf`.

For shaped elements:

```text
join_elim_cross_hom(first,second,cross,a,b)
  -> cross[a,b].
```

Equivalently, using ordinary notation:

```text
join_elim(first,second,cross)_*(chi_{a,b}) -> cross_{a,b}.
```

The RHS should be the same narrow shaped evaluation of the supplied `cross`
cell, not a general `Prof_comp_transf(cross, Prof_terminal_hom(a,b))` normal
form. During migration, the old expression may remain a temporary
compatibility view, but it must not be the final runtime owner.

### Prof_func_transf In Join

`Prof_func_transf(F)` currently appears because applying a functor to a hom
profunctor is represented as a functor-induced equipment cell. That is a
reasonable temporary encoding, but it should not force the whole join recursor
through general equipment composition.

Target:

- keep `Prof_func_transf` only as a compatibility cell while needed;
- prefer a narrower representable hom-action owner for:

  ```text
  Hom_prof_along(join_fst,join_snd)
  -> Hom_prof_along(first,second)
  ```

  induced by `join_elim_func(first,second,cross)`;
- route join beta through the narrow owner.

### Join Migration Phases

1. Decide the narrow shaped cell-evaluation/projection API.

   Either introduce a general but narrow owner such as:

   ```text
   Prof_cell_eval(c,a,b)
   ```

   or keep the first implementation join-specific:

   ```text
   join_cross_hom(A,B,I,a,b).
   ```

   The chosen owner must be narrower than `Prof_comp_transf`.

2. Add a probe with direct `join_cross_hom` as a stable shaped projection.

   Keep active source unchanged. Reproduce current shaped typing checks.

3. Add a join-specific cross-transf action head or beta head.

   Test:

   ```text
   join_elim_cross_transf(first,second,cross) -> cross
   join_elim_cross_hom(first,second,cross,a,b) -> cross[a,b]
   ```

4. Migrate diagnostics.

   Replace checks whose only purpose is current `Prof_comp_transf` join beta
   with checks over the join-specific heads.

5. Remove join-specific `Prof_comp_transf` beta rules.

   Do not remove generic `Prof_comp_transf` yet. The tensor/co-Yoneda slice may
   still depend on it.

6. Audit whether `join_cross_hom` can become transparent again.

   Only do this if the transparent body uses a narrow projection owner. Do not
   revert to `Prof_comp_transf` as the canonical body.

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
- adding fixed-endpoint co-Yoneda owner names in a future implementation
  validation pass;
- adding a join-specific shaped projection or a narrow cell-evaluation owner.

Medium feasibility:

- migrating active co-Yoneda beta rules away from `Prof_comp_transf`, because
  the current rules simultaneously encode co-Yoneda cancellation, tensor
  introduction, endpoint reindexing, and shaped-element specialization.
- replacing join cross beta without a disguised `Prof_comp_transf`, because
  the RHS needs a real narrow shaped evaluation of the supplied `cross` cell.

Medium risk:

- `Prof_func_transf` may need a better representable hom-action owner before
  both general co-Yoneda and join can become clean.
- the exact generality of `Prof_cell_eval` is not yet settled. Too narrow a
  head duplicates join-specific logic; too broad a head recreates equipment
  composition.

Known non-goals:

- no tensor associator/unitor coherence in this migration;
- no general coend/coinserter semantics for `Prof_tensor`;
- no semantic collage implementation for `Join_cat`;
- no full bicategory/equipment coherence layer.

## Implementation Order

1. Documentation and indexing.

   Promote this report and cross-link it from the DefIso migration report and
   report index.

2. Narrow cell evaluation first.

   Decide whether the first owner is general (`Prof_cell_eval`) or
   join-specific (`join_cross_hom`). This is the missing layer identified by
   the 2026-06-28 reassessment.

3. Join migration.

   Join has the smallest semantic surface and the clearest non-collage target.
   A direct `join_cross_hom` / shaped cell-evaluation owner plus
   join-specific beta head should let the code remove the join-specific
   `Prof_comp_transf` rules without touching tensor.

4. Tensor/co-Yoneda.

   Introduce fixed-endpoint co-Yoneda map/comparison owners and migrate
   diagnostics. Keep endpoint-changing public names as wrappers until their
   consumers are gone.

5. `Prof_func_transf` audit.

   Decide whether it remains a narrow representable equipment compatibility
   cell or is replaced by a hom-action owner.

6. Generic `Prof_comp_transf` retirement.

   Only after join and tensor/co-Yoneda no longer rely on it.

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
| `EQUIP-INVENTORY` | proposed | this report | Maintain the remaining `Prof_comp_transf` consumer classification before code deletion. |
| `EQUIP-CELL-EVAL` | proposed | future design refinement | Decide the narrow shaped cell-evaluation/projection owner, such as `Prof_cell_eval` or a first join-specific `join_cross_hom`, before migrating join beta. |
| `EQUIP-JOIN-NARROW` | proposed | future implementation probe | Replace join-specific `Prof_comp_transf` shaped cross and cross beta with direct/narrow join owners. |
| `EQUIP-TENSOR-COYONEDA` | proposed | future implementation probe | Add fixed-endpoint co-Yoneda map/comparison owners and migrate beta checks away from general equipment composition. |
| `EQUIP-PROF-FUNC` | proposed | future implementation probe | Audit `Prof_func_transf` as representable hom-action compatibility, especially for general co-Yoneda and join. |
| `EQUIP-COMP-RETIRE` | blocked on previous tasks | future cleanup | Demote or remove `Prof_comp_transf` only after join and tensor/co-Yoneda no longer consume it. |
