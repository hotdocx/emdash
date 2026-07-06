# EMDASH v3.2 Primitive Prof Cat Redesign Plan

Date: 2026-07-06
Last reviewed: 2026-07-06
Plan-ID: EMDASH-V3-2-PROF-CAT-PRIMITIVE-REDESIGN-2026-07-06
Depends-On: EMDASH-V3-2-PROFUNCTOR-WEIGHTED-LIMITS-2026-06-17; EMDASH-V3-2-PROFUNCTOR-REPRESENTABILITY-2026-06-19; EMDASH-V3.2-DEFISO-HOM-ACTION-PROFCOMP-MIGRATION-2026-06-28; EMDASH-V3-2-CAT-CATD-SPECIALIZATION-ALIAS-MIGRATION-2026-07-04; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Supersedes: no whole report; refines the long-term note that making `Prof_cat` primitive is a separate foundation-level migration
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-analysis-2026-07-06
Infinity-Codex-Decision-Responses: infinity-codex:019f3811-100c-7ea0-8c38-5534271c1cde:019f3823-a12a-7901-b834-2dc4d4ef0519
Status: proposed plan for review; no active code promoted

Review update 2026-07-06: a follow-up source review found that the proposed
`Prof_cat`-specific `hom_postcomp_fapp0` identity and incoming-map bridge were
overfitted to a stale Catd-specific bridge. The active generic hom-action
rules already provide the intended identity and source-accumulation behavior.
This plan now treats the Catd-specific bridge and several old
`ProfComparison` helpers as cleanup candidates, not patterns to clone.

Review update 2026-07-06b: a further source review found that
`Prof_imply_cov_transf` is also likely stale. It is used only by its own
definition/checks, and its fixed-endpoint computation is just the generic
capped action of `Prof_imply_cov_func2` on a product arrow. The primitive
`Prof_cat` migration should therefore clean this wrapper away and keep
`Prof_imply_cov_func2` / `Prof_imply_cov_func(Q)` as the public functorial
surface. The contravariant placeholder `Prof_imply_con_transf` is a parallel
cleanup candidate; the follow-up note below strengthens this to immediate
deletion rather than waiting for a future contravariant mixed functor.

Review update 2026-07-06c: after reviewing the whole closed-implication
equipment-view cluster, `Prof_imply_con_transf` should be deleted now rather
than deferred. It is a `constant symbol`, has no computation rule, and has no
source consumer beyond its type check. The endpoint-changing
`Prof_eval_*_transf` / `Prof_lambda_*_transf` wrappers, including the shaped
`*_hom_transf` variants, are likewise historical equipment-style compatibility
views. The general fixed-endpoint `*_map` cores remain the actual
computational owners; the follow-up note below reclassifies the shaped
`*_hom_map` pairs as cleanup/deferred-derived API.

Review update 2026-07-06d: the shaped `*_hom_map` pairs are mathematically
unit-tensor specializations of the general fixed-endpoint closed core. They
would be derivable from `Prof_eval_*_map` / `Prof_lambda_*_map` plus full
co-Yoneda unit equivalences. The active code currently has only the one-way
co-Yoneda maps `Unit tensor P -> P` and `P tensor Unit -> P`, so the eval
direction is not derivable judgmentally today. Since the shaped `*_hom_map`
pairs have no source consumer beyond their own checks, they should be cleaned
or deferred as future derived wrappers rather than kept as primitive owners.

## Purpose

This report records the proposed redesign of the profunctor category surface:
make `Prof_cat(A,B)` a stable primitive category head while keeping the existing
Cat-valued family semantics available through explicit projection rules and
proof-time compatibility.

The motivating concern is that the current definition:

```text
Prof_cat(A,B) := Catd_cat(Product_cat(Op_cat A,B))
```

lets the semantic presentation of profunctors unfold freely into the
directed-family calculus. That is useful today, but it makes it hard to control
which equations are runtime cut-elimination normal forms and which are
proof-time or semantic identifications.

The goal is not to rewrite every product-indexed Cat-valued family as a
profunctor. The goal is to make the fixed-endpoint profunctor category itself
the public stable head, with a measured projection ladder into the existing
`Catd_cat(Product_cat(Op_cat A) B)` infrastructure.

## Current Assessment

The active code currently has:

```text
Prof_base(A,B) := Product_cat(Op_cat A,B)
Prof_cat(A,B)  := Catd_cat(Prof_base(A,B))
Prof(A,B)      := Obj(Prof_cat(A,B))
ProfMap(P,Q)   := Obj(Hom_cat(Prof_cat(A,B),P,Q))
```

This makes `Prof_cat` a transparent alias. It also means that vertical
profunctor identities, composition, and many DefIso/ProfComparison facts
currently compute because `Prof_cat(A,B)` reduces to
`Catd_cat(Product_cat(Op_cat A) B)`.

A source map on 2026-07-06 found the migration is not just a local rule change:

```text
main raw τ(Catd(Product_cat(Op_cat ...))) profunctor occurrences: 39
check-file raw τ(Catd(Product_cat(Op_cat ...))) occurrences: 70
main Prof_cat occurrences: 101
check-file Prof_cat occurrences: 108
main ProfMap occurrences: 46
check-file ProfMap occurrences: 42
```

So the redesign is a representation-boundary migration. The public API already
uses `Prof_cat` and `ProfMap` heavily, while many constructors still expose raw
Cat-valued family types.

Temporary probes during the design review showed:

- replacing `Functor_cat K Cat_cat -> Catd_cat K` by proof-time unification
  alone is not currently viable, but that issue is deferred from this plan;
- making `Prof_cat` primitive with only proof-time compatibility is too weak,
  because existing code needs runtime projections such as `Hom_cat(Prof_cat A B)`;
- the broad runtime rule
  `Catd_cat(Product_cat A B) -> Prof_cat(Op_cat A,B)` is the wrong direction:
  it reclassifies arbitrary product-indexed families and creates
  subject-reduction pressure.

## Architectural Decision

### 1. Make `Prof_cat` a stable public category head

The intended new surface is:

```text
injective symbol Prof_cat (A B : Cat) : Cat;

symbol Prof (A B : Cat) : Grpd
≔ Obj (Prof_cat A B);
```

`Prof_base(A,B)` can remain as a transparent readability alias for
`Product_cat(Op_cat A) B`, but it should not become a rewrite discriminator.

### 2. Project `Prof_cat` into the existing Catd semantics

The first required runtime projections are expected to be:

```text
rule Obj (Prof_cat $A $B)
  ↪ Obj (Catd_cat (Product_cat (Op_cat $A) $B));

rule Hom_cat (Prof_cat $A $B) $P $Q
  ↪ @Functord_cat (Product_cat (Op_cat $A) $B) $P $Q;
```

These replace the current alias conversion needed by `ProfMap`, ordinary
vertical maps, `IsoEvidence(Prof_cat A B,...)`, and `DefIso(Prof_cat A B,...)`.

### 3. Use generic `Prof_cat` composition as the public vertical normal form

The preferred migration target is to state fixed-endpoint profunctor vertical
composition with generic category composition:

```text
@comp_fapp0 (Prof_cat A B) P Q R q p
```

rather than exposing:

```text
@comp_catd_fapp0 (Product_cat (Op_cat A) B) P Q R q p
```

or its unfolded `@comp_fapp0 (@Catd_cat ...)` spelling in public profunctor
statements.

This does not remove `comp_catd_fapp0`; it remains the directed-family owner
under the projection layer. But `ProfComparison`, weighted-limit comparison
lemmas, co-Yoneda maps, and fixed-endpoint closed operations should prefer
`@comp_fapp0 (Prof_cat A B)` in their public equality targets when the ambient
category is visibly a profunctor category.

### 4. Do not clone stale Catd hom-action bridges

The current generic hom-action layer already has the ordinary identity and
incoming-map accumulation rules needed by identity-functor postcomposition:

```text
rule @hom_postcomp_fapp0 $A $B $F $W $X $X (@id $B $X) $g
  ↪ $g;

rule @comp_fapp0
      $A
      $V
      $W
      _
      (@hom_postcomp_fapp0 $A $B $F $W $X $Y $f $g)
      $h
  ↪ @hom_postcomp_fapp0
      $A $B $F $V $X $Y $f
      (@comp_fapp0
        $A
        $V
        $W
        (@fapp0 $B $A $F $X)
        $g
        $h);
```

Instantiating these rules at:

```text
X = Prof_cat A B
F = id_(Prof_cat A B)
```

already covers the proposed `Prof_cat` identity and accumulation shapes. Adding
parallel `Prof_cat`-specific rules would duplicate the generic owner and create
avoidable overlap.

The existing Catd-specific pair:

```text
rule @hom_postcomp_fapp0
      (@Catd_cat $K)
      (@Catd_cat $K)
      (@id Cat_cat (@Catd_cat $K))
      ...
  ↪ ...

rule @comp_fapp0
      (@Catd_cat $K)
      ...
      (@hom_postcomp_fapp0
        (@Catd_cat $K)
        (@Catd_cat $K)
        (@id Cat_cat (@Catd_cat $K))
        ...)
      ...
  ↪ ...
```

should be audited for deletion before any `Prof_cat` migration. The second
rule's RHS uses `comp_catd_fapp0`, but after the Cat/Catd alias migration that
symbol is only a transparent public alias over generic
`@comp_fapp0 (@Catd_cat K)`. Therefore the Catd bridge is likely historical
cleanup debt rather than an active semantic owner.

A future `Prof_cat`-specific hom-action bridge should be added only after a
concrete consumer fails and a focused check shows that the generic rule cannot
express the desired public normal form. It should then be documented as a
projection-ladder confluence bridge, not as basic profunctor functoriality.

### 5. Add proof-time compatibility, not broad runtime folding

The useful proof-time comparison is expected to be:

```text
unif_rule
  Prof_cat $A $B
  ≡ Catd_cat (Product_cat $A0 $B)
  ↪ [ $A ≡ Op_cat $A0 ];
```

This rule is for elaboration and semantic compatibility. It should not be used
as a substitute for the runtime `Obj` and `Hom_cat` projections above, and it
should not be paired with a broad runtime rewrite from `Catd_cat(Product_cat
...)` to `Prof_cat`.

Depending on the first probes, additional proof-time rules may be useful for
object classifiers:

```text
unif_rule
  Obj (Prof_cat $A $B)
  ≡ Obj (Catd_cat (Product_cat $A0 $B))
  ↪ [ $A ≡ Op_cat $A0 ];
```

These should be validated with typed `eq_refl` terms, not just `assert t ≡ u`,
because `assert` checks conversion rather than proof-time unification.

## Proposed Implementation Phases

### Phase 0: Baseline and inventory

Capture before editing:

```text
EMDASH_TYPECHECK_TIMEOUT=60s make check
make warning-summary
python3 scripts/audit_rule_lhs.py --strict
```

Record the warning inventory and the exact first consumers that fail in a
temporary primitive-`Prof_cat` copy.

### Phase 1: Primitive head plus projections

In a probe copy:

1. Change `Prof_cat` from a transparent definition to an injective symbol.
2. Keep `Prof` as `Obj(Prof_cat A B)`.
3. Add the `Obj(Prof_cat ...)` projection.
4. Add the `Hom_cat(Prof_cat ...)` projection.
5. Add focused checks for:

```text
Prof A B = Obj(Catd_cat(Product_cat(Op_cat A) B))
ProfMap(P,Q) = Functord(P,Q)
id(Prof_cat A B,P) : ProfMap(P,P)
comp_fapp0(Prof_cat A B,q,p) : ProfMap(P,R)
```

Do not yet migrate all constructor signatures.

### Phase 2: Fixed vertical normal forms

Before migrating public `ProfComparison` statements, clean up the stale
generic/Catd boundary:

```text
audit/delete Catd-specific hom_postcomp_fapp0 identity bridge;
audit/delete Catd-specific hom_postcomp_fapp0 source-accumulation bridge;
verify generic hom_postcomp_fapp0 identity and accumulation checks cover the
  former cases.
```

Migrate the first public profunctor vertical statements from
`comp_catd_fapp0(Product_cat(Op_cat A) B,...)` to:

```text
@comp_fapp0 (Prof_cat A B) ...
```

The immediate target cluster is:

```text
ProfMap
ProfComparison
prof_comparison_push
prof_comparison_pull
prof_comparison_to/from
prof_comparison_evidence
```

The following names look stale after the DefIso/hom-action migration and should
be deleted or replaced by generic `DefIso`/`hom_postcomp_*` checks unless a
current consumer proves otherwise:

```text
prof_comparison_push_selected
prof_comparison_pull_selected
prof_comparison_push_semantics
prof_comparison_pull_semantics
prof_comparison_push_func
prof_comparison_pull_func
prof_comparison_to_evidence
prof_comparison_from_evidence
```

The first four expose old Catd-composition semantics. The functor wrappers are
transparent uses of `hom_postcomp_func`, and current source search shows no
active implementation dependency beyond their checks. The `to/from_evidence`
proofs are only used by the stale semantic lemmas. By contrast,
`prof_comparison_evidence` is still a useful compatibility map from
`ProfComparison` to `IsoEvidence` and is used by weighted-limit and adjunction
checks.

### Phase 3: Internalized profunctor functors

Audit and migrate the functors whose source or target is `Prof_cat`:

```text
Op_prof_func
Hom_prof_func
Prof_reindex_func
Prof_tensor_func
Prof_imply_cov_func2
Prof_imply_cov_fixed_weight_func
Prof_imply_cov_func
```

The `Prof_imply_cov` cluster should be simplified before the primitive
`Prof_cat` migration:

```text
delete Prof_imply_cov_transf;
delete or rewrite its checks as direct checks of
  fapp1_fapp0(Prof_imply_cov_func2, Struct_sigma o q);
keep Prof_imply_cov_func2 as the mixed-variance functor owner;
keep Prof_imply_cov_fixed_weight_func(Q) as the product insertion
  O |-> (O,Q);
keep Prof_imply_cov_func(Q) as the opaque fixed-weight semantic composite.
```

The current `Prof_imply_cov_transf` type packages an endpoint-changing
equipment view, but its only promoted computation is the fixed-endpoint case:

```text
Prof_imply_cov_transf(id,id,o,q)
  -> fapp1_fapp0(Prof_imply_cov_func2, Struct_sigma(o,q)).
```

That makes the named transf a compatibility wrapper around the generic mixed
functor action, not an owner. Its presence adds noise to the future
`Prof_cat`-primitive migration because it preserves raw Catd/Product endpoint
spelling and suggests constructor-specific functoriality that the SOP says
should remain with `fapp*`.

The current `Prof_imply_cov_func2` / `Prof_imply_cov_func(Q)` architecture is
mostly the right idiom:

```text
Prof_imply_cov_func2 :
  Product_cat (Prof_cat A X) (Op_cat (Prof_cat B X)) -> Prof_cat A B

Prof_imply_cov_func(Q)
  := Prof_imply_cov_func2 o Prof_imply_cov_fixed_weight_func(Q)
```

This mirrors the Product/Hom pattern: keep a stable semantic functor head, add
an object-action rule, let generic `fapp1_func` / `fapp1_fapp0` own identity
and composition, and make the fixed-weight operation an opaque semantic
composite with a direct object-action rule. Unlike `Product_map_func`, there is
no available end-level arrow formula for implication maps, so no product-style
component projection rule should be invented now.

The contravariant sibling `Prof_imply_con_transf` is also suspicious: it is a
`constant symbol`, has no computation rule, and source/normalized search shows
no current consumer beyond its type check. It should be deleted as immediate
cleanup. A later `Prof_imply_con_func2` mixed functor may still be desirable,
but absence of that future owner is not a reason to retain an unusable
placeholder.

The endpoint-changing eval/lambda wrappers should be treated the same way:

```text
delete Prof_eval_cov_transf;
delete Prof_lambda_cov_transf;
delete Prof_eval_con_transf;
delete Prof_lambda_con_transf;
delete Prof_eval_cov_hom_transf;
delete Prof_lambda_cov_transf_hom;
delete Prof_eval_con_hom_transf;
delete Prof_lambda_con_transf_hom;
```

These are transparent reindexed equipment views around the fixed-endpoint
cores. Source search shows they are only used by their own inverse checks. The
checks should be removed or rewritten against the retained general
fixed-endpoint owners:

```text
Prof_eval_cov_map / Prof_lambda_cov_map;
Prof_eval_con_map / Prof_lambda_con_map.
```

The general fixed-endpoint pairs should stay:

```text
Prof_eval_cov_map / Prof_lambda_cov_map;
Prof_eval_con_map / Prof_lambda_con_map.
```

They are the genuine closed-core computational API. By contrast, the shaped
`*_hom_map` pairs:

```text
Prof_eval_cov_hom_map / Prof_lambda_cov_hom_map;
Prof_eval_con_hom_map / Prof_lambda_con_hom_map.
```

should be treated as cleanup or deferred-derived API. Semantically, for
example, `Prof_lambda_cov_hom_map` can be recovered from
`Prof_lambda_cov_map` by first composing a map `Q -> O` with the left-unit
co-Yoneda map:

```text
Unit_prof(A) tensor Q -> Q -> O.
```

But `Prof_eval_cov_hom_map` would need the reverse unit map:

```text
Q -> Unit_prof(A) tensor Q,
```

or a full `ProfComparison`/DefIso unit law for the co-Yoneda unitor. The active
co-Yoneda layer exposes only the one-way map
`Unit_prof(A) tensor Q -> Q`, plus beta/fusion rules for tensor-introduced
shaped elements. The same asymmetry holds on the right-unit/contravariant
side. Therefore the shaped `*_hom_map` pairs are currently extra primitive
closed-structure assertions, not derivations from the general core.

Recommendation: delete the shaped `*_hom_map` pairs during cleanup unless a
near-term consumer needs them. Reintroduce them later as derived wrappers after
the unit/co-Yoneda comparison is represented as a full invertible comparison.

For each, verify:

```text
object action;
capped arrow action;
identity behavior;
composition behavior;
compatibility with ProfMap and ProfComparison.
```

### Phase 4: Constructor signatures

Gradually replace raw public profunctor arguments:

```text
τ (Catd (Product_cat (Op_cat A) B))
```

by:

```text
τ (Prof A B)
```

where the symbol is semantically fixed-endpoint profunctor-facing. This should
be staged, not mechanical, because some lower-level projections deliberately
need the raw Catd/Product base as their discriminator.

Likely migration candidates include:

```text
Op_prof
Prof_reindex
Prof_reindex_fapp1_func
Hom_prof
Unit_prof
Prof_transf_cat
Prof_hom_cat
Prof_hom
Prof_cell_apply
Prof_reindex_transf
Prof_tensor
Prof_imply_cov
Prof_imply_con
Terminal_prof
Prof_cell_eval
```

Each candidate should be probed in dependency order.

### Phase 5: Checks and reports

Update `emdash3_2_checks.lp` alongside each promoted slice. Keep checks focused
on the intended public surface:

```text
Prof_cat A B
Prof A B
ProfMap
@comp_fapp0 (Prof_cat A B)
```

Retain raw `Catd_cat(Product_cat(Op_cat A) B)` checks only when they are
testing the semantic projection layer itself.

After meaningful promoted changes:

```text
make catalog
make health
make ci
```

## Rejected Or Deferred Directions

### Broad runtime reclassification

Do not add:

```text
rule Catd_cat (Product_cat $A $B) ↪ Prof_cat (Op_cat $A) $B;
```

This rewrites arbitrary product-indexed Cat-valued families into profunctor
syntax and is not justified by cut-elimination ownership.

### Demoting `Functor_cat K Cat_cat` in this plan

The `Catd_cat` versus `Functor_cat K Cat_cat` runtime/proof-time boundary is a
separate architectural topic. It should not be bundled into the primitive
`Prof_cat` migration.

### Primitive `ProfMap` composition heads

Do not add primitive `ProfMap_id` or `ProfMap_comp` merely for naming.
Fixed-endpoint vertical maps should continue to use ordinary category identity
and composition in `Prof_cat(A,B)`.

## Side-Task Ledger

### PROF-CAT-PRIM-001: Primitive `Prof_cat` projection probe

Status: proposed.

Scope:

```text
injective Prof_cat;
Obj(Prof_cat) projection;
Hom_cat(Prof_cat) projection;
basic Prof/ProfMap/id/comp checks.
```

Exit criteria: bounded probe succeeds and identifies the next missing public
vertical normal form.

### PROF-CAT-PRIM-002: ProfComparison public composition migration and cleanup

Status: proposed.

Scope: remove stale Catd-semantics comparison helpers, keep only the
`ProfComparison` compatibility surface that still has current consumers, and
migrate any retained public vertical equality targets from
`comp_catd_fapp0(Product_cat(Op_cat A) B,...)` to
`@comp_fapp0 (Prof_cat A B) ...`.

Exit criteria: comparison beta/eta, weighted-limit comparison, and adjunction
comparison checks still pass; no retained statement exposes raw Catd
composition unless it is explicitly testing the projection layer.

### PROF-CAT-PRIM-003: Catd hom-action bridge cleanup

Status: proposed.

Scope: delete the stale Catd-specific `hom_postcomp_fapp0` identity and
source-accumulation bridge if the generic rules cover the same behavior.

Exit criteria: focused checks demonstrate the generic identity and accumulation
rules cover the former Catd cases; warning-enabled check shows no new problem.
Do not introduce any analogous `Prof_cat` bridge unless a concrete later
consumer fails without it.

### PROF-CAT-PRIM-004: Public constructor signature migration

Status: proposed.

Scope: replace raw fixed-endpoint profunctor family argument types by
`τ (Prof A B)` where doing so improves the public surface and does not remove a
needed raw Catd/Product discriminator.

Exit criteria: each promoted cluster has focused checks and no broad global
folds are introduced.

### PROF-CAT-PRIM-005: Prof implication mixed-functor and equipment-view cleanup

Status: proposed.

Scope: delete `Prof_imply_cov_transf`, delete `Prof_imply_con_transf`, rewrite
or remove their coverage around direct `Prof_imply_cov_func2` generic action
checks, and remove the closed-implication shaped/equipment wrappers:

```text
Prof_eval_cov_transf;
Prof_lambda_cov_transf;
Prof_eval_con_transf;
Prof_lambda_con_transf;
Prof_eval_cov_hom_map;
Prof_lambda_cov_hom_map;
Prof_eval_con_hom_map;
Prof_lambda_con_hom_map;
Prof_eval_cov_hom_transf;
Prof_lambda_cov_transf_hom;
Prof_eval_con_hom_transf;
Prof_lambda_con_transf_hom.
```

Exit criteria: weighted-limit and right-adjoint consumers still use
`Prof_imply_cov_func(Q)` and `Prof_imply_cov_func2` directly; fixed-endpoint
general eval/lambda `*_map` beta/eta checks still pass; no constructor-specific
implication functoriality rule is introduced. If shaped closed maps are needed
later, they should be derived from the general core plus a full co-Yoneda unit
comparison, not reintroduced as independent primitive inverses.
