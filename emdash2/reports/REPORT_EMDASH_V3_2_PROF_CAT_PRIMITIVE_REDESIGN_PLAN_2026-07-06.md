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

### 4. Add `Prof_cat` hom-action bridges where needed

The current generic hom-action layer has Catd-specific bridges such as:

```text
hom_postcomp_fapp0(Catd_cat K, Catd_cat K, id, ...)
```

For primitive `Prof_cat`, the analogous fixed-endpoint bridges should be added
at the profunctor boundary. The likely core pair is:

```text
rule @hom_postcomp_fapp0
      (@Prof_cat $A $B)
      (@Prof_cat $A $B)
      (@id Cat_cat (@Prof_cat $A $B))
      $R
      $P
      $P
      (@id (@Prof_cat $A $B) $P)
      $r
  ↪ $r;
```

and the incoming-map accumulation bridge:

```text
rule @comp_fapp0
      (@Prof_cat $A $B)
      $S
      $R
      $Q
      (@hom_postcomp_fapp0
        (@Prof_cat $A $B)
        (@Prof_cat $A $B)
        (@id Cat_cat (@Prof_cat $A $B))
        $R $P $Q
        $to
        $r)
      $h
  ↪ @hom_postcomp_fapp0
      (@Prof_cat $A $B)
      (@Prof_cat $A $B)
      (@id Cat_cat (@Prof_cat $A $B))
      $S $P $Q
      $to
      (@comp_fapp0 (@Prof_cat $A $B) $S $R $P $r $h);
```

These are not new profunctor-specific functoriality laws. They are
projection-boundary joins, analogous to the existing Catd-specific hom-action
bridges, needed because the public category head is no longer definitionally
`Catd_cat(Product_cat(Op_cat A) B)`.

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

Migrate the first public profunctor vertical statements from
`comp_catd_fapp0(Product_cat(Op_cat A) B,...)` to:

```text
@comp_fapp0 (Prof_cat A B) ...
```

Add the `Prof_cat`-specialized `hom_postcomp_fapp0` identity and accumulation
bridges only if a concrete `ProfComparison` or weighted-limit check needs them.

The immediate target cluster is:

```text
ProfMap
ProfComparison
prof_comparison_push_selected
prof_comparison_pull_selected
prof_comparison_push_semantics
prof_comparison_pull_semantics
prof_comparison_push_func
prof_comparison_pull_func
```

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

### PROF-CAT-PRIM-002: ProfComparison public composition migration

Status: proposed.

Scope: migrate selected `ProfComparison` semantic equality targets from
`comp_catd_fapp0(Product_cat(Op_cat A) B,...)` to
`@comp_fapp0 (Prof_cat A B) ...` where the statement is public fixed-endpoint
profunctor syntax.

Exit criteria: existing comparison beta/eta and weighted-limit comparison
checks still pass.

### PROF-CAT-PRIM-003: Prof-specific hom-action bridges

Status: proposed.

Scope: add the minimal `hom_postcomp_fapp0` bridge family over `Prof_cat(A,B)`
needed by `ProfComparison` and later weighted-limit/co-Yoneda consumers.

Exit criteria: warning-enabled probe classifies any overlap with the generic
Catd bridge and confirms the bridge is a projection-boundary join, not a
second owner of functoriality.

### PROF-CAT-PRIM-004: Public constructor signature migration

Status: proposed.

Scope: replace raw fixed-endpoint profunctor family argument types by
`τ (Prof A B)` where doing so improves the public surface and does not remove a
needed raw Catd/Product discriminator.

Exit criteria: each promoted cluster has focused checks and no broad global
folds are introduced.

