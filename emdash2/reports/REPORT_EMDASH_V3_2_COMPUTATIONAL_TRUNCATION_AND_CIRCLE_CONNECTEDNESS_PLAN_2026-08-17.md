# Emdash v3.2 Computational Truncation And Circle Connectedness Plan

Date: 2026-08-17 (America/Toronto)

Plan-ID: `COMPUTATIONAL-TRUNCATION-CIRCLE-CONNECTEDNESS-V3.2`

Parent-Decision-Record:
`REPORT_EMDASH_V3_2_INTERNAL_LAXITY_AND_GROUPOIDAL_REALIZATION_CONTINUATION_PLAN_2026-08-17.md`,
row `ILGR-TRUNC-1`

Depends-On: active `emdash3_2.lp`; the existing `TruncLevel`,
`IsTruncGrpd`, `TruncGrpdU`, package path/univalence, and truncation-closure
owners; the selected-realization pattern of
`emdash3_2_direct_cover_sheafification.lp`; the restricted-eliminator pattern
of `emdash3_2_telescope_localization_hit.lp`; the completed Circle and
path-realized pseudo-laxity extensions; the active Foundations, current SOP,
canonical syntax, and parent decision record

Supersedes: no completed implementation plan. It reopens only
`ILGR-TRUNC-1` with Circle connectedness as the selected HoTT consumer.

Side-Task-Ledger: `CTCC-00`, `CTCC-NTYPE-1`, `CTCC-REFLECT-2`,
`CTCC-ACTION-3`, `CTCC-CIRCLE-4`, conditional `CTCC-CIRCLE-5`,
`CTCC-PUBLIC-6`, and `CTCC-CLOSE-7`

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`; selected truncation/Circle
connectedness continuation response
`01a01115-9618-7b60-9334-3f417fb393d8`

Infinity-Codex-Decision-Responses: response `0040`, archived at
`/home/user1/emdash1/emdash2/tmp/ai-responses/sessions/2026-08-14_019ffe392eb9/responses/0040_2026-08-17T19-01-39Z_01a01115-9618-7b60-9334-3f417fb393d8.md`.
Active code and SOP, then this plan and its parent decision record, outrank
the archive.

Status: **complete at the bounded acceptance boundary**. `CTCC-00` through
`CTCC-CLOSE-7` are complete. No generic groupoidification, Gray tensor,
arbitrary quotient/HIT schema, book rewrite, push, merge, publication,
release, history rewrite, branch deletion, or worktree removal is in scope.
Local checkpoint commits require the repository Git SOP and separate explicit
authorization if the active launch prompt does not supply it.

Branch-And-Worktree: `goal/computational-truncation-v3.2` in
`/home/user1/emdash1-groupoidal-circle-v1`

Baseline: completed path-realized pseudo-laxity checkpoint `2fe1e54`,
descended from `main` baseline `86042df`

Checkpoint: bounded semantic implementation `998c60f26adacee2b2211353e3e60e0f84b529aa`;
this ledger-only follow-up records that checkpoint without changing its
validated mathematical or generated-health content

## 1. Objective

Implement the first actual homotopy-truncation reflector in the computational
HoTT layer while preserving the distinction between:

1. `IsTruncGrpd(n,A)`, a property of an existing ambient classifier;
2. `TruncGrpdU(n)`, the existing package of a carrier with retained evidence;
3. `Trunc_ntype(n,A)`, the result classified intrinsically as an `n`-type; and
4. `Trunc_grpd(n,A)`, the decoded ambient carrier of that classified result.

The implementation is not complete merely because these four names can be
typed. It must expose a restricted dependent eliminator with point
computation and derive map action through that same owner.

The selected concrete consumer is Circle connectedness:

```text
CircleConnected(x)
  := Trunc_grpd(-1, circle_base = x)

circle_connected(x)
  : CircleConnected(x).
```

Mathematically this is

```text
Pi x:S1, || circle_base = x ||_-1.
```

It deliberately does not choose a path continuously at every point. The
propositional truncation retains existence while discarding the impossible
global choice of a based path. If the first consumer is stable, the next
bounded result is

```text
IsContr(Trunc_grpd(0,Circle_grpd)).
```

This validates the parent plan's distinction: set-truncating the connected
Circle produces a contractible set, whereas groupoidifying the directed
WalkingEnd freely inverts its generator and retains the integer loop group.

## 2. Why this row is ready

The generic internal-laxity and path-realization rows are complete. The parent
plan's next ordered architectural row is the classified truncation facade and
reflector. The active kernel already supplies most prerequisites:

- native levels from `-2` upward;
- recursive `IsTruncGrpd`;
- monotonicity, dependent Pi/Sigma closure, equivalence invariance, and
  proposition-valued truncation evidence;
- `TruncGrpdU(n)` with computing carrier/evidence projections;
- controlled package paths, restricted package univalence, and the expected
  successor truncation level of that package universe;
- the set-truncated telescope-localization HIT as evidence that a primitive
  restricted eliminator with point beta is viable; and
- the Circle eliminator, with proposition-valued motives already used to
  discharge loop coherence.

What remains is not another property theorem. It is the reflector itself and
its classified output.

## 3. Selected architecture

### 3.1 The classifier facade

Use the same selected-realization pattern as the active Cat-valued sheaf
facade:

```text
NType_cat(n) : Cat

Obj(NType_cat(n))
  --> TruncGrpdU(n)

Hom_NType(X,Y)
  --> Hom_Grpd(
        trunc_grpd_carrier(X),
        trunc_grpd_carrier(Y)).
```

Identity and composition delegate to `Grpd_cat`. One whole inclusion exposes
the decoded carrier:

```text
ntype_include_grpd_func(n)
  : Functor(NType_cat(n),Grpd_cat).
```

No pair of arbitrary package-conversion functions is introduced. An object of
`NType_cat(n)` already realizes directly as the existing package.

### 3.2 Classified formation and decoded carrier

The primary result is a code in the smaller classifier:

```text
Trunc_ntype(n,A) : Obj(NType_cat(n)).
```

The usable ambient type is its decoding:

```text
ElNType(n,X) := trunc_grpd_carrier(X)

ElNType(n,Trunc_ntype(n,A))
  --> Trunc_grpd(n,A).
```

The retained evidence projection computes to

```text
trunc_ntype_is_truncated(n,A)
  : IsTruncGrpd(n,Trunc_grpd(n,A)).
```

The direction above is intentional. `Trunc_grpd(n,A) : Grpd` is a decoded
carrier normal form, not the primary codomain of the reflector.

### 3.3 Restricted dependent elimination

The intrinsic eliminator quantifies over a family of classified `n`-types:

```text
trunc_ind
  [P : ElNType(n,Trunc_ntype(n,A)) -> Obj(NType_cat(n))]
  (d : Pi a:A, ElNType(n,P(trunc_intro(a))))
  : Pi z:ElNType(n,Trunc_ntype(n,A)), ElNType(n,P(z)).

trunc_ind(P,d,trunc_intro(a))
  --> d(a).
```

A transparent convenience form may accept an ambient family plus explicit
`IsTruncGrpd(n,-)` evidence by packaging each fibre with
`Struct_trunc_grpd`. It must reduce through the intrinsic eliminator rather
than become a second primitive recursor.

The first prototype selects the compact sorted primitive interface above.
The classical hub-and-spoke HIT remains the HoTT reference presentation and
semantic comparison. It is not necessary to duplicate every hub/spoke
constructor before the sorted interface can be tested computationally, but
the plan must not claim that an arbitrary post-hoc package constructs the
reflector.

### 3.4 Map and whole action

For `f:A->B`, define `trunc_map(n,f)` by restricted recursion into the already
classified target:

```text
trunc_map(n,f)(trunc_intro(a))
  --> trunc_intro(f(a)).
```

Then expose

```text
Truncation_func(n) : Functor(Grpd_cat,NType_cat(n))
```

with object action `Trunc_ntype(n,-)` and hom action owned by one retained
whole functor whose object projection is `trunc_map`. Identity, composition,
and subsequent higher observations must follow from this same action/recursor
boundary; unrelated map axioms are excluded.

## 4. Circle consumer

### 4.1 Mere based connectedness

Define the proposition-valued family

```text
CircleConnected(x)
  := Trunc_grpd(trunc_minus_one,
       circle_base = x).
```

Its retained truncation evidence makes every fibre a proposition. Circle
induction therefore needs only:

- base datum `trunc_intro(refl)`; and
- the existing proposition-family `PathOver` coherence constructor around
  `circle_loop`.

Required computation:

```text
circle_connected(circle_base)
  --> trunc_intro(refl).
```

This is the first real consumer of propositional truncation. It is stronger
evidence than collapsing a closed Boolean example and avoids claiming a
nonexistent untruncated global path choice.

### 4.2 Conditional set truncation of the Circle

Once mere connectedness and the generic recursors are stable, construct the
centre

```text
trunc_intro(circle_base) : Trunc_grpd(0,Circle_grpd)
```

and eliminate first over the set truncation, then over each merely inhabited
based-path fibre, to produce a path from that centre to every point. The
target path family is proposition-valued because the outer truncation is a
set.

This row is conditional within the first goal. If it reveals a genuinely
missing PathOver or truncation-family owner, record and isolate that
prerequisite rather than weakening the eliminator or adding proof erasure.

## 5. Reuse and anti-duplication matrix

| Desired observation | Existing owner | Planned treatment |
| --- | --- | --- |
| level recursion and readable `-1/0/1` | `TruncLevel`, `IsTruncGrpd` | reuse unchanged |
| classified carrier/evidence data | `TruncGrpdU`, `Struct_trunc_grpd`, projections | direct `Obj(NType_cat)` realization |
| package paths and univalence | `TruncGrpdPathView` and active package theorems | reuse; no new package equality |
| category facade | Cat-valued `Sheaf_cat` realization | copy the structural pattern, not its semantics |
| restricted HIT elimination | telescope-localization `ind`/point beta | copy the owner discipline and LHS policy |
| Circle induction | `circle_ind`, proposition-family `PathOver` | construct connectedness without a new Circle rule |
| path proposition from sethood | `IsSetGrpd` recursion | reuse directly |
| whole map action | ordinary `fapp1_func`/`fapp1_fapp0` ladder | retain one hom-action owner; do not stop at a capped rule |

Before each source promotion, relocate these symbols and test the proposed
owner at its actual extension position. A public stable head is justified
only when a transparent term loses the intended computation or higher owner.

## 6. Execution ledger

| Row | Status | Deliverable and acceptance boundary |
| --- | --- | --- |
| `CTCC-00` | complete | The child plan is active on the clean descendant branch at `2fe1e54`; active authorities, worktrees, Git SOP, selected sheaf/HIT patterns, truncation owners, and the focused kernel baseline were reviewed. |
| `CTCC-NTYPE-1` | complete | `NType_cat(n)`, its selected object/Hom/identity/composition realization, `ElNType`, and the object-computing carrier inclusion are promoted. The tracked reviewer checks object and Hom computation, typed identity/composition delegation, inclusion/decoding, level non-collapse, foreign-category rejection, and wrong-level rejection. The source is registered in the maintained checker/health inventories and active authority map. Focused source/reviewer checks, `1132/159` warning evidence (`+20/0` from the explicit composition facade), and strict zero-LHS audit are green. The attempted resumable health refresh was stopped after it unexpectedly invalidated the whole registry snapshot; it reported no failure before interruption, changed no health report, and is deferred to the closeout gate rather than treated as row evidence. |
| `CTCC-REFLECT-2` | complete | `Trunc_ntype(n,A)` is a primitive code in `NType_cat(n)` whose carrier/evidence projections compute to stable `Trunc_grpd` and `trunc_ntype_is_truncated` owners. `trunc_intro` and intrinsic `trunc_ind` provide point computation only into classified `n`-type motives. Transparent ambient induction/recursion require explicit same-level evidence and reduce through the intrinsic owner. The reviewer checks all point betas and rejects both a raw unclassified motive and successor-only evidence. The promoted source/reviewer are focused-green, strict LHS audit is zero, and warnings remain `1132/159`. |
| `CTCC-ACTION-3` | complete | `trunc_map` reduces through `trunc_rec`; `trunc_map_family` retains the whole function-space map, and `trunc_map_func` is transparently the existing iterable `path_map_func` on that family. Same-level path truncation lets restricted induction prove pointwise and whole identity/composition paths. `Truncation_func(n)` computes on objects and retains one propositional comparison from its generic hom action to this derived whole owner; no competing capped action rule is installed. The reviewer checks point action, both functor-law paths, the whole comparison, one next Path action, and a mismatched target endpoint. Source/reviewer checks are green, warnings remain `1132/159`, and strict LHS audit is zero. |
| `CTCC-CIRCLE-4` | complete | `CircleConnected(x)` is the propositional truncation of the based-path fibre. Retained proposition evidence supplies the generating-loop `PathOver`, and dependent Circle induction constructs `circle_connected` with judgmental base computation. The tracked reviewer checks the fibre, evidence, loop coherence, base beta, absence of an untruncated path choice, and dependent-endpoint non-collapse. The rule-free source/reviewer checks are focused-green, warnings inherit `1132/159`, and strict LHS audit is zero. |
| `CTCC-CIRCLE-5` | complete | Mere connectedness is eliminated into paths of `Trunc_grpd(0,Circle_grpd)` and set-truncation induction contracts every point. `circle_set_trunc_is_contr` proves `IsContr(Trunc_grpd(0,Circle_grpd))`; its centre and constructor/base cases compute, while a tracked negative rejects judgmental carrier equality with `Unit_grpd`. No missing owner, rule, unifier, or unrestricted eliminator was required. Focused source/reviewer checks are green, warning evidence is unchanged, and strict LHS audit is zero. |
| `CTCC-PUBLIC-6` | complete | The two focused reviewer examples are registered. Root and kernel READMEs, source authority, current SOP, Foundations, canonical notation, report index, and the parent decision ledger now describe only implemented claims and preserve the classified-versus-decoded and evidence-versus-carrier boundaries. Report-header, source-TOC, active-reference, shell-syntax, Python-compilation, strict-catalog, and diff-whitespace checks pass. |
| `CTCC-CLOSE-7` | complete | Focused source/reviewer checks, exact `1112/159 -> 1132/159` warning comparison, strict zero-unreviewed-clause LHS audit, strict unchanged 2,114-check catalog, source-TOC/report-header/active-reference/diff gates, and exact current health are green. Health covers 76 core/extension files and 100 reviewer examples with all 176 passing, zero resumed evidence, and no timeout. The one required health refresh replaced stale generated evidence; redundant maintained and repository-wide aggregates were not rerun. |

## 7. Validation policy

1. Keep every Lambdapi invocation below the active 90-second per-target
   ceiling.
2. For each new rule or unifier, use an owner-position full-file probe,
   positive typed consumer, negative/non-collapse consumer, warning
   comparison, subject-reduction check, and strict LHS audit.
3. Prefer no `unif_rule` in the first facade/reflector slice. If a proof-time
   comparison becomes necessary, document why neither side is a runtime
   normal form and validate it with typed `eq_refl`.
4. Run the active source, new module, and nearest reviewer during iteration.
   Run catalog/health only when maintained assertions or source inventory
   actually changes. Do not rerun `make check`, `make examples`, `make ci`, or
   repository-wide aggregates merely for reassurance when focused evidence
   already covers an unchanged boundary.
5. Treat warnings as diagnostic evidence, not an automatic veto. Reject
   subject-reduction failures, unreviewed LHS growth, unintended proof
   erasure, and unbounded normalization.
6. Checkpoint only a bounded green tranche whose ledger and exact staged diff
   are synchronized, and only when local checkpoint commits are explicitly
   authorized. No other Git or publication mutation is implied.

## 8. Explicit exclusions and stop conditions

This goal does not include:

- generic `Groupoidify` or its adjunction;
- `GrayHom`, Gray tensor, or `I tensor I`;
- arbitrary quotient, pushout, suspension, or HIT declaration schemas;
- proof irrelevance or broad truncation-evidence erasure;
- unrestricted elimination out of truncation;
- a claim that the sorted primitive interface is already a complete semantic
  construction in every model;
- importing truncation into existing scheme/site mathematics before a later
  consumer explicitly reopens it; or
- book/article integration.

Stop or repartition when:

1. the sorted result cannot realize directly through `TruncGrpdU(n)` without
   duplicating package identity;
2. subject reduction requires an eliminator stronger than elimination into
   classified `n`-types;
3. a map/functor rule duplicates generic action rather than projecting the
   recursor;
4. Circle connectedness would require an untruncated path choice or a new
   Circle computation rule;
5. a proposed rule causes an unbounded check or an unclassified critical
   interaction; or
6. the conditional contractibility result requires a missing general owner
   large enough to deserve its own plan row.

## 9. Baseline evidence

At branch creation:

- worktree: `/home/user1/emdash1-groupoidal-circle-v1`;
- branch: `goal/computational-truncation-v3.2`;
- baseline: `2fe1e54530eb549efb7debf6a9157d42a2c6e1cf`;
- tracked status: clean;
- `timeout 90s lambdapi check emdash3_2.lp`: exit `0` in approximately
  2.3 seconds with the existing warning inventory; and
- no long aggregate was run.

The first `CTCC-NTYPE-1` owner probe is
`tmp/probes/computational_truncation_ntype_facade.lp`. Its quiet and
warning-enabled runs both pass. The warning count changes from the inherited
`1112/159` to `1132/159`; all twenty added unjoinable reports are rooted at
the explicit `NType_cat(n)` composition delegation, and replaceable-pattern
warnings remain unchanged. The strict LHS audit reports zero unreviewed
clauses. The same declarations are now promoted to
`emdash3_2_truncation_reflector.lp`, whose direct bounded check passes. The
tracked reviewer is `examples/computational_truncation_facade.lp`; it adds the
foreign-category and wrong-level negatives. The module is registered in
`scripts/check.sh`, `scripts/check_metrics.py`, `AGENTS.md`, and the current
status/SOP authority map. A resumable health regeneration was attempted after
registration, but the changed registry snapshot caused a broad rerun rather
than narrow cache reuse. It was intentionally interrupted after 44 green
targets, before report emission, under this plan's no-redundant-aggregate
policy. Exact health regeneration remains one `CTCC-CLOSE-7` gate.

`CTCC-CIRCLE-4` and the conditional `CTCC-CIRCLE-5` both promoted without a
new computation rule. The rule-free `emdash3_2_circle_connectedness.lp`
constructs `Pi x:S1, ||circle_base=x||_-1`, with point computation inherited
from `circle_ind`, then eliminates those merely inhabited based-path fibres
into the set truncation and contracts every point by restricted truncation
induction. The tracked reviewer checks proposition evidence, loop `PathOver`,
base computation, absence of an untruncated path choice, exact centre and
constructor/base contraction computation, and non-collapse of the carrier to
`Unit_grpd`. Direct source/reviewer checks pass, strict LHS audit is zero, and
the rule-free tranche leaves the measured `1132/159` warning boundary
unchanged.

## 10. Closure verdict

The bounded computational-truncation/Circle-connectedness objective is
complete. The active additions are:

- `emdash3_2_truncation_reflector.lp`, owning the classified `NType_cat(n)`
  facade, `Trunc_ntype`/`Trunc_grpd` result, restricted point-computing
  induction/recursion, recursor-derived map laws, and iterable whole Path
  action;
- `emdash3_2_circle_connectedness.lp`, owning mere based connectedness and
  contractibility of the set truncation without an untruncated path choice or
  a carrier rewrite to Unit; and
- their focused tracked reviewers
  `examples/computational_truncation_facade.lp` and
  `examples/circle_connectedness.lp`, including the required negative and
  non-collapse boundaries.

The inherited kernel warning inventory is `1112/159`. The classified
`NType_cat(n)` composition facade contributes exactly twenty unjoinable
critical-pair diagnostics and no replaceable-pattern growth, so the owning
truncation/Circle closure is `1132/159`. Circle connectedness and
contractibility add no rule or warning family. The strict LHS audit reports
zero unreviewed clauses, and the existing strict catalog remains current at
2,114 classified checks.

The generated health report is current across 176 maintained targets: 76
core/extension files and 100 reviewer examples, all passing with a 90-second
per-target ceiling, zero resumed results, and 1,626.623 seconds total. Its
source-metrics snapshot is
`sha256:19141dc0f20f68b2225dc945d0f1cf10405e0a99d4564465b5726657b12b3dd9`;
its checked-content snapshot is
`sha256:864d52499a6278c588a50ee5c0d6b30aa341f9925fc23dcec9262f91dcf5e555`.
This was the one aggregate required after the maintained registry changed.
No redundant `make check`, `make examples`, `make ci`, or root aggregate was
run.

The public authority map, current SOP, Foundations, canonical notation,
READMEs, report index, parent ledger, generated health, and living plan are
synchronized. Report-header, source-TOC, active-reference, shell-syntax,
Python-compilation, health-script unit, strict-catalog, strict-LHS, and exact
diff checks pass. Generic groupoidification, Gray tensor, classical
hub-and-spoke comparison, arbitrary quotient/HIT schemas, scheme integration,
and book/article work remain separate consumer-gated goals. No checkpoint
commit had been authorized at semantic closure. The user subsequently
authorized a local checkpoint. The bounded implementation is checkpointed at
`998c60f26adacee2b2211353e3e60e0f84b529aa`; this ledger-only follow-up records
that fact. No push, merge,
publication, release, history rewrite, branch deletion, or worktree removal
was performed.

## 11. Persistent-goal launch boundary

The persistent objective should delegate implementation details to this file
and its parent decision record. It may approve unattended continuations only
inside the rows and exclusions above, after synchronizing the ledger. It must
use focused probes and eagerly avoid long aggregates unless omission of one
would block an actual closeout gate. It may not push, merge, publish, release,
rewrite history, delete branches/worktrees, or modify sibling repositories.
