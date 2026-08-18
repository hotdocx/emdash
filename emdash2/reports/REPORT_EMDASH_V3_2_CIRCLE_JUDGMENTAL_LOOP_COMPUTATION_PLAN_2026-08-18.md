# Emdash v3.2 Circle Judgmental Loop Computation Plan

Date: 2026-08-18 (America/Toronto)

Plan-ID: `CIRCLE-JUDGMENTAL-LOOP-COMPUTATION-V3.2`

Status: **active living implementation plan**.

Parent:
`REPORT_EMDASH_V3_2_INTERNAL_LAXITY_AND_GROUPOIDAL_REALIZATION_CONTINUATION_PLAN_2026-08-17.md`

Depends-On: active `emdash3_2.lp`; `emdash3_2_circle_hit.lp`; completed
WalkingEnd--Circle extension, universality, and monodromy modules; current
Foundations, current status/SOP, canonical syntax, and nested Lambdapi SOP

Supersedes: no implementation plan. It promotes only the explicitly deferred
`WCGU-CIRCLE-COMP-TODO` row to an active bounded migration.

Reopens:
`REPORT_EMDASH_V3_2_WALKING_CIRCLE_GROUPOIDIFICATION_UNIVERSALITY_PLAN_2026-08-17.md`,
row `WCGU-CIRCLE-COMP-TODO` only. The completed WalkingEnd--Circle
universality result and its generic-groupoidification decision remain closed
evidence.

Side-Task-Ledger: `CJLC-00`, `CJLC-PROBE-1`, `CJLC-PROMOTE-2`,
`CJLC-CONSUMER-3`, `CJLC-GROUPIFY-HANDOFF-4`, and `CJLC-CLOSE-5`

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`; decision response `0047`, archived at
`/home/user1/emdash1/emdash2/tmp/ai-responses/sessions/2026-08-14_019ffe392eb9/responses/0047_2026-08-18T04-34-51Z_01a01322-f029-7f01-9030-f0af5473569a.md`.
Active code and SOP, then this plan and its parent decision records, outrank
the archive.

Infinity-Codex-Decision-Responses: response `0047`, archived at the absolute
path above. It clarifies that Circle loop computation is now dependency-ready
and that the completed generic-promotion decision did not cancel the larger
generic groupoidification objective.

Baseline: completed WalkingEnd--Circle closeout checkpoint
`cdf3f7cd23728c8850b6cd3df7358d22ba457332`

Worktree: `/home/user1/emdash1-circle-loop-v1`

Branch: `goal/circle-judgmental-loop-v3.2`

Git authority: the user's standing instruction authorizes this dedicated
local goal branch/worktree and validated local checkpoint commits. It does
not authorize push, merge, publication, release, history rewrite, branch
deletion, or worktree removal.

## Objective

Make the Circle path-constructor computation genuinely judgmental at the
canonical dependent owner, if the Lambdapi rewrite and subject-reduction
audits validate the intended normal form:

```text
apd(circle_ind(D,b,ell), loop)  -->  ell.
```

The promoted computation must retain the full dependent `PathOver` type. It
must not erase endpoint transport, introduce a second equality eliminator,
or turn unrelated `eq_apd` terms into Circle-specific normal forms.

Ordinary recursion is a derived constant-family facade. This tranche must
determine whether

```text
ap(circle_rec(B,b,ell), loop)  -->  ell
```

is already exposed by the dependent rule and existing constant-family
projection ladder. A second runtime rule is permitted only when a concrete
ordinary consumer cannot observe the dependent computation through that
ladder and a narrow owner-position projection passes the same audits.

## Why This Row Is Now Ready

The earlier universality plan deliberately left Circle point beta
judgmental and loop beta propositional while it tested whether the latter
blocked the whole mapping-object theorem. `WCGU-EQUIV-3` and the monodromy
consumer are now complete: propositional beta was sufficient, so no normal
form was changed implicitly during that theorem.

That sequencing condition is now discharged. The migration remains useful
on its own because it:

- realizes the intended computational-HIT interface at the generating path;
- gives later HITs a checked higher-constructor beta pattern;
- can simplify Circle code, extension, and monodromy observations without
  changing their mathematical statements; and
- supplies direct design evidence for the arrow-constructor beta of a future
  generic free-coherent-inversion `Groupoidify` HIT.

## Current Authority And Exact Gap

`emdash3_2_circle_hit.lp` currently owns:

```text
circle_ind(D,b,ell,base)  -->  b

circle_ind_beta_loop(D,b,ell)
  : apd(circle_ind(D,b,ell),loop) = ell.
```

The first line is a runtime rule. The second is opaque propositional
signature data. `circle_rec_beta_loop` and `circle_rec_beta_loop_path` are
derived from it. In contrast, the directed WalkingEnd HIT already has a
runtime generator beta at its canonical displayed action owner and a
computing ordinary observer. This plan does not copy WalkingEnd's directed
types; it copies only the owner-first computation discipline.

The first candidate owner-position rule is schematically:

```text
eq_apd(
  Circle,
  D,
  (lambda x, circle_ind(D,b,ell,x)),
  base,
  base,
  loop)
    --> ell.
```

Its actual left-hand side must follow the inferred-slot SOP: rigid Circle and
constructor heads are discriminators; inferred family/endpoints remain `_`
unless a measured subject-reduction or decision-tree reason requires an
explicit guard.

## Scope

### In scope

- exact inventory of `circle_ind_beta_loop`, `circle_rec_beta_loop`, and
  `circle_rec_beta_loop_path` definitions and consumers;
- a temporary full-file owner-position probe of the dependent beta;
- positive typed `eq_refl` evidence that the candidate fires;
- rejection for another path, motive, eliminand, or non-Circle action as
  appropriate;
- subject-reduction, critical-pair, warning-delta, decision-tree, and strict
  LHS audits;
- promotion of the smallest successful dependent runtime rule;
- conversion of the named dependent beta theorem to transparent reflexivity
  when its type computes;
- a measured decision on the ordinary constant-family projection;
- focused regression of Circle code, connectedness, WalkingEnd extension,
  universality, and monodromy consumers whose dependency closure changes;
- synchronization of active reports, source/example ownership, catalog, and
  exact resumable health evidence; and
- an evidence-backed handoff for generic groupoidification beginning with a
  walking non-endomorphism arrow and a composable pair/triangle.

### Out of scope

- changing `circle_base`, `circle_loop`, Circle dimensional evidence, or the
  encode/decode proof's mathematical content;
- rewriting arbitrary `eq_apd`, `eq_ap`, `PathOver`, or constant-family
  projections globally without an independently justified generic consumer;
- adding a second equality/J eliminator;
- declaring generic `Groupoidify_func`, its adjunction, or an opaque free
  inversion operation;
- implementing the walking-arrow or composable-pair groupoidification
  consumers in this bounded tranche;
- mirror Gray closure, global strict-cut migration, book/TypeScript/npm work,
  push, merge, release, or publication; and
- blind long repository-wide aggregates. Carry forward exact green evidence
  for unaffected boundaries and run only the proportional required closeout
  gates.

## Acceptance Tests

The dependent beta is accepted only if all of the following hold:

1. the rule is tested at its intended position in a temporary full copy of
   `emdash3_2_circle_hit.lp`;
2. a typed `eq_refl` proves that the `eq_apd` observation reduces to `ell`;
3. an intentionally mismatched observation remains rejected or stuck;
4. subject reduction remains enabled and green;
5. warning comparison identifies no unexplained overlap family;
6. the strict inferred-slot audit has no unreviewed candidate;
7. the Circle source and focused reviewer remain under the 90-second target
   ceiling; and
8. at least one real downstream loop consumer observes the new computation.

The ordinary beta becomes judgmental only if its own typed `eq_refl` succeeds
through the promoted dependent owner or through one narrowly justified
Circle-specific projection. A broad cancellation rule for every
`const_pathover_path(const_pathover(...))` is not authorized by this plan.

## Execution Ledger

| Row | Status | Deliverable and acceptance boundary |
| --- | --- | --- |
| `CJLC-00` | complete | The dedicated branch/worktree descends cleanly from `cdf3f7c`; staged and unstaged baselines were empty; the plan and parent ledgers are linked; the original-root Infinity archive verifies at 708 responses; report-header and active-reference lints pass; and direct Circle source/reviewer baselines are green under five seconds. The warning baseline is `1112` critical-pair plus `159` replaceable-slot diagnostics. No aggregate ran. |
| `CJLC-PROBE-1` | complete | The first direct rule correctly failed because public `eq_apd` was defined by `≔ ind_eqr`. A full active-kernel copy validated the narrow prerequisite: stable injective `eq_apd`, its reflexive beta, and a derived `eq_apd_ind_eqr_path`. The full Circle owner copy then accepted the higher-constructor rule, typed reflexivity, constant-family inheritance, and arbitrary-section non-collapse. Decision-tree inspection selects reflexivity versus the rigid Circle path/function shape; strict LHS audit is zero. Replacing either nested Circle motive/base guard by `_` fails subject reduction, so both are retained and annotated. Warning inventory remains exactly `1112/159`. |
| `CJLC-PROMOTE-2` | complete | `emdash3_2.lp` now owns stable `eq_apd`, its generic reflexive beta, and the transparent J-comparison theorem. `emdash3_2_circle_hit.lp` adds the selected dependent loop rule and makes `circle_ind_beta_loop` reflexivity; `circle_rec` inherits judgmental dependent `PathOver` beta. Ordinary `eq_ap` remains propositional: making it generically stable breaks the active half-adjoint fibre proof's definitional boundary, while the narrow alternative would match the expanded nested `const_pathover`/J tree and did not fire. No brittle outer-eliminator/inner-cut rule is promoted. |
| `CJLC-CONSUMER-3` | in progress | `examples/circle_judgmental_loop_computation.lp` owns positive typed reflexivity, named-theorem transparency, constant-family inheritance, arbitrary-section non-collapse, generic J comparison, and the explicit ordinary-`eq_ap` non-conversion boundary. Direct Circle source/reviewer, Circle connectedness, restriction, extension, universality, monodromy, and their focused downstream reviewers are green under five seconds each. Remaining: public authority/report synchronization and closeout evidence. |
| `CJLC-GROUPIFY-HANDOFF-4` | pending | Record that generic `Groupoidify` remains a valid separate construction. Define the next plan's first two source-shape probes—walking non-endomorphism arrow and composable pair/triangle—and the required indexed categorical-HIT unit/recursor/whole-beta-eta boundary. Do not add an opaque reflector here. |
| `CJLC-CLOSE-5` | pending | Synchronize Foundations, current status/SOP, canonical syntax, report index, diagnostics/catalog/health as affected; run proportional required gates; checkpoint a clean worktree; and record the next dependency-ready generic-groupoidification goal. |

## Validation Policy

Every Lambdapi target is bounded to 90 seconds. The inner loop is the
owner-position probe followed by the directly affected source/reviewer. Use
warning-enabled checks and strict LHS auditing for the candidate rule. Do not
rerun unchanged root TypeScript, browser, print, book, npm, or repository-wide
aggregates. A final kernel CI/health action is run only to the extent required
by the changed dependency closure and the active SOP; resumable exact evidence
must be reused for byte-identical unaffected targets.

## Initial Probe Finding — 2026-08-18

The literal candidate headed by public `eq_apd` cannot be added to today's
kernel: Lambdapi reports that no rewrite rule can be attached to a symbol
already defined with `≔`. This rules out both a direct Circle rule and a
proof-time variant at that head. It does not refute judgmental Circle loop
computation.

The smallest successful repair is to turn the already-public `eq_apd` into
the stable action owner it conceptually represents:

```text
injective eq_apd(f,p) : PathOver(P,p,f(x),f(y))
eq_apd(f,refl_x) --> refl_(f(x)).
```

The former transparent semantics remains internally recoverable through a
derived path

```text
eq_apd(f,p) = ind_eqr(p,...,refl_(f(y))).
```

proved by `ind_eqr`; no second equality eliminator or opaque comparison axiom
is needed. In a full copy of the active kernel, this stable owner and its
semantic comparison check. The later Circle-shaped constructor rule also
checks with inferred family/endpoints left as `_`, while an arbitrary
dependent section over the same generating path remains non-convertible to
the supplied constructor datum. Warning-enabled checking remains exactly at
the baseline `1112/159`.

This is a narrow generic prerequisite rather than a broad redesign of
`PathOver` or equality. The active inventory has 31 `eq_apd` references in
seven Lambdapi files; direct kernel and `path_category` checks confirm that
their existing reflexive and Pi-observer computations remain unchanged.

## Promoted Computation Result — 2026-08-18

The active kernel and Circle source now implement the successful design. The
public action `eq_apd` is a stable injective owner with the same reflexive
runtime beta as its former transparent `ind_eqr` definition. The theorem
`eq_apd_ind_eqr_path` derives their equality on every path by the sole
primitive equality eliminator. Existing direct kernel and `path_category`
checks confirm the reflexive/Pi observer boundary is retained.

The Circle rule is selected by the rigid `Circle_grpd`, `circle_ind`, and
`circle_loop` heads. It computes

```text
eq_apd((lambda x, circle_ind(D,b,ell,x)),circle_loop) --> ell.
```

The named `circle_ind_beta_loop` proof is consequently literal reflexivity.
After unfolding the derived `circle_rec`, the same rule computes its dependent
action to `const_pathover(circle_loop,ell)`. An arbitrary dependent function
over Circle does not reduce.

The separate ordinary `eq_ap` observer remains J-derived and propositional.
Two alternatives were rejected with direct probe evidence:

1. making generic `eq_ap` a stable owner causes the active
   `qinv_fibre_pathover`/half-adjoint proof to lose a definitional equality;
2. matching the Circle case at normalized `ind_eqr` would need to inspect the
   full second J tree produced by `const_pathover`, and the first narrow
   pattern did not match the actual normal form.

The latter is precisely the brittle commuting-conversion shape excluded by
the SOP. `circle_rec_beta_loop_path` therefore remains the safe readable
propositional `eq_ap` equation. This does not weaken the promoted HIT
constructor computation: dependent elimination and its canonical `PathOver`
action are judgmental.
