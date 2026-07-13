# EMDASH v3.2 Primitive Pi Facade Rearchitecture Plan

Date: 2026-07-12
Last reviewed: 2026-07-12
Plan-ID: EMDASH-V3-2-PRIMITIVE-PI-FACADE-REARCHITECTURE-2026-07-12
Depends-On: EMDASH-V3-2-DISPLAYED-FACADE-TOWER-REARCHITECTURE-2026-07-11; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Supersedes: no whole report; resolves the deferred Sigma-first-projection section owner from DFACADE-08 and refines the section-category layer used by the proposed general Pi-along-functor construction
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-analysis-2026-07-12
Infinity-Codex-Decision-Responses: infinity-codex:019f526a-dafb-77d0-9dea-2778a57275b7:019f547c-2fc3-7a61-81fc-184f11a90ed8
Status: promoted 2026-07-12; owner-position and active source, full-diagnostics, typed-comparison, runtime-projection, subject-reduction, warning-inventory, reviewer-example, and complete local-CI gates pass

## Goal

Promote `Pi_cat` from a transparent alias to the stable category facade for
sections of a displayed Cat-valued family. Its equality with the existing
terminal-source `Functord_cat` and ordinary Cat-valued `Transf_cat`
presentations becomes proof-time. Runtime computation crosses the facade
through explicit `Obj` and `Hom_cat` projections.

This general owner should replace the ad hoc need for a separate stable
Sigma-section category head. In particular,

```text
Pi_cat
  (Sigma_cat K R)
  (Sigma_proj1_pullback_catd K R D)
```

is the stable section facade whose proof-time uncurrying comparison is
`Functord_cat K R D`.

The architecture extends the displayed-facade invariant:

> Stable semantic category heads remain visible. Equality with alternative
> ordinary or displayed presentations is proof-time. Runtime `Obj` and
> `Hom_cat` projections expose the represented data and the next iterable
> hom layer.

## Scope And Distinction From General Pi Along A Functor

`Pi_cat(K,E)` is the category of global sections of one family
`E : K -> Cat`. Making it primitive does not implement the proposed general
dependent product/right Kan extension

```text
Pi_along_func(f) : Catd(A) -> Catd(B).
```

Rather, it provides the stable section-category owner used in each comma
fibre of that construction:

```text
(Pi_f E)[b]
  = Pi_cat(Pullback_catd(E,CommaOut_proj(f,b))).
```

The present migration is therefore a prerequisite/refinement for the
`Pi_along_func` plan, not a replacement for it.

## Active Baseline

At plan creation:

```text
tracked working tree                    clean
EMDASH_TYPECHECK_TIMEOUT=60s make check pass
warning inventory                       1253
  unjoinable critical pairs             1090
  replaceable pattern variables          163
```

The active definition is transparent:

```lambdapi
symbol Pi_cat [K : Cat] (E : τ (Catd K)) : Cat
≔ @Functord_cat K (@Const_catd K Terminal_cat) E;
```

This transparency prevents a proof-time comparison for Sigma-section
uncurrying from seeing distinct rigid heads: `Pi_cat` unfolds to the same
`Functord_cat` head as its target before the intended specialized comparison
can operate.

## Selected Primitive Facade

### Stable category head

```lambdapi
injective symbol Pi_cat [K : Cat] (E : τ (Catd K)) : Cat;
```

This is a stable facade, not a new independent semantics. Its current body is
retained through comparison and projection rules.

### Direct proof-time comparisons

General displayed section presentation:

```lambdapi
unif_rule
  @Pi_cat $K $E
  ≡ @Functord_cat $K' (@Const_catd $K' Terminal_cat) $E'
  ↪ [ $K ≡ $K'; $E ≡ $E' ];
```

Direct ordinary presentation:

```lambdapi
unif_rule
  @Pi_cat $K $E
  ≡ @Transf_cat $K' Cat_cat (@Const_catd $K' Terminal_cat) $E'
  ↪ [ $K ≡ $K'; $E ≡ $E' ];
```

Constant-family specialization:

```lambdapi
unif_rule
  @Pi_cat $K (@Const_catd $K $A)
  ≡ Functor_cat $K' $A'
  ↪ [ $K ≡ $K'; $A ≡ $A' ];
```

All three comparisons are direct because Lambdapi unification rules are not
reliably transitive. Each must be exercised by typed `eq_refl` rather than a
runtime conversion assertion.

### Runtime projection ladder

```lambdapi
rule Obj (@Pi_cat $K $E)
  ↪ Obj
      (@Functord_cat
        $K
        (@Const_catd $K Terminal_cat)
        $E);

rule Hom_cat (@Pi_cat $K $E) $s $t
  ↪ @Transfd_cat
      $K
      (@Const_catd $K Terminal_cat)
      $E
      $s
      $t;
```

The `Obj` rule projects into the existing displayed facade and then follows
its established ordinary classifier projection. The `Hom_cat` rule exposes
the next displayed rung directly, preserving iteration.

## Sigma-Section Uncurrying Instance

Replace the current whole-category runtime fold

```text
Functord_cat
  (Sigma_cat K R)
  ConstTerminal
  (Sigma_proj1_pullback_catd K R D)
    -> Functord_cat K R D
```

with the distinct-head proof-time comparison:

```lambdapi
unif_rule
  @Pi_cat
    (@Sigma_cat $K $R)
    (@Sigma_proj1_pullback_catd $K $R $D)
  ≡ @Functord_cat $K' $R' $D'
  ↪ [ $K ≡ $K'; $R ≡ $R'; $D ≡ $D' ];
```

Runtime object computation uses the general Pi and displayed projection
ladder, followed by the measured minimal ordinary classifier join:

```lambdapi
rule Obj
      (@Transf_cat
        (@Sigma_cat $K $R)
        Cat_cat
        (@Const_catd (@Sigma_cat $K $R) Terminal_cat)
        (@Sigma_proj1_pullback_catd $K $R $D))
  ↪ Obj (@Transf_cat $K Cat_cat $R $D);
```

A direct displayed `Obj(Pi_cat special)` rule is intentionally omitted: the
ablation probe established that it duplicates the general facade projection.

The iterable next-hom projection is:

```lambdapi
rule @Transfd_cat
      (@Sigma_cat $K $R)
      (@Const_catd (@Sigma_cat $K $R) Terminal_cat)
      (@Sigma_proj1_pullback_catd $K $R $D)
      $s $t
  ↪ @Transfd_cat $K $R $D $s $t;
```

The ordinary `Obj(Transf_cat)` join is the minimal rule required for subject
reduction of `path_ind_sec -> fib_cov_transf`; the next-hom projection is
separately justified by iterability.

## Consumer Migration

Most active consumers already state `Pi_cat` explicitly. The positive probe
found one semantic owner that relies materially on transparent unfolding:

```text
pi_eval_transf(E)
  : Functord(Const_K(Functord_cat(ConstTerminal,E)),E).
```

Retype its source canonically as:

```text
pi_eval_transf(E)
  : Functord(Const_K(Pi_cat(E)),E).
```

Retype the corresponding `tapp0_fapp0` projection discriminator in the same
way. This removes a representation leak; the component remains
`piapp0_func(E,k)`.

## Identity And Composition Audit

The source and full diagnostic probes pass without adding constructor-specific
identity or composition laws. Before declaring promotion complete, inspect:

- `id(Pi_cat E,s)` versus the existing `id_transfd` presentation;
- generic `comp_fapp0` at `Pi_cat E` after `Hom_cat` exposes `Transfd_cat`;
- `Pi_func(K)[id_funcd] -> id_func(Pi_cat E)`;
- whether any direct identity projection is demanded by a concrete consumer.

The global `fapp*`/`tapp*` calculus remains the sole owner of generic
functoriality. Do not add Pi-specific identity or composition rewrites unless
a focused consumer probe demonstrates a missing projection.

## Feasibility Evidence

Ignored owner-position probes:

```text
tmp/probes/primitive_pi_facade_probe.lp
tmp/probes/primitive_pi_facade_checks_probe.lp
tmp/probes/primitive_pi_facade_full_checks_probe.lp
```

Measured results:

1. the complete source passes with primitive `Pi_cat`;
2. typed `eq_refl` passes for all general and specialized category
   comparisons;
3. runtime `Obj` and `Hom_cat` projection assertions pass;
4. the Sigma-section category, object, and next-hom assertions pass;
5. `path_ind_sec -> fib_cov_transf` preserves typing through the ordinary
   classifier join;
6. after retyping `pi_eval_transf`, the complete diagnostic suite passes;
7. four old whole-category runtime assertions require migration to typed
   `eq_refl`;
8. the warning-enabled source probe has the same 1253-warning inventory as the
   active baseline.

This establishes feasibility, not final confluence or universal semantic
policy for every future dependent-product comparison.

## Promotion Result

The selected architecture is promoted in the active source. `Pi_cat` is an
injective stable facade with direct proof-time comparisons to its displayed,
ordinary, and constant-family presentations. Its `Obj` and `Hom_cat`
projections expose the represented section object classifier and the next
`Transfd_cat` hom.

The Sigma-first-projection whole-category rewrite has been removed. Its
replacement consists of the direct `Pi_cat`/`Functord_cat` proof-time
comparison, the measured ordinary `Obj(Transf_cat)` classifier join, and the
iterable `Transfd_cat` projection. The existing
`path_ind_sec -> fib_cov_transf` computation preserves typing.

`pi_eval_transf` now owns the canonical `Const_catd K (Pi_cat E)` source.
The identity/composition audit found no concrete consumer requiring a
Pi-specific generic law: the existing `Pi_func` identity diagnostic and the
general `Hom_cat(Pi_cat)` projection suffice, so global generic owners remain
unchanged.

Final validation:

```text
make check             pass
make examples          pass
make warning-summary   pass; 1253 = 1090 critical-pair + 163 pattern warnings
make audit-rules       pass; 0 unreviewed candidates
make catalog           pass; 776 classified checks, 0 unclassified
make toc               pass; 86 headings, sections 0-19
make health            pass; 8 files
make ci                pass
git diff --check       pass
```

The final warning inventory matches the positive owner-position probe. The
old category fold's overlap removal lowers the `fapp1_fapp0` and
`tapp0_fapp0` head counts by one each relative to the pre-migration summary;
the total warning count remains unchanged.

## Implementation Phases

### Phase 0: Plan and reproducible baseline

1. Create and index this plan.
2. Preserve the positive owner-position probes under ignored `tmp/probes/`.
3. Confirm staged/unstaged state and bounded baseline.

### Phase 1: Primitive Pi facade

1. Change `Pi_cat` from a transparent `symbol` to an `injective symbol`.
2. Add direct `Pi/Functord`, `Pi/Transf`, and constant-family comparisons.
3. Add runtime `Obj` and `Hom_cat` projections.
4. Add focused typed and runtime diagnostics.

### Phase 2: Evaluation owner

1. Retype `pi_eval_transf` through `Const_catd K (Pi_cat E)`.
2. Retype its component rule discriminator.
3. Retain `piapp0_func` as the named semantic evaluation interface; its
   runtime object and hom owners are audited in the 2026-07-13 primitive-Pi
   eliminator follow-up.

### Phase 3: Sigma-section uncurrying

1. Remove the whole-category `Functord_cat` runtime fold.
2. Add the `Pi_cat(Sigma,pullback) / Functord_cat` proof-time comparison.
3. Add the measured ordinary classifier join.
4. Add the iterable `Transfd_cat` next-hom projection.
5. Exercise both projection orders and path-induction subject reduction.

### Phase 4: Diagnostic and documentation migration

1. Change whole-category runtime assertions to typed `eq_refl`.
2. Preserve runtime assertions for `Obj`, `Hom_cat`, evaluation, and
   components.
3. Update the Foundations, canonical syntax, living SOP, displayed-facade
   decision record, source comments, catalog, and health report.

### Phase 5: Audit and handoff gate

Run:

```text
make check
make examples
make warning-summary
make audit-rules
make catalog
make toc
make health
make ci
git diff --check
```

Compare warning categories and locations, not only totals.

## Promotion Criteria

The migration is complete when:

1. `Pi_cat` remains visible as a stable category head;
2. general and specialized proof-time comparisons pass typed `eq_refl`;
3. runtime section object, hom, evaluation, and path-induction computations
   pass;
4. no direct redundant displayed-`Obj` Sigma rule is introduced;
5. no Pi-specific generic functoriality rules are added without a concrete
   consumer;
6. the complete diagnostics and reviewer examples pass;
7. warning changes are classified;
8. all architectural conclusions are recorded in active authorities.

## Side-Task Ledger

- `PIFACADE-01`: Create/index the plan and preserve feasibility evidence.
  Status: complete.
- `PIFACADE-02`: Promote the primitive category head, direct proof-time
  comparisons, and runtime projection ladder. Status: complete.
- `PIFACADE-03`: Retype `pi_eval_transf` and its component discriminator.
  Status: complete.
- `PIFACADE-04`: Migrate Sigma-section uncurrying and verify path-induction
  subject reduction. Status: complete.
- `PIFACADE-05`: Audit identity/composition and other transparent-alias
  consumers. Status: complete; no Pi-specific generic functoriality rule is
  justified by a current consumer.
- `PIFACADE-06`: Migrate diagnostics and active documentation. Status:
  complete.
- `PIFACADE-07`: Complete warning comparison and the full CI/handoff gate.
  Status: complete.

The follow-up
`REPORT_EMDASH_V3_2_PRIMITIVE_PI_ELIMINATOR_AUDIT_AND_REDESIGN_PLAN_2026-07-13.md`
confirms that `piapp0*` and `piapp1*` remain semantic definitions. It promotes
the missing generic full/capped hom projection from Cat-valued
`tapp0_func` evaluation to `tdapp0_func` / `tdapp0_fapp0`; it does not promote
Pi-specific eliminator heads.

## Deferred Boundaries

This plan does not implement:

- the general comma/right-Kan `Pi_along_func`;
- comparison of general comma fibres with strict fibres;
- Beck-Chevalley, adjunction, or exactness laws;
- a named `section_total` functor;
- arbitrary semantic uncurrying beyond the measured Sigma-projection case;
- new surface syntax.
