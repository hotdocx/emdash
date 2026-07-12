# EMDASH v3.2 Displayed Facade Tower Rearchitecture Plan

Date: 2026-07-11
Last reviewed: 2026-07-11
Plan-ID: EMDASH-V3-2-DISPLAYED-FACADE-TOWER-REARCHITECTURE-2026-07-11
Depends-On: REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26; EMDASH-V3-2-CAT-CATD-SPECIALIZATION-ALIAS-MIGRATION-2026-07-04; EMDASH-V3-2-PROF-CAT-PRIMITIVE-REDESIGN-2026-07-06; EMDASH-V3-2-FULL-NATURALITY-PRELIM-2026-06-12
Supersedes: no whole report; proposes a representation-boundary migration refining the current Functor/Catd and Transf/Functord runtime folds
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-analysis-2026-07-11
Infinity-Codex-Decision-Responses: infinity-codex:019f526a-dafb-77d0-9dea-2778a57275b7:019f526d-c79f-7850-8802-f99a59b0a028; infinity-codex:019f526a-dafb-77d0-9dea-2778a57275b7:019f52bb-060e-75c0-87bb-ef593b24310b
Status: core architecture promoted 2026-07-11; Sigma-first-projection section-fold demotion and sigma_map_transf off-diagonal action remain explicit deferred follow-ups

## Goal

Replace the current whole-category runtime collapses between the ordinary
Cat-valued functor/transfor hierarchy and the displayed-family hierarchy by a
levelwise, omega-extensible facade boundary.

The intended invariant is:

> Displayed heads remain stable category facades. Their equality with the
> corresponding ordinary iterated-hom presentation is proof-time. Runtime
> computation crosses the boundary only through documented `Obj` and
> `Hom_cat` projections.

This should preserve both kinds of information needed by the kernel:

- the ordinary `Functor_cat` / `Transf_cat` / iterated-`Hom_cat` heads remain
  visible to the generic `fapp*` / `tapp*` calculus;
- the displayed `Catd_cat` / `Functord_cat` / `Transfd_cat` heads remain
  visible to fibre, displayed-component, and higher-family projections.

The redesign is not a one-rule cleanup. It is a representation-boundary
migration whose correctness criterion is a coherent tower of category-level
proof-time comparisons and runtime eliminator projections.

## Active Baseline And Motivation

The active source currently selects displayed category heads as runtime normal
forms through:

```text
Functor_cat K Cat_cat
  ↪ Catd_cat K

Transf_cat K Cat_cat E D
  ↪ Functord_cat K E D.
```

The first fold means that a rule whose literal discriminator is
`Functor_cat ... Cat_cat` cannot see that head after normalization. The second
fold repeats the same choice one cell higher by erasing the literal
`Transf_cat ... Cat_cat` head.

The active source compensates with displayed-specific projection ladders, but
the result mixes two concerns:

1. mathematical/proof-time identification of two category presentations;
2. runtime projection of objects and homs from the displayed facade.

This plan separates them.

The validated active baseline at plan creation is:

```text
EMDASH_TYPECHECK_TIMEOUT=60s make check    pass
warning inventory                         1303
  unjoinable critical pairs               1140
  replaceable pattern variables            163
tracked working tree                      clean
```

Warning totals are diagnostic evidence, not a confluence gate.

## Mathematical Tower

The current named displayed hierarchy supplies the first three rungs of an
iterated-hom tower.

Define the displayed facade rungs:

```text
D0(K)       = Catd_cat K
D1(E,D)     = Functord_cat K E D
D2(FF,GG)   = Transfd_cat K E D FF GG.
```

Their ordinary presentations are:

```text
S0(K)       = Functor_cat K Cat_cat
S1(E,D)     = Transf_cat K Cat_cat E D
S2(FF,GG)   = Hom_cat (Transf_cat K Cat_cat E D) FF GG.
```

The displayed hom projections are already conceptually:

```text
Hom_cat(D0(K),E,D)       ↪ D1(E,D)
Hom_cat(D1(E,D),FF,GG)   ↪ D2(FF,GG).
```

At every named rung, the proposed schema is:

```text
category comparison:  Dn(...) ≡ Sn(...)       proof time
object projection:    Obj(Dn(...)) ↪ Obj(Sn(...))
hom projection:       Hom_cat(Dn(...),x,y) ↪ D(n+1)(x,y)
```

The category comparison must be direct at every represented rung. Lambdapi
unification rules are experimental and not reliably transitive, so the
`D2/S2` comparison must not be inferred by chaining the `D0/S0` and `D1/S1`
rules.

Future displayed-transfor levels should extend this schema rather than add
isolated conversions. If no named `D3` exists, the `D2` hom layer may remain
opaque until a concrete higher-cell consumer establishes its required
constructor and projections.

## Proposed First Three Rungs

### Rung 0: Catd as the displayed facade of Cat-valued functors

Replace the whole-category fold by:

```text
rule Obj (@Catd_cat $K)
  ↪ Obj (Functor_cat $K Cat_cat);

unif_rule
  Functor_cat $K Cat_cat
  ≡ @Catd_cat $K'
  ↪ [ $K ≡ $K' ];
```

The `Obj` rule is a runtime eliminator, not a broad category reclassification.
It states that a directed-family object is represented by an ordinary
Cat-valued functor while preserving `Catd_cat K` as a visible category head.

The proof-time-only object alternative is mechanically feasible:

```text
unif_rule
  Obj (@Catd_cat $K)
  ≡ Obj (Functor_cat $K' Cat_cat)
  ↪ [ $K ≡ $K' ];
```

A source probe for this alternative passed and produced fewer reported
critical pairs, but it removes the intended runtime decoding of the facade.
The current architectural preference is the runtime `Obj` projection because
the Foundations reading identifies a directed family with a Cat-valued
functor and because this matches the successful primitive-`Prof_cat` facade
pattern. Warning count alone does not decide the issue.

Keep the existing displayed hom projection:

```text
rule Hom_cat (@Catd_cat $K) $E $D
  ↪ @Functord_cat $K $E $D;
```

### Rung 1: Functord as the displayed facade of Cat-valued transfors

Replace the current whole-category transfor fold by:

```text
unif_rule
  @Transf_cat $K Cat_cat $E $D
  ≡ @Functord_cat $K' $E' $D'
  ↪ [
      $K ≡ $K';
      $E ≡ $E';
      $D ≡ $D'
    ];

rule Obj (@Functord_cat $K $E $D)
  ↪ Obj (@Transf_cat $K Cat_cat $E $D);
```

Use distinct variables on the two sides. Repeating `E`, `D`, or `K` in the
pattern can turn endpoint recovery into a match-time convertibility condition
instead of an explicit generated unification problem.

Keep the existing next hom projection:

```text
rule Hom_cat (@Functord_cat $K $E $D) $FF $GG
  ↪ @Transfd_cat $K $E $D $FF $GG;
```

### Rung 2: Transfd as the displayed facade of the ordinary next hom

Add the direct object projection and category-level comparison:

```text
rule Obj (@Transfd_cat $K $E $D $FF $GG)
  ↪ Obj
      (Hom_cat
        (@Transf_cat $K Cat_cat $E $D)
        $FF
        $GG);

unif_rule
  Hom_cat (@Transf_cat $K Cat_cat $E $D) $FF $GG
  ≡ @Transfd_cat $K' $E' $D' $FF' $GG'
  ↪ [
      $K ≡ $K';
      $E ≡ $E';
      $D ≡ $D';
      $FF ≡ $FF';
      $GG ≡ $GG'
    ];
```

This is the minimum explicit higher comparison required by the SOP rule that
unification-rule transitivity must not be assumed.

## Prof_cat Compatibility

The primitive `Prof_cat` facade already follows the same representation-
boundary architecture:

```text
Obj(Prof_cat(A,B))
  ↪ Obj(Catd_cat(Product_cat(Op_cat(A),B)))

Hom_cat(Prof_cat(A,B),P,Q)
  ↪ Functord_cat(P,Q).
```

Its proof-time endpoint recovery should use distinct variables for both base
components:

```text
unif_rule
  Prof_cat $A $B
  ≡ Catd_cat (Product_cat $A0 $B0)
  ↪ [
      $A ≡ Op_cat $A0;
      $B ≡ $B0
    ];
```

This formulation passed the full source/check probe and did not change the
candidate warning inventory.

Do not assume a direct proof-time comparison between `Prof_cat A B` and
`Functor_cat (Product_cat (Op_cat A) B) Cat_cat` by transitivity. Consumers
should use the explicit stable `Catd_cat` intermediary unless a concrete typed
consumer proves that a direct rule is necessary.

## Catd_cat_func Under The New Boundary

`Catd_cat_func : Cat_cat^op -> Cat_cat` is currently a transparent composition
through `Functor_cat_func`. Under the proposed orientation, its object action
naturally computes to:

```text
Functor_cat K Cat_cat
```

and compares with `Catd_cat K` at proof time. Therefore this plan does not
currently propose making `Catd_cat_func` primitive.

Its existing arrow-action rule must be rekeyed from the middle category
created by the old global fold:

```text
Catd_cat Cat_cat
```

to the literal middle category in the transparent definition:

```text
Functor_cat Cat_cat Cat_cat.
```

The arrow action should continue to compute to `Pullback_catd_func`.
Diagnostics which currently demand runtime equality of
`Catd_cat_func[K]` with `Catd_cat K` should become typed `eq_refl`
comparisons.

## Sigma Totalization As The Omega-Iteration Test

`Sigma_func(K) : Catd_cat(K) -> Cat_cat` is the key current test of whether the
facade tower interacts correctly with ordinary iterated functor action.

At objects:

```text
Sigma_func(K)[E] = Sigma_cat(E).
```

At the first hom level, the generic full hom action has type:

```text
(Sigma_func K)_1[E,D]
  : Functord_cat(E,D)
      -> Functor_cat(Sigma_cat(E),Sigma_cat(D)).
```

Its capped object action is already owned by:

```text
Sigma_func(K)[FF] = sigma_map_func(FF).
```

At the next hom level, generic iteration predicts:

```text
((Sigma_func K)_1[E,D])_1[FF,GG]
  : Transfd_cat(FF,GG)
      -> Transf_cat(sigma_map_func(FF),sigma_map_func(GG)).
```

The exact kernel source term is the hom action of:

```text
@fapp1_func
  (Catd_cat K)
  Cat_cat
  (Sigma_func K)
  E D.
```

The generic `fapp1_func` / `fapp1_fapp0` calculus supplies the type of this
iteration, while the facade rules identify its source and target hom
categories. What remains to probe is whether the capped higher action already
computes through existing generic projections or needs a named stable
`sigma_map_transf`-style projection head.

Do not identify this operation automatically with `Sigma_transfd_funcd`.
The existing `Sigma_transfd_funcd` is a related but different telescope-
uncurrying construction:

```text
eta : Transfd(S,T)
  |-> Sigma_transfd_funcd(eta)
       : Functord(Sigma_catd_functord_catd(S),
                   Sigma_catd_functord_catd(T)).
```

It is a useful prototype and consumer for higher Sigma behavior, but it is not
definitionally the general second-hom action of `Sigma_func`. The Sigma probe
must state both types explicitly and determine their exact relationship before
adding a bridge.

This makes `Sigma_func` a model for omega iteration, not a second owner of
ordinary functoriality. Generic `fapp*` remains the sole owner; any Sigma-
specific rule must expose a projection hidden by totalization.

### Sigma continuation-probe conclusion

The focused probe `tmp/probes/dfacade_sigma_iteration_probe.lp` confirms that
both generic iterable terms are already well typed:

```text
(Sigma_func K)_1[E,D]
  : Functord_cat(E,D)
      -> Functor_cat(Sigma_cat(E),Sigma_cat(D))

((Sigma_func K)_1[E,D])_1[FF,GG]
  : Transfd_cat(FF,GG)
      -> Transf_cat(sigma_map_func(FF),sigma_map_func(GG)).
```

The capped second action therefore already takes a displayed `Transfd` object
to an ordinary `Transf` object at the type level. Its point component does not,
however, reduce to the expected `sigma_arrow` in the active calculus.

The continuation probe installs a narrow stable projection:

```text
sigma_map_transf(eta)
  : Transf_cat(sigma_map_func(FF),sigma_map_func(GG)),
```

links the generic second action to it, and computes its component at `(k,u)`
to the fibrewise component over `id_k`, packaged by `sigma_arrow`. The full
source and check probes pass. A second variant introduced a new stable owner
for the entire first-hom functor; it also passed, but added another global
owner and four more critical-pair warnings than the narrower projection. The
narrow `sigma_map_transf` design was therefore selected and is now the
promoted projection.

`Sigma_transfd_funcd` is not that second-hom action. Its result is a displayed
functor between the two `Sigma_catd_functord_catd` families, whereas
`sigma_map_transf` is an ordinary transfor between total functors. The probes
establish related fibrewise behavior but different source and target types;
no bridge between them is currently justified.

The point projection is validated. A dedicated off-diagonal `tapp1_*`
projection is still deferred until its complete base-arrow/fibre-cell formula
and a concrete higher consumer are identified.

## Constant-Section Fold Probe Decision

The active source contains:

```text
rule
  Functord_cat
    (Const_catd K Terminal_cat)
    (Const_catd K A)
  ↪ Functor_cat K A.
```

This is the section formula:

```text
Pi_k Const_K(A) = Functor_cat(K,A).
```

The facade-tower probe showed that demoting the global
`Transf_cat -> Functord_cat` fold requires a join for the competing object
paths. The first successful candidate used:

```text
rule Obj
      (Transf_cat
        (Const_catd K Terminal_cat)
        (Const_catd K A))
  ↪ Obj (Functor_cat K A).
```

This object rule is mathematically meaningful: an ordinary Cat-valued
transfor from the terminal constant family to the constant `A` family encodes
an ordinary functor `K -> A`. It is nevertheless not sufficient to settle the
whole category fold.

If the current whole-category rewrite is demoted to proof-time comparison:

```text
unif_rule
  Functord_cat
    (Const_catd K Terminal_cat)
    (Const_catd K A)
  ≡ Functor_cat K0 A0
  ↪ [ K ≡ K0; A ≡ A0 ];
```

then the next hom layer must also be addressed directly:

```text
Transfd_cat(K,Const(Terminal),Const(A),s,t)
  versus
Transf_cat(K,A,s,t).
```

A complete probe must therefore compare at least three options:

1. retain the whole-category section fold and add the measured object-path
   join required by the new facade boundary;
2. demote the section fold to proof time, retain a runtime object projection,
   and add direct next-hom comparison/projection rules;
3. make both category and object comparisons proof-time only and identify the
   exact runtime projections needed by `piapp0`, section homs, and downstream
   Sigma/Pi consumers.

For every option, test:

- `Pi_cat(Const_catd K A)` at category, object, and hom levels;
- `piapp0` and ordinary functor application;
- `Hom_cat(Pi_cat(Const A),s,t)` versus `Transf_cat(s,t)`;
- both owner-first and projection-first reduction orders;
- the terminal-source component rule used by the homd/section pipeline;
- warning and subject-reduction effects.

The three-option continuation probe selected option 3:

- the section-category comparison is proof-time;
- the terminal-to-constant object comparison is also proof-time, with direct
  rigid-headed rules for both the ordinary `Transf_cat` and displayed
  `Functord_cat` presentations;
- the next-hom `Transfd_cat`/ordinary `Transf_cat` comparison is direct and
  proof-time;
- runtime section computation crosses through `piapp0`, displayed component
  projections, and named constant-section owners rather than an `Obj` fold.

This policy exposed two real prerequisites. The hom action of
`const_section_func` must remain displayed, so the probe adds
`Const_transfd_func` and `Const_transfd` with a fibre-component projection.
Also, ordinary weakening `Const_func_func(A,B)` can no longer be a transparent
alias through the displayed `const_section_func(A,B)`; it needs its own
ordinary stable owner with ordinary `Const_func`/`Const_transf` projections.
This is not cosmetic duplication: the two constructors now live on opposite
sides of a proof-time-only facade boundary.

The complete source/check probes pass for all three options, but option 3 has
the clearest runtime ownership and the smallest warning inventory. It was
subsequently promoted as recorded below.

## Probe Evidence At Plan Creation

The owner-position full-file probe
`tmp/probes/catd_facade_tower_level2_prof_endpoints_probe.lp` implements:

- `Obj(Catd_cat) -> Obj(Functor_cat(...,Cat_cat))`;
- category-level Functor/Catd unification;
- category-level Transf/Functord unification;
- `Obj(Functord_cat) -> Obj(Transf_cat(...,Cat_cat))`;
- the direct Transfd/ordinary-next-hom comparison and object projection;
- the `Catd_cat_func` arrow-action rekeying;
- the terminal-to-constant transfor object join;
- explicit two-endpoint `Prof_cat` recovery.

The companion check probe
`tmp/probes/catd_facade_tower_level2_prof_endpoints_checks_probe.lp` converts
category-identification assertions to typed `eq_refl` checks and adds focused
runtime object-projection diagnostics.

Results:

```text
full source probe                         pass
full diagnostic probe                    pass
warning-enabled source probe             pass

active warnings                          1303 = 1140 + 163
facade-tower candidate warnings          1282 = 1119 + 163
```

A source-only variant using proof-time-only `Obj(Catd_cat)` comparison also
passed:

```text
proof-time-only Obj variant warnings     1273 = 1110 + 163
```

These counts do not select the semantic policy. They show that the proposed
facade tower does not introduce an obvious warning explosion and that both
object-boundary orientations are mechanically plausible.

## Continuation Probe Evidence, 2026-07-11

The constant-section variants were tested as owner-position full-file source
copies with the complete diagnostic module:

```text
option 1: retain whole-category and Obj folds       1282 = 1119 + 163
option 2: category proof-time, Obj runtime          1287 = 1124 + 163
option 3: category and Obj proof-time               1247 = 1084 + 163
```

Option 2 and option 3 both require the displayed constant-transformation
owner and the split ordinary weakening owner described above. Option 3 also
passed typed `eq_refl` diagnostics for the section category, both direct
object comparisons, and the direct next-hom comparison, plus runtime
`piapp0`, ordinary functor application, and displayed component checks.

The selected combined probe is:

```text
tmp/probes/dfacade_facade_sigma_constant_option3_probe.lp
tmp/probes/dfacade_facade_sigma_constant_option3_checks_probe.lp
```

It combines the first three facade rungs, explicit two-endpoint `Prof_cat`
recovery, option 3 for constant sections, and the narrow
`sigma_map_transf` projection. Results:

```text
full source probe                         pass
full diagnostic probe                    pass
warning-enabled source probe             pass
strict inferred-slot audit               pass
combined warnings                        1253 = 1090 + 163
```

The six critical pairs added by `sigma_map_transf` relative to option 3 are
the measured interactions with generic identity/composition and reducible
Sigma endpoints. No constructor-specific identity or composition joins were
added: those laws remain owned by the generic calculus. Explicit inferred
source/target guards on the higher Sigma projection and constant-owner rules
are retained and annotated because the minimal-LHS variant increased the
combined inventory to `1261 = 1097 + 164` before the unused-pattern cleanup.
Warning counts remain diagnostic evidence rather than a semantic selection
criterion.

## Active Promotion And Wider-Fold Audit, 2026-07-11

The selected combined candidate has been promoted to `emdash3_2.lp` and
`emdash3_2_checks.lp`. The active implementation now contains all three facade
rungs, explicit `Prof_cat` endpoint recovery, the proof-time constant-section
boundary, displayed constant-transformation owners, the separate ordinary
weakening owner, and `sigma_map_transf` with its point projection.

The active warning inventory is the measured combined result:

```text
active warnings                          1253 = 1090 + 163
previous active warnings                 1303 = 1140 + 163
```

Promotion validation passes:

```text
make check
make examples
make warning-summary
make audit-rules
make catalog
make health
make ci
git diff --check
```

The diagnostic catalog contains `774` classified checks with zero
unclassified entries. The Sigma reviewer example includes the generic
second-hom action to `sigma_map_transf`.

The wider semantic-fold audit examined the remaining runtime contraction:

```text
Functord_cat
  (Sigma_cat K R)
  (Const_catd (Sigma_cat K R) Terminal_cat)
  (Sigma_proj1_pullback_catd K R D)
    -> Functord_cat K R D.
```

The first owner-position probe,
`tmp/probes/dfacade_sigma_projection_section_prooftime_probe.lp`, replaced it
with direct proof-time category, object, ordinary-object, and next-hom
comparisons. Source checking failed subject reduction at the existing
computation:

```text
path_ind_sec
  (Sigma_proj1_pullback_catd Z (Rep_catd Z x) D)
  u
    -> fib_cov_transf Z D x u.
```

The left side is owned by the section facade over the Sigma total, while the
right side is owned by `Functord_cat Z (Rep_catd Z x) D`. A proof-time category
comparison alone does not establish runtime subject reduction for that rule.

A follow-up hybrid probe,
`tmp/probes/dfacade_sigma_projection_section_runtime_layers_probe.lp`, kept
the whole-category comparison at proof time but added runtime projections for
the displayed `Obj` classifier, the ordinary `Obj(Transf_cat)` classifier
exposed by the global facade projection, and the next `Transfd_cat` hom. Those
runtime layers do restore subject reduction: the full source probe passes, so
the earlier failure is specifically a missing runtime projection and not
evidence that `Obj` must remain proof-time-only.

A three-way ablation then located the minimal subject-reduction owner. Removing
the direct displayed-`Obj` rule still passes, as does removing the next-hom
rule; removing the projected ordinary `Obj(Transf_cat)` join fails subject
reduction. The direct displayed-`Obj` rule is therefore redundant with the
global facade projection followed by that ordinary join. A cleaner probe
oriented the indispensable rule entirely between ordinary `Obj(Transf_cat)`
classifiers and also passes. The next-hom rule remains a plausible iterable
projection, but it is an architectural completeness choice rather than the
cause of the `path_ind_sec` repair.

The hybrid is nevertheless not promotable with the current category heads.
A typed `eq_refl` does not exercise either the direct same-head comparison
between the two `Functord_cat` applications or a comparison written through
`Pi_cat`: structural unification decomposes the incompatible arguments of the
shared `Functord_cat` head, and transparent `Pi_cat` unfolds to that same head.
The global contraction is therefore retained as a measured exception. Its
proper prerequisite is either a distinct stable Sigma-section category owner,
with the measured `Obj` and next-hom projection ladder, or an explicit
section-uncurrying functor/equivalence. The former stable owner would give a
pair of rigid heads on which the intended proof-time comparison can actually
operate.

## Implementation Phases

### Phase 0: Plan, inventory, and reproducible baseline

1. Record this architecture and add it to `reports/INDEX.md`.
2. Preserve the positive owner-position probes under ignored `tmp/probes/`.
3. Inventory every whole-category rewrite which identifies a displayed head
   with an ordinary head.
4. Inventory diagnostics which currently test those identifications by
   conversion rather than typed reflexivity.
5. Record the active warning summary and relevant decision trees.

### Phase 1: Rung-0 facade boundary and Prof endpoint hygiene

1. Replace `Functor_cat K Cat_cat -> Catd_cat K` by the selected object
   projection plus category-level unification rule.
2. Add focused runtime-`Obj` and typed-category diagnostics.
3. Rekey the transparent `Catd_cat_func` arrow action to the literal ordinary
   functor-category middle head.
4. Change the `Prof_cat` unification rule to recover both product endpoints
   explicitly.
5. Run a bounded source/check probe and warning comparison before promotion.

### Phase 2: Rung-1 and rung-2 facade boundaries

1. Demote `Transf_cat K Cat_cat E D -> Functord_cat K E D` to direct
   proof-time comparison.
2. Add the `Obj(Functord_cat)` runtime projection.
3. Add the direct `Transfd_cat` versus ordinary next-hom comparison and object
   projection.
4. Add typed diagnostics which prove that no comparison depends on
   unification-rule transitivity.
5. The original staging proposal for a terminal-to-constant object join was
   superseded by the completed Phase 4 probe; no such runtime join is
   promoted.

Phases 1 and 2 may be promoted together if separating them leaves the active
kernel in an architecture which typechecks only through temporary compatibility
scaffolding.

### Phase 3: Sigma omega-iteration probe

1. State the full type of the first hom action of `Sigma_func`.
2. Add a focused typed term for its next hom action on
   `eta : Transfd(FF,GG)`.
3. Test whether its capped result computes to an existing generic term or
   needs a stable Sigma-specific projection head.
4. Compare, without conflating, the result with `Sigma_transfd_funcd` in the
   telescope-to-constant-Cat specialization.
5. Test `tapp0_fapp0` and, where available, off-diagonal action of the result.
6. Record missing higher projections as prerequisites rather than installing
   a capped rule that loses the iterable functor object.

### Phase 4: Constant-section fold decision

The three-option probe selected option 3. The direct
category/object/next-hom unification rules, displayed
constant-transformation owner, ordinary weakening-owner split, and focused
diagnostics were promoted as one coherent change. The old whole-category and
terminal-to-constant `Obj` runtime folds were not retained as compatibility
scaffolding.

### Phase 5: Wider semantic-fold audit

Audit other whole-category semantic folds which may compete with facade object
projections, especially:

- sections over Sigma first-projection pullbacks;
- constant-family Pi contractions;
- product-valued transfor categories;
- any future terminal-source or product-indexed facade classification.

Do not demote them mechanically. Each fold requires a concrete owner,
consumer, and both-order probe.

The first audit pass is complete. Product-valued transfor computation remains
a genuine ordinary runtime projection. The Sigma-first-projection section fold
is retained for the `path_ind_sec -> fib_cov_transf` consumer. A hybrid probe
shows that one ordinary `Obj(Transf_cat)` classifier join repairs subject
reduction; a direct displayed-`Obj` rule is redundant, while a next-hom rule
would provide iterable projection rather than the immediate repair. The
whole-category proof-time comparison still requires the distinct stable
section owner (or explicit uncurrying construction) recorded above. No other
whole-category facade collapse was found that should be changed in this
migration.

### Phase 6: Promotion and documentation

1. Update comments which currently call `Catd_cat` or `Functord_cat` the
   runtime normal form of the ordinary hierarchy.
2. Update the living SOP and Foundations with the selected facade invariant.
3. Keep canonical surface syntax unchanged unless a notation ambiguity is
   discovered.
4. Migrate conversion assertions to runtime projection checks or typed
   `eq_refl` comparisons according to their intended layer.
5. Refresh the check catalog and health report.
6. Run the complete validation gate.

## Validation Matrix

Every promoted rung or semantic-fold change requires:

```text
focused owner-position full-file source probe
focused check probe with runtime and typed proof-time diagnostics
EMDASH_TYPECHECK_TIMEOUT=60s make check
warning-enabled comparison and warning classification
python3 scripts/audit_rule_lhs.py --strict
make catalog
make examples when Sigma/Pi reviewer milestones change
make ci
make health
git diff --check
```

For unification rules, use typed `eq_refl`; a bare `assert t ≡ u` tests only
runtime conversion. For every direct higher comparison, include distinct
endpoint variables on the two sides and explicit generated equality problems.

## Risks And Guards

### Unification is not transitive

Every represented facade rung needs its own direct comparison. Do not infer
`Transfd_cat ≡ Hom_cat(Transf_cat,...)` by chaining lower rules, and do not
infer `Prof_cat ≡ Functor_cat(Product(...),Cat_cat)` by chaining through
`Catd_cat`.

### Object projections can compete with inner category rewrites

An outer `Obj(Functord_cat(...))` projection and an inner specialized
`Functord_cat(...) -> ...` rewrite can reduce in different orders. Every such
case must have a documented join or a selected single owner.

### Stable facade heads are not ordinary-law owners

`Catd_cat`, `Functord_cat`, and `Transfd_cat` may own projections unavailable
on arbitrary categories. They must not duplicate generic identity,
composition, functoriality, or naturality already owned by `fapp*` / `tapp*`.

### Sigma iteration must remain functor-level

Do not replace the next hom action of `Sigma_func` by a pointwise-only rule.
The result must remain a functor or transfor object capable of further
iteration.

### Unification rules are trusted experimental infrastructure

Use only rigid-headed, narrowly typed comparisons with explicit endpoint
recovery. Add no bare-variable eta rules and no broad classification of
arbitrary product-indexed Cat-valued families.

## Non-Goals

- This plan does not identify the facade comparison itself with the complete
  Grothendieck straightening/unstraightening equivalence. `Sigma_cat` remains
  the active total-category construction.
- This plan does not add a finalized infinite family of displayed-transfor
  symbols before concrete higher-cell consumers exist.
- This plan does not split `emdash3_2.lp` into modules.
- This plan does not mechanically demote all mathematical equivalences to
  unification rules.
- This plan does not make warning-count reduction a semantic objective.
- This plan does not add direct `Prof_cat`/raw-`Functor_cat` comparison without
  a concrete consumer.

## Success Criteria

The redesign is successful when:

1. `Functor_cat K Cat_cat` and `Catd_cat K` remain distinct runtime category
   heads with a direct proof-time comparison;
2. `Obj(Catd_cat K)` has the selected documented projection/comparison with
   `Obj(Functor_cat K Cat_cat)`;
3. `Transf_cat K Cat_cat E D` and `Functord_cat K E D` remain distinct runtime
   category heads with a direct proof-time comparison;
4. `Obj(Functord_cat)` projects to the ordinary Cat-valued transfor object
   classifier;
5. `Transfd_cat` compares directly with the ordinary next hom and its object
   projection computes;
6. no intended comparison relies on unification-rule transitivity;
7. `Catd_cat_func` pullback action still computes from its transparent
   ordinary definition;
8. `Prof_cat` explicitly recovers both base endpoints;
9. the next hom action of `Sigma_func` is typed, tested, and either computes
   through a documented generic path or has a justified stable projection;
10. the constant-section fold has a recorded category/object/hom-level
    decision with both reduction orders tested;
11. comments, Foundations, SOP, diagnostics, catalog, and health report agree
    with the promoted architecture;
12. all validation commands pass and warning deltas are classified.

## Side-Task Ledger

- `DFACADE-01`: Map the active Functor/Catd, Transf/Functord, and
  Transfd/ordinary-next-hom tower. Status: complete in the 2026-07-11 design
  review.
- `DFACADE-02`: Reproduce a full owner-position facade-tower source/check
  probe, including explicit `Prof_cat` endpoint recovery. Status: complete;
  quiet and warning-enabled probes pass.
- `DFACADE-03`: Create and index the dedicated proposed architecture plan.
  Status: complete 2026-07-11; no kernel promotion is authorized by this item.
- `DFACADE-04`: Promote or revise the rung-0 object projection and category
  comparison after final warning/decision-tree review. Status: complete and
  promoted 2026-07-11.
- `DFACADE-05`: Promote or revise the rung-1 and rung-2 facade comparisons and
  projections. Status: complete and promoted with `DFACADE-04`.
- `DFACADE-06`: Probe the full first- and second-hom action of `Sigma_func`,
  including its precise relation to `Sigma_transfd_funcd`. Status: core probe
  complete and the narrow `sigma_map_transf` point projection is promoted;
  the generic iterable action passes, and the two Sigma constructions have
  distinct types. Off-diagonal action remains a prerequisite for any broader
  Sigma rule.
- `DFACADE-07`: Resolve the constant-section whole-category fold through the
  three-option category/object/hom probe. Status: complete; option 3, with
  displayed constant-transformation and separate ordinary weakening owners,
  was promoted 2026-07-11.
- `DFACADE-08`: Audit the Sigma-projection section fold and other competing
  whole-category semantic folds. Status: first audit and hybrid follow-up
  complete. Ablation shows that the projected ordinary `Obj(Transf_cat)` join
  alone repairs the `path_ind_sec` subject-reduction failure; the direct
  displayed-`Obj` rule is redundant, and the next-hom rule is independently
  motivated by iterability. The category comparison cannot be exercised
  through the current same `Functord_cat` head or transparent `Pi_cat`. The
  runtime fold remains until a distinct stable Sigma-section owner or explicit
  section-uncurrying construction is designed.
- `DFACADE-09`: Update the `Prof_cat` rule to recover `$B0` explicitly and add
  a focused inferred-endpoint diagnostic. Status: complete and promoted.
- `DFACADE-10`: Migrate diagnostics, comments, SOP, Foundations, catalog, and
  health report; run the complete handoff gate. Status: complete; all listed
  validation commands pass 2026-07-11.
