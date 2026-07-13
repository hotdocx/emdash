# EMDASH v3.2 Displayed Identity And `tdapp0` Coherence Cleanup Plan

Date: 2026-07-13
Last reviewed: 2026-07-13
Plan-ID: EMDASH-V3-2-DISPLAYED-IDENTITY-TDAPP0-COHERENCE-CLEANUP-2026-07-13
Depends-On: EMDASH-V3-2-PRIMITIVE-PI-ELIMINATOR-AUDIT-REDESIGN-2026-07-13; EMDASH-V3-2-DISPLAYED-FACADE-TOWER-REARCHITECTURE-2026-07-11; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Supersedes: no whole report; closes the classified identity and generic naturality/composition follow-up from the primitive-Pi eliminator audit
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-analysis-2026-07-13
Infinity-Codex-Decision-Responses: current-session-user-direction-2026-07-13
Status: promoted; identity and naturality cleanup complete, strict vertical-composition contraction classified and deferred pending an outer-category-preserving projection owner, full handoff gate passed

## Goal

Complete the coherence cleanup exposed by the generic Cat-valued component
projection:

1. make the displayed-transfor identity a transparent view of generic `id`,
   consistently with `id_func` and `id_funcd`;
2. preserve the existing identity-specialized displayed internal-hom
   computation without a second identity constructor;
3. join the meaningful identity, vertical-composition, and naturality paths
   through `tdapp0_func` / `tdapp0_fapp0`;
4. distinguish a missing semantic projection from a merely reported generic
   critical pair before adding any exceptional commuting bridge.

The selected runtime owner remains the global `id` / `comp_fapp0` /
`fapp*` / `tapp*` calculus. `tdapp0_func` and `tdapp0_fapp0` are projection
heads that retain the displayed component rung; they do not become a second
source of ordinary functor laws.

## Recovered Baseline

The bounded active check passes. The warning inventory inherited from the
primitive-Pi eliminator work is:

```text
warnings                         1,257
unjoinable critical pairs        1,094
replaceable pattern variables      163
```

The four newly classified critical pairs consist of two identity
presentations and two generic naturality/composition interactions around the
new capped projection

```text
fapp1_fapp0(tapp0_func(K,Cat,E,D,z),FF,GG,eta)
  -> tdapp0_fapp0(K,E,D,FF,GG,z,eta).
```

Warning count is diagnostic evidence, not the promotion criterion.

## Identity Audit

The active identity family is currently asymmetric:

```text
id_func(A)   := id(Cat_cat,A)
id_funcd(E)  := id(Catd_cat(K),E)

id(Functord_cat(E,D),FF) -> id_transfd(FF)
```

The first two are transparent public views. `id_transfd` is instead a
primitive constant and runtime normal form. No active `id_transf` symbol
exists; ordinary transfor identities are written directly with generic `id`
at `Functor_cat`.

The preferred migration is therefore:

```text
id_transfd(FF) := id(Functord_cat(E,D),FF)
```

with the old `id(Functord_cat) -> id_transfd` rule removed. The public name may
remain as a readable compatibility view, but it must no longer own a distinct
normal form. Every identity-specialized displayed internal-hom rule must then
match generic `id` at its typed consumer. The probe must exercise both the
stable displayed category presentation and the proof-time-comparable ordinary
`Transf_cat(K,Cat,E,D)` presentation.

## `tdapp0` Laws To Probe

### Identity component

The required component law is:

```text
tdapp0_fapp0(z,id(FF)) = id(Fibre_func(FF,z)).
```

It should be owned by the existing component-evaluation projection and the
generic identity-component law. A narrow consumer rule is acceptable only if
the stable `tdapp0_fapp0` head has erased the literal `tapp0_fapp0` pattern.

### Vertical composition

The required component law is:

```text
tdapp0_fapp0(z,eta o epsilon)
  = tdapp0_fapp0(z,eta) o tdapp0_fapp0(z,epsilon).
```

First probe whether normalizing the input through the ordinary
`tapp0_fapp0` owner already joins. If the stable capped projection prevents
that owner from matching, install at most one projection rule at
`tdapp0_fapp0`, oriented toward pointwise composition.

### Higher naturality

The remaining two warnings involve generic naturality cuts whose inner
functor-action component can now project to `tdapp0_fapp0`. They are not, by
themselves, evidence for a new broad law. For each warning:

1. instantiate the critical pair as a typed two-path probe;
2. determine whether identity/composition normalization makes it join;
3. if it still fails, locate the stable projection that erased the generic
   owner;
4. promote one specialized projection-order bridge only if both paths have a
   mathematically canonical common normal form and warning/subject-reduction
   audits remain bounded.

Do not duplicate generic transfor naturality on a new constructor-specific
surface merely to reduce the warning count.

## Implementation Phases

### Phase 0: plan, map, and baseline

1. Create and index this focused plan.
2. Re-read the active authorities and inspect staged/unstaged state.
3. Locate every active `id_transfd`, `tdapp0_func`, and `tdapp0_fapp0` owner
   and consumer.
4. Run the bounded baseline and preserve focused evidence under
   `tmp/probes/`.

### Phase 1: unify the displayed identity family

1. Probe `id_transfd` as a transparent alias of generic `id` in a full-file
   owner-position copy.
2. Replace identity-specialization patterns by typed generic-`id` patterns.
3. Exercise the displayed `Functord_cat` and ordinary `Transf_cat` spellings.
4. Compare subject reduction, warning inventory, and decision trees.
5. Promote only if all existing identity-specialized consumers still compute.

### Phase 2: component identity and composition

1. Add typed two-path probes for `tdapp0_fapp0(z,id)`.
2. Add typed two-path probes for vertical composites.
3. Test both displayed and ordinary comparable category presentations.
4. Promote the smallest consumer projections required by the stable capped
   head.

### Phase 3: higher naturality classification

1. Recompute warnings after Phases 1 and 2.
2. Extract the exact residual `tdapp0` critical pairs.
3. Probe both reduction orders at the real owner position.
4. Promote a bridge only when it expresses the same generic naturality law
   after a documented projection erasure; otherwise record the remaining
   global prerequisite instead of forcing a brittle encoding.

### Phase 4: diagnostics and documentation

1. Retain the `id_transfd` alias check and add direct generic identity checks.
2. Add one durable diagnostic per promoted identity/composition/naturality
   join.
3. Update the SOP, Foundations, canonical syntax, primitive-Pi eliminator
   decision record, and this report with the selected ownership boundary.
4. Regenerate the check catalog and health report.

### Phase 5: handoff gate

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

## Promotion Criteria

This cleanup is complete when:

1. `id_transfd` is either a validated transparent view of generic `id` or a
   measured report explains why a primitive identity normal form is required;
2. all six identity-specialized displayed internal-hom projections compute
   through the selected generic identity owner;
3. direct `tdapp0_fapp0` identity paths join their generic
   component-evaluation paths, and vertical composition either has a
   subject-reducing global-owner join or is isolated with the exact stable
   owner prerequisite rather than a brittle inferred-slot workaround;
4. each residual higher-naturality warning is either joined by one justified
   projection-order bridge or recorded with a precise missing owner;
5. no `id_transf`-style parallel identity constructor is introduced;
6. promoted rules pass subject reduction, focused two-path checks, strict LHS
   audit, warning classification, examples, and full local CI.

## Side-Task Ledger

- `IDTDAPP-01`: Create/index this plan, recover baseline, and map identity and
  component owners. Status: complete.
- `IDTDAPP-02`: Probe and, if healthy, promote transparent `id_transfd` plus
  generic-identity consumer patterns. Status: complete.
- `IDTDAPP-03`: Probe and promote the smallest `tdapp0_fapp0` identity and
  vertical-composition joins. Status: identity join complete; the general
  runtime vertical-composition contraction is precisely deferred because the
  capped projection no longer carries the outer category required for subject
  reduction.
- `IDTDAPP-04`: Reclassify and resolve or precisely defer the two higher
  naturality/composition critical pairs. Status: complete; four typed
  projection-order joins cover both naturality orientations and their two
  identity-base degenerations.
- `IDTDAPP-05`: Add diagnostics and synchronize active documentation. Status:
  complete.
- `IDTDAPP-06`: Run the complete handoff gate and record final metrics.
  Status: complete.

## Implementation Results

### One generic displayed identity

`id_transfd` is now a transparent compatibility view:

```text
id_transfd(FF) := id_(Functord_cat(E,D))(FF).
```

The former runtime fold from generic `id` to a second primitive identity head
has been removed. No active `id_transf` symbol exists. All six
identity-specialized displayed internal-hom consumers now match typed generic
identity directly. Each consumer accepts both the stable displayed
`Functord_cat(E,D)` presentation and the proof-time-comparable ordinary
`Transf_cat(K,Cat,E,D)` presentation.

The identity migration removed 19 critical-pair reports from the inherited
inventory. Durable diagnostics cover the public alias, every one of the six
consumer rungs, the ordinary façade spelling at the first and final rungs, and
the displayed component of identity at both category presentations.

### Component identity and higher naturality

The stable capped projection erased the literal generic identity pattern, so
two narrow component consumers were promoted:

```text
tdapp0_fapp0(z,id(FF)) -> id(Fibre_func(FF,z)).
```

They differ only in whether the typed identity is presented at
`Functord_cat(E,D)` or `Transf_cat(K,Cat,E,D)`.

Four projection-order joins were also promoted. They cover pre/right and
post/left ordinary naturality after one generic component action has projected
to `tdapp0_fapp0`, plus the two reduction orders in which
`tapp1(epsilon,id)` has already become `tapp0(epsilon)`. Each rule retains
only the outer category variable `$B`, because that variable is genuinely
shared with the surviving ordinary `tapp1`/`tapp0` operand and the RHS. The
three inferred `comp_fapp0` endpoints remain `_`, in accordance with the LHS
SOP. A product-valued target diagnostic establishes why `$B` cannot be
replaced by a rigid `Functor_cat` spelling.

### Strict vertical composition: classified prerequisite

The desired runtime normal form remains the generic strict-functor
orientation:

```text
comp(tdapp0(z,eta),tdapp0(z,epsilon))
  -> tdapp0(z,comp(eta,epsilon)).
```

Four owner-position candidates were measured:

1. Expanding `tdapp0(z,comp(eta,epsilon))` toward pointwise composition passed
   focused typing but intersected the general inner composition calculus. It
   duplicates the global functoriality owner and was rejected.
2. The minimal contraction with `comp_fapp0 _ _ _ _` failed subject
   reduction. Once both operands are stable `tdapp0_fapp0` heads, Lambdapi
   cannot recover the outer functor category needed to type the result.
3. Making the outer `Functor_cat` and the three `tapp0_fapp0` endpoints
   explicit made the ordinary-target probe fire, but the rule missed the
   product-valued case after
   `Functor_cat(X,Product_cat(A,B)) -> Product_cat(...)`. Those inferred slots
   are therefore not legitimate universal LHS discriminators or guards. This
   candidate was rejected under the SOP rather than annotated and promoted.
4. A temporary two-rigid-head proof-time `unif_rule` passed typed `eq_refl`
   probes, including the product target. This established only mechanical
   proof-time feasibility: the experimental pattern had not earned retention
   of its inferred slots under the rewrite/unification LHS SOP. More
   importantly, it did not join runtime conversion or the critical pair.
   Strict functor composition is a runtime law, so even a subsequently
   minimized unification pattern would only conceal the missing computational
   owner.

The remaining prerequisite is structural: a future redesign must preserve a
stable outer-category owner through the capped projection, or otherwise keep
the generic `fapp1_fapp0(tapp0_func)` owner visible until its composition cut
has accumulated. It must not recover the category by hard-coding reducible
inferred endpoints. This is narrower than, and independent of, the completed
identity and naturality cleanup.

### Warning and LHS evidence

After the identity migration and the complete naturality package, the active
inventory is:

```text
warnings                         1,272
unjoinable critical pairs        1,109
replaceable pattern variables      163
```

The naturality package adds 34 classified reports while the identity
migration removes 19, a net increase of 15 over the recovered 1,257-warning
baseline. Warning count was not used as a veto: the promoted rules pass typed
two-path and product-target diagnostics. The strict LHS audit reports zero
unreviewed candidates; the rejected vertical candidates are not present in
the active source.

## Final Validation Record

The promoted source, diagnostics, generated reports, and documentation pass
the complete handoff gate:

```text
make check             pass
make examples          pass
make warning-summary   pass
make audit-rules       pass; 0 unreviewed candidates
make catalog           pass
make toc               pass; 86 headings, sections 0-19
make health            pass; 8 checked files/examples
make ci                pass
git diff --check       pass
```

Final measured state:

```text
diagnostic assertions              791
unclassified checks                  0
intentional LHS annotations          37 slots across 21 clauses
warning inventory                 1,272
  unjoinable critical pairs        1,109
  replaceable pattern variables      163
```
