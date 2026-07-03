# EMDASH v3.2 Eckmann-Hilton Application Plan

Date: 2026-07-03
Last reviewed: 2026-07-03
Plan-ID: EMDASH-V3-2-ECKMANN-HILTON-APPLICATION-2026-07-03
Depends-On: EMDASH-V3-2-FULL-NATURALITY-2026-06-12; EMDASH-V3.2-DEFISO-HOM-ACTION-PROFCOMP-MIGRATION-2026-06-28; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Supersedes: none
Side-Task-Ledger: this-report#side-task-ledger
Infinity-Codex-Origin: current-session-analysis-2026-07-03
Infinity-Codex-Decision-Responses: none-yet
Status: implementation started; safe EH slice, hom-action proof lemmas, and component-level ordinary-transfor interchange promoted

## Purpose

This report plans a reviewer-facing v3.2 application around the
Eckmann-Hilton argument. The goal is not merely to add another diagnostic
conversion assertion. The application should expose ordinary mathematical
proof symbols in `emdash3_2.lp`, with proof terms of equality type
`τ (lhs = rhs)`.

Some steps should compute by reflexivity:

```text
lemma : τ (lhs = rhs) ≔ eq_refl normal_form
```

Other steps should be explicit proof terms using the existing equality
combinators:

```text
eq_trans
eq_sym
eq_ap
```

The existing `assert ... ≡ ...` diagnostics in `emdash3_2_checks.lp` remain
useful for DevOps/regression tracking of rewrite behavior. They are not the
intended presentation of the Eckmann-Hilton theorem.

## Mathematical Target

For a category `B`, an object `x : Obj(B)`, and the identity 1-cell

```text
i = id_B(x) : Hom_B(x,x),
```

the 2-endomorphisms of `i` are objects of:

```text
Hom_cat (Hom_cat B x x) i i.
```

Given:

```text
alpha beta : Hom_{Hom_B(x,x)}(i,i),
```

Eckmann-Hilton should demonstrate that the vertical composition of these
2-cells is commutative:

```text
beta · alpha = alpha · beta.
```

The intended proof route is the standard degenerate interchange argument:

```text
beta · alpha
  = beta * alpha
  = (beta · id_i) * (id_i · alpha)
  = (beta * id_i) · (id_i * alpha)
  = alpha · beta
```

The exact orientation and term order must follow the active `comp_fapp0`
convention:

```text
comp_fapp0 C x y z g f  =  g after f.
```

## Current Infrastructure

The active kernel already has the relevant 2-categorical substrate:

- `Hom_cat` iterates cells: homs are themselves categories.
- `id` and `comp_fapp0` give identity and vertical composition at every hom
  level.
- `hom_`, `hom_postcomp_tele_func`, `hom_postcomp_func`, and
  `hom_postcomp_fapp0` expose represented postcomposition.
- `hom_postcomp_tele_fapp1_func` and `hom_postcomp_tele_fapp1_fapp0` expose
  the higher action of postcomposition as the postcomposing arrow varies.
- `tapp1_func` and `tapp1_fapp0` expose off-diagonal transfor action.
- `comp_cat_cov_func_func_tapp1_fapp0` is the ordinary-transfor horizontal
  composite owner in the Cat-specialized functor-composition layer.
- `eq_refl`, `eq_trans`, `eq_sym`, and `eq_ap` are available for mathematical
  equality proofs.

The first-layer stable hom-action projection joins are already present. They
must be read carefully:

- the generic single-functor law in the core calculus is still the usual
  cut-elimination fold:

```text
F[q] o F[p]  ->  F(q o p)
```

This is implemented by the generic `fapp1_fapp0` rule on raw composites.

- the special `hom_postcomp_*` / `hom_precomp_along_*` rules below have the
  opposite-looking direction because they are stable projection joins. They
  normalize a hom-action applied to a composite base arrow into nested stable
  hom-actions. They are not a decision to reverse ordinary functoriality
  globally.

- postcomposition has stable functor-level and capped object-level folds
  corresponding to:

```text
(F(q o p))_*        -> (F q)_* o (F p)_*
(F(q o p))_*(g)    -> (F q)_*((F p)_*(g))
```

- precomposition has the contravariant stable functor-level and capped
  object-level folds:

```text
(F(q o p))^*        -> (F p)^* o (F q)^*
(F(q o p))^*(g)    -> (F p)^*((F q)^*(g))
```

- postcomposition has the represented-source accumulation:

```text
((F f)_*(g)) o h    -> (F f)_*(g o h)
```

These are reviewer-facing candidates for proof-by-reflexivity lemmas.

Their purpose is to state the current normal form of the hom-action projection
owners. If a theorem wants the usual folded mathematical presentation, for
example:

```text
(F q)_*((F p)_*(g))  =  (F(q o p))_*(g)
```

the first implementation strategy should be a theorem-style equality lemma
using `eq_refl` or `eq_sym`, not a global rewrite-orientation flip.

In the Došen-style reading, the upstream `hom_*` owners also computationally
control associativity where the term is already expressed through those
owners. The downstream ordinary-composition associativity rule is
intentionally only proof-time unification:

```text
(h o g) o f  ~~  h o (g o f)
```

That unification rule is semantically valid and useful for elaborating proofs,
but it is not the preferred runtime computation when an upstream hom-action
accumulation can choose the normal form.

The audit also found important raw semantic-presentation shapes. These should
not be treated as additional default runtime computations:

- the raw adjacent postcomposition presentation

```text
F[q] o ((F[p])_*(g))
```

stays as a raw `comp_fapp0`; it does not reduce directly back into the
stable hom-action owner. This is not the current runtime normal form of
the stable hom-action projection. The current stable projection computation is:

```text
(F(q o p))_*(g)  ->  (F q)_*((F p)_*(g))
```

When a concrete proof context naturally produces the raw
`F[q] o ((F[p])_*(g))` presentation, the intended bridge is proof-time
compatibility through the existing `hom_postcomp_fapp0` unification rule. In
particular, a typed equality may identify the raw composite with the nested
stable presentation:

```text
(F q)_*((F p)_*(g))
```

without adding a new runtime rewrite from raw `comp_fapp0` back into the
stable owner.

Mathematically, the folded presentation

```text
F[q] o ((F[p])_*(g))  ->  (F(q o p))_*(g)
```

is the usual direction one may want in a proof. The plan does not reject that
mathematical orientation; it only says not to install it as a runtime rewrite
until a concrete implementation roadblock shows that proof-time equality is
insufficient.

- the analogous raw adjacent precomposition term

```text
k o ((F[p])^*(g))
```

stays as a raw `comp_fapp0`; it does not reduce directly to
`(F[p])^*(k o g)`. This is likewise a proof-time compatibility case unless a
later concrete consumer requires runtime normalization.

- the source-side precomposition counterpart

```text
((F[p])^*(g)) o F[q]
```

also stays as a raw `comp_fapp0`; it does not reduce directly to
`(F(p o q))^*(g)` or to the current nested stable normal form. Again, the
primary functoriality orientation is:

```text
(F(p o q))^*(g)  ->  (F q)^*((F p)^*(g))
```

The existing `hom_precomp_along_fapp0` unification rule is the intended
proof-time bridge between the stable precomposition owner and its raw
`comp_fapp0` reading. A future runtime bridge remains possible infrastructure
only if a checked proof or example needs judgmental reduction there; it is not
part of the EH first-slice plan.

- the corresponding naturality/ordinary-transfor accumulation is already
  represented in the active file. At the capped component level:

```text
G[h] o epsilon[f]  ->  epsilon[h o f]
epsilon[f] o F[h]  ->  epsilon[f o h]
```

and at the full functor level the `tapp1_func` naturality rules accumulate
through `hom_postcomp_func` and `hom_precomp_along_func`. This is the
semantically correct analogue of pushing a codomain/source arrow through a
transformation component.

- the higher-action stable heads
  `hom_postcomp_tele_fapp1_fapp0` and
  `hom_precomp_along_tele_fapp1_fapp0` expose the action on 2-cells. They do
  not currently fold identity 2-cells or vertical composites by runtime
  reduction. The promoted 2026-07-03 tele-level slice adds proof-time
  unification rules and reviewer-facing equality lemmas for those four
  comparisons, so typed `eq_refl` proofs can use the functoriality laws while
  runtime normalization remains unchanged.

This matters for the demo design. When a proof is meant to use generic
functoriality or naturality, formulate the term through the global
`fapp1_*`/`tapp1_*` owner or through an existing stable owner whose join is
known to compute. Do not assume that a raw `comp_fapp0` adjacent to a stable
hom-action projection will be re-associated into the hom-action normal form.

The existing interchange diagnostic near `emdash3_2_checks.lp`'s comment
`Interchange law instance for the Cat-valued representable hom_` is relevant
but should not be copied verbatim into the application theorem. It is a
full-owner regression for a Cat-valued representable postcomposition action.
More precisely, it checks a fundamental naturality/whiskering aspect of
interchange: one postcomposing 2-cell `e_fg : f => g` interacts correctly with
a vertical composite `beta · alpha` in the precomposed hom. It is not yet the
textbook four-2-cell interchange law:

```text
(theta * beta) · (eta * alpha)
  =
(theta · eta) * (beta · alpha)
```

where two compatible 2-cells vary in each of the two horizontal directions.
The four-cell interchange theorem should therefore become an explicit early
subtask before the final Eckmann-Hilton proof chain, after the hom-action
accumulation audit has classified the normalization paths that interchange
needs.

## Probe Evidence

Temporary probes were run under `tmp/probes/`. These are ignored scratch files
and are not promoted code.

### Reflexive Computations Already Present

The following proof-by-reflexivity probe succeeds:

```text
eh_identity_postcomp_eq :
  τ (hom_postcomp_func(id_B(x)) = id_func(Hom_B(x,x)))
≔ eq_refl ...

eh_identity_whisker_eq :
  τ (fapp1_fapp0(hom_postcomp_func(id_B(x)), alpha) = alpha)
≔ eq_refl ...
```

Probe:

```text
tmp/probes/eckmann_hilton_eq_refl_probe.lp
```

Result:

```text
EMDASH_TYPECHECK_TIMEOUT=20s scripts/probe.sh tmp/probes/eckmann_hilton_eq_refl_probe.lp
```

succeeds.

### Raw Horizontal Candidate Normal Forms

The raw horizontal candidate was written as:

```text
tapp1_fapp0
  (hom_postcomp_func(id_x))
  (hom_postcomp_func(id_x))
  (fapp1_fapp0(hom_postcomp_tele_func, beta))
  alpha
```

Separate `compute` queries showed the normal-form gap:

```text
raw horizontal candidate
  -> tapp1_fapp0
       (id_func (Hom_cat B x x))
       (id_func (Hom_cat B x x))
       (hom_postcomp_tele_fapp1_fapp0 B B id_B x x x id_x id_x beta)
       alpha

vertical composition
  -> comp_fapp0 (Hom_cat B x x) id_x id_x id_x beta alpha
```

Probe:

```text
tmp/probes/eckmann_hilton_compute_probe.lp
```

This means the raw comparison is not currently reflexive after normalization.

### Failed Reflexivity Candidate

The direct proof:

```text
raw_horizontal_candidate = beta · alpha
```

with body:

```text
eq_refl (beta · alpha)
```

fails. The remaining goal is exactly the difference between:

```text
comp_fapp0(... beta alpha)
```

and:

```text
tapp1_fapp0(... hom_postcomp_tele_fapp1_fapp0(... beta) alpha)
```

Probe:

```text
tmp/probes/eckmann_hilton_hcomp_eq_refl_fail_probe.lp
```

### Candidate Bridge Probe

A narrow temporary bridge was probed:

```text
tapp1_fapp0
  (id_func (Hom_cat B x x))
  (id_func (Hom_cat B x x))
  (hom_postcomp_tele_fapp1_fapp0 B B id_B x x x id_x id_x beta)
  alpha
  -> comp_fapp0 (Hom_cat B x x) id_x id_x id_x beta alpha
```

Probe:

```text
tmp/probes/eckmann_hilton_candidate_bridge_probe.lp
```

Quiet checking succeeds, and the reflexivity proof then succeeds. However,
warning-enabled comparison against the no-bridge probe changed the local
warning inventory:

```text
no bridge imported probe:   1366 warnings
bridge imported probe:      1378 warnings
delta:                       +12 unjoinable critical pairs
```

This bridge is therefore not ready for promotion. It is useful evidence for a
missing join at the identity-endomorphism horizontal-composition boundary, but
the rewrite-rule SOP requires more work before any runtime rule can be added.

### Hom-Action Functoriality And Accumulation Probe

Probe:

```text
tmp/probes/hom_action_functoriality_accumulation_probe.lp
```

Result:

```text
EMDASH_TYPECHECK_TIMEOUT=20s scripts/probe.sh tmp/probes/hom_action_functoriality_accumulation_probe.lp
```

succeeds.

The following `eq_refl` proof symbols succeed in the probe:

```text
hom_postcomp_func(q o p)
  =
comp_cat_fapp0(hom_postcomp_func(q), hom_postcomp_func(p))

hom_postcomp_fapp0(q o p,g)
  =
hom_postcomp_fapp0(q, hom_postcomp_fapp0(p,g))

((F f)_*(g)) o h
  =
(F f)_*(g o h)

hom_precomp_along_func(q o p)
  =
comp_cat_fapp0(hom_precomp_along_func(p), hom_precomp_along_func(q))

hom_precomp_along_fapp0(q o p,g)
  =
hom_precomp_along_fapp0(p, hom_precomp_along_fapp0(q,g))
```

The `compute` queries show that the following raw expanded presentations do
not currently reduce to the corresponding stable hom-action target:

```text
F[q] o hom_postcomp_fapp0(p,g)
k o hom_precomp_along_fapp0(p,g)
hom_precomp_along_fapp0(p,g) o F[q]
```

This is now considered intentional for the EH plan. These terms should remain
raw at runtime by default, while typed proof contexts may use the existing
`hom_postcomp_fapp0` / `hom_precomp_along_fapp0` unification rules, plus the
ordinary `comp_fapp0` associativity unification rule where necessary, to
elaborate `eq_refl` proofs against stable presentations.

The following higher-action normal-form gaps were genuine prerequisite
subgoals for interchange and Eckmann-Hilton:

```text
hom_postcomp_tele_fapp1_fapp0(f,f,id_f)
hom_precomp_along_tele_fapp1_fapp0(f,f,id_f)
hom_postcomp_tele_fapp1_fapp0(g,h,e_gh)
  o hom_postcomp_tele_fapp1_fapp0(f,g,e_fg)
hom_precomp_along_tele_fapp1_fapp0(g,h,e_gh)
  o hom_precomp_along_tele_fapp1_fapp0(f,g,e_fg)
```

They are now solved at proof time by promoted `unif_rule`s and checked
`eq_refl` equality lemmas. They remain non-runtime computations: direct
runtime stable-head bridges were probed and left deferred because the
owning-position runtime package changed the warning inventory before the
necessary confluence joins were designed.

The exact precomposition-source probe confirms that the stable composite
target:

```text
(F(p o q))^*(g)
```

currently normalizes further to the nested stable form:

```text
(F q)^*((F p)^*(g))
```

so if the optional raw-runtime bridge side-task is reopened later, a bridge
may choose the composite expression as readable RHS only if the existing
composite-arrow rule then continues to the accepted canonical normal form.

### Tele-Level Higher-Action Proof-Time Probe

The first direct typed proof probe confirmed that the stable heads themselves
do not compute by runtime conversion:

```text
tmp/probes/hom_action_tele_phase1_probe.lp
```

The remaining goal for postcomposition identity was:

```text
id(hom_postcomp_func(f))
  ≡
hom_postcomp_tele_fapp1_fapp0(f,f,id_f)
```

The generic-owner variant:

```text
fapp1_fapp0(hom_postcomp_tele_func, id_f)
```

also exposed the stable head before the generic identity fold could solve the
goal. This is the measured projection-ladder case described in the SOP.

Runtime bridge probes then showed that stable-head identity and composition
rules are feasible but not implementation-decision complete as runtime rules:

```text
tmp/probes/hom_action_tele_bridge_probe.lp
tmp/probes/emdash3_2_tele_bridge_full_probe.lp
```

The owning-position full-file runtime probe passed quietly, but warning
classification changed from:

```text
baseline full-file copy: 1199 unjoinable critical pairs, 167 replaceable-pattern reports
runtime bridge copy:     1237 unjoinable critical pairs, 167 replaceable-pattern reports
delta:                   +38 unjoinable critical pairs
```

The new families include normalized identity siblings such as `Path_cat`,
`Catd_cat`, `Functord_cat`, `Cat_cat`, and `Terminal_cat`, plus overlaps
between the broad stable-head composition bridge and category-specific
composition owners. A stricter append probe keyed on the explicit
`Functor_cat` ambient category still passed but worsened the warning stream,
so it is not the chosen runtime design.

The promoted solution is proof-time identification:

```text
tmp/probes/hom_action_tele_unif_probe.lp
```

The proof-time probe passed both quiet and warning-enabled checks. Its
warning-enabled inventory stayed at the baseline:

```text
proof-time unif append: 1199 unjoinable critical pairs, 167 replaceable-pattern reports
```

Promoted in `emdash3_2.lp`:

```text
hom_postcomp_tele_fapp1_fapp0_id_eq
hom_postcomp_tele_fapp1_fapp0_comp_eq
hom_precomp_along_tele_fapp1_fapp0_id_eq
hom_precomp_along_tele_fapp1_fapp0_comp_eq
```

These are reviewer-facing equality terms whose bodies are `eq_refl`, but they
depend on proof-time unification rather than runtime conversion. Runtime
tele-level bridges remain a deferred infrastructure side-task, not an
EH-local workaround.

### Raw Presentation Proof-Time Compatibility Probes

Two additional append-only probes tested candidate runtime bridges from raw
semantic presentations back into stable hom-action owners:

```text
tmp/probes/hom_action_raw_accumulation_bridge_probe.lp
tmp/probes/hom_action_raw_accumulation_bridge_strict_probe.lp
```

Both quiet probes succeed and prove the desired `eq_refl` assertions for:

```text
F[q] o ((F[p])_*(g))
((F[p])^*(g)) o F[q]
k o ((F[p])^*(g))
```

The warning-enabled append probes also terminate. They produce local
unjoinable-critical-pair families at the candidate postcomposition bridge, but
under the active SOP this is diagnostic evidence, not a veto on a semantically
intended runtime rule.

The current EH decision is stricter than those probes: do not promote any raw
`comp_fapp0`-headed bridge as part of the first EH implementation path. Raw
expanded compositions should have no additional runtime behavior by default.
Their intended compatibility with stable hom-action syntax is proof-time
unification, using the existing bridges:

```text
hom_postcomp_fapp0(...)       ~~  raw comp_fapp0(F[-], ...)
hom_precomp_along_fapp0(...)  ~~  raw comp_fapp0(..., F[-])
```

If a future concrete consumer needs judgmental reduction from a raw expanded
presentation back to a stable owner, reopen this as a separate infrastructure
side-task. The append probes then become warning evidence to classify: the
minimal bridge is underconstrained, while the stricter bridge still overlaps
with category-specific composition owners (`Op_cat`, `Path_cat`, `Catd_cat`,
`Cat_cat`, `Terminal_cat`) and existing postcomposition identity/composite
rules. Those warnings are not a semantic veto, but they show that any promoted
runtime bridge would need a narrower owner, a stable intermediate projection
head, or follow-up joins.

Do not promote the append-probe rules verbatim. Also do not treat these
bridges as the primary functoriality orientation of `(F -)_*` or `(F -)^*`;
that orientation is already the composite-stable-head-to-nested-stable-head
direction recorded above.

### Four-Cell Interchange Probes

Two additional probes tested the more textbook four-2-cell interchange shape.

The arbitrary-hom version uses:

```text
f,g,h : Hom_B(N,L)
e_fg : f => g
e_gh : g => h
X,Y,Z : Hom_B(M,N)
alpha : X => Y
beta  : Y => Z
```

with horizontal composition expressed through the current representable
postcomposition owner. The two sides are:

```text
lhs = hcomp(e_gh,beta) · hcomp(e_fg,alpha)
rhs = hcomp(e_gh · e_fg, beta · alpha)
```

Probe:

```text
tmp/probes/interchange_four_cell_probe.lp
```

Result:
the formulation is well-typed and `compute` shows the expected normal forms,
but the `eq_refl` proof fails. The left side normalizes to a vertical
`comp_fapp0` of two raw `tapp1_fapp0(... hom_postcomp_tele_fapp1_fapp0 ...)`
horizontal composites. The right side normalizes to one raw `tapp1_fapp0`
whose two arguments are the vertical composites.

The ordinary-natural-transformation version uses:

```text
F,G,H : X ⊢ Y
alpha : F => G
beta  : G => H
P,Q,R : Y ⊢ Z
eta   : P => Q
theta : Q => R
```

with horizontal composition expressed by the current
`comp_cat_cov_func_func_tapp1_fapp0` owner:

```text
lhs = hcomp(theta,beta) · hcomp(eta,alpha)
rhs = hcomp(theta · eta, beta · alpha)
```

Probe:

```text
tmp/probes/interchange_transf_four_cell_probe.lp
```

Result:
the whole-transfor equality is well-typed but not reflexive. The normal forms
show the left side as two nested vertical composites of
`comp_cat_cov_transf` and `comp_cat_con_transf`, while the right side is the
single horizontal composite of the two vertical composites.

A component-level version at `a : Obj(X)` was also probed:

```text
tmp/probes/interchange_transf_component_probe.lp
```

It is still not reflexive. The component goal exposes the expected textbook
proof obligations: associativity, functoriality of `R`, and naturality of
`theta` with respect to `alpha`. That explicit proof route has now succeeded:
`transf_interchange_component` is promoted as the first component-level
ordinary-transfor interchange theorem, without adding a rewrite or
unification rule.

## Architecture Decision

Do not start by adding a global Eckmann-Hilton rewrite rule.

Do not promote the temporary candidate bridge as-is.

Instead, implement the application in phases:

1. Promote the safe reviewer-facing computation slice first: transparent EH
   aliases and the already-validated `eq_refl` computation lemmas.
2. Then formulate the four-cell interchange theorem surface and determine
   whether a component-level ordinary-transfor version, or the arbitrary-hom
   representable version, can be proved as an explicit equality chain using
   existing associativity, functoriality, and naturality proof/computation
   infrastructure.
3. Add reviewer-facing notation and proof symbols whose bodies use the
   existing computation by `eq_refl`.
4. Define a named horizontal-composition facade for the identity-endomorphism
   setting, if needed, without immediately adding a runtime rewrite.
5. State the comparison between that facade and vertical composition as a
   mathematical lemma.
6. Attempt to prove that comparison using the existing equality combinators
   and existing interchange/naturality owners.
7. Only if the proof is blocked by a genuine missing computational join, probe
   the smallest owner-position bridge under the rewrite-rule SOP.

This preserves the project discipline: generic functoriality and naturality
belong to the global `fapp*`/`tapp*` calculus, while specialized bridges are
allowed only as measured projection-ladder joins.

## Reassessment

Review date: 2026-07-03.

The plan is globally coherent. The safe first implementation slice is now
implementation-decision complete: start with transparent EH aliases and
validated `eq_refl` computation lemmas. The full interchange/EH theorem path
still has narrower design questions. The architecture remains: stable
hom-action computation first, four-cell interchange second, then
Eckmann-Hilton specialization. The plan also correctly avoids a global EH
rewrite and treats raw `assert ... ≡ ...` diagnostics as DevOps evidence
rather than the reviewer-facing theorem.

Computable feasibility is mixed:

- High confidence:
  the basic `EH_2End`, `EH_vcomp`, identity postcomposition, identity
  whiskering, first-layer post/pre hom-action functoriality, and represented
  source accumulation can be promoted as `eq_refl` proof symbols.
- High confidence:
  raw expanded semantic presentations can be related to stable hom-action
  presentations at proof time by the existing `hom_postcomp_fapp0` and
  `hom_precomp_along_fapp0` unification rules. They should not receive new
  runtime behavior for the first EH implementation slice.
- Demonstrated:
  component-level ordinary-transfor interchange is now proved as
  `transf_interchange_component`, using `comp_assoc`, strict functoriality,
  and strict naturality. This result is component-level, not whole-transfor
  extensionality.
- Low confidence as a whole-theorem target:
  whole-transfor interchange currently lacks a known transfor extensionality
  principle. The first reviewer-facing interchange result should therefore be
  component-level or arbitrary-hom-level, not whole-transfor equality.
- Main blocker:
  `EH_hcomp_to_vcomp` still depends on identifying a raw
  `tapp1_fapp0(... hom_postcomp_tele_fapp1_fapp0 ...)` normal form with
  vertical composition. The temporary bridge for that comparison works in a
  focused probe but changes the warning inventory. That delta does not veto
  the bridge if it is the intended computation, but it does require
  classification of overlap families and a search for missing joins or a
  better owner before promotion.

Decision status before implementation:

The safe first slice is implementation-decision complete: promote only the
validated `eq_refl` computation lemmas and transparent aliases that have
already been probed. The first milestone scope is therefore settled:
implement the safe lemmas first. The broader infrastructure direction is also
settled at a high level: the current stable-head hom-action projection normal
forms and ordinary transfor naturality are general infrastructure and should
precede the final EH argument where they are needed.

Settled decisions after the 2026-07-03 review:

1. The first promoted slice is conservative: transparent EH aliases and safe
   `eq_refl` lemmas only.
2. Generic single-functor functoriality remains oriented in the usual fold
   direction `F[q] o F[p] -> F(q o p)`. Separately, the current stable
   hom-action projection joins for `(F -)_*` and `(F -)^*` are oriented from
   composite stable heads to nested stable heads, at both the functor level
   and the capped `fapp0`-projected level. This is an explicit provisional
   design choice, not a global reversal of ordinary functoriality.
3. Raw terms such as `F[q] o ((F[p])_*(g))` are not the primary functoriality
   orientation and should not reduce back into the stable owner by default.
   Their intended compatibility layer is proof-time unification with the
   existing `hom_*_fapp0` stable heads, validated by typed `eq_refl` probes
   when a concrete theorem uses them.
4. The semantically correct transformation analogue is ordinary naturality
   accumulation, and it is already represented by the full `tapp1_func`
   naturality rules and the capped `tapp1_fapp0` rules.
5. Whole-transfor interchange is not the first target; without extensionality,
   the first interchange deliverable should be component-level or
   arbitrary-hom-level.
6. Tele-level higher-action identity/composition is proof-time infrastructure
   for the current EH plan. Four `unif_rule`s identify the stable
   `hom_postcomp_tele_fapp1_fapp0` /
   `hom_precomp_along_tele_fapp1_fapp0` identity and composition
   presentations with their functoriality targets, and four checked equality
   symbols expose those comparisons by `eq_refl`. Runtime tele bridges remain
   deferred because the broad owning-position bridge added 38 unjoinable
   critical-pair reports and the stricter ambient-category variant was worse.
7. The first promoted four-cell interchange target is component-level
   ordinary-transfor interchange. The theorem
   `transf_interchange_component` is an explicit equality proof over
   components, not a whole-transfor extensionality theorem and not a runtime
   rewrite. It factors through `transf_naturality_component` and the
   arrow-level `arrow_square_pasting_*` proof chain.

The remaining decisions are narrower:

1. Interchange extension surface.

   Decide whether the next promoted interchange result should be the
   arbitrary-hom representable theorem, an EH-specialized component theorem,
   or a small bridge from the ordinary-transfor component theorem to the
   representable postcomposition surface. Whole-transfor equality should stay
   deferred unless a checked transfor extensionality principle is added.

2. Horizontal-composition facade.

   Decide whether `EH_hcomp_raw` remains a transparent alias over the current
   owner stack, or whether a named stable facade is needed. A facade must not
   hide semantic duplication; it should route through the chosen hom-action
   owner.

3. Horizontal-to-vertical proof route.

   Decide the intended status of `EH_hcomp_to_vcomp`: explicit equality proof,
   proof-time `unif_rule`, or runtime bridge. The current narrow runtime
   bridge is useful evidence but not approved; its warning delta must be
   classified as missing joins/placement evidence before promotion.

4. Alias elaboration surface.

   Probe the proposed `EH_*` aliases in their final alias form before
   promotion, because unfolded `Hom` types may elaborate more robustly than
   `Obj (EH_2End x)`.

Deferred optional infrastructure:
raw bridges from expanded `comp_fapp0` presentations back to stable hom-action
owners are not required before the EH demo. If later reopened, the bridge
owner/orientation and warning follow-up policy must be settled in a separate
side-task before promotion.

Pause/re-design trigger:
if the concrete EH or four-cell-interchange implementation repeatedly gets
stuck exactly because the stable hom-action projection normal form expands
composite base arrows while the proof needs the usual folded presentation,
pause before adding ad hoc bridges. Reassess whether the hom-action projection
orientation should stay as-is with theorem-style `eq_sym` lemmas, receive a
narrow proof-time `unif_rule`, or be redesigned at the owning projection
layer. Do not silently work around this choice with EH-local runtime rules.

## Proposed Symbols

Names are provisional but should stay close to the active kernel vocabulary.

### Object Classifier

```text
symbol EH_2End
  [B : Cat]
  (x : τ (Obj B))
  : Cat
≔ Hom_cat (Hom_cat B x x) (@id B x) (@id B x);
```

This is a category, not merely a groupoid/type, so it remains compatible with
higher iteration.

### Vertical Composition

Readable alias:

```text
symbol EH_vcomp
  [B : Cat]
  (x : τ (Obj B))
  (beta alpha : τ (Obj (EH_2End x)))
  : τ (Obj (EH_2End x))
≔ @comp_fapp0
    (Hom_cat B x x)
    (@id B x) (@id B x) (@id B x)
    beta alpha;
```

This should remain transparent and should not own new rewrite rules.

### Horizontal Composition Facade

A first facade can be transparent over the raw current owner:

```text
symbol EH_hcomp_raw
  [B : Cat]
  (x : τ (Obj B))
  (beta alpha : τ (Obj (EH_2End x)))
  : τ (Obj (EH_2End x))
≔ @tapp1_fapp0
    (Hom_cat B x x)
    (Hom_cat B x x)
    (@hom_postcomp_func B B (@id_func B) x x x (@id B x))
    (@hom_postcomp_func B B (@id_func B) x x x (@id B x))
    (@id B x)
    (@id B x)
    (@fapp1_fapp0
      (Hom_cat B x x)
      (Functor_cat (Hom_cat B x x) (Hom_cat B x x))
      (@hom_postcomp_tele_func B B (@id_func B) x x x)
      (@id B x)
      (@id B x)
      beta)
    alpha;
```

If this raw facade is too noisy for theorem statements, add a shorter
transparent alias:

```text
symbol EH_hcomp ... ≔ EH_hcomp_raw ...
```

Do not add a rewrite rule on `EH_hcomp` until a concrete proof obligation
requires it and an owning-position probe classifies the consequence.

### Computation Lemmas

The following are safe first proof symbols because they already compute:

```text
symbol EH_identity_postcomp
  [B : Cat] (x : τ (Obj B))
  : τ (
      @hom_postcomp_func B B (@id_func B) x x x (@id B x)
      =
      @id_func (Hom_cat B x x))
≔ eq_refl (@id_func (Hom_cat B x x));

symbol EH_identity_whisker
  [B : Cat] (x : τ (Obj B))
  (alpha : τ (Obj (EH_2End x)))
  : τ (
      @fapp1_fapp0
        (Hom_cat B x x)
        (Hom_cat B x x)
        (@hom_postcomp_func B B (@id_func B) x x x (@id B x))
        (@id B x)
        (@id B x)
        alpha
      =
      alpha)
≔ eq_refl alpha;
```

Endpoint elaboration may require using the unfolded `Hom` type in the first
implementation slice, then introducing the `EH_2End` alias after a focused
probe confirms that it does not make inference brittle.

### Horizontal-To-Vertical Lemma

Target statement:

```text
symbol EH_hcomp_to_vcomp
  [B : Cat] (x : τ (Obj B))
  (beta alpha : τ (Obj (EH_2End x)))
  : τ (EH_hcomp beta alpha = EH_vcomp beta alpha);
```

This is not currently an `eq_refl` lemma for the raw facade. Implementation
must first try an explicit proof using `eq_trans`, `eq_sym`, and `eq_ap`.

If the proof remains blocked at the normal-form gap identified above, use the
rewrite-rule SOP to decide whether to add a runtime bridge, a proof-time
`unif_rule`, or no kernel rule.

### Interchange Lemma

Target statement should specialize the existing representable interchange
diagnostic to the EH setting. The theorem should be a mathematical proof
symbol, not only:

```text
assert ... ≡ ...
```

Provisional shape:

```text
symbol EH_interchange
  [B : Cat] (x : τ (Obj B))
  (alpha beta gamma delta : τ (Obj (EH_2End x)))
  (...)
  : τ (
      EH_vcomp (EH_hcomp beta alpha) (EH_hcomp delta gamma)
      =
      EH_hcomp (EH_vcomp beta delta) (EH_vcomp alpha gamma));
```

The exact argument order must be fixed by a focused probe against the active
`comp_fapp0` orientation. The first implementation should use only the
two-variable version required for EH, not a premature fully general
interchange theorem.

Before the EH-specialized theorem, add a first interchange subtask with two
candidate surfaces.

Candidate A: ordinary natural transformations in `Cat_cat`.

```text
symbol transf_interchange
  [X Y Z : Cat]
  [P Q R : τ (Functor Y Z)]
  (eta : τ (Transf P Q))
  (theta : τ (Transf Q R))
  [F G H : τ (Functor X Y)]
  (alpha : τ (Transf F G))
  (beta : τ (Transf G H))
  : τ (
      comp(
        hcomp(theta,beta),
        hcomp(eta,alpha))
      =
      hcomp(
        comp(theta,eta),
        comp(beta,alpha)));
```

Here `hcomp` should be the existing
`comp_cat_cov_func_func_tapp1_fapp0` owner or a transparent readability alias
over it.

Candidate B: arbitrary-hom/representable postcomposition.

```text
symbol hom_postcomp_interchange
  [B : Cat] [M N L : τ (Obj B)]
  [f g h : τ (Hom B N L)]
  (e_fg : τ (Hom (Hom_cat B N L) f g))
  (e_gh : τ (Hom (Hom_cat B N L) g h))
  [X Y Z : τ (Hom B M N)]
  (alpha : τ (Hom (Hom_cat B M N) X Y))
  (beta : τ (Hom (Hom_cat B M N) Y Z))
  : τ (
      hcomp(e_gh,beta) · hcomp(e_fg,alpha)
      =
      hcomp(e_gh · e_fg, beta · alpha));
```

Candidate A is probably the cleaner first proof target because its horizontal
composition owner is already explicit. Candidate B is closer to the
Eckmann-Hilton application over arbitrary hom-categories and should follow
only after the ordinary-transfor proof route or missing infrastructure is
understood.

### Eckmann-Hilton Commutativity

Target theorem:

```text
symbol EH_comm
  [B : Cat] (x : τ (Obj B))
  (alpha beta : τ (Obj (EH_2End x)))
  : τ (
      EH_vcomp beta alpha
      =
      EH_vcomp alpha beta);
```

The proof should be an explicit equality chain. The expected ingredients are:

- left and right unit laws for `EH_vcomp`, probably by `eq_refl`;
- left and right unit laws for `EH_hcomp`, either by `eq_refl` after a
  selected bridge or by explicit proof;
- `EH_interchange`;
- `EH_hcomp_to_vcomp` in the required orientations.

## Rewrite-Rule SOP For This Plan

Any proposed rewrite or unification rule must follow the active SOP in
`REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md` and `README.md`.

In particular:

1. Normalize both sides of the target equation separately with `compute`
   before adding rules.
2. Distinguish runtime normalization from proof-time identification.
3. Prefer a mathematical proof term if runtime computation is not semantically
   required.
4. Probe rules in `tmp/probes/` before editing `emdash3_2.lp`.
5. Keep inferred source/target slots implicit unless they are true
   discriminators.
6. Treat an LHS of the form
   `tapp1_fapp0(... hom_postcomp_tele_fapp1_fapp0 ... )` as a high-risk
   outer-eliminator / inner-action commuting conversion until proven
   otherwise.
7. Test both reduction paths:
   owner-first through `hom_postcomp_tele_fapp1_fapp0`, and projection-first
   through `tapp1_fapp0`.
8. Run a warning-enabled comparison and classify any delta.
9. Do not promote a bridge whose only evidence is that one focused
   `eq_refl` proof starts checking.

The temporary bridge probe added 12 unjoinable critical-pair warnings in an
imported-file comparison. That does not automatically veto a semantically
necessary rule, but it does mean the rule is not implementation-decision
complete.

## Implementation Phases

### Phase 0: Plan Validation

- Keep this report current as the implementation-decision source.
- Do not edit `emdash3_2.lp` until the theorem surface below is accepted.
- Re-run:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

### Phase 1: Hom-Action Functoriality And Accumulation Audit

This phase is now the first implementation subtask.

Work items:

1. Promote no new runtime rule initially.
2. Keep `tmp/probes/hom_action_functoriality_accumulation_probe.lp` as the
   focused scratch probe while iterating.
3. Decide which computations are reviewer-facing `eq_refl` lemmas:
   first-layer post/pre composite-arrow functoriality, postcomposition
   represented-source accumulation, and identity/unit cases are good
   candidates.
   Record both readings where useful:

   ```text
   runtime stable projection:
     (F(q o p))_*(g) -> (F q)_*((F p)_*(g))

   theorem-style usual fold:
     (F q)_*((F p)_*(g)) = (F(q o p))_*(g)
   ```

   The second form should initially be a proof lemma, probably by `eq_sym` of
   the first reflexive computation, not a new rewrite rule.
4. For raw expanded post/pre composition forms, first try to restate demo
   terms through existing stable hom-action owners. If a raw adjacent
   `comp_fapp0` is unavoidable, treat it as a proof-time compatibility case
   using the existing `hom_*_fapp0` unification rules. Validate the concrete
   theorem shape with a typed `eq_refl` probe instead of adding a runtime rule.
   The raw shapes include:

   ```text
   F[q] o ((F[p])_*(g))       ~~ stable hom_postcomp owner
   ((F[p])^*(g)) o F[q]       ~~ stable hom_precomp owner
   k o ((F[p])^*(g))          ~~ stable hom_precomp owner
   ```

   These are raw-presentation proof-time comparisons, not the primary
   functoriality orientation of `(F -)_*` or `(F -)^*`.
5. Treat the append-only raw-presentation bridge probes as archived feasibility
   evidence only. The current EH plan does not promote them. If a later
   concrete consumer needs runtime behavior, split the bridge package by rule,
   install each candidate at its owning position in a temporary full-file copy,
   and warning-classify the overlap families. Treat warning families as
   diagnostics for missing joins or placement/redesign work, not as an
   automatic veto.
6. For tele-level higher-action identity/composition, determine whether the
   desired computation belongs to the stable projection heads
   `hom_postcomp_tele_fapp1_fapp0` /
   `hom_precomp_along_tele_fapp1_fapp0`, or whether the application should
   route through the generic `fapp1_fapp0` functoriality owner before the
   stable projection is exposed.
7. Re-run `compute` on both sides of each candidate lemma before deciding
   between explicit proof terms, proof-time unification, or runtime rewrite.

### Phase 2: Four-Cell Interchange Foundation

Work items:

1. Add no promoted code initially.
2. Keep the ordinary-transfor and arbitrary-hom four-cell probes in
   `tmp/probes/` while iterating.
3. Normalize both sides and the component-level versions with `compute`.
4. Try a mathematical proof of the ordinary-transfor component statement using
   the existing proof/computation tools:
   `eq_trans`, `eq_sym`, `eq_ap`, `comp_assoc`, functoriality by reflexivity,
   and naturality by reflexivity through `tapp1_fapp0`.
5. If component-level proof succeeds, decide whether a whole-transfor theorem
   is possible with current infrastructure. Without a transfor extensionality
   principle, whole-transfor equality may need to remain a named computation
   rule, a proof-time comparison, or a deferred theorem.
6. Only after the ordinary-transfor route is understood, specialize or port the
   theorem to the arbitrary-hom representable postcomposition surface needed
   by Eckmann-Hilton.

Current implementation status:
the ordinary-transfor component route has succeeded and is promoted as
`transf_interchange_component`. The proof is not reflexivity: it uses
component naturality, functoriality of the codomain functor by reflexivity,
and an explicit `arrow_square_pasting_right_to_left` associativity chain. No
whole-transfor interchange theorem has been promoted, and the arbitrary-hom
representable theorem remains the next interchange-design question.

Do not add a four-cell interchange rewrite rule merely because the direct
`eq_refl` candidates fail. The component probe shows ordinary mathematical
proof obligations, not yet a proof that runtime normalization should choose
one side as canonical.

### Phase 3: Reviewer-Facing Computation Lemmas

Add a new subsection under applications in `emdash3_2.lp`, after the current
path-induction/transitivity examples unless a later reorganization plan chooses
a separate examples module.

Promote only the `eq_refl` lemmas already validated:

- `EH_2End`
- `EH_vcomp`
- `EH_identity_postcomp`
- `EH_identity_whisker`

Add corresponding concise comments explaining the EH reading.

Add diagnostic assertions to `emdash3_2_checks.lp` only for regression
coverage of the promoted computations, and regenerate the catalog if new
checks are added.

### Phase 4: Horizontal Composition Facade

Add `EH_hcomp_raw` as a transparent alias over the current hom-action owners.

Run compute probes for:

- `EH_hcomp_raw beta alpha`
- `EH_vcomp beta alpha`
- left and right horizontal unit candidates
- the existing representable interchange specialized to `x`

Do not add a runtime rule yet.

### Phase 5: Proof-Term Attempt

Try to prove:

```text
EH_hcomp_to_vcomp
```

using:

- `eq_trans`
- `eq_sym`
- `eq_ap`
- existing `EH_identity_*` lemmas
- existing naturality/interchange computation from the full-naturality layer

If this succeeds without new rules, proceed to `EH_comm`.

If it fails at the known normal-form gap, record the exact stuck goal in this
report before considering kernel infrastructure.

### Phase 6: Infrastructure Decision Point

Only after Phase 5 fails, choose one:

1. Keep `EH_hcomp_to_vcomp` as explicit non-reflexive evidence with a more
   detailed proof term.
2. Add a proof-time `unif_rule` if the comparison is intended only for proof
   elaboration and not runtime normalization.
3. Add a runtime bridge if the comparison is the intended computational normal
   form.
4. Add a more general stable owner if the raw bridge is too ad hoc.

Candidate runtime bridge from the probe:

```text
tapp1_fapp0
  (id_func (Hom_cat B x x))
  (id_func (Hom_cat B x x))
  (hom_postcomp_tele_fapp1_fapp0 B B id_B x x x id_x id_x beta)
  alpha
  -> comp_fapp0 (Hom_cat B x x) id_x id_x id_x beta alpha
```

This exact bridge is not currently approved. Before promotion:

- install it in a temporary full-file copy at the intended owning position;
- run quiet and warning-enabled full checks;
- compare warning counts and first-warning families;
- inspect decision-tree impact if needed;
- test both owner-first and projection-first reduction paths;
- document any remaining overlap family in this report.

### Phase 7: Eckmann-Hilton Theorem

Implement `EH_comm` as a proof-term chain. It should be readable enough that a
reviewer can see the Eckmann-Hilton argument:

```text
vertical
  = horizontal
  = interchange with units
  = horizontal in the opposite order
  = vertical in the opposite order
```

Prefer small named lemmas over one giant `eq_trans` term.

## Side-Task Ledger

### EH-HOM-ACTION-FUNCTORIALITY-AUDIT

Trigger:
the Eckmann-Hilton and four-cell interchange demos require functoriality of
the represented hom-actions at both the capped object-action layer and the
tele-level 2-cell-action layer.

Required audit:
classify which stable-head functoriality/identity/accumulation laws already
compute by `eq_refl`, which can be proved explicitly, and which require a
runtime or proof-time bridge. The current evidence shows first-layer
post/pre functoriality computes, while tele-level identity/composition is now
handled by proof-time unification plus checked `eq_refl` equality lemmas.

Status:
partially complete; first-layer post/pre identity, composite-arrow, capped
object-action, source-accumulation, and theorem-style fold equality lemmas
have been promoted. Tele-level 2-cell-action identity/composition proof-time
lemmas have also been promoted. Runtime tele-level stable-head bridges remain
deferred because the owning-position runtime bridge probe introduced a `+38`
unjoinable-critical-pair delta.

### EH-RAW-PRESENTATION-BRIDGES

Trigger:
raw adjacent terms such as `F[q] o ((F[p])_*(g))` and
`((F[p])^*(g)) o F[q]` stay as raw `comp_fapp0` terms. The
codomain-side precomposition form `k o ((F[p])^*(g))` is also raw.

Required audit:
for the EH plan, these raw shapes should have no new runtime behavior by
default. Concrete theorem contexts should use the existing proof-time
unification bridges from `hom_postcomp_fapp0` and
`hom_precomp_along_fapp0` to raw `comp_fapp0`, validated by typed `eq_refl`
probes. A runtime raw bridge is a deferred optional infrastructure task, not a
prerequisite for the safe EH slice.

Status:
deferred; no bridge is approved or planned for the first EH implementation
slice. Quiet append probes prove local assertions, but warning-enabled append
probes expose local overlap families at the candidate postcomposition bridge.
Those warnings are diagnostic evidence, not a semantic veto, if this side-task
is reopened later.

### EH-TELE-HIGHER-ACTION-FUNCTORIALITY

Trigger:
`hom_postcomp_tele_fapp1_fapp0` and
`hom_precomp_along_tele_fapp1_fapp0` expose higher action on 2-cells but do
not currently runtime-compute identity or composition of those 2-cells at the
stable head.

Required audit:
determine whether these are missing projection-ladder joins or whether the
interchange proof should remain explicit at this layer. Any proposed rule must
be probed at the owning position and warning-classified because it overlaps
with generic functoriality.

Status:
proof-time complete for the current EH plan; four `unif_rule`s and four
reviewer-facing equality lemmas are promoted. Runtime conversion is deferred:
the broad owning-position runtime bridge passed quietly but added 38
unjoinable critical-pair reports, and the stricter ambient-`Functor_cat`
append variant was worse.

### EH-HCOMP-JOIN

Trigger:
`EH_hcomp_to_vcomp` cannot be proved without identifying the raw horizontal
normal form with vertical composition.

Required audit:
classify whether the join belongs to `tapp1_fapp0`, to the postcomposition
telescope higher-action owner, to a new EH-local facade, or only to proof-time
equality.

Status:
open; temporary imported bridge succeeds but adds 12 warning reports.

### EH-INTERCHANGE-THEOREM

Trigger:
the existing Cat-valued representable interchange diagnostic is insufficient
for the textbook four-2-cell argument needed by `EH_comm`.

Required audit:
first formulate the four-cell ordinary-transfor and arbitrary-hom theorem
surfaces; test component-level proof terms before any runtime rule; specialize
to identity-endomorphism cells only after the general proof route is clear.

Status:
partially complete; `transf_interchange_component` is promoted as the first
four-cell theorem at the ordinary-transfor component level. The arbitrary-hom
representable theorem and any EH-specialized interchange theorem remain open.

### EH-FOUR-CELL-INTERCHANGE

Trigger:
the current `emdash3_2_checks.lp` interchange diagnostic covers a
one-postcomposing-cell naturality slice, not the full four-cell textbook law.

Required audit:
prove or classify the ordinary-transfor four-cell theorem and then the
arbitrary-hom representable theorem. If proof attempts fail, identify whether
the missing infrastructure is associativity/naturality proof lemmas,
transfor extensionality, a proof-time comparison, or a runtime bridge.

Status:
partially complete. Direct `eq_refl` candidates fail for whole-transfor,
arbitrary-hom, and ordinary-transfor component formulations, but the
ordinary-transfor component theorem is now proved explicitly as
`transf_interchange_component`. Whole-transfor equality remains deferred
without extensionality; arbitrary-hom representable interchange remains open.

### EH-SURFACE-SYNTAX

Trigger:
the raw kernel terms become unreadable in `emdash3_2.lp`.

Required audit:
add transparent aliases only; no semantic duplication and no helper alias with
a copied body that bypasses the named owner.

Status:
open.

## Implementation Log

### 2026-07-03: First Safe Computation Slice

Promoted in `emdash3_2.lp` under the Applications section:

- `EH_2End`
- `EH_vcomp`
- `EH_identity_postcomp`
- `EH_identity_whisker`
- `EH_vcomp_alias`

The promoted binder types use the explicit alias form `@EH_2End B x`. This
matches the successful probe and avoids relying on implicit reconstruction of
the ambient category before a later readability cleanup is separately checked.

The exact alias form was first checked in:

```text
tmp/probes/eckmann_hilton_first_slice_probe.lp
```

Validation:

```bash
EMDASH_TYPECHECK_TIMEOUT=20s scripts/probe.sh tmp/probes/eckmann_hilton_first_slice_probe.lp
EMDASH_TYPECHECK_TIMEOUT=60s lambdapi check -w emdash3_2.lp
```

No runtime rewrite rule, proof-time unification rule, horizontal-composition
facade, or interchange theorem was promoted in this slice. The promoted proof
symbols are ordinary equality terms whose bodies are `eq_refl`; this is the
reviewer-facing computation layer, not a diagnostic `assert ... ≡ ...`
section.

### 2026-07-03: First-Layer Hom-Action Proof Lemmas

Promoted near the semantic hom-action owners in `emdash3_2.lp`:

- `hom_postcomp_func_id_eq`
- `hom_postcomp_fapp0_id_eq`
- `hom_postcomp_func_comp_eq`
- `hom_postcomp_func_comp_fold_eq`
- `hom_postcomp_fapp0_comp_eq`
- `hom_postcomp_fapp0_comp_fold_eq`
- `hom_postcomp_fapp0_source_accumulation_eq`
- `hom_precomp_along_func_id_eq`
- `hom_precomp_along_fapp0_id_eq`
- `hom_precomp_along_func_comp_eq`
- `hom_precomp_along_func_comp_fold_eq`
- `hom_precomp_along_fapp0_comp_eq`
- `hom_precomp_along_fapp0_comp_fold_eq`

The runtime-direction lemmas are `eq_refl` proofs of the current stable-head
normal forms. The `*_fold_eq` lemmas record the usual folded mathematical
direction by `eq_sym`; no rewrite orientation was changed.

The exact proof-symbol package was first checked in:

```text
tmp/probes/hom_action_phase1_promote_probe.lp
```

Validation:

```bash
EMDASH_TYPECHECK_TIMEOUT=20s scripts/probe.sh tmp/probes/hom_action_phase1_promote_probe.lp
EMDASH_TYPECHECK_TIMEOUT=60s lambdapi check -w emdash3_2.lp
```

### 2026-07-03: Tele-Level Hom-Action Proof-Time Lemmas

Promoted near the tele-level hom-action owners in `emdash3_2.lp`:

- `hom_postcomp_tele_fapp1_fapp0_id_eq`
- `hom_postcomp_tele_fapp1_fapp0_comp_eq`
- `hom_precomp_along_tele_fapp1_fapp0_id_eq`
- `hom_precomp_along_tele_fapp1_fapp0_comp_eq`

The four equality symbols are `eq_refl` terms enabled by four narrow
proof-time unification rules. No runtime rewrite rule was promoted for these
tele-level laws.

Probe history:

```text
tmp/probes/hom_action_tele_phase1_probe.lp
tmp/probes/hom_action_tele_generic_phase1_probe.lp
tmp/probes/hom_action_tele_bridge_probe.lp
tmp/probes/hom_action_tele_unif_probe.lp
tmp/probes/emdash3_2_tele_bridge_full_probe.lp
```

The direct stable-head and generic-owner proof probes failed at the expected
normal-form gap. The runtime bridge probes passed but the owning-position
full-file bridge changed the warning inventory by `+38` unjoinable
critical-pair reports. The proof-time unification probe passed with the
baseline warning inventory (`1199` unjoinable critical pairs and `167`
replaceable-pattern reports), so proof-time identification was selected for
the current EH plan.

Validation:

```bash
EMDASH_TYPECHECK_TIMEOUT=20s scripts/probe.sh tmp/probes/hom_action_tele_unif_probe.lp
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_TYPECHECK_TIMEOUT=20s scripts/probe.sh tmp/probes/hom_action_tele_unif_probe.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

### 2026-07-03: Component-Level Ordinary-Transfor Interchange

Promoted near the ordinary transfor/naturality owner in `emdash3_2.lp`:

- `transf_diag_to_offdiag_id`
- `transf_naturality_left`
- `transf_naturality_right`
- `transf_naturality_component`
- `arrow_square_pasting_step1` through `arrow_square_pasting_step6`
- `arrow_square_pasting_right_to_left`
- `transf_hcomp`
- `transf_interchange_component`

This is the first promoted four-cell interchange theorem. It is intentionally
component-level:

```text
tapp0((theta * beta) · (eta * alpha), a)
  =
tapp0((theta · eta) * (beta · alpha), a)
```

The proof is not `eq_refl`. It factors through an explicit arrow-level
associativity chain, the component naturality of `theta` along `alpha[a]`,
and ordinary functoriality of `R` by reflexivity. No whole-transfor
extensionality principle, runtime rewrite rule, or new unification rule was
introduced.

The exact proof route was first checked in:

```text
tmp/probes/transf_naturality_component_probe.lp
tmp/probes/interchange_component_steps_probe.lp
```

Validation:

```bash
EMDASH_TYPECHECK_TIMEOUT=20s scripts/probe.sh tmp/probes/transf_naturality_component_probe.lp
EMDASH_TYPECHECK_TIMEOUT=20s scripts/probe.sh tmp/probes/interchange_component_steps_probe.lp
EMDASH_TYPECHECK_TIMEOUT=60s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
EMDASH_TYPECHECK_TIMEOUT=60s make examples
make warning-summary
```

## Resume / Compaction Note

After context compaction, interruption, or handoff, do not continue this plan
from memory alone. Reload `AGENTS.md`, `README.md`, `emdash3_2.lp`,
`emdash3_2_checks.lp`, this report, the current SOP report,
`reports/EMDASH_FOUNDATIONS.md`, and the canonical surface syntax report;
then re-check `git status --short`, `git diff --cached`, `git diff`, relocate
the active symbols with `rg`, and run a bounded baseline check before new
edits.

## Validation Checklist

Before handing off any promoted implementation:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
make catalog        # if emdash3_2_checks.lp gains new checks
make examples       # if an examples/*.lp milestone is added
make warning-summary
```

For any promoted rewrite or unification rule:

```bash
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_TYPECHECK_TIMEOUT=20s make check
python3 scripts/audit_rule_lhs.py --show-kept
```

If a rule changes the warning inventory, update this report with:

- the exact rule;
- the intended semantic owner;
- quiet check result;
- warning-enabled delta;
- first new warning family if identifiable;
- why runtime rewrite, proof-time unification, or explicit proof evidence was
  selected.
