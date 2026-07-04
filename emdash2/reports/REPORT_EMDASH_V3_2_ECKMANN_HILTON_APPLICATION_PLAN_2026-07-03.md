# EMDASH v3.2 Eckmann-Hilton Application Plan

Date: 2026-07-03
Last reviewed: 2026-07-04
Plan-ID: EMDASH-V3-2-ECKMANN-HILTON-APPLICATION-2026-07-03
Depends-On: EMDASH-V3-2-FULL-NATURALITY-2026-06-12; EMDASH-V3.2-DEFISO-HOM-ACTION-PROFCOMP-MIGRATION-2026-06-28; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Supersedes: none
Side-Task-Ledger: this-report#side-task-ledger
Infinity-Codex-Origin: current-session-analysis-2026-07-03
Infinity-Codex-Decision-Responses: none-yet
Status: fold-oriented hom-action/interchange infrastructure promoted to the active kernel on 2026-07-04; safe EH slice and first-layer hom-action proof lemmas retained; raw adjacent hom-action folds promoted; pre-configured representable interchange now has a reviewer-facing equality theorem; prior proof-time tele workaround and component-level ordinary-transfor interchange were superseded by the promotion

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
were migrated on 2026-07-04 to the fold direction needed by the
pre-configured representable-interchange computation:

- the generic single-functor law in the core calculus is still the usual
  cut-elimination fold:

```text
F[q] o F[p]  ->  F(q o p)
```

This is implemented by the generic `fapp1_fapp0` rule on raw composites.

- postcomposition has stable functor-level and capped object-level folds
  corresponding to:

```text
(F q)_* o (F p)_*     -> (F(q o p))_*
(F q)_*((F p)_*(g))   -> (F(q o p))_*(g)
```

- precomposition has the contravariant stable functor-level and capped
  object-level folds:

```text
(F p)^* o (F q)^*     -> (F(q o p))^*
(F p)^*((F q)^*(g))   -> (F(q o p))^*(g)
```

- postcomposition has the represented-source accumulation:

```text
((F f)_*(g)) o h    -> (F f)_*(g o h)
```

These are now the current runtime normal forms, not merely reviewer-facing
proof lemmas. The corresponding `*_comp_eq` proof symbols remain valid by
conversion, but their bodies now reduce through the fold-oriented runtime
rules.

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

The audit also found important raw semantic-presentation shapes. The
pre-revision plan treated all of them as proof-time-only compatibility cases.
That was too coarse. Some of these shapes are genuine Došen-style
accumulation candidates and must be classified one by one:

- the raw adjacent postcomposition presentation

```text
F[q] o ((F[p])_*(g))
```

currently stays as a raw `comp_fapp0` in the active file; it does not reduce
directly back into the stable hom-action owner. A focused append probe shows
that the runtime bridge

```text
F[q] o ((F[p])_*(g))  ->  (F(q o p))_*(g)
```

is feasible locally, and the existing composite-arrow rule then continues to
the current fold normal form

```text
(F(q o p))_*(g)
```

This bridge is now active runtime infrastructure. It was promoted with the
matching source-side precomposition bridge after append and owning-position
full-copy probes checked quietly and warning-enabled.

- postcomposition already has the represented-source accumulation:

```text
((F[p])_*(g)) o k  ->  (F[p])_*(g o k)
```

This is active runtime infrastructure.

- the analogous codomain-side precomposition term

```text
k o ((F[p])^*(g))
```

is now active runtime accumulation:

```text
k o ((F[p])^*(g))  ->  (F[p])^*(k o g)
```

- the source-side precomposition counterpart

```text
((F[p])^*(g)) o F[q]
```

is now active runtime accumulation:

```text
((F[p])^*(g)) o F[q]  ->  (F[p o q])^*(g)
```

with the order fixed against the active `comp_fapp0` convention.

- the corresponding naturality/ordinary-transfor accumulation is represented
  in the active file. At the capped component level:

```text
G[h] o epsilon[f]  ->  epsilon[h o f]
epsilon[f] o F[h]  ->  epsilon[f o h]
```

and at the full functor level the `tapp1_func` naturality rules accumulate
through `hom_postcomp_func` and `hom_precomp_along_func`. These rules are
still considered active infrastructure. However, the review raised a separate
orientation question for vertical composites of transformations:

```text
(theta · eta)[f]  ?  theta[f] · eta[f]
```

The point-component rule currently expands vertical composites:

```text
(theta · eta)[Y]  ->  theta[Y] · eta[Y]
```

The off-diagonal `tapp1_fapp0` rules promoted on 2026-07-04 deliberately use
the fold/accumulation direction needed by representable interchange:

```text
theta[Y] · eta[p]      -> (theta · eta)[p]
theta[q] · eta[X]      -> (theta · eta)[q]
theta[q] · eta[p]      -> (theta · eta)[q · p]
```

This is an explicit design choice and a pause/re-design point if later
implementation finds a roadblock rooted in this normal form.

- the higher-action stable heads
  `hom_postcomp_tele_fapp1_fapp0` and
  `hom_precomp_along_tele_fapp1_fapp0` expose the action on 2-cells. They now
  fold identity 2-cells and vertical composites by runtime reduction:

```text
action(id_f)                  -> id
action(e_gh) · action(e_fg)   -> action(e_gh · e_fg)
```

The earlier proof-time `unif_rule` workaround and its four checked equality
symbols were part of the superseded post-baseline attempt; they are no longer
the active design.

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

The next representable-interchange target should start from that existing
diagnostic and generalize it by adding:

```text
h : Hom_B(N,L)
d_gh : g => h.
```

In schematic notation, the existing check is approximately the
pre-configured one-variable interchange/naturality slice:

```text
(g o beta)_*(-) o_Cat (e_fg)_*[-]
  ->
(e_fg)_*[-] o_Cat beta_*(-)
```

and at input `alpha`:

```text
(g o beta) · (e_fg)_*[alpha]
  ->
(e_fg)_*[beta · alpha].
```

The four-cell representable generalization should aim first at the similarly
pre-configured form:

```text
((d_gh)_*[beta]) · ((e_fg)_*[alpha])
  ->
(d_gh · e_fg)_*[beta · alpha].
```

This is closer to the computational shape wanted by the demo than starting
from the symmetric textbook formula directly. A textbook interchange theorem
can then be proved by first rewriting/setting it up into this pre-configured
form, rather than by forcing the kernel to make every presentation reflexive.
This observation also reopens the orientation question for off-diagonal
vertical-composite rules: a rule expanding `(theta · eta)[f]` may be the wrong
runtime direction for the representable interchange normal form.

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

This bridge was not promoted as an EH-local rule. It remains useful evidence
for a missing join at the identity-endomorphism horizontal-composition
boundary, but the promoted fold-oriented representable-interchange path
should be used first. If this bridge is revisited, warning deltas should be
treated as diagnostics rather than as an automatic veto.

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

The pre-revision plan treated all three as intentionally raw. That was too
coarse. The codomain-side precomposition shape

```text
k o hom_precomp_along_fapp0(p,g)
```

should be reclassified as a likely missing runtime accumulation rule:

```text
k o ((F[p])^*(g))  ->  (F[p])^*(k o g).
```

The source-side precomposition and adjacent-codomain postcomposition shapes
remain open accumulation/functoriality bridge candidates. Existing proof-time
unification is useful compatibility evidence, but it should not be used to
declare these runtime normal forms unnecessary before the arbitrary-hom
interchange proof has been probed.

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

The post-`3f9ee5f` attempt made them usable at proof time by promoted
`unif_rule`s and checked `eq_refl` equality lemmas. That interim state is
superseded. The active kernel now promotes the runtime fold direction that
the original runtime bridge probe used:

```text
action(e_gh) o action(e_fg)  ->  action(e_gh o e_fg)
```

and changed the warning inventory. A later scratch probe for the reverse
stable-projection direction

```text
action(e_gh o e_fg)  ->  action(e_gh) o action(e_fg)
```

also checked quietly but produced local warning families under warnings. The
active design chooses the fold direction as the intended runtime normal form
for representable interchange; warning deltas are diagnostic evidence, not a
semantic veto.

The exact precomposition-source probe confirms that the stable composite
target:

```text
(F(p o q))^*(g)
```

now normalizes to the folded stable form:

```text
(F(p o q))^*(g)
```

so a promoted raw-runtime bridge may choose the composite expression as a
readable RHS when that is the accepted canonical normal form.

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

The promoted interim solution is proof-time identification:

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
tele-level bridges remain open infrastructure. The full-file `+38` warning
delta above belongs to the fold direction

```text
action(e_gh) o action(e_fg) -> action(e_gh o e_fg).
```

After the 2026-07-03 orientation review, the reverse stable-projection
direction was also tested in:

```text
tmp/probes/hom_action_tele_bridge_reverse_probe.lp
```

That append probe checks quietly and warning-enabled, with local warning
families at the probe rules. It has not yet been installed at the active
owning position or fully classified. Therefore the plan must not use the
earlier `+38` result as evidence that all tele-level runtime orientations are
rejected.

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

The pre-revision EH decision was stricter than those probes and promoted no
raw `comp_fapp0`-headed bridge. That decision is no longer adequate for the
next implementation phase. In particular:

```text
k o ((F[p])^*(g)) -> (F[p])^*(k o g)
```

is now a likely missing accumulation rule and should be probed first at the
owning position. The existing proof-time compatibility bridges remain useful:

```text
hom_postcomp_fapp0(...)       ~~  raw comp_fapp0(F[-], ...)
hom_precomp_along_fapp0(...)  ~~  raw comp_fapp0(..., F[-])
```

but proof-time compatibility is not by itself a reason to reject a
semantically intended runtime accumulation. The append probes become warning
evidence to classify: the minimal bridge is underconstrained, while the
stricter bridge still overlaps with category-specific composition owners
(`Op_cat`, `Path_cat`, `Catd_cat`, `Cat_cat`, `Terminal_cat`) and existing
postcomposition identity/composite rules. Those warnings are not a semantic
veto, but they show that any promoted runtime bridge would need a narrower
owner, a stable intermediate projection head, or follow-up joins.

Do not promote the append-probe rules verbatim. Also do not assume the active
composite-stable-head-to-nested-stable-head direction is final for every
interchange consumer. The interchange proof may force a redesign or a
fold-direction theorem/rule at the relevant projection owner.

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
`theta` with respect to `alpha`. An explicit proof route succeeded in the
superseded post-`3f9ee5f` attempt as `transf_interchange_component`, but that
theorem is no longer part of the active kernel after the 2026-07-04
fold-orientation promotion.

## Architecture Decision

Do not start by adding a global Eckmann-Hilton rewrite rule.

Do not promote the temporary candidate bridge as-is.

Instead, implement the application in phases:

1. Promote the safe reviewer-facing computation slice first: transparent EH
   aliases and the already-validated `eq_refl` computation lemmas.
2. Pause EH-specific theorem work while auditing the hom-action accumulation
   and interchange-orientation infrastructure identified by the 2026-07-03
   review.
3. Generalize the existing representable-postcomposition interchange check to
   the pre-configured two-2-cell form before attempting the symmetric textbook
   statement.
4. Add reviewer-facing notation and proof symbols whose bodies use the
   existing computation by `eq_refl`.
5. Define a named horizontal-composition facade for the identity-endomorphism
   setting, if needed, without immediately adding a runtime rewrite.
6. State the comparison between that facade and vertical composition as a
   mathematical lemma.
7. Attempt to prove that comparison using the existing equality combinators
   and existing interchange/naturality owners.
8. Only if the proof is blocked by a genuine missing computational join, probe
   the smallest owner-position bridge under the rewrite-rule SOP.

This preserves the project discipline: generic functoriality and naturality
belong to the global `fapp*`/`tapp*` calculus, while specialized bridges are
allowed only as measured projection-ladder joins.

## Reassessment

Review date: 2026-07-03.

The post-implementation review found that the pre-revision plan was not
globally coherent enough to continue directly into EH theorem implementation.
The safe first slice remains valid. The broader path paused for an
infrastructure audit, then the 2026-07-04 promotion resolved the main
normal-form choices in favor of the fold-oriented package. The main
corrections were:

- raw precomposition accumulation was misclassified as intentionally raw;
- tele-level proof-time unification was an interim workaround, not a final
  runtime decision, and has now been superseded by runtime folds;
- the ordinary-transfor component theorem is not a substitute for the
  arbitrary-hom representable interchange law and is no longer active;
- the off-diagonal vertical-composite orientation for `tapp1_fapp0` needed
  the fold direction required by representable interchange; this direction is
  now active.

The revised architecture remains: stable hom-action computation first,
pre-configured arbitrary-hom interchange second, then Eckmann-Hilton
specialization. The plan also continues to avoid a global EH rewrite and
treats raw `assert ... ≡ ...` diagnostics as DevOps evidence rather than the
reviewer-facing theorem.

Computable feasibility is mixed:

- High confidence:
  the basic `EH_2End`, `EH_vcomp`, identity postcomposition, identity
  whiskering, first-layer post/pre hom-action functoriality, and represented
  source accumulation can be promoted as `eq_refl` proof symbols.
- High confidence:
  raw expanded semantic presentations can be related to stable hom-action
  presentations at proof time by the existing `hom_postcomp_fapp0` and
  `hom_precomp_along_fapp0` unification rules. This is compatibility
  evidence, not a blanket reason to reject runtime accumulation.
- High confidence:
  the precomposition codomain shape
  `k o ((F[p])^*(g)) -> (F[p])^*(k o g)` is a semantically natural
  accumulation candidate and is now active runtime infrastructure.
- Historical evidence:
  component-level ordinary-transfor interchange was proved in the superseded
  post-`3f9ee5f` attempt as `transf_interchange_component`, using
  `comp_assoc`, strict functoriality, and strict naturality. This result is
  component-level, not whole-transfor extensionality, and is no longer part
  of the active kernel.
- Low confidence as a whole-theorem target:
  whole-transfor interchange currently lacks a known transfor extensionality
  principle. Further interchange work should therefore target the
  arbitrary-hom representable theorem, not whole-transfor equality.
- Promoted:
  the coherent fold-oriented package now in the active kernel makes the
  pre-configured arbitrary-hom representable interchange statement compute by
  conversion:
  `((d_gh)_*[beta]) · ((e_fg)_*[alpha])` normalizes to
  `(d_gh · e_fg)_*[beta · alpha]`. The required package was not merely a
  local interchange rule; it included first-layer hom-action fold migration,
  precomposition codomain accumulation, runtime DefIso cancellation exposed
  by that migration, a `Prof_reindex_transf` projection-ladder functoriality
  bridge, tele-level higher-action folds, and a general off-diagonal
  `tapp1_fapp0` vertical-composite fold. The regression check lives in
  `emdash3_2_checks.lp` under "Pre-configured four-cell interchange for the
  Cat-valued representable".
- Follow-up audit:
  the promoted fold package intentionally changes the warning inventory. The
  detached pre-hygiene package reported `1704` warnings (`1537` unjoinable
  critical pairs and `167` replaceable-pattern reports). After LHS endpoint
  hygiene in the active file, `make warning-summary` reports `1479` warnings
  (`1312` unjoinable critical pairs and `167` replaceable-pattern reports).
  After promoting the two remaining raw adjacent hom-action folds, the active
  inventory is `1573` warnings (`1406` unjoinable critical pairs and `167`
  replaceable-pattern reports).
  The strict LHS audit passes. These warnings are diagnostic evidence for
  follow-up joins and not a semantic veto on the promoted normal form.

Decision status after the 2026-07-04 promotion:

The safe first slice is still retained. The former infrastructure pause is
resolved in favor of the fold-oriented hom-action package. Further
implementation may continue from the pre-configured representable
interchange regression, with warning-family classification and follow-up
joins tracked as maintenance work rather than as a blocker.

Settled decisions after the 2026-07-03 review:

1. The first promoted slice is conservative: transparent EH aliases and safe
   `eq_refl` lemmas only.
2. Generic single-functor functoriality remains oriented in the usual fold
   direction `F[q] o F[p] -> F(q o p)`.
3. The stable hom-action projection joins for `(F -)_*` and `(F -)^*` are now
   oriented in the fold direction at both the functor level and the capped
   `fapp0`-projected level. This is a kernel normal-form migration, not an
   EH-local shortcut.
4. The identified raw adjacent hom-action folds are active runtime
   accumulation:

```text
F[q] o ((F[p])_*(g))       ->  (F[q o p])_*(g)
k o ((F[p])^*(g))          ->  (F[p])^*(k o g)
((F[p])^*(g)) o F[q]       ->  (F[p o q])^*(g)
```
5. Ordinary naturality accumulation is represented by the full `tapp1_func`
   naturality rules and the capped `tapp1_fapp0` rules. Off-diagonal vertical
   composites now fold to the composite transfor action; this is the chosen
   normal form for the representable-interchange path.
6. Whole-transfor interchange is not the first target; without extensionality,
   the next interchange deliverable should be arbitrary-hom representable
   interchange in the pre-configured form. The previously promoted
   component-level ordinary-transfor theorem was part of the superseded
   post-baseline attempt and is no longer active.
7. Tele-level higher-action identity/composition is active runtime
   infrastructure in the fold direction. The previous proof-time `unif_rule`
   workaround is superseded.
8. The pre-configured arbitrary-hom representable interchange regression is
   active and reflexive by conversion. The reviewer-facing equality theorem
   `hom_postcomp_representable_interchange_eq` is now promoted in
   `emdash3_2.lp`.

The remaining decisions are now:

1. EH specialization surface.

   Specialize `hom_postcomp_representable_interchange_eq` toward the
   identity-endomorphism setting before attempting a symmetric textbook
   whole-transfor interchange statement. Whole-transfor equality should stay
   deferred unless a checked transfor extensionality principle is added.

2. Warning-family follow-up for the promoted fold package.

   Use warning-enabled logs to classify the remaining overlap families around
   `hom_postcomp_fapp0`, `comp_fapp0`, `comp_cat_fapp0`,
   `hom_precomp_along_fapp0`, `tapp1_fapp0`, and the new projection-ladder
   joins. Add joins only when they express intended computation or repair a
   concrete consumer.

3. Horizontal-composition facade.

   Decide whether `EH_hcomp_raw` remains a transparent alias over the current
   owner stack, or whether a named stable facade is needed. A facade must not
   hide semantic duplication; it should route through the chosen hom-action
   owner.

4. Horizontal-to-vertical proof route.

   Decide the intended status of `EH_hcomp_to_vcomp`: explicit equality proof,
   proof-time `unif_rule`, or runtime bridge. The promoted representable
   interchange computation should be used first before considering an
   EH-specific bridge.

5. Alias elaboration surface.

   Probe the proposed `EH_*` aliases in their final alias form before
   promotion, because unfolded `Hom` types may elaborate more robustly than
   `Obj (EH_2End x)`.

Infrastructure no longer classified as optional:
warning-family classification for the promoted fold package, plus any raw
bridge/accumulation rule that a later theorem actually needs.

Pause/re-design trigger:
if the concrete arbitrary-hom interchange implementation repeatedly gets
stuck because the active stable hom-action projection normal form expands
composite base arrows while the proof needs a folded/accumulated
presentation, pause before adding ad hoc bridges. Reassess whether the
hom-action projection orientation should stay as-is with theorem-style
`eq_sym` lemmas, receive a narrow proof-time `unif_rule`, or be redesigned at
the owning projection layer. Do not silently work around this choice with
EH-local runtime rules.

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
`comp_fapp0` orientation. The next implementation target is not the
EH-specialized two-variable theorem yet, and not a premature whole-transfor
extensionality theorem. It is the arbitrary-hom representable
postcomposition theorem in the pre-configured form obtained by generalizing
the existing `emdash3_2_checks.lp` interchange diagnostic.

Auxiliary surface: ordinary natural transformations in `Cat_cat`.

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
over it. The superseded `transf_interchange_component` proof showed that this
route is possible componentwise, but it is no longer the active primary route
to the EH application.

Primary surface: arbitrary-hom/representable postcomposition.

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

For implementation, first target the pre-configured computational shape:

```text
((e_gh)_*[beta]) · ((e_fg)_*[alpha])
  =
(e_gh · e_fg)_*[beta · alpha]
```

where `(-)_*` is the appropriate higher representable postcomposition action.
The symmetric textbook statement can be derived by rewriting/setup into this
form. This avoids forcing every surface presentation of horizontal
composition to compute by one global conversion rule.

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

The currently best pre-configured route is to engineer the EH proof backward
from `hom_postcomp_representable_interchange_eq`, not from a fully symmetric
surface statement. With `i = id_B(x)` and `1_i = id_{Hom_B(x,x)}(i)`, the
useful degenerate instances are:

```text
(beta_*[1_i]) · (1_i_*[alpha])
  =
(beta · 1_i)_*[1_i · alpha]

(1_i_*[alpha]) · (beta_*[1_i])
  =
(1_i · beta)_*[alpha · 1_i]
```

The right sides are designed to meet at the same horizontal composite
`beta_*[alpha]` after vertical-unit and identity-action computation. This
should let the final commutativity proof compare `beta · alpha` and
`alpha · beta` through a shared computational middle term, instead of asking
one raw horizontal-composition presentation to reduce directly to vertical
composition globally.

The current known gap is the right identity whiskering/unit:

```text
beta_*[1_i] = beta
```

The existing general unification rule
`tapp1_fapp0 epsilon id_X ≡ tapp0_fapp0 X epsilon` suggests the missing
kernel comparison may be a stable component rule for
`tapp0_fapp0 x (hom_postcomp_tele_fapp1_fapp0 ... beta)`, or an explicit
EH-local proof over that component. This should be investigated separately
before adding a broad `EH_hcomp_to_vcomp` bridge.

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

1. Keep `tmp/probes/hom_action_functoriality_accumulation_probe.lp` and
   `tmp/probes/hom_action_raw_accumulation_bridge_probe.lp` as the focused
   scratch probes while iterating.
2. Confirm the already-promoted reviewer-facing `eq_refl` lemmas:
   first-layer post/pre identity, composite-arrow functoriality,
   postcomposition represented-source accumulation, and theorem-style fold
   equalities.
3. Probe the missing codomain-side precomposition accumulation first:

   ```text
   k o ((F[p])^*(g)) -> (F[p])^*(k o g)
   ```

   Install it only after an owning-position full-file probe, warning-enabled
   classification, and a checked regression lemma.
4. Then separately classify:

   ```text
   F[q] o ((F[p])_*(g))       -> (F(q o p))_*(g)
   ((F[p])^*(g)) o F[q]       -> (F[p o q])^*(g)
   ```

   with exact composition order fixed by focused typed probes. These may be
   runtime accumulation rules, proof-time bridges, or explicit theorem lemmas;
   the decision is rule-specific.
5. Record both active and possibly desired readings where useful:

   ```text
   active stable projection:
     (F(q o p))_*(g) -> (F q)_*((F p)_*(g))

   possible fold/accumulation theorem or runtime direction:
     (F q)_*((F p)_*(g)) = (F(q o p))_*(g)
   ```

   Do not flip existing active rules globally without downstream and warning
   audits.
6. For tele-level higher-action identity/composition, probe both directions:

   ```text
   action(e_gh) o action(e_fg) -> action(e_gh o e_fg)
   action(e_gh o e_fg)         -> action(e_gh) o action(e_fg)
   ```

   Include identity rules in the same package. Decide whether the proof-time
   `unif_rule`s should remain as interim infrastructure, be replaced by
   runtime rules, or be kept only for proof elaboration.
7. Re-run `compute` on both sides of each candidate lemma before deciding
   between explicit proof terms, proof-time unification, or runtime rewrite.

### Phase 2: Four-Cell Interchange Foundation

Work items:

1. Keep the existing arbitrary-hom four-cell probe as the primary scratch
   target, and add a new probe that starts from the existing
   `emdash3_2_checks.lp` representable interchange diagnostic.
2. Generalize that diagnostic with `h` and `d_gh : g => h`.
3. First target the pre-configured form:

   ```text
   ((d_gh)_*[beta]) · ((e_fg)_*[alpha])
     =
   (d_gh · e_fg)_*[beta · alpha]
   ```

   before trying the symmetric textbook statement.
4. Normalize both sides with `compute`; also normalize the candidate
   intermediate setup terms separately.
5. If the proof gets stuck, classify whether the missing infrastructure is:
   raw hom-action accumulation, tele-level higher-action functoriality,
   off-diagonal vertical-composite orientation for `tapp1_fapp0`, ordinary
   associativity, or an absent stable projection head.
6. Treat the ordinary-transfor component theorem as auxiliary evidence. Do
   not block the arbitrary-hom representable theorem on whole-transfor
   extensionality.

Current implementation status:
the ordinary-transfor component route succeeded in the superseded
post-`3f9ee5f` attempt but is not active. No whole-transfor interchange
theorem has been promoted. The arbitrary-hom representable pre-configured
diagnostic now computes by conversion, and the next implementation target is
the reviewer-facing theorem over that surface.

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
post/pre functoriality computes; it also shows that at least one
precomposition accumulation rule was missing and has now been promoted.
Tele-level identity/composition is handled by runtime folds in the active
kernel.

Status:
active kernel promoted; first-layer post/pre identity, fold-composition,
capped object-action, source accumulation, precomposition codomain
accumulation, tele-level identity/composition folds, raw DefIso cancellation,
and `Prof_reindex_transf` projection-ladder joins are in `emdash3_2.lp`.
Strict LHS audit passes after endpoint-slot hygiene. Remaining work is
warning-family classification and adding follow-up joins only for concrete
consumers.

### EH-RAW-PRESENTATION-BRIDGES

Trigger:
raw adjacent terms such as `F[q] o ((F[p])_*(g))` and
`((F[p])^*(g)) o F[q]` used to stay as raw `comp_fapp0` terms. The
codomain-side precomposition form `k o ((F[p])^*(g))` was the first active
accumulation promoted in this family.

Required audit:
classify these raw shapes rule by rule. The promoted family is:

```text
F[q] o ((F[p])_*(g)) -> (F[q o p])_*(g)
k o ((F[p])^*(g)) -> (F[p])^*(k o g).
((F[p])^*(g)) o F[q] -> (F[p o q])^*(g)
```

Existing proof-time unification from `hom_postcomp_fapp0` and
`hom_precomp_along_fapp0` to raw `comp_fapp0` remains useful compatibility
evidence for other surfaces, but these three shapes now have intended runtime
normal forms.

Status:
complete for the currently identified adjacent raw hom-action shapes. The
postcomposition adjacent-codomain and precomposition source-side folds were
promoted after append and owner-position full-copy probes. Warning-enabled
checking exposed additional overlap families concentrated at `comp_fapp0`;
those warnings remain diagnostic evidence, not a semantic veto.

### EH-TELE-HIGHER-ACTION-FUNCTORIALITY

Trigger:
`hom_postcomp_tele_fapp1_fapp0` and
`hom_precomp_along_tele_fapp1_fapp0` expose higher action on 2-cells but do
runtime-compute identity and composition of those 2-cells at the stable head.

Required audit:
track whether the promoted projection-ladder joins create concrete missing
joins downstream. Any additional proposed rule must be probed at the owning
position and warning-classified because this layer overlaps with generic
functoriality.

Status:
active runtime fold design. The previous proof-time `unif_rule` workaround is
superseded and no longer present in the active kernel.

### EH-OFFDIAGONAL-VCOMP-ORIENTATION

Trigger:
`tapp0_fapp0` currently expands point-components of vertical composites:

```text
(theta · eta)[Y] -> theta[Y] · eta[Y].
```

The arbitrary-hom representable interchange setup needs an off-diagonal
comparison for `(theta · eta)[f]`. The active kernel chooses the
fold/accumulation direction.

Required audit:
track warning families and downstream consumers of the promoted
`tapp1_fapp0` off-diagonal folds:

```text
theta[Y] · eta[p] -> (theta · eta)[p]
theta[q] · eta[X] -> (theta · eta)[q]
theta[q] · eta[p] -> (theta · eta)[q · p]
```

Do not add the reverse direction. Reconsider this design only if a concrete
consumer demonstrates a roadblock rooted in this normal form.

Status:
active runtime fold design. The endpoint-correct partial folds
`theta[Y] · eta[f] -> (theta · eta)[f]` and
`theta[f] · eta[X] -> (theta · eta)[f]` are promoted, but they were not enough
by themselves to make four-cell representable interchange reflexive. The
decisive promoted rule is the general off-diagonal fold:

```text
theta[q] · eta[p] -> (theta · eta)[q · p].
```

The promoted version keeps the `comp_fapp0` source/middle/target endpoints
implicit on the LHS, because explicit `fapp0` endpoints failed to match after
stable endpoint projection had already normalized.

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
start from the existing representable postcomposition diagnostic and
generalize it to the pre-configured two-2-cell form:

```text
((d_gh)_*[beta]) · ((e_fg)_*[alpha])
  =
(d_gh · e_fg)_*[beta · alpha].
```

Use the ordinary-transfor component theorem as auxiliary evidence only; do
not require whole-transfor extensionality for the arbitrary-hom result.

Status:
partially complete. The active diagnostics now include a conversion
regression for the pre-configured arbitrary-hom representable theorem in
`emdash3_2_checks.lp`, and `emdash3_2.lp` now promotes the corresponding
reviewer-facing equality theorem
`hom_postcomp_representable_interchange_eq`. Any EH-specialized interchange
theorem remains open. The previous `transf_interchange_component` theorem was
part of the superseded post-baseline attempt and is no longer in the active
kernel.

### EH-FOUR-CELL-INTERCHANGE

Trigger:
the current `emdash3_2_checks.lp` interchange diagnostic covers a
one-postcomposing-cell naturality slice, not the full four-cell textbook law.

Required audit:
prove or classify the arbitrary-hom representable theorem first. If proof
attempts fail, identify whether the missing infrastructure is raw hom-action
accumulation, tele-level higher-action orientation, off-diagonal
vertical-composite orientation, associativity/naturality proof lemmas,
proof-time comparison, or a runtime bridge.

Status:
partially complete. Whole-transfor equality remains deferred without
extensionality. The arbitrary-hom representable pre-configured interchange
diagnostic computes by conversion in `emdash3_2_checks.lp`, and the
reviewer-facing equality theorem is promoted in `emdash3_2.lp`. The next
target is to specialize that theorem toward Eckmann-Hilton and resolve the
right-identity whiskering/component gap.

### EH-SURFACE-SYNTAX

Trigger:
the raw kernel terms become unreadable in `emdash3_2.lp`.

Required audit:
add transparent aliases only; no semantic duplication and no helper alias with
a copied body that bypasses the named owner.

Status:
open.

## Implementation Log

### 2026-07-03/04: Fold-Orientation Baseline Probe And Promotion

Probe location:

```text
/home/user1/emdash1_orientation_3f9ee5f/emdash2
```

Baseline commit:

```text
3f9ee5f77741b2293467f0f234b9456be5e14351
```

Clean baseline warning inventory:

```text
1366 warning(s)
1199 unjoinable critical pair
 167 replaceable pattern variable
```

The probe replaced the first-layer stable post/pre hom-action composition
orientation by the fold direction:

```text
(F q)_* o (F p)_*       -> (F(q o p))_*
(F q)_*((F p)_*(g))     -> (F(q o p))_*(g)
(F p)^* o (F q)^*       -> (F(q o p))^*
(F p)^*((F q)^*(g))     -> (F(q o p))^*(g)
```

It also added the codomain-side precomposition accumulation:

```text
k o ((F[p])^*(g)) -> (F[p])^*(k o g).
```

The first fold-only package checked at the kernel level but broke a DefIso
diagnostic. Computing both sides showed that the migration exposed raw
`comp_fapp0` DefIso cancellation inside a hom-action argument. Adding runtime
raw DefIso cancellation restored the focused DefIso check. Full diagnostics
then exposed a weighted-limit beta residue where
`Prof_reindex_transf(from) · Prof_reindex_transf(to)` was hidden behind a
stable projection head. Adding identity/composition joins for
`Prof_reindex_transf` restored full `make check`.

Validation after first-layer fold, precomp accumulation, raw DefIso
cancellation, and `Prof_reindex_transf` joins:

```text
make check: passed
warning-summary: 1631 warning(s)
 1464 unjoinable critical pair
  167 replaceable pattern variable
```

Adding runtime fold rules for tele-level post/pre higher action also passed:

```text
action(e_gh) o action(e_fg) -> action(e_gh o e_fg)

make check: passed
warning-summary: 1667 warning(s)
 1500 unjoinable critical pair
  167 replaceable pattern variable
```

The endpoint-correct partial off-diagonal vertical-composite folds checked
but did not make representable interchange reflexive:

```text
theta[Y] · eta[p] -> (theta · eta)[p]
theta[q] · eta[X] -> (theta · eta)[q]
```

The successful pre-configured arbitrary-hom representable interchange probe
required the general off-diagonal fold:

```text
theta[q] · eta[p] -> (theta · eta)[q · p].
```

with inferred source/middle/target endpoint slots on the `comp_fapp0` LHS.
The explicit-endpoint variant typechecked but failed to match the
representable statement after endpoint projection normalized to stable
`hom_postcomp_fapp0` heads.

Focused probe:

```text
tmp/probes/orientation_representable_interchange_probe.lp
```

Result:

```text
((e_gh)_*[beta]) · ((e_fg)_*[alpha])
  ≡
(e_gh · e_fg)_*[beta · alpha]
```

checks by conversion in the detached baseline.

Validation for the complete detached package:

```text
make check: passed
make examples: passed
warning-summary: 1704 warning(s)
 1537 unjoinable critical pair
  167 replaceable pattern variable
```

The pre-promotion LHS audit reported eight reconstructible compound slots
across four new rule clauses. The flagged clauses were the migrated
first-layer post/pre functor-level folds, the new precomposition codomain
accumulation, and the `Prof_reindex_transf` composition bridge.

Promotion decision:
the package was promoted to the active `emdash3_2.lp` on 2026-07-04 by
replacing the wrong post-`3f9ee5f` attempt with the checked detached package.
This intentionally superseded the proof-time tele workaround and the
component-level ordinary-transfor interchange theorem that had been added
after `3f9ee5f`.

LHS hygiene after promotion:
the reconstructible endpoint/category slots in those four rule clauses were
replaced by `_`, preserving the semantic discriminators while avoiding
unreviewed compound inferred LHS slots.

Validation after active promotion and LHS hygiene:

```text
make check: passed
make examples: passed
strict LHS audit: passed
warning-summary: 1479 warning(s)
 1312 unjoinable critical pair
  167 replaceable pattern variable
```

A generalized pre-configured representable interchange assertion was added
to `emdash3_2_checks.lp`:

```text
((e_gh)_*[beta]) · ((e_fg)_*[alpha])
  ≡
(e_gh · e_fg)_*[beta · alpha]
```

The check succeeds by conversion in the active kernel.

Architectural conclusion:
the fold-oriented design is now the active kernel normal form. It directly
supports the desired pre-configured representable interchange and remains a
general infrastructure migration, not a small EH-local patch. Warning-family
classification remains useful follow-up work, but warnings alone were not a
veto on this semantically intended runtime normal form.

### 2026-07-04: Raw Adjacent Folds And Representable Interchange Theorem

Promoted in `emdash3_2.lp`:

- `hom_postcomp_fapp0_raw_adjacent_fold_eq`
- `hom_precomp_along_fapp0_raw_adjacent_fold_eq`
- `hom_postcomp_representable_interchange_eq`

The new runtime folds are:

```text
F[q] o ((F[p])_*(g))       ->  (F[q o p])_*(g)
((F[p])^*(g)) o F[q]       ->  (F[p o q])^*(g)
```

Together with the already active codomain-side precomposition fold:

```text
k o ((F[p])^*(g))          ->  (F[p])^*(k o g)
```

these complete the currently identified raw adjacent hom-action accumulation
family.

Probe history:

```text
tmp/probes/hom_action_raw_adjacent_fold_current_probe.lp
tmp/probes/emdash3_2_raw_adjacent_fold_full_probe.lp
tmp/probes/representable_interchange_eq_symbol_probe.lp
```

The append probe and owner-position full-copy probe checked quietly and
warning-enabled. The full-copy warning-enabled inventory matched the promoted
result:

```text
warning-summary: 1573 warning(s)
 1406 unjoinable critical pair
  167 replaceable pattern variable
```

The delta from the previous active `1479` inventory is concentrated at
`comp_fapp0`, as expected for these raw adjacent bridges. This is recorded as
diagnostic follow-up evidence, not as a veto.

The theorem `hom_postcomp_representable_interchange_eq` promotes the
pre-configured representable interchange diagnostic to a reviewer-facing
equality proof:

```text
((e_gh)_*[beta]) · ((e_fg)_*[alpha])
  =
(e_gh · e_fg)_*[beta · alpha]
```

Its proof is `eq_refl` against the fold-oriented kernel normal form.

### 2026-07-03: Post-Implementation Roadmap Correction

The plan was reassessed after the component-level ordinary-transfor
interchange slice. The old roadmap treated some raw hom-action presentations
as intentionally proof-time-only and treated tele-level proof-time
unification as sufficient for the current EH path. That was too conservative
and partially inconsistent with the intended Došen-style accumulation
discipline.

Corrections recorded in this report:

- `k o ((F[p])^*(g)) -> (F[p])^*(k o g)` was a first-class missing
  accumulation candidate and is now active runtime infrastructure.
- Raw adjacent postcomposition and source-side precomposition bridges are
  live rule-specific audit candidates, not globally rejected runtime behavior.
- Tele-level higher-action composition is now active runtime fold
  infrastructure.
- Off-diagonal vertical-composite orientation for `tapp1_fapp0` is now the
  fold direction required by representable interchange.
- The next interchange target is the pre-configured arbitrary-hom
  representable theorem obtained by generalizing the existing
  `emdash3_2_checks.lp` representable interchange diagnostic.

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

The equality symbols remain in the active file. In the original slice the
`*_fold_eq` lemmas recorded the folded mathematical direction by `eq_sym`
without changing runtime orientation. The 2026-07-04 promotion later changed
the runtime orientation itself to the fold direction, so this section should
now be read as the proof-symbol history, not as the current normal-form
policy.

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

Superseded. These symbols were promoted in the post-`3f9ee5f` attempt, but
the 2026-07-04 fold-orientation promotion replaced that attempt and removed
the proof-time workaround from the active kernel.

Formerly promoted near the tele-level hom-action owners in `emdash3_2.lp`:

- `hom_postcomp_tele_fapp1_fapp0_id_eq`
- `hom_postcomp_tele_fapp1_fapp0_comp_eq`
- `hom_precomp_along_tele_fapp1_fapp0_id_eq`
- `hom_precomp_along_tele_fapp1_fapp0_comp_eq`

The four equality symbols were `eq_refl` terms enabled by four narrow
proof-time unification rules. The active kernel now uses runtime tele-level
folds instead.

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

Superseded. This theorem was promoted in the post-`3f9ee5f` attempt, but the
2026-07-04 fold-orientation promotion replaced that attempt. The theorem is
therefore historical evidence, not part of the current active kernel.

Formerly promoted near the ordinary transfor/naturality owner in
`emdash3_2.lp`:

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
