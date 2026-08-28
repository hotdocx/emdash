# Emdash v3.2 Cubical Dependent-Hom Plan

Date: 2026-08-23 (America/Toronto)

Plan-ID: `CUBICAL-DEPENDENT-HOM-V3.2`

Status: **completed bounded implementation plan**. The fully varying endpoint
telescope and combinatorial cubical continuations remain explicitly deferred
at the precise prerequisites recorded below.

Corrective-Continuation:
`REPORT_EMDASH_V3_2_CUBICAL_INTERNALIZATION_AND_SIGMA_DERIVATION_PLAN_2026-08-24.md`.
That plan reopens the generic endpoint telescope as primitive `homdc_int` and
requires any two-sided total to derive through existing Sigma/comma machinery.

Supersedes: no completed implementation plan. It promotes only the two-sided
dependent-hom/cubical direction developed after the dependent-simplex and
internal-laxity plans; those plans remain authoritative for their own scopes.

Depends-On: `emdash3_2.lp`, especially `hom_int`, `hom_con_int`, `homd_`,
`homd_int`, Sigma/Pi totalization, and whole action; the completed internal
laxity, profiled Gray, and coherent-nerve/dependent-simplex plans named below;
and the active Foundations, canonical syntax, current SOP, and Git workflow.

Side-Task-Ledger: `CUB-00`, `CUB-01`, `CUB-02`, `CUB-03`, `CUB-04`,
`CUB-05`, `CUB-06`, `CUB-07`, `CUB-DOC-8`, and `CUB-CLOSE-9`.

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`; brainstorming decision response
`0115_2026-08-22T10-13-17Z_01a028f3-9396-7dc1-9187-dac4ba840075.md`.

Infinity-Codex-Decision-Responses: `infinity-codex:019ffe39-2eb9-7080-88e3-06b77d69b8d1:01a028f3-9396-7dc1-9187-dac4ba840075`.

Branch: `goal/cubical-dependent-hom-v3.2`

Worktree: `/home/user1/emdash1-cubical-hom-v1`

Baseline: `689f41c057f5eeee5fd82486fcad79acd136bdfa` (`main` and
`origin/main` at goal creation).

Parent authorities:

- `emdash3_2.lp`, especially `hom_int`, `hom_con_int`, `Hom_tele_func`,
  `Hom_func`, `fib_cov_tapp0_func`, the displayed endpoint-action ladder,
  `homd_`, and `homd_int`;
- `REPORT_EMDASH_V3_2_INTERNAL_LAXITY_AND_GROUPOIDAL_REALIZATION_CONTINUATION_PLAN_2026-08-17.md`;
- `REPORT_EMDASH_V3_2_PROFILED_GRAY_HOM_AND_I_TENSOR_I_PLAN_2026-08-17.md`;
- `REPORT_EMDASH_V3_2_COHERENT_NERVE_AND_DEPENDENT_SIMPLEX_BRIDGE_PLAN_2026-08-19.md`;
- `EMDASH_FOUNDATIONS.md`, the current SOP, canonical syntax, and
  `AGENTS.md`.

Recovery evidence:

- Infinity Codex response `0115`, archived at
  `/home/user1/emdash1/emdash2/tmp/ai-responses/sessions/2026-08-14_019ffe392eb9/responses/0115_2026-08-22T10-13-17Z_01a028f3-9396-7dc1-9187-dac4ba840075.md`;
- the later variance correction and cross-corner analysis in the originating
  conversation.

Active code and this evolving plan outrank archived conversation.

## 1. Objective

Add a computationally internal **cubical dependent hom** to the functorial
type-theory layer without replacing the existing globular `hom_int` or
simplicial `homd_int` architecture.

The selected construction must compare two independently transported
dependent endpoints in a common cross-corner fibre. Its prototypical identity
Hom instance must compute to the ordinary directed lax-square filler category

```text
Hom_{Hom_C(x1,y2)}(b o u, v o a),
```

for

```text
u : Hom_C(x1,x2),
v : Hom_C(y1,y2),
a : Hom_C(x1,y1),
b : Hom_C(x2,y2).
```

The first bounded milestone is this fixed-endpoint whole classifier and its
visible square. Later rows internalize all endpoints, expose four whole edge
projections, retain a next action between squares, and test whether source,
target, and those four actions give the six square faces of a cube.

The plan does not assume that a new primitive is necessary. It requires a new
semantic owner/API, but the first hypothesis is that its fixed-endpoint form
is a transparent composition of existing whole owners.

## 2. Why Ordinary `homd_` Is Insufficient

For a displayed family `D : Z -> Cat`, ordinary dependent hom transports one
source endpoint along one base arrow and compares it with a target endpoint:

```text
homd_D(x,u;y,v)[p]
  = Hom_{D[y]}(D[p](u),v).
```

Instantiating it directly with the unit Hom profunctor on `C^op x C` gives a
legitimate but differently typed twisted cell. For forward
`a : x1 -> y1`, the relevant base arrow runs from `(y1,x2)` to `(x1,y2)`;
therefore its endpoint data are

```text
u_tw : Hom_C(y1,x2),
v_tw : Hom_C(x1,y2),

b o u_tw o a ==> v_tw,
```

because the source coordinate of a profunctor is contravariant. It does not
give the conventional fully directed square

```text
b o u ==> v o a
```

for forward side arrows `a` and `b`.

The cubical construction must instead transport `u` forward in the second
coordinate and transport `v` backward in the first coordinate, landing both
in the cross fibre before taking their hom.

## 3. Selected Curried Mathematical Interface

Let

```text
E : K1^op -> Catd(K2)
```

be the curried form of a Cat-valued mixed-variance family. Fix

```text
x1 y1 : Obj(K1)
x2 y2 : Obj(K2)

u : Obj(E[x1][x2])
v : Obj(E[y1][y2]).
```

For side arrows

```text
a : Hom_K1(x1,y1)
b : Hom_K2(x2,y2),
```

the existing actions land in the same cross fibre:

```text
source_E(u,b) := E[x1][b](u)       : E[x1][y2]
target_E(v,a) := E[a^op][y2](v)    : E[x1][y2].
```

The selected lax orientation is

```text
homdc_E(x,u;y,v)[a][b]
  := Hom_{E[x1][y2]}
       (source_E(u,b), target_E(v,a)).
```

Its whole fixed-endpoint classifier has the curried variance

```text
homdc_E(x,u;y,v)
  : Hom_K1(x1,y1)
      -> Catd(Op(Hom_K2(x2,y2))).
```

Equivalently, it is Cat-valued on

```text
Hom_K1(x1,y1) x Hom_K2(x2,y2)^op.
```

Only the second hom factor is opposite. Emdash has the runtime rule

```text
Hom_{Op(K1)}(y1,x1) --> Hom_K1(x1,y1)
```

without an additional opposite on the hom category. Moreover `a` controls
the target of the final Hom and is covariant, whereas `b` controls its source
and is contravariant.

The mirror filler

```text
target_E(v,a) ==> source_E(u,b)
```

has the opposite profile

```text
Hom_K1(x1,y1)^op x Hom_K2(x2,y2).
```

It remains deferred until the selected lax orientation and first consumer are
green.

## 4. Prototypical Identity-Hom Instance

Take

```text
K1 = K2 = C
E  = hom_int(id_C).
```

Then

```text
E[x][y] = Hom_C(x,y),
source_E(u,b) = b o u,
target_E(v,a) = v o a,
```

and therefore

```text
homdc_{hom_int(id_C)}(u,v)[a][b]
  = Hom_{Hom_C(x1,y2)}(b o u,v o a).
```

This visible instance is the first positive consumer and mathematical
acceptance test. A negative consumer must retain the distinction from the
differently typed unit-profunctor cell
`b o u_tw o a ==> v_tw`; the latter does not even use the same pair of
vertical square edges `u : x1 -> x2` and `v : y1 -> y2`.

## 5. Transparent Fixed-Endpoint Construction Hypothesis

The fixed-endpoint owner appears derivable without a primitive symbol.

### 5.1 Source-action functor

At fixed `x1`, `x2`, `y2`, and `u`, reuse

```text
fib_cov_tapp0_func(E[x1],u)
  : Hom_K2(x2,y2) -> E[x1][y2].
```

This sends `b` to `source_E(u,b)`.

### 5.2 Target-action functor

The whole hom action of

```text
E : Op(K1) -> Catd(K2)
```

at `y1 -> x1` in `Op(K1)`, followed by fibre evaluation at `y2` and object
evaluation at `v`, should give

```text
homdc_target_func(E,v)
  : Hom_K1(x1,y1) -> E[x1][y2]
```

sending `a` to `target_E(v,a)`. The implementation should first compose the
existing `fapp1_func`, `tapp0_func`, and object-evaluation owners rather than
postulate a point action.

### 5.3 Final Hom family

For the source-action functor `S`,

```text
hom_con_int(S)
  : E[x1][y2] -> Catd(Op(Hom_K2(x2,y2)))
```

sends a target `w` to the family `b |-> Hom(S[b],w)`. Composing it with the
target-action functor gives the selected classifier:

```text
homdc_(E,x,u,y,v)
  := hom_con_int(S) o homdc_target_func(E,v).
```

This composition is the first implementation hypothesis. Reject or refine it
if the current `Functord_cat`/`Transf_cat` comparison cannot type the target
evaluation honestly, if its identity-Hom instance does not reach the expected
cross-corner category, or if it caps away the action needed by the next row.

## 6. Whole Internalization And Stable-Head Policy

The eventual `homdc_int` must internalize, in sequence:

```text
source K1 endpoint
  -> source K2 endpoint and object
    -> target K1 endpoint
      -> target K2 endpoint and object
        -> side arrow a
          -> side arrow b
            -> filler category.
```

The exact telescope may be reordered if the existing `Pi_cat`/displayed
owners require it, but it must preserve these observations and their higher
actions.

Policy:

1. prefer transparent semantic definitions;
2. introduce a readable `homdc_` alias only after its transparent body is
   green;
3. add an injective/stable `homdc_int` head only if a concrete whole-action
   consumer cannot retain the projection ladder through definitions;
4. add no rewrite or unification rule merely to make notation concise;
5. if a rule becomes necessary, follow the owner-position, LHS-minimality,
   subject-reduction, warning, negative, and catalog SOP in full.

The previously deferred displayed `homd_con_int` mirror is not an assumed
prerequisite. The cubical whole-action consumer may justify it later if the
active ordinary `hom_con_int` plus opposite specialization cannot retain the
target-side action.

### 6.1 Measured endpoint-internalization boundary

The fixed-boundary probe established the precise relationship with the
existing dependent-hom tower. For each visible first-coordinate arrow `a`,
the fibre `homdc_[a]` has the same semantic shape as

```text
homd_(E[a^op],x2,u,y2,v).
```

The active kernel can project `homd_int(FF)` through `x2`, `u`, `y2`, and `v`
once `FF` is already selected. It does not yet expose `homd_int` as a functor
of its displayed-functor argument. The minimum missing owner is schematically

```text
homd_parameter_func(D,E)
  : Functor(
      Functord_cat(D,E),
      Functord_cat(Op_catd(E),Homd_target_catd(D)))

homd_parameter_func(D,E)[FF] = homd_int(FF),
```

with a whole action on displayed transfors. Composing that owner with the
outer action of `E : K1^op -> Catd(K2)` would keep `a`, the endpoint telescope,
and every subsequent hom action under one construction. No current symbol has
that type or action; `tdapp1_int_func_transfd` instead owns the different
internal naturality/laxity comparison from `homd_int(id_E)` to a reindexed
`homd_int(GG)`.

This is the exact consumer-backed prerequisite for a fully varying
`homdc_int`. The present tranche therefore does not postulate that owner. It
continues with the strongest derived boundary already justified by existing
action: a fixed-vertical-boundary total retaining both side-arrow coordinates.
The selected orientation does not require a displayed `homd_con_int`; that
mirror remains deferred for a genuine opposite-orientation consumer.

## 7. Square, Cube, And Combinatorial Continuation

After fixed endpoints are green, construct one whole square classifier whose
objects retain

```text
u, v, a, b, alpha : b o u ==> v o a.
```

It must expose four whole line-face functors. An arrow between two such square
objects has two ordinary endpoint squares; the hom actions of the four line
faces should expose four side squares, giving the six faces of a cube.

Only after that vertical slice should the plan consider:

- an internal augmented semicube face-code category;
- a comparison with iterated walking-arrow/Gray-tensor cube shapes;
- variable-dimensional recursion;
- the groupoidal-source specialization
  `Hom_prof_along(Core_incl_func(C),id_C)` and its bicubical reading;
- a comparison with Herbelin--Ramachandra binary parametricity.

These are consumers and validation layers, not prerequisites for the first
cross-corner computation.

## 8. Explicit Nonclaims

This plan initially claims none of the following:

- a full cubical type theory;
- degeneracies, connections, reversals, diagonals, symmetries, or Kan filling;
- a category of all cubes in variable dimension;
- equivalence with `Functor(WalkingArrow^n,C)` or a Gray tensor power;
- equivalence with Herbelin--Ramachandra semicubical sets;
- a fully symmetric treatment of cubical coordinates;
- a primitive `homdc_` or `homdc_int` before transparent feasibility is
  measured;
- a displayed `homd_con_int` mirror without a failing whole consumer;
- removal of historical strict functoriality/naturality cuts; or
- global normalization, confluence, canonicity, or consistency.

## 9. Execution Ledger

| Row | State | Deliverable and acceptance boundary |
| --- | --- | --- |
| `CUB-00` | complete | Audited the active hom, displayed-hom, product, and profunctor owners; corrected the direct `homd_int(Unit_prof)` proposal to a twisted cell; selected the cross-corner formula, curried input, one-op variance, branch/worktree, baseline, validation policy, and this living plan. The core `emdash3_2.lp` baseline checked green; the unnecessary registered extension sweep was interrupted under the standing aggregate-avoidance policy after several unchanged predecessors also passed. |
| `CUB-01` | complete | Promoted the transparent `homdc_source_func`, `homdc_target_func`, `homdc_`, and readable fibre observation in `emdash3_2_cubical_dependent_hom.lp`. Existing `fib_cov_tapp0_func`, the outer `fapp1_func`/`tapp0_func`/object-evaluation ladder, and `hom_con_int` supply the whole classifier and typed generic cross-fibre computation. The focused source and reviewer are green; the module adds six transparent symbols and no rule, unifier, or primitive filler. |
| `CUB-02` | complete | The transparent `hom_int(id_C)` specialization computes to `Hom_{Hom_C(x1,y2)}(b o u,v o a)`. The reviewer checks the whole profile, typed generic and concrete point computations, retained hom actions in both side-arrow coordinates, and noncollapse against the differently typed unit-profunctor cell `b o u_tw o a ==> v_tw`. |
| `CUB-03` | complete with precise prerequisite | The active `homd_int` cascade handles a selected `FF`, but there is no whole `homd_parameter_func` mapping `FF` to `homd_int(FF)` with displayed-transfor action. That exact owner is required before all four endpoints can vary in one derived `homdc_int`; `tdapp1_int_func_transfd` has a different source/target and is not a substitute. The existing fixed-boundary `homdc_` already retains hom actions in both side-arrow coordinates. No displayed `homd_con_int` consumer arose for the selected orientation. |
| `CUB-04` | complete at the fixed-boundary scope | `emdash3_2_cubical_square_total.lp` totalizes first the contravariant `b` family and then the covariant `a` family. Objects are constructor-visible `(a,(b,alpha))`. Top and the two fixed vertical faces are whole functors; bottom is a whole Pi section over the stable Sigma-projection pullback. All four object observations compute. The generic `sigma_proj1_family_funcd` and its one component beta are the only new infrastructure; there is no flat cubical record, filler rule, or unifier. |
| `CUB-05` | complete at the bounded fixed-boundary scope | For `theta` in the next hom between two square objects, ordinary source/target provide two faces and `homdc_cube_{top,bottom,left,right}_face` provide four more. Top is ordinary whole action, bottom retains the dependent Pi action, and the fixed left/right faces compute to identities. This is a genuine six-face bounded cube with two explicitly degenerate sides, not a claim of fully varying nondegenerate cubical endpoints. The warning-enabled owner-position probe adds no probe-local warning. |
| `CUB-06` | deferred | Add semicubical face codes, arbitrary dimension, walking-arrow/Gray comparison, or Herbelin--Ramachandra comparison only after `CUB-05` identifies the native semantic recursion. |
| `CUB-07` | deferred | Add the groupoidal-source/bicubical specialization only after the fully directed cross-corner owner is stable; compare its reflexive-source restriction with the simplicial fixed-apex construction. |
| `CUB-DOC-8` | complete with explicit health deferral | Foundations, current status/SOP, canonical syntax, `emdash2/README.md`, AGENTS authority/source registries, report index, both focused reviewers, and the check catalog are synchronized. Report-header, active-reference, book-evidence, catalog, and diff checks are green. A single `make health` attempt unexpectedly invalidated the whole registry cache and became a repo-wide sweep; it was stopped at direct user instruction after both new sources passed in 2.676s/2.726s and the unchanged aggregate `emdash3_2_checks.lp` hit the existing 90-second ceiling. It changed no tracked health report. Health refresh is therefore intentionally deferred to a future release boundary or a future selected-file/additive health mode; it is not rerun for this scoped checkpoint. |
| `CUB-CLOSE-9` | complete | The two implementation tranches are checkpointed at `7ec3a9d` and `f61c7a3`; final documentation is checkpointed separately. Focused source/reviewer checks, the warning-enabled owner probe, extension LHS audit, report/header/reference/book-evidence/catalog checks, and exact diff hygiene are green. `CUB-06`, `CUB-07`, full endpoint variation, and health refresh have named prerequisites rather than hidden claims. No push, merge, publication, tag, PR, history rewrite, branch deletion, or worktree removal was performed. |

## 10. Validation And Git Policy

- Keep each Lambdapi command bounded to 90 seconds.
- Use ignored owner-position probes first.
- For definition-only experiments, run the focused probe/source/reviewer and
  the smallest active-import diagnostic; do not rerun broad aggregates for
  reassurance.
- Compare warnings when adding any stable head, rewrite, or unifier; warnings
  are diagnostic evidence, not an automatic veto.
- Validate every unifier through typed `eq_refl`, never conversion-only
  `assert`.
- Use `_` on inferred rule-LHS slots unless a documented discriminator or
  subject-reduction/performance guard is measured.
- Preserve a relevant negative/noncollapse consumer.
- Run catalog, health, examples, or CI only at the affected integration
  boundary and only when their omission would leave changed registered
  behavior unclassified.
- The user authorizes the dedicated branch/worktree and SOP-compliant local
  checkpoint commits after bounded green tranches.
- Do not push, merge, publish, tag, create a PR, rewrite history, delete the
  branch, or remove the worktree without separate explicit authorization.

## 11. Persistent-Goal Launch Prompt

> Continue the emdash v3.2 cubical-dependent-hom implementation in
> `/home/user1/emdash1-cubical-hom-v1` on branch
> `goal/cubical-dependent-hom-v3.2`, delegating the exact mathematics,
> sequencing, evidence, exclusions, validation, Git discipline, and
> completion boundary to
> `emdash2/reports/REPORT_EMDASH_V3_2_CUBICAL_DEPENDENT_HOM_PLAN_2026-08-23.md`
> and its active authority chain. Begin from baseline
> `689f41c057f5eeee5fd82486fcad79acd136bdfa`. Work one dependency-ready row
> at a time, starting with the transparent `CUB-01` cross-corner classifier;
> do not postulate a filler, primitive owner, rewrite, or unifier before the
> transparent construction and identity-Hom consumer are measured. Keep
> every Lambdapi invocation bounded to 90 seconds and eagerly avoid broad
> registered or repository aggregates unless omission blocks classification
> of genuinely changed behavior. The user authorizes SOP-compliant local
> checkpoint commits on this dedicated branch after each bounded green
> tranche and synchronized ledger. Do not push, merge, publish, tag, create a
> PR, rewrite history, delete branches, or remove worktrees. Do not mark the
> goal complete until every scoped row is implemented, rejected with durable
> evidence, or explicitly deferred behind a concrete prerequisite and all
> affected authorities and proportional gates are synchronized.

This launch prompt is retained as historical recovery text. The bounded goal
has completed; a later goal must explicitly reopen either
`homd_parameter_func`, variable-endpoint cubical totals, semicubical codes, or
the groupoidal-source specialization rather than silently continuing this
closed ledger.

## 12. Completion Definition

The bounded goal is complete when:

1. the fixed-endpoint `homdc_` classifier has a typed whole owner and its
   cross-corner formula is checked;
2. the `hom_int(id_C)` instance computes to
   `Hom_{Hom_C(x1,y2)}(b o u,v o a)` and remains distinct from the differently
   typed unit-profunctor cell;
3. whole endpoint internalization either retains a next action or records an
   exact, consumer-backed stable-head prerequisite;
4. a native square has four whole face projections;
5. a bounded next-action consumer either exposes six cube faces or records
   the precise mathematical/LF obstruction;
6. no combinatorial cubical claims exceed the checked native semantics;
7. documentation, examples, catalog/health evidence required by the actual
   promoted diff are synchronized;
8. every noncompleted row is explicitly deferred behind a named consumer or
   prerequisite; and
9. the dedicated branch is clean at reviewed local checkpoints.

## 13. Closeout Evidence And Deferred Boundary

Promoted sources and reviewers:

- `emdash3_2_cubical_dependent_hom.lp` and
  `examples/cubical_dependent_hom.lp`;
- `emdash3_2_cubical_square_total.lp` and
  `examples/cubical_square_total.lp`.

Focused validation completed under the uniform 90-second target ceiling:

- both promoted sources check directly;
- both reviewers check directly;
- the warning-enabled owner-position square-total probe is green and adds no
  probe-local warning;
- `audit_rule_lhs.py --strict emdash3_2_cubical_square_total.lp` reports zero
  unreviewed slots;
- report-header lint, active-reference lint, book-evidence check, check-catalog
  strict check, source-TOC check, and `git diff --check` pass.

The interrupted health refresh is negative scope evidence, not a mathematical
failure. It expanded beyond the changed files, while the new sources had
already passed. It also found the unrelated registered aggregate
`emdash3_2_checks.lp` exceeding the same 90-second ceiling. No timeout was
raised for either new source, no report was rewritten, and no health claim is
inferred. A future release may refresh that report once the aggregate itself
fits the policy or
the tool supports additive selected-file evidence.

The principal mathematical continuation remains:

```text
homd_parameter_func(D,E)[FF] = homd_int(FF)
```

with a whole displayed-transfor action. That owner is the exact prerequisite
for replacing the present fixed-vertical-boundary total by a fully varying
nondegenerate cubical endpoint telescope. Semicubical combinatorics and the
groupoidal-source specialization remain later consumers, not retroactive
requirements of the bounded square/cube result.
