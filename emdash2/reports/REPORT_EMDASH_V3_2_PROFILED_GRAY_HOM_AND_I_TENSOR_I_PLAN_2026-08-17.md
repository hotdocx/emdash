# Emdash v3.2 Profiled Gray Hom And `I Tensor I` Plan

Date: 2026-08-17 (America/Toronto)

Plan-ID: `PROFILED-GRAY-HOM-I-TENSOR-I-V3.2`

Parent: `REPORT_EMDASH_V3_2_INTERNAL_LAXITY_AND_GROUPOIDAL_REALIZATION_CONTINUATION_PLAN_2026-08-17.md`, row `ILGR-GRAY-1`

Depends-On: active `emdash3_2.lp`; completed internal-laxity rows
`ILGR-LAX-1` through `ILGR-LAX-5`; completed path realization
`ILGR-GRPD-1`; active `Join_cat`, terminal-category, product, evaluation,
curry/uncurry, and profunctor owners; the current Foundations, SOP, and
canonical-syntax reports

Supersedes: no completed implementation plan. It reopens only
`ILGR-GRAY-1` through the bounded profiled right-closure and `I tensor I`
consumer selected here.

Side-Task-Ledger: `GRAY-00`, `GRAY-01`, `GRAY-02`, `GRAY-03`, `GRAY-04`,
`GRAY-05`, and `GRAY-CLOSE-1`

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`; selected profiled-Gray continuation
response `01a011a0-540c-74e2-8e19-f0bfaeb599d6`

Infinity-Codex-Decision-Responses: response `0043`, archived at
`/home/user1/emdash1/emdash2/tmp/ai-responses/sessions/2026-08-14_019ffe392eb9/responses/0043_2026-08-17T21-34-44Z_01a011a0-540c-74e2-8e19-f0bfaeb599d6.md`.
Active code and SOP, then this plan and its parent decision record, outrank
the archive.

Baseline: local checkpoint `ef43ef4`, including computational truncation and
Circle connectedness at `998c60f`

Worktree: `/home/user1/emdash1-groupoidal-circle-v1`

Branch: `goal/profiled-gray-hom-v3.2`

Status: active bounded implementation plan. `GRAY-00` through `GRAY-04` are
complete; `GRAY-05` is the selected next row. Local green checkpoint commits
are authorized by the user; push, merge, publication, release, history
rewrite, branch deletion, and worktree removal are not authorized.

Checkpoints: completed `GRAY-01` semantic tranche
`9222dad7caf71741d0811505aeebef033f404059`; completed `GRAY-02` walking-arrow
tranche `1caf642a3b99d4699becac3a1d90e26f4e58c4b1`; completed `GRAY-03`
right-closure semantic tranche
`37a5ede9cdfeaea10f0aa2d6dfbbbdacc7e3a957`

## Objective

Implement one selected, computationally inspectable **right-closed Gray
slice** sufficient to demonstrate that the shared emdash internal-action
calculus can support a strict-object/lax-arrow internal hom and recover the
directed interchanger of the walking square.

The tranche is deliberately smaller than a Crans--Gray monoidal structure.
It must establish the following chain without duplicating the ambient
functor/transfor tower:

```text
computational strict-functor code and stable decoder
    -> GrayHom profile category
    -> whole inclusion into the ambient Functor_cat
    -> derived walking arrow I = Join(1,1)
    -> one chosen Gray tensor/right-closure transpose
    -> coevaluation of I tensor I
    -> interchanger projected from the existing whole laxity action
    -> one retained next action.
```

The result may be called a profiled one-sided Gray-closed slice. It must not be
called the full Crans--Gray tensor until the mirror closure, biclosed
naturality, and monoidal coherences exist.

## Scope Boundary

### In scope

- a primitive `StrictFunctorData(B,C)` code sort with a stable
  `strict_functor_carrier` decoder into the shared ambient `Functor`;
- one selected identity code, a whole carrier equality to `id_func`, and
  profile-local compositor computation at the active `fdapp1_int_cell` owner;
- a selected `GrayHom_oplax(B,C)` (name and orientation to be confirmed by
  the first typed consumer) whose objects are strict functors and whose homs
  reuse the existing ambient `Transf_cat` tower;
- one whole inclusion into `Functor_cat(B,C)` with computing object and hom
  action;
- a curated walking-arrow interface transparently derived from
  `Join_cat(Terminal_cat,Terminal_cat)`, including two endpoints and its
  generator projected from `join_cross_transf`;
- one tensor category owner, one right curry/uncurry pair, beta/eta boundary,
  and evaluation/coevaluation needed by the selected consumer;
- the four objects and two coordinate arrow families of `I tensor I`;
- a named interchanger that is an alias or stable projection of the existing
  `functord_laxity_transf` / `fapp1_compositor` action, never an independent
  square axiom; and
- one next-action observation showing that the interchanger owner remains
  iterable.

### Explicitly out of scope

- the mirror left closure and full biclosedness;
- a proof of the complete Crans--Gray monoidal structure;
- tensor associativity, unitors, symmetry, or braiding;
- a wholesale migration of the current global strict functoriality and
  naturality cuts;
- a second functor/transfor/modification hierarchy;
- generic groupoidification or its free-coherent-inversion construction;
- a generic walking-category or directed-HIT schema;
- a complete simplicial/globular/associahedral coherence theorem;
- book, article, TypeScript, npm, browser, GetPaidX, Arrowgram, deployment,
  and publication work; and
- long repository-wide aggregates except where an actual closeout boundary
  cannot be validated proportionally.

## Settled Architectural Decisions

### 1. Computational strictness is a decoded sort, not a path property

The first probe corrected the preliminary Sigma-package sketch. In the
univalent setting, an internal equality between the two functoriality
endpoints induces an invertible categorical cell through `path_to_hom`.
Requiring an arbitrary ambient compositor to equal that cell describes a
canonical or path-induced **pseudo** constraint; it does not make the
endpoints judgmentally identical or the compositor an identity. Calling that
boundary `IsStrictFunctor` would therefore overstate what it computes.

The selected computational boundary is instead syntactic and sorted:

```text
StrictFunctorData(B,C) : Grpd

strict_functor_carrier
  : StrictFunctorData(B,C) -> Functor(B,C).
```

The decoder remains a stable head. The active generic compositor of a decoded
strict code reduces to identity at its existing `fdapp1_int_cell` owner. The
current prototype's global strict cuts already identify its formal endpoints;
when those cuts are eventually migrated, their strict specialization must be
re-homed at this same decoder shape. No redundant endpoint unifier is added in
this tranche.

This is analogous to the primitive sorted `NType_cat` boundary: computation
belongs to the code/decoder interface, while an eventual extensional
realization comparing strict codes with ambient functors plus laws can be
added separately. A generic constructor from arbitrary `F` and a path-valued
witness is deliberately absent here, because reducing such a constructor's
decoder would erase the strict discriminator.

The selected identity code keeps the decoder head and carries a whole equality
of its decoded functor with `id_func`. A direct decoder beta was probed and
rejected because it races the strict-compositor rule in three reduction
positions; duplicate constructor-specific `fapp0`/`fapp1` rules were also
rejected as competing generic owners.

### 2. `GrayHom` is a selected profile, not an alias of `Functor_cat`

The public shape is:

```text
GrayHom_oplax(B,C) : Cat

Obj(GrayHom_oplax(B,C))
  --> StrictFunctorData(B,C)

Hom_GrayHom_oplax(X,Y)
  --> Transf_cat(strict_carrier(X),strict_carrier(Y)).
```

Identity and composition delegate to `Functor_cat(B,C)`. The homs therefore
retain ordinary transformations, modifications, and all subsequent iterated
homs already owned by the kernel. The category heads remain distinct: there
is no broad `GrayHom == Functor_cat` unification rule.

### 3. Strict and lax share the ambient action machinery

The current prototype globally identifies several functoriality/naturality
endpoints, but it does not reduce the newly exposed laxity cell terms to
identities. The profile therefore records which functor objects are selected
as strict while retaining the shared ambient action and higher-cell calculus.

Constructor-specific identity specialization is allowed only at a stable
profile carrier or at a later Gray-curry constructor whose strictness is a
genuine discriminator. It must not become a global collapse of every
`fapp1_compositor`.

This bounded goal does **not** remove the historical global endpoint cuts.
Their migration belongs to a later consolidation task that re-homes endpoint
computation at strict/profile constructors and audits existing consumers in
stages. Until that migration, this tranche may claim computational
discrimination of the retained laxity cell, but not ambient endpoint
non-collapse or a completed generic lax classifier.

### 4. The interval reuses the active directed join

The audit corrected the preliminary “missing walking arrow” assumption. The
active kernel already states that

```text
I := Join_cat(Terminal_cat,Terminal_cat)
```

is a walking arrow. What is missing is only a curated direct interface. The
two endpoint objects are evaluations of `join_fst_func` and `join_snd_func` at
`Terminal_obj`. The generating arrow must be projected from the existing
whole `join_cross_transf` at the terminal base pair and terminal fibre object.
No second primitive category or unrelated generator is allowed.

If that component cannot presently be observed as an ordinary `Hom`, the row
must identify the exact missing generic projection and probe it at its owner.
It must not fill the gap with a standalone arrow constant.

### 5. Select the right closure first

The intended semantic orientation is provisionally

```text
StrictMap(GrayTensor(A,B),C)
  ~= StrictMap(A,GrayHom_oplax(B,C)).
```

The exact `lax`/`oplax` name is accepted only after the `I tensor I`
interchanger direction is checked. If the computed boundary has the mirror
orientation, rename the selected profile rather than adding a pointwise
reversal rule.

Curry/uncurry must expose a whole higher action and beta/eta comparisons.
Coevaluation is `gray_curry_R(id)`, and evaluation is
`gray_uncurry_R(id)`. An opaque tensor plus unrelated square is not an
acceptable implementation.

### 6. The square consumes extracted laxity

For the curried identity on `I tensor I`, the outer generating arrow is a
lax/oplax transfor between two strict inner functors. Applying its whole
internal action to the inner generator must yield the interchanger. A readable
`gray_interchanger` name may be a transparent alias or a stable owner with a
runtime projection to this term. It must not postulate the same 2-cell
independently.

The first square milestone checks four distinct constructed object terms, the
two boundary directions, both composite endpoints, orientation, and one next
hom action. It does not claim a complete cube or all-dimensional theorem.

## Anti-Duplication Inventory (`GRAY-00`)

Completed on 2026-08-17 before semantic edits:

- `Functor_cat`, `Transf_cat`, identity, composition, evaluation, product,
  and iterated homs are active and reusable;
- `fapp1_compositor`, `tapp1_post_laxity_transf`,
  `tapp1_pre_laxity_transf`, and `functord_laxity_transf` already expose the
  required whole laxity provenance;
- `curry_func_func` and `uncurry_func_func` are useful Cartesian scaffolds but
  do not own beta/eta equivalence and must not be silently reinterpreted as
  Gray closure;
- no active `IsStrictFunctor`, `StrictFunctorData`, `StrictMap`,
  `GrayHom_*`, `GrayTensor`, or Gray curry/uncurry owner exists;
- no curated `WalkingArrow_cat` name exists, but `Join_cat(1,1)` and its
  internally natural cross cell already provide the mathematical interval;
- the sheaf and `NType_cat` modules demonstrate the selected-realization
  category pattern; and
- the clean baseline is `ef43ef4` on the dedicated worktree/branch above.

The bounded active-kernel baseline

```text
timeout 90s lambdapi check emdash3_2.lp
```

passes in approximately 2.24 seconds. Existing warnings are diagnostic
baseline evidence; no new warning conclusion is inferred from that quiet
typecheck alone.

## Execution Ledger

| Row | Status | Deliverable and acceptance boundary |
| --- | --- | --- |
| `GRAY-00` | complete | Git/SOP recovery, authority review, anti-duplication inventory, clean child branch, and bounded kernel baseline. The interval is corrected from “missing object” to “missing curated projection surface” over active `Join_cat(1,1)`. |
| `GRAY-01` | complete | `emdash3_2_gray_profiles.lp` provides the primitive strict-functor code/decoder, selected identity code/path, profile-local compositor-to-identity computation, `GrayHom_oplax`, and its whole inclusion. The registered reviewer and central diagnostics cover object/Hom/identity/composition, inclusion object/hom action, retained next hom, rigid unprofiled non-collapse, and arbitrary-functor rejection. Focused source, reviewer, and central checks pass with subject reduction; the strict LHS audit is zero; the accepted warning inventory is `1130/159`, exactly `+18/0` over `1112/159`; and the regenerated strict catalog has 2,121 checks across 102 areas with zero unclassified checks. |
| `GRAY-02` | complete | `emdash3_2_walking_arrow.lp` transparently defines `WalkingArrow_cat` as `Join_cat(1,1)`, derives its two distinct endpoints from the join inclusions, and obtains the generator as the terminal component of the fibre of `join_cross_transf`. The whole fibre functor and its `fapp1_func` next action are retained. The focused source/reviewer and affected central diagnostics pass; no rule or unifier is added; the strict LHS audit is zero; the source warning inventory is unchanged at `1112/159`; and the strict catalog has 2,131 checks across 103 areas with zero unclassified checks. |
| `GRAY-03` | complete | `emdash3_2_gray_right_closure.lp` provides one opaque `GrayTensor_R` category, computationally strict whole curry/uncurry functors between the profiled Hom categories, whole beta/eta paths assembled as the existing `OmegaEquivAlong Cat_cat`, their object evaluations, and coevaluation/evaluation derived at strict identity codes. The rule-free source/reviewer/central targets pass; warning evidence remains exactly `1130/159`; the strict LHS audit is zero; and the catalog has 2,145 checks across 104 areas with zero unclassified checks. The right-closure typing is fixed, while the `oplax` orientation name remains provisional until `GRAY-05` observes the interchanger. |
| `GRAY-04` | complete | `emdash3_2_gray_walking_square.lp` derives the four `I tensor I` vertices and both coordinate arrow families from coevaluation. Inner edges retain whole Terminal-indexed generator owners; outer edges are two whole component evaluations of one coevaluation-generated transformation. All six pairwise vertex non-collapses and the concrete Cartesian non-collapse are checked. |
| `GRAY-05` | selected next | Project the directed interchanger from the active whole laxity owner, identify its two boundary composites, and retain one next hom action. No independent square axiom or capped-only facade. |
| `GRAY-CLOSE-1` | pending | Synchronize source/example ownership, master/child ledgers, Foundations/SOP/canonical syntax, report index, checks/catalog/health required by the actual diff, and local green checkpoints. Record exclusions and next consumer. |

## First Experiment (`GRAY-01`)

Hypothesis:

> A selected category with decoded strict-functor codes and ambient
> `Transf_cat` homs can reuse the complete existing higher-cell tower while a
> whole inclusion computes on both objects and hom categories.

Smallest owner-position experiment:

1. define the strict-functor code sort and stable decoder in a new extension
   importing only the active kernel;
2. define the selected Gray-hom category with `Obj`, `Hom_cat`, `id`, and
   `comp_fapp0` delegating to the ambient functor category;
3. define a whole inclusion whose object projection is the stable strict
   carrier and whose hom action is the identity functor on the reused
   `Transf_cat`;
4. construct an identity strict code, retain a whole carrier equality to the
   ambient identity, and check its generic compositor through the selected
   decoder rule;
5. assert the next hom category remains the ambient modification category;
   and
6. reject an arbitrary ambient functor where a strict code is
   required.

Reject or repartition the hypothesis if the facade needs broad category-head
unification, duplicates `Transf_cat`, erases the decoder discriminator,
creates a subject-reduction failure, or cannot preserve the next hom action.

### Initial feasibility result — 2026-08-17

The superseding disposable probe
`tmp/probes/gray_computational_profile_probe.lp` is quiet-green and
warning-green and establishes the basic architecture before promotion:

- an internal path-valued property of an arbitrary ambient functor is only a
  path-induced pseudo boundary; the computational strict boundary is a
  primitive code with a retained decoder head;
- the generic compositor of that decoded head reduces to identity at the
  existing `fdapp1_int_cell` owner, and a rigid unprofiled ambient functor does
  not acquire that reduction;
- the selected identity code retains its discriminator and has a whole carrier
  equality to `id_func`; a direct decoder beta and duplicate capped action
  rules were rejected after measured reduction-order/warning probes;
- the selected category reuses `Transf_cat` for its Homs and every next hom,
  while its inclusion has a computing whole hom-functor action;
- an arbitrary ambient functor is rejected where a strict code is required;
  and
- the walking interval, its two endpoints, its ordinary generator, and one
  next action all derive from `Join_cat(1,1)` and the fibre component of
  `join_cross_transf`; no new interval primitive is needed.

The strict LHS audit reports zero unreviewed reconstructible compound slots.
Against the active-kernel `1112/159` warning baseline, the selected candidate
is `1130/159`, an exact `+18/0`: 17 interactions are the established
selected-category identity/composition delegation family and one is the whole
inclusion's generic evaluator interaction. The strict compositor rule itself,
the identity code/path, and the walking-interval derivation add no warning.
Before promotion the 18 selected-category interactions remain diagnostic
rather than automatic vetoes. The earlier
`tmp/probes/gray_profile_facade_probe.lp` remains historical probe evidence
only and must not be promoted. The initial
result is feasibility evidence, not yet an accepted warning verdict or active
source change.

### Promoted `GRAY-01` result — 2026-08-17

The probe architecture is now promoted in
`emdash3_2_gray_profiles.lp`, with its reviewer in
`examples/gray_profiles.lp` and seven classified central diagnostics in
`emdash3_2_checks.lp`.

The decisive boundary is computational rather than merely propositional:

- `StrictFunctorData(A,B)` is a primitive code sort;
- `strict_functor_carrier` is a retained decoder head into the shared ambient
  `Functor(A,B)` classifier;
- only a decoded strict code makes the existing extracted
  `fapp1_compositor` reduce to identity at `fdapp1_int_cell`;
- a rigid ordinary ambient functor retains its compositor, while an arbitrary
  ambient functor is rejected as a `GrayHom_oplax` object; and
- `GrayHom_oplax` reuses `Transf_cat` for every hom and subsequent iterated
  hom, so no parallel transformation/modification hierarchy was introduced.

Identity and composition are diagnosed as terms in the decoded ambient homs,
following the established selected-category pattern of `NType_cat`. They are
not asserted as literal cross-category term equalities: the two category heads
remain intentionally distinct, and the whole inclusion is the canonical
typed observation surface.

The focused source, reviewer, and affected central diagnostic targets pass
with ordinary subject-reduction checking. The strict inferred-slot audit has
zero unreviewed candidates. The warning-enabled owning source is exactly
`1130` critical pairs and `159` replaceable-pattern diagnostics, an accepted
`+18/0` over the active `1112/159` baseline: 17 are the established
selected-category identity/composition delegation family and one is the whole
inclusion evaluator. The strict catalog is regenerated at 2,121 checks in 102
areas, with zero unclassified checks. Health/CI replacement remains deferred
to `GRAY-CLOSE-1`; no repository-wide aggregate was run for this intermediate
row.

The bounded semantic tranche is locally checkpointed at `9222dad`; this
ledger entry records that immutable recovery anchor without widening the
validated scope.

### Promoted `GRAY-02` result — 2026-08-17

The walking interval is now a transparent derived interface in
`emdash3_2_walking_arrow.lp`, with its reviewer in
`examples/walking_arrow.lp`. It adds no second interval primitive and no
standalone generating arrow:

```text
WalkingArrow_cat
  := Join_cat(Terminal_cat,Terminal_cat)

walking_arrow_src
  := join_fst_func[Terminal_obj]

walking_arrow_tgt
  := join_snd_func[Terminal_obj]

walking_arrow_generator_func
  := Fibre_func(join_cross_transf, (Terminal_obj,Terminal_obj))

walking_arrow_generator
  := walking_arrow_generator_func[Terminal_obj].
```

The whole generator functor is intentionally public. Its hom action
`walking_arrow_generator_next_func` is the literal `fapp1_func` projection,
so the future `I tensor I` consumer is not forced to reconstruct higher data
from a capped arrow. Positive diagnostics lock both projection steps to
`join_cross_transf`; negative diagnostics keep the endpoints distinct and
reject a Cartesian-product reinterpretation.

The focused source and reviewer pass, as does the affected central diagnostic
target. Because this extension is transparent and rule-free, its
warning-enabled source has exactly the active-core `1112/159` inventory. The
strict LHS audit is zero. Ten new central checks regenerate the strict catalog
at 2,131 checks in 103 areas, with zero unclassified checks. Health/CI remains
reserved for `GRAY-CLOSE-1`; no all-source or all-example aggregate was run.

The bounded walking-arrow tranche is locally checkpointed at `1caf642`; this
ledger entry records that recovery anchor without widening the row.

### Promoted `GRAY-03` result — 2026-08-17

The one-sided right-closure boundary is now promoted in
`emdash3_2_gray_right_closure.lp`, with its reviewer in
`examples/gray_right_closure.lp`. The implementation reuses the existing
strict-code and equality-valued omega-equivalence owners rather than adding a
second map or equivalence hierarchy:

```text
GrayRightSource(A,B,C)
  := GrayHom_oplax(GrayTensor_R(A,B),C)

GrayRightTarget(A,B,C)
  := GrayHom_oplax(A,GrayHom_oplax(B,C)).
```

`gray_curry_R_func` and `gray_uncurry_R_func` decode selected
`StrictFunctorData` codes between these two category heads. They are therefore
whole functors with the generic iterable `fapp1_func` action, while their
objects remain strict-functor codes. Two equality-valued whole cancellation
paths assemble `gray_right_closure_omega : OmegaEquivAlong Cat_cat`; both
selected inverse projections compute to the same uncurry functor. Evaluating
the whole paths derives object-level beta and eta comparisons without adding
judgmental `uncurry(curry(H))` or `curry(uncurry(K))` folds.

Coevaluation and evaluation are not independent operations:

```text
gray_coevaluation_R_data(A,B)
  := gray_curry_R(strict_identity_data(GrayTensor_R(A,B)))

gray_evaluation_R_data(B,C)
  := gray_uncurry_R(strict_identity_data(GrayHom_oplax(B,C))).
```

Their public functors are the existing strict decoder applied to these data.
This gives the exact introduction/elimination surface required by the next
`I tensor I` consumer while keeping the tensor distinct from `Product_cat`
and the profiled target distinct from nested ambient `Functor_cat`.

The source, focused reviewer, and affected central diagnostic target pass
with ordinary subject reduction. The extension adds no rule or unifier, so
its warning-enabled source remains exactly `1130` critical pairs and `159`
replaceable-pattern advisories inherited from `emdash3_2_gray_profiles.lp`.
The strict LHS audit reports zero unreviewed candidates. Fourteen central
diagnostics regenerate the strict catalog at 2,145 checks across 104 areas,
with zero unclassified checks. Health/CI remains reserved for
`GRAY-CLOSE-1`; no all-source, all-example, or repository-wide aggregate was
run.

This row fixes the typed **right** closure. It does not yet settle whether the
chosen higher-cell direction deserves the `lax` or `oplax` name; that label is
confirmed only when `GRAY-05` projects the oriented interchanger.
The bounded semantic tranche is locally checkpointed at `37a5ede`; this
ledger entry records that recovery anchor without widening the row.

### Promoted `GRAY-04` result — 2026-08-17

The walking-square boundary is now promoted in
`emdash3_2_gray_walking_square.lp`, with its reviewer in
`examples/gray_walking_square.lp`. No object or arrow of the tensor is
postulated independently. Instead, right coevaluation is evaluated at the
outer source and target to obtain two strict inner codes, and decoding those
codes gives two inner functors

```text
I -> GrayTensor_R(I,I).
```

Evaluating the two inner functors at the two walking-arrow endpoints gives
the four vertices `gray_square_obj00`, `gray_square_obj01`,
`gray_square_obj10`, and `gray_square_obj11`. The two inner-coordinate edge
owners are whole composites

```text
Terminal_cat
  -> Hom_I(0,1)
  -> Hom_GrayTensor(F_i(0),F_i(1)),
```

so their capped arrows are generic `fapp1_fapp0` projections and their higher
action remains available. Applying the whole coevaluation functor to the
outer generator produces one transformation between the inner functors. The
two outer-coordinate arrows are its components through the existing whole
`tapp0_func` evaluators, not separately declared edges.

The source, reviewer, and affected central diagnostics pass with ordinary
subject reduction. The source is transparent and rule-free, so its
warning-enabled inventory is exactly the inherited `1130/159`, with no local
warning. The strict LHS audit remains zero. Twenty-three new central checks
establish both whole-owner routes, all six pairwise vertex non-collapses, and
the concrete distinction from `Product_cat`; the regenerated strict catalog
has 2,168 checks across 105 areas and zero unclassified checks. Health/CI
replacement remains deferred to `GRAY-CLOSE-1`, and no all-source,
all-example, or repository-wide aggregate was run.

This row supplies only the typed square boundary. The orientation name and
the nonidentity interchanger remain owned by `GRAY-05`, which must project
them from the existing whole laxity action and retain one next hom action.

## Validation Policy

All Lambdapi commands are bounded to 90 seconds per target.

During each row:

1. use a disposable focused probe and, for any rule, a full-file copy at the
   intended owner position;
2. add typed positive and relevant negative/non-collapse consumers;
3. run the smallest direct source and reviewer checks;
4. compare warnings against the exact owning baseline and classify every
   delta by owner;
5. run strict LHS/subject-reduction audits for rules;
6. update the catalog only when durable assertions change; and
7. refresh health/CI only at a meaningful synchronized closeout boundary.

Do not rerun `check:all`, root TypeScript aggregates, print/book gates, or an
all-target kernel aggregate for reassurance. Carry forward the exact
176-target green health evidence from the truncation checkpoint until this
tranche changes maintained source/example content enough to require one final
replacement snapshot.

Warnings locate interactions but are not automatic vetoes. Runtime rules are
reserved for selected normal forms; proof-time comparisons must use narrowly
typed two-rigid-head `unif_rule`s and typed `eq_refl` validation. LHS inferred
slots follow the nested minimization SOP.

## Git And Recovery Policy

- Continue only in `/home/user1/emdash1-groupoidal-circle-v1` on
  `goal/profiled-gray-hom-v3.2`.
- Treat `ef43ef4` as a comparison/backtracking anchor, never as permission to
  reset descendants.
- Before each continuation, inspect all worktrees, current branch/HEAD,
  staged and unstaged state separately, ancestry, this plan, and the parent
  row.
- Commit only a bounded green tranche after synchronizing this ledger and
  reviewing the exact staged diff plus `git diff --cached --check`.
- Prefer correcting commits; do not amend, rebase, reset, or hide failed
  experiments.
- Do not push, merge, publish, release, remove the worktree, or delete the
  branch without separate user authorization.

## Persistent Goal Objective

Continue `EMDASH-V3.2-PROFILED-GRAY-HOM-AND-I-TENSOR-I` by following this
living plan and its parent master plan. Select only the next dependency-ready
row, preserve the bounded exclusions, use focused probes before promotion,
keep every Lambdapi target under 90 seconds, avoid long aggregate reruns unless
they are genuinely required for closeout, synchronize the ledger at every
decision, and make only user-authorized local green checkpoint commits in the
dedicated branch/worktree. Complete the goal only when every scoped row is
implemented, rejected with durable evidence, or explicitly deferred behind a
concrete prerequisite.
