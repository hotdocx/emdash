# EMDASH v3.2 Path Action And Equivalence Compatibility Retirement Plan

Date: 2026-07-19
Last reviewed: 2026-07-20
Plan-ID: EMDASH-V3-2-PATH-ACTION-AND-EQUIVALENCE-COMPATIBILITY-RETIREMENT-2026-07-19
Depends-On: REPORT_EMDASH_V3_2_WALKING_ENDOMORPHISM_DIRECTED_HIT_PLAN_2026-07-17; REPORT_EMDASH_V3_2_EQUALITY_VALUED_OMEGA_EQUIVALENCE_REREDESIGN_PLAN_2026-07-17; REPORT_EMDASH_V3_2_OBSERVATIONAL_EQUALITY_TRUNCATION_UNIVALENCE_REDESIGN_PLAN_2026-07-13; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26; EMDASH_FOUNDATIONS; emdash3_2.lp; emdash3_2_nat_arithmetic.lp; emdash3_2_walking_end_hit.lp; emdash3_2_eq1_hom_action.lp; emdash3_2_eq1_evidence_property.lp; emdash3_2_checks.lp
Supersedes: no whole report; reopens the deferred `EVOGJ-OBSACTION-SCOPE` functor-view refactor and the optional legacy-compatibility retirement boundary, while preserving the completed native-EQ1 and WalkingEnd results
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-user-requested-path-action-and-compatibility-review-2026-07-19
Infinity-Codex-Decision-Responses: current-session-review-response-2026-07-19; current-session-canonical-action-correction-2026-07-20; no archived logical ID is required to interpret this plan
Status: **COMPLETE 2026-07-20 — P0–P9 remain completed historical phases; P10 supersedes P6 and deletes the legacy compatibility closure and clients, P11 supersedes P7 and makes the collision-free native API unsuffixed, and P12 synchronizes authorities and passes the complete proportional gate**
Implementation starting baseline and review provenance: `2444c9d406fc3d201602ace7af5105c20c241680`
Initial worktree state: clean, with staged and unstaged diffs both empty
Initial bounded baseline: `EMDASH_TYPECHECK_TIMEOUT=60s make check` passes

## Status And Authority

This is the living implementation and decision ledger for two related but
deliberately separate cleanup tracks:

1. retiring registered observational action in favor of the canonical
   internal `Path_cat_func`/`path_map_func` action, with no parallel selected-
   action registry and with dependent transport owned directly by `eq_apd`
   unless a future honest displayed construction is adopted; and
2. migrating genuine kernel consumers off the opaque D0/D1 compatibility
   representation, extracting or deleting that compatibility layer, and only
   then deciding the final unsuffixed names of the native EQ1 API.

The authority order remains the repository order in `AGENTS.md`.
`emdash3_2.lp` and the one-way native extension modules are implementation
authorities. This report records the selected objective, dependency order,
probe results, migrations, rejected alternatives, and completion evidence. It
does not override a contradictory active owner or authorize a rewrite merely
because the mathematical comparison is plausible.

The two tracks must not be implemented as one undifferentiated cleanup. The
native discrete/dimension/WalkingEnd migration completed in P3–P5 remains
final, and the 2026-07-20 P9 correction remains a separate completed removal
of the disproven selected-action abstraction and isolated Sum experiment.
The later user decision recorded in P10 deliberately reopens only P6's
bounded-retention branch: repository backward compatibility is no longer a
goal, so the frozen compatibility contract, its self-only clients, and its
legacy OneCat theorem are deletion material. That deletion removes the only
measured P7 collision source, so P11 deliberately reopens only the namespace
decision. Neither correction reopens the native representation, WalkingEnd,
Nat, PathRecord, finite-dimension, or canonical path-action designs.

## Goal

Replace the unusual `ObsAction` presentation with direct use of the canonical
iterable functor

```text
path_map_func(f) : Functor(Path_cat(A),Path_cat(B)),
```

retire `ObsDAction` unless a real displayed-functor/section consumer justifies
it, remove the later `PathActionRefinement` recasting after confirming that no
active semantic consumer needs an alternative definitional normal form,
retire the isolated Sum feature for later redesign, migrate noncompatibility
users from opaque D0/D1 omega-equivalence to the native equality-valued
representation, isolate or delete the remaining compatibility surface, and
make an evidence-backed decision about dropping the historical `_EQ1` suffix.

The implementation must preserve the generic `fapp*`/`tapp*` owners, proof
provenance, current WalkingEnd semantics, finite-dimension results, and the
one-way dependency direction of the native theorem modules.

## Review Verdict

The initial 2026-07-19 review selected two separate projects:

1. Recast `ObsAction` as an optional computational refinement of the
   now-canonical `path_map_func`, retiring `ObsDAction` first.
2. Migrate genuine kernel consumers off D0, then extract/delete the
   compatibility layer, and only afterward remove `_EQ1`.

P0–P8 implemented that selection and completed the compatibility work. A
follow-up consumer audit on 2026-07-20 invalidated the first project's chosen
abstraction, without invalidating its canonical `path_map_func` owner or any
P3–P8 result. The corrected verdict is:

1. `path_map_func(f)` and the generic `fapp*` calculus are already the complete
   principled nondependent action interface.
2. `PathActionRefinement` is type-correct but architecturally unnecessary in
   the active library: it is a parallel first-path-only channel, constructs no
   functor, supplies no higher action, and has no independent semantic
   consumer.
3. Remove the generic refinement package, its Nat and PathRecord wrappers,
   its proof-time support that exists only to compare a selected presentation,
   and its checks/examples. Do not retain aliases.
4. Retire the isolated Sum feature—including its ordinary decoded former—at
   the explicitly selected user boundary, and redesign it later only if a
   concrete consumer appears.
5. Retain direct dependent `eq_apd`, canonical `Path_cat_func`/
   `path_map_func`, `NatSucc_func`, and every completed native practical
   result. Do not retain a legacy theorem or example merely to preserve the
   compatibility representation through which it was once stated.

### Corrected compatibility and namespace verdict — 2026-07-20

The initial P6/P7 conclusion assumed that backward compatibility, including
the complete D0-based OneCat equivalence, was itself a repository objective.
That assumption was incorrect. The selected objective is the latest native
equality-valued design and its practical consequences, not continued support
for the old D0/D1/decoder presentation.

The corrected verdict is therefore:

1. Delete `emdash3_2_legacy_compat.lp`. It is a quarantined historical
   representation with no active implementation consumer and no authority
   role; extraction was a safe staging step, not a permanent library boundary.
2. Delete all seven clients that explicitly import it. Five are purely legacy
   demonstrations. The two mixed examples do not contain unique selected
   native behavior: their useful native categorical-universe and ordinary
   Product-isomorphism assertions are already owned by the main diagnostics
   and retained native reviewer examples.
3. Delete the exact legacy `one_cat_iso_type_equiv` theorem and its old
   two-sided decoder laws. It is mathematically sensible, but it is neither a
   prerequisite nor a consumer of the selected WalkingEnd/`BNat`, Nat,
   finite-dimension, or native equality-valued results. The repository is not
   required to re-prove that theorem before deleting its old representation.
4. Retain `OneCat`, native hom discreteness, native OneCat hom action and
   groupoidality, finite-`NCat` truncation, the one-way ordinary
   `IsoEvidence -> OmegaEquiv` lift, and all WalkingEnd/Nat results. These are
   the current design's meaningful OneCat content. A future full native
   equivalence between object equality and ordinary isomorphism evidence may
   be proposed independently if a concrete consumer warrants it; it is not a
   cleanup blocker and no compatibility-shaped alias is retained for it.
5. Once deletion removes the legacy exports, strip `_EQ1` from the native
   public identifiers by one exact token mapping. Do not create reverse
   aliases, partial mixed naming, or a second compatibility namespace.
6. Keep `emdash3_2_eq1_hom_action.lp` and
   `emdash3_2_eq1_evidence_property.lp` as module filenames in this phase.
   Their filenames remain useful architectural labels; renaming files while
   renaming symbols would unnecessarily mix a module-layout migration with a
   collision-free public-identifier cleanup.

## Validated Current State

The review started at exact commit
`2444c9d406fc3d201602ace7af5105c20c241680`. The worktree was clean, staged
and unstaged diffs were empty, and the bounded active check passed.

The lexical inventory at that baseline was:

```text
suffix   distinct names   occurrences   .lp files
_D0      57               1207          14
_D1       6                100           4
_EQ1    138               1548          14
```

These counts are navigation evidence, not deletion criteria. In particular,
the semantic legacy layer also hides behind unsuffixed aliases.

## `ObsAction`, `PathMap`, And Canonical Ownership

### Current implementation is stronger than stale July wording

The current implementation has advanced beyond some stale report text. Since
the July 19 G2 promotion the kernel has:

- `Path_cat_func : Grpd_cat -> Cat_cat`;
- `path_map_func(f) : Path_cat(A) -> Path_cat(B)`;
- object action by `f`;
- capped equality action by `eq_ap(f)`;
- a full iterable next-hom action;
- action on function equality through `path_map_transf`;
- inherited whole-functor identity and composition.

The active owners are near `Path_cat_func` and `path_map_func` in
`emdash3_2.lp`; permanent checks live under the catalog area “Internal Path
action and explicit Core-inclusion kappa.” The current G2 record in the
WalkingEnd plan is authoritative over its older `PathMap`, `ObsAction`, and
higher-functoriality section.

This creates a documentation inconsistency that must be repaired before or
with the first semantic slice:

- the current G2 override and the kernel say `path_map_func` is active;
- an older WalkingEnd-plan section still says it is not active;
- Foundations first documents `Path_cat_func`/`path_map_func`, then later says
  that the kernel contains no such constructor;
- deferred-boundary prose still lists a raw-function `PathMap` constructor as
  absent.

Do not infer implementation state from the stale paragraphs. Update them to
distinguish the now-active canonical `path_map_func` from any still-deferred
constructor that would build a new functor from an independently selected
action tower.

### Corrected canonical formulation — supersedes the P2 selection

For `f : tau(A) -> tau(B)`, `x,y : tau(A)`, and `p : x = y`, the ordinary
path action is exactly

```lambdapi
@fapp1_fapp0
  (Path_cat A)
  (Path_cat B)
  (@path_map_func A B f)
  x y p
```

The kernel's capped `Path_cat_func` rule reduces this term to `eq_ap(f,p)`.
The same functor retains its iterable next-hom action through `fapp1_func`,
action on equality of functions through `path_map_transf`, and ordinary
identity/composition behavior through the global `fapp*` calculus. No extra
record is required to define, recover, or compose path action.

P2 introduced the approximately typed package

```text
Sigma act : (Pi x y, x = y -> f(x) = f(y)),
  Pi x y p, act(x,y,p) = canonical_action(f,p).
```

That package is mathematically coherent, but it does not construct a functor,
does not strengthen `path_map_func`, does not make `path_map_func` use `act`,
and exposes only a capped first action. When `act` is canonical, the package
is a Sigma wrapper around the term above with reflexive coherence. Its only
possible role is to retain a different definitional presentation, such as
Nat successor's exposed predecessor path `p` instead of `eq_ap(succ,p)`, or a
branchwise Sum term instead of `eq_ap(sum_map(f,g),p)`.

The reproduced current-owner inventory finds no measured consumer that needs
either alternative normal form:

- Nat arithmetic and WalkingEnd use `nat_succ_function` and the canonical
  iterable `NatSucc_func`; no later arithmetic or WalkingEnd construction
  consumes `nat_succ_path_action_refinement`.
- the Sum selected-action surface is self-contained in its one-way module,
  diagnostics, and reviewer example;
- `path_record_action` merely projects the selected operation, and with the
  canonical package reduces back to direct `fapp1_fapp0(path_map_func(f),p)`;
- refinement identity and composition only demonstrate closure of the
  optional presentation; canonical functoriality already has a generic owner.

The corrected ownership boundary is therefore:

- `path_map_func(f)` solely owns nondependent semantic path action and every
  higher action;
- ordinary consumers use the exact `fapp1_fapp0` term above;
- consumers needing the iterable object retain the functor and use
  `fapp1_func`, rather than accepting a naked first-action map;
- no generic `PathActionRefinement` Sigma, selected-action parameter,
  compatibility alias, or parallel computation channel remains;
- a future exceptional operation may be introduced locally only after a
  measured consumer demonstrates a required definitional normal form, with a
  local comparison theorem if needed;
- a future dependent higher analogue remains a displayed functor/path-family
  action or section problem, not an ordinary `Path_cat(A) -> Path_cat(B)`.

### Corrective consumer retirement

The P9 migration is deletion-led rather than an API rename:

1. delete `PathActionRefinementMap`, `PathActionRefinementCoherence`,
   `PathActionRefinement`, and every generic introduction/projection,
   canonical, identity, composition, application, and agreement operation;
2. delete `path_record_action` and `path_record_action_agrees`, while retaining
   the independent PathRecord structure and direct `path_record_witness_action`
   through `eq_apd`;
3. delete `nat_succ_path_action_map`, its coherence, and its package, while
   retaining `nat_succ_function` and `NatSucc_func` because WalkingEnd uses
   the canonical functor;
4. delete the now-dead Nat comparison support—`nat_succ_ap_basis`, its two
   proof-time `unif_rule`s, `nat_succ_component_basis`,
   `nat_succ_basis_outer`, and `nat_succ_eq_ap`—because their only role is to
   relate the abandoned `p |-> p` presentation to canonical `eq_ap`;
5. remove refinement-specific diagnostics and reviewer examples, while
   preserving a focused canonical `path_map_func` regression at the ordinary
   Path-category owner;
6. remove active documentation of the abandoned interface without erasing
   dated P2 probe and promotion evidence; mark that evidence superseded.

### Selected Sum retirement boundary

The Sum inventory distinguishes two layers:

1. the selected-action extension `emdash3_2_sum_observational_action.lp` with
   its two stable bases, four proof-time comparisons, componentwise `eq_ap`
   theorems, and selected refinement; and
2. the independent kernel `SumData`/`Sum_grpd` former, visible-constructor
   equality rules, `sum_elim`, and `sum_map`.

Removing only the extension would be sufficient to correct path-action
ownership. The explicitly selected 2026-07-20 boundary is broader: retire the
entire currently isolated Sum feature and redesign it later if a concrete
consumer requires it. Exact `.lp` inventory finds Sum only in the kernel, the
main diagnostics, its one-way extension, and three reviewer examples
(`binary_sum`, `sum_observational_equality`, and
`sum_observational_action`). No Nat, WalkingEnd, native-EQ1, evidence-property,
or frozen-compatibility theorem consumes it.

P9 therefore deletes both layers, all three reviewer examples, their
diagnostics, and active build/health/authority wiring. This is a deliberate
feature withdrawal, not a logical consequence of canonical path action. Dated
Sum promotion evidence remains historical and receives a supersession note;
no inactive compatibility module or alias preserves the removed experiment.

## `ObsDAction`

`ObsDAction` is substantially easier to retire. Its only concrete kernel
registration is `path_record_witness_daction`, which is the canonical
`obs_daction_from_section`; `path_record_witness_action` therefore supplies
nothing beyond `eq_apd` through an extra Sigma package.

Outside the registry's own checks and reviewer example, there is no
specialized dependent implementation or downstream consumer. The selected
first migration is therefore:

1. define or retain `path_record_witness_action` directly through `eq_apd`;
2. preserve any useful formation and PathOver regression assertions at that
   direct owner;
3. delete `path_record_witness_daction`;
4. delete `ObsDActionMap`, `ObsDActionCoherence`, `ObsDAction`, and the generic
   `obs_daction_*` operations once their exact consumer inventory is zero;
5. rewrite or retire the dependent part of `examples/observational_action.lp`.

A future full dependent analogue of `path_map_func` would be displayed
structure: a displayed functor/path-family action or a section over
`Path_cat(A)`. It would not be an ordinary
`Path_cat(A) -> Path_cat(B)`. Do not retain the present one-level registry as
a placeholder for that unimplemented construction, and do not claim that its
deletion constructs displayed higher action.

## D0/D1 Compatibility Retirement

### Why suffix deletion is not semantic retirement

Deleting `_D0` spellings is not enough. The unsuffixed public layer still
hides D0:

```text
OmegaEquivAlong(f) := OmegaEquivAlong_D0(f)
OmegaEquiv         := Sigma f, OmegaEquivAlong(f).
```

More importantly, `IsDiscreteCat` still stores legacy `OmegaEquivAlong`
evidence for `Core_incl_func`, while `discrete_core_homwise`,
`discrete_core_hom_inv_func`, `hom_to_path`, and their round trips use the D0
next-hom action and recursive cells. `IsNCat` uses `IsDiscreteCat` at zero,
and WalkingEnd consumes the resulting dimension/discreteness spine and
`hom_to_path`.

The native hom-action and evidence-property modules are D0-free, but the
overall kernel and finite-dimension consumer spine are not yet entirely
D0-free. This distinction must remain explicit in reports and completion
claims.

### Selected native migration

The dependency-ready representation change is:

1. redefine or migrate `IsDiscreteCat(C)` so its second factor is native
   `IsGroupoidalCat_EQ1(C)` or the definitionally identical native fixed-map
   evidence, while preserving object sethood as the first factor;
2. make the corresponding projection return native groupoidality evidence;
3. route homwise path selection and re-inclusion through
   `groupoidal_core_homwise_EQ1`, `groupoidal_arrow_to_path_EQ1`, and
   `groupoidal_path_to_arrow_retract_EQ1` from the one-way native hom-action
   extension;
4. decide the resulting module owner of `hom_to_path` and its compatibility
   name without creating a kernel-to-extension cycle;
5. update WalkingEnd and any other genuine consumer to import and use the
   native owner;
6. verify that `IsNCat`, `NCat`, the WalkingEnd dimension witness, Hom--Nat
   proof, sethood results, and directed negative consequences preserve their
   existing public behavior.

The likely clean dependency direction is to keep the formation of
`IsDiscreteCat`/`IsNCat` in the kernel with native evidence, place homwise
derived consumers in the existing native hom-action extension, and make
WalkingEnd import that extension. This is a hypothesis to reproduce in a
focused full-owner probe, not a license to move symbols before checking for
cycles and downstream imports.

### Compatibility consumers to classify individually

After the discrete/dimension spine is native, classify remaining old APIs by
role rather than suffix:

- opaque `OmegaEquivAlong_D0` and its four recursive observations;
- transparent D0 Sigma packages and finite observation/path views;
- EQ1-to-D0 and D0-to-EQ1 migration constructors;
- D0b-style next-hom helpers whose former classifier name has already
  disappeared but whose `_D0` operations remain;
- D1 path, opposite, Product, and category-next-hom compatibility owners;
- `CatPathView`, `idtoequiv_cat`, `omega_equiv_path`, and decoder round trips;
- ordinary-isomorphism-to-D0 and OneCat decoder-based lift material;
- the conditional D0 evidence-property and finite-observation truncation
  experiments;
- examples whose sole purpose is to demonstrate those compatibility APIs.

For each consumer, select one of:

1. migrate to a native equality-valued constructor/projection/theorem;
2. redefine transparently through `object_path_equiv_EQ1`, the stable cast
   view, or a native derived bridge;
3. retain as a useful theorem-level library result with a non-D0 statement;
4. move unchanged into an opt-in compatibility module;
5. delete when it has no nonself consumer.

Do not delete useful theorem-level `TypeEquiv`, `IsEquivMap`, or explicit
comparison theorems merely because they once participated in a universe
decoder. The target is retirement of opaque recursive D0 as an operational
foundation, not removal of standard theorem-level formulations of
equivalence.

The OneCat ordinary-isomorphism material is a likely native simplification
candidate: ordinary inverse arrows and equality laws can construct
`OmegaEquivAlong_EQ1` directly, and the stable native cast can return object
equality. Reproduce exact computation and round-trip needs before deciding
whether to migrate or delete the decoder-based API.

### Extraction and deletion order

Do not combine the semantic migration with a file split. First migrate active
kernel consumers in place and validate their behavior. Only after exact-token
inventory shows that the remaining old layer is downstream-only should a
mechanical extraction move it into a compatibility module.

The extraction is an intermediate architectural test:

- the active kernel and native theorem modules must check without importing
  the compatibility module;
- WalkingEnd, Nat, and the main diagnostic suite must not acquire a legacy
  import transitively;
- legacy reviewer examples must import the compatibility module explicitly;
- no rule, unifier, or decoder may be duplicated across the boundary.

Once isolated, delete the compatibility module if repository backward
compatibility is not a selected requirement. If it is retained temporarily,
mark it as non-authoritative and keep it out of normal imports.

The six `_D1` names belong entirely to compatibility-era staging. Retire them
with the D0/decoder surface rather than polishing their suffixes as a separate
API.

## Removing `_EQ1`

Eventually, removing `_EQ1` is appropriate. The July 17 equality-valued plan
explicitly retained the suffix because unsuffixed legacy names were still
public. Once those names are freed, the native API should be considered for
the ordinary mathematical namespace:

```text
OmegaEquivAlong_EQ1  -> OmegaEquivAlong
OmegaEquiv_EQ1       -> OmegaEquiv
IsGroupoidalCat_EQ1  -> IsGroupoidalCat
AllArrowsEquiv_EQ1   -> AllArrowsEquiv
ncat_obj_trunc_EQ1   -> ncat_obj_trunc
ObjectPathCastView_EQ1 -> ObjectPathCastView
...
```

This is semantically low-risk but mechanically broad: the initial inventory
found 138 distinct `_EQ1` names across 14 `.lp` files. It must be a standalone
namespace migration after compatibility retirement, not part of the D0
representation change.

Before renaming:

- all unsuffixed collisions must be removed or deliberately reassigned;
- the compatibility module must be deleted or explicitly frozen under a
  separate legacy namespace;
- public versus protected helper names must be inventoried;
- module filenames and example filenames must be considered separately from
  symbol names;
- reports must stop using EQ1 as a staging label when they mean the canonical
  equality-valued equivalence concept.

A temporary reverse alias layer is permitted only if it has a concrete
external compatibility consumer and does not recreate two equal-status public
APIs. Otherwise perform one synchronized rename and update every active
authority.

## What Must Not Be Conflated

The plan distinguishes four cleanup decisions:

1. retiring `ObsDAction` and recasting selected nondependent action;
2. migrating opaque recursive D0/D1 evidence and its genuine consumers;
3. retaining useful theorem-level equivalence/round-trip libraries where they
   remain mathematically valuable;
4. renaming the canonical native namespace after old names are free.

Passing one boundary does not imply the others. In particular:

- `path_map_func` does not make every selected computational action
  definitionally canonical;
- deleting `ObsDAction` does not construct displayed higher action;
- native theorem modules being D0-free does not mean `IsDiscreteCat` and
  WalkingEnd are already D0-free;
- deleting suffix-bearing names does not remove unsuffixed legacy aliases;
- direct equality/EQ1 comparison does not make every raw path expose facade
  observers;
- D0 retirement does not require deleting `TypeEquiv` as a library concept;
- D0 retirement does not by itself justify removing `_EQ1` in the same diff.

## Phased Implementation Plan

### Phase P0 — Recovery, adoption, documentation correction, and baselines

1. Re-read all authorities relevant to the next slice and this plan.
2. Inspect staged and unstaged diffs separately and preserve unrelated work.
3. Confirm whether the current commit is the implementation baseline or a
   descendant/checkpoint; never reset to the recorded commit.
4. Register this report in `reports/INDEX.md` as the active living plan.
5. Correct stale `PathMap` absence claims in Foundations, the current SOP,
   and the older WalkingEnd-plan section without rewriting historical probe
   evidence.
6. Relocate every affected symbol with `rg` and record the exact consumer
   inventory in this ledger.
7. Run a bounded baseline, warning inventory, and strict LHS audit before the
   first semantic probe.

Exit gate: active documentation agrees that `Path_cat_func` and
`path_map_func` are implemented; the worktree provenance, baseline checks,
warning counts, and audit counts are recorded here; no semantic code has yet
changed.

#### P0 promotion record — 2026-07-19

- `HEAD` was exactly the implementation starting baseline
  `2444c9d406fc3d201602ace7af5105c20c241680`. Staged and unstaged tracked
  diffs were empty before adoption; this new plan was the only initial
  untracked path after creation.
- `EMDASH_TYPECHECK_TIMEOUT=60s make check` passed.
- `make warning-summary` passed with 1,016 unjoinable and 159 replaceable
  kernel warnings, 1,175 total. The raw inventory is retained at
  `logs/warnings/latest.log`.
- `make audit-rules` passed with zero reconstructible/unreviewed LHS findings
  and 45 annotated slots across 27 intentional clauses.
- Exact-token relocation confirmed that the active canonical owner is
  `Path_cat_func`, with readable `path_map_func`/`path_map_transf` projections,
  capped action reducing to `eq_ap`, and iterable higher action retained by
  the generic functor calculus.
- The complete active dependent-registry inventory is confined to three
  `.lp` files: its generic definitions and one PathRecord wrapper in
  `emdash3_2.lp`, self-tests plus the PathRecord test in
  `emdash3_2_checks.lp`, and two reviewer assertions in
  `examples/observational_action.lp`. There is no native-EQ1, Nat, WalkingEnd,
  Sum-module, or other semantic consumer. The only concrete wrapper,
  `path_record_witness_action`, has exactly the direct `eq_apd` target.
- `INDEX.md`, Foundations, the current SOP, the older WalkingEnd plan, and the
  equality-valued redesign handoff now distinguish the active canonical path
  functor from optional selected computation. Dated pre-G2 probe conclusions
  are retained as historical evidence rather than rewritten.
- `git diff --check` passed after this documentation-only synchronization; no
  semantic source, diagnostic, or example was changed in P0.

### Phase P1 — Retire `ObsDAction`

1. Build the smallest owner-position full-file probe in which
   `path_record_witness_action` calls `eq_apd` directly.
2. Preserve positive arbitrary-PathOver formation and computation checks.
3. Remove the PathRecord dependent registration and generic dependent
   registry in the probe.
4. Check for hidden imports, rule interactions, and reviewer-example uses.
5. Promote the smallest validated edit to the kernel/checks/example.

Exit gate: no active `ObsDAction` or `obs_daction_*` occurrence remains; the
PathRecord witness action and its semantic agreement remain checked; no new
rewrite or `unif_rule` was introduced.

#### P1 promotion record — 2026-07-19

- The ignored owner-position full-file probe is
  `tmp/probes/paecr_p1_obsd_retire_owner_full.lp`. It removes the complete
  dependent registry at its actual owner, removes
  `path_record_witness_daction`, defines `path_record_witness_action` directly
  by `eq_apd`, and adds arbitrary-PathOver formation plus definitional-
  agreement assertions. Quiet and warning-enabled probe logs end in
  `20260719-212716` and `20260719-212725`; both pass.
- The warning-enabled full-file probe preserves the baseline 1,016
  unjoinable/159 replaceable inventory. The promoted `make warning-summary`
  independently reports the same 1,175 total warnings, so deleting the
  semantic packages introduced no rewrite or critical-pair delta.
- Promotion deletes `ObsDActionMap`, `ObsDActionCoherence`, `ObsDAction`, all
  four `obs_daction_*` operations, and `path_record_witness_daction` from
  `emdash3_2.lp`. `path_record_witness_action` is now the readable direct
  `eq_apd` definition. No rule, `unif_rule`, or opaque capability was added.
- Registry self-tests, the obsolete concrete-package test, and the arbitrary-
  package negative were removed from `emdash3_2_checks.lp`. The arbitrary
  PathOver formation assertion and the direct-`eq_apd` equality remain. The
  reviewer example replaces its generic dependent-registry assertion with the
  same direct PathRecord equality and remains at ten assertions.
- Exact-token search has zero `ObsDAction`, `obs_daction_*`, or
  `path_record_witness_daction` occurrence in active `.lp` files. Historical
  report occurrences are retained only where they describe dated promotion
  evidence and are paired with supersession notes in current status sections.
- `EMDASH_TYPECHECK_TIMEOUT=60s make check`, the focused reviewer check, and
  `make examples` pass. `make audit-rules` remains zero/45/27.
- The regenerated catalog contains 2,074 classified checks across 77 areas,
  with zero legacy tags and zero unclassified checks. The eight-check decrease
  is exactly the retired package's self-tests and obsolete negative; no
  semantic PathRecord coverage was lost.
- `make health` passes all 55 measured source/example targets and writes the
  2026-07-19T21:37:53-0400 health report. Final `make ci` passes the same 55
  targets with 164.887s aggregate typecheck time, all 16 Infinity-Codex tests,
  shell/Python integrity checks, diff/TOC/reference/header checks, strict LHS
  audit, and fresh strict catalog validation.
- README, INDEX, Foundations, the current SOP, and retained decision reports
  now identify direct `eq_apd` as the dependent owner and reserve any stronger
  analogue for a consumer-driven displayed functor/section construction. P2
  was intentionally not mixed into this deletion slice.

### Phase P2 — Recast `ObsAction` as `PathActionRefinement`

1. Probe the new refinement classifier against the exact capped
   `path_map_func` action, not a duplicated `eq_ap` body.
2. Verify that the existing canonical, identity, composition, Nat, PathRecord,
   and Sum constructions typecheck through it.
3. Check both reduction orders for identity and composition consumers.
4. Keep `path_map_func` as the sole ordinary functor owner.
5. Promote aliases first if that materially reduces migration risk, then
   migrate consumers one at a time.
6. Move former-specific refinements out of the kernel when their dependency
   boundary is already a one-way library module.
7. Remove the old observational names after exact-token inventory reaches the
   selected boundary.

Exit gate: every retained selected action is explicitly a refinement of the
canonical Path functor action; no active native-EQ1 or WalkingEnd consumer
depends on the old names; full higher action remains owned solely by
`Path_cat_func`.

#### P2 promotion record — 2026-07-19

- The exact starting consumer inventory was confined to six active `.lp`
  files: the generic/PathRecord/Nat owners in `emdash3_2.lp`, permanent
  diagnostics, the one-way Sum module, and the three observational-action
  reviewer examples. Native EQ1 and WalkingEnd had no dependency on the old
  API.
- `PathActionRefinementMap`, `PathActionRefinementCoherence`, and
  `PathActionRefinement` now live immediately after the capped
  `path_map_func` action owner. Their public coherence target is the exact
  `fapp1_fapp0(path_map_func(f),p)` term, not a duplicated `eq_ap` body. The
  introduction, selected-map/application, agreement, canonical, identity, and
  composition operations add no rewrite or `unif_rule` and construct no
  second functor.
- Owner-position full-file probes are
  `tmp/probes/paecr_p2_path_action_refinement_owner_full.lp`,
  `tmp/probes/paecr_p2_nat_path_action_refinement_owner_full.lp`, and
  `tmp/probes/paecr_p2_sum_path_action_refinement_owner_full.lp`. Quiet logs
  end in `215103`, `215133`, and `215231`; warning-enabled generic/Sum logs end
  in `215717` and `215719`. The focused cross-owner diagnostic probe
  `tmp/probes/paecr_p2_path_action_refinement_checks.lp` passes in `215657`.
- The identity reduction orders join: canonical path-map action of the
  categorical identity reduces to the input path. Composite canonical action
  does not convert to nested canonical action at open endpoints; the existing
  propositional `eq_ap_comp` theorem supplies the exact comparison. Permanent
  positive and negative diagnostics retain this boundary, so no competing
  composition fold was introduced.
- Nat-specific selection moved from the kernel into the already one-way Nat
  extension as `nat_succ_path_action_map`,
  `nat_succ_path_action_coherence`, and
  `nat_succ_path_action_refinement`, coherently targeting `NatSucc_func`.
  PathRecord consumes the generic refinement while its dependent witness
  remains direct `eq_apd`. The Sum library now exposes
  `sum_path_action_map`, `sum_path_action_coherence`, and
  `sum_path_action_refinement`, with its existing proof-time bases retained as
  internal proof support.
- All generic, Nat, PathRecord, Sum, diagnostic, and reviewer consumers were
  migrated directly. No temporary `ObsAction` alias was needed. Exact-token
  search has zero old nondependent or dependent action API occurrence in
  active `.lp` files; filenames that still contain `observational_action` are
  retained module/example paths, not a second symbol namespace.
- The promoted bounded `make check` and all three affected reviewer examples
  pass. `make warning-summary` remains exactly 1,016 unjoinable and 159
  replaceable warnings, and `make audit-rules` remains zero unreviewed
  candidates with 45 annotated slots across 27 intentional clauses.
- The regenerated catalog contains 2,077 classified checks across 77 areas,
  with zero legacy tags and zero unclassified checks. `make examples` passes.
  `make health` passes all 55 measured targets and writes the
  2026-07-19T22:22:52-0400 report. Final P2 `make ci` passes the same 55
  targets with 133.929s aggregate typechecking, all 16 Infinity-Codex tests,
  shell/Python integrity checks, diff/TOC/reference/header checks, strict LHS
  audit, and fresh strict catalog validation.

### Phase P3 — Native discrete/dimension/WalkingEnd migration

1. Probe the native representation of the second `IsDiscreteCat` field.
2. Reproduce the module dependency graph for native homwise path selection.
3. Migrate projections and consumers without introducing a kernel-extension
   cycle.
4. Migrate `hom_to_path`, both round trips, and any reviewer-facing aliases to
   native groupoidality owners.
5. Update WalkingEnd imports and its hom-discreteness normalization proof.
6. Recheck `IsNCat`, `NCat`, native object truncation, WalkingEnd Hom--Nat
   packages, sethood, and directed negative results.

Exit gate: the discrete/dimension/WalkingEnd spine contains no D0, D1, or
D0/EQ1 migration-constructor reference; its public mathematical behavior is
preserved and all affected examples pass.

#### P3 promotion record — 2026-07-19

- The reproduced dependency graph confirmed that native
  `IsGroupoidalCat_EQ1` formation already belongs to the kernel, whereas its
  homwise inverse/retract construction correctly belongs to the one-way
  `emdash3_2_eq1_hom_action.lp` extension. This permits native formation in
  the kernel and derived path selection downstream without a cycle.
- `IsDiscreteCat(C)` is now exactly
  `IsSetGrpd(Obj(C)) × IsGroupoidalCat_EQ1(C)`. Its constructor and second
  projection accept/return native evidence, and
  `discrete_cat_is_groupoidal_EQ1` is a transparent projection alias rather
  than a D0-to-EQ1 migration.
- Canonical `discrete_core_homwise`, `discrete_core_hom_inv_func`,
  `hom_to_path`, `discrete_core_hom_left_law`, both named round trips, and
  `one_cat_hom_core_homwise` now live in the native hom-action extension.
  They route through `groupoidal_core_homwise_EQ1`,
  `groupoidal_arrow_to_path_EQ1`, and
  `groupoidal_path_to_arrow_retract_EQ1`. Re-inclusion is exposed first as
  equality by `path_to_hom_hom_to_path_path`; the retained directed-cell API
  is its canonical `path_to_hom` image. The other round trip uses the stored
  object-set proof. Neither is a runtime cancellation.
- WalkingEnd now imports the native hom-action extension explicitly. Its based
  cell-to-path consumer uses the native `hom_to_path`, and `nat_path_discrete`
  constructs its second field directly with `path_cat_is_groupoidal_EQ1`, so
  WalkingEnd/BNat contain no D0, D1, or migration-constructor occurrence.
  The native evidence-property and finite-object-truncation module remains
  D0-free and continues to consume the projected groupoidality witness.
- The pre-existing OneCat ordinary-isomorphism decoder is not silently
  represented as native. Its seven discrete helpers and next-hom alias have
  been renamed with explicit `_D0` ownership and remain a temporary
  compatibility island in the kernel. They are not in the canonical
  discrete/dimension/WalkingEnd dependency closure and are the first P4
  consumer family to migrate, extract, or delete.
- Owner-position full-file probes are
  `tmp/probes/paecr_p3_native_discrete_kernel_owner_full.lp`,
  `tmp/probes/paecr_p3_native_discrete_eq1_owner_full.lp`,
  `tmp/probes/paecr_p3_native_discrete_nat_owner_full.lp`,
  `tmp/probes/paecr_p3_native_discrete_walking_owner_full.lp`, and
  `tmp/probes/paecr_p3_native_discrete_evidence_owner_full.lp`; their quiet
  logs end in `223646`, `223743`, and `223805`. The focused cross-owner probe
  `tmp/probes/paecr_p3_native_discrete_checks.lp` passes in `223931` and
  retains the native-field negative and both runtime non-cancellation
  controls.
- No rewrite or `unif_rule` was added. Bounded `make check`, the six focused
  discrete/dimension/groupoidal/evidence/WalkingEnd/OneCat examples, and the
  full reviewer suite pass. Warnings remain exactly 1,016 unjoinable and 159
  replaceable; strict audit remains zero unreviewed with 45 annotated slots
  across 27 clauses.
- The regenerated catalog has 2,079 classified checks across 77 areas, zero
  legacy tags, and zero unclassified checks. Health passes all 55 targets and
  writes the 2026-07-19T22:56:41-0400 report. Full P3 `make ci` passes the same
  55 targets with 140.508s aggregate typechecking, all 16 Infinity-Codex
  tests, shell/Python integrity checks, diff/TOC/reference/header checks,
  strict LHS audit, and fresh strict catalog validation.

#### P4 role and consumer inventory — 2026-07-19

The post-P3 declaration inventory contains 67 kernel declarations whose names
contain `D0` and exactly six whose names contain `D1`. No such declaration is
owned by either native EQ1 extension, Nat, WalkingEnd, or the Sum refinement
module. Exact-token searches put all remaining implementations in
`emdash3_2.lp`; the other occurrences are diagnostics and explicitly legacy
reviewer examples. Unsuffixed `OmegaEquivAlong`, `OmegaEquiv`, their observers,
the Cat decoder, and the associated univalence API remain semantically D0 and
must therefore be counted even though their public spellings have no suffix.

The current role classification is:

| Family | Exact current consumers | P4 decision |
| --- | --- | --- |
| opaque fixed-arrow owner, recursive observations, transparent D0 package, and unsuffixed public aliases | compatibility kernel itself; D0/D1, migration, decoder, Product, conditional, and OneCat diagnostics/examples | foundational compatibility core; retain only until its downstream families are migrated or deleted, then extract mechanically rather than rename it |
| one-layer `OmegaEquivAlongObservation_D0`/`PathView` experiment | kernel self-use, diagnostics, `omega_equiv_evidence_view.lp`; the deep-view example mentions the one-layer API only as a nonconversion control | delete: it is a historical observation/debug experiment with no theorem or native consumer |
| dimension-indexed D0 observation and path-view experiment | kernel self-use, diagnostics, `omega_equiv_evidence_dim_view.lp` | delete: native unrestricted evidence-property and finite-`NCat` truncation results supersede its purpose |
| `OmegaEquivAlongEvidenceProp_D0` and `ncat_obj_trunc_from_evidence_prop` | kernel self-use, diagnostics, `ncat_object_truncation_conditional.lp` | delete the capability and conditional theorem; retain `prop_is_trunc_cat_dim`, which has two real consumers in `emdash3_2_eq1_evidence_property.lp` and is representation-independent |
| D0/EQ1 migration constructors and `object_path_equiv_D0` | compatibility kernel, diagnostics, `equality_evidence_migration.lp`, categorical-universe compatibility checks, and the current OneCat lift | retain only as temporary migration/extraction surface; delete with the final D0 core after those consumers are classified |
| D0 next-hom reconstruction and the six D1 decoder/opposite/Product/category-hom owners | compatibility kernel, diagnostics, `omega_equiv_along_d0b.lp`, `omega_equiv_d1.lp`, and Product provenance checks | compatibility-only; the native next-hom replacement is already promoted, so these move or disappear with their legacy examples rather than receiving further API polish |
| temporary discrete `_D0` helper island | kernel-internal support for `one_cat_omega_inverse_path`; no diagnostic or example names the helpers directly | remove when the OneCat decoder proof is migrated or extracted; `one_cat_hom_core_homwise_D0` has no consumer at all and is immediately deletable |
| ordinary-isomorphism lift and OneCat decoder round trips | kernel, diagnostics, `onecat_iso_lift.lp`; no active dimension/WalkingEnd consumer | retain the theorem-level `one_cat_iso_type_equiv` objective, but first probe a native proof. If the native stable cast lacks the required package/path coherence, classify the existing proof as an opt-in decoder theorem for extraction rather than weakening its two round trips |
| Cat/Grpd decoder, object-TypeEquiv, and object-truncation invariance interfaces | compatibility kernel, diagnostics, `categorical_universe_identity.lp`, `categorical_truncation_invariance.lp`, and legacy portions of Product provenance | classify interface by interface: native direct universe identity remains authoritative; preserve ordinary `TypeEquiv` mathematics only where it can be restated without the opaque decoder; otherwise extract it explicitly |

The examples whose stated purpose is solely D0/D1 staging are therefore not
permanent API obligations. The first deletion tranche may remove the two
finite observation examples and the conditional truncation example together
with their self-only checks. The OneCat result is deliberately excluded from
that tranche until the native round-trip probe below is resolved.

#### P4 native feasibility and first retirement record — 2026-07-19

The OneCat replacement probe resolves the ordinary-isomorphism split more
precisely than the preliminary inventory:

- ordinary `IsoEvidence(C,x,y)` directly constructs
  `OmegaEquivAlong_EQ1(C,x,y,iso_evidence_to(i))`; the single selected inverse
  fills both inverse slots, and the two ordinary inverse equations already
  have the native equality-valued law types;
- packaging that evidence as `OmegaEquiv_EQ1(C,x,y)` and applying the stable
  native cast does return an object path;
- the stable cast deliberately does not provide package/raw-path reification
  coherence. Even at ordinary reflexivity, the explicit native package
  `omega_equiv_pack_EQ1(...)` is not judgmentally `eq_refl`; the smallest
  attempted base case for the old OneCat decoder therefore fails at exactly
  that comparison.

The passing focused feasibility probe is
`tmp/probes/paecr_p4_onecat_native_cast_feasibility.lp`, with log ending
`20260719-231229`. The intentional expected-failure probe is
`tmp/probes/paecr_p4_onecat_native_cast_expected_failure.lp`, with log ending
`20260719-231240`; its residual goal is the explicit native package versus
`eq_refl`. This agrees with the equality-valued redesign boundary: stable
facade casts are not package observers or raw-path decoders.

The selected decision is therefore:

1. promote the useful one-way native ordinary-isomorphism lift;
2. retain `one_cat_iso_type_equiv` and its two specified inverse laws as an
   opt-in compatibility theorem for later extraction;
3. do not weaken either round trip, add a proof-time package/path
   identification, or invent a decoder/coherence theorem merely to remove its
   D0 implementation;
4. record native package/path reification coherence as the exact prerequisite
   that could change this classification in a future separately probed task.

The promoted kernel definitions are
`iso_evidence_omega_along_EQ1` and `iso_evidence_omega_equiv_EQ1`, immediately
after `object_path_equiv_EQ1`. They are transparent structural definitions and
add no rewrite or `unif_rule`. The owner-position full-file probe is
`tmp/probes/paecr_p4_iso_evidence_eq1_kernel_owner_full.lp`; its quiet and
warning logs end in `231432` and `231506`. The warning inventory remains
exactly 1,016 unjoinable and 159 replaceable. Permanent diagnostics cover
formation, the forward projection, a selected inverse, the right law, and the
negative stable-cast/reflexivity provenance boundary. The native reviewer
example contains corresponding public assertions.

The first consumer-led deletion tranche is also promoted. It removes:

- the one-layer `OmegaEquivAlongObservation_D0`/`PathView` record, observer,
  reflexivity, and path-action experiment;
- the dimension-indexed D0 observation/path-view experiment and all of its
  constructors, observers, and path operations;
- `OmegaEquivAlongEvidenceProp_D0` and the conditional
  `ncat_obj_trunc_from_evidence_prop` theorem, now superseded by the
  unconditional native evidence-property and finite-dimension results; and
- the unused `one_cat_hom_core_homwise_D0` helper.

`prop_is_trunc_cat_dim` remains in the kernel with representation-independent
wording because the native evidence-property module has two real consumers.
The owner-position deletion probe is
`tmp/probes/paecr_p4_self_only_compat_retire_kernel_owner_full.lp`; quiet and
warning logs end in `231723` and `231732`, again at 1,016/159. The synchronized
check probe is `tmp/probes/paecr_p4_self_only_compat_retire_checks_full.lp`.
The self-only reviewer examples
`omega_equiv_evidence_view.lp`, `omega_equiv_evidence_dim_view.lp`, and
`ncat_object_truncation_conditional.lp` are deleted. Exact active `.lp`
searches contain none of the retired symbols.

After this tranche the kernel has 54 declarations whose names contain `D0`
(52 ending in `_D0` and the two reverse migration names containing
`_D0_to_EQ1`) and six whose names end in `_D1`; all implementations remain in
`emdash3_2.lp`, with occurrences elsewhere confined to diagnostics and
explicit compatibility examples. The bounded active check, complete reviewer
suite, and `git diff --check` pass. `make warning-summary` remains exactly
1,016 unjoinable/159 replaceable warnings, and `make audit-rules` remains zero
unreviewed with 45 annotated slots across 27 intentional clauses. The
regenerated catalog has 2,034 classified checks across 74 areas, zero legacy
tags, and zero unclassified checks. Health passes all 52 surviving
source/example targets and writes the 2026-07-19T23:36:10-0400 report. The
source TOC remains synchronized at 87 headings across sections 0–20. Full P4-
tranche `make ci` passes all 52 targets with 136.435s aggregate typechecking,
all 16 Infinity-Codex tests, shell/Python integrity checks, diff/TOC/reference/
header checks, strict LHS audit, and fresh strict catalog validation.

#### P4 native theorem migration and final extraction manifest — 2026-07-19

The final consumer review preserves categorical object-truncation invariance
without the legacy decoder. The kernel now provides transparent
`omega_equiv_along_obj_path_EQ1`,
`omega_equiv_along_obj_type_equiv_EQ1`,
`is_obj_trunc_cat_equiv_type_equiv_EQ1`,
`is_obj_trunc_cat_equiv_to_EQ1`, and
`is_obj_trunc_cat_equiv_from_EQ1`. A fixed functor and its native evidence are
packaged with `omega_equiv_pack_EQ1`, cast to object equality through the
stable facade, mapped through `Obj`, and decoded by `idtoequiv_grpd`; the
standard `is_trunc_grpd_type_equiv` theorem then transports truncation. No new
rule or `unif_rule` was introduced. Both TypeEquiv round trips are permanent
diagnostics. Explicit native reflexivity deliberately does not collapse to a
raw object path or reflexive TypeEquiv, preserving the stable-facade
provenance boundary.

The owner-position full-file probe is
`tmp/probes/paecr_p4_native_obj_trunc_invariance_kernel_owner_full.lp`; its
quiet and warning-enabled logs end in `234320` and `234327`, with the warning
inventory unchanged at 1,016/159. The synchronized diagnostic probe is
`tmp/probes/paecr_p4_native_obj_trunc_invariance_checks_full.lp`, log ending
`234516`. `categorical_truncation_invariance.lp` now uses only the native EQ1
theorem and passes in log `234714`. Exact search leaves the old unsuffixed
object-truncation invariance family self-contained inside compatibility.

The remaining incidental visible-constructor consumers were then migrated
from `idtoequiv_cat`/`omega_equiv_refl` to
`object_path_equiv_EQ1`/`omega_equiv_refl_EQ1`. The focused probe
`tmp/probes/paecr_p4_native_elementary_encoder_checks.lp` covers Unit, Bool,
Nat, Sum, and both literal and already-shaped PathRecord reflexivity; its final
log ends in `235551`. The main diagnostics and the four public
`*_observational_equality.lp` reviewer examples use the same native owners,
while their independent ordinary `idtoiso_cat` checks remain standard library
coverage. Bounded `make check` passes, and focused reviewer logs for Unit,
Bool, Nat, and Sum end in `235733`. The native equality-valued and direct-
univalence examples no longer mention D0 or `CatPathView` merely as negative
controls.

P4 therefore classifies the complete remaining compatibility closure for a
single mechanical extraction:

- all 54 declarations whose names contain `D0` and all six declarations whose
  names end in `_D1` move together, including the opaque fixed-arrow owner,
  D0 package and observations, migration constructors, D0b next-hom family,
  Product/opposite compatibility, category-hom decoder action, and temporary
  OneCat discrete helpers;
- the unsuffixed D0-backed `OmegaEquivAlong`, `OmegaEquiv`, projections,
  inverse cells, reflexivity, fibres, opposite/Product constructors, decoder,
  `CatPathView`, category-univalence capability, and CatPath surface move with
  their actual owner rather than remaining as misleading canonical names;
- legacy `iso_evidence_path` and its Product computation rule move because
  they are a bodyless decoder capability. Ordinary `idtoiso_cat`,
  `CatIsoUnivalence`, `isotoid_cat`, `iso_evidence_product`, and the Product
  `idtoiso_cat` rule remain in the active kernel;
- the old decoder-based object-TypeEquiv/object-truncation family moves now
  that its useful theorem-level result has a native statement;
- `one_cat_iso_type_equiv` and its complete two-sided contract move intact.
  The exact missing native prerequisite remains facade-package/raw-path
  reification coherence, so P4 neither weakens the theorem nor invents a
  proof-time equality;
- `GrpdPathView = TypeEquiv`, the groupoid decoder, and their theorem-level
  Pi/Sigma/Product action library remain in the kernel: they are D0-free,
  useful independently, and are not an alternative omega-equivalence
  foundation;
- native Cat/Grpd direct EQ1 equality rules, `IsDiscreteCat`, `IsObjTruncCat`,
  `CatDim`, `OneCat`, `one_cat_hom_discrete`, and every native extension remain
  in the active dependency closure.

The exact suffix-bearing declaration manifest is:

```text
OmegaEquivAlong_D0 OmegaEquiv_D0 omega_equiv_to_D0
omega_equiv_evidence_D0 omega_equiv_along_left_inv_D0
omega_equiv_along_right_inv_D0 omega_equiv_along_left_cell_D0
omega_equiv_along_right_cell_D0 omega_equiv_along_left_cell_to_D0
omega_equiv_along_right_cell_from_D0 omega_equiv_along_refl_D0
omega_equiv_refl_D0 omega_equiv_along_path_D1 omega_equiv_along_op_D1
omega_equiv_along_D0_to_EQ1 omega_equiv_D0_to_EQ1
omega_equiv_along_EQ1_to_D0 omega_equiv_EQ1_to_D0 object_path_equiv_D0
iso_evidence_omega_along_D0
omega_equiv_along_left_whisker_right_cell_from_D0
omega_equiv_along_right_whisker_left_cell_to_D0
omega_equiv_along_inverse_assoc_path_D0
omega_equiv_along_inverse_assoc_D0 omega_equiv_along_left_to_right_D0
omega_equiv_along_product_D1 omega_equiv_along_left_functor_D0
omega_equiv_along_right_functor_D0 omega_equiv_along_left_to_transf_D0
omega_equiv_along_left_from_transf_D0 omega_equiv_along_right_to_transf_D0
omega_equiv_along_right_from_transf_D0 omega_equiv_along_left_to_component_D0
omega_equiv_along_left_from_component_D0
omega_equiv_along_right_to_component_D0
omega_equiv_along_right_from_component_D0
omega_equiv_along_right_to_left_component_D0
omega_equiv_along_left_to_right_component_D0
omega_equiv_along_left_inverse_right_component_D0
omega_equiv_along_fapp1_right_source_D0
omega_equiv_along_fapp1_right_target_D0 omega_equiv_along_fapp1_left_inv_D0
omega_equiv_along_fapp1_right_inv_D0
omega_equiv_along_fapp1_left_cell_to_D0
omega_equiv_along_fapp1_left_cell_evidence_D0
omega_equiv_along_fapp1_left_cell_D0
omega_equiv_along_fapp1_right_cell_to_D0
omega_equiv_along_fapp1_right_cell_evidence_D0
omega_equiv_along_fapp1_right_cell_D0 omega_equiv_along_fapp1_D0
idtoequiv_cat_functor_D1 idtoequiv_cat_fapp1_along_D1
idtoequiv_cat_fapp1_D1 is_discrete_cat_core_equiv_D0
discrete_core_homwise_D0 discrete_core_hom_inv_func_D0 hom_to_path_D0
discrete_core_hom_left_cell_D0 hom_to_path_path_to_hom_D0
path_to_hom_hom_to_path_D0
```

The seven retained compatibility reviewer examples are
`categorical_universe_identity.lp`, `equality_evidence_migration.lp`,
`omega_equiv_along_d0.lp`, `omega_equiv_along_d0b.lp`,
`omega_equiv_d1.lp`, `onecat_iso_lift.lp`, and
`product_reflexivity_provenance.lp`. P5 will make their legacy dependency
explicit. Main diagnostics will not import compatibility: legacy-only catalog
areas will be removed rather than keeping an authoritative second diagnostic
suite. This satisfies the P4 exit gate; every remaining legacy owner and
consumer has one selected extraction or retention disposition.

### Phase P4 — Consumer-led D0/D1 and decoder retirement

1. Inventory every remaining D0/D1 and unsuffixed legacy consumer by semantic
   role.
2. Migrate native-worthy operations.
3. Retain theorem-level library comparisons where useful.
4. Delete self-contained observation/debug experiments with no selected user,
   or mark them for compatibility extraction.
5. Migrate or retire Cat/Grpd decoder consumers independently; do not delete
   by spelling.
6. Remove obsolete conditional results superseded by unconditional native
   theorems when no compatibility consumer remains.

Exit gate: every remaining legacy symbol is explicitly classified for
mechanical extraction or deliberate theorem-level retention; active kernel
semantics no longer depend on opaque D0.

### Phase P5 — Mechanical compatibility extraction

1. Move the downstream-only compatibility block without semantic rewrites.
2. Add explicit imports only to retained legacy diagnostics/examples.
3. Verify that the kernel and native modules check in its absence.
4. Re-run warning and strict-audit comparisons to catch changed owner
   positions or accidental duplicate rules.

Exit gate: compatibility is one-way, opt-in, and absent from the active
kernel/native/WalkingEnd dependency closure.

#### P5 promotion record — 2026-07-19

- The validated owner-position extraction snapshots are
  `tmp/probes/paecr_p5_compat_extract_kernel_owner_full.lp` and
  `tmp/probes/paecr_p5_legacy_compat_owner_full.lp`. The promoted active
  kernel is byte-for-byte the former snapshot; the mechanically copied legacy
  block, with only its one-way import/header boundary added, is now
  `emdash3_2_legacy_compat.lp`.
- The extracted module currently has 2,751 lines and 126 declarations. It owns
  the complete P4 manifest: all D0/D1 declarations, the unsuffixed D0-backed
  packages/observers/decoders, Product/opposite/next-hom compatibility, and
  the complete two-sided OneCat theorem. No rule, unifier, or semantic body is
  duplicated across the boundary.
- The active kernel is 19,633 lines after the 2,564-line mechanical deletion.
  Exact search finds no D0/D1 declaration or reference in the kernel, native
  hom-action/evidence extensions, Nat, WalkingEnd, Sum refinement module, or
  main diagnostics. `emdash3_2_checks.lp` removed 2,238 legacy-only diagnostic
  lines and imports no compatibility module; retained ordinary Product-iso,
  D0-free groupoid-decoder, and native direct-EQ1 checks remain.
- Exactly seven reviewer examples import compatibility explicitly:
  `categorical_universe_identity.lp`, `equality_evidence_migration.lp`,
  `omega_equiv_along_d0.lp`, `omega_equiv_along_d0b.lp`,
  `omega_equiv_d1.lp`, `onecat_iso_lift.lp`, and
  `product_reflexivity_provenance.lp`. Their focused logs end in
  `20260720-000433`; no other `.lp` file imports the module.
- Bounded `make check` passes without checking or importing compatibility.
  The active-kernel warning inventory decreases mechanically to 1,010
  unjoinable and 159 replaceable reports. The explicit legacy-module probe
  `logs/probes/emdash3_2_legacy_compat-20260720-000503.log` restores the
  combined import-closure inventory to the former 1,016/159, showing that the
  six extracted critical-pair reports moved with their owners. The strict
  audit remains zero unreviewed candidates with 45 annotated slots across 27
  clauses. `git diff --check` passes.

This satisfies the extraction exit gate: compatibility is downstream-only,
explicit, and absent from every active foundational dependency path.

### Phase P6 — Compatibility deletion or bounded retention decision

1. Reassess whether any selected external/reviewer consumer warrants keeping
   the extracted module.
2. If not, delete the module, its self-only examples, and obsolete catalog
   areas.
3. If yes, document the exact retention contract, freeze the namespace, and
   keep it out of active authority claims.

Exit gate: there is no ambiguous second equivalence foundation.

#### P6 bounded-retention decision — 2026-07-19

The extracted module is retained temporarily, but under a closed contract:

1. it is frozen, opt-in, non-authoritative, and excluded from the ordinary
   kernel/native/check dependency closure;
2. only the seven explicitly legacy reviewer examples above may import it;
3. no new consumer, theorem family, feature, alias, or compatibility polish is
   permitted; fixes may only preserve its existing contract;
4. its sole selected mathematical retention reason is the complete two-sided
   `one_cat_iso_type_equiv` theorem and its specified inverse laws; and
5. it is deleted when native facade-package/raw-path reification coherence
   supports that theorem through a separately reviewed migration, or when
   repository backward compatibility is deliberately dropped.

The direct one-way ordinary-isomorphism lift already lives natively as
`iso_evidence_omega_along_EQ1`/`iso_evidence_omega_equiv_EQ1`. The focused P4
probe showed that the stronger OneCat round trip fails at the intentional
stable-cast/package reification boundary, even for reflexivity. Weakening the
theorem or inventing a proof-time package/path identification was rejected.
The frozen D0/D1/unsuffixed names therefore describe historical representation
inside one quarantined module, not an alternative foundation.

### Phase P7 — Native namespace migration

1. Inventory collisions between unsuffixed legacy names and native `_EQ1`
   names.
2. Select the public rename table and protected-helper policy.
3. Perform a synchronized symbol rename without semantic rule changes.
4. Rename modules/examples only when it improves the stable public
   architecture; do not mix unrelated file reorganization.
5. Update all active reports, comments, examples, catalog areas, and command
   documentation.

Exit gate: canonical native names are unsuffixed or the ledger records a new
evidence-backed reason to retain `_EQ1`; no stale mixed namespace remains.

#### P7 namespace decision — 2026-07-19

The canonical native `_EQ1` suffix is retained while the frozen compatibility
module exists. An exact declaration inventory over the active kernel and five
one-way native/library modules finds 139 native `_EQ1` declarations and zero
already-unsuffixed collisions inside the active closure. Stripping `_EQ1`
nevertheless collides with these 11 declarations exported by
`emdash3_2_legacy_compat.lp`:

```text
OmegaEquiv
OmegaEquivAlong
is_obj_trunc_cat_equiv_from
is_obj_trunc_cat_equiv_to
is_obj_trunc_cat_equiv_type_equiv
iso_evidence_omega_equiv
omega_equiv_along_obj_path
omega_equiv_along_obj_type_equiv
omega_equiv_evidence
omega_equiv_refl
omega_equiv_to
```

All seven legacy examples necessarily open both the active kernel and the
compatibility module. Renaming all native declarations would therefore create
real same-client collisions; renaming only the other 128 would replace one
coherent canonical namespace with a mixed suffixed/unsuffixed API. A reverse
alias layer would also recreate two equal-status surfaces and is rejected.

This is a final decision for the present plan, not an unmeasured deferral:
`_EQ1` remains the canonical native spelling until the frozen module is
deleted, or until a separate adopted migration first namespaces and rewrites
that legacy surface. P7 performs no semantic rule change and introduces no
alias. Current authorities and comments must consistently call `_EQ1` native
and the unsuffixed/D0/D1 surface frozen legacy compatibility.

### Phase P8 — Consolidation and final gates

1. Run focused probes for every changed owner and permanent sanity assertion
   for every new rule or unification equation, if any.
2. Run bounded checks, reviewer examples, warning summary, strict audit,
   catalog, TOC, health, and full CI in the SOP order.
3. Verify zero unclassified diagnostics and synchronized generated reports.
4. Re-read Foundations, current SOP, canonical syntax, INDEX, and this plan
   for stale compatibility claims.
5. Record final inventories, warning/audit deltas, rejected alternatives, and
   precise retained boundaries.

Exit gate: the selected plan is genuinely complete, all active authorities
agree, and the repository passes the proportional final gate.

#### P8 consolidation record — 2026-07-19

- Final exact inventory finds zero D0/D1 declaration or reference in the
  active kernel, native extensions, Nat, WalkingEnd, Sum refinement module, or
  main diagnostics. Exactly seven `.lp` files import the frozen compatibility
  module. The active native namespace contains 139 `_EQ1` declarations and
  the frozen module contains the 11 recorded unsuffixed collision bases.
- `EMDASH_TYPECHECK_TIMEOUT=60s make check` and the complete `make examples`
  sweep pass. Every legacy example checks the compatibility module through an
  explicit import; native-only examples do not load it.
- `make warning-summary` reports the expected active inventory of 1,010
  unjoinable critical pairs and 159 replaceable pattern variables. The P5
  explicit compatibility probe retains the former combined 1,016/159 closure.
  `make audit-rules` remains zero unreviewed candidates with 45 annotated
  slots across 27 intentional clauses.
- `make catalog` produces 1,791 classified checks—1,587 positive and 204
  negative—across 66 areas, with zero legacy source-line tags and zero
  unclassified statements. `make toc` passes at 86 headings across sections
  0–20 after removing the extracted 5f header entry. Active-reference and
  report-header lints pass.
- `make health` passes all 52 measured targets (seven active source modules and
  45 reviewer examples) in 258.540 seconds aggregate and writes the
  `2026-07-20T00:28:48-0400` health report. Compatibility remains outside the
  active source list but is checked transitively by all seven of its clients.
- Full `EMDASH_TYPECHECK_TIMEOUT=60s make ci` passes the same 52 targets in
  241.282 seconds aggregate, all 16 Infinity-Codex tests, Python/shell/JSON
  integrity, diff/TOC/reference/header checks, strict LHS audit, and strict
  catalog freshness. `git diff --check` passes and staged changes remain
  empty.

No rule or `unif_rule` was introduced by P5–P8. The only final source-map edit
removes the stale header entry for the Product omega-equivalence section that
moved mechanically to compatibility. All acceptance criteria are satisfied;
future deletion of the frozen module or removal of `_EQ1` requires a new
adopted migration at the exact P6/P7 boundary rather than reopening this plan
implicitly.

### Phase P9 — Correct canonical action and retire isolated Sum

P9 is a post-completion corrective phase. It supersedes the architectural
selection of P2 while preserving P2's dated probe evidence and every P3–P8
result.

1. Reproduce the exact current-owner consumer inventory and record the clean
   descendant baseline, bounded check, warning inventory, and strict audit.
2. In an owner-position full-kernel probe, remove the generic
   `PathActionRefinement` block, the PathRecord selected-action wrappers, the
   Nat selected-action proof-time basis/comparison family, and the complete
   isolated Sum former/action surface.
3. Verify that the kernel and all non-Sum active extensions still check and
   that WalkingEnd continues to consume `nat_succ_function`/`NatSucc_func`
   through canonical `path_map_func` action.
4. Promote the kernel deletion without replacement rewrites, unification
   rules, selected-action aliases, or local copies of canonical `eq_ap`.
5. Remove the three Nat refinement declarations from the Nat extension and
   delete the one-way Sum action module.
6. Delete refinement/Sum diagnostic areas and the obsolete
   `nat_observational_action`, `observational_action`, `binary_sum`,
   `sum_observational_equality`, and `sum_observational_action` reviewer
   examples. Move or add only the smallest canonical `path_map_func` checks
   needed at `examples/path_category.lp` or another existing canonical owner.
7. Remove the Sum module from active check/metrics wiring and remove Sum and
   refinement entries from `AGENTS.md`, current SOP, Foundations, and INDEX.
   Preserve dated history with explicit P9 supersession notes rather than
   rewriting old results as if they never existed.
8. Regenerate the strict check catalog and health report, then run the complete
   warning, audit, TOC, examples, and CI gate.

P9 invariants:

- direct `fapp1_fapp0(Path_cat(A),Path_cat(B),path_map_func(f),x,y,p)` remains
  checked and reduces to `eq_ap(f,p)`;
- full next-hom action remains available from the same functor through
  `fapp1_func`;
- `path_record_witness_action` remains direct `eq_apd`;
- `nat_succ_function` and `NatSucc_func` remain stable WalkingEnd inputs;
- no active `.lp` occurrence of `PathActionRefinement`,
  `path_action_refinement_*`, `path_record_action`, `nat_succ_path_action_*`,
  `nat_succ_ap_basis`, or a Sum declaration/reference remains;
- no active source, diagnostic, or reviewer example imports the deleted Sum
  module;
- P3–P8 native/compatibility namespace and module boundaries do not change.

Exit gate: exact-token inventories satisfy the invariants; the warning and
strict-audit deltas are explained by removed owners only; all retained
canonical-action, Nat, WalkingEnd, PathRecord-dependent, native-EQ1, and
legacy-contract checks pass; current authorities agree that selected action
and Sum are absent pending a future consumer-led redesign; full CI passes.

#### P9 adoption record — 2026-07-20

- The implementation starts from clean `HEAD`
  `20e286be55badc06da90d22bd7065dc5da2f2e63`, a descendant of the original
  `2444c9d406fc3d201602ace7af5105c20c241680` provenance. Staged and unstaged
  diffs were empty before this plan update.
- `EMDASH_TYPECHECK_TIMEOUT=60s make check` passes at that baseline.
- Exact inventory confirms that no arithmetic, WalkingEnd, native-EQ1,
  evidence-property, or frozen compatibility theorem consumes the selected
  Nat action or Sum. WalkingEnd uses only `nat_succ_function` and
  `NatSucc_func` from the relevant Nat slice.
- The entire Sum inventory is confined to `emdash3_2.lp`,
  `emdash3_2_checks.lp`, `emdash3_2_sum_observational_action.lp`, and the three
  Sum reviewer examples. The broader feature retirement is therefore
  dependency-ready.
- The ignored owner-position full-kernel deletion probe
  `tmp/probes/paecr_p9_canonical_action_sum_retire_owner_full.lp` passes both
  quiet and warning-enabled checks. Its logs end in `012142` and `012151`;
  warnings remain exactly 1,010 unjoinable/159 replaceable, so deletion adds no
  overlap family.
- The probed deletion was promoted without a replacement rule, `unif_rule`,
  alias, or local copy of `eq_ap`. The kernel removes the generic refinement
  block, PathRecord nondependent wrappers, comparison-only Nat basis and its
  two proof-time rules, and the complete Sum former. The Nat extension removes
  its three refinement declarations. The Sum extension and six examples whose
  only purpose was selected action or Sum are deleted.
- `emdash3_2_checks.lp` removes the matching diagnostic areas while retaining
  canonical path-map, direct dependent witness-action, native-EQ1, Nat,
  WalkingEnd, and compatibility-contract regressions. The updated
  `examples/path_category.lp` checks the object component, exact capped
  `eq_ap`, full `fapp1_func` next-hom action, function-equality action, and
  direct `eq_apd` witness transport.
- Exact active `.lp` search is empty for every retired refinement, Nat-basis,
  and Sum declaration/reference. `make check`, the focused warning-enabled
  path-category example, and the full `make examples` sweep pass.
- The regenerated strict catalog has 1,671 classified checks—1,496 positive
  and 175 negative—across 61 areas, with zero legacy tags and zero
  unclassified checks. The source TOC remains 86 headings across sections
  0–20; strict LHS audit remains zero unreviewed clauses/45 annotated slots/27
  intentional clauses.
- Generated health passes all 46 retained source/example targets in 198.158
  seconds aggregate. The kernel is 19,202 lines with 758 symbols, 602 rewrite
  rules, and 61 unification rules; the diagnostic suite has 1,496 assertions.
- Current authorities and dated decision ledgers are synchronized with the P9
  supersession. Full local CI passes all 46 retained targets in 253.673
  seconds, all 16 Infinity-Codex recovery tests, Python/shell/JSON validation,
  diff/TOC/reference/report-header integrity, the strict LHS audit, and strict
  catalog freshness. P9 is complete.

### Phase P10 — Delete the obsolete compatibility closure and its clients

P10 reopens the exact alternative left by P6. The extraction evidence remains
valid: the module is downstream-only, non-authoritative, and absent from every
active dependency path. What changes is the retention objective. The user has
explicitly selected the current native design and practical end results rather
than backward compatibility, so the P6 retention condition is now false.

The deletion closure is exactly:

```text
emdash3_2_legacy_compat.lp
examples/equality_evidence_migration.lp
examples/omega_equiv_along_d0.lp
examples/omega_equiv_along_d0b.lp
examples/omega_equiv_d1.lp
examples/onecat_iso_lift.lp
examples/categorical_universe_identity.lp
examples/product_reflexivity_provenance.lp
```

The reviewer-example disposition is deliberate rather than a filename-based
purge:

1. `equality_evidence_migration.lp` exists to compare D0 and native evidence;
   after D0 deletion it has no independent statement.
2. `omega_equiv_along_d0.lp`, `omega_equiv_along_d0b.lp`, and
   `omega_equiv_d1.lp` expose the old fixed-arrow, hom-action, and decoder
   presentations and are wholly legacy.
3. `onecat_iso_lift.lp` is the reviewer client for D0 package/path coherence
   and the complete legacy `one_cat_iso_type_equiv`; deleting that theorem
   deletes the example's selected purpose.
4. `categorical_universe_identity.lp` mixes native checks with legacy decoder
   comparisons, but its useful native content is already represented in
   `emdash3_2_checks.lp` and
   `examples/direct_univalence_eq1_boundary.lp`. It has no unique practical
   theorem to migrate.
5. `product_reflexivity_provenance.lp` mixes ordinary Product-isomorphism
   checks with D1 Product evidence, but its retained ordinary-isomorphism
   content is already owned by the main Product diagnostic area. It likewise
   has no unique practical theorem to migrate.

No file in this deletion closure mentions WalkingEnd, `BNat`, Nat, or the Nat
extension. The active kernel, native extensions, Nat, WalkingEnd, and main
diagnostics neither import nor reference the compatibility module. Deletion
therefore cannot remove the selected walking-endomorphism/Nat correspondence;
that claim remains subject to the full checks and examples rather than lexical
evidence alone.

#### OneCat boundary selected by P10

The phrase “delete the legacy OneCat theorem” does not mean deleting OneCat.
The following current structures and results remain selected:

- `OneCat` and its evidence-retaining finite-dimensional packaging;
- `one_cat_hom_discrete` and the native iterated hom action;
- native equality-valued groupoidality and the finite-`NCat`
  object-truncation/evidence-property results;
- the native one-way ordinary-isomorphism lift currently spelled
  `iso_evidence_omega_along_EQ1` and
  `iso_evidence_omega_equiv_EQ1` before P11;
- WalkingEnd/`BNat`, their Hom--Nat comparison, sethood, and directed negative
  results.

What is deleted is the exact D0-based equivalence
`one_cat_iso_type_equiv` and its compatibility-specific two-sided decoder
laws. The prior native feasibility probe established a valid one-way native
lift but not the stronger stable-facade-package/raw-path reification equality.
P10 neither weakens that theorem nor invents a proof-time identification to
keep its old name. It simply removes an unused legacy theorem. A future
fully-native object-equality/ordinary-isomorphism equivalence is optional
research, to be introduced under its own consumer-led plan if it becomes
useful.

P10 implementation sequence:

1. preserve the P5 extraction manifest and P6 decision as dated evidence;
2. delete the compatibility module and all seven explicit importers in one
   bounded slice so no broken compatibility client is left behind;
3. remove the module and examples from current authority, architecture,
   source-health, and reviewer-surface claims;
4. verify exact zero active occurrences of `legacy_compat`, `_D0`, `_D1`, and
   `one_cat_iso_type_equiv` before starting the namespace edit;
5. run `make check` immediately, then let P12 exercise the full retained
   reviewer and CI surface.

P10 introduces no symbol, rewrite rule, unification rule, alias, or replacement
theorem. Its exit gate is a closed native dependency graph with no legacy
module/client and with the retained OneCat and WalkingEnd/Nat checks passing.

### Phase P11 — Make the native equality-valued API unsuffixed

P11 reopens the exact P7 namespace boundary after P10 removes its only
collision source. At the adoption baseline, excluding the compatibility
module and its seven clients, the active `.lp` surface contains:

```text
18 files
1,570 occurrences of exact *_EQ1 identifiers
143 distinct exact *_EQ1 identifiers
139 explicitly declared implementation owners
1 explicitly declared reviewer-local helper
0 declaration collisions after stripping the suffix
```

The remaining distinct tokens include generated/referenced eliminator and
projection names rather than additional public declarations. The one
reviewer-local declaration is
`consume_omega_equiv_along_fapp1_EQ1`. The old set of 11 hard collisions was
exported entirely by `emdash3_2_legacy_compat.lp`; after excluding P10's
deletion closure, an exact comparison of every stripped native declaration
with every existing unsuffixed declaration is empty.

The frozen mechanical mapping is:

```text
for each exact Lambdapi identifier NAME_EQ1 in the retained active .lp set:
  NAME_EQ1  ->  NAME
```

The edit must use identifier boundaries, not unrestricted substring
replacement. It applies synchronously to declarations, generated-name
references, rules, assertions, and retained reviewer examples. It does not:

- add old-to-new or new-to-old aliases;
- retain selected `_EQ1` names as a partial namespace;
- change term bodies, argument order, rewrite orientation, ownership, or
  module dependencies;
- rename conceptual prose merely because it uses “EQ1” to describe the
  equality-valued representation;
- rename the two `emdash3_2_eq1_*.lp` module files in this phase; or
- blindly rewrite dated reports whose suffixed spellings are part of true
  historical promotion evidence.

P11 implementation sequence:

1. re-run the collision manifest after P10 and stop if it is nonempty;
2. record the exact retained file list and counts;
3. apply the exact automated mapping to all retained `.lp` owners and clients
   as one mechanical namespace edit;
4. verify zero `_EQ1` identifier occurrences in active `.lp` files and zero
   references to deleted compatibility names;
5. run `make check` before editing current prose, so any missed generated name
   or hidden collision is isolated to the namespace slice;
6. update current authorities and examples to the new unsuffixed spellings,
   while adding explicit P10/P11 supersession notes to dated ledgers instead
   of falsifying their recorded historical names.

The renamed unsuffixed API is the same native equality-valued representation,
not a return to the old unsuffixed decoder design. For example,
`OmegaEquivAlong` after P11 denotes the current equality-valued Sigma evidence
that was previously named `OmegaEquivAlong_EQ1`; there is no surviving D0
alias with that spelling.

P11 introduces no semantic rule change. Its exit gate is an exact-zero active
`_EQ1` identifier inventory, a passing active check, and a single unsuffixed
native public surface.

### Phase P12 — Synchronize authorities and complete the final gate

P12 makes the semantic distinction visible everywhere current architecture is
described:

1. remove the deleted module and seven examples from `AGENTS.md`, `README.md`,
   `reports/INDEX.md`, Foundations, the current SOP, source-health data, and
   current command/architecture inventories;
2. update current symbol references to the P11 unsuffixed names;
3. state that native OneCat infrastructure and the one-way ordinary-iso lift
   remain, while the old complete `one_cat_iso_type_equiv` theorem is absent
   and any fully-native replacement is optional future work;
4. annotate the equality-valued redesign, observational-equality redesign,
   and WalkingEnd ledgers where necessary so their dated `_EQ1`, P6, or P7
   claims are explicitly superseded without rewriting historical evidence;
5. regenerate the strict catalog and health report; and
6. run the bounded active check, all retained examples, warning summary,
   strict rule-LHS audit, catalog, TOC, health, full CI, reference/header
   integrity, and `git diff --check`.

Expected structural deltas are deletion-only or spelling-only: seven fewer
reviewer examples and one fewer non-authoritative source file, unchanged active
kernel diagnostics, unchanged warning/audit behavior except for any reporting
text keyed by renamed symbols, and no new computation owner. Any different
semantic delta must be investigated and recorded before completion.

#### P10–P12 adoption record — 2026-07-20

- Implementation starts from clean `HEAD`
  `34708ca2547a6d54af2e9b67f9f605a2bcb9a4a9`, a descendant of the original
  `2444c9d406fc3d201602ace7af5105c20c241680` implementation/review baseline.
  Staged and unstaged diffs were both empty before this ledger update.
- `EMDASH_TYPECHECK_TIMEOUT=60s make check` passes at that baseline.
- The compatibility dependency inventory is unchanged from P5: exactly seven
  reviewer examples import the module, and no active authority imports it.
- Exact search finds no WalkingEnd, `BNat`, Nat, or Nat-extension identifier in
  the compatibility module or its seven clients.
- The P10 consumer classification above finds no unique selected native result
  in the two mixed examples; the corresponding native categorical-universe and
  ordinary Product-isomorphism diagnostics already have retained owners.
- The reproduced post-deletion collision simulation covers 18 retained `.lp`
  files, 1,570 occurrences, and 143 distinct suffixed identifiers. It finds
  139 implementation declarations, the one local reviewer helper, and zero
  stripped-name collision. P10 and P11 are therefore dependency-ready.
- P10 deletes the exact eight-file closure. Post-deletion search is empty for
  the compatibility import/module name, every exact D0/D1 identifier, and
  `one_cat_iso_type_equiv`; the immediate bounded active check passes. No
  symbol, theorem replacement, rule, `unif_rule`, or alias is added.
- P11 applies the frozen identifier-boundary mapping to the 18 retained files.
  Post-migration active `.lp` search is empty for exact `_EQ1`, `_D0`, and
  `_D1` identifiers, and `make check` passes. The two lowercase `eq1` module
  filenames and three reviewer filenames remain architecture/history labels;
  public declarations and references are wholly unsuffixed.
- The catalog generator drops dead Sum/D0 migration classifiers and recognizes
  the unsuffixed native owners. The regenerated strict catalog remains 1,671
  checks—1,496 positive and 175 negative—across 61 areas, with zero legacy
  tags and zero unclassified checks.
- All 33 retained reviewer examples pass. This includes the current native
  categorical-universe, ordinary Product-isomorphism, OneCat/dimension,
  WalkingEnd/`BNat`, Hom--Nat, Nat, evidence-property, and path-action owners;
  no statement had to be copied out of either deleted mixed legacy example.
- Warning inventory is unchanged at 1,010 unjoinable critical pairs and 159
  replaceable pattern variables. Strict LHS audit remains zero unreviewed
  clauses with 45 annotated slots across 27 intentional clauses. The source
  TOC remains 86 headings across sections 0–20.
- Generated health passes all 39 retained targets—six active source/diagnostic
  modules and 33 reviewer examples—in 120.169 seconds aggregate. The kernel
  has 19,201 lines, 758 symbols, 602 rewrite rules, and 61 unification rules;
  the one-line delta from P9 is comment-only. Main diagnostics retain 1,496
  assertions.
- `AGENTS.md`, README, INDEX, current SOP, Foundations, the three affected
  historical ledgers, catalog, and health report are synchronized. Historical
  D0/D1/`_EQ1` spellings remain only with explicit supersession context; the
  current glossary, authorities, and operational classifier use unsuffixed
  native names.
- Full local CI passes all 39 targets in 133.036 seconds aggregate, all 16
  Infinity-Codex recovery tests, Python/shell/JSON validation, diff/TOC/
  active-reference/report-header integrity, strict LHS audit, and strict
  catalog freshness. `git diff --check` passes. P10–P12 are complete.

## Acceptance Criteria

The plan is complete only when all selected criteria hold:

1. `Path_cat_func`/`path_map_func` are documented consistently as the
   canonical iterable raw-function path action.
2. `ObsDAction` is absent unless a concrete displayed-structure consumer and
   separately adopted design justify it.
3. No generic nondependent selected-action/refinement registry remains;
   ordinary action uses `fapp1_fapp0(path_map_func(f),p)` directly.
4. No alternate selected presentation competes with or wraps generic
   `fapp*`/`tapp*` functoriality without a separately adopted measured
   consumer.
5. Nat and WalkingEnd retain canonical `NatSucc_func` behavior, PathRecord
   dependent witness transport remains direct `eq_apd`, and the isolated Sum
   feature is absent pending later redesign.
6. The active discrete/dimension/WalkingEnd spine uses native equality-valued
   groupoidality, not D0 compatibility.
7. Active kernel and native modules do not import an extracted compatibility
   layer.
8. `emdash3_2_legacy_compat.lp` and its seven explicit clients are absent;
   every old Cat/Grpd decoder in that closure is deleted rather than retained
   as a second library interface.
9. Native `TypeEquiv`, contractible-fibre, categorical-universe, Product-iso,
   and ordinary-isomorphism-lift results with current consumers remain even
   though their redundant legacy comparisons are deleted.
10. The exact D0-based `one_cat_iso_type_equiv` and compatibility-specific
    inverse laws are absent, while native `OneCat`, hom discreteness/action,
    finite-dimension, and WalkingEnd/Nat behavior remain checked.
11. `_D0` and `_D1` do not remain as an ambiguous second foundation in active
    `.lp` files or current authority claims.
12. `_EQ1` is removed by one collision-free exact identifier migration, with
    no partial namespace or compatibility aliases.
13. Equality-valued module filenames may retain `eq1` as architecture labels;
    no file split/rename is mixed into the public-symbol migration.
14. No semantic migration is combined with an unvalidated file split.
15. No promoted code uses `--no-sr-check`, an untyped proof-time comparison,
    or an unmeasured broad rewrite.
16. Every new rule or `unif_rule`, if unavoidable, has focused positive,
    negative, runtime/proof-time, warning, and subject-reduction evidence.
17. Current authorities use the unsuffixed native spelling; dated plans retain
    historical spellings only with explicit P10/P11 supersession context.
18. `make check`, affected examples, catalog, health, warning summary, strict
    audit, and `make ci` pass at final handoff.

## Probe And Validation Matrix

| Slice | Minimum focused evidence | Proportional repository gate |
| --- | --- | --- |
| documentation/adoption | exact-token and authority comparison | bounded `make check` |
| `ObsDAction` retirement | direct `eq_apd` owner-position full-file probe; PathOver formation and computation | `make check`; observational-action reviewer example |
| canonical-action correction | owner-position deletion probe; direct capped/full path action; Nat/WalkingEnd and direct-`eq_apd` PathRecord consumers; zero retired-token inventory | `make check`; affected examples; warning comparison; strict audit; catalog/health |
| native discrete spine | native `IsDiscreteCat` formation/projections; homwise path/retract consumers; import-cycle control | kernel/native/walking checks; directed/discrete/groupoidal/walking examples |
| D0/D1 consumer migration | one probe per semantic owner; decoder and provenance controls | affected examples; warning summary; strict audit; catalog |
| compatibility extraction | dependency/import inventory; no-duplicate-owner check | `make check`; `make examples`; warning/audit comparison |
| compatibility deletion | exact eight-file closure; retained-result duplicate/consumer inventory; zero legacy-token search | immediate `make check`; retained OneCat/WalkingEnd/Nat examples; full reviewer sweep |
| namespace migration | exact collision inventory; mechanical-definition equality | full examples, catalog, TOC, health, CI |
| final consolidation | all permanent diagnostics and negative controls | full `make ci` |

Typechecks must remain bounded by the repository timeout policy. A quiet
timeout or hidden interaction must be reduced to the smallest owner and
rerun with relevant warnings/debug flags before a candidate is rejected.

## Risks And Mitigations

### Risk 1: an optional first-action presentation is retained as infrastructure

Mitigation: keep `path_map_func` as the only functor and remove the generic
selected-action package. Reintroduce any exceptional presentation only at a
measured local consumer, with no claim that it supplies a higher-action tower.

### Risk 2: selected computation is installed as competing runtime action

Mitigation: expose no selected-action projection in the active API. Use the
canonical `fapp1_fapp0` value directly and do not add a generic rewrite from
PathMap action to an alternate term.

### Risk 3: `ObsDAction` deletion is overstated as displayed functoriality

Mitigation: retain direct `eq_apd` behavior and state the future displayed
section prerequisite explicitly.

### Risk 4: suffix inventory is mistaken for semantic dependency inventory

Mitigation: search unsuffixed aliases, types, bodies, imports, examples, and
normal forms. Treat `OmegaEquivAlong := OmegaEquivAlong_D0` as legacy even
without a suffix at the use site.

### Risk 5: native migration creates a dependency cycle

Mitigation: probe module ownership before moving code. Prefer kernel
formation plus one-way derived homwise consumers and an explicit WalkingEnd
import over copying the 2,400-line native hom-action proof into the kernel.

### Risk 6: compatibility deletion removes useful theorem-level APIs

Mitigation: classify representations, computational adapters, decoders,
round trips, and practical consumers separately. Retain selected native
library mathematics under native statements. Do not manufacture a native
replacement for the unused legacy `one_cat_iso_type_equiv` merely to make
deletion look like migration; record a future full native theorem as optional.

### Risk 7: `_EQ1` rename obscures semantic regressions

Mitigation: perform it only after semantic retirement, as a standalone
mechanical migration with a frozen rename table and full gates.

### Risk 8: documentation history is rewritten rather than corrected

Mitigation: update current-status claims and add supersession notes to older
sections while preserving dated negative/probe evidence that was true at its
checkpoint.

### Risk 9: large cleanup destroys proof provenance

Mitigation: preserve generic `eq_refl`, shaped reflexivity, decoder negatives,
and runtime/proof-time distinctions until their exact replacement has passed
the corresponding controls.

## Side-Task Ledger

| Task ID | Status | Objective | Dependency | Exit evidence |
| --- | --- | --- | --- | --- |
| `PAECR-P0-AUTHORITY-SYNC` | **completed 2026-07-19** | adopt plan, repair stale PathMap claims, record baselines/inventory | current clean baseline | INDEX/SOP/Foundations/WalkingEnd/equality-plan wording synchronized; bounded check, 1,016/159 warning inventory, zero/45/27 LHS audit, and exact three-file dependent-registry inventory recorded |
| `PAECR-P1-OBSD-RETIRE` | **completed 2026-07-19** | replace canonical dependent registry use with direct `eq_apd` and delete dead package | P0 | owner-position quiet/warning probes pass; active `.lp` inventory is zero; direct PathOver formation/agreement checks and ten-statement reviewer example pass; warnings/audit unchanged; 2,074/77 catalog, 55-target health, and full CI pass |
| `PAECR-P2-PATH-REFINEMENT` | **completed 2026-07-19** | introduce `PathActionRefinement` over canonical `path_map_func` | P1 and active PathMap owners | owner-position generic/Nat/Sum and focused consumer probes pass; old active `.lp` token inventory is zero; identity joins and composition propositional/non-conversion controls are permanent; warnings/audit unchanged; 2,077/77 catalog, 55-target health, examples, and full CI pass |
| `PAECR-P3-NATIVE-DISCRETE` | **completed 2026-07-19** | migrate `IsDiscreteCat`, hom-to-path, dimension, and WalkingEnd consumers off D0 | native hom-action extension | native kernel formation/projection; derived EQ1 homwise path/retract API; D0-free WalkingEnd/BNat; owner-position kernel/native/Nat/Walking/evidence plus focused probes; 2,079/77 catalog, 55-target health, warnings/audit unchanged, full CI pass |
| `PAECR-P4-D0-CONSUMERS` | **completed 2026-07-19** | migrate, retain, or delete each D0/D1/decoder consumer by role | P3 | native ordinary-iso and categorical-truncation theorems promoted; incidental Unit/Bool/Nat/Sum/PathRecord consumers migrated; self-only views deleted; exact 54-D0/six-D1 plus unsuffixed extraction manifest and seven explicit compatibility examples recorded; OneCat retained only for missing package/path coherence |
| `PAECR-P5-COMPAT-EXTRACT` | **completed 2026-07-19** | mechanically isolate downstream compatibility after semantic migration | P4 | 2,751-line/126-declaration one-way module; active kernel/native/check closure has zero D0/D1 or compatibility import; seven explicit legacy examples pass; active 1,010/159 versus combined 1,016/159 warnings; audit zero/45/27 |
| `PAECR-P6-COMPAT-DECIDE` | **completed with bounded retention 2026-07-19** | delete compatibility or record bounded opt-in retention | P5 | frozen non-authoritative module, seven-consumer ceiling, no new features; retained only for complete OneCat two-sided theorem pending native package/raw-path coherence or deliberate compatibility deletion |
| `PAECR-P7-NAMESPACE` | **completed with `_EQ1` retained 2026-07-19** | remove `_EQ1` after collisions are freed, or record reason to retain | P6 | 139 native declarations inventoried; 11 hard unsuffixed legacy collisions; partial rename and reverse aliases rejected; canonical suffix frozen until compatibility deletion/namespacing |
| `PAECR-P8-CONSOLIDATE` | **completed 2026-07-19** | final reports/catalog/health/warnings/audit/CI | all selected phases | 1,791/66 strict catalog; 52-target health and CI; 1,010/159 warnings; zero/45/27 audit; 86-heading TOC; reference/header/diff integrity and 16 recovery tests pass |
| `PAECR-P9-CANONICAL-ACTION-SUM-RETIRE` | **completed 2026-07-20** | supersede P2's unconsumed refinement abstraction, use canonical path action directly, and retire isolated Sum pending redesign | completed P2 inventory plus canonical G2 owner | owner-position quiet/warning deletion probes pass at unchanged 1,010/159; promotion and exact-zero active inventory pass; check/examples, 1,671/61 strict catalog, 46-target health, 86-heading TOC, and zero/45/27 audit pass; full CI passes all 46 targets in 253.673s plus every repository-integrity gate |
| `PAECR-P10-COMPAT-DELETE` | **completed 2026-07-20** | supersede P6's backward-compatibility assumption; delete the frozen D0/D1/decoder module, seven clients, and exact legacy OneCat theorem | completed P5 extraction plus explicit user selection | exact eight-file deletion promoted; zero active compatibility/D0/D1/legacy-OneCat inventory; immediate check and all retained OneCat/WalkingEnd/Nat/Product/universe examples pass; no replacement theorem/rule/alias |
| `PAECR-P11-NATIVE-UNSUFFIX` | **completed 2026-07-20** | supersede P7 after P10; map every retained exact `NAME_EQ1` identifier to collision-free `NAME` without aliases or semantic edits | P10 deletion | exact 18-file/1,570-occurrence/143-token migration with 139 implementation declarations plus one example helper; zero stripped collision and zero active suffix inventory; bounded/full checks pass; module filenames unchanged |
| `PAECR-P12-CONSOLIDATE` | **completed 2026-07-20** | synchronize current authorities and supersession records, regenerate reports, and pass proportional final gates | P10 and P11 | current authorities and three dated ledgers synchronized; 1,671/61 strict catalog, 39-target health/CI, 1,010/159 warnings, zero/45/27 audit, 86-heading TOC, 16 recovery tests, and every integrity gate pass |
| `PAECR-DISPLAYED-PATH-SECTION` | deferred research | design honest dependent path-family displayed functor/section | concrete consumer | separately adopted plan and owner probes |
| `PAECR-NATIVE-ONECAT-ISO-EQUIV` | deferred optional research | if a future consumer warrants it, state and prove a fully native object-equality/ordinary-isomorphism equivalence without restoring D0 compatibility | concrete native consumer and separate adoption | native theorem and coherence probes; not a P10/P11 completion prerequisite |
| `PAECR-TYPEEQUIV-LIBRARY` | retained boundary | preserve useful contractible-fibre equivalence theorems independently of primary universe identity | consumer review | explicit library classification |

Only update a row to complete after its exit evidence is promoted and
recorded. Add newly discovered prerequisites or rejected alternatives here
rather than hiding them in conversational handoff.

## Recommended First Implementation Slice

The first bounded slice is P0 followed by P1:

1. synchronize the contradictory `PathMap` documentation and register this
   plan;
2. reproduce a direct-`eq_apd` PathRecord witness-action probe at the current
   owner position;
3. retire `ObsDAction` if that probe and its affected checks/example pass;
4. stop and record the slice before introducing `PathActionRefinement`.

This is dependency-ready, validates the smallest cleanup claim, and avoids
mixing the nondependent action API redesign with the first deletion.

Completion result (2026-07-19): this first bounded slice passed every exit
gate and is promoted. P2 subsequently completed without recreating the
dependent package. The next continuation starts from P3 and must preserve
`PathActionRefinement` as optional data while migrating the discrete/dimension
spine independently.

Current supersession (2026-07-19): P3–P8 are also promoted. Compatibility is
mechanically extracted and frozen under the exact P6 contract, and `_EQ1` is
retained for the evidenced P7 collision reason. P8 synchronized every active
authority and generated report and passed the full final gate. No plan row
remained open at that checkpoint.

Completed corrective slice (2026-07-20): P9 closed the only reopened row. Its
implemented bounded slice was:

1. reproduce the canonical-action, selected-action, Nat, PathRecord, and Sum
   inventories at their current owners;
2. validate the complete deletion in an owner-position kernel probe;
3. promote the kernel/Nat/module deletion and immediately restore
   `make check`;
4. migrate diagnostics, examples, wiring, and current authorities without a
   compatibility alias;
5. run the proportional final gate and append the exact evidence to P9.

The P2 record is retained as dated implementation evidence but its
`PathActionRefinement` conclusion is superseded. No continuation should
preserve that package merely because P2 once passed its gate. No row in this
plan remained open at the P9 checkpoint; future Sum or displayed-dependent
action work still requires a new consumer-led adoption rather than implicit
reopening.

Completed corrective slice (2026-07-20): P10–P12 supersede that last sentence
at the exact compatibility boundary. The dependency-ready implementation is:

1. delete the isolated compatibility module and its seven importers, including
   the old complete OneCat theorem rather than blocking on a native re-proof;
2. verify the retained native OneCat, WalkingEnd/BNat, Nat, finite-dimension,
   categorical-universe, and Product results by their current owners;
3. re-run the collision manifest and mechanically map every exact retained
   `NAME_EQ1` identifier to `NAME` in one synchronized `.lp` edit;
4. restore `make check` before changing prose, then synchronize current
   authorities and annotate historical ledgers with P10/P11 supersession;
5. regenerate catalog/health data and run the complete proportional gate.

P10 deletes the exact closure, P11 promotes the collision-free unsuffixed
namespace, and P12 passes the complete gate recorded above. No native theorem
construction, new rewrite, alias, module rename, or compatibility facade was
part of the slice. No plan row remains open; any fully native two-sided OneCat
equivalence or future Sum/displayed-action work requires a new consumer-led
adoption.

## Completion And Blocker Policy

Difficulty, proof length, warning count, or a slow full check is not by itself
a blocker. A blocker must name the exact desired term/rule/theorem, the
smallest failing owner-position probe, the failure class, and the prerequisite
that would change the result. If one phase is blocked, pursue any independent
dependency-ready side task and record both results in this ledger.

Do not mark the plan complete while a selected compatibility dependency,
stale authority claim, unsynchronized generated report, or required gate
remains. If evidence invalidates the proposed representation or sequencing,
revise this living plan before promoting a different architecture.

## Recovery And Future Handoff

The implementation starting baseline and review provenance is
`2444c9d406fc3d201602ace7af5105c20c241680`. It never authorizes reset or
rollback. Work from the current state when it is that commit or a descendant,
including temporary checkpoints.

On every continuation:

1. inspect staged and unstaged work separately;
2. re-read the active authorities and this plan rather than relying on a
   compacted summary;
3. resolve any explicitly linked Infinity Codex decision response when one is
   later added;
4. relocate affected symbols with `rg`;
5. reproduce the relevant bounded baseline and owner-position probe;
6. preserve unrelated user work;
7. continue the next dependency-ready ledger row;
8. synchronize this report, INDEX, current SOP, Foundations, checks, examples,
   catalog, health, warnings, and audit in proportion to the promoted change.

Ignored probes and logs remain evidence, not implementation authorities.
Promoted code must live in the active owner modules with permanent diagnostic
coverage.
