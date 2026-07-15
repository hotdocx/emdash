# EMDASH v3.2 Observational Equality, Truncation, And Univalence Redesign Plan

Date: 2026-07-13
Last reviewed: 2026-07-15
Plan-ID: EMDASH-V3-2-OBSERVATIONAL-EQUALITY-TRUNCATION-UNIVALENCE-REDESIGN-2026-07-13
Depends-On: EMDASH-V3-2-GROUPOID-COMPUTATIONAL-UNIVALENCE-2026-06-23; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Supersedes: no whole report yet; proposes the successor architecture for the active groupoid/computational-univalence track after review and staged approval
Side-Task-Ledger: #side-task-ledger
Implementation-Handoff: #implementation-handoff-start-here
Current-Implementation-Slice: none started; default next slice is OETU-ELEMENTARY-HOTT / Candidate G
Infinity-Codex-Origin: current-session-analysis-2026-07-13
Infinity-Codex-Decision-Responses: current-session-user-direction-2026-07-13-and-2026-07-14; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f5d7c-3fd0-7932-a38e-48985ba4bda0; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f618e-041a-77d2-ad93-31d04d584fa2; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f61d1-7ce1-7272-8082-bf22c8ba6047; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f625c-22a9-7350-8aea-3f06d4784bec; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f6282-d8ef-79f3-8735-aad1435e0b05; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f6293-83c1-70a0-817b-9128a37151c0; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f62b3-d3c8-7b12-9b33-a10d1d0950fe; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f62e3-db49-7653-8b49-ca98cd9015a7; infinity-codex:019f6392-0363-7e80-8a61-c05a8a667912:019f6396-f48c-75a0-852b-71a827ee0a7f; infinity-codex:019f6392-0363-7e80-8a61-c05a8a667912:019f644e-f14e-70f1-9402-19d688282343
Status: handoff-ready revised proposed staged redesign; the review, append-only feasibility pass, full-file `Path_cat` composition/collapse-removal audit, a minimal owner-position path-symmetry-functor audit, and the proof-time-unification trust-boundary audit are complete, Candidate G is the default first implementation slice, Candidate D is split into a D0 recursive-owner feasibility gate and a D1 public normal-form migration, Candidate E is split into E0 composition/collapse removal and E1 symmetry-core promotion with later fixed-map equivalence packaging, the exact Product boundary for `IsDiscreteCat` is selected with its homwise adequacy theorem still a promotion gate, groupoid/categorical decoder ownership is split around D1 and separated from `TypeEquiv` algebra, the hybrid generic/shaped equality contract is explicit, and the immediate MVP is distinguished from the eventual full-observational endpoint; no redesign kernel migration has yet started or been promoted, so the current implementation remains the active draft until individual slices are owner-position probed, diagnosed, and accepted

## Goal

Replace the current first-draft groupoid/univalence architecture with a staged
program whose eventual target is full observational equality and computational
univalence, while introducing the truncation and finite-dimensional structure
needed to state the mathematics correctly.

The program must integrate four concerns that should no longer be developed in
isolation:

1. observational equality for functions, dependent pairs, records, universes,
   and later inductive/coinductive structures;
2. HoTT truncation levels and the universes of propositions, sets, and
   `n`-groupoids;
3. directed `n`-categories, especially an ordinary/univalent `OneCat` layer;
4. one coherent computational-univalence interface at the groupoid and
   categorical levels.

The near-term objective is not to implement this whole program at once. It is
to settle the dependency structure, select canonical owners, identify small
feasible slices, and prevent the current draft rules from becoming accidental
permanent foundations. A second objective is to maintain an executable
foundational-adequacy benchmark: the minimal introductory HoTT kernel and its
immediate category/omega-category analogues must remain expressible, with
explicit prerequisites where the active file does not yet contain the needed
classifier, constructor, action, or eliminator.

The immediate H0/H1/Omega0 MVP is deliberately smaller than the eventual
full-observational endpoint. In particular, the MVP may use the current
univalence encoder/decoder and transport interface without yet making public
universe equality reduce directly to equivalence data. That later universe-
identity problem remains an explicit research and implementation track rather
than an unacknowledged requirement of the first milestone.

External systems and papers are comparative baselines, sources of examples,
and design inspiration only. They do not specify an implementation target to
copy. The selected owners must be rediscovered in the local Kosta--Došen/
Emdash cut-elimination architecture and the Lambdapi distinction between
runtime rewrites and proof-time unification. A simpler or more computational
local formulation is preferred whenever it passes the same adequacy and
coherence tests.

## Implementation Handoff: Start Here

This section is the operational entry point for a new conversation or agent.
It summarizes the intended endpoint, the exact current status, the evidence
that may be reused, the default first slice, and the update protocol. The rest
of this report contains the detailed architecture, alternatives, risks,
phases, benchmark matrix, and acceptance criteria. No Infinity Codex response
or raw conversation archive is required to begin implementation; those items
are provenance only.

### Original intent and wanted endpoint

The wanted end state is not merely a few additional univalence rules. It is a
computational foundation in which:

- full observational equality is available for the ordinary HoTT/MLTT core,
  including Pi, Sigma, finite dependent records, universes, and eventually
  inductive, coinductive, and higher-inductive formers;
- equality has a deliberate hybrid generic/shaped architecture: an unknown or
  unsupported classifier retains the ordinary primitive `=`/`eq_refl`/`J`
  interface and literal-reflexivity beta, while a registered shaped former may
  additionally decompose equality, reflexivity, action/substitution, and
  dependent elimination through coherent former-specific owners;
- truncation properties, `Prop`/`Set`/ordinary-groupoid universes, directed
  `n`-categories, `OneCat`, and their universe packages are stated without
  conflating homotopy truncation with directed categorical dimension;
- groupoid and categorical univalence use one operational decoder per layer,
  and categorical equivalence is usable over an already-named arrow through
  primary `OmegaEquivAlong(F)` evidence plus a Sigma-packaged first-class
  equivalence;
- all active `C : Cat` continue to be treated as univalent, while the
  unstratified `Cat_cat : Cat` policy (often abbreviated “`Cat : Cat`”),
  universe stratification, consistency, general semantic models, and complete
  normalization/canonicity proofs remain explicitly outside the concrete MVP;
- the minimal introductory HoTT kernel and the immediately corresponding
  category/omega-category notions are executable, with at least one witness
  iterating through the next hom level; and
- Lambdapi rewrite rules provide selected runtime computation while narrowly
  typed `unif_rule`s may provide selected proof-time definitional equations.
  They never masquerade as runtime normalization, and—because Lambdapi does
  not sanity-check them—their semantic justification and trust class are
  recorded explicitly rather than inferred from a successful typed
  `eq_refl` consumer.

The staged milestones used throughout the report are:

`H0` denotes the decoded dependent type-theory core, `H1` its standard
univalent HoTT compatibility surface, `H2` truncation reflectors and broader
higher-constructor readiness, and `Omega0` the first directed
category/omega-category extension that remains iterable at the next hom level.
The later adequacy matrix gives the complete per-former inventory.

| Milestone | Required content |
| --- | --- |
| Architecture MVP | Every H0/H1/H2/Omega0 row has an honest owner, prerequisite, or deferral, and no selected interface blocks the wanted endpoint. |
| Foundational implementation skeleton | H0 formation, decoding, elimination, beta, ordinary identity, and negative diagnostics are active; the exact H1/Omega0 boundary is recorded. |
| Foundational HoTT MVP | H1 is active, including standard Pi/Sigma/record path compatibility and ordinary equivalence/univalence algebra, and one integrated fixed-map Omega0 univalence/action witness passes. |
| H2/HIT completion | Truncation reflectors and representative higher constructors have their restricted eliminators and computation; this is intentionally later. |

Direct computational universe identity is not an extra hidden gate on the
foundational HoTT MVP. H1 requires the standard `idtoequiv`/decoder round trips
and selected transport/action computation. Making `A = B` itself expose
equivalence/bisimulation data belongs to the later full-observational track.

### Current handoff status and feasibility verdict

The current kernel has **not** been migrated by this plan. It still contains
the useful but hybrid first-draft equality, `OmegaEquiv`, category-univalence,
and adjunction interfaces described under “Current Baseline And Review
Findings.” The plan is ready for bounded implementation slices, but is still a
proposed successor until its adoption/migration record is made explicit.

| Track | Status at this handoff | Next status-changing result |
| --- | --- | --- |
| Plan review and dependency architecture | handoff-ready proposed design; every benchmark row is classified | Accept names/boundaries as each slice is promoted; formally adopt the successor plan and update the June 23 plan when appropriate. |
| H0 elementary core | partly active (`Unit`, Pi, Sigma, equality; native `nat`), but decoded Empty/Bool/Nat are missing | Complete Candidate G with owner-position evidence and durable active checks. |
| H1 ordinary HoTT compatibility | incomplete/hybrid | Complete Pi equivalence packaging, arbitrary Sigma/record round trips, `TypeEquiv` algebra, and the groupoid-decoder-owned round trips and selected action beta. |
| H2/HIT layer | deferred | Begin only after the observational equality and restricted higher-elimination owners are credible. |
| Path algebra/opposite | E0 composition/collapse removal and E1 symmetry core owner-position probed; neither active | Promote E0 with durable checks and action-unit cleanup, then classify the twelve E1 warning blocks and promote its functor/action/propositional-coherence core; fixed-map packaging follows Candidate D. |
| Omega0/category analogue | broad active first draft plus append-only fixed-map/indexed expressibility | First pass Candidate D0's owner-position recursive-owner/Sigma/refl/next-hom gate; only then attempt Candidate D1's public closure/decoder migration and integrated witness, followed later by discreteness/`OneCat`. |
| Discreteness/directed dimension | exact `IsSetGrpd(Obj(C)) × OmegaEquivAlong_{Cat_cat}(Core_incl_func(C))` contract selected; append-only formation and hom-action-target probe passes | After E1 and Candidate D, derive and diagnose fixed-map equivalence of every core-inclusion hom action before promoting `IsDiscreteCat` as the `IsNCat` base. |
| Indexed adjunction migration | separate append-only feasibility track; active owner unchanged | Run the owner-position 153-occurrence migration with triangle, opposite, mate, and named-operation controls. |
| Direct observational universe identity | later explicit research track; not an immediate MVP gate | Select a local direct-equality or identity-view architecture only after the equality/action and univalence-decoder owners are stable. |
| Universe/metatheory | deliberately deferred | No concrete implementation slice should claim consistency, stratified closure, or a model merely from Lambdapi acceptance. |

The present feasibility assessment is positive but bounded:

1. No concrete Lambdapi expressibility blocker has been found for the proposed
   record convention, truncation-property kernel, elementary H0 classifiers,
   conservative/shaped record paths, standard Pi beta/eta surface, fixed-map
   omega-equivalence telescope, or indexed adjunction telescope.
2. All seven original append-only OETU probes listed below pass warning-enabled
   checking as of 2026-07-14. They establish plausibility only, not final owner
   placement, subject-reduction behavior in source order, or global coherence.
3. A separate adversarial proof-time-unification control confirms the exact
   trust boundary. An intentionally unjustified two-rigid-head `unif_rule`
   leaves its sides non-convertible but nevertheless lets typed `eq_refl`
   inhabit their cross-head equality. Thus typed `eq_refl` is the correct
   operational test that a rule fires, but not an independent mathematical
   validation of the rule. This does not reject `unif_rule`; it classifies a
   selected rule as trusted logical authority at proof time.
4. A separate full-file `Path_cat` composition audit now supplies stronger
   evidence. Keeping `comp_fapp0(Path_cat(A),...)` as the shared category-level
   composition head, removing its fold to J-derived `eq_trans`, and adding two
   narrow `eq_refl` unit bridges passes the full active source, the entire
   migrated check suite, warning-enabled checking, runtime units, generic
   proof-time associativity, and a J-derived propositional comparison with
   `eq_trans`. The unjoinable-pair inventory falls from 1,109 to 1,091 in that
   candidate; this is useful diagnostic evidence, not a confluence proof.
5. Folding `comp_fapp0(Path_cat(A),...)` to the existing postcomposition action
   head instead makes the unit and pre/post comparison probes pass but causes
   associativity consumers to exceed the bounded check. The layered owner is
   therefore currently better supported: `comp_fapp0` owns category-level
   composition, while `hom_postcomp_fapp0` and
   `hom_precomp_along_fapp0` separately own oriented runtime actions.
6. Removal of the self-opposite collapse in the shared-composition full-file
   candidate also passes the entire migrated suite warning-enabled, reducing
   the unjoinable-pair inventory further to 1,072. A minimal
   `PathSym_A` functor from `Path(A)^op` to `Path(A)` then passes the full
   source and migrated suite
   with strict reflexivity and anti-composition through generic functoriality,
   propositional `eq_sym` agreement and involution, and a pointwise
   `Core_incl_func`/opposite square. That candidate reports 1,084 unjoinable
   pairs: twelve reports mention the new functor owner and remain to classify,
   while the strict inferred-LHS audit has no unreviewed slot.
7. The exact `IsDiscreteCat` Product contract and the type of its homwise
   adequacy target pass an append-only warning-enabled probe. The hom action's
   object projection computes to the existing `path_to_hom` owner. The probe
   deliberately does not inhabit the adequacy theorem: deriving fixed-map
   equivalence of every hom action remains a Candidate-D/Phase-9 promotion
   obligation.
8. The best/original goal therefore remains credible as a staged
   implementation and research program. It is not yet demonstrated as one
   globally normalizing implementation. The largest concrete risks are the
   promotion/classification of the new `Path_cat` symmetry core and its later
   fixed-map equivalence packaging, public shaped-equality migration, Pi
   equivalence packaging, active `OmegaEquiv` normal-form migration, and the
   broad adjunction consumer migration.
9. Deferred `Cat_cat : Cat` consistency, universe stratification, and general
   semantic/metatheoretic justification do not block the concrete MVP, but
   every report and code comment must preserve that boundary.

The revised audit verdict is:

| Boundary | Revised conclusion | Remaining promotion gate |
| --- | --- | --- |
| `Path_cat` composition and opposite/symmetry | No fundamental symmetry/asymmetry contradiction. E0's shared category composition, oriented pre/post runtime actions, and collapse removal are full-file feasible. E1's minimal symmetry-functor core is now owner-position probed. | Promote E0 with its two category-unit bridges; clean/classify four oriented action-unit bridges; classify the twelve E1 warning reports and promote its functor-action/reflexivity/propositional-coherence core. Package the functor as fixed-map omega-equivalence only after Candidate D supplies that owner. |
| Hybrid generic/shaped `J` and Candidate H | Coherent candidate. Generic primitive J plus a selected reflexive Pi coherence basis may prove propositional eta even when the equality classifier is shaped. The stable probe supplies that basis through a trusted proof-time equation, while the transparent probe independently obtains the unfolded basis by conversion. | Owner-position Pi bridge, explicit semantic justification/trust classification of that equation, and `IsEquivMap` packaging; fibrancy only for extra runtime betas on arbitrary structured constructors. |
| Direct universe equality | Necessary for the eventual full-observational endpoint, not the immediate H1 MVP. | Phase 13 local owner research after decoder/action stabilization; no external design is a replication target. |
| Global ordinary-iso univalence | Exploratory compatibility approximation, not successor architecture for arbitrary `Cat`. | Freeze new uses in Phase 0; migrate/retire after OneCat-scoped replacement. |
| Fixed-map omega-equivalence | Sigma/fixed-index direction is sound, but current probes establish telescope/package expressibility rather than the recursive owner. | Pass D0 (fresh owner plus minimal Sigma package, reflexivity, and one next-hom observation) before describing D1 as implementation-feasible; complete D1's op/Product/decoder/integrated-witness ladder before calling the public migration ready. |
| `IsDiscreteCat` foundation | The exact Product contract is now selected; its set-object and fixed-core-map factors are nonredundant, and its hom-action target is mechanically well typed. | After Candidate D, derive the homwise fixed-map equivalence whose object action is `path_to_hom`, expose an arrow-to-path inverse with both round trips, and pass one recursive `IsNCat` consumer before promotion. |
| Decoder and equivalence-algebra ownership | The earlier phase/ledger text duplicated groupoid round trips and attempted to finalize the categorical decoder before its equivalence normal form changed. | Groupoid decoder results belong only to `OETU-GRPD-UNIV-DECODER`; `TypeEquiv` algebra owns only ordinary equivalence operations; categorical decoder finalization is jointly scheduled with D1 under `OETU-CAT-UNIV-DECODER`. |
| Proof-time `unif_rule` authority | A semantically justified rule is a legitimate and potentially important Emdash proof-time definitional mechanism, not merely a disposable elaboration trick. It is also trusted logical authority: typed `eq_refl` shows that the rule fires, not that its equation is sound. | Classify every promoted rule as declaration/field-backed, structurally justified selected proof-time law, or explicit postulate. Reword Candidate F/H evidence as conditional on the selected bridge; do not require a duplicate internal path for every generic law when its trusted definitional status and semantic obligation are explicit. |

### Complete OETU probe and evidence inventory

These are the current probe artifacts relevant to this plan. They live under
ignored `tmp/probes/`; they are review evidence, not source authorities and
not durable active diagnostics.

| Probe | What it demonstrates | Promotion boundary that remains |
| --- | --- | --- |
| `tmp/probes/oetu_architecture_feasibility_probe.lp` | One-constructor dependent records, truncation codes/predicate/package, conservative record paths, a stable nondependent shaped-reflexivity head with reflexive `ind_eqr`, strict local path operations, and recursive `IsNCat` formation. | It combines several late append-only experiments. Split the selected slice, place it at each real owner, cover dependent/nested action where claimed, and audit all literal-`eq_refl` consumers. |
| `tmp/probes/oetu_fixed_map_followup.lp` | A transitional `OmegaEquivAlong(F)` bridge into the current opaque `OmegaEquiv`, computing selected-map/inverse observations, recursive higher-cell endpoints, and the semantic homotopy fibre. | Replace or migrate the real owner; do not retain the bridge as the final two-layer architecture or infer property-valuedness. |
| `tmp/probes/oetu_discrete_cat_contract.lp` | The selected `IsDiscreteCat` Product boundary, exact `Cat_cat` indexing of `Core_incl_func`, the hom-action functor from `Path_cat(x=y)` to `Hom_cat(C,x,y)`, its `path_to_hom` object projection, and the type of the required homwise adequacy theorem all pass append-only warning-enabled checking. | It deliberately provides no inhabitant of the homwise theorem. Derive that theorem from the promoted fixed-map owner (or document a revised evidence boundary), add inverse/round-trip diagnostics, and reprobe at owner position before promoting discreteness. |
| `tmp/probes/oetu_indexed_structure_architecture_probe.lp` | Primary fixed-map evidence plus Sigma packaging, indexed `Adjunction(F,G)`, both exact triangle patterns, transparent versus proof-time functor views, fixed-arrow higher cells, and the mechanics of typed named-unit/counit comparison under per-instance proof-time equations. | Move candidates to owner positions, minimize/annotate its eight scratch-local replaceable-pattern-variable advisories, and migrate active opposite/mate/decoder consumers. Its independently declared `ReviewNamedAdj`, unit, and counit do not semantically justify their own `unif_rule`s; promotion must bind the names through declaration data/fields or classify the generated equations as trusted declaration postulates. |
| `tmp/probes/oetu_adjunction_named_unit_runtime_probe.lp` | Negative control: runtime unit/counit projection betas erase the stable triangle discriminators, leaving both the projected and raw named-operation spellings stuck as expected. | Preserve stable unit/counit observations or design a different audited triangle owner; clean its two scratch-local LHS advisories before reusing a pattern. |
| `tmp/probes/oetu_hott_elementary_formers.lp` | Decoded Empty, Bool, and Nat classifiers; dependent eliminator facades; Bool and Nat constructor beta. | Promote at the foundations owner with active diagnostics; identity/no-confusion, higher action, canonicity, and categorical universal properties remain separate. |
| `tmp/probes/oetu_hott_pi_adequacy.lp` | Standard diagonal `happly`, transparent `funext` with related-input action, judgmental beta, non-judgmental arbitrary eta, and conversion of the unfolded reflexive reverse composite to `eq_refl`. This independently motivates the stable-head reflexive law. | Select stable public owners, verify that their proof-time equation faithfully preserves this transparent computation, and construct the actual `IsEquivMap(PiHapply)` evidence rather than citing beta/eta sketches. |
| `tmp/probes/oetu_hott_pi_stable_funext.lp` | Stable `PiHapply`/`PiFunext` heads, related-input action, a two-rigid-head selected proof-time reflexive equation, and—conditional on that equation—propositional eta via generic `ind_eqr`. | Reprobe at owner position, retain the explicit hybrid generic-`J` contract, justify or explicitly select the reflexive equation as a trusted structural proof-time law, and package the active equivalence; fibrancy is required only for additional structural computation, not for this conditional generic-J eta proof. |
| `tmp/probes/oetu_unif_trust_boundary_probe.lp` | Adversarial negative control: an intentionally unjustified rule equates two unrelated rigid heads at proof time; runtime conversion remains negative, while typed `eq_refl` constructs their cross-head equality. This isolates firing from semantic validation. | Never promote the arbitrary rule. Retain the probe as methodological evidence that every real `unif_rule` needs a recorded semantic trust class and that typed `eq_refl` is an operational regression test, not independent foundational evidence. |
| `tmp/probes/oetu_path_oriented_owner_probe.lp` | The existing postcomposition and precomposition point heads give distinct oriented runtime presentations of path composition, each can receive both narrow `eq_refl` unit bridges, and their existing direct `unif_rule` supplies typed proof-time comparison. | Append-only action-owner evidence only. Its four replaceable-variable advisories and one local overlap with postcomposition accumulation must be cleaned/classified; it does not select either action head as the category-level composition normal form. |
| `tmp/probes/oetu_path_shared_comp_owner_full.lp` plus `tmp/probes/oetu_path_shared_comp_owner_checks_full.lp` | Owner-position E0 composition candidate: generic `comp_fapp0` remains the `Path_cat` composition head, two `eq_refl` projection-order unit bridges are added, J-derived comparison with `eq_trans` is propositional, and the entire migrated active check suite passes warning-enabled. | Promote only together with removal of the old `comp_fapp0(Path_cat)->eq_trans` fold and durable agreement/unit/associativity checks. This artifact deliberately retains the self-opposite collapse and therefore supplies no E1 evidence. |
| `tmp/probes/oetu_path_symmetry_removal_full.lp` plus `tmp/probes/oetu_path_symmetry_removal_checks_full.lp` | E0 removal-only extension of the shared-composition candidate: deleting `Op_cat(Path_cat(A))->Path_cat(A)` still passes the full source and entire migrated suite warning-enabled, with 1,072 unjoinable-pair reports. | This is a sounder promotion intermediate, not a symmetry implementation. It proves that E0 need not retain the bad collapse while E1 is developed. |
| `tmp/probes/oetu_path_symmetry_owner_full.lp` plus `tmp/probes/oetu_path_symmetry_owner_checks_full.lp` | Owner-position E1 core: `PathSym_A : Path(A)^op -> Path(A)` fixes objects; its arrow action is the readable `path_sym` owner; a narrow reflexivity bridge computes; generic functoriality supplies anti-composition; J supplies propositional `eq_sym` agreement and involution; and a pointwise `Core_incl_func`/opposite square is proved. The full migrated suite, warning-enabled source/checks, negative conversion controls, and strict LHS audit pass. | The 1,084 inventory contains twelve new reports mentioning `PathSym_A`; classify them with both-order consumers before promotion. Functor-level natural packaging and `OmegaEquivAlong(PathSym_A)` wait for the fixed-map owner rather than being faked through the old opaque package. |
| `tmp/probes/oetu_path_oriented_owner_full.lp` and its focused unit/bridge/associativity consumers | Negative owner-position comparison: folding `comp_fapp0(Path_cat)` to `hom_postcomp_fapp0` preserves both units and typed pre/post agreement. | Associativity consumers exceed the bounded check, so this fold is rejected unless the global associativity interaction is redesigned and remeasured. |

To reproduce any row, run the following command with that row's path:

```bash
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_TYPECHECK_TIMEOUT=60s \
  scripts/probe.sh tmp/probes/oetu_hott_elementary_formers.lp
```

The original seven-probe set was rerun successfully on 2026-07-14; the corresponding log
names end in `20260714-200013` under `logs/probes/`. Imported active warnings
remain visible in those logs. Absence of a probe-local unjoinable critical
pair is not proof of global confluence, and the named-unit negative probe
shows why explicit positive/negative computation checks are also necessary.

The Candidate-D-relevant `oetu_fixed_map_followup.lp` and
`oetu_indexed_structure_architecture_probe.lp` rows were additionally rerun
warning-enabled on 2026-07-14; those later logs end in `20260714-234358`, and
both files finish checking successfully. The indexed probe still reports its
eight scratch-local replaceable-pattern-variable advisories. These later
passes do not change either artifact's append-only status or supply the absent
D0 recursive-owner computation.

The append-only exact-discreteness contract probe
`oetu_discrete_cat_contract.lp` passes warning-enabled on 2026-07-15; its log
ends in `20260715-114925`. It adds no probe-local warning family beyond the
1,109 imported active reports. It checks the exact Product formation,
`Cat_cat` indexing, the hom-action endpoints, and the definitional
`path_to_hom` object projection. It intentionally types but does not inhabit
the homwise adequacy theorem, so it is contract evidence rather than an
`IsDiscreteCat` implementation.

The adversarial unification-trust control
`oetu_unif_trust_boundary_probe.lp` passes warning-enabled on 2026-07-15; its
successful log ends in `20260715-124106`. The control intentionally chooses an
equation with no supplied mathematical justification. Its `assertnot` runtime
comparison and successful typed cross-head `eq_refl` make the logical trust
boundary executable. It is not a candidate rule and contributes no positive
semantic evidence for Candidate F or H.

The original path-owner warning-enabled migrated-suite log ends in
`20260714-234330`; a byte-identical later rerun ends in `20260715-000459`.
The shared-`comp_fapp0` full-file source and migrated check suite finish
successfully with 1,091 unjoinable-pair reports. The action-owner fold's unit
and bridge consumers finish, while its associativity consumers time out.
These positive and negative results are part of Candidate E0's selection
evidence and should not be collapsed into the weaker phrase “append-only
feasibility.”

The 2026-07-15 E0 collapse-removal source/check logs end in
`20260715-015457` and `20260715-015535`; both pass, and the source reports
1,072 unjoinable pairs. The final E1 symmetry-owner source/check logs end in
`20260715-020314` and `20260715-020507`; both pass,
the source reports 1,084 pairs, exactly twelve warning blocks mention
`Path_sym_func`, the open strict/J-derived and double-symmetry conversions
remain negative as intended, and the strict inferred-LHS audit reports zero
unreviewed candidates. Counts are warning inventories, not confluence proofs.

Older `tmp/probes/univalence_*` artifacts belong to the June 23 predecessor
plan. They are not prerequisites for Candidate G and need not be read during
normal handoff. Consult them only when an identified univalence migration
question requires historical evidence; never let them override active code,
checks, this plan, or the current SOP.

### Required procedure at the start of an implementation turn

The authority order remains active code, active checks, current SOP,
Foundations, canonical syntax, and then task plans/decision records. This
handoff is self-contained as a task plan, but it does not replace those active
authorities.

1. Read `AGENTS.md`, `README.md`, the relevant regions of `emdash3_2.lp` and
   `emdash3_2_checks.lp`,
   `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`,
   `reports/EMDASH_FOUNDATIONS.md`,
   `reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`,
   `reports/INDEX.md`, and this handoff section plus the selected candidate,
   matrix row, phase, risk, ledger row, and acceptance criteria.
2. Run `git status --short`; inspect unstaged and staged diffs separately and
   preserve unrelated user work. Do not assume the clean snapshot recorded
   here still describes the workspace.
3. Choose exactly one side-task ID. Unless the user selects another slice, use
   `OETU-ELEMENTARY-HOTT` / Candidate G. Change `Current-Implementation-Slice`
   and that ledger row to `in progress` with the date and bounded scope before
   broadening the work.
4. Relocate every relevant symbol and nearby rule with `rg`; remembered line
   numbers and archive responses are not authorities.
5. Run the bounded baseline before editing:

   ```bash
   EMDASH_TYPECHECK_TIMEOUT=60s make check
   ```

6. Refine the smallest candidate in a temporary **full-file copy**, placing it
   at the intended source owner rather than merely importing `emdash3_2` and
   appending it. Add focused runtime assertions, typed `eq_refl` checks that
   proof-time comparisons fire, an explicit semantic trust class for each new
   `unif_rule`, negative controls, both reduction orders where relevant, and
   warning comparison.
7. Promote only the minimal coherent declarations/rules. Add durable
   regression statements to `emdash3_2_checks.lp`, mathematical/ownership
   comments beside the active owners, and a reviewer example only when the
   slice has a genuine end-to-end milestone.
8. Update this report using the protocol below, then run validation in
   proportion to the slice. A promoted semantic slice normally requires
   focused probes, `make check`, warning/LHS audits where relevant,
   `make catalog`, `make health`, and `make ci`; run `make examples` when a
   reviewer milestone changes.

### Default first implementation slice: Candidate G

Candidate G is selected as the default next slice because it closes the
smallest concrete H0 gap, has a passing focused feasibility probe, does not
depend on the unresolved public equality/path owners, and turns the adequacy
benchmark into active foundation code. This selection does not formally adopt
every later migration decision and may be overridden by an explicit user
instruction.

The bounded deliverable is:

1. introduce a native empty carrier and Bool carrier, their decoded
   `Empty_grpd` and `Bool_grpd` classifiers, and reviewed dependent eliminator
   facades at the foundations owner;
2. introduce `Nat_grpd` as a decoded facade over the active native `nat`, with
   a reviewed groupoid-level eliminator routed through generated `ind_nat`;
3. use Bool, rather than making the first slice also design a general binary
   sum. A later sum former remains a separate H0 extension;
4. add active decoding/formation assertions, both Bool constructor betas,
   both Nat constructor betas, Empty-eliminator formation, and an appropriate
   Bool constructor non-collapse conversion check;
5. confirm source-order subject reduction, warning behavior, bounded runtime,
   and that existing equality/Pi/Sigma checks remain unchanged; and
6. update the H0 snapshot, Candidate G text, Phase 0/11 status, and
   `OETU-ELEMENTARY-HOTT` ledger row only after the promoted code and active
   checks pass.

This first slice explicitly does **not** claim:

- observational identity, no-confusion, higher action, or canonicity for
  Empty, Bool, or Nat;
- initial-object, coproduct, or natural-number-object universal properties in
  `Cat`;
- a new general sum former, a truncation reflector, or any univalence closure;
- resolution of shaped `eq_refl`, additional structured-path `J` computation,
  `Path_cat`, fixed-map omega-equivalence, or indexed adjunction.

After Candidate G, Candidates A (record convention) and B (truncation property
kernel) are the default low-risk infrastructure slices; they may be ordered by
the first concrete consumer. Candidate H and the H1 compatibility ledgers can
then make the ordinary HoTT surface complete while Candidate E0/E1 promotes
the now-probed path owners required before public Candidate C registration.

### Global roadmap and dependency outline

The numbered phases below remain the detailed global migration order. The
following lanes make the intended dependency structure explicit; plan details
may be revised when owner-position evidence changes a boundary.

```text
Immediate H0 bootstrap
  Candidate G: Empty / Bool / Nat decoding and eliminator beta

Reusable property/structure infrastructure
  Candidate A: record convention ─┐
  Candidate B: truncation kernel ─┴─> packaged truncated universes

Ordinary HoTT compatibility
  Candidate H: Pi happly/funext equivalence under generic J
        + a selected, semantically justified reflexive proof-time basis
        + Sigma/record arbitrary path round trips
        + TypeEquiv algebra
        + groupoid decoder round trips and transport/action squares
        ───────────────────────────────────────────────────────> H1 MVP

Public observational equality and path algebra
  Candidate E0: shared comp_fapp0 Path_cat owner + collapse removal
        ─> Candidate E1: PathSym functor/action + propositional coherence
        ─> Candidate C: public shaped reflexivity/reflexive J
        ─> structural action ─> fibrancy/dependent J ─> former-by-former migration

Omega/category extension
  record/equality owners
        ─> Candidate D0: fixed-map owner + Sigma package + refl/next-hom gate
  categorical decoder contract + passing D0
        ─> Candidate D1 + categorical decoder finalization:
           op/Product + public decoder migration + integrated witness
  promoted E1 symmetry core + Candidate D1 fixed-map owner
        ─> PathSym/Core fixed-map packages
        ─> exact IsDiscreteCat Product + core-hom adequacy
        ─> IsNCat / OneCat
        ─> one-next-hom Omega0 univalence/action witness

Separate category migration lane
  Candidate F: indexed Adjunction(F,G), stable unit/counit, triangles/opposite/mates

Later higher layer
  truncation reflectors ─> representative HITs ─> optional H2 completion
  computational universe identity ─> eventual full-observational endpoint
  stratified universes / Cat_cat:Cat metatheory remain a separate deferred research phase
```

Candidates C, D0, E0/E1, F, and H remain available immediately as focused design
or owner-position probes; D1 waits for D0. “Immediately available” does not
bypass their listed promotion dependencies, and Candidate F's adjunction
witness never substitutes for H0/H1/Omega0 adequacy.

### Progress tracking and handoff update protocol

Use this report as the status ledger rather than leaving architectural results
only in conversation.

At the start of a slice:

- update `Last reviewed`, `Current-Implementation-Slice`, and the selected
  side-task row to `in progress (YYYY-MM-DD)` with its exact exclusions;
- record the baseline result and any pre-existing worktree changes that affect
  the slice; and
- create or name the owner-position probe separately from the append-only
  evidence files above.

During and after a slice:

- update the applicable status-snapshot/matrix row, phase item, candidate
  feasibility paragraph, risk, diagnostics, and ledger row together;
- use `active` only for promoted code covered by active diagnostics;
- use `owner-position probed` only for a full-file candidate placed at its
  intended owner and checked with the relevant warnings/reduction orders;
- use `append-only feasibility demonstrated` for the seven original import
  probes and never shorten that phrase to `probed`; record the later shared-
  `comp_fapp0`, collapse-removal, and symmetry-owner candidates separately as
  owner-position probed, with their differing scopes and warning inventories;
- record new architectural decisions under “Decisions Accepted For This
  Proposal,” and record rejected runtime orientations under risks/diagnostics
  rather than silently deleting the reason;
- add every new relevant scratch path to the probe inventory and References,
  but move durable assertions to `emdash3_2_checks.lp`;
- preserve staged versus unstaged user changes and do not fold unrelated work
  into the slice; and
- return `Current-Implementation-Slice` to `none` only when the row is marked
  completed/promoted or when a documented blocker/transfer names the exact
  resume trigger.

A slice is complete for handoff only when its code, focused and active checks,
warning/LHS classification, bounded performance, report/matrix/ledger status,
catalog, health report, and relevant CI/examples agree. A passing scratch
probe alone is never completion. If evidence changes the roadmap, update this
top handoff, the detailed phase, and the ledger in the same edit so the next
agent sees one coherent plan.

## Decisions Accepted For This Proposal

This proposal incorporates the following project directions.

1. **Full observational equality is the eventual target.** A deliberate hybrid
   generic/shaped architecture is compatible with that target: unknown or
   unsupported classifiers keep the ordinary primitive identity interface,
   while registered formers expose additional structural computation. What is
   not intended as the final design is the current unregistered coexistence of
   direct Sigma/Pi views, generic consumers, and partially shaped computation.
2. **Truncation is an immediate architecture prerequisite.** `Prop`, `Set`,
   ordinary groupoids, `OneCat`, and general finite-dimensional variants must
   be designed together with univalence, even if their first implementation
   slice is only formation and projection computation.
3. **Every active `C : Cat` remains globally univalent for now.** The kernel may
   retain `cat_univalence(C)` and its decoder-oriented companion as explicit
   operational assumptions.
4. **No `PreCat`/`UnivCat` split is required in the near term.** If non-univalent
   structures are needed later, they may receive a separate classifier; the
   current `Cat` interface itself is interpreted as univalent.
5. **Universe stratification and a model of `Cat_cat : Cat` remain deferred.**
   The code and reports must label the current policy as an unstratified
   operational specification, not as a consistency or model-existence result.
6. **Ordinary isomorphism univalence is dimension-specific.** The global
   omega-level principle compares equality with `OmegaEquiv`; the
   `IsoEvidence` comparison belongs to `OneCat` or an explicit ordinary-category
   truncation hypothesis.
7. **Finite dependent structures should not default to deeply nested Sigma
   projections.** A one-constructor dependent inductive record convention is
   the preferred explicit encoding; small existential/property packages may
   continue to use Sigma.
8. **The equality redesign has two cooperating tracks inside one hybrid
   contract.** Generic `=`/`eq_refl`/`ind_eqr` remain available at every
   classifier, with the ordinary beta on literal reflexivity. A conservative
   classifier-and-observer MVP may be promoted without waiting for arbitrary
   structural computation, while registered shaped `eq_refl`, structural
   action/substitution, and computational shaped `J` remain available for
   immediate design and implementation as soon as an owner-position probe
   meets the promotion criteria below.
9. **Earlier failed encodings are evidence, not vetoes.** In particular, the
   earlier failure of a raw `eq_refl ->` path-record-constructor rewrite does
   not prohibit a stable shaped-reflexivity head, a different action owner, or
   another now-feasible architecture.
10. **Missing infrastructure is an ordinary prerequisite, not a reason to
    weaken the target.** A slice may first add a classifier, stable facade,
    record convention, equality action, or equivalence certificate that is not
    yet in `emdash3_2.lp`; existing first-draft owners may also be redesigned or
    corrected after focused migration probes.
11. **Foundational adequacy is a design test.** The plan must account for the
    minimal HoTT-style notions listed below and their immediate directed
    categorical/omega analogues, including at least one iteration through the
    next hom level. Passing Lambdapi formation alone is not sufficient; the
    matrix records expected computation and missing prerequisites.
12. **Equivalence structure over an already-named map is primary.** A Sigma
    fibre such as `Sigma e, omega_equiv_to(e) = F` is a valid semantic
    specification, but it is not the selected runtime interface for declaring
    that a concrete functor is an equivalence. The proposed end state makes
    neutral `OmegaEquivAlong(F)` the fixed-map evidence layer and defines the
    ordinary first-class equivalence type as its Sigma package. The
    `IsOmegaEquivArrow(F)` property spelling is introduced only after
    property-valuedness is proved.
13. **Adjunction is likewise an indexed relation in the proposed end state.**
    Rather than retain a permanent `AdjunctionAlong(F,G)` facade alongside the
    current `Adjunction(R,L)`, migrate `Adjunction` itself to be indexed by the
    already-named left and right functors. An existential first-class package
    may be derived separately when a consumer truly does not know the functors.
14. **Runtime projections are not delegated to unification rules.** A narrow
    `unif_rule` may be a deliberately selected trusted proof-time equation
    relating an opaque compatibility view to an index, but data needed by
    downstream reduction must either compute by a transparent
    definition/projection beta or remain visible as the stable observation
    selected by its consumer rule. Its proof-time semantic authority does not
    turn it into a runtime normal-form owner.
15. **Indexed adjunctions retain stable unit/counit runtime observations.**
    `F` and `G` are indices, so `left_adj_func`/`right_adj_func` disappear or
    remain transparent migration views. In contrast, `unit_adj_transf(J)` and
    `counit_adj_transf(J)` remain opaque stable heads because the generic
    triangle cut-elimination rules discriminate on them. The exact two
    indexed triangle patterns have been mechanically demonstrated in an
    append-only probe; they use `F` and `G` as consistently repeated
    parameters, never as rewrite heads.
16. **Preselected adjunction operations are connected proof-time by default.**
    A declaration that explicitly binds `myAdj : Adjunction(myF,myG)` to a
    named `myUnit`/`myCounit` may generate narrow, typed `unif_rule`s as its
    trusted proof-time declaration equations. Alternatively, explicit
    agreement fields/paths may back the comparison. Independently declared
    constants are not made mathematically related merely by checking a typed
    `eq_refl`; that check only confirms that the selected rule fires. Runtime
    betas from the stable observations to arbitrary raw names are rejected by
    default because they can erase the triangle discriminator before the outer
    cut rule fires. Raw named-operation expressions do not thereby acquire
    triangle computation; a future elaborator must preserve/reconstruct the
    stable spelling, or separately generated instance rules require their own
    critical-pair and trust audit.
17. **The architecture MVP remains subject to a foundational adequacy gate.**
    It may leave named cells as prerequisites or deferred work, but it must
    make the usual minimal HoTT kernel and its immediate category/omega
    analogues expressible without brittle per-instance rules or an architecture
    that blocks their later computational completion.
18. **Architecture adequacy and implementation adequacy are different
    milestones.** An architecture MVP may classify a missing row precisely as
    a prerequisite or deferral. A foundational implementation skeleton must
    activate its declared elementary core and may count only owner-position
    probes, not append-only import experiments, toward any remaining probed
    boundary.
19. **The richer observational Pi identity must expose the standard HoTT
    compatibility surface.** Diagonal application and function extensionality
    should coexist with related-input action. Runtime beta is selected where it
    has a canonical observation; arbitrary eta is propositional, and
    `PiHapply` must eventually be packaged as an active `IsEquivMap` rather than
    inferred from beta/eta sketches alone. Under the retained generic `J`, a
    selected reflexive `PiFunext(PiHapply(refl)) = refl` basis yields the
    propositional eta proof and does not wait for a separate fibrancy
    implementation. The transparent Pi probe obtains that basis by conversion
    after unfolding; the present stable-head probe preserves it with a trusted
    proof-time equation. Thus the stable eta proof is conditional on the
    selected equation, but the equation has independent definition-level
    motivation rather than being an arbitrary instance postulate. This does
    not thereby establish new runtime computation on arbitrary structured Pi
    paths.
20. **Foundational compatibility is executable and independent of
    adjunction.** Elementary classifier/eliminator beta, Sigma/record path
    round trips, `TypeEquiv` algebra, decoder-owned univalence round trips, and
    conversion-level anti-collapse controls belong to the HoTT gate. Their
    coexistence in one gate does not merge their semantic owners. Indexed
    adjunction is a separate category-migration witness and cannot substitute
    for them.
21. **`Path_cat` has layered rather than contradictory composition owners.**
    The selected category-level candidate retains the generic
    `comp_fapp0(Path_cat(A),...)` head, with narrow `eq_refl` projection-order
    unit bridges. `hom_postcomp_fapp0` and `hom_precomp_along_fapp0` remain the
    distinct covariant/contravariant runtime action owners and compare at proof
    time. J-derived `eq_trans` is a propositional reference operation. This is
    the current full-file-tested reconciliation of symmetric category laws with
    asymmetric J-derived cuts.
22. **The immediate MVP is not the full-observational endpoint.** H1 requires
    the public univalence decoder/encoder algebra and selected transport/action
    beta, but not yet a direct reduction of universe equality to equivalence.
    The latter has its own eventual track and must not be inferred from decoder
    normalization alone.
23. **External designs are references, not replication targets.** Narya,
    cubical systems, observational type theories, and the HoTT literature supply
    comparison tests and possible ingredients. Emdash must select its own
    Kosta--Došen/Lambdapi owners, and may deliberately discover a simpler or
    more computational formulation instead of reproducing an external glue,
    fibrancy, or bisimulation implementation verbatim.
24. **The new architecture is dimension-correct about ordinary isomorphism
    from the outset.** Existing global `cat_iso_univalence` declarations are
    frozen as legacy compatibility during migration; no new redesign owner or
    theorem may depend on them for arbitrary `Cat`. Global new work uses
    `CatUnivalence`/`OmegaEquiv`, and ordinary `IsoEvidence` univalence is
    introduced only for `OneCat` or an explicit ordinary-dimensional
    hypothesis.
25. **Fixed-map omega-equivalence remains evidence until property-valuedness is
    proved.** `OmegaEquivAlong(F)` is the neutral primary name. It may be
    described operationally as a certificate/evidence package; the
    `IsOmegaEquivArrow(F)` alias and proof-field erasure are reserved for the
    theorem that its recursive coherence makes it property-like.
26. **Decoder ownership is split by layer and kept separate from equivalence
    algebra.** Groupoid decoder normalization, both groupoid round trips, and
    the `coe_grpd` action square may complete before Candidate D. The
    categorical decoder's name/orientation is selected early, but its public
    type, round trips, and `path_to_hom` squares finalize jointly with D1's
    fixed-map normal-form migration. `TypeEquiv`/`IsEquivMap` identity,
    symmetry, and composition remain the exclusive algebra task; a migration
    may rerun decoder diagnostics but does not copy their semantic bodies.
27. **`Path_cat` symmetry is a functor action, not a second path algebra.**
    E0 removes both the composition-to-`eq_trans` fold and the definitional
    self-opposite collapse. E1 introduces `PathSym_A : Path(A)^op -> Path(A)`;
    its object action is identity and its capped arrow action is the strict
    `path_sym` owner. Generic `fapp*` functoriality owns anti-composition, with
    one narrow reflexivity projection bridge. Agreement with J-derived
    `eq_sym`, double-symmetry involution, and the initial `Core_incl_func`
    opposite square are propositional. No runtime double-symmetry cancellation
    or second anti-composition rewrite is selected. Fixed-map equivalence
    packaging of `PathSym_A` waits for Candidate D rather than depending on the
    obsolete opaque `OmegaEquiv` interface.
28. **`IsDiscreteCat` has an exact two-factor contract.** The selected
    definition is `IsSetGrpd(Obj(C))` paired with fixed-map
    `OmegaEquivAlong_{Cat_cat}(Core_incl_func(C))` evidence. Neither factor is
    dropped: object-set truncation alone permits directed arrows, while core
    equivalence without set truncation can retain higher object-path data.
    Before promotion, the fixed-map evidence must derive equivalence of every
    hom action of `Core_incl_func`; its object action is the existing
    `path_to_hom` map. This homwise consequence is a theorem/diagnostic, not a
    duplicated third record field unless the general derivation is shown
    infeasible and the decision is explicitly revised.
29. **A `unif_rule` may be foundational proof-time computation, but it is not
    self-validating evidence.** Emdash deliberately uses proof-time equations
    alongside runtime rewrites; this is a genuine architectural capability and
    is not prohibited merely because other HoTT implementations lack it. Every
    promoted rule nevertheless receives one of three trust classes:
    (a) declaration/field-backed agreement, (b) a generic structurally and
    semantically justified selected proof-time definitional law, or (c) an
    explicit trusted postulate. A typed `eq_refl` is mandatory to test that the
    rule participates in the intended consumer, but it establishes only that
    operational fact. Requiring a duplicate internal path for every rule in
    class (b) would add ceremony without increasing trust; silently using an
    independent per-instance equation without class (a) or (c) would instead
    hide a real axiom.

## Current Baseline And Review Findings

At creation of this proposal:

```text
tracked working tree                         clean
EMDASH_TYPECHECK_TIMEOUT=60s make check      pass
active implementation                        emdash3_2.lp
active diagnostics                           emdash3_2_checks.lp
```

The 2026-07-14 handoff revalidation reran the bounded active check and all
seven original warning-enabled OETU import probes successfully before this
report-only edit. The later owner-position `Path_cat` source and migrated full
check-suite candidate also pass warning-enabled. No kernel or active-check
migration has been made by the plan. The probe logs and their distinct
append-only/owner-position limitations are recorded in the handoff inventory
and References; a successor must still rerun the baseline against its own
current worktree.

The existing architecture contains valuable first slices:

- `PathOver`, `eq_apd`, Sigma/Pi path views, and contractible-fibre
  `TypeEquiv`;
- explicit `idtoequiv_grpd`, `idtoiso_cat`, and `idtoequiv_cat` directions;
- explicit reverse decoder heads;
- a recursive `OmegaEquiv` observation interface;
- constructor-specific Product experiments;
- a global categorical-univalence policy stated visibly rather than hidden in
  conversion.

The review nevertheless found four migration boundaries.

1. The active `Path_cat` fold to one-sided J-derived `eq_trans` does not join
   the generic category units. A later full-file audit now supplies a passing
   shared-`comp_fapp0` repair candidate, so this is a source migration rather
   than an unresolved architectural contradiction.
2. `Op_cat(Path_cat(A)) -> Path_cat(A)` identifies a self-opposite equivalence
   with definitional equality and erases the endpoint reversal.
3. Sigma/Pi equality has begun reducing observationally, while the registration
   contract between generic `eq_refl`/J and shaped former computation remains
   incomplete. The hybrid itself is not contradictory; its owners and claims
   need to be explicit.
4. Capability-selected inverse maps and operational decoder heads coexist
   without named agreement, and Product reflexive collapse competes with
   structured decoder normal forms.

These are not reasons to abandon the current concepts. They show that the
next work must be an architecture migration, not additional constructor-local
rules on the existing hybrid.

The 2026-07-14 append-only import feasibility probe
`tmp/probes/oetu_architecture_feasibility_probe.lp` additionally established
the following implementation evidence. The probe is ignored scratch evidence,
not promoted source.

- a parametrized one-constructor dependent record, its generated eliminator,
  named projections, `TruncLevel`, recursive `IsTruncGrpd`, and a packaged
  truncated universe all typecheck against the active file;
- conservative observational classifiers for nondependent and dependent
  records, direct reflexivity observations, generic literal-reflexivity `J`, a
  strict path-algebra head, and recursive `IsNCat` formation are mechanically
  feasible as isolated skeletons;
- rewriting record reflexivity directly to the raw path-record constructor
  reproduced local critical-pair failures;
- replacing that raw constructor normal form by a stable former-specific
  shaped-reflexivity head, letting its projections own the component
  reflexivities, and adding a specialized reflexive `ind_eqr` rule is viable;
- generic operations that discriminate on literal `eq_refl` must register a
  narrow rule for the shaped head at the generic owner's position. After the
  probe registered strict path composition and symmetry this way, the
  warning-enabled probe passed with no probe-local warning;
- the semantic fixed-functor fibre for category equivalence typechecks, but
  this does not resolve the computational declaration/usability question.

This evidence raises shaped reflexivity and reflexive shaped `J` from a blanket
future deferral to an immediate candidate slice. It does **not** yet establish
arbitrary structured-path substitution, nested-former scalability, public
equality migration safety, or metatheoretic normalization.

Three follow-up warning-enabled append-only import probes add more specific
evidence:

- `tmp/probes/oetu_fixed_map_followup.lp` implements the exact transitional
  `OmegaEquivAlong(F)` bridge into the current opaque `OmegaEquiv`, including
  forward/inverse/higher-cell observations and the semantic homotopy fibre;
- `tmp/probes/oetu_indexed_structure_architecture_probe.lp` validates both an
  indexed `Adjunction(F,G)` relation and a fixed-arrow omega-equivalence
  property whose ordinary equivalence type is a Sigma package;
- `left_adj_func(adjunction_from_along(j)) -> F` does compute with the current
  stable projection head. It is therefore mechanically possible, contrary to
  the concern that the projection must necessarily erase before matching;
- the indexed replacement is simpler: a retained compatibility view can be a
  transparent definition returning its `F` or `G` index, and ordinary
  conversion then succeeds without a rewrite or unification rule;
- an opaque compatibility projection plus a narrow `unif_rule` lets a typed
  `eq_refl` proof elaborate but intentionally does **not** make the projection
  convertible to the index. This confirms the SOP distinction between
  proof-time comparison and runtime computation, while the adversarial control
  separately confirms that elaboration success is not semantic validation;
- where a transitional constructor bridge installs dependent observation
  betas, it must install map/functor betas before unit/counit or higher-cell
  betas, because the latter result types depend on the former normal forms
  during subject-reduction checking. This ordering result does not approve
  final indexed-adjunction betas from stable unit/counit observations to raw
  named operations;
- exact indexed versions of **both** active adjunction triangle rules pass.
  Their rigid semantic discriminators are the outer composition and the
  stable unit/counit application heads; `F` and `G` are repeated indexed
  parameters and do not need to head a rewrite pattern;
- the exact fixed-arrow left/right inverse and recursive higher-cell endpoint
  types pass. The fixed arrow `f` occurs as an index in those endpoints; no
  cancellation rule needs to discriminate on a variable map;
- the mechanics of relating a concrete preselected unit and counit proof-time
  to the stable observations by narrow `unif_rule`s work: typed `eq_refl`
  succeeds while an `assertnot` confirms that runtime conversion intentionally
  does not. In that scratch probe the adjunction, unit, and counit are
  independent constants, so the rules themselves are trusted instance
  equations and the resulting typed paths are not independent semantic
  justifications for those equations;
- the separate negative probe
  `tmp/probes/oetu_adjunction_named_unit_runtime_probe.lp` shows that ordinary
  runtime betas projecting `unit_adj_transf`/`counit_adj_transf` to arbitrary
  constructor-supplied `eta`/`epsilon` can normalize away the rigid heads
  before the generic triangle rule matches. Both the projected spelling and
  the already-raw `eta`/`epsilon` composite then remain stuck.

The warning-enabled runs typecheck, and the latest adjunction probes add no
probe-local **unjoinable critical-pair** warning over the 1,109 imported active
reports. This absence does not detect the lost-triangle computation in the
negative probe, so explicit positive and `assertnot` reduction-order
diagnostics are mandatory. The latest indexed probe has eight scratch-local
replaceable-pattern-variable advisories and the negative probe has two; these
must be minimized or annotated in an owner-position promotion probe. All four
redesign probes remain feasibility evidence, not a replacement for migration
probes of the active declarations.

Three additional append-only import probes refine the foundational feasibility
assessment without changing any formal matrix row to `probed`:

- `tmp/probes/oetu_hott_elementary_formers.lp` demonstrates decoded Empty,
  Bool, and Nat classifiers, dependent eliminator facades, and their
  constructor beta rules over the active `Prop := Grpd`, `P := τ` boundary;
- `tmp/probes/oetu_hott_pi_adequacy.lp` separates the judgmental diagonal beta
  of `happly(funext(h))` from the non-judgmental arbitrary eta/coherence law;
- `tmp/probes/oetu_hott_pi_stable_funext.lp` demonstrates stable `PiHapply` and
  `PiFunext` heads, related-input action, a selected two-rigid-head proof-time
  reflexive equation, and propositional eta derived conditionally from it by
  generic `ind_eqr`.

All three pass warning-enabled checking without a probe-local warning. They are
still late extensions after importing the active owner. Consequently they show
mechanical plausibility, not owner-position/full-file coherence. The elementary
probe does not establish observational identity, no-confusion, higher action,
or canonicity for its inductives. The Pi probe does not yet construct the
active contractible-fibre `IsEquivMap(PiHapply)` package, and its proof-time
comparison remains an owner-position candidate. Its generic-J propositional eta
is valid in the theory extended by the selected reflexive proof-time equation;
the typed `eq_refl` base checks that equation operationally rather than deriving
its semantic soundness. The equation may still be adopted as a justified
generic proof-time definitional law. Neither result is evidence that arbitrary
structured Pi-path elimination has acquired a new runtime computational rule.

The later full-file `Path_cat` audits strengthen this boundary beyond
append-only feasibility:

- removing `comp_fapp0(Path_cat)->eq_trans` leaves generic `comp_fapp0` as the
  category-level path-composition normal form;
- two narrow unit bridges handle the competing projection
  `id(Path_cat(A),x)->eq_refl(x)`;
- generic proof-time associativity, both runtime units, a typed comparison with
  the oriented postcomposition action, and a J-derived propositional comparison
  with `eq_trans` all pass;
- the entire migrated active check suite passes warning-enabled, with the
  unjoinable-pair count reduced from 1,109 to 1,091;
- in contrast, folding the category-level head to `hom_postcomp_fapp0` makes
  the isolated units and pre/post comparison pass but causes the bounded
  associativity consumers to time out;
- deleting the remaining definitional self-opposite collapse from the shared-
  composition candidate preserves the complete migrated suite and lowers the
  warning inventory from 1,091 to 1,072; and
- adding the E1 `PathSym_A` functor/action owner, reflexivity bridge,
  propositional `eq_sym` agreement/involution, and pointwise Core-opposite
  square preserves the complete migrated suite with 1,084 reports and a clean
  strict LHS audit. Twelve reports mention the new functor and remain an
  explicit classification gate.

This selects E0's layered composition and collapse removal and E1's minimal
symmetry core for Phase 4. It does not yet promote either slice, classify the
twelve E1 interactions, supply functor-level natural/equivalence packaging, or
prove global confluence.

## Four Distinct Notions That Must Remain Separate

### Truncation property

`IsTruncGrpd(n,A)` states that `A` is already `n`-truncated. It does not change
the elements of `A` and should be computational only through recursion on the
level and projection of its evidence.

### Truncation reflector

`Trunc_grpd(n,A)`, written mathematically as `||A||_n`, freely turns an
arbitrary type into an `n`-type. It requires higher-inductive/path
constructors and a restricted dependent eliminator. It is not supplied merely
by an inhabitant of `IsTruncGrpd(n,A)`.

### Groupoidal truncation level

An `n`-groupoid is represented homotopy-type-theoretically by an `n`-type.
Thus propositions, sets, ordinary groupoids, and higher groupoids are levels
of the ambient type/groupoid universe.

### Directed categorical dimension axis

An `n`-category is not merely a category whose object classifier is an
`n`-type. It is a directed structure whose iterated hom-categories become
discrete above dimension `n`. This requires a separate recursive predicate
over `Hom_cat`.

The kernel names must distinguish these axes. In particular,
`IsObjTruncCat(n,C)` and `IsNCat(n,C)` must not be aliases.

## Ambient Type/Groupoid Naming

The current kernel name:

```text
Grpd : TYPE
```

classifies general type-like objects with iterated identity structure. It does
not currently impose 1-truncation and therefore behaves more like an ambient
universe of types or infinity-groupoids than a universe of ordinary
groupoids.

The near-term migration should not rename `Grpd`, because it is pervasive.
Instead:

- document `Grpd` as the legacy kernel name for the ambient type/infinity-
  groupoid classifier;
- reserve `GroupoidU_grpd` or an agreed successor name for the universe of
  1-truncated objects;
- permit the future surface language to print the ambient classifier as
  `Type`, `Space`, or another reviewed notation;
- avoid claiming that every `A : Grpd` is an ordinary 1-groupoid.

## Truncation-Level Architecture

### Level codes

Use an explicit native level datatype beginning at `-2`, rather than an
undocumented shift of ordinary natural numbers:

```lambdapi
inductive TruncLevel : TYPE ≔
| trunc_minus_two : TruncLevel
| trunc_succ : TruncLevel -> TruncLevel;
```

Derived readable levels are:

```text
trunc_minus_one = trunc_succ(trunc_minus_two)
trunc_zero      = trunc_succ(trunc_minus_one)
trunc_one       = trunc_succ(trunc_zero)
```

This encoding makes the recursion equations direct and prevents confusion
between homotopy dimension and the internal natural-number representation.

### Recursive truncation predicate

The intended computational equations are:

```text
IsTruncGrpd(-2,A)
  = IsContr(A)

IsTruncGrpd(n+1,A)
  = Pi x y : A, IsTruncGrpd(n,x = y).
```

A candidate Lambdapi surface is:

```lambdapi
symbol IsTruncGrpd (n : TruncLevel) (A : Grpd) : Grpd;

rule IsTruncGrpd trunc_minus_two $A
  ↪ IsContr $A
with IsTruncGrpd (trunc_succ $n) $A
  ↪ @Pi_grpd $A
      (λ x : τ $A,
        @Pi_grpd $A
          (λ y : τ $A, IsTruncGrpd $n (x = y)));
```

This recursion has been mechanically validated in the isolated 2026-07-14
probe. It remains candidate architecture rather than promoted code until its
active owner position, warnings, and diagnostics are reviewed.

Named properties should be transparent views:

```text
IsPropGrpd(A)     := IsTruncGrpd(-1,A)
IsSetGrpd(A)      := IsTruncGrpd(0,A)
IsGroupoidGrpd(A) := IsTruncGrpd(1,A).
```

`IsContr` already exists and remains the semantic base case.

### Universes of truncated objects

The universe of `n`-types should package an ambient classifier with truncation
evidence:

```text
TruncGrpdU(n) = { A : Grpd | IsTruncGrpd(n,A) }.
```

The preferred implementation representation is the record convention below,
not a public chain of anonymous `sigma_Fst(sigma_Snd(...))` projections.

Canonical aliases are:

```text
PropU_grpd      := TruncGrpdU(-1)
SetU_grpd       := TruncGrpdU(0)
GroupoidU_grpd  := TruncGrpdU(1).
```

The future surface may print these as `Prop`, `Set`, and `Gpd`/`Groupoid`.
The active Lambdapi builtin already maps the kernel builtin name `Prop` to
`Grpd`, so the kernel must not immediately reuse the literal symbol `Prop` for
the internal proposition universe.

The universe record needs at least:

```text
trunc_grpd_carrier   : TruncGrpdU(n) -> Grpd
trunc_grpd_evidence  : Pi X : TruncGrpdU(n),
                         IsTruncGrpd(n,trunc_grpd_carrier(X)).
```

Carrier projection and decoding should compute. Truncation evidence is a
proof capability and must not acquire broad proof-erasing runtime rules.

The package itself must not silently be assigned the carrier's truncation
level. Under univalence, the expected universe of `n`-types is generally an
`(n+1)`-type: for example, the universe of propositions is set-like and the
universe of sets is groupoid-like. The first package slice may leave its own
truncation theorem open, but its comments and types must not claim
`IsTruncGrpd(n,TruncGrpdU(n))` without a proof.

### Evidence irrelevance

For paths in `TruncGrpdU(n)` to be controlled by paths/equivalences of the
carrier, the theory eventually needs:

```text
IsPropGrpd(IsTruncGrpd(n,A)).
```

This should be derived from the recursive definition. It must not be replaced
by a global proof-irrelevance rewrite. Until the derivation is available,
univalence of the truncated universes remains incomplete.

The derivation is not independent of the equality architecture. In the
standard HoTT proof, dependent-product closure and the proposition-valuedness
of `IsTruncGrpd(n,A)` use function/Pi extensionality. The side-task dependency
must therefore name the selected observational function-extensionality
interface, not merely "stable paths". The theorem assigning the packaged
universe its expected `(n+1)` truncation level additionally depends on ambient
univalence and the evidence-path comparison.

### Closure and invariance ledger

The property kernel is only the beginning of usable truncation support. Each
following item needs an explicit status (`active`, `probed`, `prerequisite`, or
`deferred`) rather than an assumed closure axiom:

- equality lowers truncation by one recursive step;
- truncation is monotone: `IsTruncGrpd(n,A)` implies
  `IsTruncGrpd(trunc_succ(n),A)`;
- truncation is invariant under `TypeEquiv`;
- dependent products preserve an appropriate fixed truncation level;
- dependent sums use the truncation of both base and fibres with the standard
  level bound rather than an unconditional same-level rule;
- contractibility, proposition, set, and 1-groupoid evidence is itself
  property-valued at the required level;
- carrier/evidence paths in `TruncGrpdU(n)` are controlled by carrier paths;
- univalence for `TruncGrpdU(n)` agrees with ambient univalence restricted to
  equivalences preserving the packaged property.

Only the first recursion equations are required for the earliest MVP. The
remaining entries are prerequisites for claiming that the truncated universes
are closed, univalent, or convenient foundations for later HoTT examples.

### Truncation reflectors

The desired later interface is:

```text
Trunc_grpd(n,A)       : Grpd
trunc_intro(n,A)      : A -> Trunc_grpd(n,A)
trunc_is_truncated    : IsTruncGrpd(n,Trunc_grpd(n,A))
trunc_elim            : elimination into n-truncated families.
```

This is a higher-inductive construction. It is deferred until the
observational equality and higher-constructor elimination architecture is
settled. No opaque `Trunc_grpd` plus unrestricted eliminator should be promoted
as a shortcut, because that would provide neither the desired computation nor
the required universal property.

## Finite Dependent Record Convention

### Assessment of the proposed manual pattern

The proposed pattern of a carrier type, one constructor, named projections,
and constructor projection rules is fundamentally sound. It is preferable to
nested Sigma when:

- the structure has many named fields;
- later fields depend on earlier fields;
- field names are part of the mathematical API;
- observational equality should follow the field telescope;
- a stable constructor head is useful to computation.

For ordinary finite data structures, the carrier should normally be declared
with Lambdapi's parametrized `inductive` command rather than as an unrelated
opaque `constant`. Lambdapi then generates the dependent eliminator and its
constructor beta rule. Named record projections still have to be declared
manually.

### Canonical schematic encoding

For a parameter telescope `P` and dependent fields, use the following pattern:

```lambdapi
(P : Parameters) inductive RData : TYPE ≔
| Struct_R
    (field0 : Field0 P)
    (field1 : Field1 P field0)
    (field2 : Field2 P field0 field1)
    : RData P;

constant symbol R_grpd (P : Parameters) : Grpd;
rule τ (R_grpd $P) ↪ RData $P;

symbol r_field0 [P] (r : RData P) : Field0 P;
rule r_field0 (@Struct_R $P $f0 $f1 $f2) ↪ $f0;

symbol r_field1 [P] (r : RData P) : Field1 P (r_field0 r);
rule r_field1 (@Struct_R $P $f0 $f1 $f2) ↪ $f1;
```

The exact implicit slots require an owner-position probe. The example states
the convention, not a mechanical rule about explicit arguments. Prefix
parameters of a parametrized inductive are already in scope for its
constructors and must not be duplicated in the constructor binder. Generated
constructor applications will still expose those parameters in their
elaborated form. Projection LHSs should infer non-discriminating parameters as
`_` wherever the subject-reduction and warning audit permits.

For the covering-sieve example, the user's `Struct_cov_sieve` idea therefore
has the right semantic shape. The recommended refinements are:

1. use a one-constructor dependent inductive carrier if the structure is
   ordinary finite data;
2. expose `cov_sieve_cat`, `cov_sieve_func`, and `cov_sieve_hom` as named
   projections with constructor beta rules;
3. use current `Cat`/functor/hom names in promoted v3.2 code rather than
   obsolete lowercase spellings;
4. add an explicit eliminator wrapper only when the generated eliminator has
   an inconvenient parameter/motive surface;
5. do not install runtime record eta by default.

### When not to use an inductive record

Use an opaque stable facade with destructors instead when the object is
intentionally abstract, coinductive, or operationally specified only through
observations. Current examples include `OmegaEquiv` and the computational
`DefIso` facade. The proposed indexed `Adjunction(F,G)` is another operational
interface: its unit/counit observations retain stable heads rather than
projecting by ordinary record beta to arbitrary raw operations.

Use nested Sigma when the package is small and genuinely existential, for
example a map together with one property. `TypeEquiv` may retain a Sigma
semantic presentation if its path algebra remains manageable. Named
projections should hide nesting from consumers.

### Observational equality of records

For a record with fields `f0`, `f1`, and `f2`, equality is a dependent path
telescope:

```text
RPath(r,s)
  = Sigma p0 : f0(r) = f0(s),
      PathOver(Field1,p0,f1(r),f1(s))
      ... followed by the transported path for f2.
```

In the final observational design this should be a dedicated record identity
classifier with named fields, not definitionally an ordinary nested Sigma.
Later path fields depend on all earlier path fields.

The minimum generated/manual package for an observational record is expected
to contain:

- the data carrier and constructor;
- named data projections and beta rules;
- the dedicated path-record carrier;
- named path projections;
- structural reflexivity observations;
- structural action/substitution observations;
- an eliminator or extensionality theorem;
- diagnostics for constructor-first and projection-first reduction.

### Optional external generator

The repeated boilerplate is suitable for a future deterministic repository
tool, for example `scripts/gen_record.py`, driven by a small field-telescope
schema. A generator may emit checked Lambdapi declarations, projection rules,
path-record skeletons, and diagnostic templates.

The generator must not become a second semantic authority. Generated output
must follow the same owner rules, remain reviewable, and be validated by
Lambdapi. This tooling is optional and should follow one or two successful
manual record implementations.

## Groupoidal Truncation Versus Directed `n`-Categories

### `n`-groupoids

Use the HoTT identification:

```text
NGroupoid(n) = TruncGrpdU(n).
```

Thus:

```text
(-1)-groupoids = propositions
0-groupoids    = sets
1-groupoids    = ordinary groupoids
n-groupoids    = n-types.
```

This is a property/universe hierarchy inside the ambient `Grpd` classifier.

### Object truncation of a category

Define the independent property:

```text
IsObjTruncCat(n,C)
  := IsTruncGrpd(n,Obj(C)).
```

This says nothing by itself about non-invertible arrows or higher directed
cells.

### Recursive directed categorical dimension

Introduce a nonnegative native dimension code:

```lambdapi
inductive CatDim : TYPE ≔
| cat_zero : CatDim
| cat_succ : CatDim -> CatDim;
```

The proposed recursive directed-dimension property is:

```text
IsNCat(0,C)     := IsDiscreteCat(C)
IsNCat(n+1,C)   := Pi x y : Obj(C), IsNCat(n,Hom_cat(C,x,y)).
```

The base `IsDiscreteCat` is a real prerequisite. It expresses that `C` has no
directed information beyond the equality/groupoidal structure of a set of
objects. The selected plan-level definition is the exact Product:

```text
IsDiscreteCat(C)
  := IsSetGrpd(Obj(C))
     × OmegaEquivAlong_{Cat_cat}(Core_incl_func(C)).
```

The kernel spelling of `×` is `Product_grpd`; it is data/evidence packaging,
not an unproved logical conjunction or an opaque predicate.

Here

```text
Core_incl_func(C)
  : Hom_{Cat_cat}(Core_cat(C),C)
  = Functor(Core_cat(C),C),
```

so the `Cat_cat` subscript fixes the ambient category in which this already-
selected functor is required to be an omega-equivalence. The selected
architecture makes that fixed-map notion primary rather than recovering it as
the fibre of an opaque package projection.

The two factors are nonredundant. `IsSetGrpd(Obj(C))` alone says nothing about
non-identity directed arrows. Conversely, equivalence with `Core_cat(C) =
Path_cat(Obj(C))` without the set condition can preserve higher object-path
information, so it does not by itself make `C` zero-dimensional.

The required homwise adequacy consequence is also fixed now. Define the
existing generic hom action in readable notation by:

```text
core_incl_hom_func(C,x,y)
  := fapp1_func(Core_incl_func(C),x,y)
  : Functor(Path_cat(x = y),Hom_cat(C,x,y)).

fapp0(core_incl_hom_func(C,x,y),p)
  -> path_to_hom_C(p).
```

Before `IsDiscreteCat` is promoted as the base of `IsNCat`, its fixed-map
evidence must derive:

```text
discrete_core_homwise
  : IsDiscreteCat(C)
    -> Pi x y : Obj(C),
       OmegaEquivAlong_{Cat_cat}(core_incl_hom_func(C,x,y)).
```

This is the recursive/full-faithfulness form of “no extra directed arrows.”
At the immediately visible arrow level it must expose an inverse
`hom_to_path(d,f) : x = y` and propositional/omega-coherent round trips:

```text
hom_to_path(d,path_to_hom(p)) = p
path_to_hom(hom_to_path(d,f)) = f.
```

These are diagnostics/theorems, not broad runtime cancellation rewrites. The
preferred owner is a general hom-action consequence of
`OmegaEquivAlong_{Cat_cat}(F)`, with the core inclusion as its first concrete
consumer. Duplicating homwise evidence as a third `IsDiscreteCat` field is a
fallback only if that derivation is shown infeasible.

The semantic/reference presentation is the homotopy fibre:

```text
OmegaEquivFibre(F)
  := Sigma e : OmegaEquiv(Cat_cat,A,B),
       omega_equiv_to(e) = F.
```

The equality in the fibre formula is ordinary HoTT practice: it says that the
forward map selected by an equivalence package is the fixed map under study.
It remains useful as a specification and as a comparison target during
migration. It is not the best runtime interface, because recovering `F`
otherwise travels through an equality proof.

The proposed end state instead mirrors the active
`IsEquivMap(f)`/`TypeEquiv(A,B)` split:

```text
OmegaEquivAlong_C(f) : Grpd

OmegaEquiv_C(x,y)
  := Sigma f : Hom_C(x,y), OmegaEquivAlong_C(f)

omega_equiv_to(e)       := sigma_Fst(e)
omega_equiv_evidence(e) := sigma_Snd(e).
```

`OmegaEquivAlong_C(f)` stores or exposes the selected inverse arrows and the
recursively required hom-equivalence/coherence data while `f` is an index. The
name is intentionally neutral between operational certificate and proved
property. `IsOmegaEquivArrow_C(f)` is reserved as an alias after
property-valuedness is established. Its
higher observations may refer to the packaged `OmegaEquiv` at the next hom
level:

```text
omega_equiv_along_left_inv(u)  : Hom_C(y,x)
omega_equiv_along_right_inv(u) : Hom_C(y,x)

omega_equiv_along_left_cell(u)
  : OmegaEquiv_{Hom_C(x,x)}(left_inv(u) o f,id_x)

omega_equiv_along_right_cell(u)
  : OmegaEquiv_{Hom_C(y,y)}(f o right_inv(u),id_y).
```

These higher cells, rather than raw cancellation rewrites, are the recursive
omega-equivalence witnesses. In particular, the architecture does **not** add:

```text
left_inv(u) o f  -> id_x
f o right_inv(u) -> id_y.
```

Such equations would strictify higher equivalence into judgmental equality.
The fixed `f` is merely an index in the endpoint types of the stable
`left_cell`/`right_cell` observations. Reflexive, opposite, Product, and later
constructors discriminate on their own evidence constructors/observations,
not on the variable `f`. The exact inverse and higher-cell telescope has been
validated in the indexed-structure probe.

This arrangement retains the ordinary first-class type needed as the codomain
of categorical univalence while making a declaration about an already-named
arrow direct:

```text
myF       : Functor(A,B)
myWitness : OmegaEquivAlong_{Cat}(myF)
myEquiv   := (myF,myWitness)

omega_equiv_to(myEquiv) ≡ myF.
```

No equality witness or per-instance unification rule is required for that
projection. The 2026-07-14 indexed-structure probe validates formation,
introduction, both Sigma projections, and the fixed-arrow recursive
higher-cell endpoint types. Its latest warning-enabled run has no probe-local
unjoinable critical-pair report; scratch-local replaceable-variable advisories
remain to clean before promotion.

The active `OmegaEquiv` is an opaque observation interface rather than this
Sigma package. Migrating it is consequently a normal-form migration, not a
transparent alias edit. A compatibility bridge from fixed-map evidence into
the old interface also has append-only feasibility evidence and may be useful
during staging, but it is transitional rather than the selected final two-layer
architecture. The
migration must route the current reflexive/opposite/Product generators and all
destructors through the fixed-map evidence layer, then revalidate both
univalence decoders and their round trips.

The fixed-map evidence is intended to be property-like, but that must be
established from its recursive coherence or an equivalent contractible-fibre
characterization; it is not licensed by a suggestive name. Until then, paths
of `IsDiscreteCat`/`NCat` packages still contain an evidence-field obligation.

### Fixed-map omega-equivalence promotion ladder

The passing probes establish the telescope and package shape, not yet the new
recursive owner. Candidate D is therefore divided into two gates. **D0** is a
fresh owner-position recursive-interface probe, not a public normal-form
migration. **D1** is the later public `OmegaEquiv` migration. Candidate D must
advance through the following ladder before the report calls the migration
globally coherent:

1. place a general-`C` `OmegaEquivAlong_C(f)` owner at the intended source
   position in a full-file copy, independent of the old opaque `OmegaEquiv`
   owner;
2. define the first-class `OmegaEquiv_C(x,y)` Sigma package, declare the
   inverse observations and recursive higher-cell observations returning that
   package at the next hom level, and validate generic map/evidence projection
   beta before any dependent higher-cell beta;
3. implement the reflexive fixed-map generator and check its recursive
   higher-cell observations through at least the next hom level;
4. implement opposite closure with the correct endpoint reversal and both
   higher-cell projections;
5. implement one representative binary constructor, initially Product, and
   test constructor-first, projection-first, and decoder-first diamonds;
6. migrate the active `omega_equiv_*` destructors, `idtoequiv_cat`, and
   `omega_equiv_path` declarations to the new package in the same full-file
   candidate; jointly rerun the `OETU-CAT-UNIV-DECODER`-owned round trips,
   `path_to_hom` squares, and one Product decoder consumer;
7. declare one concrete named functor `F`, evidence `u : OmegaEquivAlong(F)`,
   and package `(F,u)`, then exercise univalence/action and one recursive
   next-hom observation without a per-instance `unif_rule`;
8. compare the operational evidence propositionally in both useful directions
   with `OmegaEquivFibre(F)`, while keeping the theorem that the evidence is a
   proposition as a separately statused obligation; and
9. pass source-order subject reduction, inferred-LHS audit, warning comparison,
   both-order diagnostics, and bounded full-suite timing. No evidence field may
   be erased before the property theorem exists.

Steps 1--3 are the D0 gate. Step 2 belongs in D0 rather than D1: the recursive
left/right cell observations return first-class omega-equivalences in the next
hom-category, so they need the minimal Sigma package (or an exactly equivalent
internal package) in their result types. Postponing that package would require
a provisional second recursive codomain and would weaken the owner test. D0
must pass at source position without implementing its observations through the
old opaque `OmegaEquiv`; it may coexist under fresh candidate names and does
not by itself migrate the public normal form. A passing D0 result establishes
recursive-owner implementation feasibility, not Candidate D completion.

Steps 4--7 are D1's closure, public-consumer, decoder, and integrated-witness
migration. Steps 1--7 together in the full-file candidate remain the minimum
public promotion gate, with the applicable source-order, warning, and timing
checks from Step 9 repeated for D0 and then for the completed D1 candidate.
Step 8's property theorem may remain a named prerequisite for the first
runtime migration, but `IsDiscreteCat` package equality and any proof-field
irrelevance continue to depend on it.

### Indexed adjunctions rather than a permanent `Along` facade

The same fixed-data principle applies more directly to adjunctions. The
proposed end state replaces the current first-class `Adjunction(R,L)` owner by
an adjunction relation indexed by the already-selected functors:

```text
Adjunction [R L : Cat]
  (F : Functor(R,L))
  (G : Functor(L,R))
  : Grpd

unit_adj_transf(J)   : id_R => G o F
counit_adj_transf(J) : F o G => id_L.
```

The triangle cut-elimination rules then mention `F` and `G` directly. In
schematic surface notation, the left rule is:

```text
counit_adj_transf(J)[f] o F[unit_adj_transf(J)[g]]
  -> f o F[g].
```

The exact two active rule shapes have been reproduced with the indexed
relation and pass the focused probe. Neither rule discriminates on the
variable `F` or `G`. Their rigid heads are the outer `comp_fapp0`, the stable
`unit_adj_transf(J)`/`counit_adj_transf(J)` observations, and the surrounding
`tapp1_fapp0`/`fapp1_fapp0` application structure. The indices are recovered
and checked by their repeated occurrence in those patterns.

There is no permanent need for a second `AdjunctionAlong(F,G)` classifier. If
a compatibility surface is retained while consumers migrate, its old functor
views can be transparent definitions:

```text
left_adj_func [F G] (_ : Adjunction(F,G))  := F
right_adj_func [F G] (_ : Adjunction(F,G)) := G.
```

Because these are transparent views, no rewrite rule should be headed by them;
rules that currently pattern-match the old opaque projections must migrate to
the `F`/`G` indices. In particular, the opposite operation can expose its
selected functors in its result type:

```text
Op_adjunction(J) : Adjunction(Op_func(G),Op_func(F)).
```

The current runtime rules projecting the left/right functors of an opposite
adjunction then disappear, while the opposite unit/counit rules remain headed
by the stable unit/counit observations. If a consumer genuinely needs an
adjunction without already knowing either functor, define a separate
existential package:

```text
AdjunctionPackage(R,L)
  := Sigma F : Functor(R,L),
       Sigma G : Functor(L,R), Adjunction(F,G).
```

The focused probe also establishes a narrower fact about the rejected
transitional concern: with the **current** opaque stable `left_adj_func` head,
the beta rule

```text
left_adj_func(adjunction_from_along(j)) -> F
```

does match and compute. Nevertheless, replacing the owner by the indexed
relation is simpler and avoids keeping two permanent classifiers.

An opaque `left_adj_func(J)` connected to `F` only by a `unif_rule` is not an
equivalent **runtime** design. The probe verifies that such a rule can make an
`eq_refl`-typed comparison elaborate while `left_adj_func(J) ≡ F` still fails
conversion. If selected, the rule is a trusted proof-time equation rather than
mere syntactic sugar, but it still cannot supply the runtime projection needed
by functor application, triangle normalization, or mate computation. Since
`F` is already an index here, the transparent/direct-index presentation is
both simpler and requires no additional trusted proof-time equation.

The unit and counit have a different role from the left/right functor views.
They must remain stable runtime observations:

```text
unit_adj_transf(J)
counit_adj_transf(J).
```

Suppose a concrete declaration explicitly selects named operations:

```text
myF       : Functor(R,L)
myG       : Functor(L,R)
myUnit    : id_R => myG o myF
myCounit  : myF o myG => id_L
myAdj     : Adjunction(myF,myG).
```

The binding between `myAdj` and those operations must be part of the
declaration contract—through constructor/declaration data, explicit agreement
fields, or deliberately selected trusted proof-time declaration equations.
For the last choice, the bridge is:

```text
unif_rule unit_adj_transf(myAdj)   ≡ myUnit   ↪ [ ... ]
unif_rule counit_adj_transf(myAdj) ≡ myCounit ↪ [ ... ].
```

Each rule must be narrowly typed and mechanically exercised with a typed
reflexive path, schematically:

```text
my_unit_agreement
  : unit_adj_transf(myAdj) = myUnit
  := eq_refl(myUnit).
```

This is a genuine path term in the theory extended by the `unif_rule`, but it
is not independent evidence for the equation that made the term typecheck.
The append-only probe declares `ReviewNamedAdj`, `ReviewNamedUnit`, and
`ReviewNamedCounit` independently, so it demonstrates exactly these mechanics
and no semantic agreement between the constants. A promoted per-instance rule
must therefore either be generated from an explicit declaration binding or be
labelled as a trusted instance postulate. An explicit agreement field/path
that does not itself rely on the same rule is the alternative. This condition
does not require every generic, semantically justified proof-time law to be
duplicated by a second internal path.

An `assertnot` conversion check records that the bridge does not select a
runtime normal form. The canonical triangle term must retain
`unit_adj_transf(myAdj)` and `counit_adj_transf(myAdj)`. A raw composite written
only with `myUnit` and `myCounit` does not compute by the generic triangle rule,
because proof-time unification does not rewrite it back to the stable heads.

Ordinary constructor projection betas

```text
unit_adj_transf(AdjunctionIntro(eta,epsilon))    -> eta
counit_adj_transf(AdjunctionIntro(eta,epsilon)) -> epsilon
```

are therefore rejected for the primary computational interface unless an
alternative owner supplies and audits the corresponding raw triangle rules.
The negative probe demonstrates that inner projection normalization can erase
the observations before the outer generic triangle is selected; the warning
checker did not report a local critical pair for this lost computation.

A future `declare_equivalence` or `declare_adjunction` source generator may
emit fixed-map evidence declarations, optional Sigma packages, narrowly typed
proof-time operation comparisons, their declared trust class/backing, and
their typed/negative diagnostics. A
surface elaborator may also print a user's operation names while elaborating
computational triangle terms to the stable observation spellings. It should
not generate an unrecorded per-instance equation between otherwise independent
constants or generate instance-specific triangle rewrites by default; any such
rewrite generation is a separate critical-pair-audited design.

Consequently, the selected `IsDiscreteCat` contract must be implemented and
its homwise adequacy validated before `IsNCat` is promoted. The blocker is
specifically fixed-functor omega-equivalence and its hom-action theorem—not an
unspecified need for every possible notion of category equivalence.

The recursive definition matches the iterated-hom architecture: an ordinary
1-category has discrete hom-categories; a 2-category has ordinary
hom-categories; and so on.

The intended comparison between the two truncation axes should be recorded as
a theorem target:

```text
IsNCat(n,C) -> IsObjTruncCat(n,C).
```

Its proof uses global categorical univalence together with the fixed-arrow
equivalence property and the required evidence-truncation results. It is not a
formation rule for `IsNCat`, and the converse is false in general because
object truncation alone does not remove directed arrows.

This is the project's strict/iterated-hom notion of finite categorical
dimension. It is distinct from an `(n,1)`-category presented as a complete
semi-Segal type. Connections with Segal/Rezk presentations are future
comparison theorems, not definitional equalities.

### Packaged finite-dimensional categories

Once `IsNCat` is stable, define record packages:

```text
NCat(n) = { C : Cat | IsNCat(n,C) }
ZeroCat = NCat(0)
OneCat  = NCat(1).
```

Because the current policy makes every `C : Cat` globally univalent, these
packages need not carry an additional `CatUnivalence(C)` field. Their extra
data is finite-dimensionality evidence.

Carrier projections should compute:

```text
ncat_carrier(Struct_ncat(C,h)) -> C.
```

No runtime eta or proof-field erasure should be installed initially.

### `OneCat` and ordinary isomorphism univalence

The current global symbol:

```text
cat_iso_univalence(C) : CatIsoUnivalence(C)
```

is quarantined immediately for successor-architecture work and is replaced by
the dimension-correct interface:

```text
onecat_iso_univalence
  : Pi C : OneCat,
      CatIsoUnivalence(onecat_carrier(C)).
```

The preferred final result is to derive this from:

- global `CatUnivalence` into `OmegaEquiv`;
- the discreteness/truncation of all hom-categories of a `OneCat`;
- a comparison between `OmegaEquiv` and `IsoEvidence` at that level.

A scoped operational axiom is acceptable before the derivation. The unscoped
active symbol may remain temporarily as a compatibility surface during the
bounded migration, but no new general-`Cat` work may consume it.

### Universes of `n`-categories

Later interfaces may include:

```text
NCat_grpd(n) : Grpd
NCat_cat(n)  : Cat
OneCat_grpd  : Grpd
OneCat_cat   : Cat.
```

`NCat_cat(n)` should be the full category of `n`-categories and ordinary
functors between their carriers. Its univalence and equality must account for
the fact that `IsNCat(n,C)` is property-valued. This depends on evidence
irrelevance and the repaired category-univalence decoder, and is not an early
slice.

## Full Observational Equality Target

### Selected end state

Equality should compute according to the classifier of its endpoints:

- record equality is a dependent record of field paths;
- Sigma equality is a base path plus a fibre path over it;
- Pi/function equality relates values at related inputs;
- universe equality is equivalence;
- reflexivity and action/substitution compute structurally;
- later inductive/coinductive equality follows the corresponding structural
  observation scheme.

The identity classifier for a record or inductive structure should normally
be a dedicated identity structure. It may be definitionally isomorphic to a
Sigma encoding without being literally the same public record.

Making the public `=` head itself reduce to those dedicated structures is a
deliberately strong Emdash computational choice, not something obtained merely
by citing observational type theory. A dedicated identity-view classifier with
encode/decode maps remains the fallback boundary until direct public rules pass
owner-position confluence, subject-reduction, and performance audits. This
fallback does not weaken the eventual full-observational target; it prevents a
failed global rewrite orientation from becoming the only representation.

### Immediate MVP boundary and eventual universe identity

The statement “universe equality is equivalence” describes the eventual
full-observational endpoint, not the immediate H1 implementation gate. The
near-term H1 contract is:

```text
idtoequiv_grpd : (A = B) -> TypeEquiv(A,B)
grpd_equiv_path / ua_grpd : TypeEquiv(A,B) -> (A = B)
both round trips propositionally;
selected transport/action along the decoded path computes through the forward map.
```

An analogous contract uses `OmegaEquiv` at the category layer. This interface
can be computationally useful before the public equality classifier of
`Grpd_grpd` or `Cat_grpd` itself exposes equivalence data.

The later `OETU-UNIVERSE-EQUALITY` track must choose, independently at each
universe layer:

- direct public equality reduction to `TypeEquiv`/`OmegaEquiv`, or a dedicated
  universe identity-view classifier with encode/decode;
- the canonical shaped universe-reflexivity owner;
- structural action/transport and any additional computational shaped `J`;
- both decoder round trips and Product/Pi/Sigma action diamonds;
- the interaction with fixed-map omega-equivalence and the open-world former
  registry; and
- the precise unstratified `Cat_cat : Cat` boundary.

Glue, bisimulation, cubical composition, or fibrancy mechanisms in external
systems are possible comparison points, not required Emdash encodings. This
track begins from the local Kosta--Došen cut owners and Lambdapi rewrite/unif
capabilities and is explicitly allowed to find a smaller native formulation.
The track is complete only after owner-position and integrated computational
evidence; no external architecture is reproduced merely to match its surface.

### `J`, shaped reflexivity, and structural action

The selected candidate is a **hybrid generic/shaped equality architecture**.
The active primitive `=`/`eq_refl`/`ind_eqr` interface is retained, not merely
as a temporary embarrassment but as the ordinary HoTT-compatible behavior of
an unknown or unsupported classifier. If `a : Grpd` is opaque to the rewrite
system, equality stays opaque and generic `ind_eqr` has its traditional beta
only on literal `eq_refl`.

When `a` is a registered shaped former, its equality classifier and selected
reflexivity/action observations may reduce structurally. Generic `ind_eqr`
still eliminates paths at that classifier and remains available for
propositional reasoning. Its generic judgmental beta is still only the literal
reflexivity case unless a narrowly audited former registration adds more
computation. Thus Candidate H's eta proof by generic J is legitimate under the
hybrid contract **once its reflexive Pi coherence basis is selected** and does
not depend on a future fibrancy implementation. The current stable-head probe
selects that basis through a trusted proof-time equation; it does not derive
the equation merely by typing `eq_refl`. The result also does not prove that J
now computes on arbitrary structured Pi-path constructors.

This removes the alleged architectural contradiction with traditional HoTT at
generic types; it is not itself a normalization, consistency, or model proof.
Every former-specific rule still requires subject reduction, overlap,
performance, and eventually semantic justification.

The design therefore separates four achievements that were previously too
easily conflated:

1. a conservative classifier MVP: equality exposes a record/Sigma/Pi path
   view; projections of literal reflexivity compute; generic `J` computes on
   literal reflexivity;
2. shaped reflexivity and reflexive shaped `J`: a supported former selects a
   stable reflexivity head whose path projections compute structurally, and
   `ind_eqr` recognizes that head at the reflexive endpoint;
3. structural action: registered open maps and dependent sections act on
   non-reflexive structured paths through explicit `ObsAction`/`ObsSubst`-like
   data;
4. additional computational dependent elimination on arbitrary structured
   path constructors: registered classifiers and motives expose the
   fibrancy/elimination capability from which sound structured `J` computation
   is obtained.

The conservative MVP and generic propositional J do not require (3) or (4),
but (2)--(4) are **not
deferred by policy**. They are immediate design/implementation tracks and may
overtake or simplify the conservative route as soon as their probes are
globally credible.

The 2026-07-14 probe gives a concrete candidate for (2):

```text
PairPathRefl(r) : PairPath(r,r)

eq_refl(PairGrpd(A,B),r) -> PairPathRefl(r)
pair_path_first(PairPathRefl(r)) -> eq_refl(first(r))
pair_path_second(PairPathRefl(r)) -> eq_refl(second(r))
ind_eqr(...,r,PairPathRefl(r)) -> branch.
```

The stable head is essential: rewriting directly to a raw nested path-record
constructor produced competing reductions. It is also not sufficient in
isolation. Every generic consumer whose beta rule discriminates on literal
`eq_refl`—the probe exercised strict composition, symmetry, and `ind_eqr`—must
register a narrow rule for the shaped head at that consumer's owning position.
With those bridges, the warning-enabled probe added no local critical-pair
warning.

The successful rule order is also part of the evidence. The shaped former head
was declared before the fresh generic consumers, and its bridges were placed
at those consumers before their literal-`eq_refl` rules. A late append-only
bridge may make final terms reduce while still hiding the critical pair from
the owner's sequential warning check. For the open-world architecture, the
active migration must therefore choose one of these scalable arrangements:

- declare the initially supported former/reflexivity heads before a centralized
  generic-consumer registry;
- refactor direct literal-reflexivity consumers through the selected structural
  action/`J` owner so that fewer former-specific bridges are required; or
- retain literal `eq_refl` as the runtime head for a former and expose a shaped
  constructor/proof-time comparison until a safe ordering migration exists.

The first shaped slice may use a closed, explicitly listed set of supported
formers. It must not claim that a successful late extension proves an
indefinitely open registration mechanism.

This candidate may be implemented immediately after it passes the full
promotion protocol for a nondependent and a dependent record. Promotion
requires all of the following:

- candidate rules inserted at their intended owner positions in a full-file
  copy, not merely appended after all consumers;
- declaration and registration order is feasible in the active source without
  forward-reference tricks or duplicating a generic semantic owner;
- constructor-first and projection-first joins for the supported former;
- generic literal-`eq_refl` `J` remains unchanged for unsupported classifiers;
- all current generic consumers of literal reflexivity are inventoried and
  either remain parametric or receive a narrow former registration;
- Sigma, Pi, one dependent path telescope, and one nested supported former are
  tested before claiming a reusable protocol;
- subject reduction, warning delta, both reduction orders, bounded full check,
  and focused typed `eq_refl` diagnostics pass.

Achievements (3) and (4) are stronger computational claims. Retaining the
primitive generic `ind_eqr` permits ordinary propositional elimination of an
arbitrary path, exactly as in the current HoTT-style interface. What is not
sound is a new rewrite that recognizes an arbitrary path-record constructor
and simply returns the reflexive branch for an arbitrary motive. Nor can an
arbitrary Lambdapi function silently acquire structural path action merely
because an `ObsSubst` symbol has been declared. The design
must select whether action/fibrancy is carried by registered classifier and map
packages, supplied by former-specific eliminators, or synthesized by a future
surface elaborator. Immediate candidate architectures include a
former-specific structural-action facade, explicit `ObsAction` and
`ObsDAction` packages, an `ObsSubst` protocol from which compatible `J` is
derived, or another stable higher-dimensional action head. The design must
eventually specify:

- structural reflexivity/degeneracy;
- symmetry and higher degeneracies in canonical form;
- action of open terms on structured paths;
- transport through dependent fields;
- the fibrancy/dependent-elimination capability accepted by arbitrary motives;
- readback or rewrite normal forms for higher composites.

Until that capability is selected, generic `ind_eqr` remains the ordinary
opaque eliminator. It may support propositional theorems such as Pi eta, but
only explicitly registered formers may claim additional runtime computation
for arbitrary structured-path `J`.

Earlier reports constrain known-bad encodings but do not veto a new solution
that passes these criteria.

### Open-world classifier protocol

The current `Grpd` universe is an open collection of stable classifier heads,
not an inductive-recursive closed universe of codes. The near-term
observational design should therefore use an explicit registration protocol:

1. each supported type former owns one equality classifier rule;
2. each former names one canonical stable classifier head; reducible aliases
   and alternative presentations state which owner has precedence;
3. it selects either conservative reflexivity observations or one stable
   shaped-reflexivity head, never competing runtime normal forms;
4. each generic literal-reflexivity consumer states whether and how a shaped
   former registers with it;
5. it owns or explicitly marks pending structural action, dependent action,
   and fibrancy/elimination projections;
6. it supplies focused critical-pair tests against generic consumers;
7. unsupported classifiers remain opaque rather than receiving guessed
   equations.

The current literal-reflexivity inventory is wider than `ind_eqr`, composition,
and symmetry. It includes the Sigma/Product projection observers, Pi
reflexivity, `Core_incl_func`, `coe_grpd`, `idtoequiv_grpd`, `idtoiso_cat`, and
`idtoequiv_cat`. Every shaped migration must re-run this lexical/type-aware
inventory and either register the canonical former at each applicable owner or
refactor that consumer through the selected generic action/elimination owner.

A later closed inductive-recursive universe of type codes might permit a more
uniform normalization proof, but it would be a major migration and would make
extensibility harder. This proposal does not choose that migration now.

### Prototype and public-owner probes before migration

Before changing the active `=`/`eq_refl`/J owners again, continue with two
complementary owner-position full-file probes. A specification-only surface may
use heads such as:

```text
ObsEq(A,x,y)
ObsRefl(A,x)
ObsSubst(...)
```

In addition, the viable shaped-reflexivity candidate must be tested on fresh
public-like equality heads at the exact positions where the real owners and
generic consumers would live. `ObsEq` alone can miss migration interactions.
Together the probes should cover one nondependent record, one dependent
record, Sigma, and Pi. They must demonstrate:

- structural record path formation;
- reflexivity projections;
- related-input function equality;
- dependent field transport;
- both orders of every projection/refl reduction;
- shaped-head registration with `ind_eqr`, composition, symmetry, transport,
  core inclusion, univalence encoders, and every other inventoried generic
  literal-reflexivity consumer;
- either structural action plus registered dependent elimination, or an
  explicit, accurately named boundary at reflexive shaped `J`;
- a credible migration path for current `=` consumers.

Only after that probe should a slice migrate the public equality owner.

## Global `Cat` Univalence Policy

The selected near-term policy is:

```text
for every C : Cat,
  cat_univalence(C)            : CatUnivalence(C)
  cat_univalence_by_decoder(C) : CatUnivalenceByDecoder(C).
```

This is an explicit global operational axiom. Under this policy,
non-univalent `Cat` values are not part of the intended semantics, even though
the primitive `Cat` declaration does not syntactically store a univalence
field.

Reports should remove or correct the claim that non-univalent intermediate
categories remain semantically expressible while the global instance applies
to every `C`.

The policy includes `Cat_cat`. The following remain deferred and must be
listed as such:

- a stratified hierarchy `Cat_i : Cat_(i+1)`;
- an impredicative or self-universe model;
- consistency/canonicity of the unstratified global axiom;
- constructor-specific computation for category-universe univalence.

The operational axiom is permitted to remain while these questions are open.
No report may infer a model-existence result merely because Lambdapi accepts
the signature.

The legacy ordinary-isomorphism capability is not part of this selected global
policy. The active source still exposes `cat_iso_univalence(C)` for every
`C : Cat` as an exploratory 1-categorical approximation. From Phase 0 onward:

- no new redesign declaration, theorem, or computation may depend on the
  global ordinary-iso capability;
- existing consumers and checks are labelled compatibility-only until their
  migration is scheduled;
- `CatUnivalence(C)` with recursive `OmegaEquiv` is the general categorical
  interface used by new work; and
- `CatIsoUnivalence` returns only as a `OneCat`-scoped derivation or explicit
  ordinary-dimensional assumption.

This is an architectural quarantine from the outset even if removal of the
legacy active symbols is staged to preserve a bounded migration.

## One Operational Inverse Per Univalence Layer

The decoder-oriented interfaces are selected as the eventual operational
owners:

```text
grpd_equiv_path
iso_evidence_path       // OneCat-scoped in the final design
omega_equiv_path.
```

The groupoid owner can be selected and finalized near the beginning of the
migration, before constructor-specific univalence closure and paths of
packaged truncated universes are claimed. The categorical **name and
orientation contract** should also be selected early so that new code does not
accumulate against another inverse, but its public domain/codomain, round trips,
and constructor computation cannot be finalized before Candidate D1 replaces
the `OmegaEquiv` normal form. That finalization is jointly scheduled with D1,
not implemented once against the old classifier and then independently
implemented again.

Capability-oriented names should be derived aliases or connected by named
agreement paths:

```text
ua_grpd(U,e)             = grpd_equiv_path(e)
isotoid_cat(U,i)         = iso_evidence_path(i)
equivtoid_cat(U,e)       = omega_equiv_path(e).
```

The equalities begin propositionally. Runtime orientation is added only when
one side is selected as a genuine evaluator normal form and both reduction
orders have been measured.

For an arbitrary supplied capability `U`, agreement with the global selected
decoder is additional coherence data; it does not follow merely because both
terms have inverse-like types. A `unif_rule` can deliberately postulate that
agreement at proof time, but then it is the trusted coherence law rather than
evidence derived from the two inverse-like types. The interface must either
store/expose agreement, restrict to the canonical capability, justify a
generic selected proof-time law, or label the comparison as an explicit
postulate/theorem prerequisite.

The coherence API must eventually include:

```text
coe_grpd(p,a)
  = type_equiv_to(idtoequiv_grpd(p),a)

iso_evidence_to(idtoiso_cat(p))
  = path_to_hom(p)

omega_equiv_to(idtoequiv_cat(p))
  = path_to_hom(p)

path_to_hom(omega_equiv_path(e))
  = omega_equiv_to(e)
```

Both round trips from each `EquivByInverse` capability need named projections
and diagnostics. Their existence inside a nested Product package is not an
adequate public coherence API. The groupoid decoder task owns its two round
trips and the `coe_grpd` transport/action square. The categorical decoder task
owns its two round trips and the `path_to_hom` squares; Candidate D1 must migrate
and revalidate those diagnostics because their equivalence type changes, but
does not become a second semantic owner. `TypeEquiv` algebra separately owns
identity, symmetry, and composition of equivalences and `IsEquivMap` evidence.

## `Path_cat` Composition, Collapse Removal, And Symmetry Core Are Probed

The path-category redesign must precede `IsDiscreteCat`, `IsNCat`, `OneCat`,
and any **public** shaped-reflexivity slice that registers with path
composition or symmetry. Shaped owner-position research probes may run earlier,
but promoted rules must not register against an owner that a later phase plans
to replace.

The owner choices are now selected by full-file probes, but remain unpromoted:

1. E0 removes the runtime collapse `Op_cat(Path_cat(A)) -> Path_cat(A)` and the
   old composition fold;
2. E1 represents self-oppositeness by `PathSym_A`, whose arrow action is the
   strict path-symmetry owner; fixed-map equivalence packaging follows only
   when Candidate D supplies the selected package;
3. promote the selected shared-`comp_fapp0` composition candidate using its
   full-file evidence;
4. make `Path_cat` satisfy the active `Cat` contract: both units compute at
   runtime and associativity is available through the generic typed proof-time
   equation, without installing a second path-specific associativity owner;
5. test generic associativity and both unit diamonds at arbitrary paths;
6. retain `Core_incl_func` and `path_to_hom` under generic functorial ownership
   and promote their opposite square propositionally before any stronger
   functor-level packaging.

Do not add a second specialized `Core_incl_func` composition owner merely to
hide a failure in `Path_cat` itself.

The full-file audit now selects a concrete composition candidate. Remove the
active fold:

```text
comp_fapp0(Path_cat(A),q,p) -> eq_trans(p,q)
```

and let the generic `comp_fapp0(Path_cat(A),q,p)` term remain the shared
category-level path-composition normal form. Add only the two narrow
projection-order bridges needed after `id(Path_cat(A),x)` reduces to
`eq_refl(x)`. The generic category unit rules then supply both runtime units,
and the existing generic `comp_fapp0` unification equation supplies typed
proof-time associativity.

This does not erase the oriented computational reading. On `Path_cat`, the
existing `hom_postcomp_fapp0` and `hom_precomp_along_fapp0` heads remain the
covariant and contravariant runtime cut/action owners. They inherit their own
accumulation and `id`-headed unit behavior and compare directly at proof time.
If the `Path_cat` identity projection has already exposed `eq_refl`, the
append-only oriented-owner probe shows that each action head needs its own two
narrow projection-order unit bridges. Those four bridges work but still have
one local overlap with postcomposition accumulation plus inferred-slot
advisories, so they require an owner-position cleanup/classification separate
from the already-passing two category-composition bridges. Thus the ownership
is layered:

```text
comp_fapp0(Path_cat)                 shared category composition;
hom_postcomp_fapp0(Path_cat)         oriented postcomposition runtime action;
hom_precomp_along_fapp0(Path_cat)    oriented precomposition runtime action;
eq_trans                             J-derived propositional reference.
```

The J-derived agreement can be defined by path induction and is judgmentally
reflexive in its base case. It is not a runtime fold between the heads. A
full-file attempt to choose `hom_postcomp_fapp0` itself as the result of
`comp_fapp0(Path_cat)` passed both units and typed pre/post agreement but made
associativity consumers time out. That orientation is therefore rejected until
the interaction with global associativity is redesigned.

The full-file collapse-removal audit shows that E0 can delete
`Op_cat(Path_cat(A))->Path_cat(A)` immediately: the complete migrated suite
still passes and the warning inventory falls to 1,072. E0 therefore does not
need to preserve a false definitional identification while E1 is developed.

E1's selected owner contract is:

```text
PathSym_A : Functor(Op_cat(Path_cat(A)), Path_cat(A))

PathSym_A[x] -> x

path_sym(p : x = y)
  := fapp1_fapp0(PathSym_A,p) : y = x

path_sym(eq_refl(x)) -> eq_refl(x).
```

The source arrow `p : x = y` is read as an arrow `y -> x` in the opposite
path category. `path_sym` is a readable transparent view; the rigid runtime
owner is the capped arrow action of `PathSym_A`. Consequently the existing
generic functoriality cut, rather than a new path-specific composition rule,
supplies the exact anti-composition computation. For `p : x = y` and
`q : y = z`:

```text
comp_Path(path_sym(p),path_sym(q))
  -> path_sym(comp_Path(q,p)),
```

or, with all ordered slots visible:

```text
comp_fapp0(Path_cat(A),z,y,x,path_sym(p),path_sym(q))
  -> path_sym(comp_fapp0(Path_cat(A),x,y,z,q,p)).
```

Only the narrow arrow-action/reflexivity bridge is specialized. The generic
`fapp*` owner still supplies identity and composition for the functor; no
second anti-composition calculus is introduced.

The initial coherence boundary is deliberately propositional:

```text
path_sym_agrees_eq_sym(p) : path_sym(p) = eq_sym(p)
path_sym_invol(p)         : path_sym(path_sym(p)) = p.
```

Both are J-derived and reflexive at `eq_refl`. Open `path_sym(p)` and
`eq_sym(p)` are not convertible, and open double symmetry has no runtime
cancellation rule. At functor level the two composites

```text
PathSym_A o Op_func(PathSym_A) : Path_cat(A) -> Path_cat(A)
Op_func(PathSym_A) o PathSym_A : Op_cat(Path_cat(A)) -> Op_cat(Path_cat(A))
```

are required to compare propositionally/naturally with the corresponding
identity functors; they are not selected as broad runtime cancellations. The
pointwise involution theorem is the current computationally checked basis for
that later packaging.

The exact initial `Core_incl_func` interaction is the square

```text
Core_incl_func(Op_cat(C)) o PathSym_(Obj(C))
  ~ Op_func(Core_incl_func(C)),
```

whose arrow component for `p : x = y` is

```text
path_to_hom_(Op_cat(C))(path_sym(p))
  = path_to_hom_C(p).
```

The pointwise arrow equation is J-derived and passes in the E1 probe. The `~`
begins as propositional/natural comparison rather than definitional equality;
full functor-path packaging waits for the selected Pi/funext surface. Likewise,
`OmegaEquivAlong(PathSym_A)` is packaged only after Candidate D supplies the
fixed-map owner. This later packaging blocks `OneCat`/discreteness consumers,
but it is not required merely to promote the symmetry operation used by a
public shaped-reflexivity registry.

The E1 full-file source and migrated suite pass warning-enabled with 1,084
unjoinable-pair reports and zero unreviewed strict-LHS candidates. Twelve
reports mention `PathSym_A`: the reflexivity bridge meets oriented hom-action
and naturality cuts, while the object projection meets generic DefIso/Product
projection consumers. They are a measured classification/both-order gate for
promotion, not evidence of a second semantic owner. Later evidence may justify
redesigning public `eq_trans`/`eq_sym`, but neither strict/J-derived comparison
is definitional in this candidate.

## Product Reflexivity Policy

Product constructor provenance should be preserved until observational
reflexivity has one canonical structured normal form.

The initial candidate migration is to remove reflexive-collapse rules of the
form:

```text
omega_equiv_product(refl,refl) -> omega_equiv_refl
iso_evidence_product(refl,refl) -> iso_evidence_refl.
```

The Product constructors and decoders can then reduce componentwise without a
competing generic evidence head. This candidate requires an owner-position
probe and warning comparison; the report does not promote the deletion.

## Computational Policy

“As computational as feasible” means:

- ordinary finite data constructors and named data projections have beta rules
  when those rules preserve the selected semantic redexes; abstract or
  operational evidence may instead expose stable observations whose heads are
  intentionally retained by downstream computation;
- truncation-level recursion computes on level constructors;
- carrier projections from `Prop`/`Set`/`n`-groupoid and `n`-category packages
  compute;
- structural equality observations compute at supported type-former heads;
- a promoted shaped-reflexivity former has exactly one selected shaped head and
  registers with generic literal-reflexivity consumers;
- fixed-map evidence takes the already-named map as an index, and its optional
  Sigma package projects back to that map by constructor/projection beta;
- indexed structures such as `Adjunction(F,G)` use their map indices directly;
  left/right compatibility views are absent or transparent, while unit/counit
  remain stable runtime observations owned by the adjunction witness;
- runtime unit/counit projection betas to arbitrary preselected raw operations
  are not installed when they would erase the observations selected by generic
  triangle computation;
- a semantically justified `unif_rule` may be a selected trusted proof-time
  equation, but it never substitutes for required conversion or projection
  computation; in particular, it does not make a triangle written only with
  raw named unit/counit terms compute, and typed `eq_refl` alone does not
  validate its semantic justification;
- transport through univalence computes through the selected equivalence map;
- proof fields remain propositions/evidence rather than arbitrary runtime
  erasure rules;
- equivalences that do not select a canonical runtime normal form remain
  propositional or proof-time;
- truncation reflectors do not pretend to compute until their higher-inductive
  eliminators exist.

Computational ambition does not justify broad collapse rules, duplicate
semantic owners, or hidden proof-irrelevance axioms.

The claim is deliberately local. Emdash may be more computational than
axiomatic Book HoTT at selected boundaries such as classifier decoding,
constructor/eliminator beta, structural path projections, shaped reflexivity,
Pi/function-extensionality beta, univalence transport beta, fixed-map
projections, and categorical cut elimination. It does not follow that every
mathematical equivalence should be judgmental, or that these reductions imply
global normalization, canonicity, or a comparison theorem with a cubical or
observational metatheory.

### Local-first comparative-reference policy

For every external proposal considered by this redesign, record three distinct
things:

1. the adequacy problem or computation it demonstrates;
2. the external mechanism used to solve that problem; and
3. the Emdash owner actually selected after a local probe.

Only (1) is automatically inherited as a comparison test. Neither the syntax
nor the implementation mechanism in (2) becomes a requirement. A proposed
Emdash formulation should first ask whether the existing Došen cut owners,
iterated hom architecture, stable projections, Lambdapi rewrites, and narrow
proof-time `unif_rule`s already expose a smaller solution. External machinery
is imported only when a concrete local prerequisite remains and the imported
idea has been recast with explicit runtime/proof-time ownership.

Accordingly, references to glue, bisimulation, cubical composition, fibrancy,
or observational code generation in this report mean “known comparative
route,” not “implementation specification.” Success is measured by the local
adequacy matrix, owner-position probes, computation, and global-coherence
diagnostics rather than fidelity to another system.

## Foundational Adequacy And Minimal HoTT/Omega Validation Matrix

This matrix is a test of the architecture, not a claim that every row is
already active and not a demand that the first small slice implement every
row. It **is** an MVP architecture gate: every usual minimal HoTT notion and
its immediate category/omega analogue must be expressible through the selected
owners or carry a precise prerequisite/deferred boundary. Every row must carry
one of four statuses in the implementation ledger:

```text
active       present in emdash3_2.lp with diagnostics;
probed       mechanically feasible in an owner-position/full-file-copy probe;
prerequisite missing infrastructure or owner-position evidence required before the consumer;
deferred     deliberately beyond the selected milestone, with the boundary stated.
```

An append-only experiment after `require open emdash.emdash3_2` may be recorded
as **feasibility demonstrated**, but that phrase is not a fifth status. Until
the candidate is placed at its intended owner and later declarations are
checked, its matrix row remains `prerequisite`. This distinction is especially
important for equality rules and `unif_rule`s because declaration order can
hide interactions from a late extension.

The plan distinguishes four content tiers and three milestone names:

| Tier | Required content |
| --- | --- |
| H0 — decoded dependent type-theory core | The ambient `Grpd_grpd` classifier/decoding and selected closure policy; Unit, Empty, Bool or binary sum, Nat, Pi, Sigma, and one named dependent record; their introductions, eliminators, and beta laws; equality, reflexivity, generic `J`, transport, `ap`, and `apd`. |
| H1 — univalent HoTT core | `PiHapply`/`PiFunext` packaged as an equivalence; Sigma/record path-characterization round trips; identity/symmetry/composition for `TypeEquiv` and the corresponding `IsEquivMap` facts; `idtoequiv`, `ua`, both round trips, selected transport beta, and low truncation properties. |
| H2 — higher-constructor completion/readiness | Propositional and set truncation reflectors with restricted elimination. A Circle or another representative higher constructor is optional for the first foundational HoTT MVP and becomes a gate only when broader HIT readiness is claimed. |
| Omega0 — immediate directed extension | `Catd`, categorical Pi/Sigma, functors/transfors, fixed-map omega-equivalence, category univalence, path/core coherence, and at least one computation that remains iterable at the next hom level. |

An **architecture MVP** accounts honestly for every row and may retain named
prerequisites or deferrals. A **foundational implementation skeleton** requires
H0 active with durable diagnostics and states the precise active/probed split
for H1 and Omega0; append-only feasibility evidence never counts as
implementation. A **foundational HoTT MVP** requires H0 and H1 active plus an
integrated Omega0 witness. If H2 remains deferred, the result is described as
a univalent MLTT/HoTT core without HIT completion, not as full HoTT.

If an introductory construction cannot be expressed without a brittle global
rewrite, that is evidence that the infrastructure needs redesign. It is not a
reason to declare the construction out of scope.

### Minimal type/groupoid-side benchmark

The first adequacy pass should inventory and exercise:

- the ambient `Grpd_grpd` classifier/decoding boundary and the selected
  universe-closure policy, followed by classifiers and decoding for unit,
  empty, booleans or binary sums, natural numbers, dependent products,
  dependent sums, and at least one named dependent record;
- for every elementary former, introductions, its intended dependent
  eliminator, and constructor beta laws; absent classifiers remain explicit
  prerequisites rather than opaque inhabitants, while observational identity,
  no-confusion, and higher action receive separate statuses rather than being
  inferred from formation;
- equality formation, `eq_refl`, `ind_eqr`/`ind_eq` (`J`), transport,
  `eq_ap`, `eq_apd`, `PathOver`, symmetry, and composition;
- contractibility, fibres, `IsEquivMap`, `TypeEquiv`, selected inverse data,
  identity/symmetry/composition, and the explicit bridge from any selected
  quasi-inverse presentation to the active contractible-fibre definition;
- function/Pi extensionality in the selected observational reading, including
  the standard diagonal `PiHapply`/`PiFunext` equivalence without discarding
  related-input action;
- Sigma and record path characterizations with both arbitrary round trips,
  propositionally when no judgmental orientation is selected, and their
  reflexive computation laws;
- groupoid-universe univalence, `idtoequiv_grpd`, the selected reverse decoder,
  transport/action beta, and named round trips;
- `IsTruncGrpd`, `PropU_grpd`, `SetU_grpd`, `GroupoidU_grpd`, the closure and
  invariance ledger, and the correct truncation level of packaged universes;
- observational identity of one nondependent and one dependent record,
  including conservative observations and the immediate shaped
  reflexivity/`J` fast track;
- conversion-level negative controls showing that an open path is not
  definitionally collapsed to reflexivity, equality reflection has not been
  introduced accidentally, and proof/evidence fields are not globally erased;
- explicit status for higher-inductive truncation reflectors. Their absence
  prevents a claim of full HoTT completeness but does not prevent a useful
  foundational skeleton.

The benchmark distinguishes `J` on literal reflexivity, reflexive shaped `J`,
and elimination/action on an arbitrary structured path. A passing result must
not report the first or second as if it had implemented the third.

### Standard Pi and structural-path compatibility surface

The richer `PiPathView` remains the identity classifier for functions. Its
ordinary HoTT-facing diagonal interface should have the following shape:

```text
PiHapply(p) : Π x, f(x) = g(x)

PiFunext(h) : f = g

PiFunext(h) x0 x1 q
  ↪ ind_eqr ... (h x1) ... q

PiHapply(PiFunext(h)) x
  ↪ h x

pi_funext_eta(p) : PiFunext(PiHapply(p)) = p.
```

The first composite and related-input application are intended runtime
computations. The reverse composite is propositional for arbitrary `p`. The
append-only stable-head probe obtains its reflexive base through a narrow
two-rigid-head proof-time equation and then derives arbitrary eta by generic
`ind_eqr`. Under the selected hybrid architecture, this is a valid ordinary-J
proof **conditional on that selected base equation**, even though the Pi
equality classifier is structured. The equation is mathematically plausible
as a generic structural coherence law and may itself be part of Emdash's
proof-time definitional architecture; typed `eq_refl` only tests its use. It is
a credible candidate, not yet the selected permanent owner. Promotion requires
an owner-position warning/reduction-order audit, explicit trust/semantic
justification, and a check that any later shaped reflexivity registration joins
it. A future fibrancy-derived computational J may be compared with this
theorem, but is not its dependency.

Beta and propositional eta supply quasi-inverse data but do not by themselves
inhabit the active contractible-fibre `IsEquivMap`. H1 therefore requires a
durable `IsEquivMap(PiHapply)` proof, or a reviewed generic theorem converting
the selected quasi-inverse presentation to contractible fibres, and a
`TypeEquiv` package with executable projections.

For Sigma and the first dependent record, the corresponding compatibility
surface includes:

```text
decode(encode(p)) = p
encode(decode(w)) = w
```

for arbitrary `p` and path-view value `w`, plus the reflexive beta laws. These
are adequacy obligations even when the migration keeps a dedicated path-view
classifier as its rollback boundary.

### Immediate category and omega-category benchmark

For each relevant type/groupoid notion, the plan should exercise the immediate
directed analogue already suggested by the iterated-hom architecture:

- `Cat`, `Obj`, `Hom`, identities, composition, opposites, `Path_cat`, and
  `Core_cat`/`Core_incl_func`;
- functors, object/arrow action, identity/composition laws, transfors, and
  naturality through the global generic owners;
- fixed-arrow omega-equivalence evidence and its first-class Sigma package,
  including usable declaration of a concrete named equivalence;
- indexed `Adjunction(F,G)`, its unit/counit and triangle computation, and an
  optional existential package only when the functors are not already known;
  the benchmark must distinguish canonical stable-observation computation
  from proof-time agreement with preselected named unit/counit terms;
- `idtoequiv_cat`, the selected category decoder, path-to-arrow coherence, and
  the ordinary-isomorphism comparison only at the appropriate dimension;
- shared path-category composition, oriented pre/post actions, and genuine
  opposite/symmetry coherence;
- `IsObjTruncCat`, `IsDiscreteCat`, recursive `IsNCat`, and packaged `OneCat`;
- the corresponding structure one hom level higher: an object-level example
  is repeated for a hom-category or transfor hom-action so that a capped point
  rule cannot accidentally erase the data needed by omega iteration.

The prose inventory is tracked by the following status-bearing correspondence
table rather than by assuming that every groupoidal notion is literally a
directed construction:

| Type/groupoid notion | Category/omega counterpart | Kind of correspondence | Initial status and iteration boundary |
| --- | --- | --- | --- |
| identity/path | `Path_cat`, `Core_cat`, `Core_incl_func` | groupoidal lift into directed structure | active first draft; E0 composition/collapse removal and E1 symmetry core are owner-position probed, while warning classification, promotion, functor-level natural packaging, and later fixed-map equivalence packaging remain prerequisites |
| functions and dependent families | functors, `Catd`, displayed functors/transfors | genuinely directed analogue | active generic owners; retain base-arrow and transfor hom-action |
| dependent Pi/Sigma | `Pi_cat`, `Sigma_cat` and their displayed action | genuinely directed analogue | broad infrastructure active; redesigned equality/univalence next-hom witness is a prerequisite |
| homotopies | transfors and displayed transfors | genuinely directed analogue | active through generic `tapp*` owners; record the first rung that remains iterable |
| `TypeEquiv` | `OmegaEquivAlong(F)` and Sigma-packaged `OmegaEquiv` | directed equivalence analogue | active first-draft observations; append-only migration feasibility demonstrated, owner-position evidence prerequisite |
| groupoid univalence | `CatUnivalence`, decoder, and `path_to_hom` coherence | directed univalence analogue | active operational capability; decoder/action coherence remains a prerequisite |
| homotopy truncation | `IsObjTruncCat`, `IsDiscreteCat`, recursive `IsNCat` | dimension/discreteness criterion, not a hom identification | prerequisite statuses with differing append-only evidence as recorded below |
| Empty/sums/Nat | initial objects, coproducts, natural-number objects | separate categorical universal properties | not implied by decoded inductives; prerequisite/deferred until separately selected |

This is not a demand to encode every HoTT construction as a directed category.
It tests the obvious structural correspondences: identity groupoids versus
path categories, maps versus functors, homotopies versus transfors,
equivalences versus omega-equivalences, and truncation versus eventual
discreteness of iterated homs.

In particular, an identity path is not an arbitrary directed hom.
`Path_cat` and `Core_incl_func` mediate the groupoidal-to-directed comparison;
the adequacy matrix must not collapse that distinction. One next-hom witness
is enough for the first skeleton, but each correspondence row must say whether
the action remains iterable or currently stops at objects.

### Architecture, foundational implementation, and end-to-end gates

The architecture MVP passes when every matrix row has an honest owner,
prerequisite, or deferral and no selected interface blocks its later
implementation. That claim alone does not say that the introductory kernel is
implemented.

A foundational implementation skeleton requires H0 active with durable
formation, elimination, beta, and identity diagnostics. It also states the
exact active/owner-position-probed boundary for H1 and Omega0. Missing
Empty/Bool/Nat decoding can remain a prerequisite for the architecture MVP but
not for this implementation-skeleton claim. A foundational HoTT MVP further
requires H1 active and at least one integrated Omega0 witness that composes the
layers rather than merely forming them independently.

The preferred Omega0 test has the following shape:

```text
F : Functor(A,B)
u : OmegaEquivAlong(F)
e : OmegaEquiv_{Cat}(A,B) := (F,u)
p : A = B                := omega_equiv_path(e)

omega_equiv_to(e) ≡ F
path_to_hom(p) = F
transport/action along p computes through F at the selected boundary.
```

The witness repeats one selected Pi/Sigma or equivalence/univalence action in a
hom-category. An adjunction-only computation is insufficient because
adjunction is not part of the minimal HoTT kernel.

Indexed adjunction has its own category-migration acceptance witness. It
declares named `F : R ⊢ L`, `G : L ⊢ R`, and `J : Adjunction(F,G)`, exercises a
triangle or mate in the canonical stable unit/counit spelling without
recovering `F`/`G` through equality proofs, and validates proof-time agreement
with one preselected unit/counit pair without claiming that the raw spelling
computes. Passing this witness is required for the indexed-adjunction migration
but does not repair a missing H0 or H1 row.

Arbitrary structured-path `J`, truncation reflectors, or later closure theorems
may remain named prerequisites/deferred boundaries for the first skeleton. H2
may remain deferred if the milestone is explicitly called a univalent
MLTT/HoTT core without HIT completion.

### Initial 2026-07-14 status snapshot

This initial inventory prevents the general benchmark from obscuring what is
already known. `Active` here means that symbols exist and current diagnostics
pass; it does not upgrade a documented first-draft coherence boundary.
“Feasibility demonstrated” in the evidence column describes a successful
append-only import probe and does not change the row's formal status.

| Benchmark row | Status | Current evidence or prerequisite |
| --- | --- | --- |
| Ambient `Grpd_grpd` classifier and decoding | active | `Obj(Grpd_cat)` decodes to the ambient `Grpd` classifier; constructor closure is tracked separately. |
| `Unit_grpd`, `Pi_grpd`, Sigma, and decoding | active | Present in `emdash3_2.lp`; Sigma/Pi equality is already partly observational. |
| Native `nat` and generated `ind_nat` at ambient `TYPE` | active | The native inductive and its eliminator are active, but this is not a decoded groupoid-level Nat classifier. |
| `Nat_grpd` and a reviewed groupoid-level eliminator facade | prerequisite; default Candidate G | Feasibility demonstrated with decoding and zero/successor beta in `oetu_hott_elementary_formers.lp`; owner-position placement and active diagnostics remain. |
| Empty and Bool decoded classifiers and eliminators | prerequisite; default Candidate G | Feasibility demonstrated with dependent elimination and constructor beta in the append-only elementary probe; these are required H0 smoke tests rather than optional consumers. A general binary sum is a separately statused extension. |
| Observational identity/no-confusion/higher action for elementary inductives | prerequisite | Not established by the formation/eliminator probe; select per-former identity owners and negative controls separately. |
| Equality, literal `eq_refl`, generic `J`, transport, `ap`, `apd`, `PathOver` | active | Present, but the equality architecture is hybrid and not the final global owner. |
| Standard `PiHapply`/`PiFunext` compatibility | prerequisite | Runtime diagonal beta and related-input action pass append-only. A trusted reflexive proof-time equation fires under typed `eq_refl`, and generic J derives propositional eta conditional on it; owner-position ownership and semantic trust selection remain open. |
| `IsEquivMap(PiHapply)` and Pi `TypeEquiv` package | prerequisite | The beta/eta skeleton gives quasi-inverse data but has not been converted to the active contractible-fibre equivalence definition. |
| Arbitrary Sigma/record path-characterization round trips | prerequisite | Current diagnostics cover projections and reflexive encode/decode cases, not both arbitrary round trips. |
| Record identity classifier and reflexivity observers | prerequisite | Nondependent and dependent conservative skeletons pass in an append-only import probe; intended placement and later-consumer audit remain. |
| Stable shaped record reflexivity and reflexive shaped `J` | prerequisite | The nondependent stable-head skeleton and simulated consumer registrations pass append-only with no local warning; a true owner-position/full-file-copy probe remains. |
| Dependent/nested shaped reflexivity, structural action, and additional computational dependent `J` | prerequisite | Immediate probe tracks, but public promotion follows path-owner selection; retained generic J remains active, while action and fibrancy must not be inferred from the nondependent reflexive probe. |
| Contractibility, fibres, `IsEquivMap`, `TypeEquiv` | active | Contractible-fibre presentation and selected map/inverse observations are active. |
| `TypeEquiv`/`IsEquivMap` identity, symmetry, and composition compatibility | prerequisite | Reflexive evidence and selected constructor closure are active; `OETU-TYPE-EQUIV-ALGEBRA` owns the missing ordinary algebra and contractible-fibre closure proofs, not univalence round trips. |
| Groupoid univalence and operational reverse decoder | active | First-draft capabilities exist; `OETU-GRPD-UNIV-DECODER` owns decoder agreement and action coherence independently of the categorical migration. |
| Both groupoid-univalence round trips and selected action coherence | prerequisite | `OETU-GRPD-UNIV-DECODER` exclusively owns named `idtoequiv(ua(e))`, `ua(idtoequiv(p))`, `coe(ua(e),a)`, and one nontrivial Pi or Sigma action diagnostic. |
| Direct observational equality of the groupoid/category universes | deferred beyond immediate MVP; eventual explicit track | H1 uses the encoder/decoder/action interface. `OETU-UNIVERSE-EQUALITY` later chooses a direct equality rule or identity view, shaped reflexivity/action/J, and the unstratified boundary. |
| Truncation properties and low-level aliases | prerequisite | `TruncLevel`/`IsTruncGrpd` skeleton has append-only feasibility evidence; intended placement and active promotion remain. |
| Packaged `PropU_grpd`/`SetU_grpd`/`GroupoidU_grpd` | prerequisite | Carrier/evidence record skeleton has append-only feasibility evidence; property paths, closure, universe-level truncation, and owner-position audit remain open. |
| Truncation reflectors | deferred | Require the higher-constructor/restricted-elimination architecture. |
| `Cat`, functors, transfors, iterated hom actions | active | Broad generic infrastructure exists and remains the owner of ordinary functoriality/naturality. |
| `Path_cat` E0 category composition and collapse removal | probed | Shared-`comp_fapp0` plus two unit bridges passes both runtime units, generic typed associativity, J-derived agreement, the migrated full check suite, and warning-enabled checking; deleting the self-opposite collapse also passes and lowers the inventory to 1,072. Promotion and durable active checks remain. |
| `Path_cat` E1 opposite/symmetry core | probed | The owner-position `PathSym_A` functor/action, strict reflexivity and generic anti-composition, propositional `eq_sym` agreement/involution, pointwise Core-opposite square, negative controls, full migrated suite, warnings, and strict LHS audit pass. Classify twelve new warning blocks before promotion; functor-level natural and fixed-map equivalence packages remain prerequisites. |
| Global ordinary-iso univalence compatibility | active legacy, frozen for new design | Current `cat_iso_univalence(C)` checks remain during migration, but new general-category architecture uses `CatUnivalence`; the replacement is OneCat-scoped. |
| First-class `OmegaEquiv` observations | active | Recursive observation/reflexivity interface exists; unrestricted introduction/corecursion is absent. |
| Primary fixed-map `OmegaEquivAlong(F)` plus Sigma package | prerequisite | The transitional bridge, opaque evidence/Sigma package, and exact fixed-arrow inverse/higher-cell telescope have append-only feasibility evidence. D0's independent recursive owner, minimal package, reflexivity, and one next-hom computation remain unprobed at owner position; D1's op/Product generators, public decoder migration, integrated witness, and full audit follow only after D0. Property-valuedness remains separate. |
| Categorical decoder finalization and round trips | prerequisite | `omega_equiv_path` is the reserved owner, but `OETU-CAT-UNIV-DECODER` finalizes its types, round trips, `path_to_hom` squares, and Product cases jointly with D1's fixed-map public migration rather than against the old normal form. |
| Indexed `Adjunction(F,G)` | prerequisite | Indexed formation, both exact triangle rules, direct `F`/`G` conversion, proof-time named-unit/counit equation mechanics, and the negative runtime-erasure control pass append-only. Because the scratch named constants are independent, declaration backing/trust classification plus active opposite/mate migration and owner-position warning/LHS audits remain. |
| `IsObjTruncCat` | prerequisite | Formation is mechanically small once `IsTruncGrpd` exists, but current evidence is append-only. |
| `IsDiscreteCat` | selected contract; implementation prerequisite | Exact set-object/fixed-core-map Product formation and the hom-action target pass append-only. It still needs repaired `Path_cat`, promoted fixed-map omega-equivalence, the derived homwise equivalence and inverse/round-trip diagnostics, and owner-position evidence. |
| Recursive `IsNCat` | prerequisite | Recursion skeleton passes append-only with an opaque stand-in for the discrete base; its base contract is now exact, but the real `IsDiscreteCat` implementation and an integrated homwise consumer remain. |
| `IsNCat(n,C) -> IsObjTruncCat(n,C)` | prerequisite | Needs categorical univalence, fixed-arrow evidence truncation, and the recursive dimension proof. |
| Packaged `OneCat` and scoped ordinary-iso univalence | prerequisite | Depends on the real discrete base, evidence paths, and the omega/ordinary comparison. |
| One-next-hom end-to-end adequacy example | prerequisite | Generic machinery exists, but the redesigned equality/truncation/univalence stack has not yet passed this integrated test. |

### Per-former computational checklist

Every former admitted to the adequacy matrix is evaluated in the following
columns:

| Column | Required question |
| --- | --- |
| formation/decoding | Does the classifier decode to the intended Lambdapi carrier? |
| introduction | Is there a constructor, indexed evidence term, or stable introduction owner with the right endpoints? |
| observations/elimination | Do named projections and the intended eliminator beta rules compute? |
| equality classifier | Is endpoint equality direct, encoded, or still opaque, and is that status honest? |
| path characterization | Do encode/decode or `happly`/`funext` maps have both required arbitrary round trips, with judgmental versus propositional status explicit? |
| reflexivity | Do conservative observations and any selected shaped head have one joining normal form? |
| action/transport | Can registered open and dependent terms act on the supported paths, or is this a recorded prerequisite? |
| fibrancy/computational shaped J | Beyond retained generic propositional J, which motives and structured constructors admit additional runtime elimination, and do those betas follow from a sound capability? |
| equivalence/univalence | Are the standard identity/symmetry/composition operations, closure, decoder round trips, and selected action beta present at the relevant universe/dimension? |
| omega iteration | Does the construction retain the owner needed at the next hom level? |
| negative controls | Do open paths/evidence remain non-collapsed at conversion level, without mistaking an `assertnot` for a metatheoretic non-derivability proof? |
| diagnostics/performance | Do typed assertions, both reduction orders, warnings, and bounded checks remain credible? |

The architecture MVP may leave cells marked `prerequisite` or `deferred`; it
fails if it silently claims those cells, chooses an interface that makes them
implausible, or cannot state the missing work precisely. A foundational
implementation skeleton may not use that permission for H0: its declared H0
surface must be active with diagnostics, and its H1/Omega0 split must be stated
explicitly.

## Proposed Implementation Phases

The phase numbers express dependency and migration order for promoted code;
they are not a prohibition on parallel design probes. Shaped reflexivity,
action/fibrancy, fixed-map equivalence, and indexed-adjunction probes remain
available immediately while the low-risk record/truncation slices are being
refined. Public shaped rules that register with composition/symmetry follow the
path-owner phase.

### Phase 0: Documentation And Freeze

1. The review/evidence pass and implementation-handoff packaging are complete;
   formal adoption as the replacement plan remains a separate recorded step.
2. Mark the June 23 univalence report as the active historical implementation
   ledger and this report as its proposed successor architecture.
3. Add no unrelated direct equality, Product decoder, or global
   `CatIsoUnivalence` computation during the redesign. Focused equality rules
   explicitly belonging to the shaped fast track are allowed after their
   promotion probe; this freeze is not a veto on that track.
4. Freeze `cat_iso_univalence` and its decoder-oriented companion as legacy
   compatibility: retain existing source/checks until a bounded migration, but
   add no new arbitrary-`Cat` consumer and use `CatUnivalence`/`OmegaEquiv` in
   all successor architecture immediately.
5. Apply the local-first reference policy: external designs define comparison
   tests or candidate ingredients, never an obligation to reproduce their
   implementation.
6. Apply the proof-time trust policy immediately: add no unclassified
   `unif_rule`, use typed `eq_refl` to test firing, and never report that test
   as independent semantic validation.
7. Preserve the passing active baseline.
8. Unless the user selects another bounded task, begin implementation with
   Candidate G / `OETU-ELEMENTARY-HOTT` under the exact exclusions in the
   handoff section. This first slice does not itself adopt the later normal-
   form migrations.

### Phase 1: Finite Record Convention Probe

1. Refine the already-passing small dependent one-constructor record in a
   temporary owner-position probe.
2. Validate the generated eliminator, named projections, dependent projection
   types, and constructor beta rules.
3. Compare its source/readability and warning behavior with a nested-Sigma
   encoding.
4. Record the final convention in the SOP or a dedicated decision section.
5. Do not yet generate observational record equality globally.

This phase is independently feasible and informs all later packaged
universes.

### Phase 2: Truncation Properties

1. Promote or refine the passing `TruncLevel` and readable-level probe.
2. Promote or refine the passing recursive `IsTruncGrpd` equations.
3. Add `IsPropGrpd`, `IsSetGrpd`, and `IsGroupoidGrpd` views.
4. Add focused formation and reduction checks.
5. Open the closure/invariance ledger without pretending that all entries are
   required for the property-kernel slice.
6. Do not add truncation reflectors.

After the default elementary-H0 slice, this is the leading
truncation-specific mathematical promotion candidate.

### Phase 3: Packaged Truncated Universes

1. Add the one-constructor `TruncGrpdU(n)` record/classifier.
2. Add computing carrier/evidence projections.
3. Add `PropU_grpd`, `SetU_grpd`, and `GroupoidU_grpd` aliases.
4. Derive or explicitly defer property-valuedness of truncation evidence.
5. Do not claim univalence of these subuniverses before proof-field paths are
   controlled.
6. State the expected `(n+1)` truncation level of the universe separately from
   the `n`-truncation evidence carried by its elements.

### Phase 4: Path-Algebra Ownership And `Path_cat` Repair

**E0 shared composition and collapse removal:**

1. Promote/refine the full-file-tested category-level composition candidate:
   remove the `comp_fapp0(Path_cat)->eq_trans` fold, retain the shared generic
   `comp_fapp0` head, and add the two narrow `eq_refl` unit bridges.
2. Preserve `hom_postcomp_fapp0` and `hom_precomp_along_fapp0` as distinct
   oriented runtime action owners with their existing proof-time comparisons;
   owner-position probe and minimize/classify the four oriented `eq_refl` unit
   bridges demonstrated append-only. Do not fold category composition into
   either action head while the measured associativity timeout remains.
3. State and check the J-derived propositional comparison with `eq_trans`.
4. Remove definitional self-oppositeness in the same candidate. Reuse the
   passing removal-only full source/suite evidence and keep a durable negative
   control against reintroducing the collapse.
5. Add both runtime-unit diamonds and typed generic associativity diagnostics;
   revalidate `Core_incl_func`, `path_to_hom`, transport/`ap`, `DefIso`,
   opposite, and Product consumers.

**E1 symmetry-functor core:**

6. Promote/refine `PathSym_A : Path(A)^op -> Path(A)` at the functor owner.
   Keep `path_sym` a transparent arrow-action view, its object action identity,
   and the one narrow `eq_refl` arrow-action bridge.
7. Let generic functoriality own the ordered anti-composition computation; do
   not add a standalone `path_sym(comp)` rewrite. Retain explicit identity-
   first/action-first and composition/action-first diagnostics.
8. Promote J-derived propositional `path_sym = eq_sym` agreement and
   involution, with negative controls showing that neither open comparison is
   a runtime conversion.
9. Promote the pointwise `Core_incl_func(Op C) o PathSym` versus
   `Op_func(Core_incl_func C)` arrow square. Defer functor-level natural/path
   packaging until the Pi/funext owner is stable.
10. Classify the twelve full-file warning reports mentioning `PathSym_A`, add
    both-order tests for their oriented hom-action, DefIso, Product-projection,
    and naturality families, and retain the clean strict-LHS result.
11. Package `PathSym_A` as `OmegaEquivAlong(PathSym_A)` only after Candidate D
    supplies the fixed-map owner. Do not bridge it through the obsolete opaque
    `OmegaEquiv` normal form merely to close Phase 4.

This phase controls the composition and symmetry owners used by later public
shaped-reflexivity registration. E0 and the E1 core may promote independently
of later fixed-map equivalence packaging; `OneCat` and discreteness still wait
for that packaging and their other listed prerequisites. This phase does not
prevent earlier isolated shaped research probes.

### Phase 5: Equality MVP And Immediate Shaped Fast Track

This phase has two cooperating lanes. Either may produce the first useful
equality slice; neither lane may misstate what it has implemented.

Conservative lane:

1. retain direct record/Sigma/Pi equality classifiers and projection observers
   where both reduction orders join;
2. keep generic `J` formation at every classifier and its computation on
   literal `eq_refl`;
3. use the lane as a fallback MVP and as a control for warning/performance
   comparisons.

Shaped lane:

1. refine the stable former-specific shaped-reflexivity head demonstrated by
   the 2026-07-14 probe;
2. cover a nondependent record and a genuinely dependent path telescope;
3. register the shaped head with `ind_eqr`, composition, symmetry, transport,
   and every inventoried generic literal-reflexivity consumer at the correct
   owner positions;
4. test Sigma, Pi, a nested former, and both reduction orders;
5. probe a structural action/substitution owner for arbitrary path-record
   values and a distinct fibrancy/dependent-elimination capability; promote
   reflexive shaped `J` independently if it passes before those designs do;
6. write an exact consumer/migration audit before changing an existing public
   former.

Generic propositional uses of `ind_eqr`, including Candidate H eta once its
reflexive coherence basis is selected and justified, remain valid in both
lanes. The fibrancy capability gates only additional structural runtime betas
on arbitrary shaped path constructors.

### Phase 6: Split Univalence Decoder Ownership

The groupoid equivalence type is not changed by Candidate D, whereas the
categorical equivalence type is. Their decoder work therefore has different
implementation schedules even though both layers retain one operational
inverse.

**Phase 6G: groupoid decoder normalization:**

1. Select `grpd_equiv_path` as the reverse decoder owner and connect
   capability-selected `ua_grpd` inverses by named coherence data or restrict
   consumers to the canonical capability.
2. Make this task the exclusive owner of both groupoid-univalence round trips,
   the `coe_grpd` transport/action square, and one nontrivial Pi or Sigma
   universe-action diagnostic.
3. Keep constructor closure propositional until the generic squares are
   stable. Do not use an unclassified arbitrary-capability `unif_rule` as if it
   derived missing coherence; either supply/derive the coherence or record the
   rule explicitly as the trusted coherence postulate.
4. Record that these decoder/action results complete the immediate H1
   groupoid-universe surface but do not implement direct observational
   universe identity.

`OETU-TYPE-EQUIV-ALGEBRA` may supply ordinary equivalence operations consumed
by examples, but it does not own or reimplement these decoder round trips or
transport squares.

**Phase 6C: categorical decoder contract before D1:**

5. Reserve `omega_equiv_path` as the categorical reverse decoder name and
   record its intended orientation, capability-agreement obligation, two round
   trips, and `path_to_hom` squares as the contract owned by
   `OETU-CAT-UNIV-DECODER`.
6. Quarantine legacy global `CatIsoUnivalence` consumers: new general-category
   coherence uses `OmegaEquiv`, while the ordinary-iso decoder exists only
   behind `OneCat` or an explicit dimension hypothesis.
7. Do not finalize the categorical decoder's public types, round trips, or
   constructor rules against the soon-to-be-replaced opaque `OmegaEquiv` normal
   form. Retype and validate them jointly with Candidate D1. D1 owns the
   normal-form migration and reruns the decoder diagnostics; the categorical
   decoder task remains their sole semantic owner.

### Phase 7: Primary Fixed-Map Omega-Equivalence And Sigma Package

**D0 recursive-owner feasibility gate:**

1. Introduce/refine neutral `OmegaEquivAlong_C(f)` as a fresh primary fixed-
   arrow evidence owner at the intended source position; reserve
   `IsOmegaEquivArrow_C(f)` until property-valuedness.
2. Define its minimal first-class Sigma package immediately, because the
   recursive higher-cell observations return packaged omega-equivalences in
   the next hom-category. Install generic map/evidence projection beta before
   dependent observation beta.
3. Add inverse observations, recursive left/right cell observations,
   reflexive fixed-map evidence, and recursive reflexive computation through
   at least one next-hom rung, without routing those bodies through the old
   opaque `OmegaEquiv` owner.
4. Pass source-position subject reduction, later-source checking, warning/LHS
   comparison, both-order diagnostics, and bounded timing. Record the result
   as D0 recursive-owner feasibility only; do not call the public migration
   implementation-feasible before this gate passes.

**D1 public normal-form migration:**

5. Replace the current opaque public `OmegaEquiv_C(x,y)` classifier by the
   promoted Sigma package and route the active public destructors through its
   fixed-map evidence.
6. Migrate opposite and Product generators without duplicating semantic
   bodies. Jointly with `OETU-CAT-UNIV-DECODER`, retype its canonical decoder
   domain/codomain and rerun its owned round trips, `path_to_hom` squares, and
   Product diamonds. This is migration validation, not duplicate decoder
   ownership inside Candidate D1.
7. Validate one concrete named equivalence declaration and the first MVP
   end-to-end next-hom univalence/action witness without a per-instance
   unification rule.
8. Compare the primary evidence propositionally with the old semantic
   `OmegaEquivFibre(F)` during compatibility staging, keeping property-
   valuedness separately statused.
9. Do not promote after D0 or telescope formation alone. Complete the recorded
   owner-position ladder through opposite, Product, decoder, integrated next-
   hom consumers, and the full warning/subject-reduction/performance audit in
   one D1 full-file candidate.

Property-valuedness of the fixed-arrow evidence may remain a named theorem
prerequisite after formation and projection migration; it is required before
evidence fields are erased propositionally in `NCat` paths.

### Phase 8: Indexed `Adjunction(F,G)` Migration

1. Replace the current `Adjunction(R,L)` observation package by the relation
   `Adjunction(F,G)` indexed by already-named functors.
2. Remove the semantic need for `left_adj_func`/`right_adj_func`; retain only
   transparent compatibility views for identified migration consumers.
3. Retype `unit_adj_transf(J)` and `counit_adj_transf(J)` directly over `F` and
   `G`, but retain them as stable opaque runtime observations.
4. Place both append-only-demonstrated triangle cut-elimination rules in an
   owner-position/full-file-copy probe with `F`/`G` as repeated indexed
   parameters and the unit/counit application heads as the rigid semantic
   discriminators.
5. Type opposite adjunction directly as
   `Adjunction(Op_func(G),Op_func(F))`; migrate its unit/counit observations,
   adjunction hom/profunctor comparisons, mates, checks, and reviewer example.
6. For one concrete preselected `myUnit`/`myCounit`, add narrowly typed
   proof-time comparisons to the stable observations only from an explicit
   declaration binding/agreement field or as clearly labelled trusted
   declaration equations. Exercise them with typed `eq_refl`, record that this
   tests firing rather than soundness, and retain `assertnot` conversion
   controls. Do not install ordinary observation-to-raw-operation runtime
   betas.
7. Add `AdjunctionPackage(R,L)` as a Sigma package only if an identified
   consumer needs existential first-class functors.
8. Validate one concrete `J : Adjunction(F,G)`, both canonical-spelling
   triangles, opposite, and a mate computation. Also validate that the raw
   named-operation spelling remains a documented non-computing surface unless
   an elaborator explicitly restores the stable observations.

This is a bounded but nontrivial migration: the lexical audit currently finds
153 `Adjunction`/left/right/unit/counit occurrences across the active source,
diagnostics, and reviewer example. The fresh exact triangle probe establishes
pattern feasibility, but the active owner-position migration, scratch-LHS
cleanup, opposite/mate surface, and performance/warning audits remain open.

### Phase 9: Discreteness, Directed Dimension, And `OneCat`

1. Add `IsObjTruncCat` independently.
2. Using the promoted E1 core and Candidate D fixed-map owner, package the
   exact `PathSym_A` functor as fixed-map omega-equivalence and package the
   functor-level Core/opposite comparison required by the first consumer.
3. Implement the selected exact Product
   `IsSetGrpd(Obj(C)) ×
   OmegaEquivAlong_{Cat_cat}(Core_incl_func(C))` as `IsDiscreteCat(C)`.
4. Derive fixed-map equivalence of
   `core_incl_hom_func(C,x,y)` for arbitrary endpoints, check that its object
   action is `path_to_hom`, and expose an arrow-to-path inverse with both
   round trips. Prefer a generic hom-action theorem for
   `OmegaEquivAlong_{Cat_cat}(F)` over a duplicated discreteness field.
5. Add `CatDim`, recursive `IsNCat`, `NCat(n)`, `ZeroCat`, and `OneCat` only
   after the homwise gate passes.
6. State and prove or stage `IsNCat(n,C) -> IsObjTruncCat(n,C)` with its exact
   univalence/evidence-truncation dependencies.
7. Introduce/derive ordinary `CatIsoUnivalence` only for `OneCat`, prove or
   defer the `OmegaEquiv`/`IsoEvidence` comparison there, migrate the remaining
   compatibility consumers, and retire the unscoped global claim.

### Phase 10: Public Equality, Structural Action, And Fibrancy Migration

1. Migrate one type former at a time from the prototype to public equality.
2. Replace old encode/decode implementations that became identity coercions.
3. Retain compatibility aliases only when they have real consumers.
4. Eliminate the two-reflexivity-normal-form Product boundary.
5. Promote structural action only through the selected registered-map
   architecture.
6. Retain generic propositional `J` throughout. Promote additional runtime
   rules for arbitrary structured-path constructors only through the selected
   fibrancy/dependent-elimination capability; do not identify that computation
   with either action alone, ordinary generic elimination, or the already
   feasible reflexive shaped beta rule.
7. Keep bounded checks and warning comparisons for every owner migration.

This phase must not be combined with a module split or broad code
reorganization.

### Phase 11: Foundational Adequacy And Closure Completion

1. Maintain every row of the H0/H1/H2/Omega0 matrix with an honest formal
   status and distinguish append-only feasibility evidence from owner-position
   probing.
2. Make the selected H0 universe/classifier boundary, Unit, Empty, Bool/sum,
   Nat, Pi, Sigma, record, eliminators, beta laws, and ordinary identity
   operations active with diagnostics before claiming an implementation
   skeleton.
3. Promote the standard Pi compatibility surface, including runtime diagonal
   beta, related-input action, propositional eta, and an active
   `IsEquivMap(PiHapply)`/`TypeEquiv` package. Audit any proof-time reflexive
   bridge at owner position and against shaped-reflexivity registration, and
   record whether it is derived/declaration-backed or a justified selected
   proof-time law. The generic-J eta theorem is conditional on that basis but
   does not wait for computational fibrancy.
4. Add both arbitrary Sigma and dependent-record path-characterization round
   trips with their reflexive computation laws.
5. Complete the `OETU-TYPE-EQUIV-ALGEBRA`-owned `TypeEquiv` and `IsEquivMap`
   identity/symmetry/composition corpus. Separately complete the
   `OETU-GRPD-UNIV-DECODER`-owned groupoid round trips and selected action beta;
   neither task duplicates the other's semantic bodies. Add further
   constructor closure only after the consumers have both prerequisites.
6. Complete the truncation closure/invariance facts needed by active packaged
   universes, including the explicit Pi/function-extensionality dependency of
   evidence property-valuedness.
7. Run at least one record/equality/equivalence or dependent Pi/Sigma example
   through the next hom level and pass the Omega0
   equivalence/univalence/action witness.
8. Pass the indexed-adjunction triangle/mate witness as a separate
   category-migration gate; do not count it as H0/H1 adequacy.

### Phase 12: Truncation Reflectors And Higher Constructors

1. Design propositional and set truncation as higher-inductive structures.
2. Specify their restricted dependent eliminators and beta rules.
3. Generalize to `n`-truncation only after the low levels are computationally
   credible.
4. Integrate truncated higher-inductive structures rather than assuming that
   post-hoc truncation always preserves desired computation.
5. Add a Circle or another representative higher constructor only when the
   milestone claims HIT readiness beyond truncation reflectors; it is not a
   prerequisite for the first univalent MLTT/HoTT core.

### Phase 13: Eventual Computational Universe Identity

This phase is part of the eventual full-observational endpoint, not the H1 MVP
gate. Design probes may begin earlier once their immediate owners are stable.

1. For `Grpd_grpd`, compare direct public equality reduction with a dedicated
   universe identity-view fallback; select only after owner-position
   rewrite/unification and performance evidence.
2. Define shaped universe reflexivity, structural transport/action, and the
   exact boundary between retained generic J and additional structured-J
   computation.
3. Integrate `TypeEquiv`, the selected reverse decoder, both round trips, and
   Product/Pi/Sigma action diamonds without duplicating semantic bodies.
4. Repeat the design question at the categorical universe using the promoted
   fixed-map `OmegaEquivAlong`/Sigma package, while preserving the
   unstratified-policy warning.
5. Test at least one nontrivial universe transport through the next hom level,
   warning behavior, subject reduction, and bounded full-suite performance.
6. Treat external glue/bisimulation/cubical mechanisms as comparison baselines;
   select a native Emdash mechanism from local owners and record why it is
   sufficient.

### Phase 14: Deferred Universe Metatheory

Compare:

- the current unstratified operational specification;
- a stratified type/category universe hierarchy;
- a deliberate impredicative/self-universe model.

This phase owns consistency/model claims. No earlier implementation phase
depends on resolving it.

## Immediately Available Candidate Slices And Design Probes

The following are intentionally bounded enough to begin as the next concrete
task. “Immediately available” means that a promotion or owner-position probe
can start; it does not mean that every candidate is already demonstrated as
implementation-feasible. Candidate D makes this distinction explicit through
its D0 feasibility gate and D1 public migration.

### Candidate A: record convention only

```text
one dependent record probe;
constructor and projection beta;
generated eliminator audit;
no active equality or univalence change.
```

Risk: low.

Feasibility status: the isolated append-only import probe passes; the remaining
work is owner-position/full-file-copy refinement, naming, diagnostics, and
promotion review.

### Candidate B: truncation property kernel

```text
TruncLevel;
IsTruncGrpd recursion;
IsPropGrpd / IsSetGrpd / IsGroupoidGrpd;
formation and reduction checks;
no packaged universes and no reflector.
```

Risk: low to medium, principally interaction with direct Pi equality and
recursive evidence types.

Feasibility status: the recursion passes in the isolated append-only probe; the
separate packaged-universe skeleton also passes but belongs to the follow-up
slice. Active-source placement and closure-ledger boundaries remain to audit.

### Candidate C: shaped record reflexivity and reflexive `J`

```text
one stable former-specific shaped-reflexivity head;
path projection beta rules;
specialized reflexive ind_eqr beta;
registration with generic composition and symmetry;
dependent-record and nested-former extension probe;
no claim yet of arbitrary structured-path action.
```

Risk: medium to high. The nondependent stable-head skeleton passes with
warnings enabled and no local warning after simulating the needed consumer
registrations in the append-only probe. True owner-position placement, the
dependent/nested case, and complete-consumer audits remain promotion gates.

This candidate is immediately available; it is not deferred behind completion
of the conservative observational MVP. It may proceed immediately as an
owner-position probe, but public registration with composition/symmetry follows
Candidate E1 core promotion.

### Candidate D0/D1: primary fixed-map omega-equivalence and Sigma package

**D0 recursive-owner feasibility gate:**

```text
fresh OmegaEquivAlong_D0(f) as a neutral primary evidence/certificate owner;
minimal OmegaEquiv_D0(x,y) := Sigma f, OmegaEquivAlong_D0(f);
generic omega_equiv_to/evidence projection beta;
inverse and self-recursive higher-cell observations using OmegaEquiv_D0;
fixed-map reflexivity and recursive reflexive beta through one next-hom rung;
owner-position full-file checking independent of the old opaque owner;
no public OmegaEquiv migration yet.
```

The minimal Sigma package is deliberately part of D0 rather than D1. Its
higher-cell observations need a first-class omega-equivalence codomain at the
next hom level; postponing the package would introduce a provisional second
recursive representation and fail to test the selected architecture.
Passing D0 would demonstrate the coinductive-style observation interface and
its canonical reflexivity computation; it would not supply unrestricted
corecursion, a productivity checker, or a terminal-coalgebra semantics.

**D1 public normal-form migration:**

```text
replace public OmegaEquiv by the promoted fixed-map Sigma package;
route active destructors through the evidence projection;
opposite and Product generators plus their recursive cells;
idtoequiv_cat/omega_equiv_path declaration migration;
rerun the categorical-decoder-owned round trips, path_to_hom squares, and Product case;
OmegaEquivFibre(F) comparison as compatibility/semantic reference;
one concrete named equivalence and integrated next-hom univalence/action witness;
no unif-only runtime semantics.
```

Risk: medium to high for D0 and high for D1's active normal-form migration.
The append-only fixed-map telescope, transitional bridge, opaque evidence/
Sigma package, computing forward projection, and higher-cell endpoint types
all pass warning-enabled probes without a local unjoinable critical-pair
report. They do not yet implement a new self-recursive owner or reflexive
computation, so D0 has not passed and D1 is not yet demonstrated as
implementation-feasible. After D0 passes, D1 remains “migration proposed”
until Steps 4--7 and the full audit pass with Steps 1--3 in the same public
full-file candidate. Property-valuedness remains a separate theorem and the
`IsOmegaEquivArrow` name is not used as evidence for it.

### Candidate E0/E1: `Path_cat` focused repair

**E0 shared composition and collapse removal:**

```text
promote/refine shared comp_fapp0 category-level composition candidate;
add two narrow eq_refl unit bridges;
retain oriented pre/post runtime action owners and proof-time comparison;
clean/classify their four separately demonstrated eq_refl action-unit bridges;
retain J-derived eq_trans only as a propositional reference;
remove the self-opposite collapse without yet claiming a replacement symmetry.
```

E0 is owner-position probed. The shared-composition source/suite passes with
1,091 rather than the active 1,109 unjoinable-pair reports, and the same
candidate with the collapse removed passes with 1,072. The attempted fold to
the postcomposition head is rejected because associativity consumers time out.
E0 may be promoted as a semantically honest intermediate without waiting for
E1, subject to durable checks and the oriented action-unit cleanup.

**E1 symmetry-functor core:**

```text
PathSym_A : Path(A)^op -> Path(A), with identity object action;
path_sym := its capped arrow action;
one narrow path_sym(eq_refl) -> eq_refl bridge;
generic-functorial anti-composition, with no duplicate specialized law;
J-derived propositional agreement with eq_sym and propositional involution;
pointwise Core_incl_func/opposite square;
no runtime double-symmetry cancellation;
fixed-map OmegaEquivAlong packaging only after Candidate D.
```

E1's core is also owner-position probed: the full source and migrated suite
pass warning-enabled with 1,084 reports, the strict LHS audit has no unreviewed
slot, and open strict/J-derived symmetry and open double symmetry remain
non-convertible as intended. Twelve reports mention the new functor owner and
must receive both-order classification before promotion. The later functor-
level natural comparison and fixed-map equivalence package remain
prerequisites for `OneCat`/discreteness, but they do not force public shaped-
path registration to wait after the E1 core itself is promoted.

Risk: medium for E0; medium to high for E1 promotion/classification and its
later equivalence packaging.

### Candidate F: indexed adjunction migration spike

```text
Adjunction(F,G) indexed relation;
left/right projections removed or transparent only;
stable unit/counit observations typed directly over F/G;
both exact triangle rules with F/G as parameters;
named unit/counit proof-time bridge with typed and assertnot controls;
explicit declaration backing or trusted-instance classification for that bridge;
negative control against runtime observation-to-raw-operation betas;
opposite and mate migration sample;
optional existential AdjunctionPackage only for a named consumer.
```

Risk: medium. The indexed relation, both triangle patterns, direct functor-index
conversion, fixed-operation proof-time bridge, and runtime-erasure negative
control pass focused warning-enabled append-only probes. The active migration
still has a bounded but broad 153-occurrence lexical surface across source, checks, and the
adjunction reviewer example, and the scratch triangle LHSs require inferred-
slot cleanup. An opaque left/right projection plus `unif_rule` is not the
runtime design. Narrow unit/counit unification can be the declaration's trusted
proof-time equation—not merely convenience—but the current independent-
constant probe establishes only its mechanics. The stable observations remain
the runtime computational owners.

### Candidate G: elementary decoded H0 formers

```text
Empty_grpd and dependent empty elimination;
Bool_grpd and dependent Bool elimination;
Nat_grpd facade over native nat/ind_nat;
constructor beta diagnostics;
general binary sum remains a separate follow-up;
explicitly separate observational identity/no-confusion follow-up;
no equality-owner or categorical-universal-property claim.
```

Risk: low to medium. The append-only probe demonstrates formation, decoding,
dependent elimination, and constructor beta. Promotion still requires intended-
owner placement under the active `Prop`/`P` builtins and durable diagnostics;
it must not upgrade those facts to observational identity, canonicity, or an
initial/coproduct/NNO universal property, and it does not claim a general sum
former.

### Candidate H: standard Pi/function-extensionality compatibility

```text
PiHapply as the diagonal observation of PiPathView;
PiFunext with related-input action by ind_eqr;
runtime happly(funext(h)) beta;
propositional funext(happly(p)) eta by generic J conditional on the reflexive basis;
owner-position comparison of the proof-time bridge with shaped-reflexivity registration;
semantic justification or explicit trusted-law selection for the reflexive bridge;
IsEquivMap(PiHapply) and TypeEquiv packaging;
no global eta rewrite.
```

Risk: medium. Both transparent and stable append-only probes pass, including a
typed two-rigid-head reflexive proof-time equation and arbitrary propositional
eta derived from it by generic J. The result is valid in the hybrid
primitive-generic/shaped theory extended by that selected equation and does not
depend on `OETU-OBS-FIBRANCY`; typed `eq_refl` is not an independent proof of
the equation's soundness. Unlike the named-adjunction instance bridge, however,
the transparent probe independently reduces the unfolded reflexive reverse
composite to `eq_refl`; the stable equation is a candidate preservation of that
semantic definition under opaque owners, not an unmotivated postulate.
Promotion may derive/back it more directly or accept it explicitly as a
semantically justified generic proof-time definitional law. It claims
propositional equality, not new runtime elimination of arbitrary structured Pi
paths. The permanent owner and contractible-fibre equivalence proof remain
open, so this candidate is immediately available for an owner-position design
probe but is not yet a formally `probed` matrix row.

Candidate G is the default first implementation slice for a new handoff;
Candidates A and B are the next safest promotion candidates and may be ordered
by their first concrete consumer. Candidates C, D0, E0/E1, F, and H are all
immediately available as design/owner-position probes. Candidate C may become
a narrow public equality slice only after E1 core promotion and its other gates
pass. Candidate D1 begins only after D0 passes and may then migrate before the
directed-dimension layer. E0 may promote before E1; E1 core promotion is the
path-operation prerequisite for public shaped registration, while fixed-map
packaging of `PathSym_A` and Candidate D remain prerequisites for
`IsDiscreteCat` and `OneCat`.
Candidate F is independent of directed dimension but must not be mixed with an
unrelated module split. Candidate H may proceed without discarding the related-
input Pi identity, but H1 cannot pass until its equivalence packaging is
active.

## Explicitly Deferred Work

Shaped `eq_refl`, structural action/substitution, reflexive shaped `J`, and
sound additional computation for arbitrary structured-path `J` are
intentionally **not** blanket entries in this deferred list. They are immediate
tracks layered over retained generic propositional J. A particular attempted
encoding may fail or an unresolved subpart may remain a prerequisite for a
later slice, but earlier reports do not defer the subject itself.

Elementary H0 formers, standard Pi/function extensionality, Sigma/record path
round trips, and ordinary equivalence/univalence compatibility are likewise
immediate prerequisite or implementation tracks, not blanket deferrals.

Direct observational universe identity is not part of the immediate H1 MVP,
but it is also not an unowned omission: Phase 13 and
`OETU-UNIVERSE-EQUALITY` explicitly own the eventual full-observational track.

- a complete normalization or canonicity proof for observational equality;
- a closed inductive-recursive universe of all groupoid/type codes;
- general record-schema metaprogramming before the manual convention is
  validated;
- runtime record eta;
- proof-irrelevance rewrites;
- propositional, set, and general `n`-truncation reflectors;
- a Circle or representative higher constructor beyond truncation unless a
  broader H2/HIT-readiness milestone is selected;
- `NCat_cat(n)` universe univalence;
- complete `OmegaEquiv` corecursion/productivity semantics;
- comparison with complete semi-Segal/Rezk presentations;
- universe stratification, impredicativity, and self-universe models;
- consistency of the global categorical-univalence policy;
- simultaneous source module splitting.

## Required Diagnostics

### Elementary H0 and Pi-compatibility diagnostics

- `Grpd_grpd` and every selected H0 classifier decode to the intended carrier;
- Unit, Empty, Bool/sum, Nat, Pi, Sigma, and the first record expose their
  intended introductions, dependent eliminators, and constructor beta laws;
- native `nat : TYPE` and decoded `Nat_grpd : Grpd` are tested and reported as
  different layers;
- Candidate G checks that the two Bool constructors do not collapse by
  conversion, while stating explicitly that this local `assertnot` is not a
  Boolean-canonicity or normalization theorem;
- elementary formation/elimination diagnostics do not claim observational
  identity, no-confusion, higher action, or canonicity without separate tests;
- `PiHapply(PiFunext(h))` has runtime diagonal beta and `PiFunext(h)` acts at
  arbitrary related inputs through the selected structural/J owner;
- a typed `eq_refl`, not a conversion assertion, exercises whether any
  retained proof-time reflexive Pi equation fires; its trust class and
  semantic justification are recorded separately;
- `PiFunext(PiHapply(p)) = p` is constructed propositionally by generic `J`,
  with its reflexive computation checked conditional on the selected base
  equation; this is a retained-generic-J theorem in that extended theory, not
  a proof of the base equation or a claim of arbitrary structured-path runtime
  elimination;
- `PiHapply` is packaged with active contractible-fibre `IsEquivMap` evidence,
  or a reviewed generic quasi-inverse-to-`IsEquivMap` theorem supplies it;
- owner-first and application/eta-first reductions, warning deltas, and the
  comparison with shaped-reflexivity registration are checked before
  promotion; computational fibrancy remains a separate stronger track.

### Proof-time unification trust diagnostics

- every new `unif_rule` is labelled declaration/field-backed, a generic
  semantically justified selected proof-time law, or an explicit trusted
  postulate;
- a runtime `assertnot` is retained when neither side is intended to be the
  evaluator normal form;
- a typed `eq_refl` exercises the real proof-time consumer and is reported as
  a firing/typechecking regression, never as independent proof of the rule;
- a backing path/field counts only if it does not itself typecheck solely by
  the same rule it is meant to justify;
- generic structural rules need not be duplicated by an internal path when
  their primitive proof-time-definitional status and mathematical argument are
  explicit;
- promoted patterns retain two rigid heads or a stable intermediary, avoid
  reliance on unification-rule transitivity, and pass bounded owner-position
  consumer timing (with focused unification traces when selection is unclear);
- overlapping applicable proof-time equations are exercised in every relevant
  expected-type orientation rather than assumed coherent from one consumer;
  and
- `oetu_unif_trust_boundary_probe.lp` remains an adversarial control showing
  that an arbitrary unjustified equation can pass the typed-`eq_refl` test.

### Record diagnostics

- constructor projection beta for every field;
- dependent later-field projection typing;
- generated eliminator beta;
- no unintended record eta;
- path-record projection order once observational equality is introduced.
- shaped-reflexivity projection order against the raw path constructor;
- specialized reflexive `ind_eqr` beta without changing unsupported formers;
- dependent path-telescope and one nested-former case;
- registrations for every generic consumer that matches literal `eq_refl`;
- for Sigma and the first dependent record, arbitrary
  `decode(encode(p)) = p` and `encode(decode(w)) = w` round trips plus their
  reflexive computation laws.

### Truncation diagnostics

- `IsTruncGrpd(-2,A) = IsContr(A)`;
- successor recursion unfolds exactly one level;
- proposition/set/groupoid aliases select the intended indices;
- carrier projection of each packaged universe;
- no runtime elimination of evidence fields.
- no false claim that `TruncGrpdU(n)` is itself `n`-truncated;
- truncation monotonicity at every promoted low level;
- explicit Pi/function-extensionality dependency for evidence
  proposition-valuedness;
- focused checks for each promoted closure/invariance fact.

### Path-category diagnostics

- `Op_cat(Path_cat(A))` remains a genuine opposite head after E0 rather than
  converting to `Path_cat(A)`; the removal-only full source and suite remain
  passing;
- both identity units at an arbitrary path;
- typed generic proof-time associativity at arbitrary paths, plus bounded
  normalization of each bracketing without a path-specific runtime
  associativity rule;
- both `id`-first and narrow-`eq_refl`-bridge-first unit reductions;
- both units for each oriented post/pre action spelling after the `Path_cat`
  identity has projected to `eq_refl`, with the postcomposition-accumulation
  overlap explicitly classified;
- opposite hom endpoints remain reversed;
- `PathSym_A` fixes objects, and its `path_sym` arrow action maps `eq_refl` to
  `eq_refl` through the one narrow projection-order bridge;
- generic functoriality supplies the ordered anti-composition conversion in
  both action-first and composition-first spellings, without a separate
  specialized anti-composition rewrite;
- shared `comp_fapp0(Path_cat)` agrees propositionally with J-derived
  `eq_trans`, and the oriented pre/post runtime action heads compare by typed
  proof-time equality;
- the rejected `comp_fapp0(Path_cat)->hom_postcomp_fapp0` orientation retains a
  bounded negative associativity control until its global interaction is
  redesigned;
- path symmetry agrees propositionally with J-derived `eq_sym` at the selected
  boundary, while their open conversion remains negative;
- `path_sym(path_sym(p)) = p` is J-derived and reflexive at `eq_refl`, while
  open double symmetry has no runtime cancellation;
- the pointwise arrow square
  `path_to_hom_(Op C)(path_sym(p)) = path_to_hom_C(p)` passes, and its later
  functor-level natural packaging is not reported as definitional equality;
- `Core_incl_func` retains generic functorial ownership;
- the twelve E1 warning blocks mentioning `PathSym_A` are classified with
  explicit both-order tests for oriented hom actions, DefIso, Product
  projections, and naturality before promotion; and
- the strict inferred-LHS audit remains free of unreviewed E0/E1 candidates.

### Discreteness and directed-dimension diagnostics

- `IsDiscreteCat(C)` unfolds to exactly
  `IsSetGrpd(Obj(C)) ×
  OmegaEquivAlong_{Cat_cat}(Core_incl_func(C))`, with computing Product
  projections and no proof-field erasure;
- a negative boundary records that `IsSetGrpd(Obj(C))` alone neither converts
  to nor constructs `IsDiscreteCat(C)`;
- `core_incl_hom_func(C,x,y)` has source `Path_cat(x=y)`, target
  `Hom_cat(C,x,y)`, and object action definitionally equal to the existing
  `path_to_hom_C` owner;
- fixed-map equivalence of `Core_incl_func(C)` yields, through a general
  hom-action theorem or an explicitly reviewed specialized derivation,
  `OmegaEquivAlong_{Cat_cat}(core_incl_hom_func(C,x,y))` at arbitrary
  endpoints;
- the induced `hom_to_path` inverse satisfies both path-to-hom and hom-to-path
  round trips propositionally/omega-coherently, with negative controls against
  broad runtime cancellation;
- `IsNCat(cat_zero,C)` unfolds to the exact selected `IsDiscreteCat(C)`, and
  the successor unfolds exactly one hom level; and
- one packaged `OneCat` consumer exercises the discrete-hom theorem through
  the next hom level rather than merely projecting object-set evidence.

### Univalence diagnostics

The first item is owned by `OETU-TYPE-EQUIV-ALGEBRA`. The groupoid round-trip,
transport, and universe-action items are owned by
`OETU-GRPD-UNIV-DECODER`. The categorical round-trip and `path_to_hom` items
are owned by `OETU-CAT-UNIV-DECODER` and are rerun inside D1 because D1 changes
their input normal form. Constructor/Product tasks may supply test data and
migration diamonds but do not acquire a second decoder implementation.

- identity, symmetry, and composition of `TypeEquiv`, plus the corresponding
  identity/composition behavior of `IsEquivMap`;
- `idtoequiv_grpd(ua_grpd(e)) = e` and
  `ua_grpd(idtoequiv_grpd(p)) = p` propositionally through the selected
  decoder/capability boundary;
- `coe_grpd(ua_grpd(e),a)` computes to `type_equiv_to(e,a)` and agrees with
  `idtoequiv_grpd` action;
- one nontrivial Pi or Sigma universe-action example;
- `path_to_hom` agrees with `idtoiso_cat`/`idtoequiv_cat` forward arrows;
- Product reflexive constructor/decoder diamonds;
- `OneCat` ordinary-iso comparison is not available for arbitrary `Cat`.
- no new diagnostic or implementation consumer uses legacy global
  `cat_iso_univalence`; retained checks are labelled compatibility-only until
  OneCat migration;
- `omega_equiv_to((F,u)) ≡ F` and
  `omega_equiv_evidence((F,u)) ≡ u` by generic Sigma projection;
- during compatibility staging only,
  `omega_equiv_to(omega_equiv_from_along(u)) ≡ F` by runtime computation;
- comparison of `OmegaEquivAlong(F)` with `OmegaEquivFibre(F)` propositionally;
- inverse/map projection betas are declared before dependent higher-cell
  betas and pass subject reduction in that order;
- fixed-arrow left/right higher-cell endpoints typecheck with `f` as an index,
  and no broad raw inverse-composite cancellation rewrite is introduced;
- a concrete named equivalence whose selected map is usable by downstream
  computation;
- reflexive, opposite, and Product fixed-map generators and their decoder
  diamonds pass in the same owner-position full-file candidate;
- one recursive next-hom univalence/action witness uses the new package rather
  than the transitional old-owner bridge;
- no semantic dependency on an unclassified per-instance `unif_rule`; typed
  `eq_refl` is required as an operational test but is not reported as semantic
  validation.

### Eventual universe-identity diagnostics

These diagnostics belong to Phase 13 and are not immediate H1 acceptance
criteria:

- direct universe equality or its selected identity view has one canonical
  owner and a documented rollback boundary;
- shaped universe reflexivity and structural transport/action join decoder
  computation in both orders;
- retained generic J continues to work at an opaque universe variable, while
  every additional structured-J beta is former-registered and capability-
  justified;
- both univalence round trips and Product/Pi/Sigma universe-action diamonds
  pass without copying a second decoder body;
- the categorical universe case uses the promoted fixed-map package and states
  the unstratified `Cat_cat : Cat` boundary explicitly;
- at least one computation remains iterable at the next hom level and passes
  warning, subject-reduction, and bounded timing audits.

### Indexed-structure diagnostics

- `J : Adjunction(F,G)` forms without existential recovery of either functor;
- unit/counit endpoints mention `F` and `G` directly;
- no semantic left/right projection remains; any retained compatibility view
  reduces transparently to its index;
- `unit_adj_transf(J)` and `counit_adj_transf(J)` remain stable runtime heads;
- exact indexed versions of both active triangle rules compute with `F`/`G` as
  repeated parameters, not rewrite-head discriminators;
- an `assertnot` conversion control distinguishes an opaque unification-only
  projection from a runtime-computing view;
- typed `eq_refl` exercises every intentionally retained proof-time
  `unif_rule`, including one concrete preselected named unit/counit pair, while
  the report separately records its declaration backing or trusted-postulate
  status;
- an agreement path offered as backing is checked not to depend solely on the
  same `unif_rule` whose soundness it is meant to support;
- `assertnot` records that those named operations are not runtime-convertible
  to the stable observations and that a raw named-operation triangle is not
  falsely claimed to compute;
- a negative constructor probe confirms that observation-to-raw-operation
  runtime betas are rejected when they erase the triangle discriminator; this
  diagnostic is required even when the warning checker reports no local
  critical pair;
- both normalization orders are exercised for every future declaration facade
  or elaboration rule that exposes a user's unit/counit names;
- both triangles, opposite adjunction, one mate/profunctor comparison, checks,
  and the reviewer example survive the indexed migration;
- a first-class `AdjunctionPackage` is added only with a concrete existential
  consumer and has constructor/projection diagnostics.

### Foundational adequacy diagnostics

- every matrix row has an `active`, `probed`, `prerequisite`, or `deferred`
  status and at least one owning file/symbol or missing-prerequisite entry;
- every milestone names whether it is the architecture MVP, foundational
  implementation skeleton, foundational HoTT MVP, or H2/HIT completion;
- append-only feasibility experiments are never reported as owner-position
  `probed` rows, and the selected H0 surface is active before an implementation
  skeleton is claimed;
- proof-time unification tests distinguish operational firing from semantic
  justification, and no independently declared instance equation is counted
  as foundational coherence merely because typed `eq_refl` succeeds;
- the elementary classifier/eliminator beta corpus, Pi equivalence package,
  Sigma/record arbitrary path round trips, `TypeEquiv` algebra, and the
  applicable decoder-owned univalence round trips pass at the tier that claims
  them;
- equality, transport, equivalence, univalence, and truncation examples compose
  rather than merely typecheck independently;
- literal-reflexivity `J`, reflexive shaped `J`, structural action, and
  additional arbitrary fibrant/dependent structured-path `J` computation are
  tested and reported separately; generic propositional J remains available
  throughout and is not conflated with the last item;
- conversion-level `assertnot` controls ensure that an open path does not
  collapse definitionally to reflexivity, equality reflection is not installed
  accidentally, and evidence fields do not erase globally; comments state that
  these controls do not prove semantic non-derivability of UIP or proof
  irrelevance;
- the fixed-map equivalence/univalence/action witness passes as the integrated
  Omega0 gate;
- the indexed-adjunction triangle/mate witness passes as a distinct category-
  migration gate and is not cited as H0/H1 evidence;
- one selected construction remains iterable through a hom-category/transfor
  action instead of terminating at a pointwise object rule;
- bounded timing and warning deltas are recorded for every promoted equality
  or univalence owner.

## Risk Register

### Direct observational equality remains the highest-risk migration

Adding open-world rules to `=` and structural reflexivity can multiply
critical pairs across every dependent consumer. The isolated prototype and
per-former registry are mandatory. A dedicated identity-view classifier with
encode/decode remains the rollback boundary until a direct public owner passes;
the eventual observational target does not justify removing the only safe
migration fallback prematurely.

### Append-only feasibility can be mistaken for owner-position coherence

An imported scratch extension sees the active declarations that precede it but
cannot expose all interactions that would arise if its owner were inserted
earlier and consumed by later rules. Successful elementary/Pi import probes are
therefore useful design evidence, not formal `probed` status. Promotion must
repeat the candidate at its semantic owner, include later consumers, and
compare warning, subject-reduction, and both-order behavior.

### Shaped reflexivity creates a generic-consumer registration obligation

The stable-head probe is locally successful, but any generic operation whose
rewrite LHS recognizes literal `eq_refl` can otherwise lose its beta rule after
the inner reflexivity rewrites. The registry must be auditable and its bridges
must live at the generic owner's position. An append-only successful assertion
is insufficient evidence. Because Lambdapi declarations are ordered, a former
introduced after an early generic owner cannot simply be referenced in that
owner's earlier rule block. The migration may need forward declaration and
section reordering, a centralized closed registry for initially supported
formers, or a generic-consumer refactor through structural action. This source
ordering change is part of Candidate C's risk, not mere formatting.

### Structural action does not automatically supply dependent `J`

An action head for registered maps does not by itself justify adding new
runtime elimination rules for an arbitrary structured path and arbitrary
dependent motive. Treating the two as one capability would hide the central
fibrancy obligation. This does not invalidate the retained primitive generic
J or the propositional theorems derived from it. The action and additional
computational dependent-elimination interfaces therefore have separate ledger
entries, diagnostics, and promotion claims.

### Native inductive records interact with the current `Prop`/`P` builtins

Lambdapi generates induction principles using the configured proposition
classifier. The active mapping `Prop := Grpd`, `P := τ` is useful but means the
generated motive and existing encoded groupoid universe must be inspected in
every record probe.

### Pi compatibility has both a packaging and a proof-time boundary

Runtime `happly(funext(h))` beta and propositional
`funext(happly(p)) = p` provide quasi-inverse data, but the active public notion
of equivalence is contractible-fibre `IsEquivMap`. Skipping that packaging would
overstate H1. Conversely, turning the successful reflexive proof-time bridge
into a global eta rewrite would erase the intended distinction between runtime
observation and propositional coherence. The owner-position design must test a
narrow two-rigid-head bridge against shaped-reflexivity registration and record
its semantic justification/trusted-law status before selecting it. Generic J
then derives eta conditional on that basis. A later fibrancy-derived
computational rule is a comparison, not a prerequisite for that conditional
generic-J theorem.

### `Path_cat` E0/E1 owners are selected, but neither is promoted

The shared-`comp_fapp0` candidate has stronger evidence than an ordinary
append-only probe and resolves the apparent unit/asymmetry contradiction at the
category-composition layer. Collapse removal and the minimal `PathSym_A` core
now also have owner-position full-file evidence. This removes the earlier
global-selection gap at the plan level: the object/arrow owner, anti-
composition orientation, `eq_sym` boundary, involution status, and Core square
are explicit.

It does not make the repair active. E0 still needs durable checks and oriented
action-unit cleanup. E1 still has twelve new warning blocks to classify and
later needs functor-level natural and fixed-map equivalence packaging when
their consumers arise. The 1,072/1,084 warning counts are diagnostics, not
confluence proofs. Reporting “Candidate E complete” before those gates would
remain an overstatement, but requiring fixed-map packaging before adopting
this staged plan—or before promoting the symmetry operation itself—would invert
the dependency on Candidate D.

### `IsDiscreteCat` is selected, but its homwise adequacy may expose missing infrastructure

Do not weaken discreteness to object-set truncation merely to make `OneCat`
easy to declare. The exact contract is now selected as
`IsSetGrpd(Obj(C)) ×
OmegaEquivAlong_{Cat_cat}(Core_incl_func(C))`, integrated with the recursive
Sigma-packaged `OmegaEquiv` rather than an opaque generic category-equivalence
property.

That selection does not yet prove that the current/proposed certificate API
can computationally expose full faithfulness. Promotion requires a derivation
that every `core_incl_hom_func(C,x,y)` is a fixed-map omega-equivalence and a
checked inverse/round-trip surface for `path_to_hom`. If the general
`OmegaEquivAlong` hom-action theorem cannot be implemented without brittle
choice or coherence machinery, record that concrete blocker and reconsider
the evidence boundary; do not silently add a redundant third field or call
object truncation “discrete.”

### Migrating `OmegaEquiv` changes a public normal form

The primary-evidence/Sigma-package architecture is mechanically simple, but
the active `OmegaEquiv` classifier is opaque and already owns reflexive,
opposite, Product, and univalence observations. Replacing it is a kernel
normal-form migration. The forward/evidence projection benefit does not waive
the constructor, decoder, subject-reduction, downstream, and warning audits.
Current probes type the telescope and package but do not implement that
recursive owner. D0 isolates that missing computation: a fresh fixed-map owner,
its necessary minimal Sigma package, reflexivity, and one recursive next-hom
observation must pass at source position before D1 is described as
implementation-feasible. D1 still bears the public constructor/decoder/
consumer migration risk. The explicit promotion ladder prevents “fixed
endpoints typecheck” from being mistaken for either “the recursive owner
computes” or “global migration is coherent.”

### Immediate decoder univalence can be mistaken for full universe identity

H1 deliberately stops at encoder/decoder round trips and selected action beta.
That is enough for the immediate MVP, but not for the eventual statement that
public universe equality itself computes as equivalence. Conversely, the
later goal does not license importing another system's glue or bisimulation
mechanism without a local owner analysis. Phase 13 owns this boundary.

Decoder normalization is also layer-sensitive. The groupoid decoder and its
H1 round trips can stabilize before Candidate D. The categorical decoder's
name can be reserved early, but finalizing it against the old opaque
`OmegaEquiv` and then treating D1 as a second implementation would invert the
dependency. Its finalization therefore occurs jointly with D1 under
`OETU-CAT-UNIV-DECODER`; `OETU-TYPE-EQUIV-ALGEBRA` remains independent of both
decoder theorem families.

### Indexed adjunction is simpler but has a broad migration surface

`Adjunction(F,G)` removes unnecessary recovery of already-known functors and
has append-only feasibility evidence for both exact triangles. The active
source, diagnostics, and reviewer example contain 153 relevant lexical
occurrences, including opposite adjunctions, triangles, mates, and profunctor
comparisons. Migrate
these as one focused semantic owner change, not piecemeal compatibility
rewrites and not together with a module split. The fresh-rule feasibility
result does not replace an owner-position audit or cleanup of its inferred LHS
slots.

### Named adjunction operations can erase the triangle discriminator

Unlike the left/right functors, the unit/counit observations cannot simply be
made transparent aliases for arbitrary preselected raw operations. The
negative probe demonstrates an inner-first reduction in which constructor
projection betas erase both stable heads before the outer triangle rule is
selected. No local unjoinable critical-pair warning identified the lost
computation. Promotion therefore requires explicit both-order positive and
negative assertions, stable canonical triangle spellings, and no runtime
operation-projection beta unless a different audited semantic owner replaces
the observation-headed triangle rules.

### Proof-time unification is legitimate trusted logical authority

`unif_rule` is part of the intended Emdash toolset, not a feature to ban or
reduce to cosmetic elaboration. A semantically justified rule can be the most
natural proof-time definitional equation, complementing runtime Došen-style
cut elimination without choosing either side as an evaluator normal form.

That advantage creates a precise trust obligation. The adversarial control
shows that an arbitrary two-rigid-head rule can leave the terms
non-convertible while allowing typed `eq_refl` to inhabit their cross-head
equality. Therefore typed `eq_refl` establishes that the rule fires in a real
consumer; it cannot establish the rule's mathematical soundness. The local
manual for the pinned Lambdapi build still labels `unif_rule` experimental and,
more importantly, states that no sanity check is performed. The project may
reasonably regard its narrow, tested rule patterns as operationally stable;
software maturity does not remove the logical trust boundary.

The correction is classification, not blanket ceremony. A promoted rule is
backed by declaration/field data, selected as a generic structurally justified
proof-time definitional law, or labelled an explicit trusted postulate. The
second class need not be duplicated by an internal path whose only purpose is
to restate the primitive equation. In contrast, a per-instance rule between
independently declared names cannot cite a path built by `eq_refl` using that
same rule as independent backing. The current named-adjunction probe therefore
demonstrates mechanics only. Candidate H demonstrates eta conditional on its
generic reflexive law, but its separate transparent probe supplies independent
definition-level reduction evidence for that law. Neither limitation prevents
promotion after the corresponding semantic decision is made.

Fixed-arrow indices, transparent functor views, stable unit/counit runtime
observations, and Sigma projection betas remain the runtime architecture. A
proof-time declaration equation cannot be cited as the reason a raw named-unit
triangle computes.

### Property fields affect universe equality

`TruncGrpdU(n)` and `NCat(n)` are structures with evidence. Their paths reduce
to carrier paths only after property-valuedness is established. Broad
proof-irrelevance is not an acceptable shortcut.

### Negative conversion controls do not prove the metatheory

`assertnot` checks can detect accidental judgmental path collapse, equality
reflection, or proof-field erasure in a concrete spelling. They cannot prove
that UIP or proof irrelevance is uninhabited in the theory, nor can they replace
normalization or model evidence. Diagnostics and reports must state this
boundary explicitly.

### Global `Cat` univalence remains semantically strong

The policy is accepted operationally but may fail in a future model or under a
constructor not closed by univalence. Such failures are architecture evidence,
not reasons to add arbitrary closure axioms silently.

The separate legacy global `cat_iso_univalence` assumption is additionally
frozen. If new general-category work uses it before `OneCat`, the redesign
would reintroduce the dimension collapse it is meant to remove. Existing
compatibility declarations may survive the bounded migration, but they are not
successor-architecture dependencies. Since both active capabilities compare
their evidence type with the same object equality, treating both as permanent
global principles would also induce an unrestricted comparison between
`IsoEvidence` and recursive `OmegaEquiv`; the OneCat boundary is what makes
that comparison dimension-correct.

## Side-Task Ledger

| ID | Status | Depends on | Resume trigger | Next action |
| --- | --- | --- | --- | --- |
| `OETU-RECORD-CONVENTION` | proposed early slice; append-only skeleton demonstrated | current inductive/Sigma infrastructure | first concrete slice selected | Refine the passing dependent one-constructor record at owner position, including projections, generated eliminator, parameter syntax, and inferred-slot audit; compare with nested Sigma. |
| `OETU-RECORD-GENERATOR` | deferred/optional | `OETU-RECORD-CONVENTION` | two manual records show repeated stable boilerplate | Specify a deterministic external schema generator; generated code remains reviewable Lambdapi source. |
| `OETU-ELEMENTARY-HOTT` | **default next slice; not started**; append-only feasibility demonstrated | active universe decoding and native inductives | next implementation turn unless the user selects another bounded slice | Promote decoded Empty, Bool, and Nat classifiers/eliminators with beta and Bool non-collapse diagnostics at their active owners; keep sums, observational identity/no-confusion/higher action, canonicity, and categorical universal properties as separately statused work. |
| `OETU-PI-FUNEXT` | immediate owner-position design track; append-only beta and conditional-eta skeleton demonstrated | active `PiPathView`, retained generic `ind_eqr`, contractible-fibre `IsEquivMap` | H1 or truncation-evidence property-valuedness is consumed | Select `PiHapply`/`PiFunext` owners, preserve related-input action, audit and semantically classify the reflexive proof-time equation against shaped registration, derive generic-J propositional eta conditional on it, and package `PiHapply` as an active equivalence; do not add a fibrancy dependency for that theorem. |
| `OETU-STRUCTURAL-PATH-COMPAT` | proposed H1 compatibility slice | active Sigma paths, `OETU-RECORD-CONVENTION`, `OETU-PI-FUNEXT` where path-valued functions require it | H1 path characterization is claimed | Add arbitrary Sigma and dependent-record encode/decode round trips, reflexive betas, and one nested path-telescope case without forcing global runtime eta. |
| `OETU-TYPE-EQUIV-ALGEBRA` | proposed H1 compatibility slice | active `IsEquivMap`/`TypeEquiv`, `OETU-PI-FUNEXT` where function extensionality is required by contractible-fibre proofs | foundational HoTT MVP or an ordinary equivalence operation is selected | Add identity, symmetry, and composition of `TypeEquiv` plus the corresponding `IsEquivMap` closure proofs. Do not own univalence decoders, round trips, transport squares, or universe-action examples. |
| `OETU-TRUNC-LEVEL` | proposed early slice; append-only skeleton demonstrated | existing `IsContr`, `Pi_grpd`, equality | truncation slice selected | Promote/refine `TruncLevel`, recursive `IsTruncGrpd`, and named low-level aliases with owner-position diagnostics. |
| `OETU-TRUNC-CLOSURE` | proposed staged ledger | `OETU-TRUNC-LEVEL`, equality/equivalence | a closure fact receives a concrete consumer | Prove one fact at a time: equality lowering, monotonicity, equivalence invariance, Pi/Sigma bounds, and package-universe truncation. |
| `OETU-TRUNC-EVIDENCE-PROP` | deferred proof | `OETU-TRUNC-LEVEL`, `OETU-PI-FUNEXT`, stable observational paths | packaged-universe equality is consumed | Derive `IsPropGrpd(IsTruncGrpd(n,A))`; do not postulate global proof irrelevance. Add ambient univalence before claiming the `(n+1)` universe theorem. |
| `OETU-TRUNC-UNIVERSE` | proposed follow-up; append-only skeleton demonstrated | `OETU-RECORD-CONVENTION`, `OETU-TRUNC-LEVEL` | low-level predicates pass | Add `TruncGrpdU`, low-level aliases, carrier/evidence projections, and an explicit no-false-universe-truncation diagnostic at owner position. |
| `OETU-TRUNC-REFLECTOR` | deferred | observational equality and HIT elimination | a theorem needs `||A||_n`, not merely `IsTruncGrpd(n,A)` | Design propositional truncation first with restricted dependent elimination. |
| `OETU-PATH-CAT-COMP` | E0 owner-position probed; not promoted | generic `comp_fapp0`, oriented hom actions, current J-derived path algebra | path composition promotion or E1 begins | Promote/refine shared `comp_fapp0` with two category-unit bridges, durable unit/associativity/J-agreement checks, oriented action-unit cleanup, and removal of the self-opposite collapse. Reuse the passing 1,072-report source/suite candidate. |
| `OETU-PATH-CAT-SYM` | E1 core owner-position probed; not promoted; later fixed-map package pending | `OETU-PATH-CAT-COMP`, generic functoriality, current J-derived `eq_sym`; equivalence packaging also depends on `OETU-OMEGA-EQUIV-ALONG` | public shaped symmetry registration, `OneCat`, or observational category equality begins | Classify the twelve `PathSym_A` warning blocks, promote the functor/action/reflexivity and propositional `eq_sym`/involution/Core-square core with durable both-order checks, then add functor-level natural and fixed-map equivalence packaging only when their owners are available. |
| `OETU-OMEGA-EQUIV-ALONG` | D0 not yet owner-position probed; D1 proposed normal-form migration; append-only evidence/package and endpoint expressibility demonstrated | recursive `OmegaEquiv`, Sigma/record convention; D1 coordinates with the `OETU-CAT-UNIV-DECODER` contract | fixed-functor equivalence or discreteness is consumed | First pass D0 with a fresh source-position fixed-map owner, minimal Sigma package, reflexivity, and one recursive next-hom observation independent of the old owner. Then complete D1's op/Product, public destructor/decoder declaration migration, named declaration, integrated witness, fibre comparison, and full audits; rerun but do not duplicate the categorical-decoder-owned round trips and squares. |
| `OETU-ADJUNCTION-INDEXED` | proposed focused migration; append-only indices, triangles, and named-operation proof-time mechanics demonstrated | current adjunction triangles/opposite/mates | indexed-structure slice selected | Replace `Adjunction(R,L)` by `Adjunction(F,G)` at owner position; remove/transparentize left/right views, retain stable unit/counit observations, bind any named operations through declaration data or classified trusted equations, and migrate the 153-occurrence source/check/example surface with the runtime-erasure negative control. |
| `OETU-STRUCTURE-DECLARATION` | proposed usability protocol; one append-only adjunction operation-bridge mechanism demonstrated | primary fixed-map evidence; indexed adjunction; `OETU-UNIF-TRUST` policy | a second concrete named structure instance is needed | Validate direct `u : OmegaEquivAlong(F)` and `J : Adjunction(F,G)` declarations; connect preselected unit/counit names by declaration-backed or explicitly trusted proof-time equations while canonical computations retain stable observations; treat typed `eq_refl` as a firing test and consider an elaborator/generator afterward. |
| `OETU-UNIF-TRUST` | proof-time trust policy selected; adversarial negative control passes | Lambdapi `unif_rule` and current runtime/proof-time SOP | every new or migrated proof-time equation | Maintain the three-class trust ledger (declaration/field-backed, generic semantically justified definitional law, explicit postulate), typed firing checks, runtime negative controls where intended, and the adversarial control; never count a same-rule `eq_refl` path as independent backing. |
| `OETU-DISCRETE-CAT` | exact contract selected; append-only formation/hom-target probe passes; implementation blocked by explicit prerequisites | `OETU-TRUNC-LEVEL`, `OETU-PATH-CAT-SYM`, `OETU-OMEGA-EQUIV-ALONG`; homwise adequacy consumes the promoted fixed-map hom-action theorem | directed dimension slice begins | Implement `IsSetGrpd(Obj(C)) × OmegaEquivAlong_{Cat_cat}(Core_incl_func(C))`; derive fixed-map equivalence of every `core_incl_hom_func`, expose `hom_to_path` with both round trips, and run a next-hom consumer. Do not substitute object truncation alone or duplicate homwise evidence without a recorded failed derivation. |
| `OETU-NCAT` | proposed architecture, implementation deferred | `OETU-DISCRETE-CAT`, `OETU-TRUNC-LEVEL`, record convention | `IsDiscreteCat` is stable | Add `CatDim`, recursive `IsNCat`, and packaged `NCat`. |
| `OETU-NCAT-OBJ-TRUNC` | theorem prerequisite | `OETU-NCAT`, categorical univalence, fixed-arrow evidence truncation | `OneCat` object truncation or iso comparison is consumed | Prove/stage `IsNCat(n,C) -> IsObjTruncCat(n,C)`; state explicitly that the converse fails. |
| `OETU-ONECAT-ISO` | proposed replacement; global legacy interface frozen now | `OETU-NCAT`, global omega-level Cat univalence | `OneCat` exists; meanwhile any new global-iso consumer is found | Add no new arbitrary-`Cat` use; scope/derive `CatIsoUnivalence` for `OneCat`, migrate compatibility consumers, and retire the unscoped claim. |
| `OETU-OBS-MVP` | proposed conservative lane; append-only skeleton demonstrated | record convention and current equality views | a low-risk equality former is selected | Refine the direct classifier, literal-reflexivity observers, and generic `J` control case at owner position without claiming arbitrary structured action. |
| `OETU-OBS-SHAPED-REFL` | immediate probe candidate; append-only nondependent skeleton demonstrated | `OETU-OBS-MVP` classifier shape, consumer inventory; public promotion also depends on the promoted `OETU-PATH-CAT-SYM` core | shaped lane selected | Extend the stable shaped head to a dependent record and nested former; register every generic literal-reflexivity consumer at owner position after E1 core promotion. Fixed-map packaging of `PathSym_A` is not an extra shaped-registration dependency. |
| `OETU-OBS-ACTION` | immediate design/probe track | path telescopes, `PathOver`, shaped registry | a registered open term must act on a structured path | Select/probe `ObsAction`/`ObsDAction` or `ObsSubst`; account for open terms, dependent fields, composites, and next-dimensional data. |
| `OETU-OBS-FIBRANCY` | immediate design/probe track for additional computation | `OETU-OBS-ACTION`, dependent motives, registered formers | a runtime beta on an arbitrary structured constructor is consumed | Specify which classifiers/motives carry fibrancy and derive sound additional dependent-elimination computation; retained generic propositional J does not depend on this capability, and action alone does not supply it. |
| `OETU-OBS-SHAPED-J` | split status: reflexive candidate immediate; additional arbitrary-constructor computation depends on fibrancy | `OETU-OBS-SHAPED-REFL`; for extra arbitrary-constructor betas `OETU-OBS-FIBRANCY` | shaped equality slice selected | Promote specialized reflexive `ind_eqr` when it passes; retain generic J; derive additional structured-constructor runtime rules only from a sound dependent-elimination architecture. |
| `OETU-OBS-MIGRATE` | deferred high-risk public migration | successful shaped/MVP probe and consumer audit | one former has canonical joins | Migrate public equality one former at a time; do not combine with reorganization. |
| `OETU-FOUNDATIONAL-ADEQUACY` | active tiered architecture/implementation gate | all relevant rows above | every slice refinement and milestone | Maintain H0/H1/H2/Omega0 status/owner/computation cells; require active H0 for an implementation skeleton, active H1 plus an integrated fixed-map univalence/action witness for a foundational HoTT MVP, and keep indexed adjunction as a separate migration witness. |
| `OETU-GRPD-UNIV-DECODER` | proposed early H1 coherence repair | current groupoid equality, `TypeEquiv` projections, and groupoid-univalence capabilities | groupoid round trips, truncated-universe paths, or constructor univalence are consumed | Select `grpd_equiv_path`, add named capability agreement, both groupoid round trips, the `coe_grpd` transport/action square, and one Pi/Sigma universe-action example. This task exclusively owns those results; it may consume but does not duplicate `TypeEquiv` algebra. |
| `OETU-CAT-UNIV-DECODER` | contract selected early; implementation finalization jointly scheduled with D1 | current Cat-univalence interface for contract selection; D0 before finalization, D1 co-execution, and promoted `OETU-PATH-CAT-SYM` for final `path_to_hom` coherence | D1 begins or a categorical round trip is consumed | Reserve `omega_equiv_path` now; during D1 retype it over the fixed-map Sigma package and validate both categorical round trips, capability agreement, `path_to_hom` squares, and Product decoder cases. D1 supplies the normal-form migration and reruns these diagnostics but does not duplicate their semantic ownership. |
| `OETU-UNIVERSE-EQUALITY` | eventual full-observational track; not an immediate H1 MVP gate | `OETU-GRPD-UNIV-DECODER`, stable hybrid equality/action owners; categorical case also depends on `OETU-CAT-UNIV-DECODER` and promoted fixed-map omega-equivalence | direct public universe identity or full-observational completion is selected | Compare direct equality with an identity-view fallback; design shaped reflexivity/action/additional J; integrate the decoder-owned round trips and Product/Pi/Sigma diamonds without copying their bodies; use external mechanisms only as comparison baselines. |
| `OETU-PRODUCT-DIAMOND` | proposed focused cleanup | stable equality/reflexivity policy | Product decoder migration begins | Probe preserving Product evidence provenance by removing reflexive collapse. |
| `OETU-CAT-GLOBAL` | accepted omega-level operational policy; legacy ordinary-iso policy quarantined | none | any report/kernel text suggests non-univalent `Cat` semantics or new arbitrary-`Cat` iso univalence | Keep every `C : Cat` omega-univalent and label the policy axiomatic/unstratified; freeze global `cat_iso_univalence` for migration to `OneCat`. |
| `OETU-CAT-SELF` | deferred metatheory | `OETU-CAT-GLOBAL` | model or universe computation is claimed | Compare stratified, impredicative, and operational self-universe readings. |
| `OETU-METATHEORY` | deferred research | mature observational kernel | consistency/canonicity claim is needed | Develop normalization/model evidence; Lambdapi typechecking alone is not sufficient. |

## Acceptance Criteria For Refining This Proposal

Before this report becomes the active replacement plan:

1. agree on kernel names for `TruncLevel`, `IsTruncGrpd`, truncated universes,
   `CatDim`, and `IsNCat`;
2. approve the exact `IsDiscreteCat(C) := IsSetGrpd(Obj(C)) ×
   OmegaEquivAlong_{Cat_cat}(Core_incl_func(C))` boundary and require, before
   its active promotion, the homwise fixed-map equivalence whose object action
   is `path_to_hom`, an arrow-to-path inverse, both round trips, and one
   recursive `IsNCat` consumer;
3. agree that the one-constructor inductive record convention is the default
   for finite named structures;
4. approve neutral primary `OmegaEquivAlong(F)` evidence plus the Sigma-
   packaged `OmegaEquiv` boundary, the transitional-only role of the old
   semantic fibre/bridge, the D0 recursive-owner/Sigma/refl/next-hom gate before
   D1's public migration, the remaining explicit promotion ladder, and the
   reservation of `IsOmegaEquivArrow(F)` until property-valuedness;
5. approve the indexed `Adjunction(F,G)` replacement, absent/transparent
   left/right compatibility policy, stable unit/counit runtime observations,
   and optional existential `AdjunctionPackage` boundary;
6. approve `unif_rule` as a legitimate selected proof-time definitional
   mechanism, together with the three-class trust policy and the rule that
   typed `eq_refl` tests firing rather than semantic soundness; for
   declaration-generated unit/counit equations, require declaration backing
   or explicit trusted-postulate status, and retain the fact that raw
   preselected spellings do not inherit generic triangle computation and
   runtime projection betas are rejected by default;
7. approve E0's full-file-tested layered `Path_cat` composition owner and
   collapse removal—shared generic `comp_fapp0`, oriented pre/post action
   heads, two `eq_refl` unit bridges, propositional `eq_trans` agreement, and
   no definitional self-opposite collapse—and E1's selected `PathSym_A`
   functor-action contract, generic anti-composition, propositional `eq_sym`
   agreement/involution, and Core square. Formal adoption of this staged plan
   does not require E0/E1 to be active first; actual public shaped promotion
   waits for E1 core promotion, while fixed-map equivalence packaging waits for
   Candidate D and blocks only its downstream consumers;
8. use Candidate G / `OETU-ELEMENTARY-HOTT` as the default first
   implementation slice unless the user explicitly selects another bounded
   candidate; shaped, fixed-map D0, path, indexed-adjunction, and Pi-
   compatibility probes may still proceed immediately while respecting their
   public-promotion dependencies, while fixed-map D1 waits for D0;
9. approve the hybrid equality contract: generic primitive
   `=`/`eq_refl`/`ind_eqr` at unknown and shaped classifiers, a stable shaped-
   reflexivity registry, structural action, and a distinct fibrancy boundary
   only for additional arbitrary-constructor J computation;
10. approve the H0/H1/H2/Omega0 tier content and the distinction between an
    architecture MVP, foundational implementation skeleton, foundational HoTT
    MVP, and optional H2/HIT completion;
11. select the permanent `PiHapply`/`PiFunext` runtime/proof-time owner,
    justify or explicitly trust its reflexive proof-time coherence basis, and
    select the route from the resulting quasi-inverse laws to active
    contractible-fibre `IsEquivMap` evidence;
12. approve the executable foundational corpus: elementary classifier/
    eliminator beta, arbitrary Sigma/record path round trips, ordinary
    equivalence algebra, decoder-owned groupoid-univalence round trips and
    selected action beta, and conversion-level negative controls with their
    metatheoretic limitation;
13. maintain the fixed-map Omega0 equivalence/univalence/action witness and the
    indexed-adjunction triangle/mate witness as separate acceptance gates;
14. approve the immediate-MVP boundary: groupoid decoder round trips and action
    beta are H1; categorical decoder finalization is jointly scheduled with
    D1 for Omega0; direct computational universe identity is owned by the later
    `OETU-UNIVERSE-EQUALITY` track;
15. approve the local-first comparative-reference policy and require every
    adopted external idea to name its local rewrite/unification owner;
16. freeze global ordinary-iso univalence for new arbitrary-`Cat` work and use
    only omega-level `CatUnivalence` until the OneCat-scoped replacement;
17. add a migration statement to the June 23 plan when this proposal is
    formally adopted.

## Long-Term Completion Criteria

The redesign program is complete only when:

```text
the selected H0 ambient universe boundary, Unit, Empty, Bool/sum, Nat, Pi,
Sigma, record, eliminators, beta laws, and ordinary identity operations are
active with diagnostics;
PiHapply/PiFunext preserve related-input observational action, satisfy runtime
beta and propositional eta from a semantically justified/explicitly selected
reflexive proof-time basis, and package PiHapply as an active equivalence;
Sigma and the first dependent record have both arbitrary path-characterization
round trips and reflexive computation laws;
TypeEquiv/IsEquivMap identity, symmetry, and composition and both groupoid-
univalence round trips form an executable standard compatibility surface;
truncation properties and packaged Prop/Set/n-groupoid universes are active;
their closure, evidence-path, and universe-level truncation claims are explicit;
Path_cat uses the shared generic composition head with runtime units, generic
typed associativity, oriented pre/post action owners, propositional eq_trans
agreement, no self-opposite collapse, and a genuine PathSym functor whose
generic arrow action owns anti-composition, whose strict/J-derived symmetry and
involution boundaries are explicit, whose Core-opposite square is coherent,
and whose fixed-map equivalence is packaged when consumed;
OneCat is defined through recursive directed hom dimension whose exact zero
base is the selected set-object/fixed-core-map `IsDiscreteCat`, with homwise
`path_to_hom` adequacy established;
fixed-map omega-equivalence is the primary evidence layer, its property-
valuedness is proved when that claim is consumed, and its Sigma package
supports usable named declarations and categorical univalence;
Adjunction is indexed by its already-named functors, with optional existential
packaging separated from the primary relation, left/right projections absent
or transparent, and unit/counit retained as stable runtime observations;
preselected named unit/counit operations have a declaration-backed or
explicitly trusted proof-time equation, mechanically exercised by typed
`eq_refl`, without erasing the canonical triangle redex or falsely claiming
raw-name runtime conversion;
ordinary IsoEvidence univalence is OneCat-scoped;
public equality computes observationally for records, Sigma, Pi, and eventually
universes, with the latter completion distinguished from the immediate H1 MVP;
structural reflexivity, structural action, and dependent elimination have
explicit canonical owners;
generic propositional J, reflexive shaped J, arbitrary structured-path action,
and additional fibrant/dependent J computation are implemented and
distinguished by diagnostics;
univalence forward/reverse maps have named round trips and action coherence;
Product constructor/reflexivity/decoder reductions join;
the minimal HoTT/omega adequacy matrix has no unacknowledged missing cell, its
architecture/implementation/HIT milestone name is honest, and the fixed-map
univalence/action witness composes end to end with at least one construction
iterating through the next hom level;
the indexed-adjunction witness passes independently as a category-migration
gate rather than substituting for foundational HoTT adequacy;
global Cat univalence remains explicitly axiomatic until a model is supplied;
every promoted unification rule has an explicit trust class and no typed
`eq_refl` firing check is reported as an independent soundness proof;
all promoted slices pass focused probes, make check, relevant examples,
warning classification, catalog checks, health refresh, and make ci.
```

## References And Design Context

- The active code, diagnostics, SOP, Foundations, and canonical syntax remain
  authoritative over this proposal.
- Every external item below is a comparative baseline, source of examples, or
  design prompt—not a specification to reproduce. The selected implementation
  must be restated through local Kosta--Došen/Emdash owners and Lambdapi
  rewrite-versus-unification policy, and may intentionally be simpler or more
  computational than the cited mechanism.
- The recursive `n`-type convention follows the standard HoTT truncation-level
  hierarchy in the [HoTT Book](https://homotopytypetheory.org/book/).
- The distinction between a truncation property and its higher-inductive
  reflector follows the same source.
- The observational target and dedicated identity records are informed by
  Michael Shulman's [Towards an Implementation of Higher Observational Type
  Theory](https://home.sandiego.edu/~shulman/papers/running-hott.pdf) and the
  [Narya documentation](https://narya.readthedocs.io/en/latest/). Narya's
  transport/lifting and glue/bisimulation implementation is one comparison
  route, not the required Emdash universe or J architecture.
- [Cubical Type Theory](https://arxiv.org/abs/1611.02108) provides comparison
  evidence that function extensionality, univalence, and selected higher
  constructors can receive computational treatment; it does not select
  Emdash's rewrite owners.
- [Towards Higher Observational Type
  Theory](https://types22.inria.fr/files/2022/06/TYPES_2022_paper_37.pdf)
  motivates equality computation per type former together with functoriality
  and naturality relative to contexts/substitutions. It is design context, not
  a metatheoretic justification for the current kernel.
- [Computational Higher Type Theory
  I](https://arxiv.org/abs/1604.08873) motivates Boolean canonicity as a strong
  computational compatibility test even with higher-dimensional structure;
  the elementary Emdash probe does not yet establish such a theorem.
- The need to connect identity of structures with a local univalence condition
  is consistent with [A Higher Structure Identity
  Principle](https://arxiv.org/abs/2004.06572).
- Complete semi-Segal/Rezk approaches to univalent `(n,1)`-categories provide
  comparison context, not the project's recursive strict/iterated-hom
  definition; see [Univalent Higher Categories via Complete Semi-Segal
  Types](https://arxiv.org/abs/1707.03693) and [A Type Theory for Synthetic
  Infinity-Categories](https://arxiv.org/abs/1705.07442).
- Lambdapi's generated induction principles and parametrized dependent
  inductives are documented in `docs/lambdapi_docs_commands.rst`; the active
  `τΣ_` implementation is the local reference example.
- Lambdapi's `unif_rule` documentation in the same local manual describes the
  feature as experimental and states that no sanity check is performed. The
  current project may treat its narrow tested patterns as operationally stable,
  but selected rules remain trusted proof-time definitional equations rather
  than runtime normal-form owners, and typed `eq_refl` does not independently
  validate them.
- The 2026-07-14 feasibility findings are supported by the ignored append-only
  probes `tmp/probes/oetu_architecture_feasibility_probe.lp`,
  `tmp/probes/oetu_fixed_map_followup.lp`,
  `tmp/probes/oetu_indexed_structure_architecture_probe.lp`, and
  `tmp/probes/oetu_adjunction_named_unit_runtime_probe.lp`. The complete probe
  set was rerun warning-enabled on 2026-07-14; that complete-run log set ends
  in `20260714-200013`. The Candidate-D-relevant fixed-map and indexed-
  structure probes were additionally spot-rerun warning-enabled; their later
  successful logs end in `20260714-234358`. The final probe is a negative
  computation test whose expected `assertnot` statements pass. The indexed
  probe retains eight and the negative probe two scratch-local replaceable-
  pattern-variable advisories. None of these scratch artifacts is promoted
  kernel source; because all extend an imported active kernel, they preserve
  feasibility evidence but do not confer formal owner-position `probed`
  status. In particular, the later Candidate D reruns do not constitute the
  new D0 recursive-owner probe.
- The selected discreteness boundary is supported by the ignored append-only
  `tmp/probes/oetu_discrete_cat_contract.lp`. Its successful warning-enabled
  log ends in `20260715-114925`; all 1,109 warning blocks are imported from the
  active source, with no new probe-local family. The probe combines the
  truncation and fixed-map feasibility surfaces, checks the exact Product and
  `Cat_cat` indices, checks that the core hom-action object projection is
  `path_to_hom`, and types the required homwise theorem. It deliberately
  supplies no inhabitant of that theorem and therefore does not make
  `IsDiscreteCat` active or owner-position probed.
- The later foundational feasibility review is supported by the ignored
  append-only probes `tmp/probes/oetu_hott_elementary_formers.lp`,
  `tmp/probes/oetu_hott_pi_adequacy.lp`, and
  `tmp/probes/oetu_hott_pi_stable_funext.lp`. Their warning-enabled logs also
  end in `20260714-200013` and pass without probe-local warnings. Because these
  files extend the imported active kernel rather than placing candidates at
  their intended owners, they establish feasibility only and do not confer
  formal `probed` status.
- The proof-time trust-boundary conclusion is supported by the ignored
  adversarial control `tmp/probes/oetu_unif_trust_boundary_probe.lp`; its
  successful warning-enabled log ends in `20260715-124106`. The intentionally
  unjustified two-rigid-head equation remains non-convertible while typed
  `eq_refl` inhabits the induced cross-head equality. This is methodological
  evidence only: the rule is never a promotion candidate and supplies no
  semantic evidence for Candidate F or H.
- The `Path_cat` composition conclusion is supported by the owner-position
  full-file candidate `tmp/probes/oetu_path_shared_comp_owner_full.lp` and the
  migrated entire suite
  `tmp/probes/oetu_path_shared_comp_owner_checks_full.lp`. The original
  warning-enabled migrated-suite log ends in `20260714-234330`; its byte-
  identical later rerun ends in `20260715-000459`, and it contains 1,091
  unjoinable-pair reports versus the active 1,109. The contrasting
  `tmp/probes/oetu_path_oriented_owner_full.lp` unit/bridge consumers pass, but
  its associativity consumers time out. The append-only
  `tmp/probes/oetu_path_oriented_owner_probe.lp` separately records the
  distinct pre/post action-owner interpretation. None is promoted source.
- The E0 collapse-removal conclusion is supported by
  `tmp/probes/oetu_path_symmetry_removal_full.lp` and
  `tmp/probes/oetu_path_symmetry_removal_checks_full.lp`. Their successful
  warning-enabled logs end in `20260715-015457` and `20260715-015535`; the
  source reports 1,072 unjoinable pairs. This pair intentionally supplies no
  replacement symmetry and exists to prove that removal is independently
  feasible.
- The E1 symmetry-core conclusion is supported by
  `tmp/probes/oetu_path_symmetry_owner_full.lp` and
  `tmp/probes/oetu_path_symmetry_owner_checks_full.lp`. Their final successful
  warning-enabled logs end in `20260715-020314` and `20260715-020507`. The
  source reports 1,084 unjoinable pairs, twelve warning blocks mention
  `Path_sym_func`, and `scripts/audit_rule_lhs.py --strict` reports no
  unreviewed slot. The migrated suite exercises strict object/reflexivity and
  anti-composition computation, propositional `eq_sym` agreement and
  involution with negative conversion controls, and the pointwise
  Core/opposite square. It does not yet package functor-level naturality or
  `OmegaEquivAlong(PathSym_A)` and is not promoted source.
