# EMDASH v3.2 Observational Equality, Truncation, And Univalence Redesign Plan

Date: 2026-07-13
Last reviewed: 2026-07-19
Plan-ID: EMDASH-V3-2-OBSERVATIONAL-EQUALITY-TRUNCATION-UNIVALENCE-REDESIGN-2026-07-13
Depends-On: EMDASH-V3-2-GROUPOID-COMPUTATIONAL-UNIVALENCE-2026-06-23; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Supersedes: EMDASH-V3-2-GROUPOID-COMPUTATIONAL-UNIVALENCE-2026-06-23 as the forward implementation master plan; the predecessor remains the historical decision record for its promoted kernel slices
Side-Task-Ledger: #side-task-ledger
Implementation-Handoff: #implementation-handoff-start-here
Current-Implementation-Slice: none selected by this predecessor after completion of the equality-valued overlay and its walking-endomorphism child plan; future work must select an explicit unaffected ledger row or a new bounded plan rather than resume the superseded 2026-07-16 Nat-successor-J handoff
Adopted-Overlay: `REPORT_EMDASH_V3_2_EQUALITY_VALUED_OMEGA_EQUIVALENCE_REREDESIGN_PLAN_2026-07-17.md` is completed at its selected native-EQ1/direct-univalence/groupoidality/structured-J/evidence-property/finite-truncation boundary; its bounded `REPORT_EMDASH_V3_2_WALKING_ENDOMORPHISM_DIRECTED_HIT_PLAN_2026-07-17.md` child is also completed at the theorem-first walking-HIT/`BNat` boundary; retained D0/decoder APIs are compatibility surface, and no primitive nonreducing cast term is selected
Current-Compatibility-Retirement: `REPORT_EMDASH_V3_2_PATH_ACTION_AND_EQUIVALENCE_COMPATIBILITY_RETIREMENT_PLAN_2026-07-19.md` owns forward path-action and legacy-retirement work. Its P4 consumer audit retired the one-layer and dimension-indexed D0 observation families, the uninhabited D0 evidence-property capability and conditional theorem, and their self-only examples. P5 mechanically extracted every remaining D0/D1/unsuffixed decoder owner into frozen `emdash3_2_legacy_compat.lp`; P6 caps it at seven explicit legacy examples and retains the complete two-sided OneCat theorem only because native stable casts lack facade-package/raw-path reification coherence. P7 retains `_EQ1` after finding 11 hard legacy collisions. Historical rows below remain probe provenance, not claims that those symbols are active. The generic `prop_is_trunc_cat_dim` helper remains native proof support
Infinity-Codex-Origin: current-session-analysis-2026-07-13
Infinity-Codex-Decision-Responses: current-session-user-direction-2026-07-13-and-2026-07-14; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f5d7c-3fd0-7932-a38e-48985ba4bda0; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f618e-041a-77d2-ad93-31d04d584fa2; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f61d1-7ce1-7272-8082-bf22c8ba6047; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f625c-22a9-7350-8aea-3f06d4784bec; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f6282-d8ef-79f3-8735-aad1435e0b05; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f6293-83c1-70a0-817b-9128a37151c0; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f62b3-d3c8-7b12-9b33-a10d1d0950fe; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f62e3-db49-7653-8b49-ca98cd9015a7; infinity-codex:019f6392-0363-7e80-8a61-c05a8a667912:019f6396-f48c-75a0-852b-71a827ee0a7f; infinity-codex:019f6392-0363-7e80-8a61-c05a8a667912:019f644e-f14e-70f1-9402-19d688282343; infinity-codex:019f6392-0363-7e80-8a61-c05a8a667912:019f66fe-80db-78b3-b78a-7b13aa48adeb
Status: retained living predecessor and promoted-work ledger, still active only for unaffected H0, truncation, dimension, directed, and former-action tracks. The completed 2026-07-17 equality-valued overlay supersedes this report for equality/equivalence/direct-univalence/groupoidality/structured-J work, its completed walking-endomorphism child discharges the bounded representative-HIT readiness experiment, and the 2026-07-19 path-action/compatibility plan supersedes its forward registry and D0-retirement conclusions. The historical 1,694-check Nat-action snapshot and the retired D0 experiment rows remain provenance, not the current baseline. The full original computational-foundation endpoint remains partial because broader observational action/J coverage, generic directed-HIT and reflector infrastructure, eventual deletion of the frozen compatibility module, and consistency/stratification/normalization/canonicity/semantic-model metatheory remain open; unrestricted native-EQ1 evidence property, unconditional finite-`NCat` object truncation, direct Cat/Grpd EQ1 identity, and one representative directed HIT are no longer blockers.

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
| Foundational HoTT compatibility MVP | H1 is active, including standard Pi/Sigma/record path compatibility and ordinary equivalence/univalence algebra, and one integrated fixed-map Omega0 univalence/action witness passes. This name does not claim metatheoretic soundness or H2/HIT completion. |
| H2/HIT completion | Truncation reflectors and representative higher constructors have their restricted eliminators and computation; this is intentionally later. |

The 2026-07-16 post-OneCat re-audit classifies the architecture MVP,
foundational implementation skeleton, and Foundational HoTT compatibility MVP
as achieved. H0 formation/decoding/elimination/beta/identity diagnostics are
active; the H1 Pi/Sigma/record path and univalence compatibility surface is
active; and the D0/D0b/D1 witness iterates through a next hom level. This is an
executable compatibility milestone, not completion of the wanted endpoint:
H2/HITs, broader former action/fibrancy, certificate extensionality, universe
metatheory, and global normalization/canonicity remain explicit later tracks.

Direct computational universe identity is not an extra hidden gate on the
foundational HoTT MVP. H1 requires the standard `idtoequiv`/decoder round trips
and selected transport/action computation. Making `A = B` itself expose
equivalence/bisimulation data belongs to the later full-observational track.

### Current handoff status and feasibility verdict

This report is now the active forward implementation master plan. The H0/H1
compatibility surface, truncation-property/package universe layer, D0/D0b/D1
fixed-arrow categorical-equivalence layer, indexed adjunction, directed
dimension/packages, registered structural action, conservative visible
constructor lane, finite groupoid/fixed-arrow identity views, direct
categorical-universe classifier, and conditional object-truncation spine are
promoted with synchronized evidence recorded below. The current OneCat lane
has progressed beyond the earlier one-sided checkpoint: strict ordinary
evidence is lifted to recursive omega evidence; arbitrary omega evidence is
decoded back by comparing its two inverse arrows, transporting the right law,
and reconstructing both proof fields; and both round trips now package a
OneCat-indexed specified inverse, contractible-fibre univalence capability,
and named `TypeEquiv`. Its synchronized CI records 109.546s measured checking
time. A post-closeout inventory then retired the three unused global
ordinary-iso capability declarations while retaining the separately consumed
  legacy decoder/Product computation. The next dependency-ready continuation
  registers successor action for recursive Nat equality: the selected map keeps
  the exposed predecessor path, while a stable proof-time basis and generic J
  prove agreement with semantic `eq_ap` without runtime proof collapse. The
  resulting current snapshot has 1,694 classified checks across 62 areas,
  971/157 warning reports, zero/45/27 strict-LHS audit counts, a
  19,988-line/808-symbol/581-rule/58-unification-rule kernel, 1,507 positive
  diagnostics, and 41 measured files. Focused owner/check/reviewer probes,
  `make check`, health, all examples, warning/catalog/audit gates, and
  synchronized CI pass; the Nat reviewer has eleven positive/five negative
  statements and CI records 220.269s measured checking time.
The bounded feasibility verdict is therefore positive
and realized for the H0/H1/Omega0 compatibility MVP. The full original
computational-foundation endpoint remains only partially feasible under the
  current representation: bounded former-by-former action is feasible and now
  covers componentwise Sum plus recursive Nat successor, whereas certificate
  extensionality/unconditional `IsNCat` object truncation, fibrant structured J,
  H2/HITs, and self-universe metatheory retain the explicit blocked/deferred
  statuses below.
Remaining rows retain
the explicit status recorded below; the active code remains authority whenever
a historical baseline description has not yet been rewritten.

| Track | Status at this handoff | Next status-changing result |
| --- | --- | --- |
| Plan review and dependency architecture | adopted as the living forward master plan; every benchmark row is classified and the June 23 plan is retained as a promoted-history decision record | Continue accepting or revising names/boundaries only through bounded owner-position evidence and synchronized ledger updates. |
| H0 elementary core | Candidates G/A/C and `OETU-H0-SUM` active: decoded Empty/Unit/Bool/Nat/general sum plus the named dependent `PathRecord_grpd`, their selected eliminators/projections/betas, PathRecord's shaped observational path/reflexivity/reflexive-J layer, the visible Unit/Boolean/Nat/general-sum equality classifiers with generic reflexivity provenance, the category/endpoint-guarded generic J beta, componentwise Sum action, registered recursive Nat successor action, and negative constructor/record-eta/action controls now join the existing Pi/Sigma/equality core | The conservative visible-constructor lane and the first recursive action are closed through synchronized CI. Preserve proof provenance and keep canonicity/metatheoretic no-confusion, other former actions, and categorical universal properties separate. |
| Truncation properties and universes | Candidate B and Phase 3 are active together with constructive one-step monotonicity, property-valued evidence, arbitrary-level dependent-Pi closure, same-level dependent-Sigma closure, canonical general `TypeEquiv` invariance, its decoder-owned fixed-map categorical object-truncation consumer, carrier/evidence package-path control, restricted package univalence, same-level carrier-`TypeEquiv` truncation, and the expected `(n+1)` package-universe theorem; native levels, recursive `IsTruncGrpd`, low-level views, evidence packages, both directional transports, base/successor computation, path/equivalence reconstruction/round trips, and open-runtime boundaries are checked | Preserve the successor-only universe bound and explicit evidence boundary. Recursive omega-equivalence evidence still waits on certificate representation. |
| H1 ordinary HoTT compatibility | active immediate surface; Candidate H, structural Sigma/record path compatibility, ordinary `TypeEquiv` algebra, and canonical groupoid decoder round trips/action coherence are promoted | Preserve the propositional decoder square and arbitrary-`ua_grpd` boundary; direct observational universe identity remains a later track. |
| H2/HIT layer | deferred | Begin only after the observational equality and restricted higher-elimination owners are credible. |
| Path algebra/opposite | E0 shared composition/collapse removal, E1 functor-owned symmetry/propositional coherence, Candidate C's shaped PathRecord reflexivity registry, and the Phase 10 registered-action owner are active | Preserve the classified runtime/propositional boundary. Fibrancy and additional structured J remain prerequisite on a sound registered classifier/motive capability and a selected concrete beta rather than following from action alone. |
| Omega0/category analogue | D0/D0b/D1 promoted: public fixed-map Sigma package, evidence-routed observations, opposite/Product closure, canonical categorical decoder, an integrated next-hom witness, the core-inclusion specialization, and a decoder-induced ordinary object `TypeEquiv` are active | Preserve the one-sided fibre/property boundary and exact evidence ownership; consume the specialized discrete hom action through recursive dimension rather than adding another stored field. |
| Discreteness/directed dimension | exact native-groupoidal `IsDiscreteCat`, independent `IsObjTruncCat`, native `CatDim`, recursive `IsNCat`, evidence-retaining packages, a native `OneCat` next-hom consumer, the unconditional `ncat_obj_trunc_EQ1` theorem, and full OneCat-scoped ordinary-iso univalence are promoted | Preserve the native evidence-property/retraction proof and computing finite-dimension equations. The global ordinary-iso capability and self-only D0 conditional theorem are retired; migrate the retained two-sided OneCat decoder only after concrete package/path coherence evidence. |
| Packaged `OneCat` ordinary-iso univalence | full scoped replacement active with synchronized 40-file CI; unused global capability inhabitants/classifier retired in the promoted follow-up | Retirement gates are closed. Keep the separately consumed `iso_evidence_path` Product compatibility owner until its own replacement exists; do not broaden the scoped theorem back to arbitrary categories. |
| Indexed adjunction migration | Phase 8 completed/promoted: `Adjunction(F,G)`, transparent functor views, stable observations, both triangles, opposite, mates, trust negatives, and reviewer example are active at 978/157 warnings | Preserve the indexed owner and stable observation boundary; reopen only for an owner bug or a declaration-backed named-operation consumer. |
| Direct observational universe identity | split by layer: the finite groupoid view is completed with synchronized 34-file CI and direct groupoid equality remains rejected; direct `OmegaEquiv(Cat_cat,A,B)` identity is completed with synchronized 35-file CI; the finite fixed-arrow certificate observation/path view is completed with synchronized 36-file CI and direct recursive certificate equality is rejected | Preserve the finite view's one-way/no-eta boundary, generic reflexivity, the groupoid fallback, and the categorical opaque-certificate reopen trigger. The selected conditional `IsNCat` theorem may consume only an explicit evidence-property capability. |
| Universe/metatheory | deliberately deferred | No concrete implementation slice should claim consistency, stratified closure, or a model merely from Lambdapi acceptance. |

The present feasibility assessment is positive but bounded:

1. No concrete Lambdapi expressibility blocker has been found for the proposed
   record convention, truncation-property kernel, elementary H0 classifiers,
   conservative/shaped record paths, standard Pi beta/eta surface, fixed-map
   omega-equivalence telescope, or indexed adjunction telescope.
2. All seven original append-only OETU probes listed below pass warning-enabled
   checking as of 2026-07-14. They establish plausibility only, not final owner
   placement, subject-reduction behavior in source order, or global coherence.
3. Candidate G has stronger promoted evidence. The fresh owner-position
   full-file source and its complete retargeted diagnostic suite pass quiet and
   warning-enabled checks; the active promotion then passes the bounded kernel
   and diagnostic check. Its warning inventory is neutral at 1,109 unjoinable
   critical-pair reports plus 163 replaceable-pattern advisories, no report
   mentions a new elementary owner, and the strict LHS audit remains at zero.
   The active catalog classifies all 17 new checks, including the local
   `assertnot false ≡ true` control, without upgrading that control to a
   canonicity or no-confusion theorem.
4. Candidate A likewise has promoted owner-position evidence. The named
   `PathRecord_grpd(A)` carrier/classifier, three dependent projections, and
   generated-eliminator facade pass the full source and retargeted suite
   quietly and warning-enabled. A probe-only nested-Sigma presentation passes
   alongside it; both preserve the 1,109/163 warning inventory. The named
   record is selected because it exposes stable field names and a direct
   three-field eliminator, whereas the comparison uses nested
   `sigma_Fst(sigma_Snd(...))`/`sigma_Snd(sigma_Snd(...))` access. No runtime
   eta, equality rewrite, or `unif_rule` is introduced, and the active negative
   eta control remains open as intended.
5. Candidate B has promoted owner-position evidence immediately after
   `IsContr`. Native `TruncLevel`, the two recursive `IsTruncGrpd` equations,
   readable low-level aliases, and evidence application pass the full source
   and retargeted suite quietly and warning-enabled with the same 1,109/163
   inventory and zero strict-LHS candidates. This activates only the
   definitional equality-lowering row; every stronger closure fact remains
   explicitly prerequisite.
6. Phase 3 has promoted owner-position evidence immediately after the active
   low-level truncation views. `TruncGrpdData(n)`/`TruncGrpdU(n)`, direct
   carrier/evidence projection beta, and the proposition/set/groupoid aliases
   pass the full source and retargeted suite quietly and warning-enabled with
   the unchanged 1,109/163 inventory and zero strict-LHS candidates. Fourteen
   active checks retain evidence, reject runtime package eta, and reject the
   false same-level typing; they do not establish evidence irrelevance,
   package univalence, or the expected `(n+1)` universe theorem.
7. A separate adversarial proof-time-unification control confirms the exact
   trust boundary. An intentionally unjustified two-rigid-head `unif_rule`
   leaves its sides non-convertible but nevertheless lets typed `eq_refl`
   inhabit their cross-head equality. Thus typed `eq_refl` is the correct
   operational test that a rule fires, but not an independent mathematical
   validation of the rule. This does not reject `unif_rule`; it classifies a
   selected rule as trusted logical authority at proof time.
8. A separate full-file `Path_cat` composition audit now supplies stronger
   evidence. Keeping `comp_fapp0(Path_cat(A),...)` as the shared category-level
   composition head, removing its fold to J-derived `eq_trans`, and adding two
   narrow `eq_refl` unit bridges passes the full active source, the entire
   migrated check suite, warning-enabled checking, runtime units, generic
   proof-time associativity, and a J-derived propositional comparison with
   `eq_trans`. The unjoinable-pair inventory falls from 1,109 to 1,091 in that
   candidate; this is useful diagnostic evidence, not a confluence proof.
9. Folding `comp_fapp0(Path_cat(A),...)` to the existing postcomposition action
   head instead makes the unit and pre/post comparison probes pass but causes
   associativity consumers to exceed the bounded check. The layered owner is
   therefore currently better supported: `comp_fapp0` owns category-level
   composition, while `hom_postcomp_fapp0` and
   `hom_precomp_along_fapp0` separately own oriented runtime actions.
10. Removal of the self-opposite collapse in the shared-composition full-file
   candidate also passes the entire migrated suite warning-enabled, reducing
   the unjoinable-pair inventory further to 1,072. A minimal
   `PathSym_A` functor from `Path(A)^op` to `Path(A)` then passes the full
   source and migrated suite
   with strict reflexivity and anti-composition through generic functoriality,
   propositional `eq_sym` agreement and involution, and a pointwise
   `Core_incl_func`/opposite square. That candidate reports 1,084 unjoinable
   pairs: twelve reports mention the new functor owner and became the promotion
   classification set, while the strict inferred-LHS audit has no unreviewed
   slot. The final rebased promotion classifies them and, after minimizing six
   generic mapped-`DefIso` endpoint guards, passes at 974/159.
11. Candidate C now has stronger owner-position evidence. The genuinely
   dependent `PathRecord` exposes a nested-Sigma path view, literal
   reflexivity selects one stable shaped head, its source/dependent-tail
   projections and reflexive `ind_eqr` beta compute, and one nested former
   iterates the design. A complete literal-reflexivity inventory registers the
   head only at shared path units, PathSym, Core inclusion, `idtoiso_cat`, and
   `idtoequiv_cat`. Forty active checks cover the core, both-order action and
   naturality diamonds, and four negative boundaries. The promoted warning
   inventory is 991/157 with zero unreviewed LHS candidates; arbitrary action,
   raw structured-path J, and runtime record eta remain absent.
12. Candidate H now has promoted owner-position evidence. Stable
   `PiHapply`/`PiFunext` heads retain the related-input Pi action, pointwise
   beta, and generic-J propositional eta. The sole new `unif_rule` is selected
   as a generic semantically justified proof-time structural law: a separate
   transparent owner reduces the same reflexive equation, typed `eq_refl`
   tests firing, and conversion-negative plus application-first checks retain
   the runtime/shaped-reflexivity boundary. The reviewed generic
   `is_equiv_map_by_inverse` capability converts explicit round trips to the
   active contractible-fibre definition and exposes only the selected fibre
   centre. Twenty-nine active diagnostics and a reviewer example pass; the
   warning inventory remains 991/157 and the strict LHS audit remains zero.
13. The exact `IsDiscreteCat` Product contract is now active. Its fixed-core
   factor feeds promoted D0b directly, the hom action's object projection is
   `path_to_hom`, and the selected inverse plus both coherent directions pass
   owner-position checks. The earlier append-only probe only typed this target;
   the Phase 9 source/check pair now inhabits it without a third stored field.
14. General truncation invariance is active. Mapping the operational groupoid
   decoder path through `IsTruncGrpd(n,-)` and applying `idtoequiv_grpd`
   produces one canonical `TypeEquiv` of evidence classifiers, both transport
   directions, reflexive computation, and inherited round trips without a new
   rewrite or `unif_rule`. Ten positive/one negative diagnostics and a seven-
   positive/two-negative reviewer example preserve 978/157 warnings and the
   zero/45/27 strict audit; the synchronized gate passes 20 files in 97.398s.
15. Fixed-map categorical object-truncation invariance is also active. The
   owner-position probe rejected the more elaborate inverse-component route
   in favor of mapping `Obj` over the existing
   `omega_equiv_along_path_D1(u)` category path. The resulting ordinary object
   equivalence feeds the general theorem at `IsObjTruncCat`; five semantic
   definitions, twelve positive/three negative diagnostics, and an eight-
   positive/two-negative reviewer example are warning/LHS neutral. The
   synchronized gate passes 21 files in 98.423s. Runtime agreement with
   `fapp0(F)` is deliberately not claimed. At that gate the recursive `IsNCat`
   theorem still waited on omega-equivalence evidence truncation and Sigma
   closure; Sigma closure is now active, leaving the evidence representation.
16. General one-step truncation monotonicity is active. Explicit path
   cancellation contracts every path space of a contractible classifier, and
   the native `TruncLevel` eliminator recursively lifts this base. The owner
   split is semantically forced: path contraction lives after the low-level
   truncation views, while the all-`Grpd` classifier theorem waits for
   `Grpd_grpd` decoding. Fully explicit Sigma indices failed elaboration; the
   inferred constructor indices are the selected, full-file-validated form.
   Twelve positive/one negative diagnostics and an eight-positive/one-negative
   reviewer example add no rule or `unif_rule`, preserve 978/157 warnings and
   zero/45/27 audit results, and bring the catalog/health inventory to 1,261
   checks across 39 areas and 22 files. The synchronized CI gate passes in
   127.18s.
17. Truncation evidence is proposition-valued at every native level. The base
   compares contractibility structures through the dependent Sigma path view;
   contractible and proposition-valued dependent-Pi lemmas supply the
   recursive step. A transparent `ind_TruncLevel` declaration and its base
   compute, but successor conversion unfolds the reducible Pi/equivalence
   motive past the 60s bound. Owner evidence therefore revises the design to a
   stable theorem head with two disjoint classifier-consumer equations. The
   full owner/check pair passes quietly and warning-enabled at 978/157 and
   zero/45/27; sixteen positive/two negative diagnostics, an eight-positive/
   two-negative reviewer example, 1,279 checks across 40 areas, and a 23-file
   health inventory are active. Open evidence is not definitionally erased;
   the synchronized CI gate passes in 75.41s.
18. Arbitrary-level dependent-Pi truncation closure is active. The base is
   `is_contr_pi`; the successor helper applies the recursive theorem to the
   pointwise path family and transports the result back through
   `pi_happly_type_equiv` using general invariance. Owner-position evidence
   selects a stable `is_trunc_pi` head with two consumer equations, and
   `is_prop_pi` now routes through its `-1` specialization rather than
   duplicating the semantic body. Ten positive/one negative diagnostics, an
   eight-positive/one-negative reviewer example, 1,290 checks across 41 areas,
   and a 24-file health inventory pass at unchanged 978/157 warnings and
   zero/45/27 audit. The synchronized CI gate passes in 131.21s.
19. Same-level dependent-Sigma truncation closure is active. The explicit
   contractible-total base pairs centres and transports the target fibre
   component along the base contraction. At successors, the recursive theorem
   consumes the existing `SigmaPathView`; reducible `PathOver` exposes the
   transported fibre equality needed by the fibre hypothesis. Ten positive/
   two negative diagnostics, an eight-positive/two-negative reviewer example,
   1,302 checks across 42 areas, and a 25-file health inventory pass with a
   stable two-equation owner, unchanged 978/157 warnings, and zero/45/27
   audit. The synchronized CI gate passes in 136.09s.
20. The planned recursive omega-equivalence evidence theorem is not yet proof-
   ready. `OmegaEquivAlong_D0(f)` is declared as an opaque `constant`, has an
   empty decision tree and no general constructor/eliminator, and the public
   semantic compatibility fibre has only a one-sided retraction. These
   observations do not construct paths between arbitrary evidence. The
   prerequisite is an explicit recursive certificate representation or an
   independently justified evidence-path capability; no property-valuedness
   axiom is selected. Independent truncated-universe package-path control is
   dependency-ready and therefore proceeded first.
21. Truncated-universe package-path control is now promoted. The native
   package eliminator, named carrier/evidence path view, evidence-derived
   reconstruction, both propositional inverse laws, reflexive theorem, and
   ordinary path `TypeEquiv` pass owner-position and active gates. Fifteen
   positive/three negative diagnostics and an eight-positive/three-negative
   reviewer bring the catalog to 1,320 checks across 43 areas and health to 26
   files without changing 978/157 warnings or zero/45/27 audit; synchronized
   26-file CI passes in 188.15s. The next
   independent fact is the restricted composition with canonical ambient
   groupoid univalence; the `(n+1)` universe theorem remains separately gated
   by truncation of carrier-equivalence classifiers.
22. Restricted truncated-universe univalence is now promoted by composing the
   path `TypeEquiv` with the canonical ambient decoder package. Exact forward
   and selected-inverse projections, two propositional round trips, forward
   reflexivity, and propositional inverse reflexivity pass. Twelve positive/
   three negative diagnostics bring the catalog to 1,335 checks across 44
   areas and health to 27 files without changing 978/157 warnings or
   zero/45/27 audit. A focused follow-up constructs every map between
   contractible classifiers as an equivalence through an explicit constant
   inverse, proves its evidence contractible, and derives contractibility of
   `TypeEquiv(A,B)`; this closes the nontrivial base prerequisite for the
   selected package-universe level theorem. Synchronized 27-file CI for the
   restricted-univalence slice passes in 282.49s.
23. The expected package-universe level theorem is now promoted. The
   explicit-inverse base makes `TypeEquiv(A,B)` contractible for contractible
   endpoints; the successor branch uses Pi/Sigma closure and
   proposition-valued equivalence evidence, with source truncation
   intentionally unused outside the base. The stable two-equation
   `is_trunc_type_equiv` owner feeds `is_trunc_grpd_universe` through
   restricted package univalence. Seventeen positive/three negative
   diagnostics and an eleven-positive/three-negative reviewer example bring
   the catalog to 1,355 checks across 45 areas and health to 28 files without
   changing 978/157 warnings or zero/45/27 audit.
24. Product reflexivity provenance is now promoted. Exactly the two ordinary-
   iso and fixed-map omega Product reflexive-collapse rule declarations are
   removed; componentwise evidence remains the selected normal form through
   recursive cells and decoders, while inverse-arrow projections still join
   the generic Product identity spelling. No replacement rewrite or
   `unif_rule` is added. Eleven scoped diagnostics, adjacent encoder controls,
   and a nine-positive/five-negative reviewer example bring the catalog to
   1,360 checks across 46 areas and health to 29 files. Warnings improve from
   978/157 to 972/157, the audit remains zero/45/27, and synchronized CI passes
   in 189.90s. Visible-constructor Boolean observational equality is selected
   next as the first remaining conservative `OETU-OBS-MVP` former.
25. Visible-constructor Boolean observational equality is now promoted. The
   four closed constructor pairs compute to the Unit/Empty classifier matrix,
   while generic `eq_refl` retains its runtime provenance. The initially
   probed collapse to native `tt` required a closed J/PathSym/Core/path-unit/
   encoder registry and added exactly 42 unjoinable reports: 14 literal-
   reflexivity consumer overlaps, 12 PathSym higher-owner overlaps, and 16
   Core overlaps. It is rejected together with a proof-time equation because
   no typed consumer requires proof erasure. The four-equation minimum is
   warning-neutral at 972/157, retains zero/45/27 audit results, adds 22
   positive/11 negative diagnostics and an 11-positive/6-negative reviewer
   example, brings the catalog to 1,393 checks across 47 areas and health to
   30 files, and passes synchronized CI in 143.199s. Visible Unit equality is
   selected next under the same provenance policy.
26. Visible-constructor Unit observational equality is now promoted. The sole
   equation reduces `tt = tt` to `Unit_grpd` while generic `eq_refl` retains
   proof provenance; no J/path/Core/unit/encoder registry or `unif_rule` is
   added. Ten positive/nine negative diagnostics and a seven-positive/six-
   negative reviewer example preserve 972/157 warnings and zero/45/27 audit,
   bring the catalog to 1,412 checks across 48 areas and health to 31 files,
   and pass synchronized CI in 153.385s. Recursive visible Nat equality is
   selected next; Empty has no visible constructor pair to register.
27. Recursive visible Nat equality is promoted together with a newly required
   generic-J subject-reduction guard. The four classifier equations expose
   Unit, Empty, or predecessor equality while outer zero/successor reflexivity
   remains visible. The rejected classifier-only candidate allowed predecessor
   and foreign reflexivity to fire the inferred-index J beta: a proof-dependent
   injective motive produced a declared predecessor-indexed term whose normal
   form was the outer-indexed branch, and that branch failed a direct typing
   check at the declared result. The selected J rule repeats its category and
   endpoint, restores the stuck boundary, preserves normal reflexive J, adds no
   registry or `unif_rule`, and removes the old generic-J/PathRecord warning.
   Twenty-three positive/eleven negative Nat diagnostics, four separate guard
   negatives, and an eleven-positive/eight-negative reviewer example bring the
   catalog to 1,450 checks across 50 areas and health to 32 files. Warnings
   improve to 971/157, the audit remains zero/45/27, and synchronized 32-file
   CI passes in 151.336s. General visible-sum equality is selected next.
28. General visible binary-sum equality is promoted under the guarded
   provenance contract. Same-tag paths recurse to component equality, mixed
   tags expose Empty, and outer sum reflexivity remains distinct from
   component reflexivity at runtime and proof time. A proof-dependent motive
   confirms the J guard at this new classifier. Inferring six reconstructible
   constructor indices removes the initial 163-advisory warning delta, leaving
   971/157 warnings and zero/45/27 audit. Twenty-four positive/eleven negative
   diagnostics and a twelve-positive/eight-negative reviewer example bring the
   catalog to 1,485 checks across 51 areas and health to 33 files. Synchronized
   CI passes with 161.044s of measured checking time (167.96s wall time).
29. The first Phase-13 groupoid-universe comparison selects the named finite
   identity view. A direct rule headed by reducible `Grpd_grpd` first adds one
   avoidable alias-unfold critical pair; the canonical `(Obj Grpd_cat)` rule
   is warning-neutral and passes the existing full suite. Nevertheless,
   normalizing public self-universe equality under that rule recursively
   reopens the same equality and exceeds 20 seconds. Baseline equality,
   standalone `TypeEquiv`, and the named view all normalize within the bound.
   `GrpdPathView(A,B) := TypeEquiv(A,B)` therefore becomes the active fallback,
   with decoder-owned encode/decode, both propositional inverse laws,
   transport agreement, and Product/Pi/Sigma consumers. Seventeen positive/
   seven negative diagnostics and a fourteen-positive/five-negative reviewer
   example bring the catalog to 1,509 checks across 52 areas and health to 34
   files; warnings and audit remain 971/157 and zero/45/27. No rule or
   `unif_rule` is added. Synchronized 34-file CI passes with 182.160s of
   measured checking time (189.18s wall time).
30. The categorical Phase-13 comparison selects the direct canonical owner.
   `@=(Obj Cat_cat,A,B)` reduces to the already-promoted
   `OmegaEquiv(Cat_cat,A,B)` Sigma package, whose opaque
   `OmegaEquivAlong_D0` evidence boundary makes self-universe normalization
   finite. The canonical spelling is warning-neutral at 971/157; a reducible
   `Cat_grpd` LHS adds one alias-unfold report. Twelve semantic symbols route
   the readable `CatPathView`, canonical package reflexivity, encoder/decoder
   round trips, selected functor/evidence, Product action, and D0b next-hom
   package through existing owners. Generic `eq_refl` remains distinct: the
   rejected collapse adds three reports and prevents the existing
   `omega_equiv_along_obj_path` reflexive `eq_ap` branch from reducing.
   Twenty-two positive/eight negative diagnostics and a fifteen-positive/
   six-negative reviewer pass active checks; one classifier rule and no
   `unif_rule` are added. The closed catalog has 1,539 checks across 53 areas;
   health checks 35 files with a 17,989-line/750-symbol/575-rule/51-
   unification-rule kernel and 1,389 positive diagnostics. The full reviewer
   sweep passes, and synchronized CI passes with 165.477s of measured checking
   time (171.88s wall time). Any future fixed-arrow certificate representation
   must reopen the self-universe normalization decision.
The following items 31–33 are historical 2026-07-16 promotion records. The
2026-07-19 P4 consumer audit later retired all named one-layer, conditional,
and dimension-indexed D0 experiment symbols and their self-only examples;
their measurements and negative conclusions remain provenance.

31. The fixed-arrow certificate comparison selected a finite native observation
   view rather than direct recursive equality. The nested
   `OmegaEquivAlongObservation_D0(f)` record contains exactly the selected
   left/right inverse arrows and recursive left/right cell packages;
   `OmegaEquivAlongPathView_D0(u,v)` is equality of two such records, and a
   genuine certificate path acts on it by `eq_ap`. The owner-position finite
   source and inherited suite pass quietly and warning-enabled, the same
   self-universe view normalizes within 20 seconds, and D0b next-hom evidence
   projects through the observation map. By contrast, adding the direct
   certificate-equality rule makes the owner-position source exceed 30 seconds
   and its append-only canonical self-universe control exceed 20 seconds.
   Thirteen positive/three negative diagnostics and a ten-positive/three-
   negative reviewer are active; five semantic symbols, no rule or
   `unif_rule`, unchanged 971/157 warnings, and zero/45/27 audit are measured.
   The catalog has 1,555 checks across 54 areas; health checks 36 files with an
   18,104-line/755-symbol/575-rule/51-unification-rule kernel and 1,402
   positive diagnostics. The full reviewer sweep and synchronized CI pass with
   186.423s of measured checking time (193.35s wall time). No decoder, eta,
   property-valuedness, or truncation theorem follows from this one-way view.
   The dependency audit therefore splits the object-truncation theorem: its
   `CatDim` induction, Sigma closure, and univalence transport are selected as
   a conditional executable slice, while construction of the required global
   fixed-arrow evidence-property capability remains representation-blocked.
32. The conditional directed object-truncation split was mechanically viable.
   `OmegaEquivAlongEvidenceProp_D0` is an uninhabited Pi-classifier over all
   fixed arrows. `prop_is_trunc_cat_dim` has exact zero/successor equations,
   and `ncat_obj_trunc_from_evidence_prop` computes from the discrete base or,
   at successor, closes `OmegaEquiv(C,x,y)` by homwise induction and same-level
   Sigma truncation before transporting through `cat_univalence_type_equiv`.
   Owner-position source, inherited checks, exact signature, and an eight-
   positive/four-negative reviewer pass. Eleven positive/four negative active
   diagnostics include a `OneCat` consumer and typed `eq_refl` proof-time
   negative. Two two-branch rule families add no `unif_rule`, preserve 971/157
   warnings, and retain zero/45/27 strict audit. The catalog has 1,570 checks
   across 55 areas; health checks 37 files with an 18,173-line/758-symbol/577-
   rule/51-unification-rule kernel and 1,413 positive diagnostics. Full
   examples and synchronized CI pass with 198.816s measured checking time
   (206.34s wall time). This completes the induction only conditionally; it
   does not construct the capability.
33. At that checkpoint, explicit directed dimension supplied a recursion-safe certificate
   observation boundary. `OmegaEquivAlongDimObservation_D0(n,h,f)` is Unit at
   zero; its successor is the nested inverse-arrow Sigma whose Product factors
   pair each selected D0 cell arrow with an observation at `n` in the
   corresponding hom-category. The observation map reuses the four D0 owners,
   all inverse/cell/deeper projections compute, and ZeroCat/OneCat controls
   establish termination. The finite path view has canonical reflexivity and
   one-way `eq_ap` action. Owner/signature/inherited-check and reviewer probes
   pass; 17 positive/5 negative diagnostics and a 12-positive/4-negative
   reviewer preserve 971/157 warnings and zero/45/27 audit. Six symbols and
   two two-equation rule families add no `unif_rule`. The catalog has 1,592
   checks across 56 areas; health checks 38 files with an 18,452-line/764-
   symbol/579-rule/51-unification-rule kernel and 1,430 positive diagnostics.
   This proves finite observability, not reverse decoding, extensionality,
   certificate property-valuedness, or the unconditional `IsNCat` theorem.
   Full examples and synchronized 38-file CI pass with 201.708s measured
   checking time (212.59s wall time).
34. The best/original goal therefore remains credible as a staged
   implementation and research program. It is not yet demonstrated as one
   globally normalizing implementation. The largest concrete risks are
   the recursive fixed-map certificate representation/evidence theorem,
   arbitrary structural-action fibrancy and
   additional shaped-J computation, direct observational universe identity,
   and the unstratified global category-univalence policy.
35. Deferred `Cat_cat : Cat` consistency, universe stratification, and general
   semantic/metatheoretic justification do not block the concrete MVP, but
   every report and code comment must preserve that boundary.

The revised audit verdict is:

| Boundary | Revised conclusion | Remaining promotion gate |
| --- | --- | --- |
| `Path_cat` composition and opposite/symmetry | E0 and E1 are active: shared category composition, distinct oriented pre/post runtime actions, genuine opposite presentation, and `PathSym_A` functor action replace the old folds. J-derived transitivity, symmetry agreement, involution, and the pointwise Core square remain propositional. | Preserve the twelve-block classification and minimized mapped-`DefIso` owner. D1 now supplies the public fixed-map package boundary; package `PathSym_A` only in its separately selected consumer slice. |
| Hybrid generic/shaped `J` and Candidate H | Promoted bounded core. Generic primitive J now repeats category and endpoint as subject-reduction guards; together with the selected reflexive Pi coherence basis it proves propositional eta even when the equality classifier is shaped. Stable owners retain the equation as a generic semantically justified proof-time law, the transparent owner independently obtains it by conversion, and the reviewed quasi-inverse theorem supplies active contractible fibres. | Preserve the proof-time/runtime negatives, foreign/predecessor-reflexivity guard probes, and application-first shaped join. Fibrancy remains necessary only for extra runtime betas on arbitrary structured constructors; Sigma/record round trips are the next separate slice. |
| Direct universe equality | The groupoid owner comparison selects `GrpdPathView(A,B) := TypeEquiv(A,B)` as the finite active fallback. Direct public equality is warning-neutral in canonical spelling but recursively expands self-universe equality beyond the 20-second bound. | Preserve the named decoder-owned view. Reopen a direct groupoid rule only with stratification or a measured recursion guard; categorical identity remains a separately bounded Phase-13 question. |
| Global ordinary-iso univalence | Exploratory compatibility approximation, not successor architecture for arbitrary `Cat`. | Freeze new uses in Phase 0; migrate/retire after OneCat-scoped replacement. |
| Fixed-map omega-equivalence | D0/D0b/D1 are promoted: the recursive fixed-arrow owner/package, variable-evidence Cat hom action, public normal form, opposite/Product generators, decoder, fibre comparison, and integrated witness all pass owner-position gates. | Preserve the 990/157, zero-strict-LHS, evidence-routed boundary; property-valuedness and concrete fixed-functor specializations remain separate. |
| `IsDiscreteCat` foundation | The exact Product, nonredundant set-object/fixed-core factors, D0b-derived homwise evidence, arrow-to-path inverse, and both coherent directions are active. | Preserve this boundary; the current recursive-dimension slice must consume it through `IsNCat`/`OneCat` without adding a third field or runtime cancellation. |
| Decoder and equivalence-algebra ownership | Groupoid decoder results belong only to `OETU-GRPD-UNIV-DECODER`; `TypeEquiv` algebra owns only ordinary equivalence operations. | Categorical decoder finalization is completed jointly with D1 under `OETU-CAT-UNIV-DECODER`; preserve the split ownership and propositional runtime boundary. |
| Product reflexivity provenance | The two generic-reflexive collapse rules are removed. Ordinary-iso and omega Product constructors remain componentwise at reflexivity; projections compute and the warning inventory improves to 972/157. | Preserve the componentwise runtime normal form. Add a proof-time comparison only for a concrete typed consumer with an explicit semantic trust class; do not infer omega-evidence property-valuedness. |
| Visible Unit/Boolean/Nat/general-sum equality | Unit, Boolean, recursive Nat, and general-sum constructor pairs reduce only their classifiers to Unit, Empty, predecessor, or component equality. Generic outer `eq_refl` remains the proof normal form. Nat owner evidence selected the category/endpoint J guard after a proof-dependent subject-reduction failure; Sum revalidates that guard and minimizes six constructor indices. | Preserve proof provenance, open generic equality, raw-`tt`, predecessor/component/foreign-reflexivity negatives, and the guarded J owner. Reopen proof erasure only for a concrete semantic consumer, and classify any proposed `unif_rule` independently. |
| Proof-time `unif_rule` authority | A semantically justified rule is a legitimate and potentially important Emdash proof-time definitional mechanism, not merely a disposable elaboration trick. It is also trusted logical authority: typed `eq_refl` shows that the rule fires, not that its equation is sound. | Classify every promoted rule as declaration/field-backed, structurally justified selected proof-time law, or explicit postulate. Candidate H retains its selected generic bridge; Phase 8 Candidate F installs none because no declaration backing exists. Do not require a duplicate internal path for every generic law when its trusted definitional status and semantic obligation are explicit. |

### Complete OETU probe and evidence inventory

These are the current probe artifacts relevant to this plan. They live under
ignored `tmp/probes/`; they are review evidence, not source authorities and
not durable active diagnostics.

| Probe | What it demonstrates | Promotion boundary that remains |
| --- | --- | --- |
| `tmp/probes/oetu_architecture_feasibility_probe.lp` | One-constructor dependent records, truncation codes/predicate/package, conservative record paths, a stable nondependent shaped-reflexivity head with reflexive `ind_eqr`, strict local path operations, and recursive `IsNCat` formation. | It combines several late append-only experiments. Split the selected slice, place it at each real owner, cover dependent/nested action where claimed, and audit all literal-`eq_refl` consumers. |
| `tmp/probes/oetu_record_convention_owner_full.lp` plus `tmp/probes/oetu_record_convention_owner_checks_full.lp` | Candidate A at the foundations owner, with a decoded parametrized `PathRecord`, named dependent projections, generated-eliminator facade, no-eta control, the complete retargeted suite, and a probe-only nested-Sigma comparison. | **Promoted 2026-07-15.** The named-record surface is active; nested Sigma remains comparison evidence. Candidate C now owns its shaped equality/reflexivity/reflexive-J layer, while arbitrary action/additional J and generic generation remain separate. |
| `tmp/probes/oetu_shaped_reflexivity_owner_full.lp` plus `tmp/probes/oetu_shaped_reflexivity_owner_checks_full.lp` | Candidate C at every real owner: dependent/nested PathRecord path view, stable reflexivity, ordered projection and reflexive-J betas, the literal-reflexivity registry, both-order action/naturality consumers, and negative arbitrary-action/J/eta controls. | **Promoted 2026-07-15.** Preserve the 991/157 classified boundary and explicit PathSym categories. Structural action, additional raw-constructor J computation, arbitrary path-data round trips, and broad former migration remain separate. |
| `tmp/probes/oetu_pi_funext_owner_full.lp` plus `tmp/probes/oetu_pi_funext_owner_checks_full.lp` | Candidate H at the Pi and equivalence owners: stable diagonal observation/extension, related-input action, pointwise beta, proof-time reflexive basis, generic-J eta, explicit quasi-inverse data, reviewed conversion to contractible fibres, selected-centre projection, application-first shaped joins, and runtime/arbitrary-J/opaque-contraction negatives. | **Promoted 2026-07-15.** Preserve the generic structurally justified trust classification, no whole-function runtime eta, and the 991/157 warning-neutral boundary. Arbitrary Sigma/record round trips, structured-Pi J/fibrancy, and ordinary `TypeEquiv` algebra remain separate. |
| `tmp/probes/oetu_trunc_level_owner_full.lp` plus `tmp/probes/oetu_trunc_level_owner_checks_full.lp` | Candidate B immediately after active contractibility, with native level codes, recursive truncation equations, low-level views, definitional equality-lowering evidence application, and the complete retargeted suite. | **Promoted 2026-07-15.** Packages, closure/invariance theorems beyond the active recursion step, evidence property-valuedness, and reflectors remain separate. |
| `tmp/probes/oetu_trunc_universe_owner_full.lp` plus `tmp/probes/oetu_trunc_universe_owner_checks_full.lp` | Phase 3 immediately after the active truncation views, with a decoded parametrized carrier/evidence record, direct projections, low-level universe aliases, evidence-retention/no-eta/no-same-level controls, and the complete retargeted suite. | **Promoted 2026-07-15.** Evidence property-valuedness/proof erasure, package paths/univalence, closure and universe-level truncation theorems, and reflectors remain separate. |
| `tmp/probes/oetu_fixed_map_followup.lp` | Historical transitional `OmegaEquivAlong(F)` bridge into the formerly opaque `OmegaEquiv`, computing selected-map/inverse observations, recursive higher-cell endpoints, and the semantic homotopy fibre. | Superseded by promoted D0/D0b/D1. Retain only as historical comparison evidence; the active fibre is a one-sided compatibility reference and still does not imply property-valuedness. |
| `tmp/probes/oetu_omega_equiv_along_d0_owner_full.lp` plus `tmp/probes/oetu_omega_equiv_along_d0_owner_checks_full.lp` | Candidate D0 at the intended source owner: a neutral general-`C` fixed-arrow certificate, transparent Sigma package and exact projections, selected inverse/recursive cell observations independent of the old public classifier, reflexive certificate computation, one projected recursive next-hom observation, and package-eta/raw-cancellation negatives. | **Promoted 2026-07-15.** Quiet logs end in `20260715-193153`/`193201`; warning-enabled logs end in `20260715-193222` and preserve 991/157 with zero strict-LHS candidates. D0b and D1 are promoted by the following rows; property-valuedness remains separate. |
| `tmp/probes/oetu_omega_equiv_along_d0b_owner_full.lp` plus `tmp/probes/oetu_omega_equiv_along_d0b_owner_checks_full.lp` | Candidate D0b after the transformation-component owners: variable `u` induces evidence for `fapp1_func(F,x,y)`; the left inverse is `Hom(eta_x,epsilon_y) o L_1`, the right inverse builds `L <-> R` endpoint comparisons from both recursive cells before conjugating `R_1`, and both returned cell packages project and remain observable once more. Raw inverse hom actions are explicit negative endpoint controls. | **Promoted 2026-07-15.** Quiet logs end in `20260715-194634`/`194846`; warning-enabled logs end in `20260715-194900` and preserve 991/157 with zero strict-LHS candidates. Twenty-four positive and two negative checks plus the reviewer example are active. D1 is promoted by the next row; the later core-inclusion specialization and property-valuedness remain separate. |
| D1 cumulative owner/check snapshots, originally `tmp/probes/oetu_omega_equiv_d1_owner_full.lp` and `tmp/probes/oetu_omega_equiv_d1_owner_checks_full.lp` | Candidate D1 at all public owners: `OmegaEquiv := Sigma f, OmegaEquivAlong(f)`, exact projections/evidence-routed observations, one-sided fibre comparison, evidence-indexed decoder, reflexive/opposite/Product evidence generators, categorical decoder capability/round trips/named `TypeEquiv`, propositional `path_to_hom` square, and the D0b-derived integrated next-hom witness. Ten observation-versus-reflexive-evidence overlap families have explicit both-order checks. After D1 promotion these cumulative snapshots were carried forward and renamed as the Phase 8 full-file pair below; the dated D1 logs remain the exact D1 evidence. | **Promoted 2026-07-15.** Quiet source/check logs end in `20260715-202501`/`202612`; warning-enabled logs end in `20260715-202626`/`202912` and improve 991/157 to 990/157 with zero strict-LHS candidates. Forty-one positive/five negative diagnostics and a twelve-positive/four-negative reviewer example are active. No new `unif_rule`, package eta, reverse fibre eta, or property-valuedness claim is added. Core-inclusion specialization remains separate. |
| Phase 8 cumulative owner/check snapshots, originally `tmp/probes/oetu_adjunction_indexed_owner_full.lp` and `tmp/probes/oetu_adjunction_indexed_owner_checks_full.lp`, plus `tmp/probes/oetu_adjunction_indexed_example.lp` | Phase 8 at every active owner: `Adjunction(F,G)`, transparent left/right views, stable unit/counit heads, both direct-index triangles, `Op_adjunction : Adjunction(Op G,Op F)`, indexed mate and weighted preservation consumers, opposite involution, absent named-operation agreement, and raw-operation runtime-erasure control. After promotion the cumulative full-file pair was carried forward and renamed as the Phase 9 discrete pair below; the dated Phase 8 logs remain exact evidence. | **Promoted 2026-07-15.** Final quiet source/check/example logs end in `20260715-211431`/`211434`/`211628`; final warning-enabled source/check logs end in `20260715-211438`/`211636`. Inferred outer opposite indices reduce warnings from 990/157 to 978/157 while `comp_fapp0` remains 400 and the strict audit stays zero with 45 intentional slots across 27 clauses. Three positive/three negative diagnostics bring the catalog to 1,133 checks across 32 areas; the reviewer example has four positive/one negative statement. No `unif_rule` or existential package is added because no bound named-operation or unknown-functor consumer exists. |
| Phase 9 discrete cumulative owner/check snapshots, originally `tmp/probes/oetu_discrete_cat_owner_full.lp` and `tmp/probes/oetu_discrete_cat_owner_checks_full.lp`, plus `tmp/probes/oetu_discrete_cat_example.lp` | Phase 9 core at the D0b and D1 owners: a generic left-inverse/right-component compositor, the exact two-factor `IsDiscreteCat`, core hom action, D0b-derived homwise evidence, selected `hom_to_path`, its recursive left cell, and both coherent directions. After promotion the cumulative pair was carried forward and renamed as the directed-dimension pair below; the dated discrete logs remain exact evidence. | **Promoted 2026-07-15.** Quiet source/check/example logs end in `20260715-213519`/`213628`/`213709`; warning-enabled logs end in `20260715-213724`/`213729` and preserve 978/157 with zero strict-LHS candidates and 45 intentional slots across 27 clauses. Thirteen positive/four negative diagnostics bring the catalog to 1,150 checks across 33 areas; the reviewer example has six positive/two negative statements. No rewrite, `unif_rule`, third homwise field, package eta, or runtime cancellation is added. |
| Phase 9 directed-dimension cumulative owner/check snapshots, originally `tmp/probes/oetu_ncat_owner_full.lp` and `tmp/probes/oetu_ncat_owner_checks_full.lp`, plus `tmp/probes/oetu_ncat_example.lp` | Phase 9 directed dimension at the real category owner: independent object truncation, native `CatDim`, exact zero/successor `IsNCat` recursion, evidence-retaining `NCat(n)`, `ZeroCat`/`OneCat`, and a OneCat homwise consumer that iterates the promoted discrete theorem. After promotion the cumulative pair was carried forward and renamed as the Phase 10 action pair below; the dated Phase 9 logs remain exact evidence. | **Promoted 2026-07-15.** Quiet source/check/example logs end in `20260715-215526`/`215625`/`215659`; both warning-enabled logs end in `20260715-215723` and preserve 978/157 with zero strict-LHS candidates and 45 intentional slots across 27 clauses. Eighteen positive/five negative diagnostics bring the catalog to 1,173 checks across 34 areas; the reviewer example has seven positive/three negative statements. Four rule declarations (five equations) add no warning family or `unif_rule`; object-truncation implication and iso-univalence remain excluded. The synchronized CI gate passes all 17 files in 78.267s with all repository-integrity checks. |
| Phase 10 action cumulative owner/check snapshots, originally `tmp/probes/oetu_obs_action_owner_full.lp` plus `tmp/probes/oetu_obs_action_owner_checks_full.lp`, and `tmp/probes/oetu_obs_action_example.lp` | Phase 10 at the equality/Sigma owner and the first shaped former: selected `ObsAction`/`ObsDAction` operations carry semantic agreement, identity and nondependent composition compute, PathRecord open maps act on arbitrary shaped paths, and its dependent witness acts through `PathOver`; coherence is next-dimensional while arbitrary J remains negative. After promotion the cumulative source/check pair was carried forward and renamed as the H0 sum pair below; the dated action logs remain exact evidence. | **Promoted 2026-07-15.** Quiet source/check/example logs end in `20260715-222426`/`222458`/`222521`; both warning-enabled logs end in `20260715-222539` and preserve 978/157 with zero strict-LHS candidates and 45 intentional slots across 27 clauses. Thirty-one positive/five negative diagnostics bring the catalog to 1,209 checks across 35 areas; the reviewer example has ten positive/three negative statements. No rule or `unif_rule` is added; package eta, runtime agreement for arbitrary registrations, loop collapse, and arbitrary-constructor J remain negative. The synchronized CI gate passes all 18 files in 86.300s with all repository-integrity checks. |

The Phase 10 row is retained as dated promotion evidence. P1 of the
2026-07-19 path-action cleanup plan subsequently found no dependent selected-
action consumer, retired `ObsDAction`, and routed
`path_record_witness_action` directly through `eq_apd`; the nondependent
registry and the historical probe/log evidence remain.
| H0 sum cumulative owner/check snapshots, originally `tmp/probes/oetu_h0_sum_owner_full.lp` plus `tmp/probes/oetu_h0_sum_owner_checks_full.lp`, `tmp/probes/oetu_h0_sum_inductive_signature.lp`, and `examples/binary_sum.lp` | Phase 11 at the elementary native-inductive owner: general decoded `Sum_grpd(A,B)`, left/right constructors, dependent elimination, both generated betas, swap consumer, and conversion controls. The full-file pair is the cumulative continuation of Phase 10. The focused signature probe rejects a grouped `(A B : Grpd)` binder because the generated induction principle generalizes `B`; separate parameter binders retain both fixed classifiers. After promotion the cumulative pair was carried forward and renamed as the dimension-index pair below. | **Promoted 2026-07-15.** Quiet source/check/example logs end in `20260715-224632`/`224632`/`224846`; warning-enabled source/check logs end in `20260715-224650` and preserve 978/157 with zero strict-LHS candidates and 45 intentional slots across 27 clauses. Six positive/one negative diagnostics bring the catalog to 1,216 checks across 36 areas; the reviewer example has eight positive/two negative statements. Only the decoding rule is added; observational identity/no-confusion/higher action, open eta, canonicity, and categorical coproduct structure remain excluded. The synchronized CI gate passes all 19 files in 88.539s. |
| Dimension-index cumulative owner/check snapshots, originally `tmp/probes/oetu_ncat_dim_trunc_index_owner_full.lp` plus `tmp/probes/oetu_ncat_dim_trunc_index_owner_checks_full.lp`, and `tmp/probes/oetu_ncat_dim_trunc_index_example.lp` | Phase 9 theorem prerequisite at the native dimension owner: `cat_dim_trunc_level(cat_zero)` computes to `trunc_zero`, successor commutes, low-dimensional aliases normalize, and an explicit negative preserves the distinction between calculating the target index and constructing object-truncation evidence. The full-file pair is the cumulative continuation of H0 sum; after promotion it was carried forward into the general-invariance pair described next. | **Promoted 2026-07-15.** Quiet source/check/example logs end in `20260715-225901`/`225901`/`225945`; warning-enabled source/check logs end in `20260715-225915` and preserve 978/157 with zero strict-LHS candidates and 45 intentional slots across 27 clauses. Five positive/one negative active diagnostics bring the catalog to 1,222 checks across 36 areas; the directed-dimension reviewer example now has eleven positive/four negative statements. The two map equations add no warning family. Categorical equivalence invariance, recursive evidence truncation, and the implication theorem remain excluded. The synchronized CI gate passes all 19 files in 87.056s. |
| General-invariance cumulative owner/check snapshots, originally `tmp/probes/oetu_trunc_equiv_invariance_owner_full.lp` plus `tmp/probes/oetu_trunc_equiv_invariance_owner_checks_full.lp`, and `examples/truncation_invariance.lp` | Phase 11 general closure at the groupoid decoder owner: map `grpd_equiv_path(e)` through `IsTruncGrpd(n,-)`, decode the resulting classifier path to a canonical `TypeEquiv`, expose forward/backward evidence transport, inherit both round trips, compute on reflexivity, and keep an arbitrary self-equivalence open at runtime. After promotion the full-file pair was carried forward and renamed as the categorical-invariance pair below; the dated logs remain exact general-invariance evidence. | **Promoted 2026-07-15.** Quiet source/check logs end in `20260715-231122`; warning-enabled logs end in `20260715-231138` and preserve 978/157 with zero strict-LHS candidates and 45 intentional slots across 27 clauses. Ten positive/one negative active diagnostics bring the catalog to 1,233 checks across 37 areas; the reviewer example has seven positive/two negative statements. No rule or `unif_rule` is added. The synchronized CI gate passes all 20 files in 97.398s. |
| `tmp/probes/oetu_cat_trunc_equiv_invariance_owner_full.lp` plus `tmp/probes/oetu_cat_trunc_equiv_invariance_owner_checks_full.lp`, `tmp/probes/oetu_cat_trunc_equiv_invariance_signature.lp`, and `tmp/probes/oetu_cat_trunc_equiv_invariance_example.lp` | Phase 11 categorical consumer at the decoder and `IsObjTruncCat` owners. The focused signature and full-file evidence select `eq_ap(Obj,omega_equiv_along_path_D1(u))` followed by `idtoequiv_grpd`, rather than reconstructing inverse object maps from D0b components. General invariance then supplies the evidence-classifier `TypeEquiv`, both transports, reflexive computation, round trips, and open map/evidence negatives. The source snapshot is byte-identical to active promotion. | **Promoted 2026-07-15.** Focused quiet/warning logs end in `20260715-232323`; full source/check quiet logs end in `20260715-232534`, warning-enabled logs end in `20260715-232547`, and the scratch reviewer log ends in `20260715-232655`. All preserve 978/157 and zero/45/27. Twelve positive/three negative diagnostics bring the catalog to 1,248 checks across 38 areas; the reviewer example has eight positive/two negative statements. Five semantic definitions add no rule or `unif_rule`. Runtime agreement with `fapp0(F)`, recursive equivalence-evidence truncation, and the `IsNCat` implication remain excluded. The synchronized CI gate passes all 21 files in 98.423s. |
| `tmp/probes/oetu_trunc_monotonicity_owner_full.lp` plus `tmp/probes/oetu_trunc_monotonicity_owner_checks_full.lp`, `tmp/probes/oetu_trunc_monotonicity_signature.lp`, `tmp/probes/oetu_trunc_level_recursor.lp`, and `examples/truncation_monotonicity.lp` | Phase 11 constructive one-step monotonicity. Focused signature evidence proves path cancellation, contracts every path space of a contractible classifier, and then uses the generated `ind_TruncLevel` owner for arbitrary levels. Owner-position evidence forces the path/base helpers after `IsGroupoidGrpd` and the all-classifier theorem after `Grpd_grpd` decoding. A fully explicit `@Struct_sigma` base fails elaboration; inferred Sigma indices are selected. | **Promoted 2026-07-15.** The recursor log ends in `20260715-234419`; the rejected/selected focused logs end in `20260715-234333`/`234454`; warning-enabled full evidence ends in `20260715-234748`; renamed quiet source/check logs end in `20260715-235318`/`235322`; and the active reviewer log ends in `20260715-235313`. Twelve positive/one negative diagnostics bring the catalog to 1,261 checks across 39 areas; the reviewer example has eight positive/one negative statement. Six semantic definitions add no rule or `unif_rule`; warnings and audit remain 978/157 and zero/45/27. The active source is byte-identical to the owner snapshot, health checks all 22 files, and the open-centre negative preserves proof relevance. The synchronized CI gate passes in 127.18s. |
| Originally `tmp/probes/oetu_trunc_evidence_prop_owner_full.lp` plus `tmp/probes/oetu_trunc_evidence_prop_owner_checks_full.lp`, the focused `oetu_trunc_evidence_prop_{base,pi,classifier,successor,recursor_decl,recursor_type,recursor_base_compute,recursive_owner}.lp` probes, and `examples/truncation_evidence_property.lp` | Phase 11 property-valued truncation evidence. The Sigma base transports contraction functions along centre paths and applies PiFunext pointwise; `is_contr_pi` and `is_prop_pi` supply the recursive closure. The generated-recursion declaration, generic type, and base computation pass, but both applied and head-only successor conversions exceed 60s. The selected stable theorem head owns two disjoint classifier-consumer equations instead. The cumulative full-file pair was carried forward and renamed as the Pi-closure pair below. | **Promoted 2026-07-16.** Final split base/Pi/successor/declaration/type/base-compute logs end in `20260716-001358`/`001254`/`001718`/`001903`/`001921`/`001935`; rejected successor logs end in `20260716-001950`/`002104`; the stable focused warning log ends in `20260716-002237`; full source/check quiet logs end in `20260716-002447`/`002455`, warning logs in `20260716-002512`/`002517`, and the active reviewer log in `20260716-002804`. Sixteen positive/two negative diagnostics bring the catalog to 1,279 checks across 40 areas; the reviewer example has eight positive/two negative statements. Ten symbols and one two-equation rule declaration preserve 978/157 warnings and zero/45/27 audit results. Health checks 23 files; open evidence remains non-convertible. The synchronized CI gate passes in 75.41s. |
| Originally `tmp/probes/oetu_trunc_pi_closure_owner_full.lp` plus `tmp/probes/oetu_trunc_pi_closure_owner_checks_full.lp`, `tmp/probes/oetu_trunc_pi_closure_signature.lp`, and `examples/truncation_pi_closure.lp` | Phase 11 arbitrary-level dependent-Pi closure. The base consumes `is_contr_pi`; the successor recursively truncates the pointwise path family and transports back through `pi_happly_type_equiv`. A stable theorem head owns two disjoint family/evidence-consumer equations, and `is_prop_pi` becomes the readable `-1` alias rather than retaining a duplicate semantic body. The cumulative full-file pair was carried forward and renamed as the Sigma-closure pair below. | **Promoted 2026-07-16.** The focused warning log ends in `20260716-004109`; full source/check quiet logs end in `20260716-004239`/`004242`, warning logs in `20260716-004251`/`004254`, the scratch reviewer log in `20260716-004330`, and the active reviewer log in `20260716-004456`. Ten positive/one negative diagnostics bring the catalog to 1,290 checks across 41 areas; the reviewer example has eight positive/one negative statement. Three symbols and one two-equation rule declaration preserve 978/157 warnings and zero/45/27 audit results. The active source was byte-identical to that owner snapshot at promotion, health checks 24 files, and open pointwise evidence remains non-convertible. The synchronized CI gate passes in 131.21s. |
| Originally `tmp/probes/oetu_trunc_sigma_closure_owner_full.lp` plus `tmp/probes/oetu_trunc_sigma_closure_owner_checks_full.lp`, `tmp/probes/oetu_trunc_sigma_closure_signature.lp`, and `examples/truncation_sigma_closure.lp` | Phase 11 same-level dependent-Sigma closure. The base pairs contractible centres and contracts the fibre after base-path transport; the successor recursively truncates the existing base-path/fibre-`PathOver` Sigma view from both hypotheses. A stable theorem head owns two disjoint two-hypothesis consumer equations. The cumulative full-file pair was carried forward and renamed as the package-path pair below. | **Promoted 2026-07-16.** Focused base/full signature logs end in `20260716-005951`/`010037`; full source/check quiet logs end in `20260716-010121`/`010214`, warning logs in `20260716-010232`, the scratch reviewer log in `20260716-010332`, and the active reviewer log in `20260716-010520`. Ten positive/two negative diagnostics bring the catalog to 1,302 checks across 42 areas; the reviewer example has eight positive/two negative statements. Four symbols and one two-equation rule declaration preserve 978/157 warnings and zero/45/27 audit results. The active source was byte-identical to that owner snapshot at promotion, health checks 25 files, and both open hypotheses remain non-convertible. The synchronized CI gate passes in 136.09s. |
| Originally `tmp/probes/oetu_trunc_universe_paths_owner_full.lp` plus `tmp/probes/oetu_trunc_universe_paths_owner_checks_full.lp`, `tmp/probes/oetu_trunc_universe_paths_signature.lp`, and `examples/truncation_universe_paths.lp` | Phase 11 carrier/evidence package-path control. A reviewed native-package eliminator supports a named Sigma path view; proposition-valued evidence reconstructs its dependent field, carrier projection and reconstruction have both propositional inverse laws, reflexivity is explicit, and the path classifiers form an ordinary `TypeEquiv`. The cumulative full-file pair was carried forward and renamed as the restricted-univalence pair below. | **Promoted 2026-07-16.** Focused introduction/final-signature logs end in `20260716-012401`/`012935`; full source/check quiet logs end in `20260716-013410`/`013528`, both warning-enabled logs end in `20260716-013542`, the scratch reviewer log ends in `20260716-014036`, and the active reviewer log ends in `20260716-014222`. Fifteen positive/three negative diagnostics bring the catalog to 1,320 checks across 43 areas; the reviewer example has eight positive/three negative statements. Twenty-two semantic symbols and no rule or `unif_rule` preserve 978/157 warnings and zero/45/27 audit results. The active source was byte-identical to that owner snapshot at promotion, health checks 26 files, and all three open cancellation/round-trip controls remain non-convertible. Restricted ambient-univalence composition and the universe-level theorem remain separate. The synchronized CI gate passes in 188.15s. |
| Originally `tmp/probes/oetu_trunc_universe_univalence_owner_full.lp` plus `tmp/probes/oetu_trunc_universe_univalence_owner_checks_full.lp`, `tmp/probes/oetu_trunc_universe_univalence_signature.lp`, and `examples/truncation_universe_univalence.lp` | Phase 11 restricted package univalence. The canonical ambient decoder capability is packaged once as a `TypeEquiv` and composed with carrier-path control; named encoder/decoder maps expose exact selected projections, both propositional round trips, and the asymmetric reflexive boundary. The cumulative full-file pair was carried forward and renamed as the universe-level pair below. | **Promoted 2026-07-16.** The focused signature log ends in `20260716-015839`; full source/check quiet logs end in `20260716-015927`/`020027`, warning-enabled logs end in `20260716-020042`/`020054`, the scratch reviewer log ends in `20260716-020146`, and the active reviewer log ends in `20260716-020326`. Twelve positive/three negative diagnostics bring the catalog to 1,335 checks across 44 areas; the reviewer example has eight positive/three negative statements. Seven semantic symbols and no rule or `unif_rule` preserve 978/157 warnings and zero/45/27 audit results. The active source was byte-identical to that owner snapshot at promotion, health checks 27 files, and both open round trips plus inverse reflexivity remain non-convertible. Direct observational universe identity and the universe-level theorem remain separate at this gate. The follow-up explicit-inverse contractible-base probe passes in `20260716-021050`; synchronized CI passes in 282.49s. |
| Originally `tmp/probes/oetu_trunc_universe_level_owner_full.lp` plus `tmp/probes/oetu_trunc_universe_level_owner_checks_full.lp`, `tmp/probes/oetu_trunc_universe_level_{base,signature}.lp`, and `examples/truncation_universe_level.lp` | Phase 11 expected package-universe level. The contractible base gives every map an explicit constant inverse, proves equivalence evidence proposition-valued/contractible, and closes `TypeEquiv` by Pi/Sigma; the successor uses target truncation plus proposition lifting. A stable two-branch owner feeds restricted package univalence to prove `IsTruncGrpd(succ n,TruncGrpdU(n))`. The cumulative full-file pair was subsequently carried forward and renamed as the Product-reflexivity pair below. | **Promoted 2026-07-16.** The selected base/signature logs end in `20260716-021050`/`022644`; full source/check quiet logs end in `20260716-022804`/`022931`, warning-enabled logs end in `20260716-022949`/`023006`, and the active reviewer log ends in `20260716-023339`. Seventeen positive/three negative diagnostics bring the catalog to 1,355 checks across 45 areas; the reviewer example has eleven positive/three negative statements. Ten semantic symbols and one two-equation rule declaration preserve 978/157 warnings and zero/45/27 audit results. The active source was byte-identical to the owner snapshot at promotion; health checks 28 files with a 17,735-line/731-symbol/572-rule/51-unification-rule kernel and 1,271 positive diagnostics. Source evidence is intentionally erased only by the successor branch, while base source and successor target evidence remain observable; no same-level universe claim, direct universe identity, or proof erasure is installed. Synchronized 28-file CI passes in 155.30s. |
| Product cumulative owner/check snapshots, originally `tmp/probes/oetu_product_diamond_owner_full.lp` plus `tmp/probes/oetu_product_diamond_owner_checks_full.lp`, and `examples/product_reflexivity_provenance.lp` | Product reflexivity provenance at the actual ordinary-iso and fixed-map omega owners. The candidate removes exactly two collapse rules, retains componentwise evidence through recursive cells and decoders, checks the remaining inverse-arrow join with generic Product identity, and records the non-collapse boundaries. After promotion the cumulative pair was carried forward and renamed as the Boolean pair below; the dated Product logs remain exact evidence. | **Promoted 2026-07-16.** Quiet source/check logs end in `20260716-025427`/`030307`; warning-enabled logs end in `20260716-030323`/`030715`; the focused reviewer log ends in `20260716-031113`. Eleven scoped Product diagnostics plus adjacent encoder controls bring the catalog to 1,360 checks across 46 areas; the reviewer example has nine positive/five negative statements. Two rule declarations are removed and no rewrite or `unif_rule` is added, improving warnings from 978/157 to 972/157 while preserving zero/45/27 audit results. Health checks 29 files with a 17,714-line/731-symbol/570-rule/51-unification-rule kernel and 1,271 positive diagnostics. Synchronized 29-file CI passes in 189.90s. |
| Boolean cumulative owner/check snapshots, originally `tmp/probes/oetu_obs_bool_owner_full.lp` plus `tmp/probes/oetu_obs_bool_owner_checks_full.lp`, and `examples/boolean_observational_equality.lp` | The first elementary observational identity owner: four visible Boolean constructor classifiers, retained generic reflexivity provenance, generic literal-reflexivity consumers, raw-`tt` runtime/proof-time boundaries, and open-endpoint controls. An earlier version of the same pair probed `eq_refl -> tt` plus a closed J/PathSym/Core/unit/encoder registry. After promotion the cumulative pair was carried forward and renamed as the Unit pair below; the dated Boolean logs remain exact evidence. | **Promoted 2026-07-16.** The rejected collapse version passes quietly in source/check logs ending `20260716-033031`/`033238` but its warning-enabled logs ending `20260716-033254` add 42 unjoinable reports, decomposed as 14 literal-reflexivity consumer, 12 PathSym higher-owner, and 16 Core reports. The selected classifier-only source/check probes pass quietly in logs ending `20260716-034236`/`034410` and warning-enabled in `20260716-034258`/`034311`, preserving 972/157 and zero/45/27 audit results. Twenty-two positive/eleven negative diagnostics bring the catalog to 1,393 checks across 47 areas; the focused reviewer log ends in `20260716-034631` with eleven positive/six negative statements. No reflexivity collapse, registry rule, or `unif_rule` is added. Health checks 30 files with a 17,728-line/731-symbol/571-rule/51-unification-rule kernel and 1,293 positive diagnostics. Synchronized 30-file CI passes in 143.199s. |
| Originally `tmp/probes/oetu_obs_unit_owner_full.lp` plus `tmp/probes/oetu_obs_unit_owner_checks_full.lp`, and `examples/unit_observational_equality.lp` | The second elementary observational identity owner: `tt = tt -> Unit_grpd`, retained generic reflexivity, generic literal-reflexivity consumers, raw-`tt` runtime/proof-time boundaries, and open-unit controls. The full-file pair was the cumulative continuation of the Boolean owner and was carried forward/renamed as the Nat pair below. | **Promoted 2026-07-16.** Quiet source/check logs end in `20260716-040227`/`040238`; warning-enabled logs end in `20260716-040248`/`040259`; the focused reviewer log ends in `20260716-040444`. Ten positive/nine negative diagnostics bring the catalog to 1,412 checks across 48 areas; the reviewer example has seven positive/six negative statements. One classifier equation and no registry or `unif_rule` preserve 972/157 warnings and zero/45/27 audit results. Health checks 31 files with a 17,737-line/731-symbol/572-rule/51-unification-rule kernel and 1,303 positive diagnostics. Synchronized 31-file CI passes in 153.385s. |
| Originally `tmp/probes/oetu_obs_nat_owner_full.lp` plus `tmp/probes/oetu_obs_nat_owner_checks_full.lp`, `tmp/probes/oetu_obs_nat_j_subject_reduction.lp`, and `examples/nat_observational_equality.lp` | The first recursive elementary observational identity owner and its generic-J prerequisite. Four Nat classifier equations preserve outer proof provenance. The rejected unguarded candidate exposes a proof-dependent ill-typed J normal form; the selected rule repeats category/endpoint guards and checks foreign/predecessor reflexivity boundaries. The cumulative full-file pair was carried forward/renamed as the sum pair below; dated Nat logs remain exact evidence. | **Completed/promoted (2026-07-16).** Rejected quiet source/check logs end in `20260716-041943`/`042647`, rejected warning logs in `20260716-042708`, and the subject-reduction log in `20260716-043035`. Selected guarded quiet source/check logs end in `20260716-043247`/`043414`, warning logs in `20260716-043427`/`043428`, and the reviewer log in `20260716-043749`. Twenty-three positive/eleven negative Nat checks plus four guard negatives bring the catalog to 1,450 checks across 50 areas; the reviewer has eleven positive/eight negative statements. One four-clause classifier declaration and the guarded existing J rule add no `unif_rule`, improve warnings to 971/157, preserve zero/45/27 audit, and produce a 32-file health snapshot with a 17,753-line/731-symbol/573-rule/51-unification-rule kernel and 1,326 positive diagnostics. Synchronized 32-file CI passes in 151.336s. |
| `tmp/probes/oetu_obs_sum_owner_full.lp` plus `tmp/probes/oetu_obs_sum_owner_checks_full.lp`, `tmp/probes/oetu_obs_sum_j_subject_reduction.lp`, and `examples/sum_observational_equality.lp` | The parameterized general-sum observational identity owner. Four tag-directed equations recurse to component equality or Empty, outer proof provenance is retained, the generic-J guard is revalidated by a component-indexed motive, and six reconstructible constructor indices are minimized. | **Completed/promoted (2026-07-16).** Initial quiet source/check logs end in `20260716-045922`/`045931`; complete diagnostics pass in `20260716-050156`; pre-minimization warning logs end in `20260716-050248`. Final minimized quiet and warning log pairs end in `20260716-050336` and `050351`; the subject-reduction and reviewer logs end in `20260716-050426` and `050744`. Twenty-four positive/eleven negative diagnostics bring the catalog to 1,485 checks across 51 areas; the reviewer has twelve positive/eight negative statements. One four-clause rule declaration and no registry or `unif_rule` preserve 971/157 warnings and zero/45/27 audit. Health checks 33 files with a 17,777-line/731-symbol/574-rule/51-unification-rule kernel and 1,350 positive diagnostics. Synchronized CI passes with 161.044s of measured checking time (167.96s wall time). |
| `tmp/probes/oetu_universe_equality_direct_owner_full.lp` plus its full checks, direct signature/self-compute controls, `tmp/probes/oetu_universe_equality_view_owner_full.lp` plus its full checks/self-compute/reviewer probes, and `examples/groupoid_universe_identity_view.lp` | The first Phase-13 groupoid-universe owner comparison. Direct public equality is tried at the actual canonical owner; the selected fallback names the existing `TypeEquiv` view, decoder-owned maps, round trips, transport theorem, and Product/Pi/Sigma consumers without copying bodies. | **Completed/promoted (2026-07-16).** The pre-decoder placement failure ends in `20260716-053144`; direct quiet source/check logs end in `20260716-053346`/`055048`, and warning logs in `20260716-053345`/`053447`. The reducible-alias spelling has 972/157 warnings; canonical `(Obj Grpd_cat)` restores 971/157. Direct self-universe normalization times out in `20260716-053636`, while baseline/standalone controls end in `20260716-053720`. Selected view quiet source/check logs end in `20260716-053946`/`054135`, warning logs in `20260716-054151`/`054233`, finite self-view normalization in `20260716-054151`, and the active reviewer in `20260716-054558`. Seventeen positive/seven negative diagnostics bring the catalog to 1,509 checks across 52 areas; the reviewer has fourteen positive/five negative statements. Seven semantic aliases, no rule, and no `unif_rule` preserve 971/157 and zero/45/27. Health checks 34 files with a 17,838-line/738-symbol/574-rule/51-unification-rule kernel and 1,367 positive diagnostics. Synchronized CI passes with 182.160s measured checking time (189.18s wall time). |
| `tmp/probes/oetu_universe_equality_cat_direct_owner_full.lp` plus its full checks, signature/self-compute controls, alias and shaped-reflexivity comparisons, `tmp/probes/oetu_universe_equality_cat_selected_owner_full.lp` plus its full checks/self-compute/reviewer probes, and `examples/categorical_universe_identity.lp` | The categorical Phase-13 owner comparison. It tests direct equality at the canonical post-`OmegaEquiv` owner, the reducible `Cat_grpd` spelling, global reflexivity collapse, finite self-universe normalization, decoder-owned maps/round trips, Product action, and a direct D0b next-hom consumer. | **Completed/promoted (2026-07-16).** Initial direct quiet source/check logs end in `20260716-060812`/`060824`, focused signature in `060849`, self-universe normalization in `060824`, and canonical warning logs in `060935` at 971/157. The alias spelling records 972/157 in `061218`. The rejected reflexivity collapse fails the inherited object-path action check in `061303` and records 974/157 in `061331`. Selected source/check quiet logs end in `061546`/`061859`, warning logs in `061725`, finite self/Product and scratch-reviewer logs in `061859`, and the active reviewer in `062228`. Twenty-two positive/eight negative diagnostics and a fifteen-positive/six-negative reviewer are active. Twelve symbols, one classifier rule, and no `unif_rule` preserve zero/45/27 audit. The catalog has 1,539 checks across 53 areas; health checks 35 files with a 17,989-line/750-symbol/575-rule/51-unification-rule kernel and 1,389 positive diagnostics. Synchronized CI passes with 165.477s measured checking time (171.88s wall time). |
| `tmp/probes/oetu_omega_equiv_evidence_view_owner_full.lp` plus its full checks, signature and finite self-compute controls, `tmp/probes/oetu_omega_equiv_evidence_direct_owner_full.lp`, its warning rerun and append-only self-compute control, `tmp/probes/oetu_omega_equiv_evidence_view_reviewer.lp`, and `examples/omega_equiv_evidence_view.lp` | The native fixed-arrow certificate-bisimulation comparison. It packages the four existing D0 observations into a nested Sigma/Product record, compares its finite path view with direct recursive certificate equality, and exercises reflexivity, one-way path action, and D0b next-hom observation. | **Completed/promoted (2026-07-16).** Finite source/signature/inherited-check logs end in `20260716-093253`/`093344`/`093545`; warning-enabled source/check logs end in `093558`/`094030` at 971/157; strict audit is zero/45/27; and finite self-view normalization ends in `093726`. The direct owner source exceeds 30 seconds in `093406`, its warning-enabled rerun exceeds 20 seconds in `093504`, and its append-only self-universe control exceeds 20 seconds in `093654`. The scratch/active reviewer logs end in `094135`/`094320`. Thirteen positive/three negative diagnostics and ten positive/three negative reviewer statements are active. Five symbols, no rule, and no `unif_rule` are added. The catalog has 1,555 checks across 54 areas; health checks 36 files with an 18,104-line/755-symbol/575-rule/51-unification-rule kernel and 1,402 positive diagnostics. Full examples pass, and synchronized CI records 186.423s measured checking time (193.35s wall time). |
| `tmp/probes/oetu_ncat_obj_trunc_conditional_owner_full.lp`, its inherited checks and focused signature, `tmp/probes/oetu_ncat_obj_trunc_conditional_reviewer.lp`, and `examples/ncat_object_truncation_conditional.lp` | The conditional Phase-9 theorem split at the actual `IsNCat` owner. It names the missing global certificate-property premise, lifts propositions to native dimensions, and checks the zero/successor proof spine through Sigma closure and categorical univalence, including `ZeroCat`/`OneCat` consumers and typed proof-time non-erasure. | **Completed/promoted (2026-07-16).** Quiet owner/signature/check logs end in `20260716-101016`/`101323`/`101446`; warning-enabled owner/check logs end in `101349`/`101510` at 971/157; strict audit remains zero/45/27; scratch/active reviewer logs end in `101606`/`101743`. Eleven positive/four negative diagnostics and eight positive/four negative reviewer statements are active. The two two-equation recursive heads add no `unif_rule`. The catalog has 1,570 checks across 55 areas; health checks 37 files with an 18,173-line/758-symbol/577-rule/51-unification-rule kernel and 1,413 positive diagnostics. Full examples pass, and synchronized CI records 198.816s measured checking time (206.34s wall time). |
| `tmp/probes/oetu_omega_equiv_evidence_dim_view_owner_full.lp`, its inherited checks and focused signature, `tmp/probes/oetu_omega_equiv_evidence_dim_view_reviewer.lp`, and `examples/omega_equiv_evidence_dim_view.lp` | The recursion-safe fixed-arrow certificate representation probe at the actual `IsNCat` owner. Its explicit CatDim recursion is Unit at zero and at successor stores both inverse arrows plus first-class recursive observations of both D0 cell packages in the smaller-dimensional hom-categories. It checks every projection ladder, ZeroCat/OneCat termination, finite path reflexivity/action, and runtime/proof-time separation from public evidence equality. | **Completed/promoted (2026-07-16).** Quiet owner/signature/check logs end in `20260716-104217`/`104520`/`104613`; warning-enabled source/check logs end in `104636` at 971/157; strict audit remains zero/45/27; scratch/active reviewer logs end in `104802`/`104928`. Seventeen positive/five negative diagnostics and twelve positive/four negative reviewer statements are active. Six symbols and two two-equation rule families add no `unif_rule`. The catalog has 1,592 checks across 56 areas; health checks 38 files with an 18,452-line/764-symbol/579-rule/51-unification-rule kernel and 1,430 positive diagnostics. Full examples and synchronized CI pass with 201.708s measured checking time (212.59s wall time). No reverse decoder, eta, public equality, or evidence-property inhabitant is inferred. |
| `tmp/probes/oetu_onecat_iso_owner_full.lp`, `tmp/probes/oetu_onecat_iso_owner_checks_full.lp`, `tmp/probes/oetu_onecat_iso_signature.lp`, `tmp/probes/oetu_onecat_iso_reverse_missing.lp`, and `examples/onecat_iso_lift.lp` | The dimension-correct ordinary-iso replacement probe at the D0, categorical-decoder, and `OneCat` owners. It constructs recursive fixed-arrow evidence from both ordinary inverse laws, compares backed reflexive evidence with canonical D0 reflexivity at proof time, proves encoder agreement by generic J, and derives the scoped decoder and first round trip. The deliberate reverse probe isolates the distinct-left/right-inverse endpoint mismatch. | **One-sided prerequisite completed/promoted (2026-07-16); full capability was prerequisite-blocked at this checkpoint and is discharged by the later rows.** Quiet owner/check/signature/reviewer logs end in `20260716-120633`/`120824`/`121149`/`121326`; warning logs end in `120226`/`120834` at 971/157; the exact reverse mismatch is recorded in `120542` and the deliberate failure in `120916`. Twelve positive/six negative diagnostics and nine positive/four negative reviewer statements bring the catalog to 1,637 checks across 58 areas. Five symbols, two two-equation families, and one semantically backed `unif_rule` preserve zero/45/27 audit. Health measures 40 files with a 19,062-line/782-symbol/581-rule/56-unification-rule kernel and 1,463 positive diagnostics. Full examples and synchronized CI pass with 281.823s measured checking time. Do not identify the two inverse arrows; the reverse direction needs a constructed directed comparison, discrete-hom path, transported law, and nested-Sigma extensionality. |
| The cumulative `tmp/probes/oetu_onecat_iso_owner_full.lp` and `tmp/probes/oetu_onecat_iso_owner_checks_full.lp` inverse-comparison continuation, plus `examples/onecat_iso_lift.lp` | The distinct-left/right-inverse prerequisite at its D0 and OneCat owners. It exposes both recursive cell arrows, compares the rejected raw `Hom_func` composite with stable post/pre whiskering, inserts an explicit propositional associator, composes the generic directed inverse comparison, and decodes it through OneCat hom discreteness. | **Completed/promoted with synchronized CI (2026-07-16).** The direct composite fails at two unit presentations and associativity in `20260716-123757`; the selected quiet owner log ends in `124247`, owner warning log in `125119`, inherited quiet/warning checks in `125136`/`125140`, and reviewer in `124544`. Nine positive/four negative diagnostics and six positive/three negative reviewer additions bring the catalog to 1,650 checks across 59 areas and the reviewer to fifteen positive/seven negative statements. Eight symbols, no rule, and no `unif_rule` preserve 971/157 warnings and zero/45/27 audit. Health measures 40 files with a 19,373-line/790-symbol/581-rule/56-unification-rule kernel and 1,472 positive diagnostics; full examples and synchronized CI pass with 139.872s measured checking time. Canonical comparison computes to the identity 2-cell, while its decoded path remains non-runtime `eq_refl`. The completed transport/round-trip row below consumes this result. |
| The same cumulative OneCat owner/check pair after right-law transport, nested-Sigma reconstruction, and scoped-capability packaging, plus `tmp/probes/oetu_set_path_probe.lp` and the expanded `examples/onecat_iso_lift.lp` | The complete OneCat-scoped replacement. It decodes both recursive laws, transports the right law to the selected left inverse, reconstructs ordinary evidence, uses hom discreteness to compare both proof fields, proves lift/reconstruction equality through the existing nested-Sigma path owner, derives the second round trip, and packages a OneCat-indexed specified inverse, contractible-fibre capability, and named `TypeEquiv`. The rejected global-classifier attempt demonstrates that the legacy decoder cannot be reused by renaming. | **Completed/promoted with synchronized CI (2026-07-16).** The small discrete-path probe passes at `132315`; the complete definition candidate passes at `132729`; the rejected global `CatIsoUnivalenceByDecoder` package fails with its hardcoded decoder at `132624`. Final focused owner quiet/warning logs end in `133706`/`133718`, inherited-suite logs in `133745`/`133751`, and reviewer in `134212`. Ten semantic symbols, no rewrite, and no `unif_rule` preserve 971/157 warnings and zero/45/27 audit. Thirteen positive/two negative diagnostics bring the catalog to 1,678 checks across 61 areas, and the reviewer has 32 positive/12 negative statements. Health passes across 40 files with a 19,883-line/804-symbol/581-rule/56-unification-rule kernel and 1,495 positive diagnostics; full examples pass. Synchronized CI records 109.546s measured checking time. |
| `tmp/probes/oetu_nat_succ_action_owner_full.lp`, `tmp/probes/oetu_nat_succ_action_owner_checks_full.lp`, and `examples/nat_observational_action.lp` | The first recursive-inductive registered-action owner. Nat successor equality exposes the predecessor path, while component and outer generic reflexivity remain distinct. One stable basis has a direct typed proof-time comparison with each form; generic J composes the resulting internal paths, and the selected `ObsAction(succ)` computes as `p |-> p`. | **Completed/promoted with synchronized CI (2026-07-16).** Quiet owner/check logs end in `141904`/`142047`, warning logs in `142057`/`142329`, and the active reviewer in `142721`. Fourteen positive/five negative diagnostics and eleven positive/five negative reviewer statements are active. Seven symbols and two semantically justified `unif_rule`s add no runtime rewrite, preserve 971/157 warnings and zero/45/27 audit counts, and yield 1,694 checks/62 areas. Health passes across 41 files at 19,988 kernel lines/808 symbols/581 rules/58 unification rules with 1,507 positives; full examples and synchronized CI pass in 220.269s. Runtime proof collapse, proof-time transitivity, successor-specific J, and canonicity remain excluded. |
| `tmp/probes/oetu_discrete_cat_contract.lp` | Earlier append-only evidence for the selected Product boundary, exact `Cat_cat` indexing, core hom-action type, and `path_to_hom` object projection. | **Superseded/fulfilled by the promoted owner-position discrete pair.** The append-only file supplied no homwise inhabitant; the active implementation now constructs it from projected D0b evidence and supplies both coherent directions. |
| `tmp/probes/oetu_indexed_structure_architecture_probe.lp` | Primary fixed-map evidence plus Sigma packaging, indexed `Adjunction(F,G)`, both exact triangle patterns, transparent versus proof-time functor views, fixed-arrow higher cells, and the mechanics of typed named-unit/counit comparison under per-instance proof-time equations. | Move candidates to owner positions, minimize/annotate its eight scratch-local replaceable-pattern-variable advisories, and migrate active opposite/mate/decoder consumers. Its independently declared `ReviewNamedAdj`, unit, and counit do not semantically justify their own `unif_rule`s; promotion must bind the names through declaration data/fields or classify the generated equations as trusted declaration postulates. |
| `tmp/probes/oetu_adjunction_named_unit_runtime_probe.lp` | Negative control: runtime unit/counit projection betas erase the stable triangle discriminators, leaving both the projected and raw named-operation spellings stuck as expected. | Preserve stable unit/counit observations or design a different audited triangle owner; clean its two scratch-local LHS advisories before reusing a pattern. |
| `tmp/probes/oetu_hott_elementary_formers.lp` | Decoded Empty, Bool, and Nat classifiers; dependent eliminator facades; Bool and Nat constructor beta. | Promote at the foundations owner with active diagnostics; identity/no-confusion, higher action, canonicity, and categorical universal properties remain separate. |
| `tmp/probes/oetu_elementary_hott_owner_full.lp` plus `tmp/probes/oetu_elementary_hott_owner_checks_full.lp` | Candidate G at its active foundations owner, with decoded signatures, generated eliminator bodies, the complete retargeted active suite, constructor betas, and Bool non-collapse. | **Promoted 2026-07-15.** Retain these ignored files as owner-position evidence; all excluded observational, canonicity, sum, and categorical obligations remain separately statused. |
| `tmp/probes/oetu_hott_pi_adequacy.lp` | Standard diagonal `happly`, transparent `funext` with related-input action, judgmental beta, non-judgmental arbitrary eta, and conversion of the unfolded reflexive reverse composite to `eq_refl`. This independently motivates the stable-head reflexive law. | Select stable public owners, verify that their proof-time equation faithfully preserves this transparent computation, and construct the actual `IsEquivMap(PiHapply)` evidence rather than citing beta/eta sketches. |
| `tmp/probes/oetu_hott_pi_stable_funext.lp` | Stable `PiHapply`/`PiFunext` heads, related-input action, a two-rigid-head selected proof-time reflexive equation, and—conditional on that equation—propositional eta via generic `ind_eqr`. | Reprobe at owner position, retain the explicit hybrid generic-`J` contract, justify or explicitly select the reflexive equation as a trusted structural proof-time law, and package the active equivalence; fibrancy is required only for additional structural computation, not for this conditional generic-J eta proof. |
| `tmp/probes/oetu_unif_trust_boundary_probe.lp` | Adversarial negative control: an intentionally unjustified rule equates two unrelated rigid heads at proof time; runtime conversion remains negative, while typed `eq_refl` constructs their cross-head equality. This isolates firing from semantic validation. | Never promote the arbitrary rule. Retain the probe as methodological evidence that every real `unif_rule` needs a recorded semantic trust class and that typed `eq_refl` is an operational regression test, not independent foundational evidence. |
| `tmp/probes/oetu_path_oriented_owner_probe.lp` | The existing postcomposition and precomposition point heads give distinct oriented runtime presentations of path composition, each can receive both narrow `eq_refl` unit bridges, and their existing direct `unif_rule` supplies typed proof-time comparison. | Append-only action-owner evidence only. Its four replaceable-variable advisories and one local overlap with postcomposition accumulation must be cleaned/classified; it does not select either action head as the category-level composition normal form. |
| `tmp/probes/oetu_path_shared_comp_owner_full.lp` plus `tmp/probes/oetu_path_shared_comp_owner_checks_full.lp` | Owner-position E0 composition candidate: generic `comp_fapp0` remains the `Path_cat` composition head, two `eq_refl` projection-order unit bridges are added, J-derived comparison with `eq_trans` is propositional, and the entire migrated active check suite passes warning-enabled. | Promote only together with removal of the old `comp_fapp0(Path_cat)->eq_trans` fold and durable agreement/unit/associativity checks. This artifact deliberately retains the self-opposite collapse and therefore supplies no E1 evidence. |
| `tmp/probes/oetu_path_symmetry_removal_full.lp` plus `tmp/probes/oetu_path_symmetry_removal_checks_full.lp` | E0 removal-only extension of the shared-composition candidate: deleting `Op_cat(Path_cat(A))->Path_cat(A)` still passes the full source and entire migrated suite warning-enabled, with 1,072 unjoinable-pair reports. | This is a sounder promotion intermediate, not a symmetry implementation. It proves that E0 need not retain the bad collapse while E1 is developed. |
| `tmp/probes/oetu_path_comp_promotion_full.lp` plus `tmp/probes/oetu_path_comp_promotion_checks_full.lp` | Final Phase-3-rebased E0 owner candidate: removes both obsolete folds, adds two SOP-minimal and LHS-annotated category-unit bridges, defines J-derived `path_comp_eq_trans`, retargets `Core_incl_func` composition, and checks generic/projection-first units, associativity, genuine opposite endpoints, typed oriented-action units, and six negative conversion boundaries. Source/suite pass quietly and warning-enabled at 1,072/159 with zero strict-LHS candidates. | **Promoted 2026-07-15.** The four-action-runtime-bridge variant measured 1,077/165, adding five critical pairs and six replaceable-variable advisories; retain the selected two-step typed proof-time witnesses and do not add those bridges without a concrete runtime consumer. |
| `tmp/probes/oetu_path_symmetry_owner_full.lp` plus `tmp/probes/oetu_path_symmetry_owner_checks_full.lp` | Owner-position E1 core: `PathSym_A : Path(A)^op -> Path(A)` fixes objects; its arrow action is the readable `path_sym` owner; a narrow reflexivity bridge computes; generic functoriality supplies anti-composition; J supplies propositional `eq_sym` agreement and involution; and a pointwise `Core_incl_func`/opposite square is proved. The full migrated suite, warning-enabled source/checks, negative conversion controls, and strict LHS audit pass. | The 1,084 inventory contains twelve new reports mentioning `PathSym_A`; classify them with both-order consumers before promotion. Functor-level natural packaging and `OmegaEquivAlong(PathSym_A)` wait for the fixed-map owner rather than being faked through the old opaque package. |
| `tmp/probes/oetu_path_symmetry_promotion_full.lp` plus `tmp/probes/oetu_path_symmetry_promotion_checks_full.lp` | Final E1 owner candidate rebased over E0: adds identity/action and composition/action orders, typed post/pre/naturality pairs, mapped-`DefIso` pre/post-projection consumers, and untyped Product controls. Six generic endpoint guards are minimized after the original spellings fail. Source/suite pass quietly and warning-enabled at 974/159 with zero strict-LHS candidates. | **Promoted 2026-07-15.** Preserve generic functor and mapped-cancellation ownership. Functor-level natural packaging and `OmegaEquivAlong(PathSym_A)` remain separately gated. |
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

The final Candidate G owner-position source/check logs end in
`20260715-154934` and `20260715-154940`. Both are warning-enabled successful
full-file runs; each reports the unchanged 1,109/163 warning inventory and no
elementary-owner warning. The corresponding final quiet logs end in
`20260715-154920` and `20260715-154926`. These candidates, unlike the original
append-only elementary probe, place the declarations at the real foundations
owner and retarget the entire active suite; the matching minimal code and
durable checks are now promoted.

The Candidate A owner-position source/check logs end in
`20260715-160154` and `20260715-160201`; both are warning-enabled successful
full-file runs with the unchanged 1,109/163 inventory and no record-owner
warning. The corresponding quiet logs end in `20260715-160134` and
`20260715-160142`. The check candidate also contains the unpromoted nested-
Sigma comparison. Its source, target, and witness observations compute through
the expected nested projection chains, while the named record exposes direct
projections and generated three-field induction. The active promotion contains
only the named owner and nine durable checks, including the negative runtime-
eta control.

The Candidate B owner-position source/check logs end in
`20260715-161102` and `20260715-161111`; both are warning-enabled successful
full-file runs with the unchanged 1,109/163 inventory and no truncation-owner
warning. The corresponding quiet logs end in `20260715-161037` and
`20260715-161050`. The strict LHS audit remains zero. These candidates exclude
the packaged-universe tail of the earlier combined append-only probe and
validate the generic successor evidence application as well as the base and
readable low-level reductions.

The Phase-3 packaged-universe owner-position quiet logs end in
`20260715-162213` and `20260715-162220`; both warning-enabled logs end in
`20260715-162232`. The source and complete retargeted suite preserve the
1,109/163 inventory, no warning mentions a package owner, and the strict LHS
audit remains zero. Promotion adds eleven positive and three negative checks:
the negative suite preserves evidence fields, leaves runtime package eta open,
and rejects treating an element's evidence as a same-level theorem about the
package universe. Active checks, examples, catalog, TOC, health, and CI pass.

The Candidate-D-relevant `oetu_fixed_map_followup.lp` and
`oetu_indexed_structure_architecture_probe.lp` rows were additionally rerun
warning-enabled on 2026-07-14; those later logs end in `20260714-234358`, and
both files finish checking successfully. The indexed probe still reports its
eight scratch-local replaceable-pattern-variable advisories. These later
passes do not change either artifact's append-only status or supply the absent
D0 recursive-owner computation or D0b variable-evidence hom action.

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
1,072 unjoinable pairs. The final rebased E0 promotion source/check quiet logs
end in `20260715-164934` and `20260715-164939`; warning-enabled logs end in
`20260715-164427` and `20260715-164430` and report 1,072 unjoinable pairs plus
159 replaceable pattern variables. The strict audit reports zero unreviewed
slots. The final E1 symmetry-owner source/check logs end in
`20260715-020314` and `20260715-020507`; both pass,
the source reports 1,084 pairs, exactly twelve warning blocks mention
`Path_sym_func`, the open strict/J-derived and double-symmetry conversions
remain negative as intended, and the strict inferred-LHS audit reports zero
unreviewed candidates. That pair is the pre-classification owner candidate,
not the promoted final source. The E1 promotion probes rebased over E0 are
`tmp/probes/oetu_path_symmetry_promotion_full.lp` and
`tmp/probes/oetu_path_symmetry_promotion_checks_full.lp`; final quiet logs end
in `20260715-170120`/`170345`, and warning-enabled source/check logs end in
`20260715-170137`/`170838`. They report 974 unjoinable pairs plus 159
replaceable variables after the mapped-`DefIso` endpoint refinement. Counts
are warning inventories, not confluence proofs.

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
3. Choose exactly one side-task ID. Use the dependency-ready default named by
   `Current-Implementation-Slice`. The current default is
   `OETU-OBS-NAT-SUCC-ELIM`: probe a former-specific successor-path induction
   facade at the Nat owner. Its public proof index must be successor equality,
   but its implementation must route the already-exposed predecessor path
   through generic `ind_eqr`, giving only component-reflexivity beta. Add no
   rewrite or `unif_rule`, retain outer reflexivity/action-basis negatives, and
   do not infer a general fibrancy package or arbitrary-constructor J.
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

### Completed first implementation slice: Candidate G

Candidate G was selected as the first slice because it closes the
smallest concrete H0 gap, has a passing focused feasibility probe, does not
depend on the unresolved public equality/path owners, and turns the adequacy
benchmark into active foundation code. This selection does not formally adopt
every later migration decision.

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

Candidate G start record (2026-07-15): the tracked worktree was clean, both
the staged and unstaged diffs were empty, and `HEAD` was the supplied
pre-implementation baseline `07a24e6f07c0cd7ecd8147f1fe6158e3af73707d`.
The bounded baseline `EMDASH_TYPECHECK_TIMEOUT=60s make check` passed before
owner-position work began. The active implementation contained native `unit`
and `nat` plus `Unit_grpd`, but no decoded Empty/Bool/Nat classifiers or
reviewed dependent eliminator facades. The existing append-only elementary
probe remains feasibility evidence only; this slice will use a fresh full-file
owner-position candidate and will promote only the exclusions-bounded surface
above.

Candidate G completion record (2026-07-15): the owner-position candidates
`tmp/probes/oetu_elementary_hott_owner_full.lp` and
`tmp/probes/oetu_elementary_hott_owner_checks_full.lp` passed the complete
source and retargeted diagnostic suite both quietly and warning-enabled. The
public eliminator signatures retain the decoded classifiers (`τ Empty_grpd`,
`τ Bool_grpd`, and `τ Nat_grpd`) rather than exposing only raw carrier names;
their bodies route through `ind_empty`, `ind_bool`, and `ind_nat`. Promotion
added 16 positive assertions and one explicit Bool conversion-level negative
control. The warning inventory remained 1,109 critical-pair reports plus 163
replaceable-pattern advisories, the strict LHS audit remained zero, and
bounded checks, examples, catalog classification, TOC, health, and CI passed.
No new `unif_rule` or manual constructor rewrite was needed. The exclusions
above remain separate ledger obligations.

Candidates G/A/B/C/H, the packaged truncated universes, the E0/E1 path
owners, `OETU-STRUCTURAL-PATH-COMPAT`, `OETU-TYPE-EQUIV-ALGEBRA`, and
`OETU-GRPD-UNIV-DECODER` are promoted. Candidates D0, D0b, and D1 under
`OETU-OMEGA-EQUIV-ALONG` are also promoted; D1 jointly completes
`OETU-CAT-UNIV-DECODER`. Phase 8's indexed-adjunction owner migration and
Phase 9's core-inclusion/discreteness gate are promoted; recursive directed-
dimension formation, its index bridge, both general/categorical truncation-
invariance subgates, general monotonicity, and evidence property-valuedness
are promoted. General dependent-Pi truncation closure is also promoted;
same-level dependent-Sigma closure is promoted as well. The opaque recursive-
evidence prerequisite is recorded, truncated-universe package paths are
promoted, restricted canonical ambient-univalence composition is promoted,
and the expected package-universe truncation theorem is promoted. Product
reflexivity-provenance cleanup is the current bounded slice.

### Global roadmap and dependency outline

The numbered phases below remain the detailed global migration order. The
following lanes make the intended dependency structure explicit; plan details
may be revised when owner-position evidence changes a boundary.

```text
Immediate H0 bootstrap
  Candidate G: Empty / Bool / Nat decoding and eliminator beta [promoted 2026-07-15]

Reusable property/structure infrastructure
  Candidate A: record convention [promoted 2026-07-15] ─┐
  Candidate B: truncation kernel [promoted 2026-07-15] ─┴─> packaged truncated universes [promoted 2026-07-15]
        ─> TypeEquiv invariance of IsTruncGrpd [promoted 2026-07-15]
        ─> fixed-map categorical object invariance [promoted 2026-07-15]
        ─> general truncation monotonicity [promoted 2026-07-15]
        ─> truncation-evidence property-valuedness [promoted 2026-07-16]
        ─> general dependent-Pi closure [promoted 2026-07-16]
        ─> same-level dependent-Sigma closure [promoted 2026-07-16]
        ─> recursive evidence truncation [blocked on certificate representation]
        ─> TruncGrpdU carrier/evidence path control [promoted 2026-07-16]
        ─> restricted ambient-univalence composition [promoted 2026-07-16]
        ─> package-universe truncation [promoted 2026-07-16]

Ordinary HoTT compatibility
  Candidate H: Pi happly/funext equivalence under generic J [promoted 2026-07-15]
        + selected, semantically justified reflexive proof-time basis [promoted]
        + Sigma/record arbitrary path round trips [promoted 2026-07-15]
        + TypeEquiv algebra [promoted 2026-07-15]
        + groupoid decoder round trips and transport/action squares [promoted 2026-07-15]
        ───────────────────────────────────────────────────────> H1 MVP

Public observational equality and path algebra
  Candidate E0: shared comp_fapp0 Path_cat owner + collapse removal [promoted 2026-07-15]
        ─> Candidate E1: PathSym functor/action + propositional coherence [promoted 2026-07-15]
        ─> Candidate C: public shaped reflexivity/reflexive J [promoted 2026-07-15]
        ─> structural action [promoted 2026-07-15]
        ─> fibrancy/dependent J [prerequisite: sound capability + selected beta]
        ─> former-by-former migration

Independent H0 completion/extensions
  Candidate G: Empty / Bool / Nat [promoted 2026-07-15]
        ─> general binary sum [promoted 2026-07-15]
        ─> per-former observational identity/no-confusion/higher action [separate]

Omega/category extension
  record/equality owners
        ─> Candidate D0: fixed-map owner + Sigma package + refl/next-hom gate [promoted 2026-07-15]
  promoted D0
        ─> Candidate D0b: variable-evidence Cat hom-action gate [promoted 2026-07-15]
  categorical decoder contract + promoted D0b
        ─> Candidate D1 + categorical decoder finalization [promoted 2026-07-15]:
           op/Product + public decoder migration + integrated witness
  promoted D0b/D1 fixed-map owner
        ─> exact IsDiscreteCat Product + core-hom adequacy [promoted 2026-07-15]
        ─> IsNCat / ZeroCat / OneCat [promoted 2026-07-15]
        ─> one-next-hom Omega0 univalence/action witness
  promoted E1 symmetry core + Candidate D1 fixed-map owner
        ─> PathSym/Core fixed-map packages only when a separate concrete consumer selects them

Separate category migration lane
  promoted Candidate F: indexed Adjunction(F,G), stable unit/counit, triangles/opposite/mates

Later higher layer
  truncation reflectors ─> representative HITs ─> optional H2 completion
  computational universe identity ─> eventual full-observational endpoint
  stratified universes / Cat_cat:Cat metatheory remain a separate deferred research phase
```

Candidate H, `OETU-STRUCTURAL-PATH-COMPAT`, `OETU-TYPE-EQUIV-ALGEBRA`, and
`OETU-GRPD-UNIV-DECODER` are promoted, as are Candidates D0/D0b/D1 under
`OETU-OMEGA-EQUIV-ALONG`; D1 jointly completes categorical decoder validation.
Candidate F/Phase 8, both Phase 9 formation subgates, the dimension-to-
truncation index, registered structural action, and the independent general
binary sum are promoted. General `TypeEquiv` invariance of `IsTruncGrpd` and
its fixed-map categorical object consumer, general truncation monotonicity,
evidence property-valuedness, and general dependent-Pi truncation closure are
also promoted; same-level dependent-Sigma closure is promoted too. Recursive
fixed-arrow evidence truncation needs a certificate representation, so
truncated-universe carrier/evidence path control proceeds independently and
is now promoted. Restricted canonical ambient-univalence composition and the
expected `(n+1)` package-universe truncation theorem are now promoted too. The
latter uses an explicit-inverse contractible base, successor
Pi/Sigma/property closure, and restricted package univalence. Product
reflexivity-provenance cleanup is promoted too: the componentwise constructors
now remain visible at reflexivity and the warning inventory improves by six
critical-pair reports. Visible-constructor Boolean observational equality is
also promoted by the warning-neutral classifier-only owner, with generic
reflexivity provenance retained. The matching Unit case is promoted under the
same policy. Recursive visible-constructor Nat equality and the generic-J
subject-reduction guard revealed by its proof-dependent probe are promoted
too; final Nat CI closeout precedes the separately bounded general-sum owner.
D0b is not a prerequisite for the already promoted
A/B/E0/E1/C/H/structural-path slices. “Immediately available”
does not bypass the listed promotion dependencies, and the promoted adjunction
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

## Decisions Accepted For This Master Plan

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
13. **Adjunction is an indexed relation in the active architecture.** Rather
    than retain a permanent `AdjunctionAlong(F,G)` facade, active `Adjunction`
    is indexed by the already-named left and right functors. An existential
    first-class package may be derived separately only when a consumer truly
    does not know the functors.
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
    indexed triangle patterns are active after owner-position probing; they
    use `F` and `G` as consistently repeated parameters, never as rewrite
    heads.
16. **Preselected adjunction operations require explicit proof-time backing.**
    A future declaration that explicitly binds
    `myAdj : Adjunction(myF,myG)` to a named `myUnit`/`myCounit` may generate
    narrow, typed `unif_rule`s as trusted declaration equations. Alternatively,
    explicit agreement fields/paths may back the comparison. Phase 8 found no
    such active declaration and therefore promoted no equation. Independently
    declared constants are not made mathematically related merely by checking
    a typed `eq_refl`; that check only confirms that a selected rule fires. Runtime
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
    from the outset.** The global `cat_iso_univalence` declarations are
    retired after the scoped replacement; no new redesign owner or theorem may
    restore them for arbitrary `Cat`. Global new work uses
    `CatUnivalence`/`OmegaEquiv`, and ordinary `IsoEvidence` univalence is
    introduced only for `OneCat` or an explicit ordinary-dimensional
    hypothesis.
25. **Fixed-map omega-equivalence remains evidence until property-valuedness is
    proved.** `OmegaEquivAlong(F)` is the neutral primary name. It may be
    described operationally as a certificate/evidence package; the
    `IsOmegaEquivArrow(F)` alias and proof-field erasure are reserved for the
    theorem that its recursive coherence makes it property-like. The completed
    promotion order is D0 -> D0b -> D1: the recursive owner computes, the
    variable-evidence Cat hom action is constructible, and the public
    `OmegaEquiv` normal form is now migrated without claiming proof erasure.
26. **Decoder ownership is split by layer and kept separate from equivalence
    algebra.** Groupoid decoder normalization, both groupoid round trips, and
    the `coe_grpd` action square complete independently. The categorical
    decoder's public type, round trips, and `path_to_hom` squares are now
    finalized jointly with D1's fixed-map normal-form migration.
    `TypeEquiv`/`IsEquivMap` identity,
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
    packaging of `PathSym_A` now depends on the promoted D1 public interface and
    remains a separately owned consumer slice rather than part of the symmetry core.
28. **`IsDiscreteCat` has an exact two-factor contract.** The selected
    definition is `IsSetGrpd(Obj(C))` paired with fixed-map
    `OmegaEquivAlong_{Cat_cat}(Core_incl_func(C))` evidence. Neither factor is
    dropped: object-set truncation alone permits directed arrows, while core
    equivalence without set truncation can retain higher object-path data.
    Before promotion, the fixed-map evidence must derive equivalence of every
    hom action of `Core_incl_func`; its object action is the existing
    `path_to_hom` map. D0b/D1 establish the general variable-evidence hom-action
    and public package; Phase 9 later instantiates it for the core
    inclusion and proves the specialized inverse/round trips. This homwise
    consequence is a theorem/diagnostic, not a duplicated third record field
    unless the general derivation is shown infeasible and the decision is
    explicitly revised.
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
then-report-only edit. The later owner-position `Path_cat` source and migrated
full check-suite candidate also pass warning-enabled. Since that creation
snapshot, Candidates G/A/B and the Phase-3 package have been promoted as
recorded above; the snapshot is historical and does not describe the current
worktree. The probe logs and their distinct append-only/owner-position
limitations are recorded in the handoff inventory and References; a successor
must still rerun the baseline against its own current worktree.

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

All three pass warning-enabled checking without a probe-local warning. At this
initial evidence stage they were late extensions after importing the active
owner and therefore showed mechanical plausibility rather than owner-position
coherence. The elementary probe did not establish observational identity,
no-confusion, higher action, or canonicity for its inductives. The Pi probe did
not itself construct contractible fibres; its generic-J eta was conditional on
the selected reflexive proof-time equation, and typed `eq_refl` tested firing
rather than semantic soundness. Candidate G and Candidate H now supersede
those two append-only promotion boundaries with the owner-position evidence
recorded in their completion sections. Neither promotion gives arbitrary
structured Pi-path elimination a new runtime computational rule.

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
  strict LHS audit. Twelve reports mention the new functor and became the
  explicit classification gate later discharged by the promotion probe.

This audit selected E0's layered composition/collapse removal and E1's minimal
symmetry core for Phase 4. Both cores are now promoted and the twelve E1
interactions are classified; functor-level natural/equivalence packaging and
global confluence remain outside that result.

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

This recursion is active. Its isolated feasibility probe was followed by the
2026-07-15 owner-position source and full retargeted-suite audit before
promotion; warnings remain neutral and the active checks exercise both
equations and arbitrary successor evidence application.

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

### Evidence proposition-valuedness

For paths in `TruncGrpdU(n)` to be controlled by paths/equivalences of the
carrier, the theory eventually needs:

```text
IsPropGrpd(IsTruncGrpd(n,A)).
```

This is now derived from the recursive definition under
`OETU-TRUNC-EVIDENCE-PROP`. It is not replaced by a global proof-irrelevance
rewrite: open evidence remains non-convertible. Truncated-universe univalence
is now active in its restricted decoder-mediated form: the carrier/evidence
package-path comparison composes with canonical ambient univalence. Direct
observational universe identity and the package-universe truncation theorem
remain separate.

The derivation is not independent of the equality architecture. In the
standard HoTT proof, dependent-product closure and the proposition-valuedness
of `IsTruncGrpd(n,A)` use function/Pi extensionality. The active theorem uses
the selected `PiHapply`/`PiFunext` interface rather than merely citing "stable
paths". The theorem assigning the packaged
universe its expected `(n+1)` truncation level additionally depends on ambient
univalence and the evidence-path comparison.

### Closure and invariance ledger

The property kernel is only the beginning of usable truncation support. The
ledger after Candidate B is:

| Fact | Status | Evidence or prerequisite |
| --- | --- | --- |
| equality lowers truncation by one recursive step | **active (2026-07-15)** | The successor rewrite exposes a decoded double Pi, and a durable check applies `h : IsTruncGrpd(succ n,A)` to `x,y` to obtain `IsTruncGrpd(n,x=y)`. |
| monotonicity `IsTruncGrpd(n,A) -> IsTruncGrpd(succ n,A)` | **active (2026-07-15)** | `is_trunc_grpd_succ` uses explicit contractible-path contraction at the base and the native level eliminator at successors; no global weakening rule or proof erasure is installed. |
| invariance under `TypeEquiv` | **active (2026-07-15)** | `is_trunc_grpd_type_equiv` maps the operational decoder path through the predicate, exposes both transports/round trips, computes on reflexivity, and passes 20-file CI without a rule or `unif_rule`. |
| `IsObjTruncCat` invariance under fixed-map `OmegaEquivAlong(F)` | **active (2026-07-15)** | `omega_equiv_along_obj_type_equiv` maps `Obj` over the evidence-indexed category decoder path; the general theorem supplies the evidence equivalence/transports with 21-file CI. Runtime agreement with `fapp0(F)` is deliberately open. |
| dependent-Pi preservation | **active (2026-07-16)** | `is_trunc_pi` uses active `is_contr_pi` at `-2` and transports the recursive pointwise-Pi result back through `pi_happly_type_equiv`; its stable two-equation consumer owner and open-evidence boundary pass 24-file CI. |
| dependent-Sigma level bound | **active (2026-07-16)** | `is_trunc_sigma` uses both base and fibre hypotheses, with `is_contr_sigma` at `-2` and recursive `SigmaPathView`/`PathOver` closure at successors; its stable owner and open-evidence controls pass 25-file CI. |
| truncation evidence is property-valued | **active (2026-07-16)** | `is_trunc_grpd_evidence_is_prop` combines dependent Sigma paths, Pi extensionality, contractible/proposition Pi closure, and a stable two-equation recursive theorem owner; open evidence remains non-convertible. |
| recursive `OmegaEquivAlong` evidence is property-valued/truncated | native EQ1 evidence is unconditionally property-valued; opaque D0 evidence remains a compatibility representation without that theorem, and its finite observation views are retired | `OmegaEquivAlong_D0` remains opaque. The historical finite views supplied no reverse decoder/eta and had no nonself consumer; direct recursive equality still fails the bounded owner/self-normalization gates. Any theorem for retained D0 itself would require a redesigned certificate representation or separately justified reverse evidence-path capability. |
| carrier/evidence paths in `TruncGrpdU(n)` are controlled by carrier paths | **active (2026-07-16)** | `TruncGrpdPathView`, evidence-derived reconstruction, reflexive behavior, both propositional inverse laws, and `trunc_grpd_carrier_path_type_equiv` pass 26-file proportional gates without package eta or a new rule. |
| truncated-universe univalence agrees with restricted ambient univalence | **active (2026-07-16)** | `grpd_univalence_type_equiv` composes with the carrier-path package; exact encoder/decoder projections, both propositional round trips, and the asymmetric reflexive runtime boundary pass 27-file proportional gates. |
| `TruncGrpdU(n)` has expected level `n+1` | **active (2026-07-16)** | `is_trunc_type_equiv` uses an explicit-inverse contractible base and successor Pi/Sigma/property closure; `is_trunc_grpd_universe` transports the result backward through restricted package univalence. Seventeen positive/three negative diagnostics and an eleven-positive/three-negative reviewer example pass 28-file proportional gates without same-level universe computation or proof erasure. |

The recursion equations, both invariance layers, restricted package
univalence, and the expected package-universe level theorem are active. The
remaining recursive-evidence and reflector entries retain their explicit
prerequisites.

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

The promoted `IsDiscreteCat` base derives from its fixed-map evidence:

```text
discrete_core_homwise
  : IsDiscreteCat(C)
    -> Pi x y : Obj(C),
       OmegaEquivAlong_{Cat_cat}(core_incl_hom_func(C,x,y)).
```

This is the recursive/full-faithfulness form of “no extra directed arrows.”
At the immediately visible arrow level it exposes an inverse
`hom_to_path(d,f) : x = y` and propositional/omega-coherent directions:

```text
hom_to_path(d,path_to_hom(p)) = p
path_to_hom(hom_to_path(d,f)) -> f  in Hom_cat(C,x,y).
```

These are diagnostics/theorems, not broad runtime cancellation rewrites. The
active owner is a general hom-action consequence of
`OmegaEquivAlong_{Cat_cat}(F)`, with the core inclusion as its first concrete
consumer. Owner-position evidence made the fallback unnecessary: homwise
evidence is derived rather than duplicated as a third `IsDiscreteCat` field.

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
recursive owner or its induced Cat hom action. Candidate D is therefore
divided into three gates. **D0** is a fresh owner-position recursive-interface
probe, not a public normal-form migration. **D0b** checks that variable fixed-
map evidence induces fixed-map evidence for the functor's hom action. **D1**
is the later public `OmegaEquiv` migration. Candidate D must advance through
the following ladder before the report calls the migration globally coherent:

1. place a general-`C` `OmegaEquivAlong_C(f)` owner at the intended source
   position in a full-file copy, independent of the old opaque `OmegaEquiv`
   owner;
2. define the first-class `OmegaEquiv_C(x,y)` Sigma package, declare the
   inverse observations and recursive higher-cell observations returning that
   package at the next hom level, and validate generic map/evidence projection
   beta before any dependent higher-cell beta;
3. implement the reflexive fixed-map generator and check its recursive
   higher-cell observations through at least the next hom level;
4. at `C = Cat_cat`, construct from variable evidence
   `u : OmegaEquivAlong_{Cat_cat}(F)` an
   `omega_equiv_along_fapp1(u,x,y) :
   OmegaEquivAlong_{Cat_cat}(fapp1_func(F,x,y))`; require its forward-map
   projection to be exactly `fapp1_func(F,x,y)`, construct an inverse with the
   actual hom-category endpoints, and check its left/right higher observations
   through one recursive rung without a per-instance `unif_rule`. The inverse
   generally conjugates/whiskers the selected inverse functor's hom action by
   components of the higher inverse cells: if `G` is that selected inverse,
   raw `fapp1_func(G,Fx,Fy)` alone has endpoints at `G(Fx)` and `G(Fy)`, not at
   `x` and `y`;
5. implement opposite closure with the correct endpoint reversal and both
   higher-cell projections;
6. implement one representative binary constructor, initially Product, and
   test constructor-first, projection-first, and decoder-first diamonds;
7. migrate the active `omega_equiv_*` destructors, `idtoequiv_cat`, and
   `omega_equiv_path` declarations to the new package in the same full-file
   candidate; jointly rerun the `OETU-CAT-UNIV-DECODER`-owned round trips,
   `path_to_hom` squares, and one Product decoder consumer;
8. declare one concrete named functor `F`, evidence `u : OmegaEquivAlong(F)`,
   and package `(F,u)`, then exercise univalence/action and one recursive
   next-hom observation without a per-instance `unif_rule`;
9. compare the operational evidence propositionally in both useful directions
   with `OmegaEquivFibre(F)`, while keeping the theorem that the evidence is a
   proposition as a separately statused obligation; and
10. pass source-order subject reduction, inferred-LHS audit, changed-head
    warning comparison, both-order diagnostics, and bounded full-suite timing.
    No evidence field may be erased before the property theorem exists.

Steps 1--3 are the D0 gate. Step 2 belongs in D0 rather than D1: the recursive
left/right cell observations return first-class omega-equivalences in the next
hom-category, so they need the minimal Sigma package (or an exactly equivalent
internal package) in their result types. Postponing that package would require
a provisional second recursive codomain and would weaken the owner test. D0
must pass at source position without implementing its observations through the
old opaque `OmegaEquiv`; it may coexist under fresh candidate names and does
not by itself migrate the public normal form. A passing D0 result establishes
recursive-owner implementation feasibility, not Candidate D completion.

Step 4 is the D0b gate. Its owner-position probe must consume variable `u`, not
only reflexive evidence, and must exercise the induced inverse, whiskering/
conjugation endpoints, and recursive observations rather than merely type the
result. It is the pre-D1 feasibility check for the general Cat hom-action
construction; it does not yet instantiate `Core_incl_func`, prove the
specialized `hom_to_path` round trips, or complete Phase 9. D0b is not a
prerequisite for Candidate G or the earlier A/B/E0 slices, but D1 may not begin
until D0b passes. This sentence records the D0b gate itself; the later Phase 9
owner-position slice now supplies that specialization and its coherent
directions.

Steps 5--8 are D1's completed closure, public-consumer, decoder, and
integrated-witness migration. Steps 1--8 together in the full-file candidate
were the minimum public promotion gate, with the applicable source-order,
warning, and timing checks from Step 10 repeated for D0, D0b, and the completed
D1 candidate.
Step 9's property theorem may remain a named prerequisite for the first
runtime migration, but `IsDiscreteCat` package equality and any proof-field
irrelevance continue to depend on it.

### Indexed adjunctions rather than a permanent `Along` facade

The same fixed-data principle applies more directly to adjunctions. The active
owner is an adjunction relation indexed by the already-selected functors:

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

The exact two rule shapes are active and pass the full owner-position source,
suite, and reviewer probes. Neither rule discriminates on the variable `F` or
`G`. Their rigid heads are the outer `comp_fapp0`, the stable
`unit_adj_transf(J)`/`counit_adj_transf(J)` observations, and the surrounding
`tapp1_fapp0`/`fapp1_fapp0` application structure. The indices are recovered
and checked by their repeated occurrence in those patterns.

There is no permanent need for a second `AdjunctionAlong(F,G)` classifier. The
retained compatibility functor views are transparent definitions:

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

The superseded runtime rules projecting the left/right functors of an opposite
adjunction have disappeared, while the opposite unit/counit rules remain
headed by the stable unit/counit observations. If a consumer genuinely needs an
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

The selected `IsDiscreteCat` contract and homwise adequacy are now implemented
and validated, so recursive `IsNCat` formation is dependency-ready. The gate
was specifically fixed-functor omega-equivalence and its hom-action theorem—
not an unspecified need for every possible notion of category equivalence—
and it was discharged directly from D0b evidence.

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

The former global symbol:

```text
cat_iso_univalence(C) : CatIsoUnivalence(C)
```

was quarantined and is now retired. The dimension-correct interface is:

```text
onecat_iso_univalence
  : Pi C : OneCat,
      CatIsoUnivalence(onecat_carrier(C)).
```

The selected result derives this from:

- global `CatUnivalence` into `OmegaEquiv`;
- the discreteness/truncation of all hom-categories of a `OneCat`;
- a comparison between `OmegaEquiv` and `IsoEvidence` at that level.

Implementation evidence now supplies both halves constructively. Strict
`IsoEvidence` lifts to recursive `OmegaEquiv`, whose canonical decoder gives
`one_cat_iso_path` and its first round trip. In the reverse direction,
recursive cells compare the separately stored omega inverses, OneCat hom
discreteness turns that directed cell into equality, and ordinary equality
action transports the right law to the chosen left inverse. Hom discreteness
also makes the two inverse-law proof fields proposition-valued, so the
existing nested-Sigma path owner proves reconstruction of arbitrary ordinary
evidence after the lift. That yields the second round trip and the scoped
`one_cat_iso_univalence`/`one_cat_iso_type_equiv` capability.

The former global decoder classifier could not own the result because it hardcoded
`iso_evidence_path`; the selected `OneCatIsoUnivalenceByDecoder(X)` instead
indexes the specified inverse by `one_cat_iso_path(X)`. The unscoped
inhabitants/classifier are removed after the bounded migration; no scoped
wrapper invokes them. The legacy decoder remains only for its separately
measured reflexive/Product computation.

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
policy. The active source has retired the exploratory arbitrary-`Cat`
`cat_iso_univalence(C)` and decoder-capability inhabitants after the scoped
OneCat replacement passed synchronized CI. The remaining policy is:

- no new redesign declaration, theorem, or computation may depend on the
  global ordinary-iso capability;
- `iso_evidence_path` remains only as a legacy runtime decoder for its
  reflexive and Product computation until a separate replacement is selected;
- `CatUnivalence(C)` with recursive `OmegaEquiv` is the general categorical
  interface used by new work; and
- `CatIsoUnivalence` returns only as a `OneCat`-scoped derivation or explicit
  ordinary-dimensional assumption.

This turns the original architectural quarantine into an enforced capability
boundary while preserving the separately consumed decoder computation.

## One Operational Inverse Per Univalence Layer

The decoder-oriented interfaces are selected as the eventual operational
owners:

```text
grpd_equiv_path
one_cat_iso_path        // scoped ordinary-iso decoder
iso_evidence_path       // retained legacy Product compatibility decoder
omega_equiv_path.
```

The groupoid owner can be selected and finalized near the beginning of the
migration, before constructor-specific univalence closure and paths of
packaged truncated universes are claimed. The categorical **name and
orientation contract** should also be selected early so that new code does not
accumulate against another inverse, but its public domain/codomain, round trips,
and constructor computation were deliberately not finalized before D1 replaced
the `OmegaEquiv` normal form. That finalization is now promoted jointly with
D1 rather than implemented once against the old classifier and again after the
migration.

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
owns its two round trips and the `path_to_hom` squares; Candidate D1 migrated
and revalidated those diagnostics because their equivalence type changed, but
does not become a second semantic owner. `TypeEquiv` algebra separately owns
identity, symmetry, and composition of equivalences and `IsEquivMap` evidence.

## `Path_cat` Composition, Collapse Removal, And Symmetry Core Are Promoted

The path-category redesign must precede `IsDiscreteCat`, `IsNCat`, `OneCat`,
and any **public** shaped-reflexivity slice that registers with path
composition or symmetry. Shaped owner-position research probes may run earlier,
but promoted rules must not register against an owner that a later phase plans
to replace.

The owner choices are selected by full-file probes and the E0/E1 cores are
promoted:

1. E0 removes the runtime collapse `Op_cat(Path_cat(A)) -> Path_cat(A)` and the
   old composition fold;
2. E1 represents self-oppositeness by `PathSym_A`, whose arrow action is the
   strict path-symmetry owner; D1 now supplies the selected public package,
   while fixed-map equivalence packaging remains a separate consumer slice;
3. the selected shared-`comp_fapp0` composition candidate is active with its
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
D1 now supplies the fixed-map owner for an eventual
`OmegaEquivAlong(PathSym_A)` package. That package remains a separately owned
downstream consumer and is not required for the promoted symmetry operation or
the core-inclusion `IsDiscreteCat` contract unless its owner-position proof
exposes a concrete dependency.

The pre-classification E1 source and suite pass at 1,084 pairs; the promoted
rebased source passes at 974/159 with zero unreviewed strict-LHS candidates.
The twelve `PathSym_A` reports split into typed oriented-action/naturality
diamonds, untyped Product projections, and six mapped-`DefIso` interactions
resolved by inferring generic endpoint slots. They are not evidence of a
second semantic owner. Later evidence may justify redesigning public
`eq_trans`/`eq_sym`, but neither strict/J-derived comparison is definitional
in the promoted core.

## Product Reflexivity Policy

Product constructor provenance should be preserved until observational
reflexivity has one canonical structured normal form.

The promoted migration removes reflexive-collapse rules of the form:

```text
omega_equiv_product(refl,refl) -> omega_equiv_refl
iso_evidence_product(refl,refl) -> iso_evidence_refl.
```

The Product constructors and decoders now reduce componentwise without a
competing generic evidence head. Owner-position source/check probes, both
reduction orders, negative non-collapse controls, and the focused reviewer
example pass. The deletion improves warnings from 978/157 to 972/157 and
leaves the strict audit at zero/45/27. No replacement proof-time comparison is
installed: no typed consumer needs one, and equating fixed-map evidence before
its property theorem would overstate the current semantics.

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

The first composite and related-input application are runtime computations.
The reverse composite is propositional for arbitrary `p`. The active stable
heads obtain its reflexive base through one narrow two-rigid-head proof-time
equation and then derive arbitrary eta by generic `ind_eqr`. Under the selected
hybrid architecture, this is a valid ordinary-J proof **conditional on that
selected base equation**, even though the Pi equality classifier is
structured. The equation is classified as a generic semantically justified
structural law: the transparent presentation reduces independently, while
typed `eq_refl` only tests operational firing. The owner-position warning and
reduction-order audit, including shaped-reflexivity joins, passes. A future
fibrancy-derived computational J may be compared with this theorem, but is not
its dependency.

Beta and propositional eta supply quasi-inverse data but do not by themselves
inhabit the active contractible-fibre `IsEquivMap`. Candidate H therefore adds
the reviewed generic theorem capability converting explicit quasi-inverse data
to contractible fibres and a `TypeEquiv` package with executable forward,
inverse, right-path, and selected-centre projections; contraction stays opaque.

For Sigma and the first dependent record, the corresponding compatibility
surface includes:

```text
decode(encode(p)) = p
encode(decode(w)) = w
```

for arbitrary `p` and path-view value `w`, plus the reflexive beta laws. These
are now active. Sigma keeps the dedicated path-view classifier and proves both
arbitrary composites propositionally, without open runtime eta. PathRecord
equality already is its view, so its named maps and round trips are transparent
and preserve shaped reflexivity through a nested former.

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
| identity/path | `Path_cat`, `Core_cat`, `Core_incl_func` | groupoidal lift into directed structure | E0 shared composition/genuine opposite and E1 functor-owned symmetry are active; functor-level natural packaging and later fixed-map equivalence packaging remain prerequisites only for their downstream consumers |
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
| Native `nat` and generated `ind_nat` at ambient `TYPE` | active | The native inductive remains distinct from the decoded `Nat_grpd` facade; both layers now have explicit active diagnostics. |
| `Nat_grpd` and a reviewed groupoid-level eliminator facade | active; Candidate G promoted 2026-07-15 | `τ Nat_grpd ↪ nat`; `nat_elim` retains the decoded classifier in its signature, routes through `ind_nat`, and has durable zero/successor beta checks. |
| Empty and Bool decoded classifiers and eliminators | active; Candidate G promoted 2026-07-15 | Native `empty`/`bool`, decoded `Empty_grpd`/`Bool_grpd`, dependent eliminators, both Bool betas, formation/introduction checks, and a local conversion anti-collapse control are active. |
| General binary sum classifier and dependent eliminator | active; `OETU-H0-SUM` promoted 2026-07-15 | Native `SumData(A,B)`, decoded `Sum_grpd(A,B)`, both constructors, dependent elimination, both betas, swap consumer, local constructor non-collapse, and 19-file CI are active. Separate native parameter binders are required to keep both classifiers fixed in the generated induction principle. Observational no-confusion/canonicity, additional action, and categorical coproduct structure remain separate. |
| Observational identity/no-confusion/higher action for elementary inductives | split: visible identity, componentwise Sum refinement, and recursive Nat successor refinement are active; no-confusion/canonicity and other former actions remain separate | Unit/Boolean/Nat/Sum identity owners, the generic-J guard, `OETU-OBS-SUM-ACTION`, and `OETU-OBS-NAT-SUCC-ACTION` are promoted. Cleanup P2 presents Sum and successor selection as `PathActionRefinement` of canonical path-map action; Sum uses Empty mixed cases and successor retains the exposed predecessor path. Both preserve the audited proof-time/runtime boundaries. |
| Equality, literal `eq_refl`, generic `J`, transport, `ap`, `apd`, `PathOver` | active | Present, but the equality architecture is hybrid and not the final global owner. |
| Standard `PiHapply`/`PiFunext` compatibility | active; Candidate H promoted 2026-07-15 | Stable owners retain related-input action and pointwise beta; generic J derives eta from a semantically justified proof-time reflexive basis, with typed firing, runtime-negative, and application-first shaped-join diagnostics. |
| `IsEquivMap(PiHapply)` and Pi `TypeEquiv` package | active; Candidate H promoted 2026-07-15 | Explicit quasi-inverse data is converted by the reviewed generic theorem capability to contractible fibres; the selected centre makes the packaged inverse/right path executable while contraction remains opaque. |
| Named finite dependent-record formation/elimination | active; Candidate A promoted 2026-07-15 | `PathRecord_grpd(A)` decodes to a parametrized one-constructor carrier; named source/target/witness projections and `path_record_ind` compute, while a durable negative control confirms no runtime eta. |
| Arbitrary Sigma/record path-characterization round trips | active; `OETU-STRUCTURAL-PATH-COMPAT` promoted 2026-07-15 | Both arbitrary Sigma composites are propositional with constructor-reflexive computation and open eta negatives. PathRecord maps are transparent because equality already is its view; both round trips, shaped reflexivity, the dependent-tail observer, and one nested former compute. |
| Record identity classifier, reflexivity, and optional action refinement | active; Candidates C, structural compatibility, historical `OETU-OBS-ACTION`, and cleanup P1/P2 are promoted | `PathRecord` equality exposes the nested dependent-Sigma view; stable reflexivity, projections, round trips, and open-map action through `PathActionRefinement` have owner-position diagnostics. The dependent witness uses direct `eq_apd`/`PathOver`; fibrancy remains separate. |
| Stable shaped record reflexivity and reflexive shaped `J` | active; Candidate C promoted 2026-07-15 | The stable former-specific head, specialized reflexive `ind_eqr`, complete literal-reflexivity registry, dependent/nested consumers, and classified warning controls pass all gates. |
| Dependent/nested shaped reflexivity, structural action, and additional computational dependent `J` | split: reflexivity and nondependent `PathActionRefinement` active; extra arbitrary-constructor `J` remains a fibrancy prerequisite | Candidate C supplies reflexivity/reflexive J; cleanup P2 supplies semantically anchored selected nondependent action, identity/composition, and exact capped-action agreement. P1 retired the unused dependent registry, so the PathRecord witness action uses direct `eq_apd`. Retained generic J stays active, and explicit negatives show action alone does not supply the fibrancy-dependent beta. |
| Contractibility, fibres, `IsEquivMap`, `TypeEquiv` | active | Contractible-fibre presentation and selected map/inverse observations are active. |
| `TypeEquiv`/`IsEquivMap` identity, symmetry, and composition compatibility | active; `OETU-TYPE-EQUIV-ALGEBRA` promoted 2026-07-15 | Reflexivity plus transparent symmetry and categorical-order composition carry derived contractible-fibre closure. Forward/inverse/right projections and forward-map units/associativity compute; package eta and contraction-derived left projection remain non-runtime. Univalence round trips are separate. |
| Groupoid univalence and operational reverse decoder | active; `OETU-GRPD-UNIV-DECODER` promoted 2026-07-15 | `grpd_equiv_path` is the sole operational inverse. The decoder package derives the canonical contractible-fibre capability and selected inverse; arbitrary legacy `ua_grpd` agreement is intentionally not postulated. |
| Both groupoid-univalence round trips and selected action coherence | active; `OETU-GRPD-UNIV-DECODER` promoted 2026-07-15 | Both named decoder round trips, generic `coe_grpd_idtoequiv`, propositional `grpd_equiv_path_coe`, Product evidence, and one Pi-universe action consumer are active. The broad runtime decoder-transport fold is rejected until Product-path transport joins. |
| Observational identity of the groupoid/category universes | split: finite groupoid identity view and canonical direct categorical identity remain active; the former finite fixed-arrow D0 observation/path views were retired by the 2026-07-19 consumer audit; direct groupoid equality and direct recursive certificate equality remain rejected at their unstratified recursion boundaries | `GrpdPathView(A,B)` reuses the canonical decoder without changing groupoid public equality. Category public equality reduces directly to `CatPathView(A,B) := OmegaEquiv(Cat_cat,A,B)` while generic reflexivity remains distinct. The retired D0 finite views remain dated feasibility evidence only; future direct rules still need stratification or another measured recursion guard. |
| Truncation properties and low-level aliases | active; Candidate B promoted 2026-07-15 | Native levels, recursive `IsTruncGrpd`, proposition/set/groupoid views, and definitional equality-lowering evidence application have owner-position and active diagnostics; stronger closure facts retain the separate ledger statuses. |
| Packaged `PropU_grpd`/`SetU_grpd`/`GroupoidU_grpd` | active; Phase 3 core plus 2026-07-16 path/univalence/level extensions promoted | `TruncGrpdU(n)` decodes to a named carrier/evidence record; projections, low-level aliases, a named package-path view, evidence-derived reconstruction, both propositional path round trips, restricted decoder-mediated equivalence with carrier `TypeEquiv`, and `IsTruncGrpd(succ n,TruncGrpdU(n))` are active. Evidence is retained and no eta, proof erasure, same-level claim, or direct universe identity is installed. |
| Truncation reflectors | deferred | Require the higher-constructor/restricted-elimination architecture. |
| `Cat`, functors, transfors, iterated hom actions | active | Broad generic infrastructure exists and remains the owner of ordinary functoriality/naturality. |
| `Path_cat` E0 category composition and collapse removal | active; promoted 2026-07-15 | Shared `comp_fapp0`, two minimized unit bridges, J-derived `path_comp_eq_trans`, genuine opposite presentation, typed oriented-action units plus non-conversion controls, the migrated suite/example, 1,072/159 warning inventory, zero strict-LHS candidates, and full CI pass. |
| `Path_cat` E1 opposite/symmetry core | active; promoted 2026-07-15 | `PathSym_A` functor/action, strict reflexivity and generic anti-composition, propositional `eq_sym` agreement/involution, pointwise Core-opposite square, negative controls, and the twelve-block warning classification are active. The mapped-`DefIso` endpoint repair lowers the inventory to 974/159. Functor-level natural and fixed-map equivalence packages remain prerequisites. |
| Global ordinary-iso univalence compatibility | arbitrary-`Cat` capability inhabitants/classifier retired; full OneCat-scoped replacement active; legacy decoder/Product computation retained | General-category architecture uses `CatUnivalence`. The derived OneCat lane supplies both round trips and a scoped capability without invoking the legacy decoder. `CatIsoUnivalence` remains as the type of an explicit/scoped assumption and `isotoid_cat` is checked with `one_cat_iso_univalence`; only `iso_evidence_path` and its reflexive/Product rules remain compatibility-owned. |
| First-class `OmegaEquiv` observations | active; Candidate D1 promoted 2026-07-15 | Public `OmegaEquiv` is the fixed-arrow Sigma package; recursive observations route through evidence and reflexive/opposite/Product generators compute. Unrestricted corecursion and package eta remain absent. |
| Primary fixed-map `OmegaEquivAlong(F)` plus Sigma package | D0/D0b/D1 active | `OmegaEquivAlong_D0(f)` remains the neutral internal owner and public `OmegaEquivAlong(f)` its transparent name; public `OmegaEquiv` is `Sigma f, OmegaEquivAlong(f)`. Exact projections, inverse/cell observations, reflexive/opposite/Product computation, variable-evidence hom action, and the integrated next-hom witness are active with 93 diagnostics across D0/D0b/D1. The semantic fibre comparison is a one-sided retraction; property-valuedness remains separate. |
| Categorical decoder finalization and round trips | active; `OETU-CAT-UNIV-DECODER` completed with D1 | The evidence-indexed `omega_equiv_path` is the operational inverse. Both named round trips, derived contractible-fibre capability, named `TypeEquiv`, selected inverse agreement, propositional `path_to_hom` square, and Product decoder projections are active; open round trips remain non-runtime. |
| Indexed `Adjunction(F,G)` | active; Phase 8 promoted 2026-07-15 | Indexed formation, direct `F`/`G` conversion, stable unit/counit observations, both exact triangles, opposite involution, mates, weighted preservation, named-operation negatives, owner-position warning/LHS evidence, and the expanded reviewer example are active. No proof-time named-operation equation is installed because no declaration-backed instance exists. |
| `IsObjTruncCat` | active; promoted with `OETU-NCAT` 2026-07-15 | Exact formation over active `IsTruncGrpd` is checked; it remains independent of recursive directed dimension and does not itself prove the later implication from `IsNCat`. |
| `IsDiscreteCat` | active; native representation promoted 2026-07-19 | Exact set-object/native-`IsGroupoidalCat_EQ1` Product formation remains in the kernel; canonical homwise evidence, selected inverse, `hom_to_path`, and both coherent directions live in the one-way native hom-action extension. Runtime negatives and reviewer coverage are preserved without a redundant homwise field, D0 migration, new rule, or unifier. The old OneCat decoder is a separately named compatibility consumer. |
| Recursive `IsNCat` | active; promoted 2026-07-15 | Exact zero/successor recursion, evidence-retaining packages, `ZeroCat`/`OneCat`, independence and no-eta negatives, and a `OneCat` next-hom consumer are active with 17-file CI. The object-truncation implication remains separately dependent. |
| `IsNCat(n,C) -> IsObjTruncCat(cat_dim_trunc_level(n),C)` | active as unconditional native theorem `ncat_obj_trunc_EQ1`; the older D0 conditional experiment is retired | The native evidence-property/retraction proof supplies the missing truncation input without an opaque-certificate eliminator. The base and successor equations compute, `prop_is_trunc_cat_dim` remains shared proof support, and the self-only D0 capability/theorem/example were deleted on 2026-07-19. |
| Packaged `OneCat` and scoped ordinary-iso univalence | active through both round trips, specified-inverse and contractible-fibre capabilities, and named `TypeEquiv`; synchronized 40-file CI passes | Formation uses the real discrete base. Strict `IsoEvidence` derives recursive `OmegaEquiv` and the first decoder round trip. Arbitrary omega evidence compares its inverse arrows, transports the right law, and reconstructs ordinary evidence. Hom discreteness plus the nested-Sigma path owner proves the retract and second round trip. The scoped classifier selects `one_cat_iso_path`; unused global capability inhabitants are retired, while the legacy Product decoder remains distinct. |
| One-next-hom end-to-end adequacy example | active; Candidate D1 promoted 2026-07-15 | A category path selects a functor and D0b-derived fixed-map evidence for its hom action; the public package has exact forward/evidence projections and an iterable recursive left cell, without a per-instance `unif_rule`. |

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
   user direction on 2026-07-15 adopts this report as the living forward
   implementation master plan.
2. The June 23 univalence report is retained as the promoted historical
   implementation ledger; this report supersedes it only for forward work.
3. Add no unrelated direct equality, Product decoder, or global
   `CatIsoUnivalence` computation during the redesign. Focused equality rules
   explicitly belonging to the shaped fast track are allowed after their
   promotion probe; this freeze is not a veto on that track.
4. **Completed 2026-07-16:** freeze, replace, and retire
   `cat_iso_univalence`, `cat_iso_univalence_by_decoder`, and their hardcoded
   classifier after the OneCat-scoped capability passed synchronized CI.
   Retain only the separately consumed `iso_evidence_path` reflexive/Product
   computation; use `CatUnivalence`/`OmegaEquiv` for general categories.
5. Apply the local-first reference policy: external designs define comparison
   tests or candidate ingredients, never an obligation to reproduce their
   implementation.
6. Apply the proof-time trust policy immediately: add no unclassified
   `unif_rule`, use typed `eq_refl` to test firing, and never report that test
   as independent semantic validation.
7. Preserve the passing active baseline.
8. **Completed 2026-07-15:** Candidate G / `OETU-ELEMENTARY-HOTT` is promoted
   under the exact exclusions in the handoff section. This first slice does
   not itself adopt any later normal-form migration. Candidates A/B are now
   also promoted, Phase 3 subsequently promotes the packaged truncated
   universes, and both Phase 4 path-category slices now promote shared path
   composition, the genuine opposite boundary, and functor-owned symmetry.
   Candidate C / `OETU-OBS-SHAPED-REFL` and Candidate H /
   `OETU-PI-FUNEXT`, `OETU-STRUCTURAL-PATH-COMPAT`,
   `OETU-TYPE-EQUIV-ALGEBRA`, and `OETU-GRPD-UNIV-DECODER` are also promoted.
   Candidates D0, D0b, and D1 under `OETU-OMEGA-EQUIV-ALONG` are now also
   promoted, jointly completing the categorical decoder. Phase 8 indexed
   adjunction and the D1-derived discreteness specialization are also
   promoted; recursive `OETU-NCAT` formation is the current Phase 9
   dependency-ready default.

### Phase 1: Finite Record Convention Probe

**Completed/promoted 2026-07-15.**

1. The small dependent one-constructor `PathRecord` was refined in a full-file
   owner-position source plus complete retargeted suite.
2. Its generated eliminator facade, named projections, dependent witness type,
   constructor betas, decoded parameter syntax, and negative runtime-eta
   control pass.
3. A probe-only nested-Sigma encoding also passes warning-neutral; it is
   retained as comparison evidence because its public access uses nested
   projection chains and its eliminator surface is less direct.
4. The final one-constructor/named-projection/generated-induction convention is
   recorded in the living SOP and Foundations.
5. Observational record equality, shaped reflexivity/action/J, generic record
   generation, and truncation packages were not introduced and remain in
   their own ledger rows.

This phase is independently feasible and informs all later packaged
universes.

### Phase 2: Truncation Properties

**Completed/promoted 2026-07-15.**

1. Native `TruncLevel` and readable `-1/0/1` aliases are active from the
   explicit `-2` origin, with a negative no-shift control.
2. The `IsContr` base and successor path-space equations of `IsTruncGrpd` are
   active at their owner immediately after contractibility.
3. `IsPropGrpd`, `IsSetGrpd`, and `IsGroupoidGrpd` are transparent active
   views.
4. Fifteen durable checks cover formation, level aliases, both recursion
   equations, low-level reductions, base evidence, and successor evidence
   application.
5. The closure/invariance ledger now marks only definitional equality lowering
   active and names the prerequisites for every stronger fact.
6. Packaged universes, property-valuedness, closure theorems, and truncation
   reflectors were not added.

After the default elementary-H0 slice, this is the leading
truncation-specific mathematical promotion candidate.

### Phase 3: Packaged Truncated Universes

**Completed/promoted 2026-07-15.**

1. Add the one-constructor `TruncGrpdU(n)` record/classifier.
2. Add computing carrier/evidence projections.
3. Add `PropU_grpd`, `SetU_grpd`, and `GroupoidU_grpd` aliases.
4. Derive or explicitly defer property-valuedness of truncation evidence.
5. Do not claim univalence of these subuniverses before proof-field paths are
   controlled.
6. State the expected `(n+1)` truncation level of the universe separately from
   the `n`-truncation evidence carried by its elements.

Phase 3 start record (2026-07-15): staged changes are empty; the unstaged
worktree contains only completed Candidates G/A/B and synchronized generated
artifacts/reports plus this ledger transition. Candidate B's full `make ci` is
the incoming baseline. The package will be a parametrized one-constructor
record immediately after `IsTruncGrpd` and its low-level views. Negative
diagnostics will verify that evidence fields are retained, arbitrary packages
do not eta-contract, and element evidence does not type as evidence that
`TruncGrpdU(n)` itself is `n`-truncated.

Phase 3 completion record (2026-07-15): `TruncGrpdData(n)` and its decoded
`TruncGrpdU(n)` classifier are active immediately after the truncation views,
with direct carrier/evidence constructor beta and transparent
`PropU_grpd`/`SetU_grpd`/`GroupoidU_grpd` aliases. The evidence projection
retains its dependent result type. Fourteen durable diagnostics cover decoding,
construction, generic and low-level projections, aliases, and the three
negative boundaries: no runtime eta, no evidence erasure, and no false
same-level universe typing. Owner-position source/suite probes pass quietly and
warning-enabled with the unchanged 1,109/163 inventory and zero strict-LHS
candidates. Active checks, examples, catalog (854 checks, zero unclassified),
TOC, health, warning summary, audit, and CI pass. Evidence
property-valuedness/proof erasure, package equality/univalence, closure and
universe-level truncation theorems, and reflectors remain separate ledger rows.

### Phase 4: Path-Algebra Ownership And `Path_cat` Repair

Phase 4 E0 start record (2026-07-15): staged changes remain empty; the
unstaged worktree contains only the promoted Candidates G/A/B/Phase-3
kernel/check/report/generated synchronization and this ledger transition, with
no unrelated user change detected. Phase 3's full `make ci` is the incoming
baseline. The bounded owner is the already-tested removal-only full-file E0
candidate, rebased conceptually over the active Phase-3 source: shared generic
`comp_fapp0` remains category composition, the old J-derived runtime fold and
self-opposite collapse are removed, narrow unit/action projection bridges are
audited, and E1 symmetry plus every univalence/shaped-equality migration remain
excluded.

**E0 shared composition and collapse removal:**

1. Promote/refine the full-file-tested category-level composition candidate:
   remove the `comp_fapp0(Path_cat)->eq_trans` fold, retain the shared generic
   `comp_fapp0` head, and add the two narrow `eq_refl` unit bridges.
2. Preserve `hom_postcomp_fapp0` and `hom_precomp_along_fapp0` as distinct
   oriented runtime action owners with their existing proof-time comparisons;
   owner-position probe and minimize/classify the four oriented `eq_refl` unit
   obligations demonstrated append-only. Do not fold category composition into
   either action head while the measured associativity timeout remains.
3. State and check the J-derived propositional comparison with `eq_trans`.
4. Remove definitional self-oppositeness in the same candidate. Reuse the
   passing removal-only full source/suite evidence and keep a durable negative
   control against reintroducing the collapse.
5. Add both runtime-unit diamonds and typed generic associativity diagnostics;
   revalidate `Core_incl_func`, `path_to_hom`, transport/`ap`, `DefIso`,
   opposite, and Product consumers.

Phase 4 E0 completion record (2026-07-15): the active kernel now retains
generic `comp_fapp0` as `Path_cat` composition, removes its old runtime fold to
`eq_trans`, removes the false `Op_cat(Path_cat(A))->Path_cat(A)` collapse,
adds two annotated SOP-minimal `eq_refl` unit projection bridges, and exposes
the J-derived propositional theorem `path_comp_eq_trans`. The diagnostic suite
replaces the old conversion claim with theorem formation/base beta, an open
non-conversion control, both unit reduction orders, typed generic
associativity, reversed opposite homs, a no-collapse control, four typed
oriented-action units, four corresponding runtime non-conversion controls,
and a direct oriented/shared proof-time comparison. `Core_incl_func`
composition now retains shared path composition on the source side. The
reviewer path-category example is synchronized.

Owner-position evidence changed Step 2's architecture. The four
constructor-specific oriented-action runtime bridges were tested in their
owning positions. With explicit action endpoints they raised the inventory to
1,077/165, five critical-pair reports and six replaceable-variable advisories
above the selected result. Existing identity-family proof-time comparisons are
not reliably transitive after immediate unit normalization, so the durable
checks first name a general typed action-to-shared-composition witness and then
specialize it to each unit. This yields the four propositions while four
`assertnot` controls preserve the action runtime heads. The final minimized
owner source/suite pass quietly (`20260715-164934`/`164939`) and
warning-enabled (`20260715-164427`/`164430`) at 1,072/159; the strict LHS audit
is zero with 39 annotated slots across 23 clauses. Active `make check`,
examples, catalog (872 checks, zero unclassified), TOC, health, warning
summary, audit, and full CI pass. E0 is complete; action runtime bridges reopen
only for a concrete consumer that cannot use the typed two-step route.

**E1 symmetry-functor core:**

Phase 4 E1 start record (2026-07-15): staged changes remain empty; the
unstaged worktree contains only the plan-scoped promoted G/A/B/Phase-3/E0
implementation, synchronized diagnostics/examples/reports/generated
artifacts, and this ledger transition, with no unrelated user change detected.
E0's full `make ci` is the incoming baseline. The bounded task is to rebase
the already owner-position-probed symmetry core over E0, classify its twelve
new warning blocks with explicit both-order consumers, and promote only the
functor/action/reflexivity plus J-derived agreement/involution and pointwise
Core square. Functor-level natural/path packaging, fixed-map equivalence,
public shaped equality, and decoder/univalence migration remain excluded.

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
11. D1 now supplies the fixed-map owner. Package `PathSym_A` as
    `OmegaEquivAlong(PathSym_A)` only in a separately selected consumer slice;
    do not fold it into the already completed Phase 4 core.

Phase 4 E1 completion record (2026-07-15): `Path_sym_func(A)` is active as a
functor from the genuine opposite `Path_cat(A)` to `Path_cat(A)`. Its object
action and one annotated reflexivity projection bridge compute; `path_sym` is
the readable arrow-action view; generic functor identity/composition owns the
identity-first/action-first and ordered anti-composition diamonds. J supplies
`path_sym_agrees_eq_sym`, `path_sym_invol`, and the pointwise
`path_sym_core_incl_agreement`; open `path_sym = eq_sym` and double-symmetry
conversions remain negative. No path-specific composition or cancellation
rewrite was added.

The twelve warning blocks changed the planned owner architecture. Both-order
post/pre action and transformation-naturality consumers join without new
rules. The two Product projection overlaps are ill-typed because
`Path_sym_func` has a rigid path-category target. The six mapped-`DefIso`
blocks exposed three over-specified `fapp0` endpoint guards in each generic
left-cancellation clause: even the nominally unprojected consumer normalized
those guards before the owner could match. Replacing those six inferred slots
by `_` makes both mapped-cancellation orientations compute before and after
all object projections. It removes 110 generic critical-pair reports; E1
retains six classified reports, for a net change from 1,072/159 to 974/159.
The full source and migrated suite pass quietly (`170120`/`170345`) and with
warnings (`170137`/`170838`); strict LHS audit remains zero with 41 annotated
slots across 24 clauses. Active checks, the reviewer example, catalog (899
checks, 883 assertions plus 16 negative assertions, zero unclassified), TOC,
health, and full CI pass. Functor-level natural
packaging and `OmegaEquivAlong(PathSym_A)` remain separate dependencies.

This phase controls the composition and symmetry owners used by later public
shaped-reflexivity registration. E0 and the E1 core may promote independently
of later fixed-map equivalence packaging; `OneCat` and discreteness still wait
for that packaging and their other listed prerequisites. This phase does not
prevent earlier isolated shaped research probes.

### Phase 5: Equality MVP And Immediate Shaped Fast Track

Candidate C's bounded shaped-reflexivity/reflexive-J core is
**completed/promoted (2026-07-15)**. Candidate H's Pi/function-
extensionality equivalence is also **completed/promoted (2026-07-15)**.
Arbitrary Sigma/record path round trips and ordinary
`TypeEquiv`/`IsEquivMap` algebra are likewise **completed/promoted
(2026-07-15)**. Groupoid decoder coherence is the current owner-position H1
slice; structural action, fibrancy, and additional arbitrary-constructor J
computation remain separate later steps.

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

Generic propositional uses of `ind_eqr`, including active Candidate H eta over
its selected and justified reflexive coherence basis, remain valid in both
lanes. The fibrancy capability gates only additional structural runtime betas
on arbitrary shaped path constructors.

### Phase 6: Split Univalence Decoder Ownership

The groupoid equivalence type is not changed by Candidate D, whereas the
categorical equivalence type is. Their decoder work therefore has different
implementation schedules even though both layers retain one operational
inverse.

**Phase 6G: groupoid decoder normalization:**

Status: **completed/promoted (2026-07-15)** under
`OETU-GRPD-UNIV-DECODER`. New consumers are restricted to the canonical
decoder capability; arbitrary legacy `ua_grpd(U,e)` agreement remains
negative. Both round trips, the propositional transport square, and the Pi
action consumer are active. Direct universe identity remains later work.

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

**Phase 6C: categorical decoder contract completed with D1:**

5. Reserve `omega_equiv_path` as the categorical reverse decoder name and
   record its intended orientation, capability-agreement obligation, two round
   trips, and `path_to_hom` squares as the contract owned by
   `OETU-CAT-UNIV-DECODER`.
6. Quarantine legacy global `CatIsoUnivalence` consumers: new general-category
   coherence uses `OmegaEquiv`, while the ordinary-iso decoder exists only
   behind `OneCat` or an explicit dimension hypothesis.
7. The categorical decoder's public types, round trips, and constructor rules
   were not finalized against the obsolete opaque `OmegaEquiv` normal form.
   D1 retyped and validated them jointly with the public migration; the
   categorical decoder task remains their sole semantic owner.

### Phase 7: Primary Fixed-Map Omega-Equivalence And Sigma Package

**D0 recursive-owner feasibility gate:**

Status: **completed/promoted (2026-07-15)** under
`OETU-OMEGA-EQUIV-ALONG`.

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
   as D0 recursive-owner feasibility only; D1 remains not implementation-
   feasible until the separate D0b gate also passes.

Completion evidence: the owner-position source/check pair
`oetu_omega_equiv_along_d0_owner_full.lp` and
`oetu_omega_equiv_along_d0_owner_checks_full.lp` passes quietly and
warning-enabled. The active kernel adds no `unif_rule`; its four reflexive
observation clauses add no warning family and preserve 991/157 with zero
strict-LHS candidates. Eighteen positive and three negative diagnostics plus
an eight-positive/three-negative reviewer example cover exact Sigma
projections, both inverse/cell types and betas, a projected recursive
next-hom observation, absent package eta, and absent raw inverse cancellation.
The active catalog has 1,055 classified checks and zero unclassified entries.

**D0b Cat hom-action adequacy gate:**

Status: **completed/promoted (2026-07-15)** under
`OETU-OMEGA-EQUIV-ALONG`.

5. In an owner-position full-file candidate, construct the following from
   variable rather than reflexive evidence:

   ```text
   u : OmegaEquivAlong_{Cat_cat}(F)
   ------------------------------------------------
   omega_equiv_along_fapp1(u,x,y)
     : OmegaEquivAlong_{Cat_cat}(fapp1_func(F,x,y)).
   ```

6. Require the forward projection to be exactly `fapp1_func(F,x,y)`. Give the
   inverse the actual hom-category endpoints by conjugating/whiskering the hom
   action of a selected inverse functor with components of the higher inverse
   cells as required by their orientations; do not silently identify it with
   raw `fapp1_func(G,Fx,Fy)` for that selected inverse `G`, whose endpoints are
   at `G(Fx)` and `G(Fy)`.
   Exercise the induced left/right higher observations through one recursive
   rung.
7. Pass source-position subject reduction, later-source checking, changed-head
   warning/LHS comparison, both-order consumers, and bounded timing without a
   per-instance `unif_rule`. Record this as D0b general hom-action feasibility,
   not as the later `Core_incl_func` inverse/round-trip theorem. D0b is a
   pre-D1 gate only and does not postpone Candidate G or the earlier A/B/E0
   slices.

Completion evidence: the owner-position source/check pair
`oetu_omega_equiv_along_d0b_owner_full.lp` and
`oetu_omega_equiv_along_d0b_owner_checks_full.lp` passes quietly and
warning-enabled. The selected left inverse is
`Hom(eta_x,epsilon_y) o L_1`. The selected right inverse uses the two recursive
cells to build `L(b) <-> R(b)` endpoint comparisons before conjugating `R_1`.
The raw `L_1` and `R_1` endpoint typings are both negative controls. Both
returned higher cells are transparent packages whose forward/evidence
projections compute and whose evidence supports one further inverse
observation. No `unif_rule`, raw cancellation, or general corecursor is added.
Twenty-four positive and two negative diagnostics plus an eight-positive/
two-negative reviewer example are active. The 1,081-check catalog is fully
classified; warning/LHS inventories remain 991/157 and zero.

**D1 public normal-form migration:**

Status: **completed/promoted (2026-07-15)** jointly under
`OETU-OMEGA-EQUIV-ALONG` and `OETU-CAT-UNIV-DECODER`.

8. Replace the current opaque public `OmegaEquiv_C(x,y)` classifier by the
   promoted Sigma package and route the active public destructors through its
   fixed-map evidence.
9. Migrate opposite and Product generators without duplicating semantic
   bodies. Jointly with `OETU-CAT-UNIV-DECODER`, retype its canonical decoder
   domain/codomain and rerun its owned round trips, `path_to_hom` squares, and
   Product diamonds. This is migration validation, not duplicate decoder
   ownership inside Candidate D1.
10. Validate one concrete named equivalence declaration and the first MVP
   end-to-end next-hom univalence/action witness without a per-instance
   unification rule.
11. Compare the primary evidence propositionally with the old semantic
   `OmegaEquivFibre(F)` during compatibility staging, keeping property-
   valuedness separately statused.
12. Do not promote after D0, D0b, or telescope formation alone. Complete the
    recorded owner-position ladder through opposite, Product, decoder,
    integrated next-hom consumers, and the full warning/subject-reduction/
    performance audit in one D1 full-file candidate.

Completion evidence: the full-file source/check candidates
`oetu_omega_equiv_d1_owner_full.lp` and
`oetu_omega_equiv_d1_owner_checks_full.lp` pass quietly and warning-enabled at
their real owners. The public package is definitionally
`Sigma f, OmegaEquivAlong(f)`; all public observations route through evidence,
and stable evidence heads own opposite and Product computation. Fully explicit
reflexive indices created extra projection-order warnings, so the promoted
rules infer non-discriminating indices and retain only ten measured
observation-versus-reflexive-evidence overlap families. Each has a durable
both-order diagnostic, and removing the superseded public rule family improves
the inventory from 991/157 to 990/157. No new `unif_rule` is added.

The categorical decoder is retyped over the Sigma package and owns both named
propositional round trips, the derived contractible-fibre capability, the named
`cat_univalence_type_equiv`, selected-inverse agreement, the propositional
encoder/`path_to_hom` square, and Product decoder projections. The semantic
fibre comparison is deliberately only a one-sided retraction; public package
eta, reverse fibre eta, and property-valuedness remain negative/deferred. The
D0b-derived category-path witness has exact forward/evidence projections and
an iterable recursive cell. Forty-one positive and five negative active
diagnostics plus a twelve-positive/four-negative reviewer example cover the
slice. The 1,127-check catalog has 1,081 positive and 46 negative entries
across 31 areas with zero unclassified; all 15 source/check/example files pass,
health records 3.313s/4.411s for source/check and 5.677s for the D1 example,
the strict audit remains zero with 45 intentional slots across 27 clauses, and
`make check`, examples, catalog, TOC, warning summary, health, and CI pass.
Quiet logs end in `20260715-202501`/`202612`; warning-enabled logs end in
`20260715-202626`/`202912`.

Property-valuedness of the fixed-arrow evidence may remain a named theorem
prerequisite after formation and projection migration; it is required before
evidence fields are erased propositionally in `NCat` paths.

### Phase 8: Indexed `Adjunction(F,G)` Migration

Status: **completed/promoted (2026-07-15)** under
`OETU-ADJUNCTION-INDEXED`.

Start record: D1's 1,127-check, 990/157, zero-strict-LHS full gate is the
incoming baseline. After an unexpected interruption the entire existing
plan-scoped layer was found staged even though this agent issued no staging
command; the index is preserved and subsequent edits are kept as a distinct
unstaged layer whenever the environment permits. This slice must first
relocate and classify every active `Adjunction`, left/right view, unit/counit,
triangle, opposite, mate, profunctor, and reviewer-example consumer before an
owner-position candidate is built. Append-only feasibility is not promotion
evidence, and independently declared named operations do not justify their own
proof-time equations.

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
6. The owner/consumer inventory found no concrete preselected
   `myUnit`/`myCounit` declaration and hence no semantic backing for a
   proof-time comparison. Promotion deliberately adds none. Active negatives
   show that arbitrary named operations neither convert nor inherit the raw
   triangle; a later concrete declaration must carry agreement data or an
   explicitly trusted generated equation under `OETU-STRUCTURE-DECLARATION`.
   Ordinary observation-to-raw-operation runtime betas remain rejected.
7. No consumer needs existential recovery of unknown functors, so
   `AdjunctionPackage(R,L)` is not added. Reopen that packaging decision only
   for a concrete existential consumer.
8. Validate one concrete `J : Adjunction(F,G)`, both canonical-spelling
   triangles, opposite, and a mate computation. Also validate that the raw
   named-operation spelling remains a documented non-computing surface unless
   an elaborator explicitly restores the stable observations.

Completion evidence: the cumulative full-file source/check candidates and the
reviewer candidate pass quietly and warning-enabled at their real owners. The
active relation is indexed by `F,G`; compatibility views unfold directly to
the indices, all semantic consumers thread the indices, and stable unit/counit
heads remain the triangle discriminators. Opposite adjunction swaps to
`Op_func(G),Op_func(F)` and its functor views require no projection rules.
Minimizing the inferred outer opposite index slots avoids `Op_func` overlap
families and improves the inventory from 990/157 to 978/157, with the
`comp_fapp0` family unchanged at 400. The strict audit remains zero with 45
intentional slots across 27 clauses. Three positive and three negative active
diagnostics yield 1,133 checks across 32 areas with zero unclassified; the
expanded reviewer example checks both triangles, opposite involution, mate
cancellation, and the absent-operation-agreement boundary. Source/check health
is 3.473s/4.795s and the reviewer example is 3.730s. No new `unif_rule`, raw
projection beta, trusted operation postulate, or existential package is added.
The synchronized `make ci` gate passes all 15 files in 66.627s together with
source TOC, active-reference/header lints, strict LHS, and fresh catalog checks.

### Phase 9: Discreteness, Directed Dimension, And `OneCat`

Status: **discrete-category and directed-formation subgates completed/promoted
(2026-07-15)** under `OETU-DISCRETE-CAT` and `OETU-NCAT`. The theorem and
ordinary-iso lanes remain separately dependent as recorded in items 6--7.

1. Add `IsObjTruncCat` independently. **Completed/promoted 2026-07-15.** This is formation
   over the already active `IsTruncGrpd`; it does not follow from and must not
   be identified with recursive directed dimension.
2. Package `PathSym_A` as a fixed-map omega-equivalence or add a functor-level
   Core/opposite comparison only when a separate concrete consumer requires
   it. **Dependency revised 2026-07-15:** owner-position specialization showed
   that neither package is needed by the first `IsDiscreteCat` consumer;
   `Core_incl_func(C)` already carries the exact D0b evidence used below.
3. Implement the selected exact Product
   `IsSetGrpd(Obj(C)) ×
   OmegaEquivAlong_{Cat_cat}(Core_incl_func(C))` as `IsDiscreteCat(C)`.
   **Completed/promoted 2026-07-15.** The Product has direct constructor and
   projection computation, retains both factors, and has no package eta or
   evidence erasure.
4. Instantiate the promoted D0b hom-action construction at
   `Core_incl_func(C)`, obtaining fixed-map equivalence of
   `core_incl_hom_func(C,x,y)` for arbitrary endpoints. Check that its object
   action is `path_to_hom`, and expose the specialized arrow-to-path inverse
   with both round trips. Do not duplicate this consequence as a discreteness
   field. If this later `Core_incl_func` specialization cannot derive the
   promised round trips from promoted D0b evidence, block discreteness and
   explicitly revise the evidence boundary rather than hiding the failure in
   Phase 9; do not retroactively treat generic D0b as unimplemented.
   **Completed/promoted 2026-07-15.** `core_incl_hom_func` has definitionally
   exact `path_to_hom` object action; projected core evidence gives
   `discrete_core_homwise`, its selected left inverse gives `hom_to_path`, and
   the public recursive left cell plus a generic left/right comparison give
   both coherent directions. No third package field, rewrite, or `unif_rule`
   is needed. Thirteen positive/four negative diagnostics and a six-positive /
   two-negative reviewer example pass at 978/157 warnings with zero strict-LHS
   candidates. Quiet logs end in `20260715-213519`/`213628`/`213709`; warning
   logs end in `20260715-213724`/`213729`. The synchronized full CI gate passes
   all 16 files in 80.043s, followed by source TOC, active-reference/header,
   strict-LHS, and fresh-catalog checks.
5. Add `CatDim`, recursive `IsNCat`, `NCat(n)`, `ZeroCat`, and `OneCat` now
   that the homwise gate passes. **Completed/promoted (2026-07-15).** The
   package retains evidence and has no runtime eta;
   `one_cat_hom_discrete` projects the exact successor evidence and
   `one_cat_hom_core_homwise` consumes `discrete_core_homwise` between
   parallel arrows. Eighteen positive/five negative diagnostics and a seven-
   positive/three-negative reviewer example pass. Quiet logs end in
   `20260715-215526`/`215625`/`215659`; warning-enabled logs end in
   `20260715-215723` and preserve 978/157 warnings with zero strict-LHS
   candidates and 45 intentional slots across 27 clauses. The catalog has
   1,173 classified checks across 34 areas, and health checks all 17 files
   with source/check/example timings 4.358s/5.552s/4.442s. The synchronized
   CI gate passes all 17 files in 78.267s with every repository-integrity
   check.
6. State and prove or stage `IsNCat(n,C) -> IsObjTruncCat(n,C)` with its exact
   univalence/evidence-truncation dependencies. Formation does not silently
   discharge this theorem. **Staged with concrete prerequisites:** kernel
   indices first need a declared `CatDim -> TruncLevel` bridge (zero maps to
   `trunc_zero`, successor commutes), now selected as the bounded
   `OETU-NCAT-DIM-TRUNC-INDEX` subtask. The proof additionally needs truncation
   invariance under the categorical decoder/fixed-map equivalences plus
   truncation of the recursive equivalence evidence. None is supplied by the
   formation rules; continue the implication under `OETU-NCAT-OBJ-TRUNC` only
   after those closure owners exist.
   **Index subgate completed/promoted (2026-07-15):**
   `cat_dim_trunc_level` has exact zero/successor equations, five positive/one
   negative active diagnostics, and four positive/one negative reviewer
   additions. Quiet logs end in `20260715-225901`/`230019`, warning logs end in
   `20260715-225915`, warnings remain 978/157, and the strict audit remains
   zero with 45 intentional slots across 27 clauses. The implication negative
   remains active.
   The synchronized CI gate passes all 19 files in 87.056s.
   **General and categorical invariance subgates completed/promoted
   (2026-07-15):** `is_trunc_grpd_type_equiv` supplies ordinary invariance;
   `omega_equiv_along_obj_type_equiv` maps `Obj` over the fixed-map decoder
   path, and `is_obj_trunc_cat_equiv_type_equiv` consumes the general theorem.
   Their synchronized gates pass 20 files in 97.398s and 21 files in 98.423s
   with unchanged 978/157 warnings and zero/45/27 strict audit.
   **Sigma-closure subgate completed/promoted (2026-07-16):**
   `is_trunc_sigma` now supplies the correct same-level total-space theorem
   from both base and fibre hypotheses with 25-file CI in 136.09s. The
   remaining theorem blocker is now solely representation-sensitive:
   `OmegaEquivAlong_D0` is opaque and has no general evidence eliminator, so
   the required recursive evidence truncation/property theorem first needs a
   certificate representation or independently justified evidence-path owner.
   **Conditional induction subgate completed/promoted (2026-07-16):**
   the missing global evidence-property theorem is now an explicit uninhabited
   classifier rather than an implicit gap. Given it,
   `ncat_obj_trunc_from_evidence_prop` computes at zero to the discrete
   object-set field and at successor through homwise induction,
   `is_trunc_sigma`, and `cat_univalence_type_equiv`. Eleven positive/four
   negative diagnostics and an eight-positive/four-negative reviewer pass at
   unchanged 971/157 warnings and zero/45/27 audit. No `unif_rule` is added;
   the typed proof-time negative preserves capability provenance. This closes
   only the conditional theorem spine. The unconditional theorem still waits
   on an inhabitant of `OmegaEquivAlongEvidenceProp_D0`.
   **Dimension-indexed evidence-view follow-up completed/promoted
   (2026-07-16):** explicit `CatDim` recursion now observes the opaque
   certificate to a finite depth. Zero computes to Unit; successor retains
   both inverse arrows and recursively observes both selected D0 cells in the
   smaller-dimensional hom-categories. Exact projection, ZeroCat/OneCat,
   reflexivity, and one-way path-action controls pass at unchanged 971/157
   warnings and zero/45/27 audit. This representation result supplies no
   reverse decoder or inhabitant of the property capability. Full examples
   and synchronized 38-file CI pass with 201.708s measured checking time
   (212.59s wall time).
7. Introduce/derive ordinary `CatIsoUnivalence` only for `OneCat`, prove or
   defer the `OmegaEquiv`/`IsoEvidence` comparison there, migrate the remaining
   compatibility consumers, and retire the unscoped global claim. **Scoped
   replacement construction and global-capability retirement
   completed/promoted (2026-07-16); legacy decoder migration remains:**
   strict `IsoEvidence` derives recursive `OmegaEquiv`, a OneCat-scoped
   decoder, and the first decoder-after-encoder round trip without the frozen
   global assumption. Recursive cells now construct the directed comparison
   of separate omega left/right inverses, and discrete-hom adequacy converts it
   to a path without a new rewrite or proof-time equation. The right law is
   transported along that path; hom discreteness compares the two proof fields;
   nested-Sigma reconstruction proves the retract and second round trip. The
   resulting OneCat-indexed specified-inverse capability derives the scoped
   contractible-fibre `CatIsoUnivalence` and named `TypeEquiv`. The rejected
   global-classifier attempt proves that a wrapper around the frozen decoder is
   not the selected architecture. Proportional closeout is recorded under the
   three completed inverse-comparison, right-transport, and round-trip ledger
   rows. The follow-up retirement removes the unused arbitrary-`Cat`
   inhabitants/classifier, migrates generic `isotoid_cat` checking to the
   scoped inhabitant, and retains only the `iso_evidence_path` reflexive/Product
   computation whose replacement is a separate future slice.

### Phase 10: Public Equality, Structural Action, And Fibrancy Migration

Status: **historical registered-action subgate and first recursive-inductive
continuation completed/promoted (2026-07-16), with the P1/P2 cleanup migration
completed 2026-07-19**. Fibrancy/additional structured J and broad former
migration remain separate. The cleanup retires the unused dependent registry
in favor of direct `eq_apd` and presents every retained nondependent selection
as `PathActionRefinement` of canonical `path_map_func`; its living plan in
`INDEX.md` is the current authority.

1. Migrate one type former at a time from the prototype to public equality.
2. Replace old encode/decode implementations that became identity coercions.
3. Retain compatibility aliases only when they have real consumers.
4. Eliminate the two-reflexivity-normal-form Product boundary.
5. Promote structural action only through the selected registered-map
   architecture. **Completed/promoted (2026-07-15).**
   `ObsAction(f)` and `ObsDAction(s)` store a selected operation plus pointwise
   agreement with `eq_ap`/`eq_apd`. Identity acts by `p |-> p`; registered
   nondependent actions compose with J-derived semantic coherence;
   `path_record_action` handles open maps on arbitrary shaped paths and
   `path_record_witness_action` handles the dependent witness field. The
   agreement path is explicit next-dimensional data. Thirty-one positive/five
   negative diagnostics and a ten-positive/three-negative reviewer example
   pass; quiet logs end in `20260715-222426`/`222458`/`222521`, warning logs
   end in `20260715-222539`, warnings remain 978/157, the strict audit remains
   zero with 45 intentional slots across 27 clauses, and health checks 18
   files at source/check/example timings 3.675s/5.023s/4.156s. No rule or
   `unif_rule` is added. The synchronized CI gate passes all 18 files in
   86.300s with all repository-integrity checks.
   The 2026-07-16 recursive continuation registers `succ` after Nat equality
   exposes predecessor paths. `nat_succ_obs_action_map` computes as `p |-> p`;
   two direct, narrowly typed proof-time comparisons connect one stable basis
   independently to component and outer reflexivity, and generic `ind_eqr`
   derives arbitrary semantic agreement without assuming unification
   transitivity. Fourteen positive/five negative diagnostics and an eleven-
   positive/five-negative reviewer pass. Seven symbols and two `unif_rule`s add
   no runtime rewrite, preserve 971/157 warnings and zero/45/27 audit counts,
   and close synchronized 41-file CI at 1,694 checks/62 areas in 220.269s.
   These names and counts record the dated Phase 10 proof. Cleanup P2 later
   renamed the generic/Nat/Sum surface to `PathActionRefinement`, moved the Nat
   selection into the Nat extension, and retained the same proof-time bases
   without adding a rule or `unif_rule`.
6. Retain generic propositional `J` throughout. The action owner-position
   negatives show that no additional arbitrary-constructor beta follows from
   registration. Fibrancy therefore remains a prerequisite until a registered
   classifier/motive capability and one concrete sound runtime beta are
   selected. Promote additional runtime
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
   skeleton. The 2026-07-16 re-audit now claims this bounded skeleton.
   Candidate G completes the Empty/Unit/Bool/Nat subset, Candidate A
   completes named finite-record formation/elimination, and `OETU-H0-SUM`
   supplies the general binary-sum extension. Elementary/record observational
   identity, no-confusion, and higher action remain separate long-term tracks;
   their absence is not hidden inside the compatibility-skeleton claim.
   `OETU-OBS-BOOL` completes the
   first bounded elementary identity/no-confusion subgate: it covers only the
   visible Boolean constructor classifier matrix, preserves generic
   reflexivity/J/consumer ownership, and rejects proof erasure to `tt`.
   `OETU-OBS-UNIT` promotes the matching single-constructor case.
   `OETU-OBS-NAT` promotes the first recursive case together with the generic-
   J category/endpoint subject-reduction guard exposed by a proof-dependent
   motive. `OETU-OBS-SUM` promotes the separately bounded general visible-sum
   classifier matrix while retaining outer reflexivity provenance; synchronized
   33-file CI closes this conservative elementary lane.
   `OETU-OBS-NAT-SUCC-ACTION` then supplies the first recursive-inductive
   registered action with explicit semantic coherence and retained runtime
   proof provenance. No successor-specific J beta, canonicity, metatheoretic
   no-confusion, or semantic-model claim follows.
3. Preserve the promoted standard Pi compatibility surface, including runtime
   diagonal beta, related-input action, propositional eta, and an active
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
   evidence property-valuedness. General `TypeEquiv` invariance and its fixed-
   map categorical object consumer, general monotonicity, and evidence
   property-valuedness are complete. General dependent-Pi preservation is now
   also completed through the stable `is_trunc_pi` owner, and same-level
   dependent-Sigma closure is completed through `is_trunc_sigma`, and
   truncated-universe carrier/evidence path control is completed through
   `trunc_grpd_carrier_path_type_equiv`; restricted ambient-univalence
   composition is completed through `trunc_grpd_univalence_type_equiv`; and
   `is_trunc_type_equiv` plus `is_trunc_grpd_universe` complete the expected
   package-universe successor-level theorem. Recursive omega-equivalence
   evidence truncation remains blocked on the opaque certificate
   representation.
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
   rewrite/unification and performance evidence. **Selected 2026-07-16:** the
   finite named view is active; the warning-neutral direct rule is rejected
   because self-universe normalization recursively reopens itself beyond the
   20-second bound.
2. Define shaped universe reflexivity, structural transport/action, and the
   exact boundary between retained generic J and additional structured-J
   computation. The groupoid view selects `type_equiv_refl` and the existing
   propositional decoder transport theorem while leaving public equality/J
   generic; any direct public shaped-J migration requires a different,
   recursion-safe universe boundary. The categorical direct owner selects
   canonical package reflexivity but retains generic `eq_refl` as a distinct
   proof head; collapsing it breaks an existing generic-action consumer.
3. Integrate `TypeEquiv`, the selected reverse decoder, both round trips, and
   Product/Pi/Sigma action diamonds without duplicating semantic bodies. The
   groupoid view subgate is promoted through aliases of those exact owners;
   its synchronized 34-file CI passes.
4. Repeat the design question at the categorical universe using the promoted
   fixed-map `OmegaEquivAlong`/Sigma package, while preserving the
   unstratified-policy warning. **Selected/promoted 2026-07-16:** the direct
   canonical owner is finite and warning-neutral at the currently opaque
   certificate boundary; `CatPathView` names its exact normal form and no
   proof-time equation is added.
5. Test at least one nontrivial universe transport through the next hom level,
   warning behavior, subject reduction, and bounded full-suite performance.
   The D0b-backed `cat_path_fapp1` and reflexive Product consumer are active;
   synchronized 35-file CI closes the gate with 165.477s of measured checking
   time (171.88s wall time).
6. Treat external glue/bisimulation/cubical mechanisms as comparison baselines;
   select a native Emdash mechanism from local owners and record why it is
   sufficient. **Completed/promoted 2026-07-16:** the finite
   one-layer `OmegaEquivAlongPathView_D0` of the four existing observations is
   warning-neutral and bounded; direct recursive evidence equality is rejected
   by both owner-position and self-normalization timeouts. The view has only a
   one-way evidence-path encoder, so this is not yet extensionality,
   property-valuedness, or a truncation theorem. Synchronized 36-file CI closes
   the view at 1,555 checks in 186.423s of measured checking time (193.35s wall
   time).

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
its D0 owner gate, D0b Cat hom-action gate, and D1 public migration.

### Candidate A: record convention only

```text
one dependent record probe;
constructor and projection beta;
generated eliminator audit;
no active equality or univalence change.
```

Promotion status: **active (2026-07-15)**; realized as
`PathRecord_grpd(A)`/`PathRecordData(A)` with `Struct_path_record`, three named
dependent projections, and `path_record_ind`. The full owner-position source
and suite, warning comparison, strict LHS audit, active checks, catalog,
examples, health, and CI pass. The probe-only nested-Sigma comparison is also
warning-neutral but is not a second active owner. Runtime record eta and
observational equality remain negative/deferred respectively.

Candidate A start record (2026-07-15): staged changes are empty; the unstaged
worktree contains only the completed Candidate G kernel/check/report/catalog/
health synchronization and this ledger transition, with no unrelated user
change detected. Candidate G's full `make ci` is the passing incoming baseline.
The selected bounded representative is a named `PathRecord_grpd(A)` whose
native one-constructor carrier stores `src,dst : τ A` and
`witness : src = dst`; public projections and elimination retain the decoded
classifier in their signatures. A nested Sigma presentation is comparison
evidence only and will not be promoted as a second public owner.

Candidate A completion record (2026-07-15): public signatures retain
`τ(PathRecord_grpd A)`, constructor applications expose the single inductive
parameter exactly once, projection LHSs infer that non-discriminating
parameter, and the strict audit finds no new candidate. Nine active checks
cover decoding, construction, all projections, dependent witness typing,
eliminator formation/beta, and absence of runtime eta. No `unif_rule`, record
equality rule, or generated-code facility was added.

### Candidate B: truncation property kernel

```text
TruncLevel;
IsTruncGrpd recursion;
IsPropGrpd / IsSetGrpd / IsGroupoidGrpd;
formation and reduction checks;
no packaged universes and no reflector.
```

Promotion status: **active (2026-07-15)**. The property kernel sits immediately
after `IsContr`, passes full owner-position/source/suite and proportional gates
warning/LHS neutral, and has 15 classified active diagnostics. Direct Pi
equality introduces no new warning family. Packaged universes remain the next
slice; stronger closure facts retain the statuses in the closure ledger.

Candidate B start record (2026-07-15): staged changes remain empty and the
unstaged worktree contains only the completed Candidates G/A synchronization
plus this ledger transition; no unrelated user change is present. Candidate
A's full `make ci` is the incoming baseline. The selected owner is immediately
after active `IsContr` and its projections, so the recursive base and Pi path
step depend only on already-declared semantic owners. Packaged
`TruncGrpdU(n)` from the combined append-only probe is explicitly excluded.

Candidate B completion record (2026-07-15): the active successor equation
exposes the double decoded Pi directly, and a typed consumer applies arbitrary
evidence to two endpoints. The base equation exposes `IsContr`. No helper
postulate, `unif_rule`, same-level universe claim, proof-erasure rule, or
reflector was added. Final owner-position quiet logs end in
`161037`/`161050`; warning logs end in `161102`/`161111`.

### Candidate C: shaped record reflexivity and reflexive `J`

Promotion status: **active (2026-07-15)**. The selected owner-position source,
complete retargeted diagnostics, active kernel/checks, reviewer example,
warning/LHS audits, catalog, health report, TOC, and full CI pass.

Candidate C start record (2026-07-15): staged changes remain empty; the
unstaged worktree contains only the plan-scoped promoted G/A/B/Phase-3/E0/E1
implementation and synchronized diagnostics/examples/reports/generated
artifacts, with no unrelated user change detected. E1's full `make ci` is the
incoming baseline. The bounded task is the owner-position shaped-reflexivity
core named by `Current-Implementation-Slice`; structural action, fibrancy,
arbitrary-constructor dependent `J`, fixed-map equivalence, and decoder work
remain excluded.

```text
one stable former-specific shaped-reflexivity head;
path projection beta rules;
specialized reflexive ind_eqr beta;
registration with generic composition and symmetry;
dependent-record and nested-former extension probe;
no claim yet of arbitrary structured-path action.
```

Candidate C completion record (2026-07-15): `PathRecordPathView(A,r,s)` reuses
the nested dependent-Sigma path owner, while literal record reflexivity
selects the stable `PathRecordPathRefl(A,r)` head. Ordered source and dependent-
tail projection betas pass subject reduction; a specialized `ind_eqr` rule
computes only on that reflexive head. One nested `PathRecord(PathRecord(A))`
consumer passes. The literal-`eq_refl` rule inventory found exactly the generic
J owner, PathSym, Core inclusion, two shared path units, `idtoiso_cat`, and
`idtoequiv_cat` as compatible consumers; rigid Sigma/Pi/Product/groupoid-
universe cases are not registered.

The initial inferred-category candidate passed at 995/157. Retaining explicit
PathSym source/target categories removes four spurious overlaps, and five
evidence-led inferred-slot refinements remove five replaceable advisories from
the pre-refinement variant. The final 991/157 inventory contains 17 new
classified critical-pair reports: seven literal/shaped owner joins, eight
typed post/pre/naturality unit diamonds, and two impossible Core-to-displayed-
target orientations covered by one negative typing control. Strict LHS audit
is zero with 45 annotated slots across 27 clauses. Forty active diagnostics
(36 positive and four negative) and five reviewer assertions retain the
no-runtime-record-eta, no-raw-structured-J, and no-arbitrary-PathSym-action
boundaries. No `unif_rule` or arbitrary structural action was added.

Final quiet owner-position logs end in `20260715-173016`/`173421`; warning-
enabled logs end in `20260715-173024`/`173435`. The active warning summary,
catalog of 939 checks, health report, examples, TOC, and full CI pass. The
five LHS refinements are the two generic Sigma projection payloads and the
non-discriminating classifier slots in the Core/ordinary-iso/omega-equivalence
registrations. Structural action, fibrancy, arbitrary-constructor dependent
`J`, and broad former migration remain separate gates.

### Candidate D0/D0b/D1: primary fixed-map omega-equivalence and Sigma package

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

**D0b Cat hom-action adequacy gate:**

```text
u : OmegaEquivAlong_{Cat_cat}(F)
------------------------------------------------
omega_equiv_along_fapp1(u,x,y)
  : OmegaEquivAlong_{Cat_cat}(fapp1_func(F,x,y));
forward projection exactly fapp1_func(F,x,y);
endpoint-correct conjugated/whiskered inverse, not the selected inverse G's raw fapp1_func(G,Fx,Fy);
left/right higher observations through one recursive rung;
variable-evidence, source-position, both-order, warning/LHS, and timing checks;
no per-instance unif_rule and no public OmegaEquiv migration yet.
```

D0b moves the capability needed by later discreteness forward to the D1
boundary. It is stronger than formation or reflexivity: the probe consumes a
variable certificate and must construct the induced inverse using the higher
inverse-cell components needed to repair its endpoints. It is weaker than the
now-promoted Phase-9 `IsDiscreteCat` result: the D0b gate itself neither
specializes to `Core_incl_func` nor proves the named `hom_to_path` coherent
directions. It belongs to the existing
`OETU-OMEGA-EQUIV-ALONG` task and is not a new implementation lane.

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

Risk was medium to high for D0 and D0b and high for D1's public normal-form
migration; all three gates are now promoted.
D0 and D0b pass their owner-position gates. The independent neutral
certificate, transparent package, exact projections, recursive observations,
reflexive computation, one next-hom observation, and endpoint-correct
variable-evidence hom action are active without a warning or LHS delta. The
older append-only telescope and transitional bridge remain only historical
feasibility evidence. D1 then passes the public full-file candidate with the
promoted D0/D0b layer: evidence-routed observations, opposite/Product owners,
categorical decoder round trips, one-sided fibre comparison, and the integrated
next-hom witness are active at 990/157 with zero strict-LHS candidates.
Property-valuedness remains a separate theorem and the
`IsOmegaEquivArrow` name is not used as evidence for it.

### Candidate E0/E1: `Path_cat` focused repair

**E0 shared composition and collapse removal:**

```text
promote/refine shared comp_fapp0 category-level composition candidate;
add two narrow eq_refl unit bridges;
retain oriented pre/post runtime action owners and proof-time comparison;
derive their four eq_refl action units through typed general comparisons and
retain negative runtime-conversion controls rather than four runtime bridges;
retain J-derived eq_trans only as a propositional reference;
remove the self-opposite collapse without yet claiming a replacement symmetry.
```

E0 is promoted. The shared-composition source/suite first passed with
1,091 rather than the active 1,109 unjoinable-pair reports, and the same
candidate with the collapse removed passes with 1,072. The attempted fold to
the postcomposition head is rejected because associativity consumers time out.
The final Phase-3-rebased owner passes at 1,072/159 with zero strict-LHS
candidates and all active gates. A four-action-runtime-bridge variant measured
1,077/165; it is rejected in favor of typed general-comparison witnesses plus
four non-conversion controls. E0 is therefore the active semantically honest
intermediate and does not wait for E1.

**E1 symmetry-functor core:**

```text
PathSym_A : Path(A)^op -> Path(A), with identity object action;
path_sym := its capped arrow action;
one narrow path_sym(eq_refl) -> eq_refl bridge;
generic-functorial anti-composition, with no duplicate specialized law;
J-derived propositional agreement with eq_sym and propositional involution;
pointwise Core_incl_func/opposite square;
no runtime double-symmetry cancellation;
fixed-map OmegaEquivAlong packaging only through the promoted D1 boundary.
```

E1's core is promoted. The rebased full source and migrated suite pass quietly
and warning-enabled at 974/159 with no strict-LHS candidate. The twelve new
warning blocks are classified: six typed action/naturality diamonds join, two
Product cases are ill-typed, and six mapped-`DefIso` cases led to a generic
endpoint minimization that removes 110 reports. Open strict/J-derived symmetry
and open double symmetry remain non-convertible as intended. The later
functor-level natural comparison and fixed-map equivalence package remain
prerequisites for `OneCat`/discreteness, but public shaped-path registration
may now proceed.

Risk: E0 and the E1 core closed at low residual risk; medium to high for E1's
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

Outcome: **completed/promoted (2026-07-15)**. The indexed relation, both
triangle patterns, transparent functor views, opposite, mate and weighted
consumers, and runtime-erasure controls pass full owner-position checks. Outer
opposite functor-index slots are inferred, improving warnings by twelve while
leaving the triangle family unchanged; strict LHS remains zero. An opaque
left/right projection plus `unif_rule` is not the runtime design. The inventory
found no declaration-backed named unit/counit, so no per-instance equation is
installed; the structure-declaration ledger owns any later concrete bridge.
The stable observations remain the runtime computational owners.

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

Promotion status: **active (2026-07-15)**. The intended-owner full-file source
and complete retargeted suite pass quietly and warning-enabled, the promoted
source/checks pass all proportional gates, and warning/LHS inventories are
neutral. The decoded eliminator signatures and generated-recursor bodies are
the selected owners. The slice does not upgrade those facts to observational
identity, canonicity, or an initial/coproduct/NNO universal property, and it
does not claim a general sum former.

### Candidate G follow-up: general binary sum

Promotion status: **completed/promoted (2026-07-15)** under `OETU-H0-SUM`.

The selected bounded extension is one native parametrized binary-sum carrier,
its decoded `Sum_grpd(A,B)` classifier, left and right introductions, and a
dependent eliminator facade routed through the generated induction principle.
Both constructor betas and a conversion-level left/right non-collapse control
must pass at the elementary owner. This surface does not claim observational
sum identity, a no-confusion theorem, higher action, canonicity, or a
categorical coproduct universal property.

Start record (2026-07-15): the incoming active source/check baseline passes
`EMDASH_TYPECHECK_TIMEOUT=60s make check`. The completed registered-action
subgate has 1,209 classified checks, an unchanged 978/157 warning inventory,
zero strict-LHS candidates, and an 18-file CI result of 86.300s. The worktree
contains the staged and unstaged plan-scoped cumulative redesign plus the
untracked action reviewer example; staged `examples/discrete_category.lp`
also has a pre-existing extra EOF blank-line diagnostic under
`git diff --cached --check`, which this slice preserves rather than folding
into its semantic work. No active or scratch owner currently defines a
general binary sum, so a fresh full-file owner-position source/check pair will
be named before promotion.

Promotion evidence (2026-07-15): `tmp/probes/oetu_h0_sum_owner_full.lp` and
`tmp/probes/oetu_h0_sum_owner_checks_full.lp` pass quietly in logs ending
`20260715-224632` and warning-enabled in logs ending `20260715-224650`.
`examples/binary_sum.lp` passes in the log ending `20260715-224846`. Six
positive/one negative diagnostics and eight positive/two negative reviewer
statements bring the active catalog to 1,216 checks across 36 areas and the
health inventory to 19 files. Warnings remain 978/157 and the strict audit
remains zero with 45 intentional slots across 27 clauses. The active source is
byte-identical to the owner candidate; the check candidate differs only by its
temporary import. The first grouped-binder candidate failed because generated
`ind_SumData` generalized `B`; the focused signature probe selects separate
`(A : Grpd) (B : Grpd)` parameter binders. Only `τ(Sum_grpd(A,B))` adds an
explicit rule, and it creates no warning family. Full CI was the closure gate;
the synchronized gate passes all 19 files in 88.539s.

### Selected `OETU-OBS-MVP` follow-up: visible Boolean identity

Status: **completed/promoted (2026-07-16)** under `OETU-OBS-BOOL`.

The first elementary observational-equality subgate uses the already-active
Boolean former because its visible constructor pairs give the smallest closed
classifier/no-confusion matrix:

```text
false = false  -> Unit_grpd
true  = true   -> Unit_grpd
false = true   -> Empty_grpd
true  = false  -> Empty_grpd.
```

The owner-position probe must select the reflexive proof presented at the two
same-constructor cases, make generic J compute on that proof, and inventory
every generic consumer that can see literal `eq_refl` before or after the
selected Boolean presentation. Candidate C's PathRecord registry identifies
the likely families—shared path-category units, PathSym, Core inclusion, and
the ordinary/omega categorical encoders—but the actual Bool owner probe, not
analogy alone, decides which registrations are necessary. Both orders must
join, open `b : Bool_grpd` must retain generic equality/reflexivity, and the
cross-constructor cases must decode to `Empty_grpd` without claiming global
canonicity or equality reflection. Arbitrary Boolean action/fibrancy,
the separately promoted guarded Nat identity, general-sum identity, and broad
public migration remain distinct rows.

Start record (2026-07-16): Product provenance is the passing incoming gate at
1,360 classified checks across 46 areas, 972/157 warnings, zero/45/27 strict
audit, 29 measured files, and synchronized CI in 189.90s. The cumulative
redesign stack is staged; Product kernel/check/report changes and its new
reviewer example are an unstaged layer that this slice preserves. The three
pre-existing staged extra-EOF blank-line findings remain unrelated. No
Boolean equality rule or proof-time comparison is currently active.

Promotion evidence (2026-07-16): the first owner-position version selected
native `tt` as the reflexivity normal form and therefore added twenty
equations: the four classifiers, two reflexivity collapses, two direct-`tt` J
betas, and closed two-constructor registrations at PathSym, Core inclusion,
both shared path units, `idtoiso_cat`, and `idtoequiv_cat`. It passes quietly
in source/check logs ending `20260716-033031`/`033238`, but warning-enabled
logs ending `20260716-033254` increase unjoinable reports from 972 to 1,014.
All 42 new reports are accounted for: 14 are the seven generic literal-
reflexivity consumers at two constructors; 12 are PathSym strict-composition,
post/pre-action, and naturality families; 16 are the corresponding Core
families, including four untyped displayed-target combinations. Supporting
that orientation would require a large consumer-diamond suite solely to erase
generic reflexivity provenance.

The revised owner decision retains `eq_refl Bool_grpd false/true` as the
runtime proof forms and promotes only the four classifier equations. This is
the Product-provenance policy applied to elementary equality: reducing the
proof's classifier to `Unit_grpd` does not justify replacing the proof head by
the unrelated native inhabitant `tt`. All existing generic J, PathSym, Core,
path-unit, and encoder betas continue to compute on literal reflexivity; raw
`tt` receives no second beta. No `unif_rule` is installed because no concrete
typed consumer requires a proof-time identification, and a negative typed-
reflexivity probe records that trust boundary. The selected full-file source/
check probes pass quietly in logs ending `20260716-034236`/`034410` and with
warnings in `20260716-034258`/`034311`, preserving 972/157 and zero/45/27
audit results. Twenty-two positive/eleven negative diagnostics bring the
catalog to 1,393 checks across 47 areas. The focused reviewer log ends in
`20260716-034631` with eleven positive/six negative statements. Health checks
30 files with a 17,728-line/731-symbol/571-rule/51-unification-rule kernel and
1,293 positive diagnostics; synchronized 30-file CI passes in 143.199s.

### Selected `OETU-OBS-MVP` follow-up: visible Unit identity

Status: **completed/promoted (2026-07-16)** under `OETU-OBS-UNIT`.

The next dependency-ready elementary case applies the promoted Boolean
provenance decision to the single visible Unit constructor:

```text
tt = tt -> Unit_grpd.
```

The bounded owner-position probe may add only this classifier equation unless
measured typed evidence invalidates the policy. Generic
`eq_refl Unit_grpd tt` must remain the reflexivity normal form, generic J/path/
Core/path-unit/categorical-encoder consumers must keep their existing literal-
reflexivity computation, and raw `tt` must not silently gain a second J or
encoder beta or a proof-time comparison. An open `u : Unit_grpd` retains the
primitive equality classifier. Unit eta/canonicity, arbitrary Unit action or
fibrancy, and Empty/Nat/general-sum observational identity are excluded.

Start record (2026-07-16): the incoming Boolean gate passes 30-file CI in
143.199s with 1,393 classified checks across 47 areas, 972/157 warnings, and
zero/45/27 strict audit. The cumulative redesign remains split across staged
and unstaged plan-scoped layers, the two reviewer examples remain untracked,
and the three unrelated staged extra-EOF findings are preserved. No Unit
equality classifier or proof-time comparison is active.

Promotion evidence (2026-07-16): the single classifier equation is the full
promoted kernel delta. Generic literal reflexivity already supplies J,
PathSym, Core inclusion, both path-category units, and both categorical
encoder betas, so no consumer registry is needed. Raw `tt` remains a separately
typed inhabitant of the reduced classifier but receives neither runtime
computation nor a proof-time equation. The cumulative full-file source/check
probes pass quietly in logs ending `20260716-040227`/`040238` and with warnings
in `20260716-040248`/`040259`, preserving 972/157 warnings and zero/45/27
audit results. Ten positive/nine negative diagnostics bring the catalog to
1,412 checks across 48 areas. The focused reviewer log ends in
`20260716-040444` with seven positive/six negative statements. Health checks
31 files with a 17,737-line/731-symbol/572-rule/51-unification-rule kernel and
1,303 positive diagnostics; synchronized 31-file CI passes in 153.385s.

### Selected `OETU-OBS-MVP` follow-up: recursive visible Nat identity

Status: **completed/promoted (2026-07-16)** under
`OETU-OBS-NAT`, jointly with the discovered `OETU-OBS-J-SR-GUARD`
prerequisite.

The next elementary case is the first recursive classifier matrix:

```text
zero   = zero   -> Unit_grpd
zero   = succ m -> Empty_grpd
succ n = zero   -> Empty_grpd
succ n = succ m -> n = m.
```

The promoted owner adds exactly these four classifier equations. Generic
`eq_refl Nat_grpd zero` and `eq_refl Nat_grpd (succ n)` retain proof
provenance even when their classifiers reduce to Unit or recursively to
`n = n`; they are not collapsed to `tt` or `eq_refl Nat_grpd n`. Open
endpoints retain primitive equality. Nat canonicity or induction-derived
no-confusion as a metatheorem, arbitrary Nat action/fibrancy, general-sum
identity, and proof-time comparison without a concrete typed consumer remain
excluded.

Start record (2026-07-16): the incoming Unit gate passes 31-file CI in
153.385s with 1,412 classified checks across 48 areas, 972/157 warnings, and
zero/45/27 strict audit. The staged/unstaged plan-scoped stack and unrelated
three staged extra-EOF findings are preserved. No Nat equality classifier or
proof-time comparison is active.

Owner-position correction (2026-07-16): the first four-equation-only source
candidate passed quiet checks and retained 972/157 warnings, but its recursive
classifier made `eq_refl Nat_grpd n` a term of the reduced successor path
classifier. The pre-existing beta

```text
ind_eqr _ u (eq_refl _) -> u
```

left category and endpoint inferred, so it also fired on predecessor
reflexivity. The focused `NatJProbeMotive` is injective in its proof index;
Lambdapi accepted `nat_j_predecessor_probe` at the predecessor-indexed result,
then `compute` normalized it to `lambda n u, u`, whose branch is indexed by
outer successor reflexivity. A separate `assertnot` confirms that `u` does not
inhabit the declared predecessor-indexed result. Because Unit, Boolean, and
Nat closed path classifiers can all reduce to `Unit_grpd`, the same beta also
admitted foreign elementary `eq_refl` heads. Quiet/warning success alone was
therefore not sufficient evidence; the classifier-only architecture is
rejected for loss of subject reduction.

Selected correction: generic J now repeats both category and reflexive
endpoint:

```text
@ind_eqr A y _ u y (@eq_refl A y) -> u.
```

These inferred slots are real subject-reduction guards under the SOP. Normal
outer zero/successor reflexivity still computes, while native `tt`, foreign
Unit/Boolean/Nat reflexivity, and predecessor reflexivity stay stuck. The
change needs no Nat registry and no `unif_rule`; a proof-time equation would
not repair an ill-typed runtime beta and no typed proof-erasure consumer exists.
It also removes the old generic-J/PathRecord shaped-reflexivity critical pair,
improving warnings from 972/157 to 971/157.

Evidence and synchronized state: rejected unguarded quiet source/check logs
end in `20260716-041943`/`042647`; unguarded warning logs both end in
`20260716-042708`; the proof-dependent counterexample log ends in
`20260716-043035`. Selected guarded quiet source/check logs end in
`20260716-043247`/`043414`, guarded warning logs end in
`20260716-043427`/`043428`, and the reviewer log ends in
`20260716-043749`. The Nat area has 23 positive/11 negative checks, the
separate J-guard area has four negative checks, and the reviewer example has
11 positive/eight negative statements. The catalog has 1,450 classified
checks across 50 areas; audit remains zero/45/27; health checks 32 files with
a 17,753-line/731-symbol/573-rule/51-unification-rule kernel and 1,326 positive
diagnostics. Synchronized 32-file CI passes in 151.336s.

### Selected `OETU-OBS-MVP` follow-up: general visible binary-sum identity

Status: **completed/promoted (2026-07-16)** under
`OETU-OBS-SUM`.

The next elementary classifier matrix is parameterized by component
groupoids:

```text
inl(a) = inl(a') -> (a =_A a')
inl(a) = inr(b)  -> Empty_grpd
inr(b) = inl(a)  -> Empty_grpd
inr(b) = inr(b') -> (b =_B b').
```

The bounded owner-position probe may add only these four equations. Generic
outer `eq_refl (sum_inl a)` and `eq_refl (sum_inr b)` retain proof provenance
even when their classifiers reduce to component equality; component
reflexivity is not identified with the outer proof. The promoted generic-J
category/endpoint guard is a prerequisite and must be exercised with foreign
and component reflexivity plus a proof-dependent motive, not assumed from the
Nat result. Existing outer-reflexivity path/Core/unit/encoder consumers must
continue to compute without a sum registry. Open sum endpoints retain
primitive equality. The slice excludes sum canonicity or induction-derived
no-confusion as a metatheorem, arbitrary sum action/fibrancy, categorical
coproduct structure, Empty observational identity, and proof-time comparison
without a concrete typed consumer.

Start record (2026-07-16): the incoming guarded Nat gate passes 32-file CI in
151.336s with 1,450 classified checks across 50 areas, 971/157 warnings, and
zero/45/27 strict audit. The staged/unstaged plan-scoped stack and unrelated
three staged extra-EOF findings are preserved. No general-sum equality
classifier, registry, or proof-time comparison is active.

Final owner decision and evidence (2026-07-16): the active owner adds exactly
the four equations above. The equality-classifier slot is inferred from the
constructor endpoints. Same-tag clauses retain only the component-classifier
index used on the RHS; the unused opposite summand and all mixed-tag indices
are inferred. The first type-correct spelling kept six of those reconstructible
constructor variables and raised Lambdapi's replaceable advisories from 157 to
163 without changing critical pairs. The minimized spelling restores 971/157
warnings and zero/45/27 strict audit while preserving all 35 diagnostics.

Generic outer inl/inr reflexivity remains distinct from component reflexivity
at runtime and under a typed `eq_refl` proof-time probe. Normal outer J,
PathSym, Core/path-to-hom, both unit orientations, and both categorical
encoders compute; component reflexivity receives none of those endpoint-
guarded betas. The focused injective `SumJProbeMotive` confirms that the
component-reflexivity J application stays stuck and its outer branch does not
inhabit the component-indexed result. No sum registry or `unif_rule` is added.

Initial quiet source/inherited-check logs end in `20260716-045922`/`045931`;
the complete diagnostic candidate passes in `20260716-050156`; the
pre-minimization warning logs both end in `20260716-050248`. Final minimized
quiet source/check logs both end in `20260716-050336`, warning-enabled logs
both end in `20260716-050351`, the subject-reduction log ends in
`20260716-050426`, and the reviewer log ends in `20260716-050744`. Twenty-four
positive/eleven negative diagnostics bring the catalog to 1,485 checks across
51 areas; the reviewer example has 12 positive/eight negative statements.
Health checks 33 files with a 17,777-line/731-symbol/574-rule/51-unification-
rule kernel and 1,350 positive diagnostics. Final synchronized CI passes with
161.044s of measured checking time
(167.96s wall time), closing `OETU-OBS-SUM`.

### Selected Phase-13 follow-up: groupoid-universe identity view

Status: **completed/promoted with synchronized CI (2026-07-16)** under
`OETU-UNIVERSE-EQUALITY-GRPD-VIEW`.

The immediate H0/H1/Omega0 corpus and the conservative visible-constructor
lane are now synchronized, while the other incomplete rows have explicit
missing triggers: recursive omega-equivalence evidence needs a certificate
representation, OneCat ordinary-iso univalence needs that evidence comparison,
additional structured J needs a concrete fibrancy consumer, declaration
bridges need a real named instance, and truncation reflectors need a theorem
consumer. The first dependency-ready independent row is therefore the bounded
Phase-13 groupoid-universe comparison already anticipated by
`OETU-UNIVERSE-EQUALITY`.

The owner probe compares:

```text
A =_{Grpd_grpd} B  ->  TypeEquiv(A,B)
```

as a direct public classifier equation against a named
`GrpdPathView(A,B)` fallback. The fallback must route its encode/decode maps
and both propositional round trips through `idtoequiv_grpd`,
`grpd_equiv_path`, and the promoted decoder theorems rather than copying their
semantic bodies. The direct candidate must be placed immediately after the
`Grpd_grpd` decoding owner and checked against literal universe reflexivity, the guarded
generic J beta, `coe_grpd`, Product/Pi/Sigma universe paths and decoder
diamonds, subject reduction, warning deltas, and bounded full-file timing.

Start record (2026-07-16): `OETU-OBS-SUM` closes at 1,485 classified checks
across 51 areas, 33 measured files, 971/157 warnings, zero/45/27 strict audit,
and synchronized CI with 161.044s measured checking time (167.96s wall time).
The active source has no `Grpd_grpd` equality rule and no named
`GrpdPathView`; the existing decoder already supplies both directions and
propositional round trips. No new `unif_rule` is selected: one will be
considered only for a concrete typed proof-time consumer with an explicit
trust class. This slice excludes categorical-universe identity, public
structured-action/additional-J claims, recursive certificate redesign,
OneCat iso-univalence, HITs/reflectors, and metatheory.

Owner decision and evidence (2026-07-16): placing the direct rule before
`τ(Obj Grpd_cat) -> Grpd` fails subject reduction because its endpoints are not
yet known to decode as classifiers; that rejected log ends in
`20260716-053144`. After the decoding rule, a spelling headed by reducible
`Grpd_grpd` passes but adds one alias-unfold critical pair (972/157). The
canonical `(Obj Grpd_cat)` spelling passes the full source/check suite and is
warning-neutral at 971/157; quiet source/check logs end in
`20260716-053346`/`055048`, and warning logs in `20260716-053345`/`053447`.

The canonical direct rule is nevertheless rejected. Computing
`τ(@= Grpd_grpd Grpd_grpd Grpd_grpd)` recursively expands the new
`TypeEquiv(Grpd_grpd,Grpd_grpd)` body, whose internal fibre equalities reopen
the same public universe equation; the 20-second probe times out in
`20260716-053636`. Baseline public self-equality and standalone
`TypeEquiv(Grpd_grpd,Grpd_grpd)` controls both finish in
`20260716-053720`, because their nested public equalities remain opaque. This
is a concrete unstratified-recursion blocker, not a warning-count veto.

The promoted fallback defines `GrpdPathView(A,B)` transparently as
`TypeEquiv(A,B)`, canonical view reflexivity as `type_equiv_refl(A)`, and
routes encode/decode, both propositional inverse laws, and transport agreement
through the existing groupoid decoder. Product computation, Pi action, and
same-base Sigma formation reuse existing owners. Seventeen positive/seven
negative diagnostics and a fourteen-positive/five-negative reviewer example
are active. Selected view quiet source/check logs end in
`20260716-053946`/`054135`, warning logs in `20260716-054151`/`054233`, finite
self-view normalization in `20260716-054151`, scratch reviewer evidence in
`20260716-054341`, and the active reviewer in `20260716-054558`. Seven
semantic aliases add no rule or `unif_rule`; warnings remain 971/157 and the
strict audit remains zero/45/27. The catalog has 1,509 checks across 52 areas;
health checks 34 files with a 17,838-line/738-symbol/574-rule/51-unification-
rule kernel and 1,367 positive diagnostics. Synchronized 34-file CI passes
with 182.160s of measured checking time (189.18s wall time), closing the row.

### Selected Phase-13 follow-up: direct categorical-universe identity

Status: **completed/promoted with synchronized CI (2026-07-16)** under
`OETU-UNIVERSE-EQUALITY-CAT-DIRECT`.

The categorical decoder, public fixed-map `OmegaEquiv` Sigma package, Product
generator, and iterated next-hom action are already promoted, so Phase 13 item
4 is dependency-ready. The bounded owner question compares

```text
A =_{Obj(Cat_cat)} B  ->  OmegaEquiv(Cat_cat,A,B)
```

as a direct classifier equation after the `Cat` universe decoder against a
finite named `CatPathView(A,B)` that aliases that exact package. Both
candidates must route reflexivity, encode/decode, both propositional round
trips, Product computation, and at least one next-hom consumer through
`omega_equiv_refl`, `idtoequiv_cat`, `omega_equiv_path`, the canonical decoder
theorems, and D1 rather than duplicating bodies. Owner-position source/check
probes, a self-universe normalization control, warnings, strict LHS audit, and
bounded full-suite timing decide whether direct equality is safe. The active
incoming baseline is the closed groupoid view: 1,509 checks across 52 areas,
34 measured files, 971/157 warnings, zero/45/27 strict audit, and synchronized
CI with 182.160s measured checking time (189.18s wall time). No `unif_rule` is
selected without a concrete typed proof-time consumer and explicit trust
classification. This slice excludes a stratified direct-groupoid retry,
additional structured J/fibrancy, recursive certificate redesign,
OneCat iso-univalence, HITs/reflectors, and metatheory.

Owner decision and evidence (2026-07-16): the classifier-only direct rule at
the canonical post-`OmegaEquiv` owner passes the full inherited source/check
suite in logs ending `20260716-060812`/`060824`; its focused signature passes
in `20260716-060849`. Unlike the groupoid `TypeEquiv` rule, computing
`τ(@=(Obj Cat_cat,Cat_cat,Cat_cat))` terminates in `20260716-060824` at a
Sigma of endofunctors and opaque `OmegaEquivAlong_D0` evidence. Canonical
warning-enabled source/check logs end in `20260716-060935` at unchanged
971/157. Replacing `(Obj Cat_cat)` by reducible `Cat_grpd` adds exactly one
alias-unfold report (972/157) in `20260716-061218`, so the canonical spelling
is selected.

A second comparison rejects global reflexivity collapse. Rewriting
`eq_refl(Obj Cat_cat,A)` to `omega_equiv_refl(Cat_cat,A)` passes source-only
checking but makes the inherited check suite fail at
`omega_equiv_along_obj_path` in `20260716-061303`: the inner category path
reduces before the outer generic `eq_ap` beta can see literal reflexivity. Its
warning log `20260716-061331` rises to 974/157. The direct classifier therefore
retains generic `eq_refl` provenance, just as the visible elementary
classifiers do; canonical package reflexivity is a second explicit witness and
receives no arbitrary structured-J beta.

The promoted interface names `CatPathView(A,B)` as the exact public normal
form, routes encode/decode and both propositional inverse laws through the
canonical categorical decoder, exposes the selected functor and certificate,
and proves the existing path-to-hom square through an alias. Product action
decodes both inputs, applies generic action/transitivity, and re-encodes once,
so canonical reflexive inputs compute. `cat_path_fapp1` consumes the package
certificate directly through D0b and remains iterable at the next hom level.
Selected quiet source/check logs end in `20260716-061546`/`061859`, warning
logs in `20260716-061725`, finite self/Product normalization and the scratch
reviewer in `20260716-061859`, and the active reviewer in
`20260716-062228`. Twenty-two positive/eight negative diagnostics and a
fifteen-positive/six-negative reviewer are active. Twelve semantic symbols,
one classifier rule, no `unif_rule`, unchanged 971/157 warnings, and zero/
45/27 strict audit are measured. The catalog has 1,539 checks across 53 areas;
health checks 35 files with a 17,989-line/750-symbol/575-rule/51-unification-
rule kernel and 1,389 positive diagnostics. The full reviewer sweep passes,
and synchronized CI passes with 165.477s of measured checking time (171.88s
wall time), closing the row. Replacing the opaque fixed-arrow certificate is
an explicit reopen trigger for self-universe normalization; this promotion
makes no stratification or consistency claim.

### Selected Phase-13 follow-up: fixed-arrow evidence observation/path view

Status: **completed/promoted with synchronized CI (2026-07-16)** under
`OETU-OMEGA-EQUIV-EVIDENCE-VIEW`.

The categorical direct owner exposes the exact point at which normalization
currently stops: `OmegaEquivAlong_D0(C,x,y,f)` is opaque, while four stable
observations expose selected left/right inverse arrows and recursive
left/right cell packages. The bounded next comparison builds a nested
Sigma/Product observation record from exactly those owners and defines its
one-layer path view without duplicating their semantic bodies. At the actual
D0 owner it compares that finite view with a direct public equality classifier
whose recursive cells can reopen fixed-arrow evidence equality. Reflexive and
self-normalization controls, the inherited D0/D1/decoder/Product/next-hom
suite, warnings, strict LHS audit, and bounded timing decide the boundary.
This slice adds no property-valuedness/truncation theorem and does not change
the certificate representation. A `unif_rule` is considered only for a real
typed proof-time consumer with an explicit trust class.

Owner decision and evidence (2026-07-16): the finite owner source passes in
the log ending `20260716-093253`, and its focused signature/projection/
reflexivity/encoder probe passes in `20260716-093344`. The inherited full
check suite passes in `20260716-093545`; final finite warning-enabled source
and check logs end in `20260716-093558`/`094030` at unchanged 971/157, and the
strict audit remains zero/45/27. The one-layer self-universe view and
observation normalize in `20260716-093726`.

The direct recursive classifier is rejected. At the same D0 owner it makes
the source exceed 30 seconds in `20260716-093406`; a warning-enabled 20-second
rerun ending `20260716-093504` expands recursive D0/D1 overlap families but
does not finish. The independent append-only canonical self-universe control
also exceeds 20 seconds in `20260716-093654`. This is a measured recursive
normalization/owner-interaction boundary, not a warning-count veto.

The promoted interface has five semantic symbols, no rule or `unif_rule`.
Thirteen positive/three negative diagnostics cover the observation type, four
exact projections, path view/reflexivity/one-way encoding, reflexive inverse
observations, a D0b next-hom projection, and the missing direct equality/eta
boundaries. The ten-positive/three-negative scratch reviewer passes in
`20260716-094135`, and the active reviewer passes in `20260716-094320`.
The catalog has 1,555 checks across 54 areas; health checks 36 files with an
18,104-line/755-symbol/575-rule/51-unification-rule kernel and 1,402 positive
diagnostics. The full reviewer suite passes. Synchronized CI passes with
186.423s of measured checking time (193.35s wall time), closing the row. A
reverse decoder or recursion-safe certificate representation is still the
prerequisite for evidence extensionality/property-valuedness.

### Selected Phase-9 follow-up: conditional directed object truncation

Status: **completed/promoted with synchronized CI (2026-07-16)** under
`OETU-NCAT-OBJ-TRUNC-CONDITIONAL`.

Closure of the finite evidence view sharpens, rather than removes, the
certificate blocker. The full `IsNCat(n,C) ->
IsObjTruncCat(cat_dim_trunc_level(n),C)` proof has two separable parts. Its
recursive mathematical spine is now dependency-ready: the discrete base is
`is_discrete_cat_obj_set`; the successor applies the induction hypothesis to
`Hom_cat(C,x,y)`, raises proposition-valued fixed-arrow evidence to the native
dimension level, closes the public `OmegaEquiv(C,x,y)` Sigma package with
`is_trunc_sigma`, and transports the result back to object equality through
`cat_univalence_type_equiv`. What remains unavailable is an inhabitant of the
global capability asserting `IsPropGrpd(OmegaEquivAlong_D0(C,x,y,f))` for all
fixed arrows.

The promoted slice names that capability but does not inhabit or postulate it.
`prop_is_trunc_cat_dim` and `ncat_obj_trunc_from_evidence_prop` are stable heads
with two disjoint dimension equations each. The zero theorem branch ignores
the unavailable capability and returns `is_discrete_cat_obj_set`; the successor
retains it in every evidence fibre. Exact owner/signature/check logs end in
`20260716-101016`/`101323`/`101446`; final warning-enabled owner/check logs end
in `101349`/`101510` at unchanged 971/157. The strict audit remains zero/45/27,
and the scratch reviewer passes in `101606`.

Eleven positive/four negative active diagnostics exercise the capability type,
native proposition lift, exact theorem branches, `ZeroCat` and `OneCat`
consumers, the bare-evidence boundary, and the absence of capability erasure.
The eight-positive/four-negative active reviewer passes in the log ending
`20260716-101743`. Its typed `eq_refl` negative confirms that no proof-time
equation identifies outputs with different capability inputs; no `unif_rule`
is justified or added. The catalog has 1,570 checks across 55 areas; health
checks 37 files with an 18,173-line/758-symbol/577-rule/51-unification-rule
kernel and 1,413 positive diagnostics. The full reviewer sweep passes.
Synchronized CI passes with 198.816s measured checking time (206.34s wall
time), closing the row. The slice excludes reverse evidence decoding,
observation eta, unconditional evidence property/truncation, and ordinary-iso
univalence.

### Selected certificate follow-up: dimension-indexed deep evidence view

Status: **completed/promoted (2026-07-16)** under
`OETU-OMEGA-EQUIV-EVIDENCE-DIM-VIEW`.

The conditional object-truncation theorem isolates the missing global
certificate-property inhabitant. The next bounded representation step can
advance that dependency without repeating the rejected unstratified rule.
For `h : IsNCat(n,C)`, define a deep observation classifier by structural
recursion on `n`: the zero observation is `Unit_grpd`; at `cat_succ n` it stores
the selected left/right inverse arrows and, for each recursive D0 cell package,
its selected forward cell together with the `n`-level observation of that
cell's fixed-arrow evidence in the corresponding hom-category. Every recursive
call therefore decreases the explicit `CatDim` index.

An observation map from `OmegaEquivAlong_D0(C,x,y,f)` must reuse the existing
inverse and cell owners at every rung. A named path view may compare the two
finite deep records, with canonical reflexivity and one-way `eq_ap` action of a
genuine evidence path. Zero- and one-dimensional controls must normalize
within the bound. This is a representation/view probe, not a reverse decoder,
eta theorem, evidence-property proof, public equality migration, or replacement
of the opaque certificate. A `unif_rule` is considered only for a concrete
typed proof-time consumer with stable heads and an explicit trust class.

Owner decision and bounded evidence (2026-07-16): the active classifier has
exactly the zero/structurally decreasing successor equations above, and the
active map calls the four D0 inverse/cell owners at every successor rung. The
first-class `OmegaEquivDimObservation_D0` cell package avoids duplicating a
cell body. All inverse, forward-cell, and recursive-evidence projections
compute; ZeroCat maps to `tt`, and the OneCat recursive cell observation also
maps to `tt`. The named path view, reflexivity, and genuine-path encoder pass;
public equality, the one-layer view, arbitrary path collapse, proof erasure,
and typed proof-time identification of distinct certificates remain negative.
Quiet owner/signature/inherited-check logs end in `20260716-104217`/`104520`/
`104613`; warning logs end in `104636`; scratch/active reviewer logs end in
`104802`/`104928`. Seventeen positive/five negative diagnostics and a twelve-
positive/four-negative reviewer add six symbols and two two-equation rule
families, no `unif_rule`, preserve 971/157 warnings and zero/45/27 audit, and
produce 1,592 classified checks across 56 areas plus a 38-file health snapshot
with an 18,452-line/764-symbol/579-rule/51-unification-rule kernel and 1,430
positive diagnostics. Full examples pass, and synchronized 38-file CI records
201.708s measured checking time (212.59s wall time), closing the row.

### Implemented elementary follow-up: componentwise binary-sum action

Status: **completed/promoted (2026-07-16)** under
`OETU-OBS-SUM-ACTION`.

The elementary-inductive adequacy row now has visible constructor equality for
Unit, Boolean, Nat, and general sums, while registered structural action has a
single shaped PathRecord consumer. General sums are the smallest independent
next former: the active eliminator can define `sum_map(f,g)`, and the four
visible endpoint cases give a componentwise selected action from
`u : ObsAction(f)` and `v : ObsAction(g)`, with mixed cases eliminated from
`Empty_grpd`.

The nontrivial gate was semantic agreement with generic `eq_ap`. Outer sum
reflexivity deliberately remains a distinct runtime proof from component
reflexivity, so the selected owner adds no runtime collapse. A direct
two-`eq_ap` proof-time candidate failed because transparent `eq_ap` unfolds to
generic `ind_eqr` before the rule can fire. The promoted architecture instead
introduces one stable reflexive action basis per tag and two narrowly typed
former-specific `unif_rule`s per basis: one direct comparison with normalized
component reflexivity and one with the exact outer-`ind_eqr` normal form. Each
direct comparison is exercised by typed `eq_refl` and classified as a
semantically justified structural-action law. The arbitrary component theorem
uses retained ordinary component J and explicitly composes the two direct
paths; it does not rely on experimental unification transitivity.

`sum_obs_action_map` delegates equal-tag paths to the supplied registrations,
returns the impossible mixed-tag input, and `sum_obs_action_coherence`
eliminates that input in mixed cases. Same-tag coherence composes the supplied
`obs_action_agrees` proof with `sum_map_inl_eq_ap` or
`sum_map_inr_eq_ap`. Runtime basis/action conversion, direct transitive
proof-time collapse, open selected/semantic action equality, and package
collapse remain negative. The owner-position feasibility, full owner, and
inherited-check logs end in `20260716-112405`, `20260716-114250`, and
`20260716-113027`; warning runs end in `20260716-113036` and
`20260716-113051`, and the active reviewer log ends in
`20260716-113631`. Twenty-one positive/six negative diagnostics and a
thirteen-positive/four-negative reviewer pass. Thirteen symbols plus four
proof-time equations add no runtime rewrite rule, preserve 971/157 warnings,
and retain the zero/45/27 strict-audit result. The catalog has 1,619 checks
across 57 areas; health measures 39 files with an 18,883-line/777-symbol/
579-rule/55-unification-rule kernel and 1,451 positive diagnostics. Full
examples pass. Synchronized 39-file CI passes with 129.250s of measured
checking time, closing the promotion gate. The slice still excludes
arbitrary-constructor J/fibrancy, proof erasure,
no-confusion/canonicity, categorical coproduct structure, and broader former
migration.

### Implemented recursive-inductive follow-up: Nat successor action

Status: **completed/promoted with synchronized 41-file CI in 220.269s
(2026-07-16)** under `OETU-OBS-NAT-SUCC-ACTION`.

The post-compatibility-MVP dependency audit selected the smallest recursive
former action still missing from the active surface. Nat equality already
computes

```text
@= Nat_grpd (succ m) (succ n)  -->  @= Nat_grpd m n,
```

so the selected successor action can retain the exposed predecessor proof
`p`. Semantic agreement with generic `eq_ap(succ)` is not judgmental at the
reflexive base: generic component `eq_refl(n)` and outer
`eq_refl(succ n)` deliberately retain distinct proof provenance. A runtime
collapse would violate that policy, and experimental unification transitivity
cannot be used as an implicit proof.

The accepted Nat owner introduces the stable
`nat_succ_ap_basis(n)` and exactly two direct proof-time comparisons, one with
each backed reflexivity presentation. Each narrowly typed `unif_rule` is
exercised independently with typed `eq_refl` and trust-classified as a generic
semantically justified former-action law. The internal paths
`nat_succ_component_basis` and `nat_succ_basis_outer` are then composed in the
reflexive branch of generic `ind_eqr`, deriving
`nat_succ_eq_ap(p) : p = eq_ap(succ,p)` for arbitrary predecessor paths.
`nat_succ_obs_action_map` selects `p |-> p`, its coherence is that theorem, and
`nat_succ_obs_action` packages both through the existing `obs_action_intro`
owner. Double successor action iterates through generic registered-action
composition.

Runtime basis/component and basis/outer conversions, direct proof-time
component/outer transitivity, selected-map/generic-action conversion, and
package collapse remain negative. No runtime rewrite, successor-specific J
beta, proof erasure, Nat canonicity, or metatheoretic no-confusion claim is
added. Owner/check quiet logs end in `141904`/`142047`; warning logs end in
`142057`/`142329`; and the active reviewer log ends in `142721`. Fourteen
positive/five negative diagnostics and an eleven-positive/five-negative
reviewer pass. Seven symbols and two `unif_rule`s preserve 971/157 warnings and
zero/45/27 audit counts. The catalog has 1,694 checks across 62 areas; health
measures 41 files with a 19,988-line/808-symbol/581-rule/58-unification-rule
kernel and 1,507 positive diagnostics. Full examples and synchronized CI pass
with 220.269s measured checking time.

### Directed one-category follow-up: scoped ordinary-iso univalence

Status: **full scoped construction completed/promoted with synchronized
40-file CI in 109.546s (2026-07-16)** under `OETU-ONECAT-ISO`,
`OETU-ONECAT-ISO-INVERSE-COMPARE`, `OETU-ONECAT-ISO-RIGHT-TRANSPORT`, and
`OETU-ONECAT-ISO-ROUNDTRIP`.

The now-retired global `cat_iso_univalence(C)` and decoder-oriented companion
were legacy arbitrary-category staging assumptions. A `OneCat` wrapper that
simply applied either global declaration to `ncat_carrier(X)` would have
renamed, not repaired, the architecture. The selected bounded replacement
instead starts from the promoted `OneCat` package,
discrete-hom evidence, D0/D0b/D1 fixed-arrow representation, and canonical
categorical univalence. Owner-position construction shows that ordinary
inverse equations do provide the recursive D0 cells needed for the forward
comparison: `iso_evidence_omega_along_D0(i)` uses `iso_evidence_from(i)` for
both inverse observations and encodes the ordinary left/right inverse
equations through `idtoequiv_cat` for the two recursive cells. The transparent
public package is `iso_evidence_omega_equiv(i) : OmegaEquiv(C,x,y)`.

A proposed runtime fold from reflexive ordinary evidence to canonical D0
reflexivity added four unjoinable reports and was rejected. The selected
comparison is instead one narrowly typed `unif_rule` between the two backed
reflexive evidence heads. A typed `eq_refl` exercises it, while runtime package
and decoder comparisons remain negative. Generic J then proves
`iso_evidence_omega_equiv(idtoiso_cat(p)) = idtoequiv_cat(p)` without relying
on unification transitivity. At a `OneCat` carrier, `one_cat_iso_path(X,i)`
uses the canonical omega decoder, and `one_cat_iso_path_idtoiso(X,p)` proves
the first decoder-after-encoder round trip propositionally. The then-active
global ordinary-iso assumptions are not used by any of these owners and are
retired after the full scoped construction closes.

The original requirement that this bounded slice immediately deliver a full
`CatIsoUnivalence` capability was therefore refined. Its first focused reverse
probe exposed a larger prerequisite rather than a missing forward constructor:
an arbitrary omega-equivalence stores distinct `left_inv` and `right_inv`
arrows. Its right recursive cell decodes at `f o right_inv`, whereas an
ordinary `IsoEvidence` package choosing `left_inv` needs a right law at
`f o left_inv`. That result selected the separately bounded
`OETU-ONECAT-ISO-INVERSE-COMPARE` continuation.

The continuation is now implemented at the intended D0 and OneCat owners. The
first direct `Hom_func` composite failed with both unit presentations and the
middle associativity comparison unresolved; this is the log ending `123757`
and rules out an architecture that silently depends on proof-time unification
transitivity. The selected construction exposes both recursive cell arrows,
whiskers the reverse right cell by the left inverse and the forward left cell
by the right inverse through the existing stable post/precomposition functors,
and joins their middle endpoints by an explicit propositional associator sent
through `path_to_hom`. Their composite is
`omega_equiv_along_left_to_right_D0`. `one_cat_omega_inverse_path` then uses
hom discreteness to obtain equality of the selected inverse arrows. Canonical
reflexive comparison reduces to the identity 2-cell through generic owners;
the decoded path remains runtime-distinct from `eq_refl`. No rewrite or
`unif_rule` is added.

Twelve positive/six negative active diagnostics and a nine-positive/four-
negative reviewer pass. Five symbols, two two-equation rule families, and one
proof-time comparison preserve 971/157 warnings and the zero/45/27 strict
audit. The catalog has 1,637 checks across 58 areas; health measures 40 files
with a 19,062-line/782-symbol/581-rule/56-unification-rule kernel and 1,463
positive diagnostics. Final owner/signature/inherited-check logs end in
`20260716-120633`/`121149`/`120824`; warning logs end in `120226`/`120834`,
the intentional reverse failure ends in `120916`, and the reviewer log ends
in `121326`. Full examples and synchronized 40-file CI pass with 281.823s of
measured checking time. Ordinary isomorphism data and recursive
omega-equivalence evidence remain distinct, and no unrestricted comparison,
proof erasure, postulate, new arbitrary-`Cat` consumer, or broad decoder
rewrite is introduced.

The inverse-comparison continuation adds nine positive/four negative active
diagnostics and six positive/three negative reviewer statements, bringing the
reviewer to fifteen positive/seven negative statements. Eight symbols preserve
971/157 warnings and zero/45/27 audit. Selected quiet/warning owner logs end in
`124247`/`125119`; inherited quiet/warning checks end in `125136`/`125140`, and
the reviewer log ends in `124544`. The catalog has 1,650 checks across
59 areas; health measures 40 files with a 19,373-line/790-symbol/581-rule/56-
unification-rule kernel and 1,472 positive diagnostics. Full examples and
synchronized CI pass with 139.872s measured checking time. This result removed
the inverse-comparison blocker and made right-law transport and reconstruction
the dependency-ready continuation.

That continuation is now active at the intended owners. The decoded left and
right recursive cells yield ordinary laws; `one_cat_omega_inverse_path`
retargets the right law to the selected left inverse, and
`one_cat_omega_iso_evidence` reconstructs ordinary evidence. OneCat hom
discreteness supplies paths between both proof fields, while the existing
nested-Sigma structural path owner proves
`one_cat_omega_iso_lift_retract`. Encoder agreement then combines with the
categorical decoder round trip and this retract to prove the reverse law
`one_cat_idtoiso_iso_path`.

The first attempt to package that law as the legacy
`CatIsoUnivalenceByDecoder` failed in the focused log ending `132624`: that
classifier hardcodes `iso_evidence_path`, so reusing it would silently select
the frozen arbitrary-category decoder. The accepted design introduces the
OneCat-indexed `OneCatIsoUnivalenceByDecoder`, derives
`one_cat_iso_univalence_by_decoder`, `one_cat_iso_univalence`, and
`one_cat_iso_type_equiv`, and keeps the legacy capability runtime-distinct.
The discrete path probe ends in `132315`, the complete definitions first pass
in `132729`, final owner quiet/warning logs end in `133706`/`133718`, inherited
suite logs end in `133745`/`133751`, and the expanded reviewer ends in
`134212`. Ten semantic symbols add no rewrite and no `unif_rule`; warnings
remain 971/157 and the audit remains zero/45/27. Thirteen positive/two negative
diagnostics bring the catalog to 1,678 checks across 61 areas, while the
reviewer has 32 positive/12 negative statements. Health passes across 40 files
with a 19,883-line/804-symbol/581-rule/56-unification-rule kernel and 1,495
positive diagnostics, and full examples pass. Synchronized CI records
109.546s measured checking time. The construction is closed: the ordinary-iso
lane's remaining work is concrete legacy-consumer migration/retirement rather
than a missing scoped univalence theorem. The immediate inventory finds the
global capability inhabitants and decoder classifier unused outside
compatibility diagnostics, while `iso_evidence_path` itself still owns
reflexive/Product computation; that evidence selects a narrower retirement
slice rather than deleting the still-consumed decoder.

### Candidate H: standard Pi/function-extensionality compatibility

Promotion status: **active (2026-07-15)**. Stable Pi owners, the classified
proof-time reflexive basis, generic-J eta, the reviewed quasi-inverse theorem
capability, contractible-fibre evidence, and the `TypeEquiv` package are
promoted with owner-position diagnostics.

Candidate H start record (2026-07-15): staged changes remain empty; the
unstaged worktree contains only the plan-scoped promoted G/A/B/Phase-3/E0/E1/C
implementation and synchronized diagnostics/examples/reports/generated
artifacts, with no unrelated user change detected. Candidate C's full
`make ci` is the passing incoming baseline: 939 classified checks, 991/157
warning inventory, and zero strict-LHS candidates. This slice is selected
next because it is dependency-ready and unblocks three named consumers—H1
compatibility, arbitrary structural path compatibility, and truncation-
evidence property-valuedness. The bounded owner-position probe must retain the
related-input Pi path, classify the reflexive proof-time basis semantically,
and construct real contractible-fibre `IsEquivMap` evidence; it excludes the
downstream consumers listed in `Current-Implementation-Slice`.

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

Final owner decision and evidence (2026-07-15): `PiHapply` and `PiFunext` are
stable injective heads immediately after the existing Pi path view. Their
application rules retain the related-input owner and make only pointwise
`happly(funext(h))` beta computational. Generic `ind_eqr` derives
`pi_funext_eta`; its reflexive base is one two-rigid-head `unif_rule`, selected
as a generic semantically justified proof-time structural law. The earlier
transparent append-only presentation reduces that equation independently.
At the real owner position, however, a transparent public owner unfolds before
the stable equation can match and fails the generic-J eta base even when the
same rule is present. This selects stable heads rather than weakening the
trust classification or adding a runtime eta fold.

The first attempted internal half-adjoint fibre construction also exposed a
real Lambdapi boundary: after `eq_ap` normalization, the reflexive Pi equation
was needed inside a nested pointwise Pi path, and experimental unification did
not reuse it transitively. A whole-function runtime eta, a bare-variable proof-
time eta, and a brittle expanded nested pattern were rejected. Instead the
reviewed generic theorem capability `is_equiv_map_by_inverse` converts explicit
left/right inverse paths to the already-active contractible-fibre
`IsEquivMap`. This is opaque logical proof authority, matching the existing
constructor-specific `*_is_equiv` capabilities, not a runtime evaluator. One
narrow projection selects each fibre centre as `(g(b),right(b))`; the
contraction stays opaque. Thus `pi_happly_type_equiv` has computing forward,
inverse, and right-path projections, while its generic left contraction does
not duplicate `pi_funext_eta` by conversion.

The owner-position source/check probes pass quietly in logs ending
`20260715-181059`/`181546` and warning-enabled in logs ending
`20260715-181407`/`182118`. Twenty-nine active diagnostics (24 positive and
five negative) cover formation, related-input action, owner-first and
application-first shaped-reflexivity orders, typed proof-time firing,
pointwise beta, propositional eta, explicit quasi-inverse fields, selected
fibre centre, `IsEquivMap`/`TypeEquiv` projections, non-runtime whole-function
beta/eta, arbitrary structured-Pi J, and opaque-contraction separation. The
reviewer Pi example has ten positive assertions and one negative. The warning
inventory remains 991/157; strict LHS audit remains zero with 45 annotated
slots across 27 clauses; the 968-check catalog has zero unclassified entries,
and all proportional gates pass.

Candidates G/A/B/C/H, Phase 3's packaged truncated universes, both Phase 4
path-category slices, `OETU-STRUCTURAL-PATH-COMPAT`,
`OETU-TYPE-EQUIV-ALGEBRA`, and `OETU-GRPD-UNIV-DECODER` are promoted. D0,
D0b, and D1 are likewise promoted. Fixed-map packaging of `PathSym_A` remains
a separately owned optional consumer; the core-inclusion specialization and
exact `IsDiscreteCat` base are now promoted. Candidate F is promoted; Phase 9
now selects recursive `IsNCat`/`OneCat` formation and must not be mixed with an
unrelated module split.

### H1 structural Sigma and dependent-record path compatibility

Promotion status: **active (2026-07-15)**. Arbitrary propositional Sigma
encode/decode round trips, transparent PathRecord maps and round trips,
constructor-reflexive computation, and a nested dependent-record consumer are
promoted with owner-position diagnostics.

Start record (2026-07-15): staged changes remain empty; the unstaged worktree
contains only the plan-scoped promoted redesign slices and their synchronized
diagnostics/examples/reports/generated artifacts, with no unrelated user
change detected. Candidate H's 968-check, 991/157, zero-strict-LHS gate is the
incoming baseline. This slice will place arbitrary encode/decode round trips
at the existing `SigmaPathView` and `PathRecordPathView` owners, test
reflexive computation and one nested dependent path telescope, and use the
promoted Pi equivalence only where equality between path-valued functions is
actually required. It will not add global runtime eta, arbitrary structured-
path J, fibrancy, record generation, or downstream equivalence/univalence
algebra. Fresh full-file owner-position source and retargeted-check probes are
required before active edits.

Completion record (2026-07-15): the full-file owner candidates are
`tmp/probes/oetu_structural_path_compat_owner_full.lp` and
`tmp/probes/oetu_structural_path_compat_owner_checks_full.lp`. The first Sigma
encode-after-decode base attempted to reuse the stable
`sigma_path_encode_decode_refl` theorem inside generic J. It failed at the real
owner in the log ending `20260715-183614`: the proof-time Sigma-reflexivity
comparison does not propagate transitively through the nested decode term.
The promoted design instead separates a literal-reflexivity base,
`sigma_path_encode_decode_eq_refl`, proved by Sigma elimination. Final quiet
source/check logs end in `20260715-183641`/`184008`; warning-enabled logs end
in `20260715-183843`/`184023`.

Sigma retains its existing componentwise/J encode and decode owners. Both
arbitrary composites are propositions, constructor-exposed reflexivity
computes, and the two open runtime-eta controls remain negative. Public
PathRecord equality already reduces to `PathRecordPathView`, so its named maps
are transparent identity views rather than a second pass through Sigma
decode/encode. Both named round trips, shaped reflexivity, the dependent-tail
observer, and a nested `PathRecord(PathRecord(A))` case compute. No rewrite or
unification rule was added. Twenty-one active diagnostics (19 positive and two
negative) and a reviewer example with nine positive assertions and one
negative cover the boundary. The 989-check catalog classifies all 21 together
with zero unclassified checks; warnings remain 991/157, and the strict audit
remains zero with 45 annotated slots across 27 clauses.

### Completed H1 slice: ordinary `TypeEquiv` algebra

Promotion status: **active (2026-07-15)**. Identity, symmetry, categorical-
order composition, their derived contractible-fibre closure evidence, and
map-level unit/associativity computation are promoted with owner-position
diagnostics.

Start record (2026-07-15): staged changes remain empty; the unstaged worktree
contains only the plan-scoped redesign implementation and synchronized
diagnostics/examples/reports/generated artifacts, with no unrelated user
change detected. The structural-path slice's 989-check, 991/157,
zero-strict-LHS gate is the incoming baseline. This slice will inventory and
place identity, symmetry, and composition at the existing `TypeEquiv` and
contractible-fibre `IsEquivMap` owners, prove or explicitly classify the
required closure evidence, and test projections and associativity/unit-facing
consumer shapes proportionally. It excludes univalence decoders and round
trips, transport/universe-action squares, direct universe equality,
truncation-evidence property-valuedness, fixed-map omega-equivalence,
structural action/fibrancy, and indexed adjunction migration. Fresh full-file
owner-position source and retargeted-check probes are required before active
promotion.

Completion record (2026-07-15): the full-file owner candidates are
`tmp/probes/oetu_type_equiv_algebra_owner_full.lp` and
`tmp/probes/oetu_type_equiv_algebra_owner_checks_full.lp`. The initial source
probe failed in the log ending `20260715-185659` because `eq_ap` was invoked
without the explicit source endpoints required by its fully explicit `@`
spelling; supplying those actual composite endpoints made the derived left and
right paths typecheck without changing the architecture. Final quiet
source/check logs end in `20260715-185714`/`185827`, and both warning-enabled
logs end in `20260715-185840` with the unchanged 991/157 inventory.

The selected design retains the existing stable `type_equiv_refl` owner and
adds transparent `type_equiv_sym` and `type_equiv_comp(eBC,eAB)` Sigma
packages. Symmetry and composition form explicit `EquivByInverse` data from
the selected inverse paths and route `IsEquivMap` closure through the reviewed
`is_equiv_map_by_inverse` theorem capability. No rewrite or unification rule
was added. Forward maps, selected inverse maps, selected right paths,
forward-map units, and forward-map associativity compute. The opaque
contraction-derived left projection, double symmetry, and identity-composite
package eta remain negative. Twenty-nine active diagnostics (25 positive and
four negative) and a reviewer example with nine positive assertions and two
negative cover the boundary. The 1,018-check catalog classifies all 29 in the
new algebra area with zero unclassified checks; the strict audit remains zero
with 45 annotated slots across 27 clauses. No notation change was required.

### Completed H1 slice: groupoid univalence decoder coherence

Promotion status: **active (2026-07-15)**. The canonical decoder capability,
both propositional round trips, generic transport coherence, the operational
decoder square, and a Pi-universe action consumer are promoted with
owner-position diagnostics.

Start record (2026-07-15): staged changes remain empty; the unstaged worktree
contains only the plan-scoped redesign implementation and synchronized
diagnostics/examples/reports/generated artifacts, with no unrelated user
change detected. The ordinary-equivalence slice's 1,018-check, 991/157,
zero-strict-LHS gate is the incoming baseline. This slice will inventory the
active `idtoequiv_grpd`, `grpd_equiv_path`, capability-selected `ua_grpd`, and
`coe_grpd` owners; select or derive named capability agreement; add both
groupoid round trips, the transport/action square, and one nontrivial Pi or
Sigma universe-action consumer. It excludes categorical decoder/D1 migration,
direct universe equality, additional constructor closure, truncation-evidence
property-valuedness, fixed-map omega-equivalence, structural action/fibrancy,
and indexed adjunction migration. Fresh full-file owner-position source and
retargeted-check probes are required before active promotion.

Completion record (2026-07-15): the full-file owner candidates are
`tmp/probes/oetu_grpd_decoder_owner_full.lp` and
`tmp/probes/oetu_grpd_decoder_owner_checks_full.lp`. Final quiet source/check
logs end in `20260715-191253`/`191350`; warning-enabled logs end in
`20260715-191401`/`191414` with the unchanged 991/157 inventory. The separate
runtime candidate `tmp/probes/oetu_grpd_decoder_runtime_coe_candidate_full.lp`
passes quiet checking in the log ending `20260715-191107` but exposes an
unjoinable Product branch: outer `coe(grpd_equiv_path(product_equiv),p)`
reduction yields the componentwise forward map, whereas decoder-first leaves
`coe(product_grpd_path(...),p)` stuck. The broad runtime orientation is
therefore rejected pending a real Product-path transport owner.

The promoted design names both fields of
`grpd_univalence_by_decoder` as `grpd_equiv_path_idtoequiv` and
`idtoequiv_grpd_equiv_path`. It derives
`grpd_univalence_from_decoder : GrpdUnivalence` through the reviewed
quasi-inverse theorem, and its selected contractible-fibre inverse
`grpd_univalence_selected_path` computes to the single operational
`grpd_equiv_path` decoder. Owner evidence showed no basis for identifying an
arbitrary primitive `ua_grpd(U,e)` with that decoder, so new coherence
consumers are restricted to the canonical decoder capability and the generic
agreement remains explicitly negative rather than postulated.

`coe_grpd_idtoequiv` is derived by generic J. Composing it with the decoder
right round trip gives the propositional `grpd_equiv_path_coe` square; the Pi
point-evaluation theorem `grpd_equiv_path_pi_action` is the nontrivial universe
action consumer. No rewrite or unification rule was added. Sixteen active
diagnostics (11 positive and five negative) and a reviewer example with eight
positive assertions and four negative cover the canonical selected centre,
both round trips, reflexive transport, Product/Pi consumers, rejected runtime
fold, and arbitrary-`ua_grpd` boundary. The 1,034-check catalog classifies all
16 with zero unclassified entries; the strict audit remains zero with 45
annotated slots across 27 clauses. No notation change was required.

### Completed Omega0 slice: Candidate D0 fixed-map equivalence owner

Start record (2026-07-15): staged changes remain empty; the unstaged worktree
contains only the plan-scoped redesign implementation and synchronized
diagnostics/examples/reports/generated artifacts, with no unrelated user
change detected. The groupoid-decoder slice's 1,034-check, 991/157,
zero-strict-LHS gate is the incoming baseline. This slice will introduce a
fresh source-position `OmegaEquivAlong_D0(F)` evidence owner independent of
the old public `OmegaEquiv`, its minimal Sigma package, forward/evidence and
inverse/higher-cell observations, fixed-map reflexivity, and one recursive
next-hom reflexive computation. It excludes D0b variable-evidence Cat hom
action, D1 public normal-form migration, categorical decoder finalization,
opposite/Product generators, unrestricted corecursion/productivity,
property-valuedness, discreteness/`OneCat`, indexed adjunction migration, and
module splitting. Fresh full-file owner-position source and retargeted-check
probes are required before active promotion.

Completion record (2026-07-15): the owner-position source and retargeted-check
probes pass quietly and warning-enabled; the active source is byte-identical
to the source probe and the check probe differs only in its import. The new
owner has no dependency on old `OmegaEquiv`, adds no unification rule, and
preserves the 991/157 warning inventory and zero strict-LHS result. The 21
active diagnostics comprise 18 positive and three negative checks; the
reviewer example has eight positive and three negative assertions. The
1,055-check catalog has 1,016 positive and 39 negative checks across 29 areas,
with zero unclassified. Exact projection beta, both inverse/cell types and
reflexive betas, one projected next-hom observation, absent open package eta,
and absent raw inverse cancellation are all covered.

### Completed Omega0 slice: Candidate D0b variable-evidence Cat hom action

Start record (2026-07-15): staged changes remain empty and the unstaged
worktree remains plan-scoped, with no unrelated user change detected. D0's
1,055-check, 991/157, zero-strict-LHS gate is the incoming baseline. This
slice consumes variable
`u : OmegaEquivAlong_D0_{Cat_cat}(F)` and must construct fixed-arrow evidence
for `fapp1_func(F,x,y)`. The selected inverse must have endpoints exactly in
the hom categories at `x,y`; raw `fapp1_func` of the selected inverse functor
is not sufficient and must be conjugated/whiskered using components of D0's
higher inverse cells. The candidate must expose both higher observations
through one recursive rung, exact forward projection, both-order and negative
endpoint controls, warning/LHS/timing evidence, and no per-instance
`unif_rule`. It excludes D1, categorical decoder finalization, the later
`Core_incl_func` specialization and its named round trips, opposite/Product
generators, property-valuedness, and discreteness/`OneCat`.

Completion record (2026-07-15): the owner-position source and retargeted-check
probes pass quietly and warning-enabled; the active source is byte-identical
to the source probe and the check probe differs only in its import. The left
inverse is `Hom(eta_x,epsilon_y) o L_1`. Because raw `R_1` also has the wrong
endpoints, the right inverse uses components of both recursive cells to build
`L(b) <-> R(b)` endpoint comparisons before conjugating `R_1`. Both returned
cells are transparent D0 packages whose forward and evidence projections
compute and remain observable once more. No raw cancellation, unrestricted
corecursor, or per-instance unification rule was added. The 26 active
diagnostics comprise 24 positive and two negative endpoint controls; the
reviewer example has eight positive and two negative assertions. The
1,081-check catalog has 1,040 positive and 41 negative checks across 30 areas,
with zero unclassified. Quiet logs end in `20260715-194634`/`194846` and
warning-enabled logs end in `20260715-194900`; warnings remain 991/157 and the
strict audit remains zero with 45 annotated slots across 27 clauses.

### Completed Omega0 slice: Candidate D1 public normal form and categorical decoder

Start record (2026-07-15): staged changes remain empty and the unstaged
worktree remains plan-scoped, with no unrelated user change detected. D0b's
1,081-check, 991/157, zero-strict-LHS gate is the incoming baseline. This slice
replaces the old opaque public `OmegaEquiv(C,x,y)` classifier with the promoted
fixed-map Sigma boundary, routes the public destructors through its evidence
projection, and migrates reflexive, opposite, and Product generators at their
owners. In the same full-file candidate it retypes `idtoequiv_cat` and
`omega_equiv_path`, validates both categorical decoder round trips and
capability agreement, covers the `path_to_hom` and Product squares, supplies a
named equivalence plus one integrated next-hom univalence/action witness, and
compares the package with the semantic fibre reference. It requires a fresh
owner-position source/check probe and proportional warning, LHS, timing,
catalog, example, health, and CI evidence. Property-valuedness, the later
`Core_incl_func` specialization, `IsDiscreteCat`/`OneCat`, unrestricted
corecursion/productivity, direct observational universe identity, indexed
adjunction migration, and module splitting remain excluded.

Completion record (2026-07-15): the owner-position source/check candidates pass
quietly and warning-enabled, and the active promotion passes all proportional
gates. The public `OmegaEquiv` normal form is the fixed-arrow Sigma package;
destructors route through evidence, while reflexive/opposite/Product evidence
heads own constructor-specific computation. The categorical decoder supplies
both named propositional round trips, a derived capability and named
`TypeEquiv`, selected inverse agreement, the propositional `path_to_hom` square,
and Product projections. `OmegaEquivFibre` is retained only as a semantic
reference with a one-sided retraction, so package eta, reverse fibre eta, and
property-valuedness are not inferred. The integrated category-path hom-action
witness has exact forward/evidence projections and remains iterable through a
recursive cell without a per-instance `unif_rule`.

The 46 D1 diagnostics comprise 41 positive and five negative assertions; ten
evidence-observation/reflexivity overlap families have explicit both-order
checks. The reviewer example has twelve positive and four negative assertions.
The catalog now has 1,127 classified checks (1,081 positive, 46 negative)
across 31 areas, warnings improve from 991/157 to 990/157, and the strict audit
remains zero with 45 intentional slots across 27 clauses. Health checks all 15
files and records 3.313s for the source, 4.411s for diagnostics, and 5.677s for
the D1 example. Quiet source/check logs end in `20260715-202501`/`202612`;
warning-enabled logs end in `20260715-202626`/`202912`. `make check`, examples,
catalog, TOC, warning summary, health, and CI all pass. The next selected slice
is Phase 8 `OETU-ADJUNCTION-INDEXED`; the now-dependency-ready core-inclusion
discreteness specialization remains a separate Phase 9 lane.

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
- `OETU-OBS-BOOL` checks all four visible Boolean equality-classifier cases,
  generic reflexivity typed by the reduced Unit classifier at both
  constructors, reflexive generic J and the existing generic path/Core/unit/
  encoder consumers, plus runtime and proof-time non-collapse to raw `tt`;
- open Boolean variables retain the generic equality/reflexivity presentation,
  cross-constructor equality decodes to `Empty_grpd`, and no negative control
  is described as a global canonicity or non-derivability theorem;
- `OETU-OBS-UNIT` checks `tt = tt -> Unit_grpd`, generic reflexivity/J and
  existing literal-reflexivity consumers, raw-`tt` runtime/proof-time
  boundaries, and an open-unit-variable control without claiming Unit eta or
  canonicity;
- `OETU-OBS-NAT` checks all four zero/successor classifier cases, recursive
  successor equality, generic zero/successor reflexivity and consumers,
  non-collapse to `tt` or predecessor reflexivity, and open-endpoint controls
  without claiming Nat canonicity or a normalization theorem;
- `OETU-OBS-J-SR-GUARD` checks that generic J still computes on exactly
  matching outer reflexivity but not on foreign Unit/Boolean/Nat reflexivity
  or predecessor reflexivity merely admitted by a shared reduced classifier;
  the focused proof-dependent injective-motive probe also computes the normal
  form and checks the branch/result typing distinction;
- `OETU-OBS-SUM` checks all four inl/inr classifier cases, recursive component
  equality, generic outer reflexivity and consumers, non-collapse to component
  reflexivity, guarded J under shared reduced classifiers, and open-endpoint
  controls without claiming sum canonicity or a normalization theorem;
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
  identity has projected to `eq_refl`, derived through a named general typed
  comparison and shared category unit rather than a specialized runtime rule;
- four negative controls showing those projected oriented action units do not
  become runtime conversions, and the rejected four-bridge variant's five
  extra critical pairs remain recorded;
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
  projections, and naturality; the mapped-`DefIso` subset selects inferred
  endpoints at the generic owner; and
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
- fixed-map equivalence of `Core_incl_func(C)` yields, by instantiating the
  promoted D0b general hom-action construction,
  `OmegaEquivAlong_{Cat_cat}(core_incl_hom_func(C,x,y))` at arbitrary
  endpoints; a specialized substitute requires an explicit revision that
  blocks D1 rather than an unnoticed extra field;
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
- `idtoequiv_grpd(grpd_equiv_path(e)) = e` and
  `grpd_equiv_path(idtoequiv_grpd(p)) = p` propositionally through the selected
  decoder capability; its derived contractible-fibre selected inverse computes
  to `grpd_equiv_path`, while arbitrary `ua_grpd(U,e)` agreement stays
  negative;
- `coe_grpd(grpd_equiv_path(e),a) = type_equiv_to(e,a)` propositionally through
  generic `idtoequiv` action plus the decoder round trip; the broad runtime
  orientation remains rejected until Product-path transport joins, while the
  existing legacy `coe_grpd(ua_grpd(U,e),a)` beta remains compatibility-only;
- one nontrivial Pi or Sigma universe-action example;
- `path_to_hom` agrees with `idtoiso_cat`/`idtoequiv_cat` forward arrows;
- Product reflexive constructor/decoder diamonds;
- both OneCat-scoped ordinary-iso decoder round trips, reconstructed evidence,
  specified-inverse capability, contractible-fibre capability, and named
  `TypeEquiv` are checked; the selected classifier is deliberately unavailable
  for arbitrary `Cat`;
- no diagnostic or implementation consumer uses a global ordinary-iso
  capability inhabitant; those declarations and their hardcoded classifier are
  retired, and generic `isotoid_cat` is checked with the scoped inhabitant;
- `omega_equiv_to((F,u)) ≡ F` and
  `omega_equiv_evidence((F,u)) ≡ u` by generic Sigma projection;
- during compatibility staging only,
  `omega_equiv_to(omega_equiv_from_along(u)) ≡ F` by runtime computation;
- comparison of `OmegaEquivAlong(F)` with `OmegaEquivFibre(F)` propositionally;
- inverse/map projection betas are declared before dependent higher-cell
  betas and pass subject reduction in that order;
- fixed-arrow left/right higher-cell endpoints typecheck with `f` as an index,
  and no broad raw inverse-composite cancellation rewrite is introduced;
- from variable `u : OmegaEquivAlong_{Cat_cat}(F)`, not merely reflexive
  evidence, `omega_equiv_along_fapp1(u,x,y)` has selected map exactly
  `fapp1_func(F,x,y)`;
- the selected inverse of that hom action has the required source and target
  hom-categories. Its diagnostic exposes the necessary conjugation/whiskering
  by higher inverse-cell components, with a negative control against treating
  a selected inverse `G`'s raw `fapp1_func(G,Fx,Fy)` as endpoint-correct when
  it is not;
- the induced hom-action evidence exposes left/right higher observations
  through one recursive rung and passes source-position subject reduction,
  later-source checking, changed-head warnings, both-order consumers, and
  bounded timing without a per-instance `unif_rule`;
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
- no opaque unification-only functor projection is retained; the append-only
  comparison probe remains evidence for why the active view is transparent;
- typed `eq_refl` must exercise every intentionally retained proof-time
  `unif_rule`. Phase 8 retains no adjunction-specific rule because its inventory
  found no concrete preselected named unit/counit pair or declaration backing;
- any future agreement path offered as backing must be checked not to depend
  solely on the same `unif_rule` whose soundness it is meant to support;
- active `assertnot` checks record that arbitrary named operations are not
  runtime-convertible to the stable observations and that a raw named-operation
  triangle is not falsely claimed to compute;
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

The promoted registered-action slice makes this boundary executable: selected
operations carry explicit agreement with `eq_ap`/`eq_apd`, while an arbitrary
selected PathRecord loop still fails the dependent-J runtime beta. An action
head for registered maps does not by itself justify adding new
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

### `Path_cat` E0 and E1 are promoted; later packaging remains gated

The shared-`comp_fapp0` candidate has stronger evidence than an ordinary
append-only probe and resolves the apparent unit/asymmetry contradiction at the
category-composition layer. Collapse removal and the minimal `PathSym_A` core
now also have owner-position full-file evidence. This removes the earlier
global-selection gap at the plan level: the object/arrow owner, anti-
composition orientation, `eq_sym` boundary, involution status, and Core square
are explicit.

The shared-composition/genuine-opposite repair and the symmetry core are active
with durable checks. E1's twelve reports are classified and the evidence-led
generic mapped-`DefIso` endpoint repair lowers the final inventory from
1,072/159 to 974/159. These inventories are diagnostics, not confluence
proofs. “Candidate E complete” still does not mean that functor-level natural
or fixed-map equivalence packaging exists; those remain at their named later
owners. D1 is now promoted, so such packages are dependency-ready only when a
concrete consumer selects their separate owner.

### `IsDiscreteCat` homwise adequacy is promoted; preserve its evidence boundary

Supersession note (2026-07-19): the section below records the original
Phase-9 D0b promotion. The current selected contract replaces its second
factor by native `IsGroupoidalCat_EQ1(C)` and derives the same homwise path
reader/round trips in `emdash3_2_eq1_hom_action.lp`. The dated probe and
warning evidence below remains historical provenance, not the current owner
description.

Do not weaken discreteness to object-set truncation merely to make `OneCat`
easy to declare. The exact contract is now selected as
`IsSetGrpd(Obj(C)) ×
OmegaEquivAlong_{Cat_cat}(Core_incl_func(C))`, integrated with the recursive
Sigma-packaged `OmegaEquiv` rather than an opaque generic category-equivalence
property.

Owner-position Phase 9 evidence now proves that the certificate API exposes
the needed full-faithfulness surface: every
`core_incl_hom_func(C,x,y)` receives D0b-derived fixed-map evidence, its object
action is `path_to_hom`, its selected inverse is `hom_to_path`, and both
coherent directions are public. The implementation required one reusable
left-inverse/right-component compositor but no new rule, `unif_rule`, PathSym
package, or third discreteness field. Preserve that result while recursive
`IsNCat` consumes it; object truncation alone still must never be called
“discrete.”

### The promoted `OmegaEquiv` normal-form migration remains an audit boundary

The primary-evidence/Sigma-package architecture replaces the formerly opaque
public classifier and therefore remains a kernel normal-form boundary even
after promotion. D0 established the recursive fixed-arrow owner/package and
reflexive next-hom computation; D0b established the endpoint-correct variable-
evidence Cat hom action; D1 migrated public constructors, decoder consumers,
and the integrated witness. The full ladder passes source-position,
subject-reduction, warning, strict-LHS, downstream, timing, and both-order
audits. Future consumers must preserve that evidence-routed normal form and
must not infer package eta or property-valuedness from the successful
migration.

### Immediate decoder univalence can be mistaken for full universe identity

H1 deliberately stops at encoder/decoder round trips and selected action beta.
That is enough for the immediate MVP, but not for the eventual statement that
public universe equality itself computes as equivalence. Conversely, the
later goal does not license importing another system's glue or bisimulation
mechanism without a local owner analysis. Phase 13 owns this boundary.

Decoder normalization is also layer-sensitive. The groupoid decoder and its
H1 round trips stabilized first; the categorical decoder then finalized
jointly with D1 against the public fixed-map Sigma normal form under
`OETU-CAT-UNIV-DECODER`. `OETU-TYPE-EQUIV-ALGEBRA` remains independent of both
decoder theorem families, and neither completed decoder upgrades the later
direct-universe-identity track.

### Indexed adjunction completed as one owner migration

`Adjunction(F,G)` now removes unnecessary recovery of already-known functors
throughout the active source, diagnostics, and reviewer example. Opposite
adjunctions, triangles, mates, profunctor comparisons, and weighted
preservation were migrated together rather than through piecemeal opaque
compatibility rules. Owner-position evidence showed that explicit
`Op_func(F/G)` terms in inferred outer LHS slots created avoidable overlaps;
replacing those slots by `_` preserves the nested semantic discriminator and
lowers the warning inventory. This is the selected active architecture, not
merely the earlier append-only feasibility result.

### Named adjunction operations can erase the triangle discriminator

Unlike the left/right functors, the unit/counit observations cannot simply be
made transparent aliases for arbitrary preselected raw operations. The
negative probe demonstrates an inner-first reduction in which constructor
projection betas erase both stable heads before the outer triangle rule is
selected. No local unjoinable critical-pair warning identified the lost
computation. The promoted slice therefore retains explicit positive and
negative assertions, stable canonical triangle spellings, and no runtime
operation-projection beta. A different orientation would require a new audited
semantic owner rather than an instance-level shortcut.

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
demonstrates mechanics only. Candidate H's promoted eta is conditional on its
selected generic reflexive law, whose separate transparent probe supplies
independent definition-level reduction evidence. Its typed consumer remains a
firing regression rather than that evidence; the law is explicitly accepted
as generic semantically justified proof-time authority.

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

The separate legacy global `cat_iso_univalence` assumption is retired. New
general-category work cannot use it and therefore cannot silently reintroduce
the dimension collapse it was meant to remove. `CatIsoUnivalence` remains a
capability type for explicit/scoped inhabitants, and the legacy
`iso_evidence_path` remains a computation owner rather than an inhabited
global equivalence claim. Treating ordinary and omega capabilities as
permanent global principles would induce an unrestricted comparison between
`IsoEvidence` and recursive `OmegaEquiv`; the OneCat boundary is what makes
that comparison dimension-correct.

## Side-Task Ledger

| ID | Status | Depends on | Resume trigger | Next action |
| --- | --- | --- | --- | --- |
| `OETU-RECORD-CONVENTION` | **completed/promoted (2026-07-15)**; named dependent `PathRecord` carrier/classifier, constructor, projections, eliminator facade/betas, and no-eta control active; owner-position/nested-Sigma comparison and all gates pass warning/LHS neutral | current inductive/Sigma infrastructure | reopen only for a concrete convention bug or a second real record that invalidates the selected pattern | Preserve decoded public signatures, single parameter binding, inferred non-discriminating projection slots, and no runtime eta. Candidate C owns equality/reflexivity/reflexive J; arbitrary action/additional J, generic generation, and truncation packages remain separate rows. |
| `OETU-RECORD-GENERATOR` | deferred/optional | `OETU-RECORD-CONVENTION` | two manual records show repeated stable boilerplate | Specify a deterministic external schema generator; generated code remains reviewable Lambdapi source. |
| `OETU-ELEMENTARY-HOTT` | **completed/promoted (2026-07-15)**; decoded Empty/Unit/Bool/Nat formation, dependent Empty/Bool/Nat elimination, constructor betas, and Bool non-collapse are active; warning/LHS neutral with full gates passing | active universe decoding and native inductives | reopen only for a concrete bug in this bounded surface | Preserve the selected decoded signatures and generated-recursion bodies. Visible Unit/Boolean/Nat classifiers are separately promoted under their observational rows; sums, remaining observational identity/no-confusion/higher action, canonicity, categorical universal properties, and later equality/univalence migration remain separate rows. |
| `OETU-H0-SUM` | **completed/promoted (2026-07-15)**; native carrier/classifier, left/right constructors, dependent eliminator/betas, six positive/one negative diagnostics, eight positive/two negative reviewer statements, unchanged 978/157 warnings, zero strict-LHS candidates, and 19-file CI are active | promoted `OETU-ELEMENTARY-HOTT`, active universe decoding, native parametrized inductives | reopen only for a sum formation/elimination owner bug | Preserve separate native parameter binders and the generated-recursor facade. Exclude observational identity/no-confusion/higher action, open eta, canonicity, and categorical coproduct properties. |
| `OETU-PI-FUNEXT` | **completed/promoted (2026-07-15)**; stable diagonal observation/extension, related-input action, pointwise beta, generic-J eta over a semantically justified proof-time basis, reviewed quasi-inverse-to-contractible-fibre theorem capability, executable selected centre, 29 diagnostics, reviewer example, 991/157 warning-neutral inventory, zero strict-LHS candidates, and all gates active | active `PiPathView`, retained generic `ind_eqr`, contractible-fibre `IsEquivMap`, promoted Candidate C hybrid equality core | reopen only for a Pi owner bug or a concrete stronger structured-J/fibrancy consumer | Preserve stable heads, proof-time/runtime negatives, application-first shaped joins, and opaque contraction. Do not add whole-function eta or rely on unification transitivity; structural paths, `TypeEquiv` algebra, and truncation evidence remain separate rows. |
| `OETU-STRUCTURAL-PATH-COMPAT` | **completed/promoted (2026-07-15)**; arbitrary propositional Sigma round trips, transparent PathRecord maps/round trips, constructor-reflexive computation, dependent-tail preservation, nested former, 21 diagnostics, reviewer example, 991/157 warning-neutral inventory, zero strict-LHS candidates, and all proportional gates active | active Sigma paths, promoted `OETU-RECORD-CONVENTION`, promoted `OETU-PI-FUNEXT` where path-valued functions require it | reopen only for a path-characterization owner bug or a concrete stronger action/fibrancy consumer | Preserve the separate literal-reflexivity J base, open runtime-eta negatives, direct PathRecord identity-view maps, and separate structural action/fibrancy boundary. Do not route PathRecord through a redundant Sigma normalization. |
| `OETU-TYPE-EQUIV-ALGEBRA` | **completed/promoted (2026-07-15)**; identity, transparent symmetry/categorical-order composition, derived `IsEquivMap` closure, executable forward/inverse/right projections and forward-map unit/associativity, 29 diagnostics, reviewer example, 991/157 warning-neutral inventory, zero strict-LHS candidates, and all proportional gates active | active `IsEquivMap`/`TypeEquiv`, promoted `OETU-PI-FUNEXT`, promoted `OETU-STRUCTURAL-PATH-COMPAT` | reopen only for an ordinary equivalence-algebra owner bug or a concrete stronger package-coherence consumer | Preserve transparent packages, explicit inverse paths, the reviewed quasi-inverse theorem route, opaque contraction-side left projection, and package-eta negatives. Decoder round trips, transport squares, and universe-action examples remain separate. |
| `OETU-TRUNC-LEVEL` | **completed/promoted (2026-07-15)**; native level codes/readable aliases, recursive `IsTruncGrpd`, low-level views, formation/reduction/evidence-application checks, and explicit closure-ledger statuses active; warning/LHS neutral with all gates passing | existing `IsContr`, `Pi_grpd`, equality | reopen only for a property-kernel bug | Preserve the explicit -2 origin, recursive owner, transparent low-level views, and definitional equality-lowering boundary; packages, remaining closure proofs, reflectors/HITs, and later equality/univalence work remain separate. |
| `OETU-TRUNC-CLOSURE` | staged ledger; equality lowering, general/fixed-map invariance, monotonicity, evidence property-valuedness, dependent-Pi/Sigma preservation, package paths, restricted package univalence, carrier `TypeEquiv` truncation, and the expected package-universe level are active; recursive fixed-arrow evidence is representation-blocked | `OETU-TRUNC-LEVEL`, equality/equivalence, promoted Pi funext and groupoid/categorical decoders | the fixed-arrow certificate representation is redesigned | Preserve the completed closure corpus; resume recursive omega-equivalence evidence only after its explicit representation prerequisite. |
| `OETU-TRUNC-EQUIV-INVARIANCE` | **completed/promoted (2026-07-15)**; decoder-induced evidence-classifier `TypeEquiv`, both transports/round trips, reflexive computation, ten positive/one negative diagnostics, seven positive/two negative reviewer statements, unchanged 978/157 warnings, zero/45/27 audit, and 20-file CI are active | promoted `OETU-TRUNC-LEVEL`, `OETU-TYPE-EQUIV-ALGEBRA`, and `OETU-GRPD-UNIV-DECODER` | reopen only for an ordinary invariance owner regression | Preserve the single `grpd_equiv_path` route and open arbitrary-self-equivalence boundary. Do not duplicate recursive predicate bodies or conflate this row with categorical/fixed-map consumers. |
| `OETU-CAT-TRUNC-EQUIV-INVARIANCE` | **completed/promoted (2026-07-15)**; decoder-induced object path/`TypeEquiv`, object-truncation evidence equivalence/transports, twelve positive/three negative diagnostics, eight positive/two negative reviewer statements, unchanged 978/157 warnings, zero/45/27 audit, and 21-file CI are active | promoted `OETU-TRUNC-EQUIV-INVARIANCE`, `OETU-CAT-UNIV-DECODER`, and `OETU-OMEGA-EQUIV-ALONG` | reopen only for a categorical object-invariance owner regression or a concrete functor-map agreement consumer | Preserve `eq_ap(Obj,omega_equiv_along_path_D1(u))` as the decoder-owned route. Do not reconstruct inverse object maps from component arrows, add a trust equation, or claim runtime agreement with `fapp0(F)`. |
| `OETU-TRUNC-MONOTONICITY` | **completed/promoted (2026-07-15)**; explicit contractible-path contraction, native level recursion, twelve positive/one negative diagnostics, eight positive/one negative reviewer statements, unchanged 978/157 warnings, zero/45/27 audit, and 22-file CI in 127.18s are active | promoted `OETU-TRUNC-LEVEL`, generic path induction/algebra, and the active Pi classifier | reopen only for a monotonicity owner regression | Preserve the forced two-position ownership, inferred Sigma constructor indices, native recursor, base/successor computation, and open-centre negative. Add no global weakening rewrite or proof erasure. |
| `OETU-TRUNC-EVIDENCE-PROP` | **completed/promoted (2026-07-16)**; dependent Sigma comparison of contractibility witnesses, contractible/proposition Pi closure, stable recursive theorem owner, sixteen positive/two negative diagnostics, eight positive/two negative reviewer statements, unchanged 978/157 warnings, zero/45/27 audit, and 23-file CI in 75.41s are active | `OETU-TRUNC-LEVEL`, `OETU-PI-FUNEXT`, active Sigma/PathOver paths, general invariance, and generic path algebra | reopen only for an evidence-property owner regression | Preserve the stable two-equation classifier-consumer owner selected after transparent-recursion successor timeouts, and retain open-evidence negatives. This row alone installs neither definitional proof erasure nor the separately promoted package-universe level theorem. |
| `OETU-TRUNC-PI-CLOSURE` | **completed/promoted (2026-07-16)**; arbitrary-level dependent-Pi preservation, stable recursive theorem owner, ten positive/one negative diagnostics, eight positive/one negative reviewer statements, unchanged 978/157 warnings, zero/45/27 audit, and 24-file CI in 131.21s are active | promoted `OETU-TRUNC-EVIDENCE-PROP`, `OETU-PI-FUNEXT`, `OETU-TRUNC-EQUIV-INVARIANCE`, and active `is_contr_pi` | reopen only for a dependent-Pi closure owner regression | Preserve the stable two-equation family/evidence-consumer owner, successor transport through `pi_happly_type_equiv`, the `is_prop_pi` specialization alias, and the open pointwise-evidence negative. Do not duplicate the semantic body or infer proof erasure. |
| `OETU-TRUNC-SIGMA-CLOSURE` | **completed/promoted (2026-07-16)**; contractible-total base, same-level recursive Sigma theorem, ten positive/two negative diagnostics, eight positive/two negative reviewer statements, unchanged 978/157 warnings, zero/45/27 audit, and 25-file CI in 136.09s are active | promoted `OETU-TRUNC-PI-CLOSURE`, active `SigmaPathView`/`PathOver`, `OETU-TRUNC-LEVEL`, and generic path algebra | reopen only for a dependent-Sigma closure owner regression | Preserve both base/fibre hypotheses, the explicit transport in the contractible base, the stable two-equation consumer owner, and both open-evidence negatives. Add no unconditional Sigma rule or stronger bound. |
| `OETU-OMEGA-EQUIV-EVIDENCE-TRUNC` | representation prerequisite; both one-layer and structurally terminating dimension-indexed observation/path views are completed, but neither has a reverse decoder, direct recursive equality remains normalization-blocked, and no proof-ready arbitrary-evidence eliminator exists | promoted D0/D1 observations, completed `OETU-OMEGA-EQUIV-EVIDENCE-VIEW`, completed `OETU-OMEGA-EQUIV-EVIDENCE-DIM-VIEW`, and `OETU-TRUNC-SIGMA-CLOSURE`; still needs a reverse certificate representation or independently justified evidence-path capability | resume construction only after a representation/path result exposes arbitrary evidence construction or elimination within the bounded normalization contract | `OmegaEquivAlong_D0` remains opaque. The one-sided compatibility-fibre retraction and both one-way encoders are insufficient; owner-position and self-universe timeouts reject direct recursive equality. A named conditional capability and a finite deep view are not inhabitants. Do not postulate property-valuedness from observations. |
| `OETU-TRUNC-UNIVERSE` | **completed/promoted core (2026-07-15)**; parametrized package/classifier, constructor, carrier/evidence projections and betas, low-level aliases, and evidence-retention/no-eta/no-same-level diagnostics active; owner-position/warning/LHS and all gates pass | promoted `OETU-RECORD-CONVENTION`, promoted `OETU-TRUNC-LEVEL` | reopen only for a package-core bug | Preserve retained evidence and the absence of runtime eta/proof erasure/same-level claims. Evidence property-valuedness, package paths, restricted univalence, and the successor universe-level theorem are owned by their promoted extension rows; reflectors remain separate. |
| `OETU-TRUNC-UNIVERSE-PATHS` | **completed/promoted (2026-07-16)**; named carrier/evidence view, native eliminator, evidence-derived reconstruction, reflexive theorem, both propositional inverse laws, path `TypeEquiv`, fifteen positive/three negative diagnostics, eight positive/three negative reviewer statements, unchanged 978/157 warnings, zero/45/27 audit, 26-file health inventory, and 26-file CI in 188.15s are active | promoted `OETU-TRUNC-UNIVERSE`, `OETU-TRUNC-EVIDENCE-PROP`, active `PathOver`, and structural path patterns | reopen only for a package-path owner regression | Preserve retained evidence, the single carrier projection/reconstruction route, propositional inverse laws, and all open runtime controls. This row does not itself install package eta, restricted ambient univalence, or the downstream universe-level theorem. |
| `OETU-TRUNC-UNIVERSE-UNIVALENCE` | **completed/promoted (2026-07-16)**; canonical ambient decoder package and restricted package-univalence composition, twelve positive/three negative diagnostics, eight positive/three negative reviewer statements, unchanged 978/157 warnings, zero/45/27 audit, 27-file health inventory, and 27-file CI in 282.49s are active | promoted `OETU-TRUNC-UNIVERSE-PATHS`, `OETU-GRPD-UNIV-DECODER`, and `OETU-TYPE-EQUIV-ALGEBRA` | reopen only for a restricted-univalence owner regression | Preserve the single decoder-owned inverse, exact projections, propositional round trips/inverse reflexivity, and forward-reflexive computation. This row does not infer direct observational universe identity; the downstream `(n+1)` theorem has its own promoted owner. |
| `OETU-TRUNC-UNIVERSE-LEVEL` | **completed/promoted (2026-07-16)**; explicit-inverse contractible `TypeEquiv` base, successor Pi/Sigma/property closure, stable two-branch owner, expected `(n+1)` package-universe theorem, seventeen positive/three negative diagnostics, eleven positive/three negative reviewer statements, unchanged 978/157 warnings, zero/45/27 audit, 28-file health inventory, and 28-file CI in 155.30s are active | promoted `OETU-TRUNC-UNIVERSE-UNIVALENCE`, Pi/Sigma truncation closure, evidence-property closure, and monotonicity | reopen only for a carrier-equivalence or package-level truncation owner regression | Preserve the genuine base use of both endpoints, successor dependence only on target truncation, stable consumer equations, and transport through restricted package univalence. Add no broad proof erasure, same-level universe claim, or direct universe identity. |
| `OETU-TRUNC-REFLECTOR` | deferred | observational equality and HIT elimination | a theorem needs `||A||_n`, not merely `IsTruncGrpd(n,A)` | Design propositional truncation first with restricted dependent elimination. |
| `OETU-PATH-CAT-COMP` | **completed/promoted (2026-07-15)**; shared composition, two minimized projection-unit bridges, J-derived comparison, genuine opposite presentation, typed/non-convertible oriented-action units, retargeted Core composition, durable suite/example, 1,072/159 warnings, zero strict-LHS candidates, and all gates active | generic `comp_fapp0`, oriented hom actions, current J-derived path algebra | reopen only for an E0 owner bug or a concrete runtime consumer that cannot use the typed action-unit route | Preserve shared category composition and distinct action heads. Do not restore the `eq_trans` fold, self-opposite collapse, or rejected four runtime bridges; later symmetry/equality/univalence work remains separate. |
| `OETU-PATH-CAT-SYM` | **completed/promoted core (2026-07-15)**; functor/action/reflexivity, generic anti-composition, propositional agreement/involution/Core square, twelve-block classification, mapped-`DefIso` endpoint repair, 974/159 inventory, and all gates active; later natural/fixed-map packages remain separate | promoted `OETU-PATH-CAT-COMP`, generic functoriality, current J-derived `eq_sym`; equivalence packaging also depends on `OETU-OMEGA-EQUIV-ALONG` | reopen the core only for a concrete regression; package only when the later owners are selected | Preserve genuine opposite and generic functorial ownership, typed/negative warning controls, and non-convertible open symmetry boundaries. Add functor-level natural and fixed-map equivalence packaging only when their consumers and owners are available. |
| `OETU-OMEGA-EQUIV-ALONG` | **D0/D0b/D1 completed/promoted (2026-07-15)**. Neutral fixed-arrow evidence, public Sigma package/projections, evidence-routed inverse/recursive cells, reflexive/opposite/Product generators, variable-evidence Cat hom action, categorical decoder round trips/named equivalence, one-sided fibre comparison, and the integrated next-hom witness are active with 93 diagnostics across three gates, three reviewer examples, a D1 endpoint of 990/157 warnings, and zero strict-LHS candidates | promoted D0/D0b plus generic Cat hom-action/component infrastructure and completed `OETU-CAT-UNIV-DECODER` | reopen only for an owner bug, a property-valuedness consumer, or the separately owned fixed-functor/core-inclusion specialization | Preserve the public fixed-map Sigma normal form, single evidence-indexed decoder, exact D0b forward hom functor, conjugated/whiskered inverses, recursive rung, ten both-order overlap checks, one-sided fibre boundary, and absence of per-instance `unif_rule` or package eta. |
| `OETU-ADJUNCTION-INDEXED` | **completed/promoted (2026-07-15)**; indexed owner, transparent functor views, stable observations, both triangles, opposite involution/unit/counit, mate/weighted consumers, three positive/three negative diagnostics, expanded reviewer example, 978/157 warnings, and zero strict-LHS candidates are active | D1 full gate was the incoming baseline; generic functor/transfor/profunctor owners remain unchanged | reopen only for an owner regression, an existential unknown-functor consumer, or a concrete declaration-backed named-operation bridge | Preserve direct `F,G` indices, stable unit/counit triangle discriminators, inferred outer opposite index slots, no raw projection beta, no unbacked per-instance `unif_rule`, and no existential package without a consumer. |
| `OETU-STRUCTURE-DECLARATION` | proposed usability protocol; append-only adjunction operation-bridge mechanics demonstrated, while Phase 8 found no concrete declaration backing to promote | primary fixed-map evidence; promoted indexed adjunction; `OETU-UNIF-TRUST` policy | a concrete named structure instance with preselected operations is needed | Validate direct `u : OmegaEquivAlong(F)` and `J : Adjunction(F,G)` declarations; connect preselected unit/counit names only by declaration-backed or explicitly trusted proof-time equations while canonical computations retain stable observations; treat typed `eq_refl` as a firing test and consider an elaborator/generator afterward. |
| `OETU-UNIF-TRUST` | proof-time trust policy selected; adversarial negative control passes | Lambdapi `unif_rule` and current runtime/proof-time SOP | every new or migrated proof-time equation | Maintain the three-class trust ledger (declaration/field-backed, generic semantically justified definitional law, explicit postulate), typed firing checks, runtime negative controls where intended, and the adversarial control; never count a same-rule `eq_refl` path as independent backing. |
| `OETU-DISCRETE-CAT` | **historical D0 implementation superseded by native P3 migration 2026-07-19**; the exact two-factor Product now stores native `IsGroupoidalCat_EQ1`, while core homwise evidence, selected `hom_to_path`, and both coherent directions live in the one-way native hom-action extension | native groupoidality and the P3 owner probes in the active compatibility-retirement plan | reopen only for an owner bug or a concrete stronger homwise coherence consumer | Preserve retained factors, derived rather than stored homwise evidence, no package eta, and no broad cancellation. Consume it as the exact `IsNCat(cat_zero,C)` base without D0 migration. |
| `OETU-NCAT` | **completed/promoted (2026-07-15)**; independent object truncation, native dimension codes, exact recursion, evidence-retaining packages, aliases, 18 positive/5 negative diagnostics, 7 positive/3 negative reviewer statements, a OneCat next-hom consumer, unchanged 978/157 warnings, zero strict-LHS candidates, and 17-file CI are active | promoted `OETU-DISCRETE-CAT`, `OETU-TRUNC-LEVEL`, and record convention | reopen only for a formation/package owner bug | Preserve the distinct axes, exact discrete base, retained evidence, and no eta; do not treat the object-truncation implication or iso-univalence as formation consequences. |
| `OETU-NCAT-DIM-TRUNC-INDEX` | **completed/promoted (2026-07-15)**; exact zero/successor index equations, five positive/one negative diagnostics, eleven positive/four negative directed-dimension reviewer statements, unchanged 978/157 warnings, zero strict-LHS candidates, and 19-file CI are active | promoted `OETU-NCAT` and `OETU-TRUNC-LEVEL` | reopen only for an index-owner regression | Preserve the native recursive map and negative evidence boundary. Do not fold categorical invariance or the implication theorem into index computation. |
| `OETU-NCAT-OBJ-TRUNC` | **completed by the native equality-valued overlay**; unconditional `ncat_obj_trunc_EQ1` is active with computing zero/successor equations | native unrestricted evidence property, retract closure, and `CatDim` recursion | reopen only for a native theorem/owner regression | Keep the theorem conclusion `IsNCat(n,C) -> IsObjTruncCat(cat_dim_trunc_level(n),C)` and state explicitly that the converse fails. The opaque D0 representation is no longer a prerequisite. |
| `OETU-NCAT-OBJ-TRUNC-CONDITIONAL` | **historical checkpoint completed 2026-07-16; implementation retired 2026-07-19**; the explicit uninhabited D0 capability, conditional theorem, diagnostics, and reviewer were deleted after the unconditional native theorem superseded them | historical promoted discrete base, native dimension index, Sigma closure, categorical decoder, and proposition lifting | reopen only if a concrete legacy consumer justifies a separately adopted compatibility theorem | Preserve the historical gate evidence in this ledger, but do not restore the capability or theorem. `prop_is_trunc_cat_dim` remains active because the native proof uses it. |
| `OETU-ONECAT-ISO` | **completed/promoted lift/first-roundtrip prerequisite (2026-07-16), synchronized 40-file CI passing in 281.823s; full scoped construction completed by the continuation rows below**; strict ordinary evidence derives recursive omega evidence, the scoped decoder, and its decoder-after-encoder law without the frozen global interface | promoted `OETU-NCAT`, `OETU-DISCRETE-CAT`, D0/D0b/D1 fixed-arrow evidence, and canonical categorical decoder | reopen only for a lift/first-roundtrip regression; use the completed inverse, transport, and reconstruction rows for the reverse direction | Preserve the five lift/decoder symbols, two two-equation families, and the single semantically backed reflexive `unif_rule`; keep runtime/package/legacy negatives and the distinction between `IsoEvidence` and `OmegaEquiv`. The synchronized one-sided evidence remains 12+/6- diagnostics, 9+/4- reviewer, 971/157 warnings, zero/45/27 audit, and 1,637 checks/58 areas. Add no arbitrary-`Cat` wrapper; the selected full capability is OneCat-indexed. |
| `OETU-ONECAT-ISO-INVERSE-COMPARE` | **completed/promoted with synchronized 40-file CI in 139.872s (2026-07-16)**; generic recursive cells construct `left_inv -> right_inv`, and OneCat hom discreteness decodes it to equality | promoted `OETU-ONECAT-ISO`, D0 cell observations, stable hom post/pre action, `path_to_hom`, and `OETU-DISCRETE-CAT` | reopen only for an inverse-comparison regression; `OETU-ONECAT-ISO-RIGHT-TRANSPORT` consumes the path | Preserve the explicit theorem-level associativity bridge and generic action ownership. The rejected direct composite is recorded at `123757`; selected evidence is 9+/4- new diagnostics, 6+/3- reviewer additions (15+/7- total), 971/157 warnings, zero/45/27 audit, 1,650 checks/59 areas, and 40-file health at 19,373 lines/790 symbols/581 rules/56 unification rules with 1,472 positives. Add no inverse-identifying rewrite or `unif_rule`; the decoded path intentionally remains non-runtime `eq_refl`. |
| `OETU-ONECAT-ISO-RIGHT-TRANSPORT` | **completed/promoted (2026-07-16)**; decoded recursive laws, ordinary equality action, and `one_cat_omega_inverse_path` transport the right law to the selected left inverse and reconstruct `IsoEvidence` from arbitrary OneCat omega evidence | completed `OETU-ONECAT-ISO-INVERSE-COMPARE`, categorical decoder, equality transport/action, and ordinary `IsoEvidence` constructor/projections | reopen only for a transported-law or reconstruction regression; `OETU-ONECAT-ISO-ROUNDTRIP` consumes the reconstructed package | Preserve explicit proof provenance and the selected left-inverse endpoint. The owner/inherited warning evidence ends in `131222`/`131311`/`131326`, ten positive/three negative diagnostics bring the catalog to 1,663 checks/60 areas, and the cumulative reviewer reaches 23+/10-. Add no global inverse equality, rewrite, or `unif_rule`; nested-Sigma reconstruction remains owned by the next row. |
| `OETU-ONECAT-ISO-ROUNDTRIP` | **completed/promoted with synchronized 40-file CI in 109.546s (2026-07-16)**; hom discreteness compares both law-proof fields, the existing nested-Sigma path owner proves lift/reconstruction equality, the reverse decoder law follows, and a OneCat-indexed specified inverse derives contractible-fibre univalence and a named `TypeEquiv` | completed `OETU-ONECAT-ISO-RIGHT-TRANSPORT`, structural Sigma paths, categorical decoder round trips, and `is_equiv_map_by_inverse` | reopen only for a scoped decoder/capability regression; `OETU-ONECAT-ISO-LEGACY-RETIRE` owns the compatibility cleanup | Preserve the scoped classifier and rejected-global evidence at `132624`. Owner/inherited logs end in `133706`/`133718`/`133745`/`133751`, reviewer in `134212`; ten symbols, no rewrite, and no `unif_rule` preserve 971/157 and zero/45/27. Thirteen positive/two negative diagnostics yield 1,678 checks/61 areas; the reviewer is 32+/12-. Health passes across 40 files at 19,883 lines/804 symbols/581 rules/56 unification rules with 1,495 positives, and full examples pass. |
| `OETU-ONECAT-ISO-LEGACY-RETIRE` | **completed/promoted with synchronized 40-file CI in 212.799s (2026-07-16)**; the unused arbitrary-`Cat` capability inhabitants and their hardcoded decoder classifier are removed, generic `isotoid_cat` checking uses the scoped inhabitant, and the still-consumed decoder/Product computation remains | completed `OETU-ONECAT-ISO-ROUNDTRIP`; active `rg` consumer inventory; retained `CatIsoUnivalence` type and generic `isotoid_cat` eliminator | reopen only if a retired global is referenced/restored or the retained decoder is mistaken for a capability; any decoder retirement needs its own replacement | Owner/check quiet logs end in `140150`/`140155`, warning logs in `140205`/`140228`, and the active reviewer in `140406`. Three symbols are removed with no rewrite or `unif_rule`; warnings remain 971/157 and audit zero/45/27. One scoped positive replaces three global positives and the obsolete scoped-vs-global negative, yielding 1,675 checks/61 areas and a 33+/11- reviewer. Health passes across 40 files at 19,859 lines/801 symbols/581 rules/56 unification rules with 1,493 positives, and full examples plus synchronized CI pass. Retain `iso_evidence_path` and its reflexive/Product rules. |
| `OETU-OBS-MVP` | conservative elementary lane completed through PathRecord shaped equality, visible Boolean/Unit/Nat/general-sum classifiers, guarded generic J, and synchronized Sum CI | record convention and current equality views | reopen for a concrete elementary-former regression or a separately selected former | Preserve the promoted classifiers and generic reflexivity/J controls. Re-audit proof-dependent subject reduction whenever distinct indices share a reduced classifier. Preserve proof provenance unless a concrete consumer justifies a shaped head or proof-time comparison; do not claim arbitrary structural action or broad migration. |
| `OETU-OBS-BOOL` | **completed/promoted (2026-07-16)**; four classifier equations, retained generic reflexivity provenance, 22 positive/11 negative diagnostics, 11 positive/6 negative reviewer statements, unchanged 972/157 warnings, zero/45/27 audit, and 30-file CI in 143.199s are active | promoted elementary Bool formation/elimination and generic equality/J/path/Core/encoder owners | reopen only for a classifier/provenance regression or a concrete typed proof-erasure consumer | Preserve the Unit/Empty matrix, open generic equality, generic literal-reflexivity computation, raw-`tt` runtime/proof-time negatives, and the rejected-collapse warning decomposition. Add no Boolean consumer registry or `unif_rule` without new semantic evidence. |
| `OETU-OBS-UNIT` | **completed/promoted (2026-07-16)**; one classifier equation, retained generic reflexivity provenance, 10 positive/9 negative diagnostics, 7 positive/6 negative reviewer statements, unchanged 972/157 warnings, zero/45/27 audit, and 31-file CI in 153.385s are active | promoted Unit formation and `OETU-OBS-BOOL` provenance decision | reopen only for a classifier/provenance regression or concrete typed proof-erasure consumer | Preserve generic `eq_refl`, raw-`tt` runtime/proof-time negatives, open Unit equality, and the absence of Unit eta/canonicity, consumer registry, or `unif_rule`. |
| `OETU-OBS-J-SR-GUARD` | **completed/promoted (2026-07-16)**; generic J repeats category and endpoint, four foreign-reflexivity negatives are active, the adversarial proof-dependent normal-form probe rejects the former inferred-index beta, warnings improve by one, and 32-file CI passes | visible Unit/Boolean classifiers and recursive Nat candidate exposed the shared-classifier risk | reopen for every new observational classifier or J owner migration | Preserve explicit category/endpoint discriminators as subject-reduction guards. Test proof-dependent injective motives, not quiet conversion alone. A `unif_rule` is not a repair for an ill-typed runtime beta. |
| `OETU-OBS-NAT` | **completed/promoted (2026-07-16)**; four recursive classifier equations, retained outer reflexivity, 23 positive/11 negative diagnostics, 11 positive/8 negative reviewer statements, 971/157 warnings, zero/45/27 audit, and 32-file CI in 151.336s are active | promoted Nat formation/elimination, Unit/Boolean provenance policy, and `OETU-OBS-J-SR-GUARD` | reopen only for a recursive-classifier/provenance/guard regression | Preserve the four cases, guarded generic consumers, proof-time/runtime non-collapse, open endpoints, and the exclusions of Nat canonicity/metatheoretic no-confusion, arbitrary action/fibrancy, and general-sum identity. |
| `OETU-OBS-NAT-SUCC-ACTION` | **completed/promoted with synchronized 41-file CI in 220.269s (2026-07-16)**; the first recursive-inductive registration selects `p |-> p`, proves arbitrary semantic agreement, and retains component/outer proof provenance | promoted `OETU-OBS-NAT`, guarded generic J, `OETU-OBS-ACTION`, `OETU-UNIF-TRUST`, and the stable-intermediary evidence from `OETU-OBS-SUM-ACTION` | reopen only for successor action/coherence/provenance regression or a separately selected fibrancy consumer | Preserve the stable Nat basis, its two direct semantically justified proof-time comparisons, explicit `ind_eqr` path composition, typed firing tests, and runtime/non-transitivity negatives. Fourteen positive/five negative diagnostics, an eleven-positive/five-negative reviewer, 1,694 checks/62 areas, 971/157 warnings, zero/45/27 audit, and a 19,988-line/808-symbol/581-rule/58-unification-rule kernel are active. Add no runtime proof collapse, successor-specific J beta, proof erasure, or canonicity claim. |
| `OETU-OBS-NAT-SUCC-ELIM` | **owner-position probe selected (2026-07-16)**; the completed successor action supplies a concrete recursive former, while the plan still lacks a sound first arbitrary-motive elimination facade | promoted `OETU-OBS-NAT`, guarded generic J, and completed `OETU-OBS-NAT-SUCC-ACTION`; no general fibrancy package is assumed | a public successor-equality-indexed facade routes its exposed predecessor proof through generic `ind_eqr`, computes only at component reflexivity, and needs no new rewrite or `unif_rule` | Probe immediately after the Nat action theorem at the actual owner. Use an arbitrary proof-dependent motive over successor equality. Preserve runtime negatives for outer `eq_refl(succ n)` and `nat_succ_ap_basis(n)`, and retain the generic J foreign-reflexivity guard. Treat this as former-specific elimination evidence, not as general fibrancy, arbitrary structured J, proof erasure, or canonicity. |
| `OETU-OBS-SUM` | **completed/promoted (2026-07-16)**; four tag-directed equations, retained outer reflexivity, 24 positive/11 negative diagnostics, 12 positive/8 negative reviewer statements, 971/157 warnings, zero/45/27 audit, and 33-file CI with 161.044s measured checking time are active | promoted general binary-sum formation/elimination and `OETU-OBS-J-SR-GUARD` | reopen only for a classifier/provenance/guard regression | Preserve component recursion, mixed-tag Empty cases, minimized constructor indices, guarded generic consumers, proof-time/runtime non-collapse, open endpoints, and the exclusions of sum canonicity/metatheoretic no-confusion, arbitrary action/fibrancy, and categorical coproduct structure. |
| `OETU-OBS-SUM-ACTION` | **completed/promoted (2026-07-16)**; eliminator-owned map, registered componentwise action, Empty mixed cases, arbitrary semantic agreement, 21 positive/6 negative diagnostics, 13 positive/4 negative reviewer statements, 971/157 warnings, zero/45/27 audit, 1,619 checks across 57 areas, 39 measured files, 55 total unification rules, and synchronized CI with 129.250s measured checking time are active | promoted general Sum formation/elimination and visible equality, promoted `OETU-OBS-ACTION`, retained generic J/`eq_ap`, and `OETU-UNIF-TRUST` | reopen only for an action/coherence/provenance regression or a separately selected former | Preserve the stable reflexive basis and two direct proof-time comparisons per tag, explicit theorem-level path composition, typed firing and runtime negatives. Add no runtime equality collapse, arbitrary J/fibrancy, proof erasure, no-confusion/canonicity, coproduct structure, or broad migration. |
| `OETU-OBS-SHAPED-REFL` | **completed/promoted (2026-07-15)**; dependent/nested PathRecord path view, stable reflexivity, projection/reflexive-J betas, closed literal-reflexivity registry, 40 diagnostics, 991/157 inventory, zero strict-LHS candidates, and all gates active | `OETU-OBS-MVP` classifier shape, consumer inventory, promoted `OETU-PATH-CAT-SYM` core | reopen only for a Candidate C owner bug or when the separate action/fibrancy work has its own proved architecture | Preserve the direct nested-Sigma view, stable-head registry, explicit PathSym category guards, ordered projection betas, and negative arbitrary-action/J/eta boundaries. Do not grow the registry without a new literal-reflexivity consumer audit. |
| `OETU-OBS-ACTION` | **completed/promoted (2026-07-15)**; semantic-agreement packages, canonical/identity/composite action, PathRecord open-map and dependent-witness consumers, 31 positive/5 negative diagnostics, 10 positive/3 negative reviewer statements, unchanged 978/157 warnings, zero strict-LHS candidates, and 18-file CI are active | active path telescopes, `PathOver`, shaped registry, and promoted PathRecord path view | reopen only for an action-owner regression or a concrete new former registration | Preserve selected-operation plus semantic-agreement data, computing identity/composition, retained coherence, and no runtime agreement for arbitrary packages. Do not infer fibrancy or arbitrary-constructor J from action. |
| `OETU-OBS-FIBRANCY` | prerequisite design/probe track for additional computation; action dependency complete but capability/consumer missing | promoted `OETU-OBS-ACTION`, dependent motives, registered formers; still needs a sound registered classifier/motive capability | a concrete consumer selects a runtime beta on an arbitrary structured constructor and the capability deriving it | Specify which classifiers/motives carry fibrancy and derive sound additional dependent-elimination computation. The action negative proves registration alone is insufficient; retained generic propositional J does not depend on this capability. |
| `OETU-OBS-SHAPED-J` | split status: reflexive `ind_eqr` promoted with Candidate C; additional arbitrary-constructor computation depends on fibrancy | promoted `OETU-OBS-SHAPED-REFL`; for extra arbitrary-constructor betas `OETU-OBS-FIBRANCY` | a consumer needs computation beyond reflexivity | Retain generic J and the narrow reflexive beta; derive additional structured-constructor runtime rules only from a sound dependent-elimination architecture. |
| `OETU-OBS-MIGRATE` | deferred high-risk public migration | successful shaped/MVP probe and consumer audit | one former has canonical joins | Migrate public equality one former at a time; do not combine with reorganization. |
| `OETU-FOUNDATIONAL-ADEQUACY` | architecture MVP, foundational implementation skeleton, and Foundational HoTT compatibility MVP achieved in the 2026-07-16 re-audit; active long-term tiered gate remains | all relevant rows above | every slice refinement and milestone; H2/HIT and metatheory keep their separate completion triggers | Maintain H0/H1/H2/Omega0 status/owner/computation cells. The achieved compatibility milestone requires active H0/H1 and the integrated fixed-map next-hom witness; it does not claim H2, certificate extensionality, consistency, normalization, canonicity, or a semantic model. Keep indexed adjunction as a separate migration witness. |
| `OETU-GRPD-UNIV-DECODER` | **completed/promoted (2026-07-15)**; canonical decoder-selected contractible-fibre capability, both propositional round trips, generic and decoder transport squares, Product/Pi consumers, 16 diagnostics, reviewer example, 991/157 warning-neutral inventory, zero strict-LHS candidates, and all proportional gates active | current groupoid equality, promoted `TypeEquiv` algebra/projections, promoted Pi/Sigma path compatibility, and groupoid-univalence capabilities | reopen only for a decoder owner bug or after a real constructor-path transport owner can join the rejected runtime fold | Preserve `grpd_equiv_path` as the sole operational inverse, restrict new consumers to the canonical decoder capability, keep arbitrary `ua_grpd` agreement and open round trips non-runtime, and retain the propositional square until Product-path transport exists. This task does not own categorical D1. |
| `OETU-CAT-UNIV-DECODER` | **completed/promoted jointly with D1 (2026-07-15)**; evidence-indexed decoder, both named propositional round trips, derived capability, named `TypeEquiv`, selected inverse agreement, `path_to_hom` theorem, Product cases, open-runtime negatives, and all gates active | promoted D0/D0b/D1 and `OETU-PATH-CAT-SYM` | reopen only for a decoder-owner bug or a concrete new constructor square | Preserve `omega_equiv_path` as the sole operational inverse, keep round trips and `path_to_hom` open terms propositional, and route new consumers through the named decoder capability rather than arbitrary `cat_univalence`. |
| `OETU-UNIVERSE-EQUALITY` | eventual full-observational track; finite groupoid view, direct categorical identity, and finite fixed-arrow certificate view are completed; direct groupoid and direct recursive certificate equalities remain rejected | `OETU-GRPD-UNIV-DECODER`, stable hybrid equality/action owners, `OETU-CAT-UNIV-DECODER`, and promoted fixed-map omega-equivalence | a stratified/guarded evidence representation or independently justified reverse path capability becomes available | Preserve both finite fallbacks and their direct-rule rejections. Keep categorical generic reflexivity distinct, reopen self-normalization when certificate representation changes, and integrate existing observation/decoder bodies rather than copying them. |
| `OETU-UNIVERSE-EQUALITY-GRPD-VIEW` | **completed/promoted (2026-07-16)**; finite named `TypeEquiv` view, canonical reflexivity, decoder-owned maps/round trips/transport, Product/Pi/Sigma consumers, 17 positive/7 negative diagnostics, 14 positive/5 negative reviewer statements, 971/157 warnings, zero/45/27 audit, and 34-file CI with 182.160s measured checking time are active; direct public equality is rejected by the 20-second self-universe normalization control | promoted `OETU-GRPD-UNIV-DECODER`, `OETU-TYPE-EQUIV-ALGEBRA`, stable generic/shaped equality and action owners, and completed `OETU-OBS-MVP` | reopen only for a view/decoder regression or a stratified, measured direct-rule design | Preserve opaque public equality, finite self-view normalization, single decoder ownership, propositional round trips/transport, and the canonical alias warning result. Reopen direct equality only with stratification or a measured recursion guard. Add no `unif_rule` without a concrete typed consumer and trust classification. |
| `OETU-UNIVERSE-EQUALITY-CAT-DIRECT` | **completed/promoted (2026-07-16)**; canonical direct classifier, exact `CatPathView`, retained generic reflexivity, decoder-owned maps/round trips/path-to-hom square, reflexive Product action, D0b next-hom package, 22 positive/8 negative diagnostics, 15 positive/6 negative reviewer statements, finite self-universe normalization, 971/157 warnings, zero/45/27 audit, 1,539 checks across 53 areas, 35 measured files, and synchronized CI in 165.477s are active; alias-headed and reflexivity-collapse alternatives are rejected | completed `OETU-CAT-UNIV-DECODER`, promoted D0/D0b/D1 fixed-map package/action, Product owner, and closed groupoid-view baseline | reopen only for a classifier/decoder/next-hom regression or when the fixed-arrow certificate representation changes | Preserve the unstratified-policy warning, canonical `(Obj Cat_cat)` LHS, single decoder ownership, generic `eq_refl` provenance, and opaque-certificate reopen trigger. Do not add structured-J/runtime round-trip rules or a `unif_rule` without a real typed consumer and trust classification. |
| `OETU-OMEGA-EQUIV-EVIDENCE-VIEW` | **completed/promoted (2026-07-16)**; nested four-observation record, exact projections, finite path view/reflexivity, one-way evidence-path encoder, D0b next-hom observation, 13 positive/3 negative diagnostics, 10 positive/3 negative reviewer statements, unchanged 971/157 warnings, zero/45/27 audit, 1,555 checks across 54 areas, 36 measured files, and synchronized CI with 186.423s measured checking time are active; direct recursive equality is rejected by 30-second owner-position and 20-second self-normalization controls | promoted D0/D0b/D1 observation owners, structural Sigma/Product paths, and the closed categorical direct baseline | reopen only for a view regression or a recursion-safe reverse decoder/certificate representation | Preserve the finite one-layer/no-eta boundary and exact reuse of all four D0 owners. Do not infer a reverse decoder, extensionality, property-valuedness, truncation, or add a `unif_rule` without an independently justified typed consumer. |
| `OETU-OMEGA-EQUIV-EVIDENCE-DIM-VIEW` | **completed/promoted (2026-07-16)**; exact zero/successor deep observation, D0-owned recursive map, all four projection ladders, finite path view/reflexivity/one-way action, ZeroCat/OneCat controls, 17 positive/5 negative diagnostics, 12 positive/4 negative reviewer statements, unchanged 971/157 warnings, zero/45/27 audit, 1,592 checks across 56 areas, 38 measured files, and synchronized CI with 201.708s measured checking time are active | completed one-layer view, promoted `IsNCat`/`CatDim`, D0 recursive observations, and closed conditional theorem baseline | reopen only for a view regression or a separately selected reverse/extensional representation experiment | Preserve explicit `IsNCat` evidence, strictly decreasing recursion, exact reuse of the four D0 owners, one-way/no-eta scope, and the opaque public certificate. Do not infer a reverse decoder, evidence property, direct equality, or add an unbacked `unif_rule`. |
| `OETU-PRODUCT-DIAMOND` | **completed/promoted (2026-07-16)**; both collapse rules removed, componentwise provenance retained, eleven scoped diagnostics plus adjacent encoder controls and a nine-positive/five-negative reviewer example active, warnings improved to 972/157, zero/45/27 audit, and 29-file CI in 189.90s | stable equality/reflexivity policy and promoted Product decoders | reopen only for a Product provenance regression or a concrete typed proof-time consumer | Preserve componentwise ordinary-iso and omega evidence at reflexivity, the projection/decoder computations, and the negative generic-head comparisons. Add no runtime collapse; add a narrowly typed `unif_rule` only with semantic justification and a real consumer, never as evidence-property erasure. |
| `OETU-CAT-GLOBAL` | accepted omega-level operational policy; legacy arbitrary-`Cat` ordinary-iso capability retired, decoder/Product computation retained | none | any report/kernel text suggests non-univalent `Cat` semantics, restores a global ordinary-iso inhabitant, or mistakes the legacy decoder for a capability | Keep every `C : Cat` omega-univalent and label the policy axiomatic/unstratified. General categories use `CatUnivalence`; ordinary `CatIsoUnivalence` is explicit/OneCat-scoped. |
| `OETU-CAT-SELF` | deferred metatheory | `OETU-CAT-GLOBAL` | model or universe computation is claimed | Compare stratified, impredicative, and operational self-universe readings. |
| `OETU-METATHEORY` | deferred research | mature observational kernel | consistency/canonicity claim is needed | Develop normalization/model evidence; Lambdapi typechecking alone is not sufficient. |

## Acceptance Criteria For Refining This Master Plan

As this active master plan is refined and its remaining owners are promoted:

1. agree on kernel names for `TruncLevel`, `IsTruncGrpd`, truncated universes,
   `CatDim`, and `IsNCat`;
2. preserve the promoted exact `IsDiscreteCat(C) := IsSetGrpd(Obj(C)) ×
   OmegaEquivAlong_{Cat_cat}(Core_incl_func(C))` boundary, its D0b-derived
   homwise fixed-map equivalence whose object action is `path_to_hom`, selected
   arrow-to-path inverse, both coherent directions, and recursive next-hom
   cell; preserve the promoted recursive `IsNCat`/`OneCat` consumer rather
   than retroactively storing a third field;
3. preserve the promoted one-constructor inductive record convention as the
   default for finite named structures, including decoded public signatures,
   named projection beta, generated induction, and no runtime eta by default;
4. approve neutral primary `OmegaEquivAlong(F)` evidence plus the Sigma-
   packaged `OmegaEquiv` boundary, the one-sided reference role of the semantic
   fibre, and the promoted D0 recursive-owner/Sigma/refl/next-hom, D0b
   variable-evidence Cat hom-action, and D1 public migration gates;
   D0b requires the exact forward hom functor, endpoint-correct conjugated
   inverse, one recursive rung, and owner-position audits without a per-instance
   `unif_rule`. Preserve D1's evidence-indexed decoder, opposite/Product owners,
   both-order checks, named equivalence, propositional squares, integrated
   witness, and reserve `IsOmegaEquivArrow(F)` until property-valuedness;
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
   agreement/involution, and Core square. E0 and E1 are now active, including
   the twelve-block warning classification and generic mapped-`DefIso`
   endpoint repair; D1 is now promoted, so separately owned fixed-map
   equivalence packaging is dependency-ready for concrete downstream consumers;
8. retain Candidates G/A/B/C/H, Phase 3's packaged universes, both Phase 4
   path-category slices, `OETU-STRUCTURAL-PATH-COMPAT`,
   `OETU-TYPE-EQUIV-ALGEBRA`, `OETU-GRPD-UNIV-DECODER`, Candidates D0/D0b/D1
   of `OETU-OMEGA-EQUIV-ALONG`, and `OETU-CAT-UNIV-DECODER` as completed
   implementation cores; retain promoted Phase 8 indexed adjunction and both
   Phase 9 formation subgates, and preserve optional path-action refinement as
   distinct from the next fibrancy boundary;
9. approve the hybrid equality contract: generic primitive
   `=`/`eq_refl`/`ind_eqr` at unknown and shaped classifiers, a stable shaped-
   reflexivity registry, semantically anchored path-action refinement, and a distinct fibrancy boundary
   only for additional arbitrary-constructor J computation;
10. approve the H0/H1/H2/Omega0 tier content and the distinction between an
    architecture MVP, foundational implementation skeleton, foundational HoTT
    MVP, and optional H2/HIT completion;
11. preserve the selected permanent `PiHapply`/`PiFunext` runtime/proof-time
    owner, its generic semantically justified reflexive proof-time coherence
    basis, and the reviewed quasi-inverse-to-contractible-fibre route; keep the
    selected-centre computation and the opaque contraction/propositional-eta
    separation under regression;
12. approve the executable foundational corpus: elementary classifier/
    eliminator beta, arbitrary Sigma/record path round trips, ordinary
    equivalence algebra, decoder-owned groupoid-univalence round trips and
    selected action beta, and conversion-level negative controls with their
    metatheoretic limitation;
13. maintain the fixed-map Omega0 equivalence/univalence/action witness and the
    indexed-adjunction triangle/mate witness as separate acceptance gates;
14. approve the immediate-MVP boundary: groupoid decoder round trips and action
    beta are H1; categorical decoder finalization and its integrated next-hom
    witness are promoted jointly with D1 for Omega0; direct computational universe identity is owned by the later
    `OETU-UNIVERSE-EQUALITY` track;
15. approve the local-first comparative-reference policy and require every
    adopted external idea to name its local rewrite/unification owner;
16. retire global ordinary-iso univalence after the OneCat-scoped replacement
    and use omega-level `CatUnivalence` for arbitrary-`Cat` work;
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
supports usable named declarations and categorical univalence, while its Cat
hom-action construction consumes variable evidence and supplies endpoint-
correct inverse and recursive observations;
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
  new D0 recursive-owner probe or the D0b variable-evidence hom-action probe.
- The earlier append-only discreteness evidence is
  `tmp/probes/oetu_discrete_cat_contract.lp`; its warning-enabled log ends in
  `20260715-114925`. It only types the Product and homwise target. The promoted
  result is instead supported by the owner-position cumulative pair
  `tmp/probes/oetu_discrete_cat_owner_full.lp` and
  `tmp/probes/oetu_discrete_cat_owner_checks_full.lp`, plus
  `tmp/probes/oetu_discrete_cat_example.lp`. Their final quiet logs end in
  `20260715-213519`/`213628`/`213709`, warning-enabled logs end in
  `20260715-213724`/`213729`, and they construct the target from D0b evidence
  with its endpoint-correct inverse and recursive observations at the active
  owners.
- The later foundational feasibility review is supported by the ignored
  append-only probes `tmp/probes/oetu_hott_elementary_formers.lp`,
  `tmp/probes/oetu_hott_pi_adequacy.lp`, and
  `tmp/probes/oetu_hott_pi_stable_funext.lp`. Their warning-enabled logs also
  end in `20260714-200013` and pass without probe-local warnings. Because these
  files extend the imported active kernel rather than placing candidates at
  their intended owners, they establish feasibility only and do not confer
  formal `probed` status.
- Candidate G's promotion is supported by the ignored owner-position full-file
  pair `tmp/probes/oetu_elementary_hott_owner_full.lp` and
  `tmp/probes/oetu_elementary_hott_owner_checks_full.lp`. Their final quiet
  logs end in `20260715-154920`/`20260715-154926`; their final warning-enabled
  logs end in `20260715-154934`/`20260715-154940` and preserve the active
  1,109 critical-pair plus 163 LHS-advisory inventory. The matching minimal
  declarations and 17 durable diagnostics are active source, while the
  scratch copies remain evidence only.
- Candidate A's promotion is supported by
  `tmp/probes/oetu_record_convention_owner_full.lp` and
  `tmp/probes/oetu_record_convention_owner_checks_full.lp`. Their final quiet
  logs end in `20260715-160134`/`20260715-160142`; warning-enabled logs end in
  `20260715-160154`/`20260715-160201` and preserve the same 1,109/163
  inventory. The check candidate's nested-Sigma helper/computations are
  comparison evidence only; the active source contains the named record owner
  and nine durable diagnostics, not a parallel Sigma facade.
- Candidate B's promotion is supported by
  `tmp/probes/oetu_trunc_level_owner_full.lp` and
  `tmp/probes/oetu_trunc_level_owner_checks_full.lp`. Final quiet logs end in
  `20260715-161037`/`20260715-161050`; warning-enabled logs end in
  `20260715-161102`/`20260715-161111` with the unchanged 1,109/163 inventory
  and zero strict-LHS candidates. The active source/checks contain the
  property kernel and 15 diagnostics only, not the earlier append-only
  packaged-universe tail.
- Phase 3's promotion is supported by
  `tmp/probes/oetu_trunc_universe_owner_full.lp` and
  `tmp/probes/oetu_trunc_universe_owner_checks_full.lp`. Final quiet logs end
  in `20260715-162213`/`20260715-162220`; both warning-enabled logs end in
  `20260715-162232` with the unchanged 1,109/163 inventory, no package-owner
  warning, and zero strict-LHS candidates. The active source/checks contain
  the named carrier/evidence package, three low-level aliases, eleven positive
  checks, and the no-eta/evidence-retention/no-same-level negative controls;
  they contain no package path/univalence, proof erasure, closure theorem,
  universe-level truncation theorem, or reflector.
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
  distinct pre/post action-owner interpretation. These earlier alternatives
  are not promoted source.
- The E0 collapse-removal conclusion is supported by
  `tmp/probes/oetu_path_symmetry_removal_full.lp` and
  `tmp/probes/oetu_path_symmetry_removal_checks_full.lp`. Their successful
  warning-enabled logs end in `20260715-015457` and `20260715-015535`; the
  source reports 1,072 unjoinable pairs. This pair intentionally supplies no
  replacement symmetry and exists to prove that removal is independently
  feasible.
- The final promoted E0 decision is supported by
  `tmp/probes/oetu_path_comp_promotion_full.lp` and
  `tmp/probes/oetu_path_comp_promotion_checks_full.lp`. Final quiet logs end in
  `20260715-164934`/`164939`; final warning-enabled logs end in
  `20260715-164427`/`164430` and report 1,072 unjoinable pairs plus 159
  replaceable pattern variables. The strict audit is clean. Intermediate
  owner-position logs `163612`, `163650`, and `163750` show the endpoint-
  minimization sequence and that the four oriented-action runtime bridges
  raise the inventory to 1,077/165. The active decision instead uses two local
  typed general-comparison witnesses in the diagnostic module, four unit
  specializations, and four runtime-negative controls.
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
  `OmegaEquivAlong(PathSym_A)` and is the pre-classification predecessor, not
  the promoted final source.
- The promoted E1 result is supported by
  `tmp/probes/oetu_path_symmetry_promotion_full.lp` and
  `tmp/probes/oetu_path_symmetry_promotion_checks_full.lp`. Quiet logs end in
  `20260715-170120`/`170345`; warning-enabled logs end in
  `20260715-170137`/`170838` at 974 unjoinable pairs plus 159 replaceable
  variables. Four mapped-cancellation consumers fail before the six endpoint
  guards are minimized and pass afterward; the same owner change removes 110
  reports. Typed action/naturality pairs and untyped Product negative controls
  classify the remaining six E1 reports. Strict LHS audit is zero with 41
  annotated slots across 24 clauses.
- Candidate C's promoted result is supported by
  `tmp/probes/oetu_shaped_reflexivity_owner_full.lp` and
  `tmp/probes/oetu_shaped_reflexivity_owner_checks_full.lp`. Final quiet logs
  end in `20260715-173016`/`173421`; warning-enabled logs end in
  `20260715-173024`/`173435` at 991 unjoinable pairs plus 157 replaceable
  variables. The earlier inferred-PathSym-category warning log `172950`
  records 995/157, so the retained explicit category guard has a measured
  four-report benefit. An earlier pre-minimization variant recorded 995/162;
  the two generic Sigma payload and three registration-classifier refinements
  account for the five-advisory decrease. The final 17 Candidate C reports
  are covered by literal/shaped joins, typed post/pre/naturality pairs, and an
  impossible displayed-target negative control. Strict LHS audit is zero with
  45 annotated slots across 27 clauses. The active source and 40 diagnostics
  match the candidate; the scratch files remain owner-position evidence only.
- The elementary observational-equality continuation is supported by the
  cumulative owner/check pair now named
  `tmp/probes/oetu_obs_sum_owner_full.lp` and
  `tmp/probes/oetu_obs_sum_owner_checks_full.lp`; its earlier Boolean, Unit,
  and Nat names are recorded in the probe inventory with their dated logs. Durable
  reviewer statements are in `examples/boolean_observational_equality.lp`,
  `examples/unit_observational_equality.lp`, and
  `examples/nat_observational_equality.lp`, with the parameterized continuation
  in `examples/sum_observational_equality.lp`. The rejected unguarded recursive
  interaction is reproduced by
  `tmp/probes/oetu_obs_nat_j_subject_reduction.lp`: before the selected J guard
  its computed normal form erases a proof index whose branch/result types are
  executable non-convertible; afterward the same term remains stuck. Final
  guarded quiet logs end in `20260716-043247`/`043414`, warning logs in
  `20260716-043427`/`043428`, and the Nat reviewer log in
  `20260716-043749`. The sum-specific guard is reproduced by
  `tmp/probes/oetu_obs_sum_j_subject_reduction.lp`; final minimized Sum quiet
  and warning log pairs end in `20260716-050336` and `050351`, and its guard
  and reviewer logs end in `20260716-050426` and `050744`.
- The first groupoid-universe identity comparison is supported by
  `tmp/probes/oetu_universe_equality_direct_owner_full.lp` and its full-check,
  signature, self-compute, baseline, and standalone-`TypeEquiv` controls,
  together with `tmp/probes/oetu_universe_equality_view_owner_full.lp` and its
  full-check, self-compute, and reviewer probes. The direct canonical-owner
  source/check logs end in `20260716-053346`/`055048`, its warning logs in
  `20260716-053345`/`053447`, and the rejecting recursive self-universe timeout
  in `20260716-053636`; finite controls end in `20260716-053720`. The selected
  named-view source/check logs end in `20260716-053946`/`054135`, warning logs
  in `20260716-054151`/`054233`, and the active durable reviewer
  `examples/groupoid_universe_identity_view.lp` passes in
  `20260716-054558`. These files record why the finite decoder-owned view is
  promoted while direct public equality requires stratification or a measured
  recursion guard.
- The categorical-universe identity decision is supported by
  `tmp/probes/oetu_universe_equality_cat_direct_owner_full.lp` and its full
  checks, signature, and self-compute controls; the alias-headed and shaped-
  reflexivity comparisons; and
  `tmp/probes/oetu_universe_equality_cat_selected_owner_full.lp` with its full
  checks, self/Product computation, and reviewer probe. Canonical direct
  source/check logs end in `20260716-060812`/`060824`, the focused signature
  in `060849`, and warning evidence in `060935` at 971/157. The reducible
  `Cat_grpd` spelling records 972/157 in `061218`; the rejected global
  reflexivity collapse fails the inherited object-path action check in
  `061303` and records 974/157 in `061331`. Selected source/check logs end in
  `061546`/`061859`, warnings in `061725`, finite self/Product and scratch-
  reviewer evidence in `061859`, and the durable
  `examples/categorical_universe_identity.lp` reviewer in `062228`. These
  files justify the direct classifier together with retained generic
  reflexivity, decoder ownership, the D0b next-hom consumer, and the explicit
  opaque-certificate reopen trigger.
- The fixed-arrow evidence-view decision is supported by
  `tmp/probes/oetu_omega_equiv_evidence_view_owner_full.lp`, its full checks,
  signature and self-compute controls, the contrasting
  `tmp/probes/oetu_omega_equiv_evidence_direct_owner_full.lp`, the append-only
  direct self-compute control, and the scratch/active reviewers. Finite quiet
  source/signature/check logs end in `20260716-093253`/`093344`/`093545`,
  warning-enabled source/check logs in `093558`/`094030`, finite self-view
  normalization in `093726`, and scratch/active reviewer logs in
  `094135`/`094320`. The owner-position direct source timeout ends in `093406`,
  its warning-enabled timeout in `093504`, and the append-only self-universe
  timeout in `093654`. These files justify the finite one-layer observation
  view, one-way encoder, and retained absence of direct evidence equality,
  reverse decoding, eta, property-valuedness, or truncation.
