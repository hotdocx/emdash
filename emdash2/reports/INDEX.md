# EMDASH Reports Index

Date: 2026-07-18

Use this file as the first stop for report discovery. `emdash3_2.lp` remains
the active kernel authority; `emdash3_2_eq1_hom_action.lp` is its one-way
derived native-EQ1 hom-action/groupoidality extension, and
`emdash3_2_eq1_evidence_property.lp` is the downstream transparent
evidence-property and finite-`NCat` object-truncation extension.
`emdash3_2_nat_arithmetic.lp` owns reusable Nat addition, associativity, and
sethood independently of the walking construction.
`emdash3_2_sum_observational_action.lp` retains the former-specific Sum action
as a library module rather than kernel infrastructure.
`emdash3_2_walking_end_hit.lp` imports that Nat module and currently contains
the previously promoted generated-word walking/`BNat` implementation. The
reopened walking plan rejects that word-carrier presentation as the intended
HIT; it remains active code only until the opaque replacement and corrected
proofs are promoted. Reports explain current status, mathematics, notation,
implementation plans, and historical decisions.

## Current Orientation

- `REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`:
  living current architecture, validation workflow, rewrite/unification SOP,
  and deferred boundaries.
- `EMDASH_FOUNDATIONS.md`: mathematician-facing guide to the implemented
  foundations and explicit staging limits.
- `REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`: notation
  authority for comments, examples, and future parser work.

## Current Plans

- `REPORT_EMDASH_V3_2_WALKING_ENDOMORPHISM_DIRECTED_HIT_PLAN_2026-07-17.md`:
  reopened corrective plan. The committed generated-word Hom presentation is
  rejected as the intended HIT. Focused probes validate an opaque
  `WalkingEnd`, judgmental point/loop beta, whole-HIT Nat Code/encode, Nat
  powers, and both transparent inverse proofs using a minimal opaque 1-cell
  HIT eliminator. The review rejects the earlier bodyless `PathOut` motive:
  enriched-slice transport is not directed-arrow `J`. Before active migration,
  the plan must select the 1-cell eliminator as a primitive component of this
  concrete categorical HIT or derive it from stronger reusable
  displayed-category/free-category infrastructure. Full functor-category
  initiality remains outside this practical computation milestone.
- `REPORT_EMDASH_MATHOPS_DEVOPS_IMPLEMENTATION_PLAN_2026-06-16.md`:
  active MathOps/DevOps/SOP improvement plan and utility roadmap.
- `REPORT_EMDASH_V3_2_PI_ALONG_FUNCTOR_IMPLEMENTATION_PLAN_2026-06-11.md`:
  proposed dependent products along functors and comma-category
  infrastructure.
- `REPORT_EMDASH_V3_2_PROFUNCTOR_REPRESENTABILITY_REDESIGN_PRELIM_PLAN_2026-06-19.md`:
  active representability/computational-comparison redesign and deferred
  internalization ledger.
- `REPORT_EMDASH_V3_2_OBSERVATIONAL_EQUALITY_TRUNCATION_UNIVALENCE_REDESIGN_PLAN_2026-07-13.md`:
  retained living predecessor/master ledger integrating full
  observational equality, HoTT truncation and `Prop`/`Set`/`n`-groupoid
  universes, directed `n`-categories and `OneCat`, finite dependent-record
  encoding, and coherent global computational univalence; Candidate G's
  decoded Empty/Bool/Nat slice and Candidate A's named dependent-record
  convention, Candidate B's recursive truncation-property kernel, and the
  Phase-3 packaged truncated universes plus both Phase 4 path-category slices
  are promoted; E1 adds functor-owned path symmetry, propositional coherence,
  and the evidence-led mapped-`DefIso` endpoint repair. Phase 5 Candidate C's
  dependent/nested PathRecord equality, stable shaped reflexivity, closed
  literal-reflexivity registry, and reflexive `J` are now promoted. Candidate
  H adds ordinary `PiHapply`/`PiFunext`, pointwise beta, generic-J
  propositional eta, and active contractible-fibre equivalence packaging.
  `OETU-STRUCTURAL-PATH-COMPAT` adds arbitrary propositional Sigma round trips
  and transparent named PathRecord round trips with reflexive and nested
  diagnostics. `OETU-TYPE-EQUIV-ALGEBRA` adds identity, symmetry, and
  categorical-order composition with derived contractible-fibre closure and
  executable map projections. `OETU-GRPD-UNIV-DECODER` names both decoder
  round trips, derives the canonical contractible-fibre capability, and adds
  propositional transport/Product/Pi action coherence while rejecting a broad
  runtime fold. Candidate D0 of `OETU-OMEGA-EQUIV-ALONG` now supplies the
  independent fixed-arrow certificate, transparent Sigma package, reflexive
  evidence, and recursive next-hom computation. Candidate D0b now adds the
  variable-evidence Cat hom action with endpoint-correct conjugated inverse
  functors and iterable cell observations. Candidate D1 now promotes the
  public fixed-map Sigma normal form, evidence-owned opposite/Product closure,
  categorical decoder round trips and named equivalence, one-sided fibre
  comparison, and the first integrated next-hom univalence/action witness.
  Phase 8 now promotes the independent indexed `Adjunction(F,G)` owner,
  transparent functor views, stable unit/counit observations, triangles,
  opposite and mate consumers, with no unbacked named-operation equation. The
  Phase 9 now promotes the exact two-field `IsDiscreteCat` boundary,
  D0b-derived core homwise evidence, `hom_to_path`, both coherent round trips,
  and a recursive-cell reviewer example without adding a homwise field or
  runtime cancellation. The same phase now also promotes independent
  `IsObjTruncCat`, native `CatDim`, recursive `IsNCat`, evidence-retaining
  `NCat`/`ZeroCat`/`OneCat`, and a next-hom OneCat consumer. The implication to
  object truncation and scoped ordinary-iso univalence retain their explicit
  later dependencies rather than being smuggled into formation. The current
  Phase 10 now promotes registered `ObsAction`/`ObsDAction`, sound semantic
  agreement, identity/composite computation, PathRecord open-map action,
  dependent witness-field transport, componentwise binary-sum action, and the
  first recursive-inductive registration: Nat successor retains the exposed
  predecessor path while agreeing propositionally with generic `eq_ap`. The
  independently statused general binary-sum
  carrier/classifier, dependent eliminator, both betas, and non-collapse
  control, and the next bounded prerequisite adds the recursive
  `CatDim -> TruncLevel` object-level index without claiming the still-blocked
  object-truncation theorem. That index now passes synchronized CI. General
  `TypeEquiv` invariance of `IsTruncGrpd` and its decoder-owned fixed-map
  categorical object-truncation consumer are also promoted with synchronized
  20- and 21-file CI. General one-step truncation monotonicity is now promoted
  by explicit contractible-path contraction and native level recursion, with
  1,261 classified checks and a 22-file CI gate passing in 127.18s. Recursive
  Sigma/Pi paths and a stable recursive owner now also prove that
  `IsTruncGrpd(n,A)` evidence is proposition-valued, bringing the catalog to
  1,279 checks and the health inventory to 23 files without changing 978/157
  warnings; the synchronized CI gate passes in 75.41s. Arbitrary-level
  dependent-Pi truncation closure is now promoted through `is_trunc_pi`, with
  a stable base/successor consumer owner, 1,290 classified checks across 41
  areas, 24 measured files, unchanged 978/157 warnings and zero/45/27 audit,
  and a synchronized 24-file CI gate passing in 131.21s. At that gate,
  recursive omega-equivalence evidence truncation and the needed Sigma
  argument still blocked the `IsNCat` implication. Same-level dependent-Sigma
  closure is now also
  promoted, with 1,302 checks across 42 areas, 25 measured files, unchanged
  978/157 warnings and zero/45/27 audit, and 25-file CI passing in 136.09s.
  The Sigma blocker is therefore closed; recursive fixed-arrow evidence remains
  blocked on the opaque `OmegaEquivAlong_D0` representation. Truncated-universe
  carrier/evidence path control is now promoted through a named path view,
  evidence-derived reconstruction, propositional round trips, and an ordinary
  path `TypeEquiv`, with 1,320 checks across 43 areas, 26 measured files,
  unchanged 978/157 warnings, zero/45/27 audit, and 26-file CI passing in
  188.15s. Restricted ambient-univalence agreement is now also promoted by
  composing the package-path equivalence with the canonical groupoid decoder;
  1,335 checks across 44 areas and 27 measured files retain 978/157 warnings
  and zero/45/27 audit, with 27-file CI passing in 282.49s. The expected
  universe-level theorem is now promoted too: explicit-inverse contractible
  `TypeEquiv` closure, successor Pi/Sigma/property closure, and restricted
  package univalence prove `TruncGrpdU(n)` is `(n+1)`-truncated. The resulting
  1,355 checks across 45 areas and 28 measured files retain 978/157 warnings
  and zero/45/27 audit, with 28-file CI passing in 155.30s. Product
  reflexivity provenance is now promoted too: removing the two ordinary-iso
  and omega Product collapse rules retains componentwise evidence through
  recursive cells and decoders, improves warnings to 972/157, and adds no
  replacement rule or `unif_rule`. The synchronized result has 1,360 checks
  across 46 areas, 29 measured files, zero/45/27 audit, a focused nine-
  positive/five-negative reviewer example, and 29-file CI passing in 189.90s.
  Visible-constructor Boolean observational equality is now promoted too. Its
  four closed cases compute only the Unit/Empty classifier matrix, retaining
  generic reflexivity provenance and rejecting an `eq_refl -> tt` plus closed-
  registry orientation that added 42 unjoinable reports. The selected minimum
  adds 22 positive/11 negative diagnostics and an 11-positive/6-negative
  reviewer example, keeps 972/157 warnings and zero/45/27 audit results, and
  brings the synchronized gate to 1,393 checks across 47 areas and 30 measured
  files; 30-file CI passes in 143.199s. Visible Unit equality is now promoted
  under the same policy: one classifier equation, 10 positive/9 negative
  diagnostics, a 7-positive/6-negative reviewer example, unchanged warning/
  audit results, 1,412 checks across 48 areas, and 31-file CI in 153.385s.
  Recursive visible Nat equality is now promoted jointly with its discovered
  generic-J subject-reduction prerequisite. The rejected classifier-only
  candidate let predecessor or foreign reflexivity fire the broad inferred-
  endpoint J beta and normalized a proof-dependent term to a branch that did
  not inhabit its declared result. The selected J owner repeats category and
  endpoint, preserves normal outer-reflexivity computation, adds no registry
  or `unif_rule`, and removes one older PathRecord overlap. The Nat and guard
  areas add 23 positive/15 negative diagnostics plus an 11-positive/8-negative
  reviewer example, improving warnings to 971/157 and bringing the synchronized
  snapshot to 1,450 checks across 50 areas and 32 measured files; 32-file CI
  passes in 151.336s. General visible binary-sum equality is now promoted under
  the guarded contract: equal tags recurse to component equality, mixed tags
  expose Empty, and outer reflexivity remains distinct from component
  reflexivity. Minimizing six reconstructible constructor indices keeps the
  slice warning-neutral at 971/157 and zero/45/27 audit. Its 24 positive/11
  negative diagnostics and 12-positive/8-negative reviewer example bring the
  snapshot to 1,485 checks across 51 areas and 33 measured files; 33-file CI
  passes with 161.044s of measured checking time (167.96s wall time).
  Fibrancy and broader structured-J computation
  remain prerequisite on a sound classifier/motive capability and a selected
  concrete beta. The first Phase-13 groupoid-universe identity slice is now
  completed/promoted with synchronized 34-file CI:
  `GrpdPathView(A,B)` exposes the existing
  `TypeEquiv(A,B)` decoder through named encode/decode, both propositional
  round trips, and transport agreement without changing public equality.
  The warning-neutral direct equality candidate is rejected because
  self-universe normalization recursively reopens the same equality and
  exceeds 20 seconds; the named view remains finite. Seventeen positive/seven
  negative diagnostics and a 14-positive/5-negative reviewer example bring
  the snapshot to 1,509 checks across 52 areas and 34 measured files while
  retaining 971/157 warnings and zero/45/27 audit. No rule or `unif_rule` is
  added. The final gate passes with 182.160s of measured checking time
  (189.18s wall time). The bounded categorical comparison has now selected
  and promoted the canonical direct owner with synchronized 35-file CI:
  public `@=(Obj Cat_cat,A,B)` reduces to
  `CatPathView(A,B) := OmegaEquiv(Cat_cat,A,B)`. Decoder-owned encode/decode
  and propositional round trips, explicit package reflexivity, functor and
  evidence projections, reflexive Product action, and a D0b next-hom consumer
  are active with 22 positive/8 negative diagnostics and a 15-positive/
  6-negative reviewer example. Self-universe normalization terminates at the
  opaque fixed-arrow certificate; warnings remain 971/157 and the strict
  audit zero/45/27. Generic `eq_refl` remains distinct: collapsing it adds
  three reports and breaks the inherited object-path `eq_ap` consumer. One
  classifier rule and no `unif_rule` are added. The closed snapshot has 1,539
  checks across 53 areas, a 17,989-line/750-symbol/575-rule/51-unification-
  rule kernel, and 1,389 positive diagnostics. CI passes with 165.477s of
  measured checking time (171.88s wall time). The next bounded Phase-13 slice
  selects the finite one-layer `OmegaEquivAlongPathView_D0`: its nested
  Sigma/Product observation record reuses both inverse-arrow and recursive-
  cell owners, canonical reflexivity and one-way evidence-path action compute,
  and D0b next-hom evidence is observable through it. The direct recursive
  equality candidate is rejected because its owner-position source exceeds
  30 seconds and its append-only canonical self-universe control exceeds 20
  seconds; the finite control passes. Thirteen positive/three negative active
  diagnostics and a 10-positive/3-negative reviewer pass with unchanged
  971/157 warnings and zero/45/27 audit. Five semantic symbols add no rule or
  `unif_rule`. The closed snapshot has 1,555 checks across 54 areas, an
  18,104-line/755-symbol/575-rule/51-unification-rule kernel, and 1,402
  positive diagnostics across 36 measured files. The full reviewer sweep and
  synchronized CI pass with 186.423s of measured checking time (193.35s wall
  time). No reverse decoder, eta, property-valuedness, or truncation theorem is
  inferred. Dependency review selects a bounded conditional
  `IsNCat -> IsObjTruncCat` induction next: it will consume an explicit global
  fixed-arrow evidence-property capability, completing the already-ready
  Sigma/univalence proof architecture without pretending that the opaque
  certificate or finite view supplies that capability. That conditional owner
  is now promoted pending final gates: `OmegaEquivAlongEvidenceProp_D0` names
  but does not inhabit the premise; `prop_is_trunc_cat_dim` lifts it; and
  `ncat_obj_trunc_from_evidence_prop` computes through the discrete base and
  homwise Sigma/univalence successor. Eleven positive/four negative diagnostics
  and an 8-positive/4-negative reviewer pass with unchanged 971/157 warnings
  and zero/45/27 audit. A typed `eq_refl` negative confirms that no
  `unif_rule` erases distinct capability inputs. The closed snapshot has 1,570
  checks across 55 areas, an 18,173-line/758-symbol/577-rule/51-unification-
  rule kernel, and 1,413 positive diagnostics across 37 measured files. The
  full reviewer sweep and synchronized CI pass with 198.816s of measured
  checking time (206.34s wall time). The dependency-ready representation
  continuation is now completed/promoted: the explicit
  `CatDim`/`IsNCat`-indexed observation is Unit at zero and at successor stores
  both inverse arrows and recursively observed D0 cells at the smaller
  dimension. All four projection/recursion owners, finite path reflexivity and
  one-way action, ZeroCat erasure, and OneCat termination pass. Seventeen
  positive/five negative diagnostics and a 12-positive/4-negative reviewer
  preserve 971/157 warnings and zero/45/27 audit; six symbols and two two-
  equation rule families add no `unif_rule`. The snapshot has 1,592 checks
  across 56 areas, an 18,452-line/764-symbol/579-rule/51-unification-rule
  kernel, and 1,430 positive diagnostics across 38 measured files. There is no
  reverse decoder, eta, public certificate equality, or evidence-property
  inhabitant. The full reviewer sweep and synchronized 38-file CI pass with
  201.708s of measured checking time (212.59s wall time). The next independent
  elementary-action slice is now completed/promoted: eliminator-owned
  `sum_map` lifts two registered summand
  actions through `sum_obs_action`, using Empty for mixed tags and explicit
  propositional agreement with generic `eq_ap`. A direct two-action
  proof-time equation failed because transparent `eq_ap` unfolds first; one
  stable reflexive basis per tag plus two direct former-specific `unif_rule`s
  per basis is selected instead, and the arbitrary theorem explicitly
  composes those paths rather than assuming unification transitivity. Twenty-
  one positive/six negative diagnostics and a 13-positive/4-negative reviewer
  pass with unchanged 971/157 warnings and zero/45/27 audit. Thirteen symbols
  and four proof-time equations add no runtime rewrite; the current snapshot
  has 1,619 checks across 57 areas, an 18,883-line/777-symbol/579-rule/55-
  unification-rule kernel, 1,451 positive diagnostics, and 39 measured files;
  synchronized CI passes with 129.250s of measured checking time.
  Runtime proof provenance, arbitrary structured J/fibrancy, proof erasure,
  no-confusion/canonicity, coproduct structure, and other former actions remain
  separate. The bounded `OETU-ONECAT-ISO` probe has now implemented its sound
  one-sided prerequisite. Strict `IsoEvidence` constructs recursive D0 omega
  evidence by encoding both inverse equations as categorical paths; a single
  semantically backed proof-time comparison handles reflexive evidence after a
  runtime fold added four unjoinable reports. The canonical decoder gives a
  OneCat-scoped path and the decoder-after-`idtoiso_cat` round trip without
  using frozen global `cat_iso_univalence`. Twelve positive/six negative
  diagnostics and a nine-positive/four-negative reviewer pass at unchanged
  971/157 warnings and zero/45/27 audit. The snapshot has 1,637 checks across
  58 areas, a 19,062-line/782-symbol/581-rule/56-unification-rule kernel,
  1,463 positive diagnostics, and 40 measured files; full examples and
  synchronized CI pass with 281.823s of measured checking time. At that
  checkpoint the full scoped capability had an explicit next prerequisite:
  arbitrary omega evidence has separate left/right inverse arrows, so it
  needed a directed comparison and discrete-hom path before right-law
  transport and the nested-Sigma reverse round trip. No rewrite or unbacked
  `unif_rule` identifies those inverses, and the frozen arbitrary-category
  interface remains unused by the new owners.
  The dependency-ready inverse-comparison continuation is now implemented in
  the active kernel. The rejected direct `Hom_func` composition exposed two
  unit comparisons and associativity that cannot depend on unification
  transitivity; the selected construction instead uses stable post/pre
  whiskering plus an explicit propositional associator. It produces
  `omega_equiv_along_left_to_right_D0` generically and
  `one_cat_omega_inverse_path` through OneCat hom discreteness, with no new
  rewrite or `unif_rule`. Nine positive/four negative diagnostics and six
  positive/three negative reviewer additions bring the current snapshot to
  1,650 checks across 59 areas and the reviewer to fifteen positive/seven
  negative statements. Warnings remain 971/157, the audit remains zero/45/27,
  health checks 40 files at 19,373 kernel lines/790 symbols/581 rules/56
  unification rules and 1,472 positive diagnostics, and full examples plus
  synchronized CI pass with 139.872s of measured checking time. Full scoped
  univalence then waited only on right-law transport and the nested-Sigma
  reverse evidence round trip, not on inverse comparison.
  That continuation is now completed in the active kernel. Decoded recursive
  laws, ordinary equality transport, and the inverse path reconstruct
  `IsoEvidence`; OneCat hom discreteness compares both inverse-law proof
  fields, and the promoted nested-Sigma path owner proves reconstruction after
  the ordinary lift. The resulting second round trip derives the new
  OneCat-indexed specified-inverse capability, contractible-fibre
  `one_cat_iso_univalence`, and `one_cat_iso_type_equiv`. A rejected packaging
  through the global decoder classifier is recorded at `132624`: its type
  hardcodes the frozen `iso_evidence_path`. The selected scoped classifier
  passes owner quiet/warning logs `133706`/`133718`, inherited-suite logs
  `133745`/`133751`, and the 32-positive/12-negative reviewer log `134212`.
  Ten symbols, no rewrite, and no `unif_rule` preserve 971/157 warnings and
  zero/45/27 audit; thirteen positive/two negative diagnostics bring the
  catalog to 1,678 checks across 61 areas with zero unclassified checks.
  Health passes across 40 files at 19,883 kernel lines/804 symbols/581
  rules/56 unification rules with 1,495 positive diagnostics, and full
  examples pass. Synchronized CI passes with 109.546s measured checking time.
  The scoped construction is closed. The inventory-backed retirement is now
  promoted: `cat_iso_univalence`, `cat_iso_univalence_by_decoder`, and
  `CatIsoUnivalenceByDecoder` had no kernel consumer and are removed, while
  generic `isotoid_cat` is migrated to the scoped inhabitant and the
  still-consumed `iso_evidence_path` Product compatibility owner remains.
  Owner/check quiet logs end in `140150`/`140155`, warning logs in
  `140205`/`140228`, and the 33-positive/11-negative reviewer in `140406`.
  Warnings remain 971/157, audit remains zero/45/27, and the catalog has
  1,675 checks/61 areas. Health passes across 40 files at 19,859 kernel
  lines/801 symbols/581 rules/56 unification rules with 1,493 positive
  diagnostics, and full examples plus synchronized CI pass; CI records
  212.799s measured checking time. The retirement slice is closed.
  The next former-action continuation is now completed/promoted. Recursive Nat
  successor equality exposes its predecessor path, so
  `nat_succ_obs_action` selects `p |-> p`; a stable basis has two direct,
  narrowly typed proof-time comparisons with component and outer reflexivity,
  and generic `ind_eqr` derives arbitrary agreement with `eq_ap(succ)` without
  runtime collapse or unification transitivity. Fourteen positive/five negative
  diagnostics and an 11-positive/5-negative reviewer pass. Seven symbols and
  two `unif_rule`s add no runtime rewrite, preserve 971/157 warnings and the
  zero/45/27 audit, and bring the snapshot to 1,694 checks/62 areas, a
  19,988-line/808-symbol/581-rule/58-unification-rule kernel, 1,507 positive
  diagnostics, and 41 measured files. Full examples and synchronized CI pass;
  CI records 220.269s measured checking time. No successor-specific J beta,
  Nat canonicity, or proof erasure is claimed.
- `REPORT_EMDASH_V3_2_DEFISO_HOM_ACTION_PROFCOMPARISON_MIGRATION_PLAN_2026-06-28.md`:
  active incremental `DefIso`, hom-action, and `ProfComparison` migration.
- `REPORT_EMDASH_V3_2_EQUIPMENT_SHADOW_TENSOR_JOIN_REDESIGN_PLAN_2026-06-28.md`:
  active/deferred redesign of remaining equipment-shadow, tensor,
  co-Yoneda, and primitive-join ownership.
- `REPORT_EMDASH_V3_2_FULL_NATURALITY_PRELIM_PLAN_2026-06-12.md`:
  full-naturality follow-up after the first implemented slice.
- `REPORT_EMDASH_V3_2_FUNCTOR_STRUCTURAL_LOGIC_PRELIM_PLAN_2026-06-04.md`:
  ordinary structural functor logic and displayed/product follow-ups.
- `REPORT_EMDASH_V3_2_PROFUNCTOR_WEIGHTED_LIMITS_PRELIM_PLAN_2026-06-17.md`:
  implementation log plus remaining profunctor, weighted-limit, duality, and
  directed-inductive follow-ups after the first end-to-end pass.

## Completed Or Promoted Decision Records

These reports remain active references for exact decisions and probe evidence,
but their promoted phases are not open implementation plans.

- `REPORT_EMDASH_V3_2_EQUALITY_VALUED_OMEGA_EQUIVALENCE_REREDESIGN_PLAN_2026-07-17.md`:
  completed selected-MVP overlay for native equality-valued fixed-arrow
  evidence, the stable first-class facade and explicit path adapters, direct
  Cat/Grpd univalence boundaries, native next-hom action, internal
  groupoidality, structured `PathOut`/`J`, unrestricted evidence uniqueness,
  unconditional finite-`NCat` object truncation, and Sum-action demotion.
  Native theorem modules are decoder/D0-free; raw unreified-path observers,
  reverse coherent-core assembly, consumer-led core-universe functors, full
  compatibility retirement, and metatheory remain separate bounded work.
- `REPORT_EMDASH_V3_2_GROUPOID_COMPUTATIONAL_UNIVALENCE_IMPLEMENTATION_PLAN_2026-06-23.md`:
  promoted historical implementation ledger for the first groupoid,
  type-equivalence, computational-univalence, omega-equivalence, and generic
  comparison slices; superseded for forward work by the observational-
  equality/truncation/univalence master plan.
- `REPORT_EMDASH_V3_2_DISPLAYED_IDENTITY_TDAPP0_COHERENCE_CLEANUP_PLAN_2026-07-13.md`:
  promoted transparent generic displayed identity, typed identity consumers,
  four naturality projection-order joins, and the warning-neutral SOP-minimal
  pointwise `tdapp0_fapp0` vertical-composition projection beta.
- `REPORT_EMDASH_V3_2_PRIMITIVE_PI_ELIMINATOR_AUDIT_AND_REDESIGN_PLAN_2026-07-13.md`:
  retained `piapp0*`/`piapp1*` as typed semantic definitions, promoted the
  missing generic full/capped `tapp0_func` hom projections to
  `tdapp0_func`/`tdapp0_fapp0`, and verified the first `piapp1_func` next action
  through `fdapp1_int_hom_fapp0`.
- `REPORT_EMDASH_V3_2_PRIMITIVE_PI_FACADE_REARCHITECTURE_PLAN_2026-07-12.md`:
  promoted `Pi_cat` from a transparent alias to the stable primitive section
  facade, with direct proof-time comparisons, runtime `Obj`/`Hom_cat`
  projections, and the Sigma-section uncurrying/path-induction boundary.
- `REPORT_EMDASH_V3_2_DISPLAYED_FACADE_TOWER_REARCHITECTURE_PLAN_2026-07-11.md`:
  promoted the levelwise proof-time/runtime boundary for the displayed
  `Catd`/`Functord`/`Transfd` tower, constant-section owner split,
  `sigma_map_transf`, and explicit `Prof_cat` endpoint recovery; its deferred
  path-induction section owner was resolved by the primitive-`Pi_cat` facade,
  while the Sigma off-diagonal prerequisite remains recorded.
- `REPORT_EMDASH_V3_2_DOCUMENTATION_KERNEL_MAINTENANCE_IMPLEMENTATION_PLAN_2026-07-10.md`:
  completed authority consolidation, mathematical/notation refresh, adjacent
  documentation across executable sections 0–19, and diagnostic-navigation
  cleanup; broad naming and module-split work remains explicitly deferred.
- `REPORT_EMDASH_INFINITY_CODEX_IMPLEMENTATION_PLAN_2026-06-23.md`:
  completed local final-response archive and compaction/resume recovery flow.
- `REPORT_EMDASH_V3_2_NOTATION_MIGRATION_AND_REORG_IMPLEMENTATION_PLAN_2026-06-05.md`:
  completed notation/check-file split history with remaining work transferred
  to current maintenance/reorganization plans.
- `REPORT_EMDASH_V3_2_CAT_CATD_SPECIALIZATION_ALIAS_MIGRATION_PLAN_2026-07-04.md`:
  promoted generic-owner migration for Cat/Catd specialization aliases and
  retained Cat-only projection structure.
- `REPORT_EMDASH_V3_2_COMP_PROD_FUNC_UNIT_PROF_ACTION_SUBPLAN_2026-07-07.md`:
  promoted product-composition owner and direct unit-profunctor action.
- `REPORT_EMDASH_V3_2_HOM_VARIANCE_SEPARATION_AND_HOM_FAPP0_CLEANUP_PLAN_2026-07-09.md`:
  completed variance separation, rigid-`Hom` selection, proof-time comparison
  boundary, and middle-constrained identity follow-up.
- `REPORT_EMDASH_V3_2_PROF_CAT_PRIMITIVE_REDESIGN_PLAN_2026-07-06.md`:
  promoted primitive fixed-endpoint `Prof_cat`, public surface, and
  `Unit_prof`/representable reindex architecture.
- `REPORT_EMDASH_V3_2_ECKMANN_HILTON_APPLICATION_PLAN_2026-07-03.md`:
  promoted conservative Eckmann-Hilton computation and recorded broader
  textbook/presentation follow-ups.

## Deferred Reorganization And Presentation Plans

- `REPORT_EMDASH_V3_2_REORGANIZATION_PLAN_2026-06-16.md`: the first
  single-file section/assertion reorganization is reflected in the active
  source; module splitting remains deferred until boundaries stabilize.
- `REPORT_EMDASH_V3_2_INDEX_3_2_READABILITY_IMPLEMENTATION_PLAN_2026-06-06.md`:
  print/index readability work.
- `REPORT_EMDASH_V3_2_RESEARCH_ARTICLE_ARCHITECTURE_2026-06-05.md`:
  research-article and paper narrative architecture.

## Audits And Retirements

- `REPORT_EMDASH_V2_RETIREMENT_AUDIT_2026-06-16.md`: audit for retiring the
  obsolete v2 baseline and consolidated v2 report.

Retired source files and superseded reports live under ignored `.scratchpad/`
paths. Do not consult them during normal work unless historical recovery is
explicitly requested.

## Generated Or Semi-Generated Reports

- `REPORT_EMDASH_HEALTH.md`: generated validation, timing, source, and section
  metrics.
- `REPORT_EMDASH_CHECK_CATALOG.md`: generated reviewer-facing map of the
  diagnostic suite.

## Maintenance Rules

- Add every new active report to this index.
- List only genuinely open plans under `Current Plans`; move completed promoted
  plans to decision records without deleting their history.
- Current plans require `Plan-ID`, dependency, supersession, side-task-ledger,
  Infinity Codex provenance, and status fields. `make ci` enforces them.
- Mark reports as current orientation, current plan, completed decision record,
  deferred plan, audit, or generated report.
- Keep normal-work instructions pointed at active authorities rather than
  ignored historical material.
