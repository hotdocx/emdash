# EMDASH v3.2 Observational Equality, Truncation, And Univalence Redesign Plan

Date: 2026-07-13
Last reviewed: 2026-07-14
Plan-ID: EMDASH-V3-2-OBSERVATIONAL-EQUALITY-TRUNCATION-UNIVALENCE-REDESIGN-2026-07-13
Depends-On: EMDASH-V3-2-GROUPOID-COMPUTATIONAL-UNIVALENCE-2026-06-23; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26
Supersedes: no whole report yet; proposes the successor architecture for the active groupoid/computational-univalence track after review and staged approval
Side-Task-Ledger: #side-task-ledger
Implementation-Handoff: #implementation-handoff-start-here
Current-Implementation-Slice: none started; default next slice is OETU-ELEMENTARY-HOTT / Candidate G
Infinity-Codex-Origin: current-session-analysis-2026-07-13
Infinity-Codex-Decision-Responses: current-session-user-direction-2026-07-13-and-2026-07-14; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f5d7c-3fd0-7932-a38e-48985ba4bda0; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f618e-041a-77d2-ad93-31d04d584fa2; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f61d1-7ce1-7272-8082-bf22c8ba6047; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f625c-22a9-7350-8aea-3f06d4784bec; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f6282-d8ef-79f3-8735-aad1435e0b05; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f6293-83c1-70a0-817b-9128a37151c0; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f62b3-d3c8-7b12-9b33-a10d1d0950fe; infinity-codex:019f5d75-e60e-7e50-8ebc-b3586081b672:019f62e3-db49-7653-8b49-ca98cd9015a7
Status: handoff-ready revised proposed integrated redesign; the review and append-only feasibility pass is complete, Candidate G is the default first implementation slice, and the architecture and implementation MVP gates are distinct; no redesign kernel migration has yet started or been promoted, so the current implementation remains the active draft until individual slices are owner-position probed, diagnosed, and accepted

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
- structural reflexivity, action/substitution, and dependent elimination have
  coherent owners, with shaped `eq_refl` and shaped/reflexive `J` promoted as
  soon as safe owner-position designs exist rather than being deferred by old
  experiments;
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
  typed `unif_rule`s provide only proof-time comparison and never masquerade
  as runtime or semantic ownership.

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
| H1 ordinary HoTT compatibility | incomplete/hybrid | Complete Pi equivalence packaging, arbitrary Sigma/record round trips, `TypeEquiv` algebra, univalence round trips, and selected action beta. |
| H2/HIT layer | deferred | Begin only after the observational equality and restricted higher-elimination owners are credible. |
| Omega0/category analogue | broad active first draft plus append-only fixed-map/indexed feasibility | Promote fixed-map omega-equivalence, decoder coherence, one next-hom univalence/action witness, and later discreteness/`OneCat`. |
| Indexed adjunction migration | separate append-only feasibility track; active owner unchanged | Run the owner-position 153-occurrence migration with triangle, opposite, mate, and named-operation controls. |
| Universe/metatheory | deliberately deferred | No concrete implementation slice should claim consistency, stratified closure, or a model merely from Lambdapi acceptance. |

The present feasibility assessment is positive but bounded:

1. No concrete Lambdapi expressibility blocker has been found for the proposed
   record convention, truncation-property kernel, elementary H0 classifiers,
   conservative/shaped record paths, standard Pi beta/eta surface, fixed-map
   omega-equivalence telescope, or indexed adjunction telescope.
2. All seven OETU probes listed below pass warning-enabled checking as of
   2026-07-14. They are append-only extensions after importing the active
   kernel, so they establish plausibility only, not final owner placement,
   subject-reduction behavior in source order, or global coherence.
3. The best/original goal therefore remains credible as a staged
   implementation and research program. It is not yet demonstrated as one
   globally normalizing implementation. The largest concrete risks are the
   `Path_cat` owner repair, public shaped-equality migration, Pi equivalence
   packaging, active `OmegaEquiv` normal-form migration, and the broad
   adjunction consumer migration.
4. Deferred `Cat_cat : Cat` consistency, universe stratification, and general
   semantic/metatheoretic justification do not block the concrete MVP, but
   every report and code comment must preserve that boundary.

### Complete OETU probe and evidence inventory

These are the current probe artifacts relevant to this plan. They live under
ignored `tmp/probes/`; they are review evidence, not source authorities and
not durable active diagnostics.

| Probe | What it demonstrates | Promotion boundary that remains |
| --- | --- | --- |
| `tmp/probes/oetu_architecture_feasibility_probe.lp` | One-constructor dependent records, truncation codes/predicate/package, conservative record paths, a stable nondependent shaped-reflexivity head with reflexive `ind_eqr`, strict local path operations, and recursive `IsNCat` formation. | It combines several late append-only experiments. Split the selected slice, place it at each real owner, cover dependent/nested action where claimed, and audit all literal-`eq_refl` consumers. |
| `tmp/probes/oetu_fixed_map_followup.lp` | A transitional `OmegaEquivAlong(F)` bridge into the current opaque `OmegaEquiv`, computing selected-map/inverse observations, recursive higher-cell endpoints, and the semantic homotopy fibre. | Replace or migrate the real owner; do not retain the bridge as the final two-layer architecture or infer property-valuedness. |
| `tmp/probes/oetu_indexed_structure_architecture_probe.lp` | Primary fixed-map evidence plus Sigma packaging, indexed `Adjunction(F,G)`, both exact triangle patterns, transparent versus proof-time functor views, fixed-arrow higher cells, and typed named-unit/counit comparison. | Move candidates to owner positions, minimize/annotate its eight scratch-local replaceable-pattern-variable advisories, and migrate active opposite/mate/decoder consumers. |
| `tmp/probes/oetu_adjunction_named_unit_runtime_probe.lp` | Negative control: runtime unit/counit projection betas erase the stable triangle discriminators, leaving both the projected and raw named-operation spellings stuck as expected. | Preserve stable unit/counit observations or design a different audited triangle owner; clean its two scratch-local LHS advisories before reusing a pattern. |
| `tmp/probes/oetu_hott_elementary_formers.lp` | Decoded Empty, Bool, and Nat classifiers; dependent eliminator facades; Bool and Nat constructor beta. | Promote at the foundations owner with active diagnostics; identity/no-confusion, higher action, canonicity, and categorical universal properties remain separate. |
| `tmp/probes/oetu_hott_pi_adequacy.lp` | Standard diagonal `happly`, `funext` with related-input action, judgmental beta, non-judgmental arbitrary eta boundary, and reflexive propositional-eta basis. | Select stable public owners and construct the actual `IsEquivMap(PiHapply)` evidence rather than citing beta/eta sketches. |
| `tmp/probes/oetu_hott_pi_stable_funext.lp` | Stable `PiHapply`/`PiFunext` heads, related-input action, a two-rigid-head typed proof-time reflexive bridge, and propositional eta via generic `ind_eqr`. | Reprobe at owner position, compare the proof-time bridge with shaped/fibrancy-derived coherence, and package the active equivalence. |

To reproduce any row, run the following command with that row's path:

```bash
EMDASH_LAMBDAPI_WARNINGS=1 EMDASH_TYPECHECK_TIMEOUT=60s \
  scripts/probe.sh tmp/probes/oetu_hott_elementary_formers.lp
```

The complete set was rerun successfully on 2026-07-14; the corresponding log
names end in `20260714-200013` under `logs/probes/`. Imported active warnings
remain visible in those logs. Absence of a probe-local unjoinable critical
pair is not proof of global confluence, and the named-unit negative probe
shows why explicit positive/negative computation checks are also necessary.

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
   appending it. Add focused runtime assertions, typed `eq_refl` checks for
   proof-time comparisons, explicit negative controls, both reduction orders
   where relevant, and warning comparison.
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
- resolution of shaped `eq_refl`, arbitrary structured-path `J`, `Path_cat`,
  fixed-map omega-equivalence, or indexed adjunction.

After Candidate G, Candidates A (record convention) and B (truncation property
kernel) are the default low-risk infrastructure slices; they may be ordered by
the first concrete consumer. Candidate H and the H1 compatibility ledgers can
then make the ordinary HoTT surface complete while Candidate E repairs the
path owner required before public Candidate C registration.

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
  Candidate H: Pi happly/funext equivalence
        + Sigma/record arbitrary path round trips
        + TypeEquiv algebra and univalence decoder/action round trips
        ───────────────────────────────────────────────────────> H1 MVP

Public observational equality and path algebra
  Candidate E: Path_cat owner repair
        ─> Candidate C: public shaped reflexivity/reflexive J
        ─> structural action ─> fibrancy/dependent J ─> former-by-former migration

Omega/category extension
  decoder normalization + record/equality owners
        ─> Candidate D: fixed-map OmegaEquiv + Sigma package
        ─> IsDiscreteCat / IsNCat / OneCat
        ─> one-next-hom Omega0 univalence/action witness

Separate category migration lane
  Candidate F: indexed Adjunction(F,G), stable unit/counit, triangles/opposite/mates

Later higher layer
  truncation reflectors ─> representative HITs ─> optional H2 completion
  stratified universes / Cat_cat:Cat metatheory remain a separate deferred research phase
```

Candidates C, D, E, F, and H remain available immediately as focused design or
owner-position probes. “Immediately available” does not bypass their listed
promotion dependencies, and Candidate F's adjunction witness never substitutes
for H0/H1/Omega0 adequacy.

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
- use `append-only feasibility demonstrated` for the seven current probes;
  never shorten that phrase to `probed`;
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

1. **Full observational equality is the eventual target.** The current hybrid
   of direct Sigma/Pi equality views and a uniform J eliminator is not the
   intended final design.
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
8. **The equality redesign has two cooperating tracks.** A conservative
   classifier-and-observer MVP may be promoted without waiting for arbitrary
   structured-path elimination, while shaped `eq_refl`, structural
   action/substitution, and shaped `J` remain available for immediate design
   and implementation as soon as an owner-position probe meets the promotion
   criteria below.
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
    `OmegaEquivAlong(F)`/`IsOmegaEquivArrow(F)` the fixed-map property and
    defines the ordinary first-class equivalence type as the Sigma package of
    a map with that property.
13. **Adjunction is likewise an indexed relation in the proposed end state.**
    Rather than retain a permanent `AdjunctionAlong(F,G)` facade alongside the
    current `Adjunction(R,L)`, migrate `Adjunction` itself to be indexed by the
    already-named left and right functors. An existential first-class package
    may be derived separately when a consumer truly does not know the functors.
14. **Runtime projections are not delegated to unification rules.** A narrow
    `unif_rule` may relate an opaque compatibility view to an index at proof
    time, but data needed by downstream reduction must either compute by a
    transparent definition/projection beta or remain visible as the stable
    observation selected by its consumer rule.
15. **Indexed adjunctions retain stable unit/counit runtime observations.**
    `F` and `G` are indices, so `left_adj_func`/`right_adj_func` disappear or
    remain transparent migration views. In contrast, `unit_adj_transf(J)` and
    `counit_adj_transf(J)` remain opaque stable heads because the generic
    triangle cut-elimination rules discriminate on them. The exact two
    indexed triangle patterns have been mechanically demonstrated in an
    append-only probe; they use `F` and `G` as consistently repeated
    parameters, never as rewrite heads.
16. **Preselected adjunction operations are connected proof-time by default.**
    A named `myUnit`/`myCounit` may be related to the stable observations of
    `myAdj : Adjunction(myF,myG)` by narrow, typed `unif_rule`s, validated with
    typed `eq_refl`. Runtime betas from those observations to arbitrary raw
    names are rejected by default because they can erase the triangle
    discriminator before the outer cut rule fires. Raw named-operation
    expressions do not thereby acquire triangle computation; a future
    elaborator must preserve/reconstruct the stable spelling, or separately
    generated instance rules require their own critical-pair audit.
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
    inferred from beta/eta sketches alone.
20. **Foundational compatibility is executable and independent of
    adjunction.** Elementary classifier/eliminator beta, Sigma/record path
    round trips, `TypeEquiv` algebra, univalence round trips, and conversion-
    level anti-collapse controls belong to the HoTT gate. Indexed adjunction is
    a separate category-migration witness and cannot substitute for them.

## Current Baseline And Review Findings

At creation of this proposal:

```text
tracked working tree                         clean
EMDASH_TYPECHECK_TIMEOUT=60s make check      pass
active implementation                        emdash3_2.lp
active diagnostics                           emdash3_2_checks.lp
```

The 2026-07-14 handoff revalidation reran the bounded active check and all
seven warning-enabled OETU probes successfully before this report-only edit.
No kernel or active-check migration has been made by the plan. The probe logs
and their append-only limitations are recorded in the handoff inventory and
References; a successor must still rerun the baseline against its own current
worktree.

The existing architecture contains valuable first slices:

- `PathOver`, `eq_apd`, Sigma/Pi path views, and contractible-fibre
  `TypeEquiv`;
- explicit `idtoequiv_grpd`, `idtoiso_cat`, and `idtoequiv_cat` directions;
- explicit reverse decoder heads;
- a recursive `OmegaEquiv` observation interface;
- constructor-specific Product experiments;
- a global categorical-univalence policy stated visibly rather than hidden in
  conversion.

The review nevertheless found four blocking design boundaries.

1. `Path_cat` inherits strict generic category identity rules that do not join
   the current one-sided J definition of `eq_trans`.
2. `Op_cat(Path_cat(A)) -> Path_cat(A)` identifies a self-opposite equivalence
   with definitional equality and erases the endpoint reversal.
3. Sigma/Pi equality has begun reducing observationally, while `eq_refl` and J
   still follow the older uniform-inductive identity architecture.
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
- an opaque compatibility projection plus a narrow `unif_rule` validates a
  typed `eq_refl` proof but intentionally does **not** make the projection
  convertible to the index. This confirms the SOP distinction between
  proof-time comparison and runtime computation;
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
- a concrete preselected unit and counit can be related proof-time to the
  stable observations by narrow `unif_rule`s: typed `eq_refl` succeeds while
  an `assertnot` confirms that runtime conversion intentionally does not;
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
  `PiFunext` heads, related-input action, a typed two-rigid-head proof-time
  reflexive comparison, and propositional eta derived by generic `ind_eqr`.

All three pass warning-enabled checking without a probe-local warning. They are
still late extensions after importing the active owner. Consequently they show
mechanical plausibility, not owner-position/full-file coherence. The elementary
probe does not establish observational identity, no-confusion, higher action,
or canonicity for its inductives. The Pi probe does not yet construct the
active contractible-fibre `IsEquivMap(PiHapply)` package, and its proof-time
comparison remains a candidate to compare with shaped-reflexivity or fibrancy-
derived coherence before promotion.

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

The base `IsDiscreteCat` is a real prerequisite. It should express that `C`
has no directed information beyond the equality/groupoidal structure of a
set of objects. A likely semantic formulation is:

```text
IsSetGrpd(Obj(C))
and IsOmegaEquivFunctor(Core_incl_func(C)).
```

Here `IsOmegaEquivFunctor(F)` means equivalence structure on the **already
selected** functor `F`. The selected architecture makes that fixed-map notion
primary rather than recovering it as the fibre of an opaque package
projection.

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

`OmegaEquivAlong_C(f)`, also provisionally named
`IsOmegaEquivArrow_C(f)`, stores or exposes the selected inverse arrows and the
recursively required hom-equivalence/coherence data while `f` is an index. Its
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
characterization; it is not licensed by the name `IsOmegaEquivArrow`. Until
then, paths of `IsDiscreteCat`/`NCat` packages still contain an evidence-field
obligation.

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
equivalent computational design. The probe verifies that such a rule can make
an `eq_refl`-typed comparison elaborate while `left_adj_func(J) ≡ F` still
fails conversion. It is therefore suitable only as a narrow proof-time
migration convenience, never as the runtime authority required by functor
application, triangle normalization, or mate computation.

The unit and counit have a different role from the left/right functor views.
They must remain stable runtime observations:

```text
unit_adj_transf(J)
counit_adj_transf(J).
```

Suppose a concrete declaration already has named operations:

```text
myF       : Functor(R,L)
myG       : Functor(L,R)
myUnit    : id_R => myG o myF
myCounit  : myF o myG => id_L
myAdj     : Adjunction(myF,myG).
```

The selected manual declaration bridge is proof-time:

```text
unif_rule unit_adj_transf(myAdj)   ≡ myUnit   ↪ [ ... ]
unif_rule counit_adj_transf(myAdj) ≡ myCounit ↪ [ ... ].
```

Each rule must be narrowly typed and validated with a typed reflexive path,
schematically:

```text
my_unit_agreement
  : unit_adj_transf(myAdj) = myUnit
  := eq_refl(myUnit).
```

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
proof-time operation comparisons, and their typed/negative diagnostics. A
surface elaborator may also print a user's operation names while elaborating
computational triangle terms to the stable observation spellings. It should
not make per-instance unification rules the sole meaning of a declaration or
generate instance-specific triangle rewrites by default; any such rewrite
generation is a separate critical-pair-audited design.

Consequently, `IsDiscreteCat` must be designed before `IsNCat` is promoted,
and the blocker is specifically fixed-functor omega-equivalence
infrastructure—not an unspecified need for every possible notion of category
equivalence.

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

should eventually be replaced or quarantined by a dimension-correct
interface:

```text
onecat_iso_univalence
  : Pi C : OneCat,
      CatIsoUnivalence(onecat_carrier(C)).
```

The preferred final result is to derive this from:

- global `CatUnivalence` into `OmegaEquiv`;
- the discreteness/truncation of all hom-categories of a `OneCat`;
- a comparison between `OmegaEquiv` and `IsoEvidence` at that level.

A scoped operational axiom is acceptable before the derivation, but the
unscoped global `CatIsoUnivalence` claim should remain labelled temporary.

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

### `J`, shaped reflexivity, and structural action

The active `ind_eqr`/`ind_eq` interface remains a useful compatibility and
semantic reference. A full observational implementation cannot, however,
depend solely on one beta rule that recognizes only the literal `eq_refl`
head. The redesign therefore separates four achievements that were previously
too easily conflated:

1. a conservative classifier MVP: equality exposes a record/Sigma/Pi path
   view; projections of literal reflexivity compute; generic `J` computes on
   literal reflexivity;
2. shaped reflexivity and reflexive shaped `J`: a supported former selects a
   stable reflexivity head whose path projections compute structurally, and
   `ind_eqr` recognizes that head at the reflexive endpoint;
3. structural action: registered open maps and dependent sections act on
   non-reflexive structured paths through explicit `ObsAction`/`ObsSubst`-like
   data;
4. arbitrary structured-path dependent elimination: registered classifiers
   and motives expose the fibrancy/elimination capability from which sound
   structured `J` is obtained.

The conservative MVP does not require (3) or (4), but (2)--(4) are **not
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

Achievements (3) and (4) are stronger. An arbitrary path-record value cannot
soundly be eliminated by returning the reflexive branch for an arbitrary
motive. Nor can an arbitrary Lambdapi function silently acquire structural
path action merely because an `ObsSubst` symbol has been declared. The design
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

Until that capability is selected, generic `ind_eqr` remains the opaque
compatibility eliminator and only explicitly registered formers may claim
computational arbitrary structured-path `J`.

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

## One Operational Inverse Per Univalence Layer

The decoder-oriented interfaces are selected as the eventual operational
owners:

```text
grpd_equiv_path
iso_evidence_path       // OneCat-scoped in the final design
omega_equiv_path.
```

This owner selection belongs near the beginning of the migration, before
constructor-specific univalence closure and before paths of packaged truncated
universes are claimed. Otherwise new code will continue to accumulate against
two unrelated inverse choices.

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
terms have inverse-like types, and experimental unification rules are not a
substitute for the missing path. The interface must either store/expose that
agreement, restrict to the canonical capability, or label the comparison as an
axiom/theorem prerequisite.

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
adequate public coherence API.

## `Path_cat` Repair Is A Prerequisite

The path-category redesign must precede `IsDiscreteCat`, `IsNCat`, `OneCat`,
and any **public** shaped-reflexivity slice that registers with path
composition or symmetry. Shaped owner-position research probes may run earlier,
but promoted rules must not register against an owner that a later phase plans
to replace.

Required decisions:

1. remove the runtime collapse `Op_cat(Path_cat(A)) -> Path_cat(A)`;
2. represent self-oppositeness by a functor/equivalence whose arrow action is
   path symmetry;
3. select a path-composition owner whose interaction with both strict category
   units is measured;
4. make `Path_cat` a strict category by the computation required by its
   declared type `Path_cat(A) : Cat`; if the weak route is selected instead,
   reclassify it outside the current strict `Cat` interface rather than leaving
   weak laws inside a supposedly strict category;
5. test associativity and both unit diamonds at arbitrary paths;
6. reconnect `Core_incl_func` and `path_to_hom` only after the selected path
   composition normal form is stable.

Do not add a second specialized `Core_incl_func` composition owner merely to
hide a failure in `Path_cat` itself.

The feasibility probe shows that a fresh strict composition/symmetry interface
with explicit endpoint guards can satisfy its local equations. It does not yet
show that replacing the active `eq_trans`/`eq_sym` owners preserves every
consumer. The repair slice therefore remains a migration audit, not merely the
addition of the fresh probe heads.

The preferred MVP orientation is:

```text
Path_cat composition uses one strict path-composition owner;
Path_cat opposite action uses one strict path-symmetry owner;
the active J-derived eq_trans/eq_sym remain semantic HoTT references;
strict-versus-J-derived agreement begins propositionally.
```

Later evidence may justify making the strict owner the general public HoTT
operation or redesigning `eq_trans` itself. Until that comparison exists, the
two operations must be named distinctly and no report may treat their
agreement as definitional. `Core_incl_func`, transport/`ap`, and the symmetry
opposite functor are the first consumers of the agreement boundary.

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
- an experimental `unif_rule` may support proof-time comparison but never
  substitutes for required conversion or projection computation; in
  particular, it does not make a triangle written only with raw named
  unit/counit terms compute;
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
two-rigid-head proof-time comparison and then derives arbitrary eta by generic
`ind_eqr`; that is a credible candidate, not yet the selected permanent owner.
Promotion requires an owner-position warning/reduction-order audit and a
comparison with any coherence supplied by shaped reflexivity or fibrancy.

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
- strict path-category composition/opposite coherence;
- `IsObjTruncCat`, `IsDiscreteCat`, recursive `IsNCat`, and packaged `OneCat`;
- the corresponding structure one hom level higher: an object-level example
  is repeated for a hom-category or transfor hom-action so that a capped point
  rule cannot accidentally erase the data needed by omega iteration.

The prose inventory is tracked by the following status-bearing correspondence
table rather than by assuming that every groupoidal notion is literally a
directed construction:

| Type/groupoid notion | Category/omega counterpart | Kind of correspondence | Initial status and iteration boundary |
| --- | --- | --- | --- |
| identity/path | `Path_cat`, `Core_cat`, `Core_incl_func` | groupoidal lift into directed structure | active first draft; strict path algebra/opposite repair is a prerequisite |
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
| Standard `PiHapply`/`PiFunext` compatibility | prerequisite | Runtime diagonal beta, related-input action, typed reflexive proof-time coherence, and propositional eta are append-only feasibility evidence; owner-position ownership remains open. |
| `IsEquivMap(PiHapply)` and Pi `TypeEquiv` package | prerequisite | The beta/eta skeleton gives quasi-inverse data but has not been converted to the active contractible-fibre equivalence definition. |
| Arbitrary Sigma/record path-characterization round trips | prerequisite | Current diagnostics cover projections and reflexive encode/decode cases, not both arbitrary round trips. |
| Record identity classifier and reflexivity observers | prerequisite | Nondependent and dependent conservative skeletons pass in an append-only import probe; intended placement and later-consumer audit remain. |
| Stable shaped record reflexivity and reflexive shaped `J` | prerequisite | The nondependent stable-head skeleton and simulated consumer registrations pass append-only with no local warning; a true owner-position/full-file-copy probe remains. |
| Dependent/nested shaped reflexivity, structural action, and arbitrary dependent `J` | prerequisite | Immediate probe tracks, but public promotion follows path-owner selection; action and fibrancy must not be inferred from the nondependent reflexive probe. |
| Contractibility, fibres, `IsEquivMap`, `TypeEquiv` | active | Contractible-fibre presentation and selected map/inverse observations are active. |
| `TypeEquiv`/`IsEquivMap` identity, symmetry, and composition compatibility | prerequisite | Reflexive evidence and selected constructor closure are active; a complete ordinary algebra and executable compatibility corpus are not. |
| Groupoid univalence and operational reverse decoder | active | First-draft capabilities exist; decoder agreement and action coherence remain an early normalization phase. |
| Both groupoid-univalence round trips and selected action coherence | prerequisite | Require named `idtoequiv(ua(e))`, `ua(idtoequiv(p))`, `coe(ua(e),a)`, and one nontrivial Pi or Sigma action diagnostic. |
| Truncation properties and low-level aliases | prerequisite | `TruncLevel`/`IsTruncGrpd` skeleton has append-only feasibility evidence; intended placement and active promotion remain. |
| Packaged `PropU_grpd`/`SetU_grpd`/`GroupoidU_grpd` | prerequisite | Carrier/evidence record skeleton has append-only feasibility evidence; property paths, closure, universe-level truncation, and owner-position audit remain open. |
| Truncation reflectors | deferred | Require the higher-constructor/restricted-elimination architecture. |
| `Cat`, functors, transfors, iterated hom actions | active | Broad generic infrastructure exists and remains the owner of ordinary functoriality/naturality. |
| Strict coherent `Path_cat` and opposite action | prerequisite | Current first draft has unit/self-opposite coherence defects; a fresh strict local algebra is only probe evidence. |
| First-class `OmegaEquiv` observations | active | Recursive observation/reflexivity interface exists; unrestricted introduction/corecursion is absent. |
| Primary fixed-map `OmegaEquivAlong(F)` plus Sigma package | prerequisite | The transitional bridge, primary-property/Sigma package, and exact fixed-arrow inverse/higher-cell telescope have append-only feasibility evidence; active-owner migration, property-valuedness, and owner-position audit remain. |
| Indexed `Adjunction(F,G)` | prerequisite | Indexed formation, both exact triangle rules, direct `F`/`G` conversion, typed proof-time agreement with named unit/counit, and the negative runtime-erasure control pass append-only. Active opposite/mate migration and owner-position warning/LHS audits remain. |
| `IsObjTruncCat` | prerequisite | Formation is mechanically small once `IsTruncGrpd` exists, but current evidence is append-only. |
| `IsDiscreteCat` | prerequisite | Needs repaired `Path_cat` and fixed-map omega-equivalence of `Core_incl_func`. |
| Recursive `IsNCat` | prerequisite | Recursion skeleton passes append-only with an opaque stand-in for the discrete base; the real base and owner-position evidence remain. |
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
| fibrancy/dependent J | Which motives admit arbitrary structured-path elimination, and does that eliminator have sound betas? |
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
4. Preserve the passing active baseline.
5. Unless the user selects another bounded task, begin implementation with
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

1. Select a fresh strict path-composition/symmetry owner for the MVP and state
   its propositional comparison boundary with J-derived `eq_trans`/`eq_sym`.
2. Remove/probe removal of definitional self-oppositeness.
3. Introduce/probe the path-symmetry opposite functor/equivalence.
4. Settle strict unit/associativity ownership required by `Path_cat : Cat`.
5. Add both-order diagnostic diamonds.
6. Revalidate `Core_incl_func`, `path_to_hom`, transport/`ap`, `DefIso`,
   opposite, and Product consumers.

This phase controls the composition and symmetry owners used by later public
shaped-reflexivity registration. It does not prevent earlier isolated shaped
research probes.

### Phase 5: Equality MVP And Immediate Shaped Fast Track

This phase has two cooperating lanes. Either may produce the first useful
equality slice; neither lane may misstate what it has implemented.

Conservative lane:

1. retain direct record/Sigma/Pi equality classifiers and projection observers
   where both reduction orders join;
2. keep generic `J` computation on literal `eq_refl`;
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

### Phase 6: Univalence Decoder Interface Normalization

1. Select the reverse decoder owner at the groupoid and categorical layers.
2. Connect capability-selected inverses by named coherence data or restrict to
   the canonical capability.
3. Expose both round trips and the path-to-arrow/transport squares.
4. Keep constructor closure propositional until the generic squares are
   stable.
5. Do not use arbitrary-capability `unif_rule`s as a replacement for missing
   coherence.

### Phase 7: Primary Fixed-Map Omega-Equivalence And Sigma Package

1. Introduce/refine `OmegaEquivAlong_C(f)`/`IsOmegaEquivArrow_C(f)` as the
   primary fixed-arrow evidence layer.
2. Migrate `OmegaEquiv_C(x,y)` from the current opaque observation classifier
   to the Sigma package `Sigma f, OmegaEquivAlong_C(f)` in an owner-position
   full-file probe.
3. Route inverse and higher-cell observations through the packaged evidence;
   install map/inverse projection betas before dependent higher-cell betas,
   and keep cancellation represented by recursive higher equivalence cells
   rather than raw composition-to-identity rewrites.
4. Migrate reflexive, opposite, and Product generators without duplicating
   semantic bodies.
5. Revalidate categorical univalence decoder domains/codomains, round trips,
   and the Product diamonds.
6. Compare the primary evidence propositionally with the old semantic
   `OmegaEquivFibre(F)` during compatibility staging.
7. Validate one concrete named equivalence declaration and the first MVP
   end-to-end univalence/action witness without a per-instance unification rule.

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
   proof-time comparisons to the stable observations, validate them with typed
   `eq_refl`, and retain `assertnot` conversion controls. Do not install
   ordinary observation-to-raw-operation runtime betas.
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
2. Select and implement `IsDiscreteCat` from object-set truncation and
   `OmegaEquivAlong(Core_incl_func(C))`.
3. Add `CatDim`, recursive `IsNCat`, `NCat(n)`, `ZeroCat`, and `OneCat`.
4. State and prove or stage `IsNCat(n,C) -> IsObjTruncCat(n,C)` with its exact
   univalence/evidence-truncation dependencies.
5. Scope ordinary `CatIsoUnivalence` to `OneCat` and prove or defer the
   `OmegaEquiv`/`IsoEvidence` comparison there.

### Phase 10: Public Equality, Structural Action, And Fibrancy Migration

1. Migrate one type former at a time from the prototype to public equality.
2. Replace old encode/decode implementations that became identity coercions.
3. Retain compatibility aliases only when they have real consumers.
4. Eliminate the two-reflexivity-normal-form Product boundary.
5. Promote structural action only through the selected registered-map
   architecture.
6. Promote arbitrary structured-path `J` only through the selected
   fibrancy/dependent-elimination capability; do not identify it with either
   action alone or the already feasible reflexive shaped beta rule.
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
   bridge at owner position and against shaped/fibrancy-derived coherence.
4. Add both arbitrary Sigma and dependent-record path-characterization round
   trips with their reflexive computation laws.
5. Derive `TypeEquiv` and `IsEquivMap` identity/symmetry/composition, stabilize
   both groupoid-univalence round trips and selected action beta, and only then
   add further constructor closure.
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

### Phase 13: Deferred Universe Metatheory

Compare:

- the current unstratified operational specification;
- a stratified type/category universe hierarchy;
- a deliberate impredicative/self-universe model.

This phase owns consistency/model claims. No earlier implementation phase
depends on resolving it.

## Immediately Feasible Candidate Slices

The following are intentionally small enough for later refinement into the
next concrete task.

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
Candidate E's path-owner decision.

### Candidate D: primary fixed-map omega-equivalence and Sigma package

```text
OmegaEquivFibre(F) as semantic reference;
OmegaEquivAlong(F) as primary evidence;
OmegaEquiv(x,y) := Sigma F, OmegaEquivAlong(F);
generic omega_equiv_to/evidence projection beta;
transitional bridge to the old opaque owner only as needed;
one concrete named equivalence declaration;
no unif-only runtime semantics.
```

Risk: medium to high as an active normal-form migration. The append-only
fixed-map telescope, transitional bridge, primary Sigma package, and computing forward
projection and higher-cell endpoints all pass warning-enabled probes without
a local unjoinable critical-pair report. Scratch-LHS cleanup remains part of
promotion. The principal risk lies in migrating active recursive observations,
generators, and univalence decoders, not in basic Lambdapi expressibility.

### Candidate E: `Path_cat` focused repair

```text
remove self-opposite collapse in an owner-position/full-file-copy probe;
classify warning delta and downstream type failures;
probe symmetry functor;
test both path-category units.
```

Risk: medium to high. This is a prerequisite for `OneCat` and for public
shaped-reflexivity registration with path composition/symmetry.

### Candidate F: indexed adjunction migration spike

```text
Adjunction(F,G) indexed relation;
left/right projections removed or transparent only;
stable unit/counit observations typed directly over F/G;
both exact triangle rules with F/G as parameters;
named unit/counit proof-time bridge with typed and assertnot controls;
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
runtime design; narrow unit/counit unification is declaration assistance only,
while the stable observations remain the computational owners.

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
propositional funext(happly(p)) eta by generic J;
owner-position comparison of proof-time versus shaped/fibrant coherence;
IsEquivMap(PiHapply) and TypeEquiv packaging;
no global eta rewrite.
```

Risk: medium. Both transparent and stable append-only probes pass, including a
typed two-rigid-head reflexive comparison and arbitrary propositional eta. The
permanent owner and contractible-fibre equivalence proof remain open, so this
candidate is immediately feasible for an owner-position design probe but is
not yet a formally `probed` matrix row.

Candidate G is the default first implementation slice for a new handoff;
Candidates A and B are the next safest promotion candidates and may be ordered
by their first concrete consumer. Candidates C, D, E, F, and H are all
immediately available as design/owner-position probes. Candidate C may become
a narrow public equality slice only after E and its other promotion gates
pass. Candidate D may migrate before the directed-dimension layer. Candidate
E remains the prerequisite for `IsDiscreteCat`, `OneCat`, and public shaped
path-operation registration. Candidate F is independent of directed dimension
but must not be mixed with an unrelated module split. Candidate H may proceed
without discarding the related-input Pi identity, but H1 cannot pass until its
equivalence packaging is active.

## Explicitly Deferred Work

Shaped `eq_refl`, structural action/substitution, reflexive shaped `J`, and a
sound arbitrary structured-path `J` are intentionally **not** blanket entries
in this deferred list. They are immediate tracks. A particular attempted
encoding may fail or an unresolved subpart may remain a prerequisite for a
later slice, but earlier reports do not defer the subject itself.

Elementary H0 formers, standard Pi/function extensionality, Sigma/record path
round trips, and ordinary equivalence/univalence compatibility are likewise
immediate prerequisite or implementation tracks, not blanket deferrals.

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
- a typed `eq_refl`, not a conversion assertion, exercises any retained
  proof-time reflexive Pi coherence;
- `PiFunext(PiHapply(p)) = p` is constructed propositionally by generic `J`,
  with its reflexive computation checked;
- `PiHapply` is packaged with active contractible-fibre `IsEquivMap` evidence,
  or a reviewed generic quasi-inverse-to-`IsEquivMap` theorem supplies it;
- owner-first and application/eta-first reductions, warning deltas, and the
  comparison with shaped/fibrancy-derived coherence are checked before
  promotion.

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

- both identity units at an arbitrary path;
- both associativity reduction orders;
- opposite hom endpoints remain reversed;
- the symmetry functor maps identity and composition correctly;
- strict path composition/symmetry agree propositionally with the J-derived
  reference operations at the selected boundary;
- `Core_incl_func` retains generic functorial ownership.

### Univalence diagnostics

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
- no semantic dependency on an untyped or unvalidated per-instance
  `unif_rule`.

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
- typed `eq_refl` validates every intentionally retained proof-time
  `unif_rule`, including one concrete preselected named unit/counit pair;
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
- the elementary classifier/eliminator beta corpus, Pi equivalence package,
  Sigma/record arbitrary path round trips, `TypeEquiv` algebra, and both
  univalence round trips pass at the tier that claims them;
- equality, transport, equivalence, univalence, and truncation examples compose
  rather than merely typecheck independently;
- literal-reflexivity `J`, reflexive shaped `J`, structural action, and
  arbitrary fibrant/dependent structured-path `J` are tested and reported
  separately;
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

An action head for registered maps does not by itself justify eliminating an
arbitrary structured path into an arbitrary dependent motive. Treating the two
as one capability would hide the central fibrancy obligation. The action and
dependent-elimination interfaces therefore have separate ledger entries,
diagnostics, and promotion claims.

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
narrow two-rigid-head bridge against shaped-reflexivity and fibrancy-derived
alternatives before selecting it.

### `IsDiscreteCat` may expose missing category-equivalence infrastructure

Do not weaken discreteness to object-set truncation merely to make `OneCat`
easy to declare. The concrete prerequisite is a fixed-functor
`OmegaEquivAlong(Core_incl_func(C))` property integrated with the recursive
Sigma-packaged `OmegaEquiv`; record it rather than postulating an opaque generic
category-equivalence property.

### Migrating `OmegaEquiv` changes a public normal form

The primary-property/Sigma-package architecture is mechanically simple, but
the active `OmegaEquiv` classifier is opaque and already owns reflexive,
opposite, Product, and univalence observations. Replacing it is a kernel
normal-form migration. The forward/evidence projection benefit does not waive
the constructor, decoder, subject-reduction, downstream, and warning audits.

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

### Declaration convenience can accidentally become semantic authority

A generated or handwritten per-instance `unif_rule` is attractive for relating
an opaque observation to an already-named map or operation. The focused probes
show the exact boundary: a typed `eq_refl` comparison can succeed while the
terms remain non-convertible. Lambdapi unification rules are experimental and
proof-time only. Fixed-arrow indices, transparent functor views, stable
unit/counit runtime observations, and Sigma projection betas remain the
semantic architecture. The convenience rule may improve declarations and
typed statements, but cannot be cited as the reason a raw named-unit triangle
computes.

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

## Side-Task Ledger

| ID | Status | Depends on | Resume trigger | Next action |
| --- | --- | --- | --- | --- |
| `OETU-RECORD-CONVENTION` | proposed early slice; append-only skeleton demonstrated | current inductive/Sigma infrastructure | first concrete slice selected | Refine the passing dependent one-constructor record at owner position, including projections, generated eliminator, parameter syntax, and inferred-slot audit; compare with nested Sigma. |
| `OETU-RECORD-GENERATOR` | deferred/optional | `OETU-RECORD-CONVENTION` | two manual records show repeated stable boilerplate | Specify a deterministic external schema generator; generated code remains reviewable Lambdapi source. |
| `OETU-ELEMENTARY-HOTT` | **default next slice; not started**; append-only feasibility demonstrated | active universe decoding and native inductives | next implementation turn unless the user selects another bounded slice | Promote decoded Empty, Bool, and Nat classifiers/eliminators with beta and Bool non-collapse diagnostics at their active owners; keep sums, observational identity/no-confusion/higher action, canonicity, and categorical universal properties as separately statused work. |
| `OETU-PI-FUNEXT` | immediate owner-position design track; append-only beta/eta skeleton demonstrated | active `PiPathView`, generic `ind_eqr`, contractible-fibre `IsEquivMap` | H1 or truncation-evidence property-valuedness is consumed | Select `PiHapply`/`PiFunext` owners, preserve related-input action, audit the reflexive proof-time boundary, derive propositional eta, and package `PiHapply` as an active equivalence. |
| `OETU-STRUCTURAL-PATH-COMPAT` | proposed H1 compatibility slice | active Sigma paths, `OETU-RECORD-CONVENTION`, `OETU-PI-FUNEXT` where path-valued functions require it | H1 path characterization is claimed | Add arbitrary Sigma and dependent-record encode/decode round trips, reflexive betas, and one nested path-telescope case without forcing global runtime eta. |
| `OETU-TYPE-EQUIV-ALGEBRA` | proposed H1 compatibility slice | active `IsEquivMap`/`TypeEquiv`, `OETU-PI-FUNEXT`, `OETU-UNIV-DECODER` for round trips | foundational HoTT MVP is selected | Add identity/symmetry/composition, the required contractible-fibre closure proofs, both groupoid-univalence round trips, selected transport beta, and one Pi/Sigma universe-action example. |
| `OETU-TRUNC-LEVEL` | proposed early slice; append-only skeleton demonstrated | existing `IsContr`, `Pi_grpd`, equality | truncation slice selected | Promote/refine `TruncLevel`, recursive `IsTruncGrpd`, and named low-level aliases with owner-position diagnostics. |
| `OETU-TRUNC-CLOSURE` | proposed staged ledger | `OETU-TRUNC-LEVEL`, equality/equivalence | a closure fact receives a concrete consumer | Prove one fact at a time: equality lowering, monotonicity, equivalence invariance, Pi/Sigma bounds, and package-universe truncation. |
| `OETU-TRUNC-EVIDENCE-PROP` | deferred proof | `OETU-TRUNC-LEVEL`, `OETU-PI-FUNEXT`, stable observational paths | packaged-universe equality is consumed | Derive `IsPropGrpd(IsTruncGrpd(n,A))`; do not postulate global proof irrelevance. Add ambient univalence before claiming the `(n+1)` universe theorem. |
| `OETU-TRUNC-UNIVERSE` | proposed follow-up; append-only skeleton demonstrated | `OETU-RECORD-CONVENTION`, `OETU-TRUNC-LEVEL` | low-level predicates pass | Add `TruncGrpdU`, low-level aliases, carrier/evidence projections, and an explicit no-false-universe-truncation diagnostic at owner position. |
| `OETU-TRUNC-REFLECTOR` | deferred | observational equality and HIT elimination | a theorem needs `||A||_n`, not merely `IsTruncGrpd(n,A)` | Design propositional truncation first with restricted dependent elimination. |
| `OETU-PATH-CAT` | proposed prerequisite repair; append-only strict local algebra demonstrated | current J-derived path algebra | public shaped registration, `OneCat`, or observational category equality begins | Select strict path owners, state propositional agreement with `eq_trans`/`eq_sym`, run the owner-position/full-file-copy self-opposite audit, and add the symmetry functor/equivalence. |
| `OETU-OMEGA-EQUIV-ALONG` | proposed normal-form migration; append-only primary-property/package, higher-cell, and bridge feasibility demonstrated | recursive `OmegaEquiv`, Sigma/record convention, univalence decoder | fixed-functor equivalence or discreteness is consumed | Migrate at owner position to primary fixed-arrow evidence plus Sigma-packaged `OmegaEquiv`; route generators/destructors and compare with the old semantic fibre without adding raw cancellation rewrites. |
| `OETU-ADJUNCTION-INDEXED` | proposed focused migration; append-only indices, triangles, and named-operation boundary demonstrated | current adjunction triangles/opposite/mates | indexed-structure slice selected | Replace `Adjunction(R,L)` by `Adjunction(F,G)` at owner position; remove/transparentize left/right views, retain stable unit/counit observations, and migrate the 153-occurrence source/check/example surface with the runtime-erasure negative control. |
| `OETU-STRUCTURE-DECLARATION` | proposed usability protocol; one append-only adjunction operation bridge demonstrated | primary fixed-map evidence; indexed adjunction | a second concrete named structure instance is needed | Validate direct `u : OmegaEquivAlong(F)` and `J : Adjunction(F,G)` declarations; connect preselected unit/counit names only by typed proof-time comparisons while canonical computations retain stable observations; consider an elaborator/generator afterward. |
| `OETU-DISCRETE-CAT` | blocked by explicit prerequisites | `OETU-PATH-CAT`, `OETU-OMEGA-EQUIV-ALONG` | directed dimension slice begins | Define object-set truncation plus `OmegaEquivAlong(Core_incl_func(C))`; do not substitute object truncation alone. |
| `OETU-NCAT` | proposed architecture, implementation deferred | `OETU-DISCRETE-CAT`, `OETU-TRUNC-LEVEL`, record convention | `IsDiscreteCat` is stable | Add `CatDim`, recursive `IsNCat`, and packaged `NCat`. |
| `OETU-NCAT-OBJ-TRUNC` | theorem prerequisite | `OETU-NCAT`, categorical univalence, fixed-arrow evidence truncation | `OneCat` object truncation or iso comparison is consumed | Prove/stage `IsNCat(n,C) -> IsObjTruncCat(n,C)`; state explicitly that the converse fails. |
| `OETU-ONECAT-ISO` | proposed replacement | `OETU-NCAT`, global Cat univalence | `OneCat` exists | Scope/derive `CatIsoUnivalence` for `OneCat`; retire the unscoped claim. |
| `OETU-OBS-MVP` | proposed conservative lane; append-only skeleton demonstrated | record convention and current equality views | a low-risk equality former is selected | Refine the direct classifier, literal-reflexivity observers, and generic `J` control case at owner position without claiming arbitrary structured action. |
| `OETU-OBS-SHAPED-REFL` | immediate probe candidate; append-only nondependent skeleton demonstrated | `OETU-OBS-MVP` classifier shape, consumer inventory; public promotion also depends on `OETU-PATH-CAT` | shaped lane selected | Extend the stable shaped head to a dependent record and nested former; register every generic literal-reflexivity consumer at owner position after path-owner selection. |
| `OETU-OBS-ACTION` | immediate design/probe track | path telescopes, `PathOver`, shaped registry | a registered open term must act on a structured path | Select/probe `ObsAction`/`ObsDAction` or `ObsSubst`; account for open terms, dependent fields, composites, and next-dimensional data. |
| `OETU-OBS-FIBRANCY` | immediate design/probe track | `OETU-OBS-ACTION`, dependent motives, registered formers | arbitrary structured-path elimination is consumed | Specify which classifiers/motives carry fibrancy and derive a sound dependent eliminator; do not infer this capability from action alone. |
| `OETU-OBS-SHAPED-J` | split status: reflexive candidate immediate; arbitrary depends on fibrancy | `OETU-OBS-SHAPED-REFL`; for arbitrary paths `OETU-OBS-FIBRANCY` | shaped equality slice selected | Promote specialized reflexive `ind_eqr` when it passes; derive arbitrary structured-path `J` only from a sound dependent-elimination architecture. |
| `OETU-OBS-MIGRATE` | deferred high-risk public migration | successful shaped/MVP probe and consumer audit | one former has canonical joins | Migrate public equality one former at a time; do not combine with reorganization. |
| `OETU-FOUNDATIONAL-ADEQUACY` | active tiered architecture/implementation gate | all relevant rows above | every slice refinement and milestone | Maintain H0/H1/H2/Omega0 status/owner/computation cells; require active H0 for an implementation skeleton, active H1 plus an integrated fixed-map univalence/action witness for a foundational HoTT MVP, and keep indexed adjunction as a separate migration witness. |
| `OETU-UNIV-DECODER` | proposed early coherence repair | current equality and univalence interfaces | round trips, truncated-universe paths, or constructor univalence are consumed | Select decoder heads, add named capability agreement and coherence squares before further closure rules. |
| `OETU-PRODUCT-DIAMOND` | proposed focused cleanup | stable equality/reflexivity policy | Product decoder migration begins | Probe preserving Product evidence provenance by removing reflexive collapse. |
| `OETU-CAT-GLOBAL` | accepted operational policy | none | any report/kernel text suggests non-univalent `Cat` semantics | Keep every `C : Cat` globally univalent and label the policy axiomatic/unstratified. |
| `OETU-CAT-SELF` | deferred metatheory | `OETU-CAT-GLOBAL` | model or universe computation is claimed | Compare stratified, impredicative, and operational self-universe readings. |
| `OETU-METATHEORY` | deferred research | mature observational kernel | consistency/canonicity claim is needed | Develop normalization/model evidence; Lambdapi typechecking alone is not sufficient. |

## Acceptance Criteria For Refining This Proposal

Before this report becomes the active replacement plan:

1. agree on kernel names for `TruncLevel`, `IsTruncGrpd`, truncated universes,
   `CatDim`, and `IsNCat`;
2. agree on the definition boundary for `IsDiscreteCat`;
3. agree that the one-constructor inductive record convention is the default
   for finite named structures;
4. approve the primary `OmegaEquivAlong(F)` property plus Sigma-packaged
   `OmegaEquiv` boundary and the transitional-only role of the old semantic
   fibre/bridge;
5. approve the indexed `Adjunction(F,G)` replacement, absent/transparent
   left/right compatibility policy, stable unit/counit runtime observations,
   and optional existential `AdjunctionPackage` boundary;
6. approve the limited proof-time role of declaration-generated `unif_rule`s,
   including the explicit fact that raw preselected unit/counit spellings do
   not inherit generic triangle computation and runtime projection betas are
   rejected by default;
7. select the strict `Path_cat` algebra owner and its propositional agreement
   boundary with J-derived `eq_trans`/`eq_sym` before public shaped promotion;
8. use Candidate G / `OETU-ELEMENTARY-HOTT` as the default first
   implementation slice unless the user explicitly selects another bounded
   candidate; shaped, fixed-map, path, indexed-adjunction, and Pi-compatibility
   probes may still proceed immediately while respecting their public-
   promotion dependencies;
9. specify the conservative equality MVP, stable shaped-reflexivity registry,
   structural-action interface, and fibrancy/dependent-`J` boundary without
   conflating them;
10. approve the H0/H1/H2/Omega0 tier content and the distinction between an
    architecture MVP, foundational implementation skeleton, foundational HoTT
    MVP, and optional H2/HIT completion;
11. select the permanent `PiHapply`/`PiFunext` runtime/proof-time owner and the
    route from its quasi-inverse laws to active contractible-fibre
    `IsEquivMap` evidence;
12. approve the executable foundational corpus: elementary classifier/
    eliminator beta, arbitrary Sigma/record path round trips, ordinary
    equivalence algebra, both univalence round trips, selected action beta, and
    conversion-level negative controls with their metatheoretic limitation;
13. maintain the fixed-map Omega0 equivalence/univalence/action witness and the
    indexed-adjunction triangle/mate witness as separate acceptance gates;
14. add a migration statement to the June 23 plan when this proposal is
   formally adopted.

## Long-Term Completion Criteria

The redesign program is complete only when:

```text
the selected H0 ambient universe boundary, Unit, Empty, Bool/sum, Nat, Pi,
Sigma, record, eliminators, beta laws, and ordinary identity operations are
active with diagnostics;
PiHapply/PiFunext preserve related-input observational action, satisfy runtime
beta and propositional eta, and package PiHapply as an active equivalence;
Sigma and the first dependent record have both arbitrary path-characterization
round trips and reflexive computation laws;
TypeEquiv/IsEquivMap identity, symmetry, and composition and both groupoid-
univalence round trips form an executable standard compatibility surface;
truncation properties and packaged Prop/Set/n-groupoid universes are active;
their closure, evidence-path, and universe-level truncation claims are explicit;
Path_cat is coherent with strict category computation, or a weak replacement is
classified outside strict Cat;
OneCat is defined through directed hom truncation/discreteness;
fixed-map omega-equivalence is the primary property and its Sigma package
supports usable named declarations and categorical univalence;
Adjunction is indexed by its already-named functors, with optional existential
packaging separated from the primary relation, left/right projections absent
or transparent, and unit/counit retained as stable runtime observations;
preselected named unit/counit operations have a typed proof-time declaration
bridge without erasing the canonical triangle redex or falsely claiming raw-
name runtime conversion;
ordinary IsoEvidence univalence is OneCat-scoped;
public equality computes observationally for records, Sigma, Pi, and universes;
structural reflexivity, structural action, and dependent elimination have
explicit canonical owners;
reflexive shaped J, arbitrary structured-path action, and fibrant/dependent J
are implemented and distinguished by diagnostics;
univalence forward/reverse maps have named round trips and action coherence;
Product constructor/reflexivity/decoder reductions join;
the minimal HoTT/omega adequacy matrix has no unacknowledged missing cell, its
architecture/implementation/HIT milestone name is honest, and the fixed-map
univalence/action witness composes end to end with at least one construction
iterating through the next hom level;
the indexed-adjunction witness passes independently as a category-migration
gate rather than substituting for foundational HoTT adequacy;
global Cat univalence remains explicitly axiomatic until a model is supplied;
all promoted slices pass focused probes, make check, relevant examples,
warning classification, catalog checks, health refresh, and make ci.
```

## References And Design Context

- The active code, diagnostics, SOP, Foundations, and canonical syntax remain
  authoritative over this proposal.
- The recursive `n`-type convention follows the standard HoTT truncation-level
  hierarchy in the [HoTT Book](https://homotopytypetheory.org/book/).
- The distinction between a truncation property and its higher-inductive
  reflector follows the same source.
- The observational target and dedicated identity records are informed by
  Michael Shulman's [Towards an Implementation of Higher Observational Type
  Theory](https://home.sandiego.edu/~shulman/papers/running-hott.pdf) and the
  [Narya documentation](https://narya.readthedocs.io/en/latest/).
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
  feature as experimental and proof-time; this is why declaration convenience
  rules are not selected as runtime or semantic owners.
- The 2026-07-14 feasibility findings are supported by the ignored append-only
  probes `tmp/probes/oetu_architecture_feasibility_probe.lp`,
  `tmp/probes/oetu_fixed_map_followup.lp`,
  `tmp/probes/oetu_indexed_structure_architecture_probe.lp`, and
  `tmp/probes/oetu_adjunction_named_unit_runtime_probe.lp`. The complete probe
  set was rerun warning-enabled on 2026-07-14; the latest logs end in
  `20260714-200013`. The final probe is a negative computation test whose
  expected `assertnot` statements pass. The indexed probe retains eight and
  the negative probe two scratch-local replaceable-pattern-variable
  advisories. None of these scratch artifacts is promoted kernel source;
  because all extend an imported active kernel, they preserve feasibility
  evidence but do not confer formal owner-position `probed` status.
- The later foundational feasibility review is supported by the ignored
  append-only probes `tmp/probes/oetu_hott_elementary_formers.lp`,
  `tmp/probes/oetu_hott_pi_adequacy.lp`, and
  `tmp/probes/oetu_hott_pi_stable_funext.lp`. Their warning-enabled logs also
  end in `20260714-200013` and pass without probe-local warnings. Because these
  files extend the imported active kernel rather than placing candidates at
  their intended owners, they establish feasibility only and do not confer
  formal `probed` status.
