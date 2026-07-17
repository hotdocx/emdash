# EMDASH v3.2 Equality-Valued Omega-Equivalence And Groupoidal-J Re-Redesign Proposal

Date: 2026-07-17
Last reviewed: 2026-07-17
Plan-ID: EMDASH-V3-2-EQUALITY-VALUED-OMEGA-EQUIVALENCE-REREDESIGN-2026-07-17
Status: independently reviewed and probe-refined proposed successor/overlay; not yet adopted as the active implementation master plan
Review baseline: `772411011ac721c84d143a2967f4e5c31e94bc70`
Primary predecessor: `REPORT_EMDASH_V3_2_OBSERVATIONAL_EQUALITY_TRUNCATION_UNIVALENCE_REDESIGN_PLAN_2026-07-13.md`
Depends on: `emdash3_2.lp`; `emdash3_2_checks.lp`; `REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md`; `EMDASH_FOUNDATIONS.md`
Provenance: independent peer review and user clarification sequence archived in Infinity Codex session `019f6bd3-8405-7d31-8ced-8a6b127c1499`, especially responses `0003` through `0005`
Proposed side-task ledger: [Side-Task Ledger](#side-task-ledger)
Proposed implementation entry point: [Recommended First Implementation Slice](#recommended-first-implementation-slice)
Preliminary feasibility evidence: ignored owner-position full-file probes under
`tmp/probes/evogj_*_full.lp`; no candidate has been promoted to the active
kernel

## Status And Authority

This document is a comprehensive proposed re-redesign of the equality,
omega-equivalence, univalence, groupoidality, and structured path-induction
parts of the July 13 living master plan. It exists beside that plan so that
the current implementation and its synchronized evidence remain available for
comparison while this simpler architecture is reviewed, probed, corrected,
and either adopted or rejected.

Until an explicit adoption decision is recorded:

1. `emdash3_2.lp` remains the active kernel authority;
2. `emdash3_2_checks.lp` remains the executable diagnostic authority;
3. the current SOP and Foundations report retain their ordinary authority;
4. the July 13 plan remains the active implementation master plan and ledger;
5. this report is a proposed successor/overlay and does not authorize deletion
   or migration merely by existing.

If this proposal is adopted, it should supersede the July 13 plan only for the
specific architecture tracks named below. The July 13 plan should remain a
historical and implementation-evidence record for all promoted slices. Its H0
formation/elimination work, truncation hierarchy, `CatDim`/`IsNCat` packages,
directed kernel, `PathOut` infrastructure, and validated examples must not be
discarded merely because their surrounding univalence interpretation changes.

The review baseline commit records the repository state from which this plan
was written. It is not a frozen boundary and must never be used as an implied
authorization to reset, restore, or overwrite later work.

Earlier checkpoints named by the predecessor implementation handoff are
`07a24e6f07c0cd7ecd8147f1fe6158e3af73707d` (pre-implementation comparison),
`7dc149294d554315bf79113420c572f1076a207b` (temporary progress), and the
current review baseline `772411011ac721c84d143a2967f4e5c31e94bc70`.
All three are historical comparison points only. None authorizes a reset or
limits ordinary forward editing.

## Executive Summary

The proposed redesign is based on one simplifying observation:

> Fixed-arrow omega-equivalence should store separate left and right inverse
> arrows whose cancellation witnesses are ordinary equalities in the
> appropriate hom-categories. Because every hom-category is again a category
> and every active category is intended to be univalent, those equalities
> already carry the recursive higher-equivalence content.

The current D0 certificate stores recursive `OmegaEquiv` cells and later
decodes them to ordinary hom equalities through categorical univalence. This
proposal reverses that ownership:

```text
current primary fields:
  left_cell  : OmegaEquiv(Hom_cat C x x, l o f, id_x)
  right_cell : OmegaEquiv(Hom_cat C y y, f o r, id_y)

proposed primary fields:
  left_law  : l o f =_{Obj(Hom_cat C x x)} id_x
  right_law : f o r =_{Obj(Hom_cat C y y)} id_y
```

Recursive omega-cells then become views of these equality fields rather than
independently stored data. This should remove the central duplication between
equality, omega-equivalence certificates, encoders, decoders, and recursive
cell observers.

The reviewed MVP has nine principal parts:

1. implement `OmegaEquivAlong(C,f)` as a decoded native one-constructor record
   with a real indexed eliminator;
2. make its separate inverses and equality-valued cancellation laws the
   primary fields;
3. use a stable primitive dependent-pair facade for first-class
   `OmegaEquiv(C,x,y)`, with constructor, projections, dependent elimination,
   propositional eta, and a transparent Sigma comparison;
4. identify `x =_{Obj C} y` directly with `OmegaEquiv(C,x,y)` through a
   carefully classified rewrite/unification architecture rather than a
   decoder tower;
5. distinguish the literal identity type view supplied by classifier
   unification from an explicit, decoder-free object-path adapter whose
   forward/inverse/law observers compute;
6. add the shaped `Path_cat` join and a computational explicit path-equivalence
   constructor, while deferring raw-coerced-path projection computation until
   its package/extensionality critical pair has a sound solution;
7. define general internal groupoidality by equivalence of `Core_cat(C)` with
   `C`, and use the existing `PathOut`/directed-family action as the structured
   groupoidal form of `J`;
8. complete the missing `Grpd_cat` hom/function boundary and derive both
   directions between `TypeEquiv` and omega-equivalence rather than assuming
   them;
9. demote unrelated former-specific action experiments, especially the
   current Sum action bases, from the foundational univalence MVP.

This is not a proposal to copy Book HoTT, cubical type theory, observational
type theory, or Narya. Those systems remain mathematical sanity checks and
sources of examples only. The implementation must be rediscovered in the
local Kosta--Dosen/Emdash cut-elimination architecture and in Lambdapi's
separation between runtime rewriting and proof-time unification.

## Final Independent Review Verdict And Probe Evidence

The proposal is globally coherent after the corrections recorded in this
review. Its central mathematical move is sound: bi-invertibility with separate
left and right inverse arrows and equality-valued cancellation laws is a
natural fixed-arrow notion, and iterated hom-categories make the higher
content available recursively through equality. The design is substantially
smaller and more reusable than the current decoder/certificate tower.

The proposal is not yet an implemented foundation. The active source still
uses the D0 certificate, public transparent Sigma package, decoder
capabilities, and current examples described by the predecessor plan. The
results below are preliminary owner-position feasibility evidence only. They
justify an implementation direction; they do not establish consistency,
normalization, confluence, canonicity, universe stratification, or a semantic
model.

Peer-review recommendation: adopt this revised report as the implementation
overlay for the named equality/univalence/groupoidality tracks once the owner
makes that status decision. Do not declare the July 13 implementation complete
or delete it wholesale; migrate its retained H0, truncation, dimension, and
directed assets phase by phase. The proposed core is now sufficiently coherent
and computationally feasible to implement, while the raw-path join,
unrestricted evidence property, and semantic fixed-point assurance remain
explicit research/extension gates.

The review changed five material architectural decisions:

1. the fixed-arrow evidence must be a decoded native record, not a bodyless
   constant with unexplained observers;
2. the transparent outer Sigma cannot be the direct-univalence normal form;
   the stable primitive dependent-pair facade is selected;
3. an explicit `path_equiv(p)` can compute fully, but an arbitrary raw path
   merely accepted through classifier unification cannot yet share those
   projection rules safely;
4. direct groupoid-universe work depends on completing the computational
   `Grpd_cat` hom boundary, after which the comparison with `TypeEquiv` is
   derivable in both directions;
5. a proof-time identity view `as_omega_equiv(p) := p` is valid but supplies no
   new term computation; observer computation belongs to a separate explicit
   object-path package built from `path_to_hom`, inverse paths, and J-derived
   laws.

### Measured owner-position results

All successful candidates were inserted at their intended owner positions in
temporary full copies of `emdash3_2.lp`. Quiet checks used the repository
60-second bound. The untouched active baseline `make check` passed before the
probes. Warning-enabled candidate results remained exactly at the active
baseline of 971 unjoinable-critical-pair warnings and 157 replaceable-pattern
warnings unless explicitly stated otherwise. The most comprehensive candidate
also retained the strict inferred-slot audit baseline: zero unreviewed
compound slots, 45 annotated slots, and 27 intentional clauses.

| Probe/result | Outcome | Architectural conclusion |
| --- | --- | --- |
| decoded equality-valued `OmegaEquivAlong` record, four projections, indexed eliminator, reflexivity | passes; no warning delta | selected fixed-arrow representation |
| transparent outer Sigma plus generic equality/equivalence `unif_rule` | term typing fails after eager `tau(Sigma)` decoding | reject Sigma as the direct-univalence normal form |
| stable outer facade, pack/projections/eliminator, generic proof-time comparison, reflexivity observers | passes; no warning delta | select stable primitive dependent-pair facade |
| facade eta and two-way transparent-Sigma comparison | passes; constructor round trips compute, both general round trips are propositional | end-user elimination/comparison is feasible; primitive eliminator remains trusted surface |
| identity type view `as_omega_equiv(p) := p` plus explicit general object-path package | passes; identity view stays literally `p`; package forward/inverse/law projections compute through `path_to_hom` and J; no warning delta | classifier interchangeability and computational reification are distinct public interfaces |
| shaped `Path_cat` classifier join | passes; no warning delta | an explicit shaped join is required in addition to the generic comparison |
| explicit `path_equiv(p)` with `path_sym(p)` inverses and J-derived laws | passes; all named observers compute; no warning delta | computational path constructor is feasible |
| raw path projection rule `omega_equiv_to(p) -> p` | adds an unjoinable package/path critical pair | do not claim raw coerced-path projection computation yet |
| package collapse in the literal path case | adds further critical pairs and divergence with evidence/elimination | reject this runtime shortcut |
| `Core_incl_func(Path_cat A) == id` plus canonical path-category groupoidality | passes; no warning delta | canonical introduction of `IsGroupoidalCat` is feasible |
| retargeted rigid Cat-universe equality to stable facade | passes and self-normalizes finitely; no warning delta | Cat direct identity is high-confidence operationally |
| broad runtime `Grpd_cat` identity/composition as lambdas | passes quietly but adds 36 critical-pair and 2 replaceable-pattern warnings | reject broad runtime folds |
| `Hom_cat Grpd_cat A B -> Path_cat(Function_grpd A B)` plus stable function owners and proof-time identity/composition comparisons | passes; no warning delta | selected `Grpd_cat` completion boundary |
| `TypeEquiv -> OmegaEquiv(Grpd_cat)` | passes; forward, inverse, and law projections compute; no warning delta | no decoder axiom is needed in this direction |
| `OmegaEquiv(Grpd_cat) -> TypeEquiv` through internally derived quasi-inverse and existing `is_equiv_map_by_inverse` | passes; forward map, selected inverse, right law, and forward-map round trip compute; no warning delta | no new bridge capability is needed; the pre-existing bodyless theorem capability remains a proof-completeness obligation |

#### Rejected, repaired, and still-open probe ledger

The negative results matter as much as the passing candidates. They reject
particular normal forms and reduction orientations; they do **not** reject the
equality-valued omega-equivalence architecture as a whole.

| Attempt | Measured failure | Classification and available alternative |
| --- | --- | --- |
| transparent public `Sigma f, Along(f)` as the direct-univalence classifier | a typed term at `Eq(Obj C,x,y)` did not acquire the unfolded `tau(Sigma ...)` type: decoding the transparent Sigma ran before the classifier-level unification rule could provide the intended join; an additional rule against the unfolded Sigma did not repair it | **representation rejected, not a core blocker**; use the warning-neutral stable dependent-pair facade and retain transparent Sigma only as a derived comparison view (`031650`, `031813`) |
| generic object-univalence comparison alone for literal `Path_cat A` | the typed assertion requiring `OmegaEquiv(Path_cat A,x,y) == Eq(A,x,y)` did not fire from the generic variable-category equation | **insufficient generic join, not a blocker**; add the narrow shaped `Path_cat` comparison, which passed without warning delta (`032208` failed; `032228`/`032231` passed) |
| raw-path observer `omega_equiv_to(Path_cat A,p) -> p` | because classifier comparison also lets a facade package inhabit the path classifier, the variable `p` matches `omega_equiv_pack(...,f,u)`; the normal package projection reduces to `f`, while the raw-path rule reduces to the whole package. Those results do not join. The warning inventory changed from `971/157` to `972/160` | **runtime orientation rejected**; type-level acceptance of a raw path remains feasible, and the explicit `path_equiv(p)` constructor gives computational projections (`032332`, `032339`) |
| runtime collapse `omega_equiv_pack(Path_cat A,...,f,u) -> f` intended to repair that diamond | it erased the package before `omega_equiv_to`, `omega_equiv_evidence`, and the primitive dependent eliminator could consume it, producing additional divergent orders; warnings rose to `975/164` | **shortcut rejected**; do not equate raw and packaged presentations by erasure. A future extensional/join theorem or different representation may address this, but it is not required for the explicit-path MVP (`032408`, `032413`) |
| reflexivity observer with the reducible classifier written explicitly as `eq_refl(Obj C,x)` on the LHS | the explicit inferred classifier overlapped the existing `Obj` reductions for `Op`, `Path`, `Catd`, terminal, and related owners, adding eight unjoinable pairs (`979/157`) | **LHS repaired under the SOP**; retain the genuine category/object discriminators but write the recoverable classifier slot as `_`. The corrected owner returned exactly to `971/157` (`032020`/`032027` rejected; `032102`/`032107` passed) |
| first `Grpd_cat` hom-completion placement/signature | subject reduction could not establish the intended `Grpd` versus `tau(Obj Grpd_cat)` endpoint (`Cannot solve Grpd ≡ τ(Obj Grpd_cat)`) | **owner/signature error, repaired rather than architectural failure**; canonical endpoints and owner order fixed the candidate (`032908` failed; final candidate below passed) |
| broad runtime `Grpd_cat` identity and composition folds directly to lambdas | quiet checking passed, but the rules competed with generic category identity/composition and functor-action owners, raising the inventory to `1007/159` | **runtime orientation rejected, not a Grpd blocker**; use stable semantic function heads with point-application beta and narrow proof-time comparisons. That design returned to `971/157` (`032933`/`032941` rejected; `033621`/`033625` passed) |

The malformed intermediate probe `031712` contained a binder-syntax error and
is deliberately not counted as architectural evidence. Likewise, a direct
lambda-pattern presentation was abandoned in favor of stable rigid heads:
Lambdapi unification rules are not reliably transitive, and consumers written
against the stable intermediary are both clearer and warning-neutral.

The phrase **raw-path projection computation** therefore has a precise and
narrow meaning here. It is not the computation of `path_equiv(p)`, which
passed. It is the stronger proposed convenience behavior in which a bare
`p : x =_A y`, accepted silently at the type
`OmegaEquiv(Path_cat A,x,y)`, would also reduce under `omega_equiv_to` as if it
had first been packaged. That reduction is the rule that failed the critical-
pair test. This leaves a surface-coercion/join question open; it does not block
paths as equivalences, their explicit computational package, direct
univalence, or the structured groupoidal-J track.

#### Consequences for the pre-probe proposal

The preliminary probes changed the original unmeasured proposal in five
specific ways:

1. its transparent-Sigma default is not computationally viable as the direct
   classifier normal form; the stable outer facade is now selected;
2. the generic object-univalence comparison does not by itself supply the
   literal `Path_cat` diamond; a shaped comparison is required;
3. silent raw-path projection and runtime path-package collapse are no longer
   milestones of the initial MVP; explicit `path_equiv` is the computational
   owner while a general join is a later extension gate;
4. direct runtime lambda folds are not an acceptable `Grpd_cat` identity and
   composition policy; stable semantic heads plus proof-time comparison are
   the measured replacement;
5. identity classifier views can remain literal `lambda p, p`, but any claim
   of recursive observer computation must use the separately constructed
   object-path package; this adapter passed without adding opaque authority or
   warning deltas.

None of these is a blocker to the selected core. The genuinely unresolved
work is narrower: unrestricted evidence property/extensionality, a principled
raw-path/package join if that convenience is ultimately wanted, full migration
from D0 and decoder consumers, a nonliteral structured-groupoidal consumer,
and semantic assurance for the generic equality/equivalence fixed point.
Direct rigid runtime equality for `Grpd_cat`, unconditional `NCat` object
truncation, and HIT/reflector work were not established by these probes; they
must be reported as unprobed or later-phase obligations, not as failed
candidates.

#### SOP and rule-hygiene audit of the review probes

The probes followed the active README/SOP discipline relevant to feasibility
work:

- candidates were placed at their intended owners in temporary full-file
  copies rather than appended after all later rules;
- quiet checks were bounded to 60 seconds and subject-reduction checking was
  retained; `--no-sr-check` was not used;
- runtime claims were tested by reduction/assertion, while proof-time
  `unif_rule` claims were exercised by typed `eq_refl` consumers rather than
  conversion assertions alone;
- warning-enabled comparisons were made against the same `971/157` baseline;
  concrete overlap families, not warning count in isolation, motivated the
  rejected orientations;
- inferred classifier/source slots on rewrite LHSs were written as `_` when
  they were recoverable and were retained only when they were actual
  discriminators or guards. The explicit-`Obj` reflexivity experiment above is
  the measured example that forced this correction;
- the most comprehensive candidate preserved the strict LHS audit at zero
  unreviewed compound slots, 45 annotated slots, and 27 intentional clauses;
- no probe was promoted to the active kernel, and no active validation was
  weakened.

Current successful local review logs (ignored and therefore
reproducible/prunable rather than durable authorities) are:

- `logs/probes/evogj_eq1_native_record_owner_full-20260717-031514.log`;
- `logs/probes/evogj_eq1_stable_outer_direct_unif_full-20260717-032107.log`;
- `logs/probes/evogj_eq1_path_generator_full-20260717-032542.log`;
- `logs/probes/evogj_eq1_path_groupoidality_full-20260717-032757.log`;
- `logs/probes/evogj_eq1_cat_direct_retarget_full-20260717-032640.log`;
- `logs/probes/evogj_grpd_cat_core_completion_full-20260717-033625.log`;
- `logs/probes/evogj_type_equiv_to_omega_bridge_full-20260717-033909.log`;
- `logs/probes/evogj_omega_type_equiv_bidirectional_bridge_full-20260717-034247.log`;
- `logs/probes/evogj_outer_facade_sigma_comparison_full-20260717-034636.log`;
- `logs/probes/evogj_eq1_general_object_path_adapter_full-20260717-045205.log`;
- `logs/probes/evogj_eq1_general_object_path_adapter_full-20260717-045217.log`.

The corresponding latest candidate source is
`tmp/probes/evogj_eq1_general_object_path_adapter_full.lp`. It is ignored
review evidence and must be reproduced at the then-current owner before
promotion.

The corresponding negative/replacement evidence is recorded in:

- `logs/probes/evogj_eq1_direct_unif_owner_full-20260717-031650.log`;
- `logs/probes/evogj_eq1_direct_unif_owner_full-20260717-031813.log`;
- `logs/probes/evogj_eq1_path_join_full-20260717-032208.log`;
- `logs/probes/evogj_eq1_path_join_full-20260717-032228.log`;
- `logs/probes/evogj_eq1_path_join_full-20260717-032231.log`;
- `logs/probes/evogj_eq1_path_join_full-20260717-032332.log`;
- `logs/probes/evogj_eq1_path_join_full-20260717-032339.log`;
- `logs/probes/evogj_eq1_path_join_full-20260717-032408.log`;
- `logs/probes/evogj_eq1_path_join_full-20260717-032413.log`;
- `logs/probes/evogj_eq1_stable_outer_direct_unif_full-20260717-032020.log`;
- `logs/probes/evogj_eq1_stable_outer_direct_unif_full-20260717-032027.log`;
- `logs/probes/evogj_eq1_stable_outer_direct_unif_full-20260717-032102.log`;
- `logs/probes/evogj_eq1_stable_outer_direct_unif_full-20260717-032107.log`;
- `logs/probes/evogj_grpd_cat_core_completion_full-20260717-032908.log`;
- `logs/probes/evogj_grpd_cat_core_completion_full-20260717-032933.log`;
- `logs/probes/evogj_grpd_cat_core_completion_full-20260717-032941.log`;
- `logs/probes/evogj_grpd_cat_core_completion_full-20260717-033621.log`;
- `logs/probes/evogj_grpd_cat_core_completion_full-20260717-033625.log`.

These ignored probes and logs are review evidence, not repository authorities.
The implementing agent must reproduce the relevant smallest candidate against
the then-current owner before promotion.

### Quality assessment after review

| Dimension | Assessment |
| --- | --- |
| Global coherence | high for the proposed MVP architecture; markedly more natural than the current parallel equality/certificate/decoder ownership |
| Mathematical correctness | high for the fixed-arrow and groupoid/`TypeEquiv` fragment; conditional at unrestricted omega level on the intended coinductive/greatest-fixed-point semantics |
| Syntactic correctness | high for the probed core; exact promoted names, locations, and implicit slots remain implementation work |
| Computational feasibility | high for construction, projection, reflexivity, the general object-path adapter, explicit literal-path witnesses, Cat self-identity, and both groupoid-equivalence bridges; medium-low only for observers applied directly to an unreified raw identity view |
| Completeness for a minimal MVP | credible but incomplete until direct owners replace decoders, a nonliteral groupoidal consumer exists, and public examples use only the new interface |
| Reusability | promising: native fixed-arrow elimination plus stable first-class elimination and Sigma comparison support library construction; not yet demonstrated in active public code |
| Expressiveness versus ordinary HoTT | intended to cover equality, equivalence, univalence, and structured transport with stronger directed/omega-categorical primitives; still lacks ordinary broad HIT/reflector coverage and does not automatically structure arbitrary raw motives |
| Foundational assurance | operational evidence only; the generic unification equation remains trusted logical authority and requires finite/stratified semantic sanity evidence |

### Status of the active implementation against this proposal

| Active area | Honest status relative to the proposed endpoint |
| --- | --- |
| decoded H0 formers and selected observational equality | substantial retained foundation; their constructor/eliminator computation is real, while observational equality is intentionally shaped rather than a complete general calculus |
| directed `Cat`/functor/transfor/family kernel | strong retained foundation and the main reason the redesign is plausible |
| current `OmegaEquivAlong_D0` | useful operational experiment with inverse/cell observers, but still an opaque primary certificate with no native construction/elimination/extensionality account |
| current public `OmegaEquiv` | transparent Sigma and usable on explicitly packaged data; not suitable as the new direct-univalence classifier normal form |
| current Cat-universe equality | finite direct runtime classifier and valuable evidence, but its computations route through D0/decoder-era interfaces and generic `eq_refl` remains distinct from canonical `cat_path_refl` |
| current Grpd-universe equality | finite `GrpdPathView := TypeEquiv` plus opaque decoder round trips; the active `Grpd_cat` hom structure is incomplete for the proposed internal equivalence reading |
| current `PathOut`/`path_ind_sec` | materially computational through existing `fapp*`/`tapp*` rules and shaped motive folds; comparison with groupoidal primitive J is incomplete, not absent |
| current Sum action example | mathematically meaningful for disjoint sums and computational on registered bases; valid library evidence but over-specialized as a foundational univalence prerequisite |
| truncation/`NCat` spine | semantically meaningful retained work; unconditional object truncation still depends on a real scoped equivalence-evidence property theorem |
| HIT/reflector scope | deferred; this redesign improves the equality/transport substrate but does not by itself provide a truncation reflector, Circle, general restricted HIT eliminator, or raw-family fibrancy |

Thus the active implementation is neither a sham nor the wanted completed
foundation. It contains a substantial natural categorical kernel and several
genuine computations, surrounded in the current univalence layer by too many
opaque capability and decoder boundaries. The redesign is a feasible
migration from real assets, not a greenfield replacement and not a license to
describe the current decoder-based layer as already complete.

### Expressiveness comparison with ordinary HoTT

| Topic | Reviewed Emdash target versus ordinary HoTT |
| --- | --- |
| Equality and J | retains primitive intensional equality and `ind_eqr`; adds shaped observational equality and directed/path-category action rather than replacing raw J |
| Equivalence | uses equality-valued categorical bi-invertibility as the computational owner; contractible-fibre `TypeEquiv` remains a derived/library formulation |
| Univalence | intends equality/equivalence comparison in trusted Lambdapi unification plus selected runtime universe heads, giving more direct observer computation than axiom-only Book HoTT but requiring a new conversion-soundness account |
| Function/Sigma/record paths | already has meaningful observational interfaces and selected computation; coverage is uneven and not a general normalization/canonicity theorem |
| Directed higher structure | substantially more expressive natively: categories, omega-homs, functors, transfors, and directed families are kernel-level concepts rather than encodings in undirected types |
| Motives/transport | arbitrary `Grpd` families retain primitive J; richer Cat-valued transport computes when the motive is supplied as a functor/directed family, so raw higher-family structuring is less automatic than in mature type theories |
| HITs and reflectors | materially behind mature HoTT/cubical libraries: no truncation reflector, Circle, representative HIT, or general HIT eliminator is currently active |
| Metatheory and libraries | far less mature: there is no comparable normalization/model result or broad standard library yet; the redesign is an MVP foundation plan, not feature parity |

The target is therefore not simply weaker or stronger than HoTT. It is
stronger and more computationally explicit in directed categorical structure,
while currently narrower in higher-inductive constructions, library coverage,
and metatheoretic assurance.

## Original Goal And Revised Design Intent

The original wanted endpoint remains a small computational foundation on
which an end user can build genuine type-theoretic and categorical standard
libraries. The foundation should feel like a natural extension of the
existing omega-categorical kernel, not a collection of special certificates,
decoder capabilities, and former-specific equations introduced only to make
selected examples pass.

The intended MVP should support:

- primitive ambient `Grpd`, decoding, equality, reflexivity, and raw `J`;
- the existing computational `Cat`/`Obj`/iterated-`Hom`/identity/composition
  kernel;
- functors, transformations, directed families, and higher projections;
- equality as hom in literal path categories;
- internally groupoidal categories not required to be syntactically
  `Path_cat(A)`;
- fixed-map and first-class omega-equivalence with reusable construction and
  observation APIs;
- direct computational/proof-time univalence rather than mandatory
  encoder/decoder round trips;
- structured, functorial motives whose transport is existing categorical
  action;
- truncated universes and finite directed dimensions embedded through actual
  functors when a concrete consumer needs them;
- a conservative shaped-computation policy for Product, Sigma, records, sums,
  and later formers.

The MVP does not require:

- copying an external cubical or observational syntax;
- automatically turning every raw meta-level family into a structured motive;
- a new general `J` beyond primitive `ind_eqr` and the existing `PathOut`
  action;
- arbitrary HITs or truncation reflectors;
- a generic full-subcategory construction;
- runtime decomposition of every identity or equivalence constructor;
- a complete model, normalization proof, canonicity theorem, or stratified
  universe hierarchy before any operational work can proceed.

Those stronger goals remain later research or standard-library tracks. They
must not be claimed merely because Lambdapi accepts a rewrite or unification
rule.

## Independent Review Diagnosis

### Foundations that should be retained

The following current components are globally coherent and should be treated
as assets of the redesign:

- the computational category, functor, transfor, and directed-family layer;
- the iterated-hom architecture, which already makes every hom-category a
  category and therefore supports dimension-recursive reasoning;
- `Path_cat(A)`, including `Obj(Path_cat A) -> A`, homs as equality path
  categories, and identity as `eq_refl`;
- `Core_cat(C) := Path_cat(Obj C)` and `Core_incl_func(C)`;
- `PathOut_cat`, its contravariant source action, the canonical `rho` arrow,
  motive transport, `path_ind_sec`, and the `PathInd_*` telescope packaging;
- the ordinary primitive equality/J fallback for unstructured motives;
- decoded H0 formers, elementary eliminators, Sigma/record path interfaces,
  truncation levels, truncated packages, `CatDim`, `IsNCat`, `NCat`, and the
  current evidence-retaining package discipline;
- the runtime/proof-time distinction and existing identity-normal-form policy,
  including the refusal to reduce a Product-category identity globally to a
  pair of identities.

### Architecture that should be reopened

The following current choices should be treated as successful experiments,
not presumed permanent foundations:

- the opaque recursive `OmegaEquivAlong_D0` certificate as the primary
  mathematical representation;
- storing recursive omega-equivalence cells and later decoding them to
  equality-valued laws;
- parallel global capabilities `cat_univalence` and
  `cat_univalence_by_decoder`;
- the first-class decoder/round-trip hierarchy required only because equality
  and equivalence remain separate classifiers;
- contractible-fibre `TypeEquiv` as the primary operational representation of
  equivalence in the groupoid universe;
- finite observation trees as a substitute for a direct, understood
  fixed-arrow representation;
- treating the absence of a traditional fibrancy package as a blocker even
  when the proposed motive is already a structured directed family;
- former-specific observational-action bases whose only foundational consumer
  is a demonstration that generic `eq_ap` can be bridged to a component view;
- the conclusion that direct groupoid universe identity failed in principle,
  when the measured failure concerned a recursively transparent
  contractible-fibre representation.

### Revised interpretation of current achievements

The current Cat-universe classifier rule already demonstrates that direct
univalence can be a finite operational normal form when the equivalence
payload is stable. The `PathOut` section already has substantial component
and motive-specific computation despite being a bodyless primitive symbol.
The current `IsDiscreteCat` already contains the likely groupoidality concept
as its second field. These are not missing ideas; they need to be reorganized
under simpler owners.

## Core Mathematical Hypothesis

Let `C : Cat`, `x y : Obj(C)`, and `f : Hom_C(x,y)`. The proposed fixed-arrow
evidence is bi-invertibility with separate inverse arrows:

```text
OmegaEquivAlongEq(C,x,y,f)

left_inv(u)  : Hom_C(y,x)
right_inv(u) : Hom_C(y,x)

left_law(u) :
  left_inv(u) o f =_{Obj(Hom_cat C x x)} id_x

right_law(u) :
  f o right_inv(u) =_{Obj(Hom_cat C y y)} id_y.
```

The separate inverse choices are deliberate. At the groupoid/type level the
bi-invertible formulation is expected to make fixed-map equivalence evidence
property-valued, unlike raw single-quasi-inverse data. At higher categorical
levels the analogous theorem is an acceptance obligation, not an assumption
that may be inferred from the shape alone.

Mathematically, first-class equivalence is the dependent pair:

```text
OmegaEquivEq(C,x,y)
  := Sigma f : Hom_C(x,y), OmegaEquivAlongEq(C,x,y,f).
```

Operationally, the selected classifier is the stable primitive facade for
this dependent pair, not the transparent Sigma alias. Its explicit Sigma view
and propositional round trips preserve this mathematical reading.

The intended univalence equation is:

```text
x =_{Obj C} y  ==  OmegaEquivEq(C,x,y).
```

Because `Hom_cat C x x` and `Hom_cat C y y` are themselves categories, the
two equality-valued laws can be observed through the same univalence equation
at the next hom level. The recursion is therefore latent in equality and
revealed only through observations. It need not be materialized as a
transparent infinite Sigma tree.

For finite `NCat` levels, this interpretation descends through the explicit
dimension index. At the omega level, its mathematical reading is the usual
greatest-fixed-point/coinductive notion of recursively invertible cells. That
reading is semantic justification, not a demand to copy an external
coinductive implementation.

### Finite approximant sanity account

The local semantic check is the dimension-indexed recursive family suggested
by the existing iterated-hom architecture. Suppressing endpoint indices, its
successor clause is:

```text
Equiv_(n+1)(f)
  := Sigma (l,r),
       Equiv_n(l o f, id) * Equiv_n(f o r, id).
```

The base clause is the corresponding active zero/terminal hom condition. If
the induction hypothesis identifies equality in every `n`-dimensional hom
with `Equiv_n`, then the proposed equality-valued cancellation fields are
exactly this successor clause. Thus the new record does not discard the
recursive cells of D0; it changes them from stored duplicate fields into the
inductively interpreted equalities of the next hom.

For finite `NCat`, hom dimension decreases and this account is well founded.
At unrestricted omega dimension, the same equation is read coinductively as
the greatest fixed point `Equiv_omega = nu X. F(X)`. The Lambdapi stable head
is an operational presentation of that equation, not itself a construction
of the greatest fixed point. In particular, the `C = Cat_cat` self case no
longer diverges syntactically in the probe because the facade is stable, but
that termination does not replace the semantic fixed-point and universe-level
justification.

This is sufficient as the plan's preliminary semantic sanity argument. A
promoted finite-`NCat` theorem should instantiate the exact repository
`CatDim` base/successor conventions; a full omega model or productivity proof
remains `EVOGJ-METATHEORY`.

## Proposed Kernel Architecture

The declarations below are conceptual signatures. Exact Lambdapi syntax,
modifiers, implicit arguments, owner position, and final names must be selected
by probes. A candidate must not be promoted merely because this pseudocode is
well-typed on paper.

### A. Equality-valued fixed-arrow evidence

Introduce a staging candidate next to the current D0 owner as a decoded native
one-constructor record. A bodyless classifier plus four bodyless observers
would repeat the central defect of D0 and is not an acceptable final
representation:

```text
(C : Cat) (x y : Obj C) (f : Hom C x y)
inductive OmegaEquivAlongEqData_EQ1 : TYPE :=
| omega_equiv_along_intro_EQ1
    (left_inv right_inv : Hom C y x)
    (left_law  : left_inv o f = id_x)
    (right_law : f o right_inv = id_y)

constant symbol OmegaEquivAlong_EQ1
  [C : Cat] [x y : Obj C]
  (f : Hom C x y) : Grpd;

rule tau(OmegaEquivAlong_EQ1(C,x,y,f))
  -> OmegaEquivAlongEqData_EQ1(C,x,y,f);

symbol omega_equiv_along_left_inv_EQ1  ...;
symbol omega_equiv_along_right_inv_EQ1 ...;

symbol omega_equiv_along_left_law_EQ1
  (u : OmegaEquivAlong_EQ1 f)
  : left_inv(u) o f =_{Hom C x x} id_x;

symbol omega_equiv_along_right_law_EQ1
  (u : OmegaEquivAlong_EQ1 f)
  : f o right_inv(u) =_{Hom C y y} id_y;
```

The candidate needs explicit construction rather than unexplained observers:

```text
omega_equiv_along_intro_EQ1
  (l r : Hom C y x)
  (alpha : l o f = id_x)
  (beta  : f o r = id_y)
  : OmegaEquivAlong_EQ1 f.
```

Projection beta should expose exactly the four supplied fields. Canonical
reflexive evidence should be built through this representation or be a stable
constructor with the same observed fields:

```text
omega_equiv_along_refl_EQ1(C,x)
  : OmegaEquivAlong_EQ1(id_x).
```

The native generated eliminator must be wrapped by a reviewed public indexed
eliminator. The arrow `f` is an index of the record family: the motive ranges
over `f` and its evidence rather than treating one fixed `f` as a uniform
parameter. Constructor beta is required. No runtime eta or proof erasure is
required initially.

This representation has passed the preliminary owner-position probe with all
four constructor and reflexivity observations, indexed elimination, subject
reduction, and no warning delta. Promotion still requires reproducing the
candidate against the current source and adding permanent diagnostics.

### B. Recursive omega-cells become derived views

Compatibility views corresponding to the current recursive fields should be
defined from the equality laws:

```text
omega_equiv_along_left_cell_EQ1(u)
  : OmegaEquivEq(
      Hom_cat C x x,
      left_inv(u) o f,
      id_x)

omega_equiv_along_right_cell_EQ1(u)
  : OmegaEquivEq(
      Hom_cat C y y,
      f o right_inv(u),
      id_y).
```

If equality and omega-equivalence are directly comparable, the cheapest
typing-only body is the literal identity view of `left_law(u)` or
`right_law(u)`. That view does not change the term head and therefore does not
make omega-equivalence projections compute. A compatibility view intended to
support recursive observation must instead use the explicit general
object-path package described below:

```text
omega_equiv_along_left_cell_EQ1(u)
  := object_path_equiv_EQ1(Hom_cat C x x,left_law(u))

omega_equiv_along_right_cell_EQ1(u)
  := object_path_equiv_EQ1(Hom_cat C y y,right_law(u)).
```

This is a transparent construction from `path_to_hom`, inverse-path action,
and J-derived cancellation laws, not a replacement opaque encoder. Until that
adapter is promoted, these computational compatibility views may temporarily
use the existing encoders. That temporary dependency must be removed before
decoder retirement is declared complete.

The reverse direction already exists conceptually in the current source:
current recursive D0 cells are decoded into `omega_equiv_left_law` and
`omega_equiv_right_law`. This provides an initial migration map from old D0
evidence to the proposed equality-valued evidence.

### C. First-class packaging fork

The preliminary packaging fork is now closed in favor of Candidate R. The
transparent Sigma remains a derived/library presentation, not the classifier
normal form used by direct univalence.

#### Candidate S: transparent Sigma comparison view

The first experiment was:

```text
OmegaEquiv_EQ1(C,x,y)
  := Sigma f : Hom C x y, OmegaEquivAlong_EQ1(C,x,y,f).
```

Advantages:

- minimal change from the current public API;
- ordinary Sigma introduction and elimination remain available;
- fixed-map evidence remains the sole semantic owner;
- the outer representation is finite because the evidence classifier is a
  stable head;
- existing code that packages a named arrow has a direct migration path.

Measured failure:

- when a term is checked against `tau(OmegaEquiv_EQ1)`, the transparent alias
  unfolds through `Sigma` and `tau(Sigma)` eagerly decodes to native
  `tauSigma_` before the classifier-level generic unification rule can identify
  equality with `OmegaEquiv_EQ1`;
- consequently, a path term accepted at the conceptual classifier boundary is
  rejected at the decoded term boundary;
- an explicit unification equation against the unfolded Sigma did not repair
  this mismatch;
- stable projection aliases do not solve a classifier that has already
  disappeared under decoding.

Candidate S is still useful as the transparent mathematical presentation and
for ordinary Sigma elimination. It must be connected propositionally to the
selected facade, but it is rejected as the direct-univalence normal form.

#### Candidate R: selected stable primitive dependent-pair facade

Use:

```text
constant symbol OmegaEquiv_EQ1(C,x,y) : Grpd;

omega_equiv_pack_EQ1
  (f : Hom C x y)
  (u : OmegaEquivAlong_EQ1 f)
  : OmegaEquiv_EQ1(C,x,y);

omega_equiv_to_EQ1
  (e : OmegaEquiv_EQ1(C,x,y)) : Hom C x y;

omega_equiv_evidence_EQ1
  (e : OmegaEquiv_EQ1(C,x,y))
  : OmegaEquivAlong_EQ1(omega_equiv_to_EQ1(e)).
```

with the two constructor projection betas. Candidate R is mathematically the
same dependent pair; its purpose is only to provide a stable classifier head
and observer boundary. It must also provide:

- a primitive dependent-pair eliminator with constructor beta;
- propositional eta derived through that eliminator, never a broad runtime eta
  rewrite;
- conversions to and from the transparent Sigma presentation, with both
  round trips proved propositionally and constructor cases computing;
- no unbacked runtime eta;
- specifically classified computation for equality terms that cross into the
  facade through direct univalence.

The full owner-position candidate passed with pack/projection beta, dependent
elimination, derived eta, Sigma comparison, and no warning delta. This closes
the operational fork. The cost must remain explicit: because the stable
classifier deliberately has no eager native decoding rule, its eliminator is
new trusted record-like kernel surface. The intended semantics is the
dependent pair, and the Sigma comparison is the executable interface sanity
check.

#### Selection gate

The gate fired for three measured reasons:

1. generic object-equality unification does not survive transparent Sigma
   term decoding;
2. the rigid first-class head supports the generic classifier equation,
   reflexivity observers, shaped joins, and Cat self-universe normal form with
   no warning delta;
3. dependent elimination, eta, and Sigma round trips are available through a
   small stable interface.

Candidate R is therefore the selected implementation target. Candidate S is
retained as `OmegaEquivSigma` (or an equivalent library name), not as a
parallel foundation.

### D. Direct univalence equations

The target generic comparison is:

```text
unif_rule
  @= (Obj $C) $x $y
  == OmegaEquiv_EQ1 $C $x $y.
```

This is proof-time logical authority, not runtime normalization. It must be
classified accordingly: a typed `eq_refl` consumer proves that Lambdapi fired
the rule, not that the rule is mathematically sound.

The stable-facade form of this generic comparison passed the preliminary full
owner-position probe. Both directions of term typing work, the classifiers do
not become runtime-convertible, and a negative primitive-`J` control remains
stuck on canonical facade reflexivity because that term is deliberately not
generic `eq_refl`. This is operational evidence, not a semantic proof.

#### Classifier identity views versus computational adapters

The generic unification equation allows a named typing view with a literal
identity body:

```text
as_omega_equiv_EQ1(p : x =_{Obj C} y)
  : OmegaEquiv_EQ1(C,x,y)
  := p.
```

This is a zero-cost proof-time view, not a computational cast. Lambdapi does
not insert a package, change the head of `p`, synthesize fixed-map evidence, or
add beta rules for `omega_equiv_to`, inverse projections, laws, or the facade
eliminator. The inverse typing view can likewise be literal identity.

When those observations are required, use a separately named, defined
adapter:

```text
object_path_equiv_EQ1(p)
  := omega_equiv_pack_EQ1(
       path_to_hom(C,p),
       object_path_equiv_along_EQ1(p)),
```

where the selected left and right inverse arrows are
`path_to_hom(C,path_sym(p))` and the cancellation laws are derived by
`ind_eqr`. This adapter is constructed from existing semantic owners; it is
neither a new opaque encoder nor a bodyless univalence capability.

The owner-position probe establishes the intended separation:

- `as_omega_equiv_EQ1(p) -> p` definitionally;
- `omega_equiv_to_EQ1(object_path_equiv_EQ1(p)) -> path_to_hom(C,p)`;
- both inverse projections expose `path_to_hom(C,path_sym(p))`;
- both law projections expose their named J-derived witnesses;
- `omega_equiv_to_EQ1(as_omega_equiv_EQ1(p))` deliberately remains stuck for
  a variable `p`;
- quiet and warning-enabled checks pass at the unchanged `971/157` inventory.

Thus “decoder-free” means that no opaque equivalence/round-trip capability is
needed. It does not mean that proof-time classifier equality automatically
reifies a raw term into an observable record. Public APIs and examples must
say whether they need only the identity type view or the computational
adapter.

The target runtime policy is hybrid:

- preserve or restate direct runtime equality for rigid universe owners where
  a finite normal form and joining observers are measured;
- initially use proof-time comparison for variable `C` because a generic
  runtime rule overlaps every category constructor whose `Obj` reduces;
- add shaped joins for `Path_cat` and later Product/Sigma/Functor categories
  only when an actual consumer requires them;
- do not make generic `eq_refl` runtime-reduce to a structured equivalence
  package;
- expose canonical equivalence observations of `eq_refl` through projections
  or narrow proof-time comparisons.

The reflexivity observer rules should retain `C`, endpoints, and the observer
head as discriminators but write the inferred equality classifier as `_` on
the rule LHS. Spelling it as `Obj C` produced eight additional overlap
warnings because `Obj` itself has multiple runtime reducers; the inferred-slot
version was subject-reducing and warning-neutral.

The already-active rigid Cat-universe rule is evidence that this policy can
produce a finite direct normal form. A redesigned Grpd-universe direct rule or
unification equation must be re-probed against the new stable payload; the
earlier transparent contractible-fibre timeout does not decide this case.

Direct univalence is not made mathematically tautological merely by placing it
in Lambdapi conversion. The generic equation internalizes the univalence
principle in trusted proof-time unification, and at the omega level it also
commits to the recursive/greatest-fixed-point interpretation of equality-
valued invertibility. Before calling the result a finished foundation, the
project needs at least a finite-dimensional/stratified semantic sanity account
showing that the equation has the intended approximants and does not identify
unrelated classifiers. A full normalization or model theorem remains a
separate research deliverable.

### E. Observer table: the real computational-univalence surface

Classifier comparison alone is insufficient. Terms accepted across the
equality/equivalence boundary must interact coherently with equivalence
observers. The MVP observer matrix is:

| Term/presentation | Required computation or comparison |
| --- | --- |
| `omega_equiv_pack(f,u)` | `to` returns `f`; evidence returns `u` |
| `eq_refl x` used as `OmegaEquiv(C,x,x)` | `to` exposes `id_C(x)` |
| same reflexivity | both inverse observers expose `id_C(x)` |
| same reflexivity | both law observers expose canonical reflexive/unit laws |
| explicit `path_equiv(p)` in `Path_cat A` | `to` exposes `p` |
| same explicit package | left/right inverse observers expose `path_sym(p)` |
| same explicit package | cancellation laws expose the selected J-derived inverse/unit theorems |
| raw `p : x =_A y` merely accepted as `OmegaEquiv(Path_cat A,x,y)` | classifier use is allowed; projections are not promised to compute in the initial MVP |
| general object path `p : x =_{Obj C} y` through `as_omega_equiv(p) := p` | identity type view only; no new observer computation |
| same path through `object_path_equiv(p)` | `to` exposes `path_to_hom(C,p)`; inverses and laws expose the defined path/J data |
| Product-category identity | compare with component identities proof-time; do not globally reduce generic `id` to a pair |
| equality law used as next-hom equivalence | identity view suffices for typing; use `object_path_equiv(law)` when recursive observers must compute; no opaque decoder |
| non-reflexive arbitrary equivalence used by primitive `J` | typechecks as equality, but `J` need not runtime-reduce |

Every promoted classifier equation must name the observers that make its
consumer behavior meaningful. A bare unification rule with no operational
consumer is not completion.

There are three deliberately different interfaces here. Direct classifier
unification permits equality and equivalence terms to be supplied to APIs
without a decoder, and a named `as_omega_equiv(p) := p` may expose that literal
identity view. General computational observation uses the constructed
`object_path_equiv(p)` package. Literal path categories additionally use the
specialized `path_equiv(p)` package when the forward arrow should compute all
the way to `p`, rather than only to `path_to_hom(Path_cat A,p)`. A preliminary direct rule
`omega_equiv_to(p) -> p` overlapped with the ordinary package projection; a
package-to-path collapse then produced additional divergent pairs with the
evidence projection and eliminator. Raw-coerced projection computation is
therefore deferred until a property/quotient/eta account supplies a joining
principle. The plan must not conceal this boundary by calling the explicit
constructors definitionally silent coercions.

### F. Exact `Path_cat` join

The type-correct shaped comparison is:

```text
OmegaEquiv_EQ1(Path_cat A,x,y) == (x =_A y).
```

It is not a comparison with `Path_cat(x = y)`, because both sides here are
`Grpd` classifiers. A proposed proof-time owner is:

```text
unif_rule
  OmegaEquiv_EQ1 (Path_cat $A) $x $y
  == @= $A $x $y.
```

Because the selected facade supplies a stable first-class head, a runtime
orientation from `OmegaEquiv_EQ1(Path_cat A,x,y)` to `x =_A y` may also be
probed. The RHS does not syntactically reconstruct `Obj(Path_cat A)`, so the
obvious direct loop is absent. It still requires a full owner-position
critical-pair audit.

The proof-time shaped rule passed and is required: the generic variable-`C`
comparison alone did not reconstruct the literal `Path_cat` classifier
diamond. No runtime orientation has yet passed the required package/observer
join tests.

The join resolves the two readings of:

```text
x =_{Obj(Path_cat A)} y:

  Obj(Path_cat A) -> A       gives x =_A y
  object univalence         gives OmegaEquiv(Path_cat A,x,y).
```

The general `object_path_equiv` adapter specializes here with forward arrow
`path_to_hom(Path_cat A,p)`. That is a valid reusable equivalence package, but
the selected proof-time comparison
`Core_incl_func(Path_cat A) == id` does not make this forward arrow
runtime-reduce to the raw variable `p`. Literal path categories therefore have
a stronger canonical path-equivalence witness:

```text
path_equiv_along_EQ1(p)
  : OmegaEquivAlong_EQ1(Path_cat A,p),
```

with both inverse fields explicitly `path_sym(p)` and the two cancellation-law
bodies derived by primitive path induction. Defining the entire evidence
package by one outer J from reflexivity is insufficient for arbitrary-`p`
inverse projection computation: the package remains stuck until `p` is
reflexive. The explicit-field/J-law construction passed the full probe.
Required observers on this explicit constructor include:

```text
omega_equiv_to_EQ1(path_equiv_EQ1(p))        -> p
omega_equiv_left_inv_EQ1(path_equiv_EQ1(p))  -> path_sym(p)
omega_equiv_right_inv_EQ1(path_equiv_EQ1(p)) -> path_sym(p).
```

These equations are for `path_equiv(p)`, not for an arbitrary raw `p` silently
accepted through the classifier join. Extending them to the latter is a later
extensionality/property gate, not initial path-join completion.

### G. Internal groupoidality

The leading definition is the current `IsDiscreteCat` core-equivalence field
without object-set truncation:

```text
IsGroupoidalCat(C)
  := OmegaEquivAlong_EQ1(
       Cat_cat,
       Core_cat C,
       C,
       Core_incl_func C).
```

This says that the identity-on-objects inclusion from the equality/path core
is an omega-equivalence. Under global univalence it expresses internally that
all directed arrows are recovered from object paths/equivalences. It is not
the same as zero-dimensional discreteness.

The existing boundary should refactor conceptually to:

```text
IsDiscreteCat(C)
  == Product_grpd(IsSetGrpd(Obj C), IsGroupoidalCat(C)),
```

subject to compatibility with the active exact two-field representation.

An alternative pointwise definition,

```text
Pi x y, Pi f : Hom C x y, OmegaEquivAlong_EQ1(C,f),
```

should be compared mathematically and computationally. It may characterize
all arrows as equivalences but does not immediately supply the reusable core
inclusion functor equivalence. The core-inclusion formulation is preferred
unless the pointwise form yields a materially simpler property theorem and a
proved equivalence between the two presentations.

### H. Canonical groupoidality of path categories

Current computation gives:

```text
Core_cat(Path_cat A)
  = Path_cat(Obj(Path_cat A))
  -> Path_cat A.
```

The remaining canonical comparison is:

```text
Core_incl_func(Path_cat A)
  == id Cat_cat (Path_cat A).
```

A narrowly typed proof-time rule is the conservative candidate. A runtime
fold may be selected only if its existing object and hom projections join in
both reduction orders. Once selected, canonical groupoidality is supplied by
reflexive fixed-map evidence for the identity functor:

```text
path_cat_is_groupoidal(A)
  : IsGroupoidalCat(Path_cat A).
```

The narrow proof-time identity comparison and this reflexive witness passed
the preliminary full probe with no warning delta; both selected inverse
projections compute to the identity functor. This establishes feasibility of
the canonical introduction, not yet the required nonliteral groupoidal
consumer.

This is the canonical introduction test for the new concept. The plan should
not claim `IsGroupoidalCat` usable until this witness and at least one
non-literal consumer exist.

### I. Complete the `Grpd_cat` computational boundary

The active `Grpd_cat` currently decodes its objects to `Grpd` and the objects
of its hom-categories to ordinary functions, but it does not yet identify the
whole hom-category or give a controlled identity/composition presentation.
Direct groupoid-universe equivalence should not be designed around that
missing structure.

The selected preliminary boundary is:

```text
Hom_cat(Grpd_cat,A,B) -> Path_cat(Function_grpd A B)

grpd_id_function(A) : Function_grpd A A
grpd_comp_function(g,f) : Function_grpd A C

grpd_id_function(A)(a) -> a
grpd_comp_function(g,f)(a) -> g(f(a))

id(Grpd_cat,A) == grpd_id_function(A)                 // proof time
comp_fapp0(Grpd_cat,g,f) == grpd_comp_function(g,f)  // proof time
```

The two semantic function owners should be stable heads with point-application
beta. The category-level identity and composition remain their existing
runtime forms and compare with those heads only at proof time. This matches
the general Emdash identity-normal-form policy.

Proof-sensitive laws must name these stable heads explicitly. The probe
confirmed the SOP warning that unification rules are not reliably transitive:
`id == grpd_id_function` does not make a typed consumer written directly
against a lambda discover the comparison after unfolding. The stable function
computes pointwise to that lambda, but it remains the join node in equality
endpoints and `PiFunext` constructions.

This exact division passed at owner position with no warning delta. Making
identity and composition themselves reduce broadly to lambdas added 36
critical-pair and two inferred-slot warnings through the global functoriality,
identity, and composition calculus; that orientation is rejected.

With the selected boundary, the standard comparison with contractible-fibre
equivalence is constructible rather than axiomatic:

```text
TypeEquiv(A,B) -> OmegaEquiv(Grpd_cat,A,B)
OmegaEquiv(Grpd_cat,A,B) -> TypeEquiv(A,B).
```

The forward bridge uses `type_equiv_to`, its selected inverse, `PiFunext`, and
the existing pointwise left/right paths. For the reverse bridge, the separate
left and right inverses agree pointwise:

```text
l(b) = l(f(r(b))) = r(b).
```

One then derives a right law for `l`, packages one `EquivByInverse`, and invokes
the existing `is_equiv_map_by_inverse`. Both bridges and their computational
forward-map/selected-inverse observations passed with no warning delta. No new
`grpd_univalence_by_decoder`-style capability is justified by this comparison.

This is derivation relative to the active kernel basis, not yet an entirely
closed proof: `is_equiv_map_by_inverse` is currently a bodyless theorem
capability. Its mathematics is the standard quasi-inverse-to-contractible-
fibres argument and is highly feasible, but a foundation advertised as
axiom-minimal should eventually implement that proof or explicitly retain and
classify it as theorem authority. The bridge must not be described as
assumption-free until that obligation is closed.

General package round trips remain propositional/extensionality work. The
finite `GrpdPathView := TypeEquiv` interface should remain a compatibility
view until the direct owner and these bridges are promoted.

### J. Structured motives are the MVP fibrancy boundary

An object `E : Catd(K)` is already a functor `K -> Cat_cat`. It contains the
action, identity/composition computation, iterated hom action, and coherence
required for transport. If `K` is groupoidal, functoriality sends its
invertible arrows to equivalences of fibres. No separate abstract
"transport-exists" or general fibrancy witness is needed for this structured
MVP.

If the fibres themselves must be sets, groupoids, or finite `n`-categories,
the motive should factor through an appropriate core-universe inclusion. This
is evidence about the image objects, not a second transport mechanism.

This boundary is deliberately restrictive:

- a raw function `P : Pi x, Grpd` is not automatically a `Catd` object;
- a raw path-dependent family `P(y,p)` is not automatically functorial on
  `PathOut`;
- the standard library or a later structured-former layer must construct the
  corresponding functor when needed;
- no claim is made that this solves arbitrary HIT fibrancy or all external
  cubical composition structure.

Within this boundary, however, the missing "fibrancy" problem is concrete and
syntactic: supply a functorial motive.

### K. `PathOut` is the structured groupoidal `J`

The current `path_ind_sec` is a primitive eliminator with an operational
specification, not an inert assumption. Its component rules expose action
along the canonical `rho` arrow, and its selected motive rules fold to generic
fibre transport.

For arbitrary directed `Z`, this is a directed initiality/action principle on
the outgoing-arrow category. For groupoidal `Z`, it is the structured
functorial form of identity/path induction. The proposed policy is:

1. keep primitive `ind_eqr` for arbitrary unstructured `Grpd`-valued motives;
2. use existing `path_ind_sec`/`PathInd_*` for structured motives;
3. require `IsGroupoidalCat(Z)` only when a theorem needs symmetric/invertible
   transport or comparison with primitive equality;
4. specialize to literal `Path_cat(A)` for the first comparison with
   `ind_eqr`;
5. use the core-inclusion equivalence to extend that comparison to a general
   internally groupoidal category;
6. do not introduce another general `GroupoidalJ` primitive unless a concrete
   consumer cannot be expressed as a readable alias/specialization of
   `path_ind_sec`.

For a path-dependent motive, the structured source is already:

```text
PathOut_cat(Path_cat A,x),
```

whose objects are `(y,p)` with `p : x =_A y`. A structured motive over this
category is exactly the selected pre-arranged/functorial fragment of ordinary
`J`.

### L. Shaped motive computation

When a motive is built from Product, Sigma, constant, pullback,
representable, or another known categorical constructor, its transport should
compute through the generic `fapp*`/`tapp*` owners of those constructors.

Do not add a separate former-specific `J` calculus. Add only:

- classifier joins;
- identity/reflexivity comparisons;
- constructor projection beta;
- a narrow projection-order bridge when an existing generic owner is erased
  by normalization and a measured consumer cannot reach it;
- theorem-level semantic comparisons where neither side should be a runtime
  normal form.

This policy is the structured replacement for the current broad
`ObsAction`/fibrancy expansion track.

### M. Core-universe inclusion functors

The MVP needs actual functors, not merely carrier functions, when a universe
is used as the codomain of a structured motive. The first missing inclusion
is the plain groupoid core, not a truncated package:

```text
GrpdCore_cat := Path_cat(Grpd_grpd)

GrpdCore_incl_func
  : GrpdCore_cat -> Cat_cat

GrpdCore_incl_func[A] := Path_cat(A).
```

This must be distinguished from `Grpd_cat`. The latter is the directed
category whose homs are functions and paths between functions; the former is
the groupoidal core whose arrows are groupoid/type equivalences under direct
univalence. A motive `A -> Grpd` supplied functorially factors through
`GrpdCore_cat` and then this inclusion into `Cat_cat`.

Later candidate constructions are:

```text
TruncGrpdCore_cat(n)
  := Path_cat(TruncGrpdU n)

TruncGrpdCore_incl_func(n)
  : TruncGrpdCore_cat(n) -> Cat_cat

TruncGrpdCore_incl_func(n)[X]
  := Path_cat(trunc_grpd_carrier X)
```

and:

```text
NCatCore_cat(n)
  := Path_cat(NCat n)

NCatCore_incl_func(n)
  : NCatCore_cat(n) -> Cat_cat

NCatCore_incl_func(n)[X]
  := ncat_carrier X.
```

A package of general groupoidal categories may later be introduced:

```text
GroupoidalCatData := Sigma C : Cat, IsGroupoidalCat(C)
GroupoidalCatU    : Grpd

GroupoidalCatCore_incl_func
  : Path_cat(GroupoidalCatU) -> Cat_cat.
```

The object projections remain useful as the object actions of these functors.
The functors own action on package paths/equivalences.

These are core/groupoidal inclusions, not full subcategories. A full
subcategory of `Cat_cat` would inherit all functor hom-categories between
selected carriers and would require additional evidence/path bookkeeping.
That construction is not required for groupoidal motives and is deferred.

### N. Sum and other visible formers

The current four binary-Sum equality classifier rules are mathematically
appropriate for the active disjoint inductive binary sum and should remain in
the retained H0/shaped layer:

```text
inl(a) = inl(a') -> a = a'
inr(b) = inr(b') -> b = b'
inl(a) = inr(b)  -> Empty
inr(b) = inl(a)  -> Empty.
```

This statement is not a claim about pushouts or general coproducts with
gluing, where zig-zag path phenomena require a different analysis.

The canonical proof-time reflexivity comparisons should be probed as general
former owners:

```text
eq_refl(Sum A B,inl a) == eq_refl(A,a)
eq_refl(Sum A B,inr b) == eq_refl(B,b).
```

Generic outer `eq_refl` should remain the runtime proof normal form; no
runtime proof erasure is proposed.

The current `sum_map` action bases and their four action-specific unification
bridges are not prerequisites of direct univalence or structured groupoidal
`J`. Before any retirement:

1. inventory all consumers;
2. show that structured motive/functor action or ordinary library-level
   `eq_ap` covers the intended use;
3. preserve a reviewer example if the action remains useful as a library
   theorem;
4. remove or demote only through a synchronized migration.

In particular, do not claim that structured motives already replace every
current raw `sum_map` consumer. That simplification depends on the promoted
`Grpd_cat`/`GrpdCore_cat` functor boundary and on an actual structured
presentation of the relevant map. Until then, the action example remains
valid library evidence even though it is not a foundational milestone.

The same principle applies to Nat successor action and future former-specific
registrations: preserve completed evidence, but pause expansion of the
registry until the direct univalence/structured-motive architecture is
resolved.

### O. Encoder/decoder retirement

Direct equality/equivalence comparison supports literal identity **type
views**:

```text
as_omega_equiv(p) := p
as_equality(e)    := e.
```

These bodies are valid because of proof-time classifier comparison. They do
not reify a path into the facade constructor and do not supply observer beta.
Consequently, a current encoder such as `idtoequiv_cat` must not be replaced
blindly by the identity view if a consumer expects its forward arrow, inverse,
law, or eliminator behavior. Its computational role should instead be
redefined through the transparent `object_path_equiv` package, possibly under
a clearer public name; only its opaque univalence-capability role is retired.

The same distinction applies at the groupoid universe once its direct
comparison is selected. This does not mean every current symbol should be
deleted at once. The migration should classify current APIs into five groups:

1. **retained semantic owners**: fixed-arrow equivalence, projections,
   `path_to_hom`, the defined object-path adapter, path/core action, `PathOut`,
   truncation and dimension data;
2. **identity type views**: literal `lambda x, x` facades whose only promise is
   classifier-level use;
3. **temporary compatibility wrappers**: current encoders/decoders used while
   old and new evidence coexist;
4. **derived library theorems**: contractible-fibre `TypeEquiv`, explicit
   round trips, transport squares, and comparison theorems useful to external
   HoTT-style consumers;
5. **retirable duplicate capabilities**: global assumptions and decoder
   packages whose only role is to mediate classifiers now identified directly.

`TypeEquiv` should not necessarily disappear from the library. Contractible
fibres remain a standard theorem-level formulation of equivalence for
ordinary functions. It should cease to be the primary operational universe
identity representation.

The preliminary `Grpd_cat` bridge demonstrates the intended migration:
neither direction needs a new opaque univalence capability. In particular,
the reverse bridge must visibly derive agreement of the separate inverse maps
before applying `is_equiv_map_by_inverse`; simply declaring
`OmegaEquiv -> TypeEquiv` would lose the main foundational benefit of this
redesign.

No decoder is retired until:

- every active consumer is relocated;
- the direct classifier equation is active at the required layer;
- identity views and computational adapters are named separately;
- reflexivity, general object-path, and literal path-category observers
  compute/compare at their documented boundaries;
- old-to-new and new-to-old migration examples pass;
- negative controls ensure no accidental runtime proof erasure;
- reports and examples no longer describe the decoder as foundational.

## Proposed Runtime And Proof-Time Policy

| Equation/behavior | Preferred initial owner | Reason |
| --- | --- | --- |
| `Eq(Obj C,x,y) == OmegaEquiv(C,x,y)` for variable `C` | proof-time `unif_rule` candidate | avoids selecting an infinite or overlap-heavy generic runtime normal form |
| `Eq(Obj Cat_cat,A,B) -> OmegaEquiv(Cat_cat,A,B)` | existing rigid runtime owner, re-probed with new payload | finite direct universe normal form already demonstrated |
| `Eq(Obj Grpd_cat,A,B)` versus groupoid equivalence | proof-time first; runtime candidate second | old timeout used a different transparent payload |
| `OmegaEquiv(Path_cat A,x,y) == Eq(A,x,y)` | proof-time shaped join first | resolves exact type-level diamond without forcing a runtime facade |
| same `Path_cat` join under selected facade | deferred runtime candidate | classifier orientation alone is plausible, but package/projection joins have not passed |
| `as_omega_equiv(p) := p` | transparent identity type view | exposes exactly what proof-time classifier comparison provides; promises no observer computation |
| general `object_path_equiv(p)` | transparent explicit package from `path_to_hom`, inverse path, and J laws | gives reusable observer computation without an opaque encoder |
| explicit `path_equiv(p)` observations | runtime constructor/projection beta | gives the intended path computation without collapsing every raw path into a package |
| raw path silently accepted as equivalence | type comparison only in initial MVP | direct projection rules currently create a critical pair |
| `eq_refl` versus canonical equivalence package | observer projection rules and/or narrow proof-time comparison | preserve generic proof provenance |
| `Hom_cat Grpd_cat A B` | runtime to `Path_cat(Function_grpd A B)` | exposes the missing higher path structure of functions |
| `Grpd_cat` identity/composition versus pointwise functions | stable semantic heads plus proof-time comparison | broad runtime lambda folds add 36 critical pairs |
| `Core_incl_func(Path_cat A)` versus identity functor | narrow proof-time candidate; runtime only after projection audit | canonical groupoidality introduction |
| Product identities versus component pair | proof-time comparison | preserve current identity normal-form policy |
| Sum outer/component reflexivity | two general proof-time comparisons | replace action-specific bridge proliferation |
| equality law used as recursive equivalence | identity view for typing; explicit object-path package for computation | central ownership reversal without pretending unification inserts a record |

Every unification rule is trusted proof-time authority. Lambdapi performs no
sanity check on user unification rules. Every candidate therefore needs:

- a precise semantic statement;
- a typed firing test;
- a negative non-firing test;
- a runtime non-conversion control;
- an overlap and performance inventory;
- an explicit trust classification in the plan and Foundations report.

## Current-To-Proposed Migration Map

| Current owner/interface | Proposed status |
| --- | --- |
| `OmegaEquivAlong_D0(C,f)` | replace as primary representation with equality-law fixed-map evidence; retain during migration |
| public `OmegaEquivAlong` alias | preserve public role; retarget after evidence migration |
| `omega_equiv_along_left/right_inv_D0` | preserve semantics and names without staging suffix after migration |
| `omega_equiv_along_left/right_cell_D0` | become derived compatibility views that apply the transparent general object-path adapter to equality laws when recursive observers are required |
| `omega_equiv_left/right_law` | move from decoder-derived theorem to primary evidence projection |
| public `OmegaEquiv := Sigma f, Along(f)` | migrate to selected stable dependent-pair facade; retain transparent Sigma as a propositionally equivalent library view |
| `omega_equiv_to`/`omega_equiv_evidence` transparent aliases | replace with stable facade observers and constructor/reflexivity betas |
| `CatUnivalence`/`CatUnivalenceByDecoder` | temporary compatibility types; expected foundational retirement |
| `cat_univalence`/`cat_univalence_by_decoder` | expected retirement after direct comparison and consumer migration |
| `idtoequiv_cat` | split its roles: retain/redefine the computational operation through transparent `object_path_equiv`; replace classifier-only uses by literal identity view; retire opaque capability dependencies |
| `omega_equiv_path` | identity type view where only reverse typing is required; retain a named theorem/library interface only for consumers needing explicit provenance or round trips |
| `GrpdPathView := TypeEquiv` | replace as primary universe identity with direct omega-equivalence; retain theorem-level comparison |
| incomplete `Grpd_cat` hom/identity/composition surface | add function-path hom runtime owner and stable pointwise identity/composition proof-time views before direct Grpd migration |
| groupoid `idtoequiv`/decoder capabilities | migrate like categorical decoders after direct Grpd comparison |
| `TypeEquiv`/`IsEquivMap` | retain as library concepts; promote derived bidirectional comparison; remove from primary universe normal form |
| `OmegaEquivAlongObservation_D0` and dimension views | retain as migration/debug evidence until new extensionality/property theorem; then reassess |
| `IsDiscreteCat` | conceptually factor as object-set evidence plus `IsGroupoidalCat`; preserve active compatibility |
| `Core_cat`/`Core_incl_func` | retain; add canonical `Path_cat` identity comparison |
| `path_to_hom` | retain as the forward arrow of the defined general object-path adapter; do not expect the identity type view alone to expose it |
| `path_ind_sec`/`PathInd_*` | retain as primary structured directed/groupoidal induction owner |
| general fibrancy/structured-J prerequisite track | narrow to construction of structured motives and concrete shaped projection joins |
| `ObsAction`/`ObsDAction` | preserve existing evidence; demote from direct-univalence MVP pending consumer inventory |
| Sum/Nat action bases | preserve until migration; no further foundational expansion before redesign decision |
| truncation universes, `CatDim`, `IsNCat`, `NCat` | retain; add core inclusion functors as concrete consumers require |

## Dependency Structure

```text
decoded equality-valued OmegaEquivAlong record
        |
        +--> selected stable dependent-pair facade
        |          +--> pack/projections/dependent eliminator
        |          +--> propositional eta/Sigma comparison
        |          +--> generic proof-time object-univalence candidate
        |          +--> general object-path computational adapter
        |
        +--> old/new evidence bridges
        |
        +--> general object-path adapter from Core_incl/J
        |          +--> computational recursive-cell compatibility views
        |
        +--> specialized Path_cat witness + shaped classifier join
        |          +--> Core_incl(Path_cat) == id
        |                     +--> IsGroupoidalCat(Path_cat)
        |
        +--> fixed-map evidence property/extensionality
                   +--> raw coerced-path/package joining principle
                   +--> unconditional IsNCat object truncation

Grpd_cat function-path hom boundary
        +--> TypeEquiv <-> OmegaEquiv(Grpd_cat) derived bridges
                   +--> direct Grpd universe owner
                   +--> decoder migration/retirement

stable facade + direct generic equation
        +--> retarget rigid Cat-universe runtime equality
        +--> finite/stratified semantic sanity account

IsGroupoidalCat + existing PathOut/Catd
        +--> structured groupoidal J comparison
        +--> Grpd/truncated/NCat core-universe inclusion functors

direct univalence + structured motives
        +--> simplify/demote former-specific ObsAction machinery
        +--> later reassess H2/HIT readiness
```

## Phased Implementation Plan

### Phase 0: Review, adoption, and frozen questions

Before kernel work:

1. treat the independent active-source review and preliminary probes recorded
   above as completed but non-promoted evidence;
2. obtain any additional external feedback desired on the unrestricted
   omega-level semantics and generic unification equation;
3. decide whether this report becomes the active successor, an adopted overlay,
   or a rejected experiment;
4. record the status change in `reports/INDEX.md` and the predecessor plan;
5. identify the exact current implementation slice and decide whether it is
   completed first or paused without deleting work;
6. keep all code untouched until the first owner-position candidate is ready.

Exit criterion: an explicit adoption statement. The selected first candidate
is the decoded native fixed-arrow record at the current D0 owner position.

### Phase 1: Equality-law fixed-arrow candidate

In a temporary full-file owner-position copy:

1. add `OmegaEquivAlong_EQ1` beside the current D0 owner;
2. implement it through a decoded native one-constructor record;
3. add separate left/right inverse and equality-law projections;
4. expose a reviewed indexed eliminator over the arrow index and evidence;
5. add canonical reflexive evidence and projection computation;
6. add positive and negative diagnostic assertions;
7. compare quiet, warning-enabled, subject-reduction, decision-tree, and
   strict-LHS results with baseline;
8. do not yet add first-class direct univalence or remove current D0.

Required positive observations:

- all four evidence fields on an introduced witness;
- all four reflexive observations;
- indexed eliminator constructor beta;
- next-hom equality laws have the exact intended classifier;
- a named fixed functor can carry evidence without first-class repackaging.

Required negatives:

- no evidence eta;
- no equality-proof erasure;
- no collapse of left and right inverse choices;
- no unintended recursive unfolding of an equality-law field;
- no direct comparison with current D0 without an explicit bridge.

Exit criterion: finite, warning-audited, subject-reducing equality-law
representation with explicit construction and observation.

### Phase 2: Stable-facade promotion and observer boundary

Using the Phase-1 candidate:

1. reproduce the measured failure of transparent Sigma term decoding with the
   smallest typed direct-univalence consumer;
2. add the selected stable `OmegaEquiv_EQ1` facade, pack constructor, forward
   and evidence projections, and constructor betas;
3. add the primitive dependent-pair eliminator and constructor beta;
4. derive propositional eta through the eliminator;
5. define the transparent Sigma comparison view and prove both round trips;
6. add reflexive package evidence and narrow reflexivity observers, using `_`
   for the inferred equality classifier on rule LHSs;
7. construct the general `object_path_equiv_EQ1(p)` package from
   `path_to_hom`, inverse paths, and J-derived cancellation laws, and test all
   forward/inverse/law projections;
8. under a local generic proof-time classifier comparison, test literal
   `as_omega_equiv_EQ1(p) := p` typing in both directions, runtime
   non-conversion, stuck raw observers, and the primitive-J negative control;
9. compare declaration count, warning inventory, eliminability, public
   construction, and performance with the reproduced probe baseline.

Exit criterion: the selected facade and Sigma comparison are promoted with
measured evidence, the general object-path adapter is defined rather than
assumed, identity views are not confused with computational reification, and
the new eliminator is explicitly documented as trusted record-like kernel
surface.

### Phase 3: `Path_cat` join and canonical groupoidality

1. retain the general object-path adapter and define the stronger literal
   `path_equiv_along_EQ1(p)` specialization;
2. use explicit `path_sym(p)` inverse fields and J-derived cancellation laws;
3. establish arbitrary-path and reflexive projection computation;
4. add the proof-time classifier join
   `OmegaEquiv_EQ1(Path_cat A,x,y) == Eq(A,x,y)`;
5. add forward/inverse/law observer computation for the explicit
   `path_equiv(p)` constructor;
6. retain a negative control showing a raw silently coerced path does not yet
   have package projection computation;
7. compare `Core_incl_func(Path_cat A)` with the identity functor;
8. define `IsGroupoidalCat_EQ1`;
9. construct `path_cat_is_groupoidal_EQ1(A)`;
10. add at least one nontrivial path consumer and one higher-hom observation;
11. keep runtime classifier and raw-path projection alternatives in probes
    until package/projection/eliminator reduction orders join.

Exit criterion: literal path categories satisfy internal groupoidality and
their explicit path-equivalence interface computes through named observers;
raw-coerced projection computation remains a separately recorded gate.

### Phase 4: `Grpd_cat` completion and `TypeEquiv` bridges

1. add the runtime hom-category owner
   `Hom_cat Grpd_cat A B -> Path_cat(Function_grpd A B)`;
2. add stable `grpd_id_function` and `grpd_comp_function` heads with only
   point-application runtime beta;
3. compare category identity/composition with those heads at proof time;
4. retain negative controls showing category identity/composition do not
   runtime-reduce to lambdas;
5. construct `TypeEquiv -> OmegaEquiv(Grpd_cat)` from the existing selected
   inverse and `PiFunext` laws;
6. construct the converse by proving the two inverse choices agree pointwise,
   deriving one `EquivByInverse`, and applying
   `is_equiv_map_by_inverse`;
7. test forward map, selected inverse, cancellation-law, and forward-map
   round-trip observations;
8. audit `is_equiv_map_by_inverse`: either implement its standard proof in a
   bounded follow-up or preserve an explicit theorem-capability trust label;
9. do not add a new opaque bridge or global groupoid-univalence capability;
10. compare warnings against baseline and reject broad runtime lambda folds.

Exit criterion: the whole function-path hom boundary and both explicit
equivalence representations interoperate without a warning delta or new
bridge capability beyond the selected facade/unification authority, with the
pre-existing quasi-inverse theorem obligation explicitly discharged or
classified.

### Phase 5: Old/new evidence bridges

Before migration:

1. define old-D0 to equality-law evidence using the existing decoded
   `omega_equiv_left/right_law`;
2. define equality-law to old-D0 using temporary current encoders at the two
   hom-law fields;
3. replace those temporary encoders with the defined general object-path
   adapter and verify recursive-cell observers at the next hom;
4. compare both representations on reflexivity, Product, opposite, and one
   D0b hom-action consumer;
5. state round trips propositionally where current evidence extensionality
   permits;
6. do not assume a round trip that is blocked by current opaque evidence;
7. identify every current consumer that genuinely needs recursive cells
   rather than equality laws.

Exit criterion: a migration table backed by executable examples and an honest
list of any unproved evidence-equality direction.

### Phase 6: Direct univalence equations

1. probe the generic variable-`C` proof-time equation at owner position;
2. test typed firing, non-firing, and runtime non-conversion;
3. expose the optional literal identity views in both directions and retain a
   negative showing that they do not acquire package observers;
4. enumerate overlaps with `Path_cat`, Product, Sigma, Functor, and universe
   object computation;
5. preserve the shaped `Path_cat` join;
6. re-target the existing rigid Cat-universe runtime rule to the new
   representation and test self-normalization;
7. promote Grpd-universe proof-time direct identity only over the completed
   Phase-4 hom boundary and bidirectional `TypeEquiv` comparison;
8. probe Grpd-universe runtime identity only after the proof-time candidate,
   self case, and bridge projections are understood;
9. add the selected observer matrix for packages, reflexivity, the general
   object-path adapter, and explicit literal-path constructors, retaining the
   raw identity-view negative boundary;
10. record the semantic/trust classification in Foundations and the plan;
11. state at least the finite-`NCat`/stratified approximant interpretation of
    the generic equation before describing it as foundationally correct.

Exit criterion: one selected generic comparison, selected rigid universe
owners, and no unexplained classifier equation lacking term consumers.

### Phase 7: Decoder migration and direct use

1. change new consumers to use equality directly as `OmegaEquiv` and vice
   versa;
2. migrate classifier-only consumers to literal identity views, while
   migrating observer consumers to the transparent general object-path
   adapter;
3. redefine or rename `idtoequiv_cat` as that constructed adapter rather than
   replacing its computational consumers by a stuck identity view;
4. reduce `omega_equiv_path` to an identity compatibility view where its
   explicit theorem-level provenance is not needed;
5. migrate groupoid universe consumers away from contractible-fibre identity;
6. retain explicit `TypeEquiv` comparison theorems in the library;
7. retire duplicate global decoder capability inhabitants only after consumer
   inventory reaches zero;
8. keep round-trip theorem names only where external compatibility warrants
   them;
9. update examples to demonstrate identity type views, general object-path
   reification, reflexivity projections, and specialized literal-path
   projections without claiming the unresolved raw-path projection equation.

Exit criterion: direct equality/equivalence is the primary public interface;
no foundational theorem requires an arbitrary decoder capability.

### Phase 8: Evidence extensionality/property and finite dimension

1. formulate `IsPropGrpd(OmegaEquivAlong_EQ1(C,f))`;
2. prove it first for literal path categories/groupoid functions if possible;
3. transfer the relevant first-class property/extensionality results through
   the facade/Sigma comparison rather than adding primitive facade proof
   erasure;
4. prove finite-`NCat` cases by dimension recursion using equality-valued laws;
5. compare separate-left/right evidence with current OneCat ordinary-iso
   evidence;
6. determine whether a general omega-level theorem follows from direct
   univalence and structured equality or requires an additional extensionality
   principle;
7. determine whether property/extensionality yields a safe joining theorem for
   raw path presentations and facade packages; do not implement a runtime
   collapse merely from propositional uniqueness;
8. use the theorem to discharge the current conditional `IsNCat` object
   truncation spine where justified;
9. retain an explicit blocker if the omega-level property remains unproved.

Exit criterion: property-valuedness is either proved at the claimed scope or
is an explicit bounded blocker; no global capability is smuggled in.

### Phase 9: General groupoidal categories and structured `J`

1. promote `IsGroupoidalCat` after the `Path_cat` introduction case;
2. compare core-inclusion and pointwise-all-arrows formulations;
3. define a package only when a consumer needs it;
4. specialize `path_ind_sec` to a groupoidal source and structured motive;
5. compare the literal `Path_cat(A)` specialization with primitive `ind_eqr`
   on a pre-arranged Cat-valued motive;
6. show that transport is an equivalence through the source inverse and
   functoriality;
7. add a nonliteral groupoidal category consumer;
8. do not introduce a second eliminator if an alias of `path_ind_sec` suffices.

Exit criterion: the documented groupoidal `J` story is executable and uses
existing directed action rather than a parallel transport calculus.

### Phase 10: Core-universe inclusion functors

1. begin with `GrpdCore_cat := Path_cat(Grpd_grpd)` and its actual inclusion
   functor to `Cat_cat` unless a still smaller concrete consumer is found;
2. define `GrpdCore_incl_func : GrpdCore_cat -> Cat_cat`, with object action
   `A |-> Path_cat(A)`;
3. make its object action compute to the carrier category;
4. derive arrow action from package equality/direct univalence;
5. demonstrate a structured motive factoring through it;
6. add other truncated/`NCat` core inclusions only when independently used;
7. defer full subcategories and all-functor homs.

Exit criterion: at least one groupoid-valued or finite-dimensional structured
motive uses an actual universe inclusion functor.

### Phase 11: Former-action simplification

1. inventory `ObsAction`, `ObsDAction`, Sum action, and Nat successor action
   consumers;
2. add the two general Sum reflexivity comparisons in a probe;
3. show, using the promoted `Grpd_cat`/`GrpdCore_cat` boundary and an actual
   structured map, that functor action covers the claimed foundational
   transport use case;
4. preserve useful `sum_map`/`eq_ap` statements as library examples;
5. retire or demote action-specific bases only after all diagnostics migrate;
6. pause new former registrations until a concrete structured-motive consumer
   cannot use generic action.

Exit criterion: the foundational kernel no longer carries action-specific
bridges merely to demonstrate a general observational-action framework.

### Phase 12: Consolidation and next-scope decision

1. remove staging suffixes only after old/new migration is closed;
2. synchronize kernel comments, checks, examples, Foundations, SOP, report
   index, health report, and catalog;
3. record final runtime/proof-time owners and trust classes;
4. re-evaluate H2/HIT readiness without assuming this redesign solves raw
   higher-inductive fibrancy;
5. decide whether the next work is evidence metatheory, standard-library
   construction, finite universes, or a representative HIT;
6. retain explicit consistency/normalization/universe-size deferrals.

Exit criterion: one coherent public equality/equivalence/groupoidal-J API and
no active duplicate foundation.

## Recommended First Implementation Slice

If this proposal is adopted, the first implementation task should be
`EVOGJ-ALONG-EQ-LAWS`, not decoder deletion, generic univalence, or Sum
cleanup.

The implementing agent should:

1. recover the active source/check/report state and inspect all current D0/D1
   consumers;
2. create a temporary owner-position full-file candidate immediately beside
   the current `OmegaEquivAlong_D0` owner;
3. reproduce the decoded native equality-law record with explicit
   introduction, four projections, reviewed indexed eliminator, and reflexive
   evidence;
4. add focused positive and negative assertions without changing public
   names;
5. compare warning, subject-reduction, rule-audit, performance, and decision
   tree results;
6. document whether the equality-law fields stay finite when merely typed and
   when individually observed;
7. stop before the selected outer facade or generic univalence and report the
   exact representation result;
8. promote only after the owner-position result and proportional full gates
   pass.

The first slice must not:

- delete or retarget current D0;
- add a broad unification rule;
- change public `OmegaEquiv` representation;
- promote the primitive outer facade in the same slice;
- add a decoder assumption;
- claim evidence property or extensionality;
- mix the representation experiment with Sum/ObsAction cleanup;
- reorganize the file.

This bounded slice gives the highest-value architectural evidence with the
smallest migration risk.

## Required Probe Matrix

Every architectural candidate should be evaluated against this matrix.

| Dimension | Required evidence |
| --- | --- |
| Formation | candidate classifiers and fields typecheck at owner position |
| Construction | explicit introduction and reflexive evidence are usable |
| Projection | selected fields compute on introductions/reflexivity |
| Elimination | native fixed-arrow and primitive first-class eliminators have constructor beta; facade eta/Sigma comparison are propositional |
| Fixed-map use | evidence can be attached to an already-named arrow without repackaging ambiguity |
| First-class use | package forward/evidence observers compute |
| Identity type view | `as_omega_equiv(p)` is literally `p`, typechecks only through the unifier, and acquires no unclaimed observer computation |
| General object-path adapter | forward/inverse/law observers compute through `path_to_hom`, inverse paths, and J-derived witnesses without an opaque encoder |
| Higher iteration | a law is usable at the next hom level by identity view for typing and by explicit object-path adapter for recursive observation, without a duplicated stored recursive body |
| Path-category join | classifier and explicit `path_equiv` observers agree with ordinary paths; raw-coerced projection remains a negative control |
| Facade critical pairs | package, `eq_refl`, explicit path, raw path, evidence projection, and eliminator reduction orders are tested separately |
| Generic univalence | typed direct use works while runtime non-conversion remains classified |
| Rigid universe | self-normalization terminates for the selected representation |
| `Grpd_cat` boundary | function-path homs compute; identity/composition fire only in typed proof-time tests; broad runtime lambdas remain negative |
| Equivalence comparison | both `TypeEquiv` bridge directions are derived and selected projections compute |
| Subject reduction | proof-dependent consumers retain declared result types |
| Critical pairs | both reduction orders for every shaped join are measured |
| Performance | bounded source/check times remain within SOP thresholds |
| Trust | every unification equation has a semantic statement and negative controls |
| Reusability | an example constructs and consumes equivalence without private staging symbols |
| Migration | old/new representations interoperate on a real current consumer |

## Acceptance Criteria For The Redesigned MVP

The equality-valued omega-equivalence/groupoidal-J MVP is complete only when:

1. fixed-arrow evidence has explicit left/right inverse and equality-law
   fields;
2. fixed-arrow evidence is a decoded native record with public indexed
   elimination and constructor beta;
3. the selected stable first-class facade has public construction,
   projections, dependent elimination, propositional eta, and a transparent
   Sigma comparison;
4. equality of category objects is directly comparable with first-class
   omega-equivalence at the selected runtime/proof-time boundary;
5. literal identity views across that boundary are distinguished from
   computational adapters and are not advertised as inserting casts or
   observer beta;
6. a transparent general object-path adapter is defined from `path_to_hom`,
   inverse paths, and J-derived laws, with computational forward/inverse/law
   observations and no opaque encoder capability;
7. equality laws are usable as next-hom equivalences by identity view for
   typing and explicit reification for recursive observation;
8. `Path_cat` has a coherent classifier join and explicit `path_equiv`
   term-observer computation, with raw-coerced behavior honestly classified;
9. `IsGroupoidalCat(Path_cat A)` is constructible;
10. at least one nonliteral internally groupoidal category is consumed;
11. structured groupoidal `J` is expressed through existing `PathOut` action;
12. primitive `ind_eqr` remains available for unstructured motives;
13. rigid Cat-universe direct equality remains finite under the new payload;
14. the `Grpd_cat` function-path hom boundary and proof-time pointwise
    identity/composition comparisons are active;
15. both `TypeEquiv` comparison directions are derived without a new opaque
    bridge capability, and the existing `is_equiv_map_by_inverse` theorem is
    proved or explicitly retained in the trust ledger;
16. Grpd-universe direct identity has a selected, explicitly trusted owner;
17. foundational encoder/decoder capability duplication has been migrated or
    retired;
18. `TypeEquiv` remains available as a theorem/library formulation rather than
    the primary universe identity normal form;
19. evidence property is proved at every scope claimed by truncation results;
20. old conditional `IsNCat` truncation is discharged only where the property
    theorem supports it;
21. former-specific action bases are either justified by concrete consumers
    or demoted;
22. all changed diagnostics, examples, comments, reports, catalog, health,
    warning, audit, and CI evidence are synchronized;
23. no claim of consistency, stratification, normalization, or canonicity is
    inferred from Lambdapi acceptance alone;
24. a finite-dimensional/stratified semantic sanity statement explains the
    intended approximants of the generic univalence equation;
25. an end-user example builds a small library construction using only public
    equality, equivalence, groupoidality, and structured-motive APIs.

## Feasibility Assessment

| Work item | Mathematical feasibility | Lambdapi feasibility | Current confidence |
| --- | --- | --- | --- |
| decoded equality-valued fixed-arrow record | high | demonstrated in full probe | high |
| transparent outer Sigma as direct normal form | high mathematically | fails the generic term-decoding consumer | rejected operationally |
| stable primitive dependent-pair facade | high as a Sigma presentation | demonstrated with elimination, eta, and Sigma comparison | high, with explicit trusted-eliminator cost |
| package/reflexivity observers | high | demonstrated without warning delta | high |
| literal identity type view across generic unification | high as classifier equality | demonstrated as `lambda p, p`; observers intentionally remain stuck | high for typing, none claimed for computation |
| transparent general object-path adapter | high by path/core functoriality and J | demonstrated with forward/inverse/law computation at unchanged `971/157` warnings | high |
| explicit `path_equiv` observers | high | demonstrated without warning delta | high |
| raw silently coerced path observers | high extensionally | current direct rules do not join | medium-low until extensionality design |
| `Path_cat` classifier join | high | demonstrated as proof-time equation | high |
| runtime `Path_cat` join/package collapse | high extensionally | current candidate adds critical pairs/divergence | low for present orientation |
| `Core_incl(Path_cat) == id` | high | high as narrow comparison | high |
| `IsGroupoidalCat` via core inclusion | high under global univalence | high | high |
| structured groupoidal `J` via `PathOut` | high | most machinery already active | high |
| generic variable-`C` univalence | plausible/intentional | demonstrated operationally; remains trusted semantic authority | medium-high operational, medium foundational |
| rigid Cat direct identity | already operational | stable-facade retarget demonstrated finite | high |
| `Grpd_cat` function-path hom boundary | high | demonstrated; broad runtime alternative rejected | high |
| `TypeEquiv <-> OmegaEquiv(Grpd_cat)` | standard mathematics | both directions demonstrated relative to bodyless `is_equiv_map_by_inverse`; closing that proof is medium-high | high architecture, medium-high proof completeness |
| redesigned Grpd direct identity | high | proof-time boundary now high; rigid runtime still to probe fully | medium-high |
| evidence property for groupoids/finite levels | high | medium | medium-high |
| evidence property for unrestricted omega level | plausible | may need extensionality principle | medium-low |
| unconditional finite-`NCat` object truncation | high after property theorem | medium | medium |
| core-universe inclusion functors | high | medium-high | high |
| full subcategories of `Cat_cat` | high but unnecessary for MVP | medium/large scope | deferred |
| decoder retirement | high after migration | medium due consumer breadth | medium-high |
| Sum/action simplification | high | high after inventory | high |
| normalization/model/self-universe metatheory | research | outside bounded MVP | deferred |

## Principal Risks And Mitigations

### Risk 1: a broad unification equation silently asserts too much

Mitigation: classify it as trusted logical authority; require typed firing,
negative firing, runtime non-conversion, semantic explanation, and shaped
consumer tests. Prefer rigid runtime rules and narrow joins where feasible.

### Risk 2: generic runtime object univalence overlaps every reducible `Obj`

Mitigation: begin with a generic proof-time equation; enumerate `Path_cat`,
Product, Sigma, Functor, and universe diamonds; add shaped joins only for real
consumers; do not assume one `Path_cat` join solves the whole system.

### Risk 3: the new stable evidence is still merely opaque

Mitigation: fixed-arrow evidence is a decoded native record with generated
induction, reviewed projections, and explicit construction. The stable outer
facade must expose its primitive eliminator, derived eta, and Sigma comparison.
An abstract classifier head is an operational boundary, not permission to
omit introduction or elimination semantics.

### Risk 4: the selected primitive facade adds unjustified trusted surface

Mitigation: record the measured transparent-Sigma failure, keep only one
primitive constructor/projection/eliminator family, derive eta rather than
making it a runtime rule, and maintain explicit propositionally inverse Sigma
views. Do not grow a second parallel algebra over the facade.

### Risk 5: fixed-arrow evidence is not proposition-valued

Mitigation: use separate left/right inverse data; prove property first at
groupoid and finite levels; do not unblock truncation through an assumed
global capability.

### Risk 6: groupoidality is conflated with discreteness

Mitigation: define `IsGroupoidalCat` independently; make `IsDiscreteCat` the
additional set-object specialization; add non-discrete groupoidal examples.

### Risk 7: structured motives are claimed to solve arbitrary fibrancy

Mitigation: state the restriction explicitly. `Catd` solves transport and
coherence only for motives supplied as functors. Raw families and HITs remain
separate.

### Risk 8: decoder retirement breaks useful theorem-level APIs

Mitigation: distinguish foundational mediators from library comparisons.
Retain `TypeEquiv`, contractible-fibre theorems, and explicit round trips where
users need them; retire only duplicate capabilities.

### Risk 9: identity/proof provenance is erased

Mitigation: preserve generic `eq_refl` and generic `id` runtime forms; use
observers and narrow proof-time comparisons; retain negative runtime controls.

### Risk 10: the redesign expands into a new giant parallel layer

Mitigation: use `_EQ1` only in probes; promote one owner at a time; migrate and
delete compatibility code before beginning unrelated new former/HIT work.

### Risk 11: raw paths and explicit packages are collapsed unsafely

Mitigation: keep the shaped classifier join proof-time, compute observers on
the transparent general `object_path_equiv(p)` package and the stronger
literal `path_equiv(p)` specialization, retain a negative showing that the
identity view `as_omega_equiv(p) := p` acquires no observer beta, and reject
the measured package-collapse/runtime-projection rules until a genuine joining
theorem and all eliminator critical pairs pass.

### Risk 12: operational acceptance is mistaken for semantic univalence

Mitigation: state that the generic `unif_rule` is trusted logical authority,
give finite-dimensional/stratified approximants of the recursive equation,
and separate that sanity account from later full consistency, normalization,
and model research.

## External/Independent Review Questions

The final review resolves the operational representation questions but leaves
the following mathematical and migration questions explicitly scoped:

| Question | Review status |
| --- | --- |
| Equality-valued bi-invertibility as primary fixed-arrow structure | accepted for the MVP; unrestricted omega semantics still needs the stated greatest-fixed-point/approximant account |
| Property-valuedness of separate-left/right evidence | standard and derivable for groupoid functions; finite and unrestricted omega proofs remain implementation/metatheory tasks |
| `IsGroupoidalCat(C) := EquivAlong(Core_incl_func C)` | accepted as leading reusable definition; pointwise all-arrows form should be a comparison theorem |
| Transparent Sigma versus stable facade | resolved in favor of the stable facade by the term-decoding probe; Sigma retained as comparison view |
| Generic object univalence owner | proof-time generic rule selected provisionally, with rigid runtime universe owners and shaped proof-time joins |
| Type view versus computational adaptation | literal identity view selected for classifier-only use; transparent `object_path_equiv` package selected for general observations; no opaque encoder required |
| Direct Grpd-universe representation | complete `Grpd_cat` and use omega-equivalence; proof-time owner first; rigid runtime orientation remains open |
| Minimal path observer interface | explicit `path_equiv(p)` computes; raw silently coerced projections are deferred |
| `Core_incl_func(Path_cat A)` orientation | proof-time comparison selected; runtime fold unnecessary for the MVP |
| `PathOut` sufficiency | highly plausible and already computational for structured motives; still needs the planned literal and nonliteral groupoidal consumers |
| Decoder APIs worth retaining | `TypeEquiv` and theorem-level round trips are clearly useful; exact current symbol inventory remains migration work |
| Remaining `ObsAction` scope | unresolved pending promoted structured `Grpd` motive consumer; not a blocker to direct univalence |
| Semantic sanity vehicle | finite `NCat`/dimension-indexed approximants are the preferred local explanation; external systems remain inspiration, not implementation templates |

Additional external mathematical review is most valuable for only three
points: unrestricted omega evidence property/extensionality, the semantic
status of the broad object-univalence unifier, and whether a concrete
nonliteral groupoidal `PathOut` consumer exposes a missing naturality law.

## Side-Task Ledger

All kernel-promotion rows remain proposed/unstarted until adoption. A
"preliminary probe passed" result records review evidence only, not active
implementation. Completed predecessor work is recorded in the July 13 ledger
and should not be duplicated here.

| Task ID | Initial status | Purpose | Dependency | Status-changing result |
| --- | --- | --- | --- | --- |
| `EVOGJ-ARCH-REVIEW` | review complete; adoption pending | independent review and adoption decision | this report | probe-refined plan; explicit adopt/reject still required |
| `EVOGJ-ALONG-EQ-LAWS` | proposed first implementation slice; preliminary probe passed | decoded equality-valued fixed-arrow representation | adoption | reproduce, promote, and pass permanent proportional gates |
| `EVOGJ-PACKAGING-FORK` | decision selected; promotion blocked on first slice | promote stable facade and Sigma comparison | equality-law candidate | preliminary facade/elimination/round-trip probe passed |
| `EVOGJ-STABLE-OBSERVERS` | partially probed; blocked on packaging promotion | package/reflexivity/explicit-path observations | packaging candidate | package/reflexivity passed; raw coerced path remains deferred |
| `EVOGJ-OBJECT-PATH-ADAPTER` | preliminary probe passed; blocked on packaging promotion | separate literal identity type view from transparent computational reification through `path_to_hom` and J | stable facade and equality-law evidence | reproduce general adapter, forward plus four evidence observations, identity-view negative, and warning-neutral result |
| `EVOGJ-PATH-CAT-JOIN` | preliminary proof-time probe passed; blocked on owners | identify path-category equivalence with path equality | equality-law package | reproduce typed join and explicit constructor computation |
| `EVOGJ-PATH-CAT-GROUPOIDAL` | preliminary probe passed; blocked on join promotion | prove `IsGroupoidalCat(Path_cat A)` | path join/core identity | canonical witness passed; nonliteral consumer remains |
| `EVOGJ-OLD-NEW-BRIDGE` | blocked on equality-law candidate | migrate current D0 evidence | candidate plus current decoder | executable bridges and honest round-trip status |
| `EVOGJ-GRPD-CAT-BOUNDARY` | preliminary probe passed; blocked on adoption/owners | complete function-path hom and pointwise identity/composition interface | selected facade | reproduce and promote warning-neutral boundary |
| `EVOGJ-TYPEEQUIV-BRIDGE` | preliminary bidirectional probe passed; blocked on Grpd boundary | derive `TypeEquiv <-> OmegaEquiv(Grpd_cat)` | Grpd boundary and fixed-arrow evidence | promote derived bridges and projection diagnostics |
| `EVOGJ-QINV-FIBRE-PROOF` | dependency audit required | close or explicitly classify bodyless `is_equiv_map_by_inverse` | active H0 path/Sigma machinery | implemented proof or retained trust-ledger entry |
| `EVOGJ-DIRECT-UNIV-GENERIC` | preliminary operational probe passed; blocked on path join | generic object equality/equivalence comparison | stable package and joins | selected trusted owner plus semantic approximant account |
| `EVOGJ-DIRECT-UNIV-CAT` | preliminary retarget probe passed; blocked on candidate | retarget rigid Cat direct rule | equality-law package | reproduce finite self-normalization and observer checks |
| `EVOGJ-DIRECT-UNIV-GRPD` | blocked on Grpd boundary promotion | replace finite TypeEquiv view as primary identity | stable package and derived bridges | selected proof-time/runtime owner |
| `EVOGJ-DECODER-MIGRATE` | blocked on direct equations | remove foundational decoder dependency | direct universe and generic owners | zero foundational decoder consumers |
| `EVOGJ-EVIDENCE-PROP` | blocked on representation | prove fixed-map evidence property | equality-law evidence | scoped theorem or blocker |
| `EVOGJ-NCAT-TRUNC` | blocked on property | discharge conditional object truncation | evidence property | unconditional theorem at justified scope |
| `EVOGJ-GROUPOIDAL-CAT` | blocked on path witness | general internal groupoidality | path-category introduction | nonliteral consumer |
| `EVOGJ-GROUP-J` | blocked on groupoidality | structured groupoidal `J` comparison | groupoidal category and PathOut | executable comparison with primitive J |
| `EVOGJ-UNIVERSE-CORE-INCL` | blocked on direct equality/groupoidality | actual package-core functor into `Cat_cat` | selected concrete motive | one used inclusion functor |
| `EVOGJ-SUM-SIMPLIFY` | blocked on direct/structured architecture | replace action-specific bases with general reflexivity joins/library action | consumer inventory | synchronized migration |
| `EVOGJ-OBSACTION-SCOPE` | blocked on structured motive evidence | decide remaining role of action registry | groupoidal J and former consumers | retain/demote decision |
| `EVOGJ-H2-READINESS` | deferred | reassess representative HIT/truncation reflector | consolidated MVP | new bounded plan or continued deferral |
| `EVOGJ-METATHEORY` | deferred research | consistency, normalization, stratification, semantic model | mature architecture | separate research evidence |

## Validation And Synchronization Protocol

Implementation must follow `AGENTS.md` and the current SOP. In particular:

- inspect staged and unstaged changes separately on every continuation;
- relocate symbols with `rg`; never rely on the line numbers in this report;
- probe nontrivial rewrite/unification changes in temporary owner-position
  full-file copies;
- preserve inferred slots unless a measured audit justifies change;
- keep checks bounded to the repository timeout policy;
- classify `unif_rule` as proof-time authority, never runtime computation;
- validate unification-rule firing with typed equality and retain conversion
  negatives;
- for every classifier boundary, test identity-view typing separately from
  explicit adapter/constructor observations; never infer term reification or
  observer beta from successful unification;
- test both reduction orders for every shaped join;
- compare warning inventories rather than using raw counts as a semantic veto;
- add focused positive and negative checks for every promoted owner;
- run `make check` for inner-loop promotion, `make examples` for reviewer
  milestones, catalog/health/warning/audit gates after architectural changes,
  and `make ci` before substantive handoff;
- update this ledger, the active master plan status, Foundations, SOP, examples,
  catalog, and health report whenever a conclusion changes;
- do not combine semantic migration with file splitting or unrelated cleanup.

## Completion And Blocker Policy

This proposal is complete as a design document when its review questions,
phases, migration map, trust boundaries, and first slice are explicit. That
does not mean its implementation is complete.

The implemented redesign is complete only when the MVP acceptance criteria
are met and old/new duplicate foundations have been reconciled. A difficult
or slow proof is not a blocker. A blocker must name:

- the exact desired term/rule/theorem;
- the smallest failing owner-position probe;
- whether failure is typing, subject reduction, nontermination, overlap,
  performance, representation, or missing mathematics;
- the prerequisite that would change the result;
- any independent dependency-ready work that remains.

Deferred metatheory is not a blocker to the bounded operational MVP unless a
claim of consistency, normalization, stratification, or canonicity becomes a
required deliverable.

## Future Implementation Handoff Requirements

After the next review/refinement turn, the implementation handoff prompt
should instruct a new coding agent to:

- read this proposal together with the July 13 master plan and active
  authorities;
- treat the new report as the selected re-redesign overlay only if its status
  has been changed to adopted;
- implement rather than merely review;
- begin with the dependency-ready ledger row, normally
  `EVOGJ-ALONG-EQ-LAWS`;
- preserve all committed work and use commit `7724110...` only as review
  provenance;
- keep source, checks, examples, reports, catalog, health, warnings, audit, and
  CI evidence synchronized;
- revise the plan when owner-position evidence invalidates a decision;
- continue safe plan-scoped work until completion or a documented hard
  blocker, without using that persistence instruction to broaden scope.

The exact `/goal` handoff text should be generated only after the next review
has resolved the plan's initial adoption status and any externally identified
corrections.
