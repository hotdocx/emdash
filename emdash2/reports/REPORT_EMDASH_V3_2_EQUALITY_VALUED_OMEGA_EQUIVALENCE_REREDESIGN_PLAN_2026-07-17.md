# EMDASH v3.2 Equality-Valued Omega-Equivalence And Groupoidal-J Re-Redesign Proposal

Date: 2026-07-17
Last reviewed: 2026-07-18
Plan-ID: EMDASH-V3-2-EQUALITY-VALUED-OMEGA-EQUIVALENCE-REREDESIGN-2026-07-17
Depends-On: REPORT_EMDASH_V3_2_OBSERVATIONAL_EQUALITY_TRUNCATION_UNIVALENCE_REDESIGN_PLAN_2026-07-13; REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26; EMDASH_FOUNDATIONS; emdash3_2.lp; emdash3_2_eq1_hom_action.lp; emdash3_2_eq1_evidence_property.lp; emdash3_2_sum_observational_action.lp; emdash3_2_checks.lp
Supersedes: the equality, omega-equivalence, direct-univalence, internal-groupoidality, and structured-PathOut/J tracks of REPORT_EMDASH_V3_2_OBSERVATIONAL_EQUALITY_TRUNCATION_UNIVALENCE_REDESIGN_PLAN_2026-07-13; no unaffected H0, truncation, dimension, directed, or former-action work
Side-Task-Ledger: #side-task-ledger
Infinity-Codex-Origin: current-session-independent-review-and-user-clarification-2026-07-17
Infinity-Codex-Decision-Responses: infinity-codex:019f6bd3-8405-7d31-8ced-8a6b127c1499:019f6e16-d397-7a60-9765-1f35e36e20f7; infinity-codex:019f6bd3-8405-7d31-8ced-8a6b127c1499:019f6e5a-9a89-7d01-a92f-f4d15f14c77e; infinity-codex:019f6bd3-8405-7d31-8ced-8a6b127c1499:019f6e9e-4c44-7e61-9320-bfc602b50d64
Status: **completed 2026-07-17 at the selected operational MVP boundary**; Phases 1 through 9, 11, and 12 are complete at their stated selected boundaries, while Phase 10 is deliberately deferred until a concrete core-universe motive consumer exists; the native EQ1 foundation, groupoidality/structured-`J` chain, unrestricted evidence-property theorem, and unconditional finite-`NCat` object-truncation theorem are decoder-free, while legacy D0/Cat/Grpd decoder APIs remain explicit compatibility/library surface rather than a second active foundation
Review baseline: `772411011ac721c84d143a2967f4e5c31e94bc70`
Implementation starting baseline: `4315137094d2faf4fcc6f4b026960a62bd5406e7`
Primary predecessor: `REPORT_EMDASH_V3_2_OBSERVATIONAL_EQUALITY_TRUNCATION_UNIVALENCE_REDESIGN_PLAN_2026-07-13.md`
Proposed implementation entry point: [Recommended First Implementation Slice](#recommended-first-implementation-slice)
Preliminary feasibility evidence: ignored owner-position full-file probes under
`tmp/probes/evogj_*_full.lp`; Phases 1 through 5 and the selected Phase-6
abstract/Cat/Grpd boundary, stable Product slice, uniform explicit-cast view,
general-groupoidality/explicit-arrow-equivalence slices, literal
structured-action/J comparison, and equivalence-valued displayed transport
have now been reproduced and promoted at their active owners. The generic
half-adjoint coherence prerequisite and the complete native next-hom package
are promoted; the latter lives in a one-way derived extension with protected
transparent implementation lemmas and one ordinary public hom-action owner.

## Status And Authority

This document is the adopted re-redesign overlay for the equality,
omega-equivalence, univalence, groupoidality, and structured path-induction
parts of the July 13 living master plan. It exists beside that plan so that
the current implementation and its synchronized evidence remain available for
comparison while this simpler architecture is implemented, probed, and
corrected.

The explicit user handoff on 2026-07-17 adopts this overlay. Authority is now:

1. `emdash3_2.lp` remains the active kernel authority;
2. `emdash3_2_eq1_hom_action.lp` is the one-way derived authority for native
   EQ1 next-hom preservation and its groupoidality/structured-transport
   consumers; it imports the kernel, never conversely;
3. `emdash3_2_eq1_evidence_property.lp` is the downstream transparent
   authority for native-EQ1 evidence property, truncation under retractions,
   and unconditional finite-`NCat` object truncation;
4. `emdash3_2_sum_observational_action.lp` is the downstream library authority
   for the optional former-specific Sum observational action;
5. `emdash3_2_checks.lp` remains the executable diagnostic authority;
6. the current SOP and Foundations report retain their ordinary authority;
7. this report is the living implementation plan and decision ledger for its
   named equality/equivalence/groupoidality tracks;
8. the July 13 plan remains the retained promoted-work ledger and the active
   plan for unaffected H0, truncation, dimension, directed, and former-action
   tracks.

This overlay supersedes the July 13 plan only for the specific architecture
tracks named below. The July 13 plan remains a
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
5. distinguish abstract proof-time classifier interchange, explicit
   identity-body casts staged through the uniform stable
   `ObjectPathCastView_EQ1`, and the decoder-free object-path package whose
   forward/inverse/law observers compute; the original unrestricted
   `lambda p, p` experiment remains rejected, while the stable carrier view
   makes its typed-let replacements specialization-safe without an opaque term
   operation;
6. add the shaped `Path_cat` join and a computational explicit path-equivalence
   constructor, while deferring raw-coerced-path projection computation until
   its package/extensionality critical pair has a sound solution;
7. define general internal groupoidality by equivalence of `Core_cat(C)` with
   `C`, use the existing `PathOut`/directed-family action as the structured
   groupoidal form of `J`, derive its exact literal-`Path_cat` comparison with
   primitive `ind_eqr`, and prove that displayed action along a groupoidal
   arrow carries explicit EQ1 equivalence evidence without introducing a
   second eliminator or decoder;
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

At the review baseline this proposal was not yet implemented. The active
source still retains the D0 certificate, public transparent Sigma package,
and decoder capabilities for compatibility, but Phases 1 through 5 and the
selected abstract, rigid-universe, stable-Product, and explicit-opposite parts
of Phase 6 are now promoted alongside them. Phase 7 generalized the
successful opposite staging pattern into one uniform carrier view, retired the
opposite-only intermediary, and closed native foundational decoder migration
while retaining consumer-owned compatibility APIs. Phase 9 now
consumes general internal groupoidality homwise, supplies discrete and
packaged-zero-category nonliteral witnesses, retains the existing
`path_ind_sec` computation as the structured-action owner, proves at a
literal `Path_cat(A)` source that the structured displayed action and the
existing section application agree propositionally with primitive `ind_eqr`,
and constructs explicit native equivalence evidence for each groupoidal arrow
and its displayed fibre transport. Generic equality-valued
half-adjointification is now an active transparent theorem. The complete
D0b-free next-hom package is promoted as
`omega_equiv_along_fapp1_EQ1` in the one-way derived module
`emdash3_2_eq1_hom_action.lp`. Its proof-engineering dependencies are
protected transparent symbols: the proof core exposes one ordinary public
hom-action owner, package projections compute, and reflexive input normalizes
to the identity hom functor. The groupoidality/structured-transport layer was
relocated to that extension and now consumes the native owner rather than the
former EQ1-to-D0/D0b/D0-to-EQ1 route.
The formerly bodyless `is_equiv_map_by_inverse` theorem is now proved
transparently in the kernel by left-oriented path induction and the generic
half-adjoint triangle, with its historical selected fibre centre preserved by
transparent re-centring rather than a rewrite. A second one-way module,
`emdash3_2_eq1_evidence_property.lp`, proves that native fixed-arrow evidence
is proposition-valued for every category: composition with the forward arrow
is an explicit equivalence on both inverse-candidate hom classifiers, so the
two-fibre record view is contractible. Arbitrary truncation is also closed
under explicit retractions, and transparent `CatDim` recursion now proves
unconditional `IsNCat(n,C) -> IsObjTruncCat(cat_dim_trunc_level(n),C)` through
the native EQ1 Sigma/facade/cast chain. No axiom, decoder, rewrite, unifier, or
proof erasure is used by this Phase-8 result.
The results below began as
owner-position feasibility evidence; the phase records distinguish what has
since become active from what remains preliminary. Neither successful probes
nor promotion establish consistency, normalization, confluence, canonicity,
universe stratification, or a semantic model.

Peer-review recommendation, now adopted: use this revised report as the
implementation overlay for the named equality/univalence/groupoidality
tracks. Do not declare the July 13 implementation complete
or delete it wholesale; migrate its retained H0, truncation, dimension, and
directed assets phase by phase. The proposed core is now sufficiently coherent
and computationally feasible to implement. The principled raw-path/package
observer join and semantic fixed-point assurance remain explicit
research/extension gates; unrestricted native evidence property and
finite-dimensional object truncation are no longer open. The selected
operational MVP is implemented and validated rather than merely feasible.

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
5. the abstract proof-time comparison is valid, but an unrestricted reducible
   `as_omega_equiv(p) := p` alias is not specialization-stable. The selected
   repair is a uniform rigid `ObjectPathCastView_EQ1`: equality enters through
   carrier reduction, EQ1 enters through one direct proof-time comparison, and
   both typed-let casts beta-reduce to their input. Product retains its stable
   path classifier; the earlier opposite-only intermediary is superseded.
   Observer computation still belongs to the explicit object-path package
   built from `path_to_hom`, inverse paths, and J-derived laws.

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
| abstract identity-body view `as_omega_equiv(p) := p` plus explicit general object-path package | passes while `C` remains abstract; package forward/inverse/law projections compute through `path_to_hom` and J; no warning delta | preliminary separation is valid only at the abstract owner; concrete specialization required the later Phase-6 audit |
| shaped `Path_cat` classifier join | passes; no warning delta | an explicit shaped join is required in addition to the generic comparison |
| explicit `path_equiv(p)` with `path_sym(p)` inverses and J-derived laws | passes; all named observers compute; no warning delta | computational path constructor is feasible |
| raw path projection rule `omega_equiv_to(p) -> p` | adds an unjoinable package/path critical pair | do not claim raw coerced-path projection computation yet |
| package collapse in the literal path case | adds further critical pairs and divergence with evidence/elimination | reject this runtime shortcut |
| `Core_incl_func(Path_cat A) == id` plus canonical path-category groupoidality | passes; no warning delta | canonical introduction of `IsGroupoidalCat` is feasible |
| general `IsGroupoidalCat_EQ1(C)` consumed through native `omega_equiv_along_fapp1_EQ1` | the coherent core-inclusion witness yields iterable fixed-arrow EQ1 evidence for every `core_incl_hom_func`; its selected right inverse maps arrows to object paths, its right law gives pointwise re-inclusion, and discrete/`ZeroCat` carriers supply nonliteral witnesses; no D0/D0b conversion, rule, unifier, decoder, or eliminator | promoted in the one-way derived extension; the former compatibility-backed consumer definitions were relocated out of the kernel and migrated without changing their public names |
| compatibility-derived arrow-to-path selection specialized to literal `Path_cat(A)` | formation passes, but the selected inverse does not definitionally reduce to the input path | retain this as a provenance negative; `path_equiv_EQ1(p)` remains the direct literal computational owner, so the failure is not a groupoidality blocker |
| literal `Path_cat(A)` displayed action, existing `path_ind_sec` application, and primitive `ind_eqr` | two narrow proof-time joins plus derived `ind_eqr` proofs establish both comparisons; primitive J computes at reflexivity while the structured presentations deliberately retain their directed runtime normal forms; quiet/warning probes pass at unchanged `971/157`, and the strict audit remains zero/45/27 | exact structured-J comparison is feasible and promoted without a second eliminator, decoder, encoder, or runtime commuting conversion |
| native EQ1 evidence for groupoidal arrows and displayed transport | ordinary functor action maps separate inverses and both equality laws; the natively selected path, its reversal, re-inclusion, `eq_ap`, and J-derived path laws construct evidence for every arrow; applying the generic theorem to `D : C -> Cat_cat` makes `fapp1_fapp0(D,f)` an equivalence of fibres; explicit inverse projections compute | Phase-9 equivalence-valued transport is promoted transparently with no opaque encoder/decoder, transport axiom, rewrite, unifier, or remaining D0b dependency in this consumer chain |
| generic equality-valued half-adjointification | path cancellation, homotopy naturality, the adjusted counit, and its triangle are derived transparently from `ind_eqr`, `eq_ap`, and path composition; arbitrary formation and reflexive counit/triangle computation pass after active-owner promotion | the former coherence prerequisite needs neither an opaque theorem nor a rewrite/unifier; focused active probe `evogj_half_adjoint_active-20260717-162534.log` |
| transparent quasi-inverse-to-contractible-fibre theorem | left-oriented J and the half-adjoint triangle construct every dependent fibre path; transparent re-centring preserves the former selected inverse/right-law centre, and both active-kernel and compatibility probes pass | closes the bodyless `is_equiv_map_by_inverse` trust boundary and removes its selected-centre rewrite; focused probes `evogj_qinv_fibre_transparent-20260717-182615.log`, `...-182714.log`, active kernel `emdash3_2-20260717-182800.log` |
| unrestricted native-EQ1 fixed-arrow evidence property | each inverse-and-law view is a homotopy fibre of composition with the forward arrow; explicit inverse composition maps and the transparent fibre theorem contract both views, while record eta contracts the native record | dimension-free proposition-valuedness is proved without local truncation, extensionality axiom, decoder, rewrite, unifier, or proof erasure; probes `evogj_general_evidence_prop-20260717-183317.log`, active module `emdash3_2_eq1_evidence_property-20260717-183438.log` |
| arbitrary truncation under retractions and finite-`NCat` object truncation | transparent `TruncLevel` induction proves retract closure; transparent `CatDim` induction combines hom recursion, Sigma truncation, evidence property, stable-facade retraction, and equality cast retraction; base and successor equations pass | unconditional native theorem `ncat_obj_trunc_EQ1` is feasible and promoted downstream; legacy D0 conditional theorem remains compatibility-only (`evogj_trunc_retract-20260717-183522.log`, `evogj_ncat_obj_trunc-20260717-183651.log`, active module `...-183710.log`) |
| D0b-free EQ1 next-hom reconstruction and derived-module extraction | all equality-path transformations, their components, both endpoint-correct inverse hom functors, both cancellation laws, and the final native package pass without D0/D0b; the extracted 2,400-line proof core uses 56 protected transparent helpers and one ordinary public owner; an external consumer sees the package, both inverse projections compute, and reflexive input normalizes to `id_func` | promoted as `emdash3_2_eq1_hom_action.lp`; the architecture needs neither an opaque next-hom capability nor a new rewrite/unifier, and the 5,600-line exploratory staging file was not imported (`160720`, `160813`, `162016`, `162055`, extracted-module `171214`, external consumer `171420`, active module `emdash3_2_eq1_hom_action-20260717-173254.log`, reviewer `equality_valued_omega_equivalence_hom_action-20260717-173305.log`) |
| direct one-`J` hom-action shortcut through a cast category path | the transparent path-to-facade cast typechecks, but `omega_equiv_to_EQ1` remains stuck on the unreified path even at primitive `eq_refl`; explicit `object_path_equiv_EQ1` instead computes its forward arrow to `path_to_hom` | classifier interchange alone cannot supply a computational hom package or make `J` reduce on a facade package; retain explicit reification/derived hom-action evidence rather than adding an opaque decoder (`evogj_direct_j_hom_action-20260717-163212.log`) |
| extracted public owner over hidden transparent helpers | Lambdapi rejects a public transparent definition whose generated definition rule retains `private` helper symbols; the same minimal pattern passes with `protected` helpers, and the full extracted module plus external consumer then pass | module-interface restriction, not an opacity or architecture blocker: keep proof helpers protected and the semantic constructor public (`evogj_protected_transparent_helper-20260717-171150.log`, extracted-module `171214`, consumer `171420`) |
| retargeted rigid Cat-universe equality to stable facade | passes and self-normalizes finitely; no warning delta | Cat direct identity is high-confidence operationally |
| broad runtime `Grpd_cat` identity/composition as lambdas | passes quietly but adds 36 critical-pair and 2 replaceable-pattern warnings | reject broad runtime folds |
| `Hom_cat Grpd_cat A B -> Path_cat(Function_grpd A B)` plus stable function owners and proof-time identity/composition comparisons | passes; no warning delta | selected `Grpd_cat` completion boundary |
| `TypeEquiv -> OmegaEquiv(Grpd_cat)` | passes; forward, inverse, and law projections compute; no warning delta | no decoder axiom is needed in this direction |
| `OmegaEquiv(Grpd_cat) -> TypeEquiv` through internally derived quasi-inverse and transparent `is_equiv_map_by_inverse` | passes; forward map, selected inverse, right law, forward-map round trip, and the underlying contractible fibres are transparently proved | no decoder or bridge capability remains in this direction |
| abstract `OmegaEquiv_EQ1(C,x,y) == Eq(Obj C,x,y)` with typed firing/non-firing controls | passes at current owner; `Path_cat`, Sigma, Functor, Cat, and Grpd cases are covered; unchanged `971/157` | promoted as proof-time authority, not runtime conversion |
| reducible identity-body alias specialized to `Product_cat` | the application is accepted by its declared signature, but unfolding it to `p` produces terms whose Product-Sigma-path and EQ1 types are not unifiable | do not promote the alias as a generally safe cast; explicit `object_path_equiv_EQ1` remains subject-reduction-safe |
| generic runtime rule `Eq(Obj C,x,y) -> OmegaEquiv_EQ1(C,x,y)` | rejected during owner checking: existing observational equality instances make the generic LHS interaction ill typed | generic runtime tautology is not feasible in the present `Obj`/former normal forms; use rigid owners plus proof-time comparison |
| rigid Cat and Grpd runtime equality retargeted to EQ1 | both pass, Cat self-normalizes finitely, old Cat/Grpd views remain explicit compatibility surfaces, warnings stay `971/157` | promoted direct universe owners; no decoder is needed for their classifier normal forms |

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
| generic runtime object-univalence rule `Eq(Obj C,x,y) -> OmegaEquiv_EQ1(C,x,y)` | the full owner candidate is rejected before diagnostics: matching existing Sum/PathRecord/Sigma observational normal forms leaves an ill-typed generic LHS instance | **generic runtime orientation rejected, not a universe blocker**; the two rigid Cat/Grpd runtime rules and the abstract proof-time rule pass independently (`073039` rejected; `073213`/`073227` pass) |
| promote the abstract `lambda p, p` typing view as a general transparent cast | abstract use passes, but after specializing to `Product_cat` the application has the advertised EQ1 type while its unfolded body is the already-decoded Sigma-path term; a cross-type conversion assertion fails | **transparent general cast rejected on specialization stability**; use `object_path_equiv_EQ1(p)` for safe path-to-package computation. A reverse or zero-cost cast requires a stable former path-view design or an explicitly primitive nonreducing interface (`072841`) |
| Product-shaped comparison against transparent `SigmaPathView`, its unfolded Sigma classifier, or decoded tau-Sigma | all three variants fail to fire after Product equality decoding; even a deliberately broad isolated Product/Sigma unifier does not repair term typing | **transparent shaped-unifier orientation rejected**; this normal-form result led to the subsequently selected rigid `ProductPathView`, not to a primitive cast (`072001`, `072024`, `072118`, `072504`, `072533`, `072608`, `072629`) |
| stable `ProductPathView`, carrier decoding to the existing constant-family `SigmaPathView`, native introduction/projections/elimination, and `Obj(Product_cat)` retargeted through `Product_grpd` | quiet and warning-enabled owner-position probes pass; carrier adapters and both local equality/EQ1 casts have literal identity bodies and definitional round trips; generic and canonical Product reflexivity retain distinct provenance; warning/audit inventories stay `971/157` and zero/45/27 | **selected and promoted**; this closes the Product normal-form gate without a primitive cast or a global Sigma migration (`093358`, `093427`, `094338`, `094347`) |
| direct `OmegaEquiv_EQ1(Op C) == Eq(Obj C)` shaped unifier | abstract opposite use passes, but `Op(Product)` and `Op(Path_cat)` specializations trigger ill-sorted unification search when the opposite-first and inner-former-first routes compete | **direct reduced-classifier orientation rejected**, not an opposite-univalence blocker (`093603`, `093731`) |
| stable `OpObjectPathView_EQ1(C,x,y)` carrier plus direct literal identity cast | the stable classifier comparison passes, but a one-step `:= p` still asks Lambdapi to compose a proof-time unifier with carrier decoding; the hints are not transitive | **one-step body rejected**; explicitly staging this intermediary passed in Phase 6, but the opposite-only head is now superseded by the uniform carrier view (`094105`) |
| stable opposite intermediary plus typed-`let` `op_path_as_omega_EQ1`/`op_omega_as_path_EQ1` | both definitions beta-reduce to their input; abstract, double-opposite, Product, and literal-`Path_cat` specializations and both round trips pass with unchanged warnings/audit | **successful Phase-6 intermediate, now generalized**; the public names remain but route through `ObjectPathCastView_EQ1` (`094208`, `094216`, `094338`, `094347`) |
| uniform `ObjectPathCastView_EQ1(C,x,y)` carrier plus two typed-let casts | equality enters by carrier reduction and EQ1 by one direct unifier; both definitional round trips pass for abstract, Product, opposite, `Op(Product)`, `Path_cat`, functor categories, Cat, and Grpd; facade observers remain negative; warnings/audit stay `971/157` and zero/45/27 | **selected and promoted Phase-7 explicit cast boundary**; the operations are transparent identities, the view is primitive but carrier-decoded, and no opaque encoder/decoder term is needed (`103710`, `103722`, `103828`, `103841`, `103948`, `104003`) |
| broad runtime repair for functor action after `id(Path_cat A,x)` exposes `eq_refl(A,x)` | the all-target rule passed quietly but raised critical pairs from 971 to 1008; restricting the target to `Cat_cat` still raised them to 1005 | **runtime orientation rejected, not a J blocker**; the narrow Cat-valued proof-time identity comparison passes at unchanged `971/157` (`122109`, `122205` rejected; `122523`, `122533` selected) |
| runtime commuting bridge from the folded `fib_cov_transf` component to the Sigma-section presentation | the intended comparison passed, but the additional runtime owner raised the inventory to `973/157` and exposed five inferred compound LHS slots | **runtime orientation rejected**; preserve the existing directed normal forms and state only the reflexive proof-time join needed by the J proof (`122956`) |
| one deeply nonlinear `unif_rule` matching the entire `PathOut`/Sigma-pullback component against its uncurried functor | even syntactically near-identical ground terms remained unsolved: Lambdapi did not reliably select the nested pattern, and transparent aliases changed which presentation was visible | **pattern shape rejected, not a semantic blocker**; match the two rigid outer heads and return the `K/F/G/k` presentation equations as residual constraints. That decomposed rule, both derived comparisons, quiet/warning checks, and strict audit pass (`124622` failed; `125121`, `125131` selected) |

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

The probes changed the original unmeasured proposal in eight
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
5. literal `lambda p, p` views are valid only while the classifier comparison
   remains at its abstract owner; they are not promoted as general transparent
   casts because Product specialization exposes a type-instability boundary;
6. the generic runtime tautology is not typable against the present open
   `Obj`/observational-equality normal forms, so only rigid Cat/Grpd runtime
   owners are selected;
7. Cat and Grpd equality can nevertheless reduce directly to EQ1, with finite
   Cat self-normalization and unchanged warning/audit evidence;
8. the defined object-path package is the safe general path-to-equivalence
   computational adapter and passes even at Product/Op; a uniform stable
   carrier view now supplies explicit transparent casts in both directions
   across every measured specialization. The primitive nonreducing cast term
   remains only an unused fallback;
9. the exact literal structured-action/J comparison is feasible, but the
   natural implementation is propositional: primitive `ind_eqr` keeps its
   reflexivity reduction, the directed action keeps its own runtime normal
   form, and two narrowly decomposed proof-time joins reconcile the identity
   and projection orders without a parallel eliminator.

None of these is a blocker to the selected core. The genuinely unresolved
work is narrower: a principled raw-path/package observer join if that
convenience is ultimately wanted, full migration from D0 and decoder
consumers, a structured motive that materially uses nonliteral groupoidality
rather than merely carrying the witness, and semantic assurance for the
generic equality/equivalence fixed point. Native evidence property and finite
`NCat` object truncation are now transparently proved.
Additional reduction-heavy formers must reuse the measured stable-view
discipline or justify a local fallback rather than reopening a general cast.
HIT/reflector work remains a later-phase obligation; unconditional finite
`NCat` object truncation no longer does.

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
- the initial review changed no active kernel code and weakened no validation;
  each later promoted slice was reproduced again at its current owner before
  active editing.

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

The Phase-6 direct-owner and reduced-former evidence is:

- `logs/probes/evogj_phase6_generic_direct_owner_full-20260717-071114.log`;
- `logs/probes/evogj_phase6_generic_direct_owner_full-20260717-071140.log`;
- `logs/probes/evogj_phase6_generic_direct_owner_full-20260717-072841.log`;
- `logs/probes/evogj_phase6_generic_runtime_owner_full-20260717-073039.log`;
- `logs/probes/evogj_phase6_cat_grpd_direct_owner_full-20260717-073213.log`;
- `logs/probes/evogj_phase6_cat_grpd_direct_owner_full-20260717-073227.log`;
- `logs/probes/evogj_phase6_shaped_direct_joins_owner_full-20260717-072001.log`;
- `logs/probes/evogj_phase6_shaped_direct_joins_owner_full-20260717-072024.log`;
- `logs/probes/evogj_phase6_shaped_direct_joins_owner_full-20260717-072118.log`;
- `logs/probes/evogj_phase6_shaped_direct_joins_owner_full-20260717-072504.log`;
- `logs/probes/evogj_phase6_shaped_direct_joins_owner_full-20260717-072533.log`;
- `logs/probes/evogj_phase6_product_join_isolated-20260717-072608.log`;
- `logs/probes/evogj_phase6_product_join_isolated-20260717-072629.log`.

The selected stable-former follow-up and its rejected intermediate
orientations are:

- stable Product carrier/API before opposite integration:
  `evogj_phase6_stable_product_path_owner_full-20260717-093358.log` and
  `-093427.log`;
- rejected direct opposite reduced-classifier specializations:
  `-093603.log` (`Op(Product)`) and `-093731.log` (`Op(Path_cat)`);
- rejected unstaged one-step identity body through two non-transitive
  comparisons: `-094105.log`;
- selected typed-intermediary opposite candidate:
  `-094208.log` and `-094216.log`;
- final Product/opposite candidate with public Product casts:
  `-094338.log` and warning-enabled `-094347.log`.

The final candidate retains `971/157` warnings and the strict zero/45/27 LHS
audit. A deliberately cross-classifier conversion-style assertion in
`-093325.log` was rejected as the wrong test: the literal identity adapter
definition is accepted, while same-typed round trips are the meaningful
runtime check. This does not weaken the classifier non-conversion negative.

The corresponding latest candidate source is
`tmp/probes/evogj_phase6_stable_product_path_owner_full.lp`. It is ignored
review evidence and must be reproduced at the then-current owner before
promotion.

The Phase-9 literal structured-action/J follow-up used the same current-owner
full-file probe. Its relevant evidence is:

- broad runtime identity repairs rejected at `1008/157` and `1005/157`:
  `evogj_phase6_stable_product_path_owner_full-20260717-122109.log` and
  `-122205.log`;
- selected narrow Cat-valued identity comparison, quiet and warning-enabled:
  `-122523.log` and `-122533.log`;
- runtime uncurrying bridge rejected at `973/157`: `-122956.log`;
- the unsuccessful deeply nonlinear proof-time component match:
  `-124622.log`;
- the selected decomposed reflexive component join plus the two derived
  comparison theorems, quiet and warning-enabled: `-125121.log` and
  `-125131.log`.

The selected candidate keeps `971/157`, the zero/45/27 strict LHS audit, and
runtime negatives for both proof-time joins. These logs are retained only as
reproducible evidence; the promoted kernel, checks, example, and this ledger
are the implementation authorities.

The native equivalence-valued-transport follow-up first passed as the focused
import probe
`logs/probes/evogj_groupoidal_transport_equiv-20260717-133457.log`.
Promotion deliberately rechecked declaration order at the real active owner:
placing the final fibre wrapper beside the earlier groupoidality declarations
failed with `Unknown symbol Fibre_cat`, because that readability alias is
declared later in the file. Relocating only the wrapper immediately after the
`Fibre_cat`/`catd_transport_func` owner made the bounded full `make check`
pass. The generic functor-preservation and groupoidal-arrow definitions remain
at their earliest dependency-complete owners. The expanded reviewer example
passes in
`logs/probes/groupoidal_structured_j_eq1-20260717-134053.log`; warning and
strict-LHS gates remain `971/157` and zero/45/27. This was an owner-order
repair, not a semantic failure, and it is concrete evidence for keeping
import probes subordinate to active-owner validation.

The subsequent D0b-free formation probe is
`tmp/probes/evogj_eq1_native_hom_action_formation.lp`. Its progressive passing
logs end in `-141556.log`, `-141855.log`, and `-141932.log`: native EQ1 laws
reify all needed transformations and endpoint components, both inverse hom
functors form, a generic conjugated hom action is J-equal to identity, and the
explicit left composite definitionally joins that conjugation. The direct
right-composite join fails in `-142013.log`; a conversion-debug rerun
`-142545.log` times out and is not used as positive evidence. The final
classified probe `-142848.log` keeps the right composite and both constituent
endpoint triangle comparisons as negative controls. The missing item is a
propositional bi-inverse adjointification/triangle-coherence theorem, not
formation, inversion, equality reification, or another decoder capability.

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
| Syntactic correctness | high for the promoted Phase-1-through-9 and selected Phase-11 boundaries: abstract/Cat/Grpd owners, stable Product equality, uniform carrier-view casts, both transparent one-way derived modules, and the extracted Sum library all pass specialization and bounded checks; only the un-staged unrestricted identity body remains correctly rejected |
| Computational feasibility | high for construction, projection, reflexivity packages, the object-path adapter, explicit transparent casts, literal-path witnesses, direct Cat/Grpd identity, Product paths, both groupoid-equivalence bridges, native next-hom action, literal structured action/J, unrestricted native evidence property, and finite-`NCat` truncation; medium-low only for observers on unreified cast terms and reverse pointwise-to-coherent-functor assembly |
| Completeness for a minimal MVP | the equality/univalence/groupoidality/structured-J/evidence-property/finite-truncation forward boundary is executable; the native foundation no longer depends on a legacy decoder, while full compatibility retirement, reverse pointwise/core assembly, and core-universe functors without a consumer are explicitly later work |
| Reusability | demonstrated by active reviewer examples and the one-way extensions: native fixed-arrow/first-class elimination, Sigma comparison, literal paths, explicit `TypeEquiv` bridges, direct univalence, native homwise preservation, pointwise groupoidality, displayed transport, evidence uniqueness, and finite object truncation support library construction; broader standard-library consumers remain later work |
| Expressiveness versus ordinary HoTT | covers the selected equality, equivalence, univalence, and structured-transport boundary with stronger directed/omega-categorical primitives; the walking-endomorphism child has been reopened because its promoted word-carrier implementation is not the intended opaque HIT, while broad HIT/reflector coverage and automatic structuring of arbitrary raw motives remain absent |
| Foundational assurance | operational evidence only; the generic unification equation remains trusted logical authority and requires finite/stratified semantic sanity evidence |

### Status of the active implementation against this proposal

| Active area | Honest status relative to the proposed endpoint |
| --- | --- |
| decoded H0 formers and selected observational equality | substantial retained foundation; their constructor/eliminator computation is real, while observational equality is intentionally shaped rather than a complete general calculus |
| directed `Cat`/functor/transfor/family kernel | strong retained foundation and the main reason the redesign is plausible |
| current `OmegaEquivAlong_D0` | useful operational experiment with inverse/cell observers, but still an opaque primary certificate with no native construction/elimination/extensionality account |
| current legacy public `OmegaEquiv` | transparent Sigma and usable on explicitly packaged data; retained for compatibility but not suitable as the new direct-univalence classifier normal form |
| promoted `OmegaEquivAlong_EQ1` / `OmegaEquiv_EQ1` | native equality-law record plus stable record-like first-class facade, with real construction, projection, elimination, explicit path-adapter computation, active abstract proof-time comparison, and explicit bidirectional D0 migration |
| current Cat-universe equality | finite direct runtime EQ1 classifier with computational explicit reflexivity packages; the old `CatPathView`/D0 encoder-decoder surface remains explicit compatibility, and generic `eq_refl` intentionally remains distinct from the canonical EQ1 reflexivity package |
| current Grpd-universe equality | direct runtime EQ1 classifier over the completed function-path hom boundary; `GrpdPathView := TypeEquiv` and its decoder round trips remain explicit compatibility/library surfaces rather than the primary normal form |
| current `PathOut`/`path_ind_sec` | materially computational through existing `fapp*`/`tapp*` rules and shaped motive folds; at a literal `Path_cat(A)` source its application and the displayed action are now proved propositionally equal to primitive `ind_eqr`, while primitive J alone retains reflexivity reduction |
| native EQ1 next-hom/groupoidality extension | transparent one-way derived module with one ordinary public hom-action owner, protected computational proof helpers, native core-inclusion groupoidality consumers, pointwise all-arrows evidence, and equivalence-valued displayed transport; no D0b route remains in this chain |
| current Sum action example | mathematically meaningful for disjoint sums and computational on registered bases; now isolated in a downstream library module and no longer a foundational univalence prerequisite |
| truncation/`NCat` spine | semantically meaningful retained work plus a transparent downstream native-EQ1 theorem `ncat_obj_trunc_EQ1`; the old D0 conditional capability remains compatibility-only |
| HIT/reflector scope | reopened: the bounded child rejects the promoted word-carrier category as the intended HIT. Opaque formation, judgmental point/loop beta, whole-HIT Code, Nat powers, and both inverse proof terms have focused probe evidence once an opaque 1-cell elimination component is supplied; primitive-versus-derived ownership of that component and active migration remain open. Truncation reflectors, Circle/groupoid completion, generic HIT abstraction, dependent Join elimination, and raw-family fibrancy remain deferred |

Thus the selected operational MVP is now a genuine native extension of the
existing categorical kernel rather than a facade over the old decoder tower.
The compatibility layer still exposes opaque D0 and decoder capabilities and
must not be described as a second completed foundation, but none of the native
hom-action, groupoidality, evidence-property, or finite-truncation chain
depends on it. The remaining foundational assurance questions are semantic
metatheory, not missing operational constructors or proofs.

### Expressiveness comparison with ordinary HoTT

| Topic | Reviewed Emdash target versus ordinary HoTT |
| --- | --- |
| Equality and J | retains primitive intensional equality and `ind_eqr`; adds shaped observational equality and directed/path-category action rather than replacing raw J |
| Equivalence | uses equality-valued categorical bi-invertibility as the computational owner; contractible-fibre `TypeEquiv` remains a derived/library formulation |
| Univalence | intends equality/equivalence comparison in trusted Lambdapi unification plus selected runtime universe heads, giving more direct observer computation than axiom-only Book HoTT but requiring a new conversion-soundness account |
| Function/Sigma/record paths | already has meaningful observational interfaces and selected computation; coverage is uneven and not a general normalization/canonicity theorem |
| Directed higher structure | substantially more expressive natively: categories, omega-homs, functors, transfors, and directed families are kernel-level concepts rather than encodings in undirected types |
| Motives/transport | arbitrary `Grpd` families retain primitive J; richer Cat-valued transport computes when the motive is supplied as a functor/directed family, so raw higher-family structuring is less automatic than in mature type theories |
| HITs and reflectors | still materially behind mature HoTT/cubical libraries: the representative walking-endomorphism HIT is reopened and its current active word presentation is not accepted as the intended opaque HIT; there is also no truncation reflector, Circle/groupoid completion, or general HIT schema |
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
- the former parallel global capabilities `cat_univalence` and
  `cat_univalence_by_decoder` (the standalone former is now retired by the
  first Phase-7 migration slice);
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

At an owner where equality and omega-equivalence compare directly, a law may
be supplied without reification. The abstract `lambda p, p` experiment does
not remain type-stable after every former-specific equality reduction and is
not a public general cast. A compatibility view intended to support recursive
observation—or simply to work uniformly after specialization—uses the explicit
general object-path package:

```text
omega_equiv_along_left_cell_EQ1(u)
  := object_path_equiv_EQ1(Hom_cat C x x,left_law(u))

omega_equiv_along_right_cell_EQ1(u)
  := object_path_equiv_EQ1(Hom_cat C y y,right_law(u)).
```

This is a transparent construction from `path_to_hom`, inverse-path action,
and J-derived cancellation laws, not a replacement opaque encoder. The
adapter and these new-to-old recursive migration views are now promoted; they
do not use the legacy encoder.

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

#### Classifier interchange versus computational adapters and casts

The abstract generic unification equation accepts equality and EQ1 evidence in
both directions while `C` remains syntactically abstract. The first probe
therefore accepted a definition with the literal body `lambda p, p`. The
current-owner specialization audit shows why that definition is **not** a
general public cast: Product equality has already reduced to a transparent
Sigma path before the generic rule can fire. Applying the predeclared alias at
`Product_cat` is accepted by its signature, but unfolding it exposes `p` at a
type no longer unifiable with EQ1. The alias is therefore not promoted.

The selected Product repair is representation-directed.
`Product_grpd(A,B)` equality now reduces to the rigid
`ProductPathView(A,B,p,q)` head; its carrier decodes to the former
constant-family `SigmaPathView`, with literal-identity carrier adapters,
native introduction/projections/elimination, and preserved generic
reflexivity provenance. `Obj(Product_cat(A,B))` now reduces through
`Product_grpd(Obj A,Obj B)`, so the Product EQ1 comparison targets that stable
head. Product still owns path construction, projections, elimination, and
direct shaped comparison.

The later Phase-7 cast probe found a uniform repair for explicit term
interchange. `ObjectPathCastView_EQ1(C,x,y)` is a rigid classifier whose
carrier reduces to `x =_{Obj C} y`; one direct proof-time equation compares it
with `OmegaEquiv_EQ1(C,x,y)`. Equality therefore enters the view by ordinary
carrier reduction and EQ1 enters it through exactly one unifier. The public
`object_path_cast_to_omega_EQ1` and `omega_cast_to_object_path_EQ1` operations
stage that view with a typed `let` and beta-reduce to their input. They do not
depend on transitivity of unification hints and pass abstract, Product,
opposite, nested opposite/Product, literal-path, functor, Cat, and Grpd
specializations. Product and opposite compatibility names now route through
these general casts; the earlier `OpObjectPathView_EQ1` is retired.

The safe path-to-equivalence operation is the separately named, defined
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

The owner-position probes establish the selected separation:

- typed equality/EQ1 interchange works for abstract `C`;
- `omega_equiv_to_EQ1(object_path_equiv_EQ1(p)) -> path_to_hom(C,p)`;
- both inverse projections expose `path_to_hom(C,path_sym(p))`;
- both law projections expose their named J-derived witnesses;
- a raw abstract path accepted through proof-time comparison has no facade
  observer computation;
- explicit equality/EQ1 casts have definitional round trips after abstract and
  representative reduced-former specialization, but do not reify a package;
- Product paths are also accepted at their stable direct EQ1 boundary, while
  raw opposite paths still require the explicit cast;
- Product/opposite cast results have no facade observer computation unless
  constructed through `object_path_equiv_EQ1(p)`;
- quiet and warning-enabled checks pass at the unchanged `971/157` inventory.

Thus “decoder-free” means that no opaque equivalence/round-trip capability is
needed for the safe forward adapter or the rigid Cat/Grpd universe identities.
It does not mean that proof-time classifier equality automatically reifies a
raw term, nor that it remains available after every former-specific normal
form has erased `Obj C`.

This plan therefore distinguishes six notions that must not be collapsed
under the word “coercion”:

1. the active abstract `unif_rule` is proof-time **classifier authority**, not
   a term and not runtime conversion;
2. `object_path_equiv(p)` is a transparent, semantically constructed
   **computational adapter** whose result is an explicit package;
3. the selected `OmegaEquiv_EQ1` facade and its dependent eliminator are a
   stable primitive **record-like interface** with constructor/projection/
   eliminator beta rules;
4. `ObjectPathCastView_EQ1` is a primitive but carrier-decoded **stable cast
   view**. Its two public operations are transparent identity-body casts with
   definitional round trips; neither constructs a package or adds observer
   beta;
5. the Product and opposite cast names are transparent **compatibility
   aliases** through that general view. Product separately retains its stable
   runtime path classifier and shaped direct comparison;
6. a primitive **nonreducing cast term** would be genuine additional trust.
   The uniform view makes such an opaque fallback unnecessary for every
   measured specialization, so none is active.

The preferred stable-view design is now uniform rather than former-local. It
closes the measured Product/opposite and general explicit-cast cases without
an opaque term operation and without migrating general dependent-Sigma
equality. This conclusion is local to this plan and does not change the
repository-wide SOP.

There is one separate migration-only case. Because retained
`OmegaEquivAlong_D0` has no constructor, the explicit EQ1-to-D0 bridge needs a
stable primitive compatibility constructor on which the old D0 projections
can compute. It is not a classifier cast and cannot be implemented as
`lambda u, u` in the present representation: EQ1 and D0 are not themselves
definitionally identified, and their primary fields have different shapes.
Its four D0 observations are specified by projection rules, so it is not an
observationally opaque decoder theorem. This exception belongs to the D0
migration phase only and does not establish a general SOP requirement for
primitive encoders or decoders.

The selected runtime policy is hybrid:

- direct runtime equality is active for the rigid Cat and Grpd universe owners,
  where the stable EQ1 normal form and finite behavior are measured;
- proof-time comparison is active for variable `C`; the generic runtime rule
  is measured-rejected as ill typed against current observational normal forms;
- the `Path_cat` shaped join remains active;
- the uniform `ObjectPathCastView_EQ1` supplies explicit transparent casts in
  both directions for all measured category shapes, without making either
  classifier runtime-reduce to the other;
- Product equality uses the stable `ProductPathView` runtime head and a shaped
  EQ1 comparison; its carrier transparently retains the old Sigma-path data;
- opposite keeps ordinary object erasure and its direct reduced-equality
  unifier remains measured-rejected; its public cast names use the uniform
  view;
- `object_path_equiv_EQ1` remains the computational package whenever facade
  projections are required;
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
| raw `p : x =_A y` merely accepted as `OmegaEquiv(Path_cat A,x,y)` | classifier use is allowed by the shaped join; projections are not promised to compute in the initial MVP |
| general object path/equivalence through the explicit stable casts | both typed-let casts and both round trips beta-reduce to their input; facade observers remain stuck on unreified terms |
| Product path through `product_path_as_omega_EQ1(p)` | compatibility alias through the general cast; inverse cast computes; facade observers remain stuck on the unreified path |
| opposite path through `op_path_as_omega_EQ1(p)` | compatibility alias through the general cast; inverse cast computes; facade observers remain stuck |
| same path through `object_path_equiv(p)` | `to` exposes `path_to_hom(C,p)`; inverses and laws expose the defined path/J data |
| Product-category identity | compare with component identities proof-time; do not globally reduce generic `id` to a pair |
| equality law used as next-hom equivalence | use `object_path_equiv(law)` as the stable general interface; direct proof-time use is permitted only where the abstract or shaped comparison actually fires |
| non-reflexive arbitrary equivalence used by primitive `J` | may typecheck as equality at an active comparison boundary, but `J` need not runtime-reduce |

Every promoted classifier equation must name the observers that make its
consumer behavior meaningful. A bare unification rule with no operational
consumer is not completion.

There are four active interfaces here. Direct classifier unification permits
equality and equivalence terms to be supplied to APIs while its abstract or
shaped owner matches. The uniform stable carrier view separately provides
explicit transparent casts in both directions after specialization, without
constructing packages. General computational observation uses the constructed
`object_path_equiv(p)` package.
Literal path categories additionally use the specialized `path_equiv(p)`
package when the forward arrow should compute all the way to `p`, rather than
only to `path_to_hom(Path_cat A,p)`. A preliminary direct rule
`omega_equiv_to(p) -> p` overlapped with the ordinary package projection; a
package-to-path collapse then produced additional divergent pairs with the
evidence projection and eliminator. Raw-coerced projection computation is
therefore deferred until a property/quotient/eta account supplies a joining
principle. The plan must not conceal this boundary by calling the explicit
constructors definitionally silent coercions. A fifth, currently unselected
fallback interface would be a primitive nonreducing cast term. Such a symbol
would be opaque unless equipped with observer rules, would add genuine trust,
and is not needed by the promoted uniform view.

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

At the review baseline `Grpd_cat` decoded its objects to `Grpd` and the objects
of its hom-categories to ordinary functions, but did not identify the whole
hom-category or give a controlled identity/composition presentation. Phase 4
has now promoted the boundary selected below, so later direct
groupoid-universe work may rely on it.

The selected active boundary is:

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

This exact division passed at owner position with no warning delta and is now
active. Making
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

This derivation is now closed transparently in the active kernel:
`is_equiv_map_by_inverse` constructs the standard quasi-inverse-to-
contractible-fibres proof from left-oriented path induction and the generic
half-adjoint triangle, then re-centres the fibre without a rewrite. The bridge
therefore adds no decoder or theorem assumption.

General package round trips remain propositional/extensionality work. The
finite `GrpdPathView := TypeEquiv` interface remains a compatibility view;
the explicit bridges are promoted, but retirement still waits for the direct
identity owner and consumer migration.

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

When a universe is actually used as the codomain of a structured motive, its
interface needs an actual functor rather than merely a carrier function. No
current MVP consumer does so, so this section specifies the consumer-led next
construction rather than an unconditional implementation requirement. The
first candidate inclusion is the plain groupoid core, not a truncated package:

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

Direct equality/equivalence comparison supports **term interchange at the
owner positions where the proof-time rule fires**. An abstract probe accepts
identity bodies such as `lambda p, p`, but the Product specialization audit
shows that such a definition is not a subject-reduction-stable general cast:
after Product equality decodes to its Sigma-path normal form, unfolding the
body no longer joins that source type to the stable EQ1 facade. The promoted
general casts do not contradict that result: they stage a rigid
`ObjectPathCastView_EQ1` in a typed `let`, rather than exposing an
unconstrained body at the result classifier. Equality reaches the view by
carrier reduction and EQ1 by one direct unifier, so both operations remain
transparent and specialization-tested.

Consequently, a current encoder such as `idtoequiv_cat` must not be replaced
blindly by `lambda p, p`, whether or not a classifier-only abstract test
passes. Its computational role should instead be redefined through the
transparent `object_path_equiv` package, possibly under a clearer public name;
only its opaque univalence-capability role is retired. Consumers may use the
uniform stable casts when no observer is required. If a future representation
cannot use that view, there are two explicit design choices:

1. preferably introduce stable injective former path-view heads with defined
   construction, observation, elimination, and transparent comparison to the
   existing decoded path presentation;
2. otherwise introduce a narrowly typed primitive nonreducing cast. That
   symbol is an explicit trusted interface and remains operationally opaque
   unless separately justified observer rules are added. It is not evidence
   that proof-time unification inserted a package.

This is a plan-local cast/reification policy, not a repository-wide demand for
encoder/decoder symbols. In particular, the selected identity casts are
transparent terms whose bodies reduce to their inputs, while
`object_path_equiv_EQ1(p)` is an explicit transparent package construction
whose fields compute. A stable primitive record/view head may own projections
without thereby becoming an opaque encoder theorem. An opaque primitive term
operation remains only the unselected fallback in item 2.

The same distinction applies at the groupoid universe once its direct
comparison is selected. This does not mean every current symbol should be
deleted at once. The migration should classify current APIs into five groups:

1. **retained semantic owners**: fixed-arrow equivalence, projections,
   `path_to_hom`, the defined object-path adapter, path/core action, `PathOut`,
   truncation and dimension data;
2. **direct classifier/explicit-cast consumers**: terms used without a cast
   only at measured abstract, shaped, or rigid owner positions; otherwise use
   the uniform stable-view identity casts when no package observation is
   required;
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
- direct classifier use, the uniform stable cast view, computational adapters,
  former path views, and any primitive fallback are named and trusted
  separately;
- reflexivity, general object-path, and literal path-category observers
  compute/compare at their documented boundaries;
- old-to-new and new-to-old migration examples pass;
- negative controls ensure no accidental runtime proof erasure;
- reports and examples no longer describe the decoder as foundational.

## Proposed Runtime And Proof-Time Policy

| Equation/behavior | Preferred initial owner | Reason |
| --- | --- | --- |
| `Eq(Obj C,x,y) == OmegaEquiv(C,x,y)` for variable `C` | active proof-time `unif_rule` | generic runtime candidate is ill typed; abstract typed firing is warning-neutral |
| `Eq(Obj Cat_cat,A,B) -> OmegaEquiv(Cat_cat,A,B)` | active rigid runtime owner with EQ1 payload | finite self-universe normal form passes |
| `Eq(Obj Grpd_cat,A,B) -> OmegaEquiv(Grpd_cat,A,B)` | active rigid runtime owner with EQ1 payload | function-path hom and explicit TypeEquiv bridges are already active |
| `OmegaEquiv(Path_cat A,x,y) == Eq(A,x,y)` | proof-time shaped join first | resolves exact type-level diamond without forcing a runtime facade |
| same `Path_cat` join under selected facade | deferred runtime candidate | classifier orientation alone is plausible, but package/projection joins have not passed |
| general reducible `as_omega_equiv(p) := p` | not selected | abstract typing passes but Product specialization is not type-stable under unfolding |
| general explicit equality/EQ1 casts | `ObjectPathCastView_EQ1` carrier reduction plus one direct proof-time comparison; typed-let operations in both directions | definitional round trips pass across abstract, Product, opposite/nested, Path, functor, Cat, and Grpd shapes without an opaque term operation |
| general `object_path_equiv(p)` | transparent explicit package from `path_to_hom`, inverse path, and J laws | gives reusable observer computation without an opaque encoder |
| Product equality and Product/EQ1 casts | runtime `ProductPathView` with transparent Sigma carrier adapters and shaped proof-time EQ1 comparison; compatibility cast names use the uniform view | closes the former Product path-normal-form gate while preserving the existing data and reflexivity provenance |
| opposite equality and opposite/EQ1 casts | runtime object erasure retained; compatibility cast names use the uniform view | direct comparison with reduced equality fails on composites, while the uniform explicit casts pass Product/Path/double-opposite specialization |
| future cast outside the uniform view | extend a semantically justified stable view first; primitive nonreducing term only as last fallback | the promoted general view currently covers every measured category shape |
| explicit `path_equiv(p)` observations | runtime constructor/projection beta | gives the intended path computation without collapsing every raw path into a package |
| raw path silently accepted as equivalence | type comparison only in initial MVP | direct projection rules currently create a critical pair |
| `eq_refl` versus canonical equivalence package | observer projection rules and/or narrow proof-time comparison | preserve generic proof provenance |
| `Hom_cat Grpd_cat A B` | runtime to `Path_cat(Function_grpd A B)` | exposes the missing higher path structure of functions |
| `Grpd_cat` identity/composition versus pointwise functions | stable semantic heads plus proof-time comparison | broad runtime lambda folds add 36 critical pairs |
| `Core_incl_func(Path_cat A)` versus identity functor | narrow proof-time candidate; runtime only after projection audit | canonical groupoidality introduction |
| Product identities versus component pair | proof-time comparison | preserve current identity normal-form policy |
| Sum outer/component reflexivity | two general proof-time comparisons | replace action-specific bridge proliferation |
| equality law used as recursive equivalence | direct use only at a measured owner; explicit object-path package for uniform typing and computation | central ownership reversal without pretending unification inserts a record |

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
| `cat_univalence` | retired in the first Phase-7 inventory slice: it had no kernel consumer beyond its declaration and two diagnostics now use `cat_univalence_from_decoder` |
| `cat_univalence_by_decoder` | retain temporarily as the single legacy categorical round-trip capability; retire only after its four kernel occurrences and dependent compatibility theorems are migrated |
| `idtoequiv_cat` | split its roles: retain/redefine the computational operation through transparent `object_path_equiv`; use direct terms only at measured classifier owners; retire opaque capability dependencies |
| `omega_equiv_path` | retain as an explicit compatibility/theorem interface until every reverse-typing consumer is covered by an active direct owner or a selected stable former view; do not replace it by an unvalidated identity-body alias |
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

### Phase 0: Review, adoption, and frozen questions — completed 2026-07-17

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

Exit criterion met: the user explicitly adopted this overlay in the
implementation handoff based at commit `4315137...`. The selected first
candidate is the decoded native fixed-arrow record at the current D0 owner
position.

### Phase 1: Equality-law fixed-arrow candidate — completed 2026-07-17

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

Exit criterion met. The active kernel now contains the decoded native
`OmegaEquivAlongEqData_EQ1` record, stable classifier, readable constructor,
four observers, indexed eliminator, and reflexive evidence beside the retained
D0 owner. Fourteen permanent diagnostics cover all introduced and reflexive
fields, eliminator beta, a named `Cat_cat`-arrow consumer, and the four
negative boundaries; the catalog contains 1,719 checks across 64 areas with
zero unclassified checks. Owner-position quiet and warning logs end in
`20260717-051555` and `20260717-051603`; warnings remain exactly 971
unjoinable/157 replaceable and the strict audit remains zero unreviewed with
45 annotated slots across 27 clauses. `make check`, `make examples`, catalog,
health, and synchronized 41-file CI all pass; the final CI metrics pass records
213.824 seconds. No comparison with D0, facade, direct-univalence rule, opaque
adapter, evidence eta, or proof erasure was added.

### Phase 2: Stable-facade promotion and observer boundary — completed 2026-07-17

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
8. under a local generic proof-time classifier comparison, test an abstract
   `as_omega_equiv_EQ1(p) := p` experiment in both directions, runtime
   non-conversion, stuck raw observers, and the primitive-J negative control;
9. compare declaration count, warning inventory, eliminability, public
   construction, and performance with the reproduced probe baseline.

Exit criterion: the selected facade and Sigma comparison are promoted with
measured evidence, the general object-path adapter is defined rather than
assumed, direct classifier use is not confused with computational reification, and
the new eliminator is explicitly documented as trusted record-like kernel
surface.

Exit criterion met, with one dependency-boundary refinement. The active
kernel now contains the stable abstract `OmegaEquiv_EQ1` facade, injective pack
constructor, forward/evidence observers, primitive dependent eliminator,
canonical package reflexivity, propositional eta, transparent Sigma comparison
with both propositional round trips, and the transparent
`object_path_equiv_EQ1` package built from `path_to_hom`, `path_sym`, and two
`ind_eqr` cancellation laws. The facade is primitive record-like kernel
surface with beta rules, not a bodyless encoder/decoder theorem; the
object-path adapter is a semantic definition rather than an assumption.

The transparent-Sigma direct-classifier failure was reproduced at the current
owner in log `20260717-054207`. The selected no-unification owner passes in
quiet/warning logs `20260717-054453`/`054501`; the isolated generic
classifier comparison and abstract identity-body experiment pass in
`20260717-054607`/`054613`. Both warning-enabled candidates remain exactly at
971/157 and both strict audits remain zero/45/27. The direct comparison was
therefore retained as Phase-6 probe evidence rather than promoted implicitly
with packaging. For the same reason, bare-`eq_refl` facade observers are
deferred to Phase 6; reflexive **packages** already compute through ordinary
constructor beta. This keeps the dependency graph honest and avoids making a
trusted unification equation a hidden prerequisite of the record facade.
The later Phase-6 Product specialization audit rejects that experiment as a
general exported cast; this Phase-2 record is retained only as the earlier
abstract-owner evidence.

Twenty-three new permanent diagnostics and the reviewer example
`examples/equality_valued_omega_equivalence.lp` cover construction,
elimination, eta-on-constructor, both Sigma views/round trips, all general
object-path observations, reflexive J laws, and five non-conversion
boundaries. The catalog has 1,742 checks across 64 areas with zero
unclassified checks; health passes 42 files with a 20,412-line/833-symbol/
589-rule/58-unification-rule kernel and 1,542 positive diagnostics. Warnings
and the strict audit remain unchanged, `make check` and `make examples` pass,
and the final synchronized CI result is recorded in the Phase-2 ledger row.

### Phase 3: `Path_cat` join and canonical groupoidality — completed 2026-07-17

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

Exit criterion met. The active kernel now has the narrow proof-time join
`OmegaEquiv_EQ1(Path_cat A,x,y) == Eq(A,x,y)`, explicit
`path_equiv_along_EQ1`/`path_equiv_EQ1` packages with literal `p` and
`path_sym(p)` fields, J-derived left/right laws, and canonical
`IsGroupoidalCat_EQ1(Path_cat A)` evidence. The latter is fixed-arrow
equivalence evidence for `Core_incl_func(C) : Core_cat(C) -> C`; in ordinary
external terminology this is stronger than merely having inverses unless the
intended univalence/completeness of `C` is also assumed. The source and
Foundations now state that scope explicitly.

The first attempt to place the Core-inclusion comparison beside
`Core_incl_func` failed immediately because that owner precedes the declaration
of `Cat_cat` (`20260717-060449`). It was relocated to the internal-groupoidality
boundary, the first semantic owner where both rigid heads exist. The selected
full owner passes quietly and warning-enabled in `20260717-060509`/`060516`
with unchanged 971/157 warnings and zero/45/27 audit. Typed `eq_refl` validates
the Core-inclusion `unif_rule`; runtime non-conversion remains negative.

The current-owner raw-path projection candidate was also re-tested. It raises
the inventory to 972/160, creates the package/path diamond in which
`omega_equiv_to(pack(f,u))` reduces either to `f` or to the entire package,
and makes a downstream assertion fail (`20260717-060625`/`060639`). It remains
rejected. The explicit package is therefore not incidental syntax: it is the
stable computational reification boundary.

Seventeen positive/six negative permanent diagnostics cover shaped typing in
both directions, every explicit path observer, reflexive laws, facade
elimination, one next-hom reification, typed Core comparison, canonical
groupoidality fields, and the raw/package/generic-J boundaries. The reviewer
example now has 18 positive statements and retains its negative controls. The
catalog has 1,765 checks across 64 areas with zero unclassified checks; health
passes 42 files with a 20,540-line/839-symbol/589-rule/60-unification-rule
kernel and 1,559 positive diagnostics. Final synchronized CI is recorded in
the Phase-3 ledger row.

### Phase 4: `Grpd_cat` completion and `TypeEquiv` bridges — completed 2026-07-17

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

Exit criterion met with the pre-existing theorem obligation explicitly
classified. The active `Grpd_cat` hom-category now reduces to
`Path_cat(Function_grpd A B)`. Stable `grpd_id_function` and
`grpd_comp_function` heads compute only when applied to an argument, while two
narrow `unif_rule`s compare the generic category identity/composition owners
with those heads at proof time. Typed `eq_refl` diagnostics exercise both
comparisons. The broad alternative that runtime-reduced category operations
directly to lambdas remains rejected because its preliminary probe raised the
warning inventory to 1007/159.

Both representation adapters are active and defined. `type_equiv_to_omega_EQ1`
uses the selected `TypeEquiv` inverse and `PiFunext` to construct both
equality-valued cancellation laws. In the converse direction, the two inverse
choices are compared pointwise, the left inverse is given a derived right law,
and `omega_along_to_type_equiv_EQ1` packages the resulting
`EquivByInverse`. Forward maps, both forward-adapter inverse fields, both
forward-adapter laws, the reverse selected inverse/right law, and the
forward-map round trip compute. No new decoder, bridge theorem, or global
groupoid-univalence inhabitant was introduced.

The standard `is_equiv_map_by_inverse` declaration is now a transparent
theorem. Its selected fibre centre remains the specified inverse/right-law
witness exactly, while the contraction is constructed through dependent Sigma
paths and the half-adjoint triangle. The former selected-centre rewrite has
been removed. Thus the representation comparison is decoder-free and adds no
opaque authority; `EVOGJ-QINV-FIBRE-PROOF` is complete.

The fresh current-owner probe is
`tmp/probes/evogj_phase4_grpd_bridges_owner_full.lp`. Quiet and warning-enabled
logs end in `20260717-062534` and `20260717-062544`; the latter remains exactly
971 unjoinable/157 replaceable warnings and the strict audit remains
zero/45/27. Seventeen positive/six negative permanent diagnostics bring the
catalog to 1,788 checks across 65 areas with zero unclassified checks. The new
reviewer example `examples/grpd_eq1_type_equiv_bridge.lp` has twelve
positive/five negative statements. At this gate the kernel has 20,787 lines,
852 symbols, 592 rules, and 62 unification rules; the diagnostic suite has
1,576 positive and 212 negative checks. `make check`, `make examples`, the
warning and strict-LHS gates, and the complete 43-file metrics pass. Final
Phase-4 behavior is also covered by the subsequent synchronized 44-file
Phase-5 CI gate, which passes with 237.578s of measured checking time.

### Phase 5: Old/new evidence bridges — completed 2026-07-17

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

Exit criterion met at the observational migration boundary. The defined
`omega_equiv_along_D0_to_EQ1` observes both old inverse arrows and decodes the
two old recursive cells through the existing `omega_equiv_left/right_law`.
The first-class `omega_equiv_D0_to_EQ1` preserves the selected forward arrow.
In the reverse direction, `omega_equiv_along_EQ1_to_D0` is a stable
compatibility constructor for the otherwise constructorless D0 target, and
`omega_equiv_EQ1_to_D0` packages it with the selected forward arrow. Its four
D0 observations are completely specified: inverse arrows are the EQ1 fields,
and both recursive cells are built from `object_path_equiv_EQ1(law)` followed
by this same compatibility constructor.

This result sharpens the primitive/opaque distinction. A primitive
compatibility constructor is needed only to inhabit the **old opaque D0
representation during migration**; it is neither a general encoder
requirement nor part of the redesigned equality-law foundation. It cannot be
the literal identity function because the retained D0 and EQ1 evidence
classifiers are not definitionally the same representation. The compatibility
head is not observationally opaque: both inverse projections, both recursive
cells, each cell's `path_to_hom` forward arrow, and a further next-hom inverse
observation compute. A preliminary version whose cells used the legacy
`idtoequiv_cat` encoder also passed, but the promoted version removes that
decoder dependency. No new decoder, D0 eliminator, or evidence eta is added.

Old reflexivity converts definitionally to new reflexive evidence. Product,
opposite, and one existing D0b hom-action consumer accept new evidence through
the reverse bridge and remain observable after converting back. The opaque D0
certificate has no eliminator, eta, or extensionality theorem, however, so
neither evidence round trip is claimed even propositionally; both remain
permanent negative controls, as does equality between converted new
reflexivity and the old stable D0 reflexivity head. These are representation
limitations of retained D0, not failures of the new evidence.

The temporary legacy-encoder probe passes quietly and warning-enabled in
`20260717-064319`/`064436`. The selected object-path candidate passes before
and after its full diagnostic matrix in `20260717-064419`, `064428`,
`064810`, and `064828`. All warning-enabled results remain exactly 971/157,
and the selected strict audit remains zero/45/27. Seventeen positive/three
negative permanent diagnostics bring the catalog to 1,808 checks across 66
areas with zero unclassified checks. The reviewer example
`examples/equality_evidence_migration.lp` has nine positive/three negative
statements. The kernel now has 20,892 lines, 856 symbols, 594 rules, and 62
unification rules; the diagnostics contain 1,593 positive and 215 negative
checks across 44 measured files. Final synchronized health/CI timing is
237.578s of measured checking time. `make examples`, `make health`, and the
complete `make ci` gate all pass on the synchronized 44-file snapshot.

### Phase 6: Direct univalence equations — selected boundary promoted

The following core sub-slice is completed and promoted on 2026-07-17:

1. the generic variable-`C` proof-time equation is active at the stable EQ1
   owner, with typed firing in both directions and runtime non-conversion;
2. Sigma-category and functor-category consumers demonstrate concrete firing
   where the abstract owner survives elaboration;
3. the existing shaped `Path_cat` join is preserved;
4. the rigid Cat-universe runtime rule now targets EQ1 and retains finite
   self-normalization;
5. the rigid Grpd-universe runtime rule now targets EQ1 over the completed
   function-path hom boundary and bidirectional `TypeEquiv` comparison;
6. package/reflexivity/general-object-path/literal-path observations retain
   their selected computations and negative provenance controls;
7. the generic runtime alternative is rejected as ill typed against existing
   observational equality normal forms;
8. Product equality now has a stable `ProductPathView` runtime owner, decoded
   Sigma carrier API, shaped EQ1 comparison, and explicit identity casts;
9. the Phase-6 opposite checkpoint retained ordinary object erasure and used
   `OpObjectPathView_EQ1` with typed-let identity casts; Phase 7 subsequently
   generalized and retired that local intermediary.

The specialization audit materially revised the original no-probe plan. An
abstract `lambda p, p` body is accepted while `C` remains a variable, but it
is **not** a stable general cast: Product equality reduces to its Sigma-path
classifier before the generic comparison can fire, and unfolding the alias
then fails the advertised cross-type conversion. Raw Product and Op paths are
therefore not rescued by exporting that unrestricted alias. Product gained a
stable local equality head. The Phase-6 opposite-only intermediary established
that typed-let staging is viable; Phase 7 replaces it with the uniform
`ObjectPathCastView_EQ1`. The explicit `object_path_equiv_EQ1(p)` package
remains the computational observer interface for every shape.

Three Product/Sigma shaped-unifier variants and a deliberately broad isolated
variant also failed to fire after the decoded equality normal form was
selected. This is not a mathematical obstruction to product equivalence. It
was an operational normal-form gate. The selected stable Product classifier
preserves the former Sigma carrier through identity adapters and adds native
construction/elimination without changing general dependent-Sigma equality.
The first direct opposite unifier then passed abstractly but failed at
`Op(Product)` and `Op(Path_cat)`. A stable opposite intermediary repaired those
composites; its one-step body still failed because unification hints are not
transitive. That intermediate result motivated the uniform stable carrier
view promoted in Phase 7. No primitive nonreducing cast was needed.

Measured Phase-6 evidence includes:

- abstract owner and specialization audits:
  `evogj_phase6_generic_direct_owner_full-20260717-071114.log` through
  `-072841.log`;
- rejected shaped Product/Sigma joins:
  `evogj_phase6_shaped_direct_joins_owner_full-20260717-072001.log` through
  `-072533.log` and
  `evogj_phase6_product_join_isolated-20260717-072608.log`/`-072629.log`;
- rejected generic runtime owner:
  `evogj_phase6_generic_runtime_owner_full-20260717-073039.log`;
- selected Cat/Grpd runtime owners:
  `evogj_phase6_cat_grpd_direct_owner_full-20260717-073213.log` and
  `-073227.log`;
- selected stable Product/opposite owner:
  `evogj_phase6_stable_product_path_owner_full-20260717-094338.log` and
  warning-enabled `-094347.log`;
- rejected direct opposite composite routes and unstaged intermediary body:
  `-093603.log`, `-093731.log`, and `-094105.log`.

The promoted boundary preserves the warning inventory at `971/157` and the
strict LHS audit at zero/45/27. Its permanent diagnostics and expanded
`examples/direct_univalence_eq1_boundary.lp` distinguish abstract direct use,
rigid universe normal forms, Product carrier/classifier/cast computation,
opposite explicit casts, unreified-observer negatives, and the explicit package
adapter. `make check`, the full reviewer sweep, warning summary, and strict
audit pass on the promoted owner. The synchronized catalog has 1,848 checks
across 66 areas (1,622 positive and 226 negative), the kernel has 21,101 lines,
869 symbols, 597 rules, and 65 unification rules, and health checks 45 files.
The expanded direct-boundary example has 15 positive/seven negative
statements. Catalog and health generation pass; final CI timing is recorded
with the promotion gate. The complete 45-file CI passes with 227.500s of
measured checking time.

Exit criterion for Phase 6 is met: the generic proof-time comparison, both
rigid universe owners, and the measured Product/opposite reduced-former
boundaries have term consumers and explicit trust classifications. The
primitive cast fallback remains unselected. The opposite-only view is retained
here as Phase-6 evidence but is no longer active after the Phase-7 uniform
view promotion.

### Phase 7: Decoder migration and direct use — completed at the selected foundational boundary 2026-07-17

1. use equality directly as `OmegaEquiv` only at measured abstract, shaped, or
   rigid owners; otherwise use the promoted uniform explicit casts;
2. migrate path-to-equivalence observer consumers to the transparent general
   object-path adapter; use the uniform identity casts only for consumers that
   do not require package observations;
3. redefine or rename `idtoequiv_cat` as that constructed adapter rather than
   replacing its computational consumers by a raw term whose direct owner may
   not fire and whose observers remain stuck;
4. distinguish the transparent EQ1-to-path cast from the computational legacy
   `omega_equiv_path` decoder; retain the latter only for consumers of its
   shaped beta and propositional round trips;
5. migrate groupoid universe consumers away from contractible-fibre identity;
6. retain explicit `TypeEquiv` comparison theorems in the library;
7. retire duplicate global decoder capability inhabitants only after consumer
   inventory reaches zero;
8. keep round-trip theorem names only where external compatibility warrants
   them;
9. update examples to demonstrate direct abstract/rigid classifier use,
   the uniform identity casts and Product/opposite aliases, general object-path reification,
   reflexivity projections, unreified-observer negatives, and specialized
   literal-path projections without claiming raw-cast facade observation or
   the unresolved raw-path projection equation.

The stable-cast checkpoint is promoted. The unrestricted body
`as_omega_equiv(p) := p` remains rejected because its unfolded term is not
specialization-stable. The selected `ObjectPathCastView_EQ1(C,x,y)` instead
has a rigid classifier head, a carrier reducing to object equality, and one
direct proof-time comparison with EQ1. The two typed-let casts therefore each
use only one conversion step at a time and beta-reduce to their input. Both
definitional round trips pass for abstract categories, Product, opposite,
`Op(Product)`, literal path categories, functor categories, Cat, and Grpd.
Runtime classifier nonconversion and facade-observer negatives remain active.
Quiet/warning owner probes `103710`/`103722`, `103828`/`103841`, and the
selected simplification `103948`/`104003` pass at unchanged `971/157` and
zero/45/27. The former `OpObjectPathView_EQ1` is removed; Product/opposite
compatibility names route through the uniform view.

The first Phase-7 inventory checkpoint is promoted. The standalone bodyless
`cat_univalence(C) : CatUnivalence(C)` inhabitant had no active kernel consumer
beyond its own declaration. Its only two diagnostic uses are now served by
the already-defined `cat_univalence_from_decoder(C)`, and the duplicate symbol
has been removed without adding a rewrite, unification equation, cast,
encoder, or decoder. The owner-position retirement probe passes quietly in
`evogj_phase6_stable_product_path_owner_full-20260717-101146.log` and with
warnings in `-101159.log`; the warning inventory remains `971/157` and the
strict audit remains zero/45/27.

The next two bounded consumers are also migrated without a primitive decoder.
The transparent `object_path_equiv_D0(p)` now composes
`object_path_equiv_EQ1(p)` with the observation-complete EQ1-to-D0 migration
constructor. Ordinary `IsoEvidence` uses that constructed adapter for both
recursive cancellation cells instead of `idtoequiv_cat`. The retained D1
next-hom compatibility API also obtains its selected category functor and D0
evidence through this adapter; consequently
`idtoequiv_cat_functor_D1(p)` now computes definitionally to
`path_to_hom(Cat_cat,p)`. The selected owner probes pass quietly and with
warnings in `-101755`/`-101805` and `-101936`/`-101947`, again at `971/157`
and zero/45/27. Five permanent diagnostics (four positive, one provenance
negative) and the affected reviewer examples cover formation, forward and
inverse observations, both ordinary-iso cells, and the D1 selected functor.
The pre-uniform-cast migration checkpoint had 1,853 checks across 66 areas
(1,626 positive, 227 negative, zero unclassified), a 21,107-line kernel with
869 symbols, 597 rewrite rules, and 65 unification rules, and 45 checked files;
its CI measured 222.477s. The synchronized uniform-cast checkpoint has 1,857
checks across the same 66 areas (1,630 positive, 227 negative, zero
unclassified), a 21,115-line kernel with 871 symbols, 597 rewrite rules, and
65 unification rules, and 45 checked files. Reviewer examples, catalog,
health, warning summary, strict audit, and CI all pass; the latter measures
269.410s of checking time.

The inventory prevents an over-broad deletion. Lexically, the active
kernel still contains 30 occurrences of `idtoequiv_cat`, 11 of
`omega_equiv_path`, ten of the evidence-indexed
`omega_equiv_along_path_D1`, and four of
`cat_univalence_by_decoder`. The groupoid side similarly retains 22
`idtoequiv_grpd`, 20 `grpd_equiv_path`, and four
`grpd_univalence_by_decoder` occurrences. These counts include declarations,
rules, and theorem bodies, but they demonstrate that the operations own real
computation and compatibility consumers rather than being duplicate unused
inhabitants. They must be migrated by role, not deleted by name.

This checkpoint sharpens the primitive-operation policy. No opaque
encoder/decoder term has been added to EQ1. The primitive cast *view* is fully
carrier-decoded, and its public operations are transparent identities. The
transparent `object_path_equiv_EQ1` remains the general computational encoder. The
primitive `omega_equiv_along_EQ1_to_D0` constructor remains necessary only to
inhabit constructorless legacy D0 during migration, with all four observations
specified. A primitive nonreducing cast term remains unselected. These are
explicit plan-local trust decisions, not a general SOP principle or a new
univalence theorem capability.

The final selected-boundary audit distinguishes foundation from compatibility
instead of deleting by spelling. Exact-token inventory still finds real legacy
kernel consumers (`idtoequiv_cat` on 30 lines, `omega_equiv_path` on 11,
`cat_univalence_by_decoder` on four, and the corresponding Grpd operations on
22/20/four). In contrast, the native hom-action and evidence-property modules
and their three public reviewer examples have **zero** references to those
Cat/Grpd decoders, D0/D0b, or either D0/EQ1 migration constructor. The former
`OmegaEquivAlong_D0b` classifier has no remaining active-kernel occurrence.
The native theorem chain is therefore
decoder-free, while the inventoried old operations remain honest
compatibility/library APIs with shaped computation and round-trip consumers.
Removing those APIs wholesale would be an unrelated compatibility migration,
not closure of a foundational prerequisite.

Exit criterion met at the selected MVP boundary: direct equality/equivalence
is the primary native interface and no native foundational theorem requires an
arbitrary decoder capability. Role-by-role retirement of still-used legacy
APIs remains optional compatibility work and must be separately consumer-led.

### Phase 8: Evidence property and finite dimension — completed 2026-07-17

The result is stronger and simpler than the original finite-first fallback:

1. the native record is exposed transparently as the product of its left and
   right inverse-and-law homotopy fibres, with propositional record eta proved
   through the indexed eliminator;
2. literal path evidence is contracted by path induction, preserving an
   explicit negative that the contraction proof is not judgmental proof
   erasure;
3. discrete and locally-set proofs were derived independently and remain
   useful scoped sanity checks;
4. ordinary categorical algebra shows the selected left and right inverse
   arrows agree, and gives the missing opposite-side law to either one;
5. composition with the forward arrow is then an explicit
   `EquivByInverse` on each inverse-candidate hom classifier;
6. the newly transparent `is_equiv_map_by_inverse` contracts the two fibres,
   so `omega_equiv_along_evidence_is_prop_EQ1(C,x,y,f)` holds for arbitrary
   `C,x,y,f`, with no truncation hypothesis or extensionality principle;
7. transparent `TruncLevel` induction proves arbitrary truncation closure
   under an explicit retraction;
8. transparent `CatDim` induction combines the hom hypothesis, same-level
   Sigma closure, general evidence property, facade/Sigma retraction, and
   equality/facade cast retraction to prove
   `ncat_obj_trunc_EQ1(n,C,h)` unconditionally;
9. base and successor computation equations are permanent diagnostics; the
   readable one-category theorem routes through the general recursion;
10. the legacy D0 global capability and conditional theorem remain explicitly
    compatibility-only because opaque D0 itself still lacks the corresponding
    extensionality account;
11. proposition-valuedness does not justify the previously rejected runtime
    collapse between a raw path and a facade package; that ergonomic join
    remains separate and optional.

The implementation lives in the one-way transparent
`emdash3_2_eq1_evidence_property.lp` module. It adds no primitive, opaque
theorem, rewrite rule, unification rule, decoder, or proof-erasure principle.
Focused evidence is recorded in
`evogj_general_evidence_prop-20260717-183317.log`,
`evogj_trunc_retract-20260717-183522.log`, and
`evogj_ncat_obj_trunc-20260717-183651.log`; active module/check/example probes
are `emdash3_2_eq1_evidence_property-20260717-183710.log`,
`emdash3_2_checks-20260717-183839.log`, and
`equality_valued_omega_equivalence_evidence_property-20260717-183908.log`.

Exit criterion met: property-valuedness is proved at unrestricted native-EQ1
scope and every finite native dimension has the predicted object-truncation
theorem, without a global capability.

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

Four Phase-9 slices are promoted. The derived hom-action and groupoidality
layer now lives in `emdash3_2_eq1_hom_action.lp`, which imports the kernel in
one direction; the kernel does not import the extension. For
`g : IsGroupoidalCat_EQ1(C)`, `groupoidal_core_homwise_EQ1(g,x,y)` applies
the native `omega_equiv_along_fapp1_EQ1` owner directly to the core-inclusion
witness, yielding equality-valued fixed-map evidence for
`core_incl_hom_func(C,x,y)` without D0 or D0b. Its selected right inverse is exposed as
`groupoidal_arrow_to_path_func_EQ1`; applying it to an arrow gives
`groupoidal_arrow_to_path_EQ1`, and the equality-valued right law plus
`eq_ap` proves that re-including the selected path recovers the original
arrow. The full homwise evidence still exposes separate left and right
inverse functors and both laws; no false single-quasi-inverse eta is claimed.

`discrete_cat_is_groupoidal_EQ1` converts the existing exact two-field
`IsDiscreteCat` evidence, and `zero_cat_is_groupoidal_EQ1` makes a packaged
`ZeroCat` carrier the concrete nonliteral consumer. The reviewer example
`examples/groupoidal_structured_j_eq1.lp` also checks that the existing
`path_ind_sec` computation for a Sigma-pullback structured motive remains
available in a context carrying groupoidality evidence. That generic assertion
remains specialization by weakening: it shows that no second eliminator or
fibrancy capability is needed for the structured action, but does not itself
consume `g`.

The second slice closes the exact literal comparison. For
`D : Catd(Path_cat A)`, `path_cat_structured_transport_EQ1(D,u,p)` is the
existing displayed functor action along `p`, while
`path_cat_ind_eqr_transport_EQ1(D,u,p)` uses primitive right `ind_eqr` with a
function-valued motive. The latter computes to `u` at `eq_refl`.
`path_cat_structured_transport_agrees_ind_eqr_EQ1` proves the two transports
equal by `ind_eqr`; its base case uses a narrow proof-time comparison between
Cat-valued functor action on `eq_refl` and the identity functor.

`path_cat_path_ind_app_EQ1` evaluates the already-existing `path_ind_sec` on
the Sigma-pullback motive at `(y,p)`. The section-level fold exposes
`fib_cov_transf` before the component projection can use its ordinary owner.
A second proof-time rule therefore compares only the reflexive component with
the terminal-source constant functor. Its outer heads are rigid, and its
result returns the exact `K/F/G/k` PathOut/Sigma-pullback presentation as four
residual constraints; it is not a general constant-component equation.
`path_cat_path_ind_app_agrees_structured_EQ1` then proves the general
comparison by `ind_eqr`, and
`path_cat_path_ind_app_agrees_ind_eqr_EQ1` composes both theorems.

This classification is intentionally asymmetric at runtime. Primitive J
retains its reflexivity reduction. Structured transport and the existing
section application do not definitionally reduce to `u` at reflexivity; their
agreement is proof-time/propositional, preserving the directed kernel's
normal forms. Broad runtime identity repairs were rejected at `1008/157` and
`1005/157`, and a runtime uncurrying bridge was rejected at `973/157`. The
selected two `unif_rule`s leave runtime negatives, warnings at `971/157`, and
the strict audit at zero/45/27. No decoder, encoder, opaque transport theorem,
or parallel eliminator was added.

The third slice closes the equivalence-valued-transport item natively in EQ1.
`omega_equiv_along_fapp1_fapp0_EQ1(F,u)` proves that ordinary functor action
preserves fixed-arrow EQ1 evidence: it maps the separate left and right
inverse arrows, applies the functor action to each equality law with `eq_ap`,
and relies on the existing global functor identity/composition owners for the
target endpoints. Both selected inverse projections therefore compute on the
explicit result package.

For `g : IsGroupoidalCat_EQ1(C)` and `f : Hom_C(x,y)`, the already-selected
path `groupoidal_arrow_to_path_EQ1(g,f)` and its reverse define
`groupoidal_arrow_inverse_EQ1(g,f)`. The pointwise re-inclusion theorem rewrites
the original arrow to `path_to_hom` of that path, while the existing J-derived
object-path laws provide cancellation. Consequently
`groupoidal_arrow_equiv_along_EQ1(g,f)` is a transparent explicit
`OmegaEquivAlong_EQ1(C,f)` package, not a capability declaration. Applying
the generic preservation theorem to `D : Catd(C)` yields
`groupoidal_fibre_transport_equiv_EQ1(g,D,f)`: the existing displayed action
`fapp1_fapp0(D,f)` is an equivalence between its two fibres, and its inverse
projection computes to action along the selected inverse arrow. This slice
adds no rule, unifier, primitive decoder/encoder, or transport axiom.

`AllArrowsEquiv_EQ1(C)` is the transparent pointwise classifier
`Pi x y, Pi f : Hom_C(x,y), OmegaEquivAlong_EQ1(C,f)`, and
`groupoidal_all_arrows_equiv_EQ1` computes pointwise to the explicit arrow
package above. This establishes the coherent-core-to-pointwise direction.
The converse is not silently postulated: pointwise choices alone do not yet
assemble the coherent omega-functor `C -> Core_cat(C)` required as the inverse
of `Core_incl_func(C)`. A reverse theorem therefore needs a reusable
structured omega-functor assembly/extensionality owner (or a revised primary
definition), not an opaque equality/equivalence decoder.

A bounded follow-up first located and then closed the former
native-next-hom coherence gap. Replacing the D0 observations by
`path_to_hom` of the two EQ1 functor laws is sufficient to define all
forward/reverse transformations and components, compare the two chosen
inverse functors, and construct both endpoint-correct inverse hom functors.
A generic J theorem proves that the hom action of any `H = id_A`, conjugated
by the path components, equals the identity. The candidate left inverse
composed with `F_1` definitionally normalizes to that generic conjugation, so
the left EQ1 law is available without D0b.

The raw right composite deliberately does not normalize to a hand-written
conjugation normal form. Its two endpoint equations are the triangle
coherences obtained by half-adjointifying separate left/right bi-inverse
data. Those coherences are now derived by the generic transparent
`half_adjoint_counit`/`half_adjoint_triangle` theorem family from `ind_eqr`,
`eq_ap`, homotopy naturality, and path cancellation. The generic theorem is
promoted in the active equality algebra; arbitrary formation, adjusted-counit
computation, and triangle-proof computation at reflexivity are permanent
diagnostics. It introduces no rewrite, unifier, primitive, decoder, encoder,
or opaque capability.

Using that theorem, `omega_equiv_along_fapp1_EQ1` constructs both hom-functor
laws and a native package for every `fapp1_func(F,x,y)`; both selected inverse
observations compute. The proof does not force the raw composite to become
judgmentally equal to the intermediate conjugation: it uses explicit
associativity paths, the restricted J-derived hom-action square for a
structured functor path, and the two triangle endpoint paths.

The public extraction is now complete without copying the exploratory file.
The hom-action proof core has one ordinary public owner and 56 protected
transparent proof helpers; the module then defines its public groupoidality
consumers from that owner. Lambdapi rejected `private` helpers because a
public transparent definition's generated rule cannot retain private symbols;
the measured protected-helper pattern passes and preserves computation.
External consumer diagnostics check formation, both inverse projections, both
law projections, and reflexive normalization of the selected inverse to
`id_func`. No opaque theorem or bodyless capability was used.

The literal specialization of the generic half-adjoint selected inverse is
well typed but does not definitionally return the input path. That negative is
permanent for this owner: the general hom-action construction is not the
literal `path_equiv_EQ1(p)` package, which remains the direct computational
owner and does reduce to `p`. Quiet and warning-enabled owner-position probes are
`evogj_phase6_stable_product_path_owner_full-20260717-111904.log` and
`-112038.log`; the focused literal negative is
`univalence_sigma_ind_query-20260717-112006.log`. The exact-J follow-up is
measured by quiet `-125121.log` and warning-enabled `-125131.log`; the rejected
orientations and their counts are recorded in the probe ledger above. The
focused native-transport probe is
`evogj_groupoidal_transport_equiv-20260717-133457.log`; active-owner promotion
also caught and repaired an initial declaration-order placement before
`Fibre_cat`. The expanded reviewer example passes in
`groupoidal_structured_j_eq1-20260717-134053.log`; after relocation and native
migration it passes again in `groupoidal_structured_j_eq1-20260717-173312.log`.
The native-next-hom follow-up reaches the full package in
`evogj_eq1_native_hom_action_formation-20260717-160813.log`; its generic
refactor and direct category-object specialization pass in `-162016.log` and
`-162055.log`. The actively promoted generic theorem and its reflexive
computational diagnostics pass the focused
`evogj_half_adjoint_active-20260717-162534.log` and bounded `make check`.
Protected-helper feasibility is isolated in
`evogj_protected_transparent_helper-20260717-171150.log`; the extracted and
active modules pass in `evogj_native_eq1_hom_action_module-20260717-171214.log`
and `emdash3_2_eq1_hom_action-20260717-173254.log`; the external computation
example passes in
`equality_valued_omega_equivalence_hom_action-20260717-173305.log`.
The synchronized checkpoint has 1,896 diagnostics across 69 areas (1,664
positive and 232 negative), a 21,986-line kernel with 892 symbols and a
2,791-line/69-symbol derived extension. The kernel retains 597 rewrite rules
and 67 unification rules; the extension adds neither. All 48 health/example
files pass, with unchanged `971/157` warnings and zero/45/27 audit results.
Synchronized 48-file CI passes with 172.350s of measured checking time.

Phase 9 is complete at the selected forward MVP boundary. The native all-EQ1
hom-action theorem, groupoidality consumer relocation, pointwise all-arrows
view, explicit equivalence-valued structured transport, and literal
`path_ind_sec`/`ind_eqr` comparison are active. The converse from arbitrary
pointwise all-arrows evidence to a coherent core-inclusion equivalence remains
an extension gate: it requires assembling and proving the laws of an inverse
omega-functor `C -> Core_cat(C)`. This is not a missing decoder, inverse-hom,
or half-adjoint coherence theorem and is not required for the selected
structured-groupoidality MVP.

Exit criterion: the documented groupoidal `J` story is executable and uses
existing directed action rather than a parallel transport calculus.

### Phase 10: Core-universe inclusion functors — deferred until a concrete consumer

The original goal requires an actual inclusion functor only when a structured
motive uses a groupoid/truncated universe as its codomain. A final source and
consumer audit found no `GrpdCore_cat`, `GrpdCore_incl_func`, or existing
structured motive that needs such an inclusion. Current motives already enter
the MVP as `D : Catd(C)`, and all promoted groupoidal-J/transport consumers use
that public boundary directly.

Speculatively defining
`Path_cat(Grpd_grpd) -> Cat_cat`, with object action `A |-> Path_cat(A)`, would
not be a mere carrier projection. Its arrow action must turn a direct-univalent
facade path into a coherent category functor and its higher action must remain
iterable. That is feasible, but it introduces a new action owner whose laws
should be selected by its first real motive consumer. Adding it now would
violate the plan's own consumer-led rule.

Decision: Phase 10 is not selected for this MVP and is not a blocker. Reopen it
when a concrete groupoid-valued or finite-dimensional structured motive is
ready; then begin with `GrpdCore_cat := Path_cat(Grpd_grpd)`, implement one
actual inclusion functor, and prove that motive uses it. Additional truncated
or `NCat` inclusions and full subcategories remain later work.

### Phase 11: Former-action simplification — completed at the selected boundary 2026-07-17

The consumer inventory found that the Sum-specific bases, componentwise
`eq_ap` comparisons, and registered `sum_obs_action` were used only by their
own diagnostics and reviewer example. `sum_map` itself is an ordinary useful
eliminator-owned map and remains in the kernel. The former-specific block was
therefore mechanically extracted, without changing a definition, rule, or
theorem body, into the one-way library module
`emdash3_2_sum_observational_action.lp`:

1. the two stable basis heads and their four proof-time comparisons moved out
   of the kernel;
2. the component/basis/outer comparison paths and arbitrary inl/inr `eq_ap`
   theorems moved with them;
3. the registered componentwise Sum `ObsAction` map, coherence, and package
   moved into the same module;
4. diagnostics and `examples/sum_observational_action.lp` explicitly import
   the library module;
5. generic `ObsAction`/`ObsDAction`, semantic `eq_ap`/`eq_apd`, Nat successor
   action, decoded Sum, `sum_elim`, and `sum_map` remain kernel assets;
6. no native EQ1, univalence, groupoidality, structured-J, or truncation
   consumer imports the Sum module.

This extraction does **not** claim that groupoidal `PathOut`/J definitionally
replaces `ObsAction`. `ObsAction(f)` registers a chosen computational action
for a raw groupoid function and proves that it agrees with `eq_ap`;
`ObsDAction` does the same for a raw dependent section and `eq_apd`.
Structured J instead consumes an already functorial `Catd` motive. Turning a
raw `f : A -> B` and selected path action into an iterable functor
`Path_cat(A) -> Path_cat(B)` would be a useful later library constructor, and
its first hom action might then subsume or present `ObsAction`. No such
constructor is currently required by a native EQ1 consumer, while Nat and
dependent-PathRecord registrations remain real retained consumers. Therefore
generic `ObsAction`/`ObsDAction` and those registrations stay in the kernel at
this compatibility boundary; they are not a second univalence, transport, or
fibrancy foundation.

Focused probes pass for the reduced kernel, extracted module, full checks, and
reviewer example in `emdash3_2-20260717-185130.log`,
`emdash3_2_sum_observational_action-20260717-185132.log`,
`emdash3_2_checks-20260717-185134.log`, and
`sum_observational_action-20260717-185137.log`.

Exit criterion met: the useful Sum action remains checked library surface, but
its former-specific proof-time bridges are no longer foundational kernel
authority. New former registrations remain paused unless a concrete consumer
cannot use generic action or a separate library module.

### Phase 12: Consolidation and next-scope decision — completed 2026-07-17

The selected endpoint decisions are now fixed:

1. `_EQ1` names remain the explicit native namespace while legacy names are
   still public compatibility APIs; removing suffixes now would combine an API
   rename with compatibility retirement and is not an MVP requirement;
2. the native fixed-arrow/facade, hom-action, groupoidality, structured-`J`,
   evidence-property, and finite-truncation chain is decoder-free and forms one
   coherent public API across the kernel and two one-way transparent modules;
3. the Sum-specific action is a downstream library module, not kernel
   univalence authority;
4. raw unreified-path projection computation, pointwise-to-coherent-core
   assembly, full legacy decoder retirement, and a first core-universe
   inclusion without a consumer are extension gates, not hidden MVP gaps;
5. HITs and truncation reflectors still need their own bounded architecture
   plan because structured `Catd` motives do not automatically make arbitrary
   raw higher-inductive motives fibrant;
6. the preferred next engineering work is a small standard-library consumer
   of the public native API. Semantic consistency, normalization,
   stratification, and universe-size work remains a separate research track.

The integrated public example `examples/groupoidal_structured_j_eq1.lp` now
uses equality-valued equivalence, coherent groupoidality, explicit displayed
transport equivalence, unrestricted evidence uniqueness, structured
`PathOut`/J comparison, and finite object truncation without a decoder or
private helper. Its focused probe passes in
`groupoidal_structured_j_eq1-20260717-185558.log`.

The final synchronized snapshot has 1,917 diagnostics across 70 areas (1,684
positive and 233 negative), zero unclassified checks, a 21,762-line/887-symbol
kernel with 596 rewrite rules and 63 unification rules, a
2,791-line/69-symbol hom-action extension, a 1,407-line/60-symbol
evidence-property extension with no explicit conversion authority, and a
430-line/12-symbol Sum library owning the four extracted proof-time
comparisons. All 51 measured source/example files pass. The kernel warning
inventory remains `971/157`, and the strict LHS audit remains zero unreviewed
clauses with 45 annotated slots across 27 intentional clauses. `make check`,
`make examples`, catalog generation/check, health, warning summary, strict
audit, and synchronized `make ci` all pass; CI measured 100.845s.

Exit criterion met: one native public equality/equivalence/groupoidal-J API is
active, the old D0/decoder surface is classified only as compatibility, all 25
acceptance criteria are met at their stated boundary, and the full validation
suite is synchronized.

## Recommended First Implementation Slice

The original entry slice below is retained as implementation history and is
complete. The previous continuation, `EVOGJ-GROUPOIDAL-CAT`, is also complete
at its selected forward boundary. The irreducible transparent proof was too
large for the monolithic kernel, so the selected one-way extension shape is
active: `emdash3_2_eq1_hom_action.lp` imports `emdash3_2.lp`, exposes
`omega_equiv_along_fapp1_EQ1`, and keeps its transparent proof helpers
protected. Diagnostics and reviewer examples import that extension. The
general groupoidality/structured-transport definitions were relocated there
and migrated from D0b to the native owner; the kernel does not import the
extension.

`EVOGJ-EVIDENCE-PROP`, `EVOGJ-NCAT-TRUNC`, and the selected foundational
`EVOGJ-DECODER-MIGRATE` boundary and Phase-12 synchronization are complete.
There is no remaining dependency-ready implementation slice required by the
selected MVP. A later task may choose a concrete standard-library
consumer, a consumer-led core-universe inclusion, legacy compatibility
retirement, reverse coherent-core assembly, or a separately planned HIT, but
none should be silently appended to this goal.

At adoption, the first implementation task was
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
| Direct classifier use | raw terms are accepted only at measured abstract, shaped, or rigid owners; the unrestricted `lambda p, p` body remains negative, while the uniform stable-view casts have definitional round trips across measured specializations |
| General object-path adapter | forward/inverse/law observers compute through `path_to_hom`, inverse paths, and J-derived witnesses without an opaque encoder |
| Higher iteration | a law is usable at the next hom level through the explicit object-path adapter, or directly only where the relevant classifier owner fires, without a duplicated stored recursive body |
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
5. direct abstract/shaped/rigid classifier use is distinguished from
   computational adapters; the rejected general identity-body cast is not
   advertised as valid, and proof-time unification is not described as
   inserting a cast or observer beta;
6. a transparent general object-path adapter is defined from `path_to_hom`,
   inverse paths, and J-derived laws, with computational forward/inverse/law
   observations and no opaque encoder capability;
7. equality laws are usable as next-hom equivalences through explicit
   reification, with cast-free direct use claimed only at measured owners;
8. `Path_cat` has a coherent classifier join and explicit `path_equiv`
   term-observer computation, with raw-coerced behavior honestly classified;
9. `IsGroupoidalCat(Path_cat A)` is constructible;
10. at least one nonliteral internally groupoidal category is consumed;
11. structured groupoidal `J` is expressed through existing `PathOut` action,
    and displayed transport along a groupoidal arrow has explicit native EQ1
    equivalence evidence;
12. primitive `ind_eqr` remains available for unstructured motives;
13. rigid Cat-universe direct equality remains finite under the new payload;
14. the `Grpd_cat` function-path hom boundary and proof-time pointwise
    identity/composition comparisons are active;
15. both `TypeEquiv` comparison directions are derived without a new opaque
    bridge capability, and the existing `is_equiv_map_by_inverse` theorem is
    proved or explicitly retained in the trust ledger;
16. Grpd-universe direct identity has a selected, explicitly trusted owner;
17. the native foundational theorem chain no longer depends on an arbitrary
    encoder/decoder capability; still-used legacy decoder APIs are explicitly
    classified as compatibility/library surface rather than a duplicate
    foundation;
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
| abstract identity-body experiment across generic unification | valid while the category remains syntactically abstract | Product specialization fails after equality decoding | rejected as a general exported cast |
| transparent general object-path adapter | high by path/core functoriality and J | demonstrated with forward/inverse/law computation at unchanged `971/157` warnings | high |
| stable Product path-view head | high as an explicit presentation of the existing decoded path classifier | promoted with carrier identity adapters, construction/elimination, shaped EQ1 comparison, specialization checks, and unchanged warnings/audit; public cast aliases now use the uniform view | high |
| uniform stable equality/EQ1 cast view | high as an explicit presentation of the already trusted direct classifier equation | carrier reduction plus one direct unifier supports transparent typed-let casts across all measured specializations at unchanged warnings/audit | high; selected explicit interface |
| opposite-only intermediary | high because opposite preserves objects | passed as a Phase-6 intermediate, then became redundant under the uniform view | retired from active kernel |
| primitive nonreducing general/reverse cast term | mathematically expressible as trusted coercion | easy to declare, but opaque without observer rules and adds authority | unnecessary fallback, not selected |
| explicit `path_equiv` observers | high | demonstrated without warning delta | high |
| raw silently coerced path observers | high extensionally | current direct rules do not join | medium-low until extensionality design |
| `Path_cat` classifier join | high | demonstrated as proof-time equation | high |
| runtime `Path_cat` join/package collapse | high extensionally | current candidate adds critical pairs/divergence | low for present orientation |
| `Core_incl(Path_cat) == id` | high | high as narrow comparison | high |
| `IsGroupoidalCat` via core inclusion | high under global univalence | high | high |
| structured groupoidal `J` via `PathOut` | high | most machinery already active | high |
| generic variable-`C` univalence | plausible/intentional | promoted proof-time owner works directly while abstract; uniform explicit casts remain stable across all measured specializations | high for explicit term interchange, medium foundational |
| rigid Cat direct identity | already operational | stable-facade retarget promoted and finite | high |
| `Grpd_cat` function-path hom boundary | high | demonstrated; broad runtime alternative rejected | high |
| `TypeEquiv <-> OmegaEquiv(Grpd_cat)` | standard mathematics | both directions plus transparent quasi-inverse-to-fibre contraction are active | high |
| redesigned Grpd direct identity | high | rigid EQ1 runtime owner promoted over the completed function-path boundary | high operational, medium foundational |
| evidence property for groupoids/finite levels | high | transparently active | high |
| evidence property for unrestricted native EQ1 | high for separate bi-inverse evidence | transparently active through composition-map equivalences and record eta | high |
| unconditional finite-`NCat` object truncation | high | transparently active with base/successor computation | high |
| core-universe inclusion functors | high | medium-high once a concrete action consumer fixes the owner | deferred by the consumer-led MVP boundary |
| full subcategories of `Cat_cat` | high but unnecessary for MVP | medium/large scope | deferred |
| native decoder independence | high | demonstrated across both native extensions and public examples | high; complete |
| full legacy decoder retirement | high after consumer migration | medium due compatibility breadth | optional/deferred |
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

### Risk 5: fixed-arrow evidence is not proposition-valued — resolved for native EQ1

Resolution: separate left/right inverse data makes each half a homotopy fibre
of an explicit composition equivalence. The unrestricted transparent theorem
and finite-`NCat` truncation are active without an assumed global capability.
Keep the legacy opaque-D0 question distinct and retain the evidence-property
diagnostics so later representation changes cannot silently reopen it.

### Risk 6: groupoidality is conflated with discreteness

Mitigation: define `IsGroupoidalCat` independently; make `IsDiscreteCat` the
additional set-object specialization; add non-discrete groupoidal examples.

### Risk 7: structured motives are claimed to solve arbitrary fibrancy

Mitigation: state the restriction explicitly. `Catd` solves transport and
coherence only for motives supplied as functors. The walking child consumes
that structured interface, but raw families and generic HIT formation remain
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
abstract proof-time comparison gives a raw path no observer beta, retain the
historical unrestricted-`lambda p,p` specialization failure together with the
selected Product/opposite local repairs, and reject the measured package-
collapse/runtime-projection rules until a genuine joining theorem and all
eliminator critical pairs pass.

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
| Property-valuedness of separate-left/right evidence | transparently proved at unrestricted native-EQ1 scope; finite object truncation is consequently unconditional, while semantic model questions remain metatheory |
| `IsGroupoidalCat(C) := EquivAlong(Core_incl_func C)` | accepted as leading coherent definition; its pointwise all-arrows comparison is promoted in the forward direction, while the converse needs coherent inverse-functor assembly |
| Transparent Sigma versus stable facade | resolved in favor of the stable facade by the term-decoding probe; Sigma retained as comparison view |
| Generic object univalence owner | proof-time generic rule promoted for the abstract owner, with rigid runtime universe owners, the shaped `Path_cat` join, stable Product equality, and uniform explicit casts after specialization |
| Type view versus computational adaptation | unrestricted un-staged identity body rejected; uniform carrier-view identity casts promoted; transparent `object_path_equiv` remains the path-to-package computation owner; no primitive nonreducing cast term is active |
| Direct Grpd-universe representation | completed function-path boundary and direct rigid EQ1 runtime owner; `TypeEquiv` retained as an explicit derived/library comparison |
| Minimal path observer interface | explicit `path_equiv(p)` computes; raw silently coerced projections are deferred |
| `Core_incl_func(Path_cat A)` orientation | proof-time comparison selected; runtime fold unnecessary for the MVP |
| `PathOut` sufficiency | selected MVP boundary closed: literal `Path_cat` comparison, nonliteral groupoidal consumers, and equivalence-valued displayed transport are executable; arbitrary unstructured motives remain outside the claim |
| Decoder APIs worth retaining | resolved for the MVP: native theorem modules are decoder-free; `TypeEquiv`, shaped computation, and theorem-level round trips remain explicit compatibility/library APIs until consumer-led retirement |
| Remaining `ObsAction` scope | resolved only for this MVP: generic registries retain real Nat/PathRecord consumers, Sum registration is downstream, and structured Cat-valued transport uses ordinary functor action; a future `Path_cat`-functor constructor may recast the registry as its first hom-action view |
| Semantic sanity vehicle | finite `NCat`/dimension-indexed approximants are the preferred local explanation; external systems remain inspiration, not implementation templates |

Additional external mathematical review is most valuable for two points: the
semantic status of the broad object-univalence unifier, and whether a concrete
nonliteral groupoidal `PathOut` consumer exposes a missing naturality law.

## Side-Task Ledger

Kernel-promotion rows are active according to their dependencies after the
2026-07-17 adoption. A "preliminary probe passed" result records review
evidence only, not active implementation. Completed predecessor work is
recorded in the July 13 ledger and should not be duplicated here.

| Task ID | Initial status | Purpose | Dependency | Status-changing result |
| --- | --- | --- | --- | --- |
| `EVOGJ-ARCH-REVIEW` | **completed; adopted 2026-07-17** | independent review and adoption decision | this report | user implementation handoff explicitly adopts the overlay at baseline `4315137...` |
| `EVOGJ-ALONG-EQ-LAWS` | **completed; promoted 2026-07-17** | decoded equality-valued fixed-arrow representation | adoption | 14 permanent diagnostics; unchanged 971/157 warnings and zero/45/27 audit; catalog/health/examples and 41-file CI pass |
| `EVOGJ-PACKAGING-FORK` | **completed; promoted 2026-07-17** | promote stable facade and Sigma comparison | equality-law candidate | stable facade/eliminator/eta and Sigma comparison promoted; transparent-Sigma failure reproduced; 23 diagnostics plus reviewer example; warnings/audit unchanged and synchronized 42-file CI passes in 110.340s |
| `EVOGJ-STABLE-OBSERVERS` | **completed for selected MVP boundary** | package/reflexivity/explicit-path observations | packaging candidate | facade, general object-path, and explicit literal-path observations are promoted; silently coerced raw-path projection is measured-rejected and remains an extension gate |
| `EVOGJ-OBJECT-PATH-ADAPTER` | **completed; promoted 2026-07-17** | separate proof-time classifier use from transparent computational reification through `path_to_hom` and J | stable facade and equality-law evidence | general adapter and all forward/inverse/law observations promoted; later Phase-6 evidence rejects the abstract identity-body experiment as a general cast |
| `EVOGJ-PATH-CAT-JOIN` | **completed; promoted 2026-07-17** | identify path-category equivalence with path equality | equality-law package and facade | shaped proof-time join and explicit path package promoted; raw observer re-rejected at 972/160; 23 diagnostics and reviewer coverage; synchronized 42-file CI passes in 84.865s |
| `EVOGJ-PATH-CAT-GROUPOIDAL` | **completed; promoted 2026-07-17** | prove `IsGroupoidalCat(Path_cat A)` | path join/core identity | Core comparison and canonical witness promoted with inverse/law observations; nonliteral general consumer remains owned by `EVOGJ-GROUPOIDAL-CAT` |
| `EVOGJ-OLD-NEW-BRIDGE` | **completed; promoted 2026-07-17** | migrate current D0 evidence | promoted equality-law candidate plus retained D0 | both explicit directions promoted; new-to-old recursive cells use `object_path_equiv_EQ1`, not the legacy encoder; two recursive levels, Product/opposite/D0b consumers pass; D0 eta/round trips remain explicitly unavailable; synchronized 44-file CI passes in 237.578s |
| `EVOGJ-GRPD-CAT-BOUNDARY` | **completed; promoted 2026-07-17** | complete function-path hom and pointwise identity/composition interface | selected facade and literal path boundary | whole function-path hom plus stable pointwise owners and two typed proof-time comparisons; broad runtime lambdas remain rejected; warnings/audit unchanged |
| `EVOGJ-TYPEEQUIV-BRIDGE` | **completed; promoted 2026-07-17** | derive `TypeEquiv <-> OmegaEquiv(Grpd_cat)` | Grpd boundary and fixed-arrow evidence | both adapters are defined; selected projections and forward-map round trip compute; no decoder or new bridge capability; 23 Phase-4 diagnostics and a 12-positive/5-negative reviewer example pass; subsequent synchronized 44-file CI covers the slice |
| `EVOGJ-QINV-FIBRE-PROOF` | **completed; promoted 2026-07-17** | close bodyless `is_equiv_map_by_inverse` | active H0 path/Sigma machinery and generic half-adjointification | transparent left-J fibre contraction plus re-centring preserves the selected centre and removes the former rewrite/theorem capability; focused and active probes pass |
| `EVOGJ-DIRECT-UNIV-GENERIC` | **completed for the abstract owner; promoted 2026-07-17** | generic object equality/equivalence comparison | stable package, shaped joins, and completed migration bridge | typed bidirectional firing and runtime negative promoted at unchanged warnings; generic runtime rule rejected; Product/opposite specialization is now covered by the completed stable-former task rather than by broadening this owner |
| `EVOGJ-DIRECT-UNIV-CAT` | **completed; promoted 2026-07-17** | retarget rigid Cat direct rule | equality-law package and generic owner decision | direct EQ1 runtime normal form, explicit reflexivity observers, legacy compatibility boundary, and finite self case promoted |
| `EVOGJ-DIRECT-UNIV-GRPD` | **completed; promoted 2026-07-17** | replace finite TypeEquiv view as primary identity | stable package, promoted derived bridges, and migration evidence | direct rigid EQ1 runtime owner promoted; finite `GrpdPathView` remains an explicit compatibility/library surface; synchronized 45-file CI passes in 212.406s |
| `EVOGJ-STABLE-FORMER-PATH-VIEW` | **completed for Product; opposite intermediate superseded 2026-07-17** | make measured reduced-former equality comparable with EQ1 through stable heads | promoted abstract/rigid direct owners and measured Product failures | `ProductPathView` preserves the decoded Sigma carrier with construction/elimination and shaped comparison; the Phase-6 `OpObjectPathView_EQ1` intermediate passed but is removed after the uniform cast view generalized its role |
| `EVOGJ-STABLE-GENERAL-CAST-VIEW` | **completed; promoted 2026-07-17** | provide explicit equality/EQ1 casts without an opaque term operation | failed unrestricted alias plus successful former-local staging | carrier-decoded `ObjectPathCastView_EQ1` and two transparent typed-let casts pass abstract/Product/Op/nested/Path/Functor/Cat/Grpd round trips and observer negatives at unchanged `971/157` and zero/45/27; Product/opposite aliases route through it |
| `EVOGJ-PRIMITIVE-CAST-FALLBACK` | deferred fallback, not selected | provide a cast if the uniform stable view fails a future representation | failed unrestricted alias and completed general stable view | no primitive nonreducing cast term is needed; any future symbol must be narrowly typed, explicitly trusted, initially nonreducing, and justified by a real consumer |
| `EVOGJ-DECODER-MIGRATE` | **completed at the selected foundational boundary 2026-07-17** | remove native foundational decoder dependency without deleting useful compatibility APIs | direct universe owners plus uniform cast view | standalone `cat_univalence` is removed and three real consumers use `object_path_equiv_D0`; exact-token inventory retains genuine legacy decoder consumers, but both native extension modules and all three native public reviewer examples contain zero Cat/Grpd decoder, D0/D0b, or D0/EQ1 migration references. Further role-by-role deletion is optional compatibility work |
| `EVOGJ-EVIDENCE-PROP` | **completed; promoted 2026-07-17** | prove fixed-map evidence property | equality-law evidence plus transparent quasi-inverse theorem | composition-map equivalences contract both inverse-law fibres and native record eta contracts the evidence; unrestricted native-EQ1 property theorem, path/local-set sanity proofs, diagnostics, and reviewer example pass without new conversion authority |
| `EVOGJ-NCAT-TRUNC` | **completed; promoted 2026-07-17** | discharge conditional object truncation | native evidence property and retract closure | transparent arbitrary-level retract closure and `CatDim` recursion prove unconditional `ncat_obj_trunc_EQ1`; base/successor equations pass; legacy D0 conditional theorem is compatibility-only |
| `EVOGJ-GROUPOIDAL-CAT` | **completed at selected forward MVP boundary; promoted 2026-07-17** | general internal groupoidality | path-category introduction | transparent native next-hom owner promoted in the one-way derived extension; protected proof helpers preserve public projection computation; groupoidality and displayed transport were relocated and migrated off D0b without public-name changes; coherent groupoidality computes to `AllArrowsEquiv_EQ1`; the converse remains an explicitly separate coherent omega-functor assembly/extensionality gate |
| `EVOGJ-BIINV-ADJOINTIFY` | **completed; promoted 2026-07-17** | derive coherent triangle laws from separate equality-valued left/right inverse data | native EQ1 evidence, functor/transfor naturality, path algebra | generic adjusted counit and triangle are transparent derived theorems; arbitrary formation and reflexive computation pass permanent diagnostics, with no rule, unifier, primitive, or opaque capability; they close the two endpoint equations in the complete native-next-hom probe |
| `EVOGJ-GROUP-J` | **completed at selected MVP boundary; promoted 2026-07-17** | structured groupoidal `J` comparison | groupoidal category and PathOut | existing `path_ind_sec`, displayed functor action, and primitive `ind_eqr` are propositionally compared at a literal `Path_cat` source through two warning-neutral proof-time joins; primitive J computes at reflexivity and directed presentations retain runtime negatives; generic functor preservation plus explicit groupoidal-arrow evidence proves displayed transport equivalence-valued without a decoder or transport axiom |
| `EVOGJ-UNIVERSE-CORE-INCL` | **deferred; not selected for this MVP** | actual package-core functor into `Cat_cat` | a concrete structured motive that needs a groupoid/truncated universe codomain | source/consumer audit found no current use; do not invent a new higher action owner before its first consumer fixes the required computation |
| `EVOGJ-SUM-SIMPLIFY` | **completed at selected boundary 2026-07-17** | demote action-specific bases while retaining useful library action | consumer inventory | all Sum-specific bases/comparisons/action symbols mechanically extracted to `emdash3_2_sum_observational_action.lp`; only checks/example import it; focused probes pass |
| `EVOGJ-OBSACTION-SCOPE` | **completed at selected MVP boundary; later functor-view refactor open** | decide remaining role of action registry | groupoidal J and former consumers | generic `ObsAction`/`ObsDAction` retain real Nat/PathRecord raw-function consumers; structured Cat-valued transport uses native functor action and does not manufacture that structure. Sum is downstream. A future constructor `Path_cat(A) -> Path_cat(B)` may make the registry a first-hom-action view, but is not an MVP prerequisite |
| `EVOGJ-CONSOLIDATE` | **completed 2026-07-17** | synchronize the selected MVP and close the living overlay | all selected phases | integrated public example and all 51 measured files pass; catalog is 1,917/70 with zero unclassified, warnings 971/157, audit zero/45/27, generated health current, and synchronized CI passes in 100.845s |
| `EVOGJ-H2-READINESS` | **corrected implementation complete through child G8; promoted 2026-07-19** | reassess representative HIT/truncation reflector | consolidated MVP | the child now has opaque `WalkingEnd`, `base`, and `loop`, no `Obj`/`Hom` exposure, and judgmental point/loop beta through the contextual `Functord` eliminator and its ordinary recursor projections. Transparent Code, powers, directed representable decoding, both Hom--Nat inverses, structured/carrier packages, sethood, and directed negative consequences are active without a word carrier or primitive `cell_ind`. Open loop-prefix compatibility is an ordinary equality from generic functoriality, with no custom rewrite or `unif_rule`. Reports, generated health/catalog, warning inventory, audits, and full 55-file CI are synchronized. A reverse BNat functor, full hom-category equivalence, and full functor-category initiality remain outside the selected practical milestone pending reusable generic infrastructure. |
| `EVOGJ-POST-CONSOLIDATE` | **historical task completed 2026-07-18; walking conclusion superseded by reopened H2 review** | reconcile the completed overlay and then-selected child-plan authority/dependency boundaries | completed overlay and former walking MVP | reusable Nat prerequisites were extracted and the then-current diagnostics/reports passed their recorded gates; that validation remains implementation provenance, while its claim that the word-carrier walking MVP satisfied the intended HIT is superseded by `EVOGJ-H2-READINESS` and the reopened child plan |
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
- update this ledger, the active master plan status, Foundations, examples,
  catalog, and health report whenever a conclusion changes; update the current
  status report with promoted architecture facts, but do not turn this plan's
  uniform equality/EQ1 cast-view representation into a repository-wide SOP
  rule;
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

## Future Work Handoff Requirements

With final validation complete, this overlay has no active implementation row
required by the selected MVP. A later handoff should name a new bounded objective rather
than instruct an agent to continue this plan indiscriminately. Candidate
objectives are a public standard-library consumer, a consumer-led
core-universe inclusion, legacy compatibility retirement, reverse coherent-
core assembly, or one explicit walking-HIT strengthening such as generic
abstraction, full initiality, dependent Join elimination, reusable `PathMap`,
or groupoid completion toward `BInt`/Circle.

Any such handoff must still read this report with the July 13 retained-work
ledger and active authorities, preserve current worktree state, reproduce
relevant owner-position evidence, and synchronize source, diagnostics,
examples, reports, catalog, health, warnings, audit, and CI. Commit
`4315137...` remains implementation provenance only; it never authorizes a
reset or rollback.
