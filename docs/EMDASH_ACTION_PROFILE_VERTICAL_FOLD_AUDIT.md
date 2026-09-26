# Action-Profile Integration: Vertical Fold Audit

Date: 2026-09-26

Status: corrected prototype and combined matching/Gray/Gamma/H/Hom consumers
qualified; production promotion and wider requalification remain pending

Owner: [living integration plan](EMDASH_ACTION_PROFILE_INTEGRATION_PLAN.md),
`API-04V`, with the [relative-profile investigation](EMDASH_ACTION_PROFILE_RELATIVE_PROFILE_FEASIBILITY.md)
as its immediate consumer. No production Lambdapi source changes in this slice.

## The Retained Rules Recovered Unprofiled Laws

The pinned source branch and the earlier main-based candidate both retained
three ordinary off-diagonal vertical folds. In schematic notation these are:

```text
eta[Y] o epsilon[f]       -> (eta o epsilon)[f]
eta[f] o epsilon[X]       -> (eta o epsilon)[f]
eta[q] o epsilon[p]       -> (eta o epsilon)[q o p].
```

First proving the third equation for generic transfors, then specializing
both transfors to `id_F`, proves composition preservation for arbitrary raw
`F`. The first two folds similarly recover raw component naturality through
identity specialization. The earlier direct reflexivity negatives missed
this staged proof route. This is a demonstrated failure of the intended lax
boundary, not a claim about every remaining source rule.

`api_vertical_fold_composition_probe.lp` contains the generic proof and its
raw-functor specialization. Its unchanged source passes on the earlier core
and fails at the first generic fold on the corrected core. The corresponding
raw-naturality reproducer has the same before/after result. The new reviewer
also rejects each of the three generic reflexivity proofs independently.

| Same-source control | Earlier positive receipt | Corrected expected failure |
| --- | --- | --- |
| Staged raw composition | `20260926T205026Z-893df48cf6b648eda6e7b132c3412dc9` | `20260926T214140Z-0caf6dbe29ae4cb78122a53167f7a0ab` |
| Staged raw naturality | `20260926T213255Z-3d44a59e5a2d48a4b80117010feb9344` | `20260926T213403Z-55e8a1246efd4ea4a93cc1e4f7238cde` |

Both corrected failures are proof-unification failures within default limits,
not allocation failures or timeouts.

## Profile-Specific Replacement

The full-file candidate comments the three raw clauses at their existing
core position. Five clauses in the existing profile layer retain the same
operations, with these admission boundaries:

| Fold | Required opaque views |
| --- | --- |
| Component of later transfor after action of earlier transfor | Later `LaxTransfor` or `StrictTransfor`; earlier may be raw |
| Action of later transfor after component of earlier transfor | Earlier `StrictTransfor`; later may be raw |
| Both transfors act on successive arrows | Earlier `StrictTransfor`; later `LaxTransfor` or `StrictTransfor` |

The later pre/right profile and earlier post/left profile are distinct.
Full-strict admission supplies both. The candidate does not introduce a new
opaque oplax classifier. An earlier lax view alone fails the second fold;
two lax views fail the third.

The outer composition codomain is explicitly the same `B` carried by the
profiled views. Leaving it inferred allowed the clauses to act on another
composition owner merely because Hom types agreed. That wider variant is
rejected. A focused control checks the distinction between `Psh_cat` and
`Catd_cat` composition presentations.

`api_profiled_vertical_paths.lp` admits actual raw inputs through their
supplied profiles and transports only equality proofs along the existing
carrier paths. Its three result statements retain the original raw transfors,
components and composites. It adds no new raw admission or runtime cast.

## Interchange And Eckmann–Hilton Dependency

Turning off the raw folds first breaks
`hom_postcomp_representable_interchange_eq`. Its three core dependents are
`EH_vcomp_to_shared_middle`, `EH_swapped_vcomp_to_shared_middle` and `EH_comm`.
The active LP reference search found no callers of those EH names outside
the nucleus.

These four proof bodies are commented in the prototype core and restored in
`api_profiled_interchange.lp` after the profile owners. This avoids a reverse
core import. The representable-interchange result now takes full-strict
evidence for its first actual tele-induced transfor and pre-strict evidence
for its second. The EH proofs take full-strict evidence for the actual
whiskering transfor induced by `beta`.

The original EH objects, vertical/horizontal operations and unit observations
stay in the core. Their result equations retain the original `alpha` and
`beta`. An ordinary-Hom consumer derives the required profile from an explicit
`IsNCat(1, Hom_cat B x x)` premise, using the existing ordinary-transfor
adapter. The old unqualified EH call is rejected. This does not establish an
unrestricted intrinsic interchange profile for arbitrary `B`; none is added
as an assumption to preserve the old signature.

The five supporting proof modules contain eleven definitions, including the
four restored names. They add no primitive, rewrite or unification rule.
Production Foundations/status prose still describes production source; its
EH qualification must change with eventual promotion.

## Warning And Owner Review

The focused profile environment changes from 1,038 to 999 critical-pair
warnings; the 150 pattern-variable diagnostics are unchanged. Comparing
complete rule-participant templates removes 54 old instances and adds 15.
After mapping unchanged source lines, no old location gains a warning; each
of the five new clauses has three warning instances. The added cases are:

- Seven base-identity overlaps: checked runtime joins.
- Three transformation-identity overlaps: checked paths from existing
  profile-cell evidence, with explicit runtime-nonconversion controls.
- Five terminal-category overlaps: checked paths from the existing
  `unit_is_prop`/contractibility proof, without a new terminal rule.

This is a classified warning delta, not a confluence proof. In particular,
proof-time paths do not make the transformation-identity branches join at
runtime. No extra unit fold is introduced to hide that distinction.

The strict inferred-slot audits report zero unreviewed candidates for the
corrected core and profile owner. The core retains 64 annotated slots across
41 intentional clauses. Subject reduction stays enabled throughout.

The combined whole-matching candidate has exactly the broad vertical
candidate's warning inventory: 1,187 critical-pair warnings and 162
pattern-variable diagnostics. Heads, rule families, complete participant
templates and mapped source locations all have zero deltas; parsing reports
no unclassified warning text.

## Exact Current Qualification

The isolated vertical candidate is
`emdash2/tmp/probes/api_vertical_fold_control/`. Its core SHA-256 is
`dcfacf6cc903f08b92fb45af71a23eb69c3075dfca9fd989bf6c87a111777276`.
Its profile owner is
`a4927422e7f2af0d37e50568ab09dbfebdab969e9fa4142bdbcf66bc9b1c3f33`.

The separate combined package is
`emdash2/tmp/probes/api_vertical_matching_candidate/`, core SHA-256
`169b5d83a105a8fc0b8d416a017ec0c59e8f0d04b44ab2a8e9f35e22b81691fe`.
It applies the already reviewed whole fixed-arrow precomposition unifier at
its existing owner, in addition to the vertical correction. That agreement
retains its status as an explicit whole theory comparison, not an inference
from pointwise equality. Neither earlier package was overwritten.

| Current successful target | Receipt | Positive / negative assertions | Seconds / maximum child RSS KiB |
| --- | --- | ---: | ---: |
| Guarded folds | `20260926T212839Z-e07377a8c94f4770adc21a196cf6ed3b` | 10 / 5 | 7.703 / 432,504 |
| Broad Gray, direct-cover, Gamma/H/Hom, EH and unit review | `20260926T213449Z-febc573e8a3b440ba3d78cd202c173ac` | 344 / 84 | 30.546 / 1,573,060 |
| Generic relative producers and terminal cases | `20260926T214215Z-d924054a85474547b0d5ac3e10b83f14` | 7 / 6 | 7.827 / 433,148 |
| Combined broad review and actual matching/relative/inverse consumers | `20260926T214504Z-e17ae0ad45c8459f8b8656ae0d51ec46` | 423 / 111 | 35.707 / 1,915,920 |

The broad vertical closure has 181 inputs; the combined closure has 207.
Counts include imported assertions; definition bodies also check. Both
packages are source-only with no compiled parents. Runs use warnings,
`OCAMLRUNPARAM=o=20,v=1024`, serial execution and the existing file/core/no-swap
limits. Focused checks use 2 GiB/90s. The broad checks use explicit 3 GiB/180s,
carrying forward the measured import-closure resource qualification rather
than repeating its known 2 GiB allocation failure. Defaults are unchanged.

The manifest
`emdash2/tmp/probes/api_vertical_current_qualification_manifest.json`
binds current source hashes, five successful receipts, same-source negative
controls, proof audits, settings, checker/runner identity and authoring files.
SHA-256: `4e794ec684f63c609d1593a7e52729701aa83b2a7995a078efece756be57b2ed`.
Exact inputs remain in the immutable receipt input store. Detailed warning
records are `api_vertical_warning_delta.json`,
`api_vertical_warning_locations.json` and
`api_vertical_combined_warning_comparison.json` beside the manifest.

## Next Boundary

Use the combined corrected package for the next displayed/profile
investigation. Generic relative identity/path producers, the actual matching
comparison, both selected inverse projections and complete action observations
survive the correction. Relative composition and inverse-assembly sufficiency,
retained-member/base directions and complete rho assembly remain open.

The earlier native-snake, all-path-cubical and Freyd/CAS receipts belong to
their earlier core pin. They do not qualify either changed core. Preserve
those results as regression targets and requalify their affected closure
before promotion. Directed/simplex consumers, TypeScript, production owner
migration, registry/catalog/health/book updates and final integration gates
remain required. No production global cut has been retired by this audit.
