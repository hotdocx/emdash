# Action-Profile Integration: Whole Matching Action

Date: 2026-09-26

Status: guarded comparison and whole matching-parameter proof pass in an
isolated candidate; profile-based rho continuation is deferred research

Owner: [living plan](EMDASH_ACTION_PROFILE_INTEGRATION_PLAN.md), `API-05R`.
The [inherited assembly baseline](EMDASH_ACTION_PROFILE_ASSEMBLY_BASELINE_REVIEW.md)
supersedes the unfinished profile/producer work as a prerequisite for the
first integration milestone. Existing results and their exact qualifications
remain preserved; research-only comparisons need separate promotion review.
This extends the
[retained-member investigation](EMDASH_ACTION_PROFILE_DISPLAYED_ASSEMBLY_INVESTIGATION.md).
The new package is
`emdash2/tmp/probes/api_mapped_precomposition_whole_control/`.
The preferred earlier package and production source remain unchanged.

## Required Whole Comparison

The retained-section proof previously evaluated at an arbitrary matching map
`m`. Lifting it to a whole functor in `m` needs a comparison of whole
precomposition functors:

```text
precompose_along(F,h) = precompose_id(F[h]).
```

The previous core provides this whole comparison only when both categories
are `Cat_cat`. For arbitrary categories, existing point and capped Hom-action
comparisons already describe the same composition data. Two definition-only
proofs establish their agreement on the unchanged core, using the existing
raw-composition and horizontal-composition paths. The no-whole-agreement
control then rejects typed reflexivity for the desired whole functor equation.

The isolated candidate generalizes the existing Cat-specialized unification
clause at its original source position. It keeps two rigid
`hom_precomp_along_func` heads, and checks the actual mapped source, target
and arrow in side conditions. There is no runtime fold or change to the
precomposition projection ladder.

This is a **new whole proof-time agreement in the candidate theory**. The
independent point/arrow proofs support its intended reading; they do not
derive that whole agreement by an extensionality principle. It is not a
strictness admission for arbitrary `F`, nor a claim that its compositor is
an identity.

Typed reflexivity for the whole agreement now passes. Runtime equality still
fails, as do comparisons using an unrelated mapped arrow or a different base
arrow. The existing residual-precomposition reviewers retain their generic-F
composition rejections, classified positive cases, identity-family cases and
both evaluation orders. The old Cat-specialized Γ/H/Hom consumers also pass
in the combined environment.

## Whole Retained-Section Result

Fix an eligible question `q`, a retained member `(p,member)` over `V`, and the
completion `X`. Let `r` be the actual represented pullback map and `e` the
existing retained-member section into the sieve extension. The new result is
an equality of **whole functors**:

```text
precompose_id(r) o glue_q = precompose_id(e)
  : Matching(q,X) -> Section(V,X).
```

`api_cover_retained_matching_functor_path` has no matching-map argument `m`.
Its proof uses the whole glue-substitution path, the two whole precomposition
comparisons, the existing extension-action and retained-factorization paths,
identity-family precomposition accumulation, associativity, and the whole
silent law. These existing supplied boundaries retain their status. No
component square, profile of an arbitrary matching map, primitive inverse,
or new rho admission is added.

The actual consumers retain the next-Hom **functor**, an arbitrary mapped
arrow and the identity-arrow observation. They use dependent path congruence
(`PathOver`) so the original endpoint images and arrow remain explicit.
These are proof observations, not operational arrow replacements. The
identity case checks after selecting the generic normal-unit theorem before
the concrete functors unfold; the direct specialized attempt is retained
as a failed normalization control. Two further controls reject runtime
collapse and reflexivity in place of the derived retained-section path.

This establishes the matching-map direction at fixed `p,member`. It does
not establish the remaining retained-member/base action, a profile of the
existing rho constructors, or any of the three whole inverse-assembly stages.
The displayed profile proposal remains unselected pending both sufficiency
and actual-producer qualification.

## Validation And Resource Evidence

All checks retain subject reduction, warnings, serial execution,
`OCAMLRUNPARAM=o=20,v=1024`, 64 MiB file limits, no core dumps and the no-swap
scope. The focused checks use the normal 2 GiB/90s settings.

| Check | Receipt | Seconds |
| --- | --- | ---: |
| Existing point and capped-arrow paths, unchanged core | `20260926T190128Z-5a31797371eb468c8faabad95cb33116` | 7.796 |
| No-whole-agreement control, one positive/four negative | `20260926T190337Z-a80a63e1a1eb4a47b5f995f53fe28623` | 5.720 |
| Guarded whole agreement, two positive/three negative | `20260926T190415Z-ac048adc144142c6be5b74517b0c32bf` | 5.126 |
| Existing profile and residual-precomposition interactions | `20260926T190552Z-91d1618c7e36468196a99c31c77400e2` | 15.905 |
| Whole matching-parameter proof | `20260926T190848Z-368c328c63be45ccb5cd02a2da03599e` | 12.817 |
| Next Hom, arrow, staged identity and noncollapse controls | `20260926T191506Z-438b36259ad0466396a0011f99570d0c` | 16.985 |
| Combined Γ/H/Hom and matching-action review, 3 GiB/180s | `20260926T191910Z-dc94abf95bc6464db84edd5d64dfe7e5` | 33.849 |

The combined review passes **269 positive and 77 negative assertions** over
156 LP files plus the package descriptor. At 2 GiB/90s, the identical input
snapshot allocation-fails in 33.385s while loading
`emdash3_2_zero_arrow_family_action_paths.lp`, receipt
`20260926T191725Z-96e00f43e1254fb9812934bf31c2f75f`.
The explicitly increased run passes with maximum child RSS 1,884,016 KiB.
RSS is not the address-space limit; this is a measured successful profile,
not a minimal-memory claim. Defaults remain unchanged. The
[resource ledger](EMDASH_ACTION_PROFILE_RESOURCE_QUALIFICATION.md)
records the same scoped exception under the user's standing authorization.

The focused baseline/candidate warning inventories are identical: 1,038
critical-pair warnings and 150 pattern-variable diagnostics, with zero parser
issues. Heads, families, complete participant templates and locations mapped
across unchanged source lines all agree. The strict LHS audit finds zero
unreviewed candidates. These checks qualify the scoped comparison; they do
not establish global confluence or replace the remaining integration gates.

## Pins And Recovery

The earlier core is
`ab48a85136935c5183b87bc0341fbb524a58be61083f1bbd9ad2563475df9965`.
The isolated candidate core is
`ee583a558c68354263c86aa76841c3e1403106149a95b55f42ca37aa6514a838`.
All inherited LP copies otherwise match the preferred package. There are no
compiled objects in the new package.

`emdash2/tmp/probes/api_matching_action_current_qualification_manifest.json`
binds seven current successful receipts, both core versions, 157 candidate
inputs, the exact single-clause delta, assertion counts, resource failure,
failed direct identity specialization and authoring scripts. Its SHA-256 is
`fe82f3216c4b9d864a442b890da18d38d45ce9d4b1e09981d9627cc916c5758e`.
The warning comparison is
`emdash2/tmp/probes/api_matching_action_warning_comparison.json`, SHA-256
`d8ec0bed68e55ea7280ea13ea634981dc0e14438b6745a7a1b7203d756b2d867`.
Use the immutable receipt input blobs for exact emitted-source recovery.

Earlier broad native/CAS/cubical receipts qualify the earlier core. They
must not be relabelled as evidence for this new rule environment, and their
compiled parents must receive the appropriate new dependency qualification
before reuse at promotion. The current source-only interaction review is a
bounded prototype milestone, not production integration.

Next account for the retained-member and base directions, connect the complete
construction to the actual rho owners, and qualify the required profiles and
inverse assembly. Preserve actual maps, both inverse choices and the separate
Op/duality boundary.

The [relative-profile continuation](EMDASH_ACTION_PROFILE_RELATIVE_PROFILE_FEASIBILITY.md)
now gives the path-induced matching comparison, and both inverses selected by
its existing whole equivalence, an explicit relative action profile. Its
identity/path producers need no strict endpoint premise. This checks another
producer obligation; it does not qualify general pointwise assembly or the
remaining retained-member/base directions of rho.
