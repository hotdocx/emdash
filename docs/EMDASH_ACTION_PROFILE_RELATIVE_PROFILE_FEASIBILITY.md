# Action-Profile Integration: Relative Profile Feasibility

Date: 2026-09-26

Status: prototype identity/path/selected-inverse producers and actual matching
consumers pass; inverse-assembly use remains unselected

Owner: [living plan](EMDASH_ACTION_PROFILE_INTEGRATION_PLAN.md), `API-05`.
This follows the
[whole matching-action comparison](EMDASH_ACTION_PROFILE_MATCHING_ACTION_FEASIBILITY.md)
and refines the profile question in the
[displayed assembly investigation](EMDASH_ACTION_PROFILE_DISPLAYED_ASSEMBLY_INVESTIGATION.md).
The existing full-strict profiles and pointwise assemblers are unchanged.

## Identity Boundary Of The Stronger Profile

The current definitions give checked conversions in both directions:

```text
IsPostStrictTransfor(id_F) <-> IsStrictFunctor(F).
```

Projecting the post field therefore gives
`IsStrictTransfor(id_F) -> IsStrictFunctor(F)`. This does not assert the
unproved converse for full strictness. The corresponding displayed identity
calculation shows that the earlier candidate's fibre factor forces
`IsStrictFunctor(Fibre_func(FF,x))` for every `x`.

That is a valid stronger property, not an error in the existing strict
classifier. It must not be inferred automatically for raw endpoint functors.
In particular, a path-induced transformation between retained lax endpoints
does not, merely by being path-induced, supply this absolute full-strict
profile. The actual consumer must determine which action condition is needed.

`api_identity_profile_boundary.lp` proves these four consequences from the
existing definitions. It introduces no assumption or rule.

## Relative Candidate Over Complete Internal Action

`api_RelativeTransforProfile(eta)` compares the existing whole actions with
routes using the actual endpoint functor action and the actual component:

```text
tapp1_at(eta,X)
  = hom_int_precomp(G,eta[X]) o fapp1_at(G,X),

tapp1_con_at(eta,Y)
  = hom_con_int_postcomp(F,eta[Y]) o fapp1_con_at(F,Y).
```

Each equation is between whole internal transfors. It is not merely an
equation between their values on one arrow, or between the Hom-functor
components at a pair of objects. The covariant and native contravariant
owners remain distinct. The routes keep the endpoint functors' existing
lax action through `fapp1_at_transf` and `fapp1_con_at_transf`.

This definition adds no alternate action, blanket admission or inverse
operation. The identity producer uses the existing normal-unit law, staged
before its concrete Hom owners project. It works for every raw `F` without
an `IsStrictFunctor(F)` premise. Path induction then supplies the profile of
`path_to_hom(F=G)` for arbitrary raw endpoints under the same normal-unit
convention.

Both whole Hom-functor observations and the complete next actions project
from the profile fields. The new definitions do not reflect those paths into
runtime conversion. Controls reject raw complete-action comparisons,
reinterpretation of relative evidence as the old full-strict evidence, and
using a path producer as evidence for an unrelated transfor with the same
endpoints.

## Actual Matching Comparison And Inverses

The established whole matching-functor equality now supplies an actual
path-induced comparison transfor, its relative profile, and its existing
`object_path_equiv_along` value. Both selected inverse projections receive
relative profiles through the reversed path. Their fields are read from that
same whole equivalence; no alternative inverse is substituted.

For this path constructor, the left and right inverse slots are both the
same reversed-path arrow by its existing definition. These checks do not
qualify assembly of an arbitrary supplied family of pointwise inverse choices.
They qualify this concrete whole producer and its two stored projections.

The actual complete source and target action consumers pass. The target
action keeps the native source
`Hom_cat (Op_cat A) X W`. Eagerly writing the convertible
`Hom_cat A W X` in the concrete typed consumer failed with an endpoint
unification mismatch, even though the individual endpoint conversions pass
and the inferred native type forms. Retaining the source presentation used by
the owner resolves that check. A further consumer verifies conversion of the
whole functor type and applies the action, and its comparison path, to the
original forward arrow `h : Hom A W X`.

The fix changes a projection's type presentation. It introduces no opposite
rule, arrow transport or kernel change. The broader Op/duality boundary stays
with its separate goal.

## Exact Qualification

The seven new support modules contain 23 definitions and no new primitive,
rewrite or unification declaration. The generic results pass independently
on the unchanged preferred core. The actual matching comparison uses the
separate whole-precomposition candidate already recorded by its parent review.

All runs use subject reduction, warnings, serial execution,
`OCAMLRUNPARAM=o=20,v=1024`, and the normal 2 GiB/90s profile with the existing
file/core/no-swap guards.

| Current check | Receipt | Seconds | Maximum child RSS (KiB) |
| --- | --- | ---: | ---: |
| Generic boundary, relative producers and observations on the earlier core | `20260926T203453Z-1bf977e0c7e94170baaf910c62b2df6b` | 8.731 | 425,736 |
| Actual comparison, both inverses and complete action consumers | `20260926T203145Z-05c415e85da341dcaed00543e6278264` | 13.231 | 1,003,676 |
| Native target source, whole type conversion and original forward-arrow use | `20260926T203314Z-34c88e29577649da98deaae0b9f7b423` | 18.911 | 1,004,672 |

The generic closure has eleven inputs and two positive/six negative
assertions. The actual-consumer union has thirty inputs and ten positive/six
negative assertions, including the generic controls. Definition bodies check
in addition to those assertions.

The generic warning inventory matches its unchanged-core baseline at 1,038
critical-pair warnings and 150 pattern-variable diagnostics. The actual
consumer matches its whole-matching parent at 1,057 and 150 respectively.
Both comparisons have zero deltas in heads, families, locations and complete
participant templates, with no parser issues. The earlier broad interaction
receipts retain their existing scope; they are not rerun merely for these
definition-only additions.

`emdash2/tmp/probes/api_relative_profile_current_qualification_manifest.json`
binds the three current successful receipts, both input closures, the
definition-only audit, assertion counts, earlier unsuccessful annotation
controls and authoring scripts. SHA-256:
`bc4e7fcd13e200d8a156e966e2fc674b33863802164a9cf13e55b051e05fd466`.
The warning manifest is
`emdash2/tmp/probes/api_relative_profile_warning_comparisons.json`, SHA-256
`0536d3470ad9a23513500b74990446adb2b48fc3b6367b34700e7da488ff47c1`.
Exact source is retained by the immutable receipt input store.

The earlier core remains
`ab48a85136935c5183b87bc0341fbb524a58be61083f1bbd9ad2563475df9965`;
the isolated matching core remains
`ee583a558c68354263c86aa76841c3e1403106149a95b55f42ca37aa6514a838`.
Neither core changed in this slice, and no production LP file was promoted.

## Corrected Vertical-Owner Replay

The subsequent [vertical-fold audit](EMDASH_ACTION_PROFILE_VERTICAL_FOLD_AUDIT.md)
found a staged unprofiled-strictness route in the earlier cores. It does not
invalidate the generic relative producer bodies: those unchanged bodies and
their controls also pass with the three raw vertical folds removed and their
profile-guarded replacements installed. The focused receipt is
`20260926T214215Z-d924054a85474547b0d5ac3e10b83f14`.

The actual matching comparison, both selected inverse profiles and complete
action consumers also pass in the separate combined corrected package,
receipt `20260926T214504Z-e17ae0ad45c8459f8b8656ae0d51ec46`. The audit owns its
new core pin, complete 423-positive/111-negative interaction scope and warning
comparison. Earlier exact-pin receipts above remain historical evidence;
neither core was silently overwritten. This replay does not qualify generic
relative composition or inverse assembly.

## Remaining Acceptance

The relative predicate is not yet selected as the sufficient premise for
general inverse assembly. Composition and unit coherence, the relationship
to complete displayed/base action, and retention of arbitrary supplied inverse
choices still need qualification. Identity/path producers alone do not prove
that sufficiency.

The actual full rho construction also still needs its retained-member and
base directions. Preserve those obligations and the three commented
whole-assembly stages. Do not weaken the old strict assembler by substituting
the relative predicate solely because the new producers typecheck, and do
not add an unproved rho-admission axiom to finish the consumer.
