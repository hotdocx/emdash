# Action-Profile Integration: Inherited Assembly Baseline

Date: 2026-09-27 UTC

Status: selected baseline qualification route; explicit-profile assembly
redesign deferred to follow-up; production promotion remains pending

Owner: [living integration plan](EMDASH_ACTION_PROFILE_INTEGRATION_PLAN.md),
row `API-05`. This supersedes the earlier requirement to solve the explicit
assembly-profile research before completing this integration milestone.

## Decision And Reason

The user proposed and then explicitly confirmed retaining the existing
assembly primitive for the first checkpointed integration baseline, preserving
the explicit-profile work for a later focused reassessment. Review supports
that sequencing. The previous profile investigation has not established a
counterexample to this exact
emdash assembly interface. Its failed or overly strong candidate conditions
are not evidence that the inherited primitive is inconsistent.

The baseline therefore preserves the existing ordinary and displayed
pointwise-to-whole assembly contracts from source tip `114dc19f`, documents
their assumed status, and qualifies their actual consumers on the corrected
lax core. It does not restore the demonstrated generic composition/naturality
leaks. Justified constructor-specific computation remains separately reviewed.
The complete integration goal, original consumers and final gates remain.

## Mathematical Distinctions

Laxness of the endpoint functors, laxness of a transformation's naturality
cells, and the coherence condition on a modification are different data.
The word "lax" alone does not decide a pointwise equivalence criterion.

Johnson–Yau define modifications between lax transformations of lax functors,
and prove that componentwise inverses form an inverse modification. Their
strong-transformation criterion is a separate result for pseudofunctors.
See [Def. 4.4.1, Lemma 4.4.9 and Prop. 6.2.16, arXiv v2](https://arxiv.org/pdf/2002.06055v2).

There is also a genuine qualification in the conventional category of lax
transformations. A walking noninvertible 2-cell between two parallel arrows
gives a lax transformation between walking-arrow diagrams with identity
object components; reversing it would require a missing reverse 2-cell.
Thus equivalence of object components alone is insufficient in that setting.
Related higher-categorical adjoint criteria require naturality or mate
conditions; see [Abellán–Gagna–Haugseng, Cor. 4.2.10](https://doi.org/10.1007/s00029-025-01084-z).

That example is not an emdash counterexample. In particular:

- The kernel describes `Transfd` as modifications between directed-family
  functors. The modification result is a relevant positive analogy.
- The source assembler takes an already formed whole `Transf` or `Transfd`.
  It does not manufacture a transformation from arbitrary unrelated maps.
- Its result is an ambient `OmegaEquivAlong`, carrying two selected inverse
  arrows and equality-valued cancellation laws. It does not declare an
  `IsStrictFunctor`/`IsStrictTransfor` profile or require its inverse to stay
  inside a classified `LaxTransfor` subcategory.
- Matching these primitive omega-level classifiers to a particular external
  model still needs semantic work. Neither the positive modification analogy
  nor the negative lax-transformation example supplies that interpretation.

The accurate remaining cost is an inherited model/interpretation obligation,
not a demonstrated inconsistency. It should be recorded as such. Adding an
experimental strictness condition whose sufficiency is itself unproved does
not automatically resolve that obligation.

## Exact Baseline Contract

Preserve the four original inverse constructors, their four component beta
rules, and four whole cancellation constants, with the derived equivalence
and path facades. Keep the supplied forward transformation and both inverse
choices. The historical `strict_*` names do not constitute a profile premise.
Do not silently strengthen their claims in comments or frontend evidence.

Both ordinary and displayed interfaces are involved: the actual locality
construction assembles an ordinary fibre transformation, a displayed
transformation, and an ordinary outer transformation. Retaining only the
displayed primitive while leaving the newly imposed ordinary guard would
not implement the intended alternative. Existing qualified ordinary helper
interfaces may remain, adapting their internal calls to the inherited
assembler where necessary.

The previously derived retained-member proof is preserved. Reintroducing
the old opaque retained-member constant is unnecessary. The original rho
heads and model/constructor contracts keep their explicit structural status.

## Concrete Trial

`emdash2/tmp/probes/api_inherited_assembly_candidate/` is a separate candidate.
Its assembly owner is byte-for-byte identical to the pinned source owner,
SHA-256 `69f85cdb848dd93471281d8f6cfce89ff44012154f65ce3a160786d6c950040f`.
The core/profile pins remain `b9cc2726` / `f670814a`; none of the corrected
generic strictness rules is restored.

The complete `emdash3_2_direct_cover_completion_locality.lp` now passes,
including all three assembly stages and the final locality interface.
All sixteen original public signatures are preserved. Its retained-member
constant is replaced by the existing checked derived body; no new premise
or assumption is added for that proof.

| Trial | Receipt | Seconds / maximum child RSS KiB |
| --- | --- | ---: |
| Complete locality owner | `20260927T014049Z-bdc149f20af54a32b776a5b630336612` | 16.610 / 786,256 |
| Inherited assembly and noncollapse controls | `20260927T014242Z-6057374277504e21bf60ebc3484d9eff` | 14.506 / 786,536 |

The controls pass eight positive and two negative assertions: both selected
inverse component projections, the displayed whole cancellation projections,
ordinary/displayed formation without a profile argument, and rejection of
generic raw composition/naturality by typed reflexivity. These checks qualify
interface and computation behavior; they do not derive the primitive or
certify every possible consequence of its axioms.

Both runs use 2 GiB/90s, warnings, subject reduction,
`OCAMLRUNPARAM=o=20,v=1024`, serial execution and the existing file/core/
no-swap guards. They are source-only. Both warning inventories report
971 critical pairs and 150 pattern diagnostics, with no parser issues.
The inherited assembler also passes the strict LHS audit with zero candidates.

The 22-input manifest is
`emdash2/tmp/probes/api_inherited_assembly_current_manifest.json`, SHA-256
`66688161de637339329ba5432430a9723aca932e5c0330900808bc25923c5a09`.
It retains exact receipts, input blobs, signatures, settings and authoring
files. This is local prototype evidence; no production LP has been changed.

## Preserved Research And Next Work

The [displayed investigation](EMDASH_ACTION_PROFILE_DISPLAYED_ASSEMBLY_INVESTIGATION.md),
[relative profiles](EMDASH_ACTION_PROFILE_RELATIVE_PROFILE_FEASIBILITY.md),
[matching action](EMDASH_ACTION_PROFILE_MATCHING_ACTION_FEASIBILITY.md) and
[inverse action](EMDASH_ACTION_PROFILE_INVERSE_ACTION_FEASIBILITY.md) remain
recoverable research. Their prior profile-sufficiency, varying-member/base
and FibCov/cone obligations are deferred as prerequisites for replacing the
primitive, rather than gates for this baseline integration.

Their useful derived proofs remain available. The genuine `API-04R/V/P/T`
strictness corrections remain selected and required. Research-only new
constructor agreements and projection joins must be classified separately
before promotion: do not include them merely because a deferred experiment
used them, and do not drop independently required corrections without checking
their consumers.

Next qualify downstream locality/sheaf consumers and interactions with the
rest of the corrected candidate, adapt existing profiled helper calls without
changing their retained data, and update the assumption ledger and source
comments. Complete the other main-consumer migrations, TypeScript alignment,
registered checks and final gates before calling the integration complete.
Concrete failures still require investigation; an inherited assumption is
not permission to ignore them or to claim a proved consistency result.

After the baseline checkpoint, a focused semantic review can identify the
intended `Transf`/`Transfd` model, establish the exact pointwise criterion,
and decide whether profiles, a different equivalence notion, or no API change
are appropriate. No new Empty audit or Op/duality repair is introduced here.
