# Action-Profile Integration: Inverse Action Feasibility

Date: 2026-09-26

Status: derived component, whole-Hom and next-Hom inverse comparisons pass;
postcomposition accumulator correction remains a prototype; whole assembly
and the higher projection audit remain open

Owner: [living plan](EMDASH_ACTION_PROFILE_INTEGRATION_PLAN.md), `API-05` and
`API-04P`. This continues the
[relative-profile investigation](EMDASH_ACTION_PROFILE_RELATIVE_PROFILE_FEASIBILITY.md)
after the [vertical-fold correction](EMDASH_ACTION_PROFILE_VERTICAL_FOLD_AUDIT.md).
No production LP file is changed by this investigation.

## Derived Action Of The Actual Inverse Choices

Let `eta : F => G` have the proposed relative action profile, and let `u[x]`
be fixed-forward `OmegaEquivAlong` evidence for its component. Write `l[x]`
and `r[x]` for the two selected inverse arrows in that same evidence.
The new definitions prove, for each original arrow `f : X -> Y`:

```text
F[f] o l[X] = l[Y] o G[f],
F[f] o r[X] = r[Y] o G[f].
```

The proof first derives equality between the two selected inverse arrows
from their supplied cancellation laws and ordinary associativity. It uses
that equality to obtain the missing cancellation law for each choice. It
does not replace either stored arrow with the other or reflect their equality
into runtime conversion. A negative control retains that distinction.

The relative profile's two complete-action fields give a whole Hom-functor
naturality equation. Evaluating it supplies the forward component square;
ordinary cancellation then gives the two inverse component squares above.
No `IsStrictFunctor(F)` or `IsStrictFunctor(G)` premise is added.

The argument also works before evaluation, yielding an equality of whole
functors from `Hom_cat A X Y` to `Hom_cat B (G[X]) (F[Y])`:

```text
precompose(l[X]) o F_XY = postcompose(l[Y]) o G_XY,
precompose(r[X]) o F_XY = postcompose(r[Y]) o G_XY.
```

Here `F_XY` and `G_XY` are the original `fapp1_func` values. The proof uses
identity-family Hom composition, its two existing `Hom_func` factorizations,
ordinary associativity and the actual inverse laws. It does not use generic
postcomposition accumulation for arbitrary `F`.

Dependent path congruence (`PathOver`) then retains the next Hom functors at
original `s,t : Hom A X Y`, including their distinct endpoint images. These
are observations of equality paths, not operational arrow transports.

The first cancellation attempt relied on the unifier composing two
associativity steps automatically and failed. Explicit `comp_assoc` paths
resolve it without a rule change. The final support modules are definitions
only. The generic reviewer has six positive and five negative assertions,
including rejection of reflexivity in place of either component or whole-Hom
comparison, even when profile evidence is in context.

## Actual Matching Producer

The existing whole matching comparison is path-induced. A new path-induction
producer gives pointwise fixed-forward inverse data for that same transfor.
Two further path-induction proofs identify each of its selected component
inverse arrows with the corresponding component of the already constructed
whole `object_path_equiv_along` inverse. Both slots are observed explicitly.

`api_cover_matching_inverse_hom_consumers.lp` instantiates the new theorem at
the actual retained-section matching comparison. It contains the pointwise
producer and four whole-Hom/next-Hom consumers, covering both inverse choices.
All five definition bodies check. For this path constructor the two inverse
slots coincide by the existing constructor definition; the generic theorem
above still accepts arbitrary supplied inverse data.

This does not create a whole inverse transfor from a family of components.
It proves action comparisons at fixed `X,Y`, with all action inside that Hom
retained. Composition/unit coherence across the complete internal action,
the varying displayed/base directions, and construction/cancellation of a
whole assembled inverse remain required. The relative profile is still
unselected as a sufficient general assembly premise.

## Further Staged Strictness Route: API-04P

The corrected vertical candidate still contained three generic
postcomposition accumulators: whole functor composition, nested point
composition and mixed raw-arrow/point composition. Staging their generic
path and the represented-to-raw comparison before substituting the initial
arrow by identity proves composition preservation for arbitrary raw `F`.

The first direct specialization failed to elaborate; it is not a negative
result for the staged route. The complete staged reproducer succeeds:
`20260926T220056Z-1eb293e1c22840ff8961f8174bca36c4`. The unchanged reproducer
fails at its first generic accumulation proof on the corrected candidate:
`20260926T220544Z-ce71b2973b884cfca83a0e25f52bcfcd`. Both are bounded checks;
the failure is proof unification, not resource exhaustion.

The separate full-file candidate comments those three generic clauses.
Two identity-family clauses preserve ordinary Hom computation in the nucleus;
three clauses after `StrictFunctor` provide the profiled computations,
retaining the actual ambient category guard. Ten positive/three negative
controls check the profiled clauses, their typed results, raw rejection and
both identity-family evaluation orders. All inverse proofs described above
also pass with this correction in place.

The telescope 2-cell accumulation and other higher projection clauses still
need a staged owner audit. This correction does not establish that all
remaining strictness routes have been removed. No new primitive admission,
Op/duality repair or Empty audit is included.

## Warning Review

The focused warning inventory changes from 999 to 947 critical-pair warnings;
150 pattern-variable diagnostics remain. Complete participant-template
comparison removes 78 instances and adds 26 restricted instances:

- Twelve identity-family specializations of the old accumulator overlaps.
- Two profiled nested-accumulation instances.
- Four profiled DefIso cancellation instances.
- Four profiled identity instances.
- Four existing composition presentations: opposite, terminal, skeleton and
  the strict-functor category.

The broad review changes from 1,187 to 1,127 critical-pair warnings, retaining
162 pattern-variable diagnostics. Its 35 added/95 removed instances include
the same 26, eight identity-family overlaps with the existing strict-mapped
and evaluated DefIso owners, and the existing `NType_cat` presentation.
No rule-family count increases. Source-location mapping finds no increase
at unchanged locations; all warning text is classified by the parser.

Thirteen additional assertions check representative associativity paths,
identity/profiled DefIso cancellation, composed DefIso cuts and the terminal
contractibility comparison. The broader reviewer also retains the existing
mapped/evaluated DefIso consumers. The presentation cases remain classified
instances of the earlier generic overlaps; this slice introduces no new
presentation join. These results do not claim that every critical branch
joins at runtime, or establish confluence.

Strict inferred-slot audits find zero unreviewed candidates in both changed
owners. The nucleus retains its 64 annotated slots across 41 clauses.
Subject reduction is enabled throughout.

## Exact Qualification And Recovery

The separate package is `emdash2/tmp/probes/api_postcomp_profile_candidate/`.
The earlier packages remain intact. Current SHA-256 pins are:

- Core: `d0de0eda354c178393b7494c21208cd8907f2b3f7f0119153bc8b31b5a34a9fe`.
- Profile owner: `f670814a83a508bd8a77a4000c7ab04690bbfc25978d106bb1d761ce6723a69c`.

| Current successful check | Receipt | Seconds / maximum child RSS KiB |
| --- | --- | ---: |
| Inverse square through complete Hom on corrected core | `20260926T220516Z-581feaa1eccd4edaa206c6de9f7208d5` | 7.932 / 449,692 |
| Profile and inverse controls, 16 positive/eight negative | `20260926T220749Z-d9fef0833c1d4ad9837e6df7abd5dd9b` | 8.072 / 452,060 |
| Broad matching/Gray/Gamma/H/Hom review, 439 positive/119 negative | `20260926T220851Z-bce93a1235fe451091e3be912fbf6c80` | 38.603 / 1,945,720 |
| Actual matching pointwise producer and both whole/next-Hom consumers | `20260926T221220Z-caff18caa84a493fb8c2a02c42c46025` | 28.689 / 1,554,256 |
| Additional overlap controls | `20260926T221418Z-2327a846b3ce47b290f9165759cecd9c` | 5.497 / 448,132 |

The final combined review also includes the actual matching consumers and
additional overlap controls. It passes **452 positive/119 negative assertions**
across 219 inputs in 46.877s, maximum child RSS 2,509,768 KiB, receipt
`20260926T221703Z-de73c554e91546a4a6626d4a7f65a469`. Its warning categories,
heads, families, full participant templates and locations exactly match the
preceding broad run.

The six new proof modules contain 27 definitions and no primitive, rewrite
or unification declaration. The package is source-only with no compiled
parents. All checks use warnings, serial execution,
`OCAMLRUNPARAM=o=20,v=1024`, subject reduction and existing file/core/no-swap
limits. Focused and actual-consumer checks use 2 GiB/90s; broad checks use
explicit 3 GiB/180s, following the existing measured closure qualification.
Defaults are unchanged.

The manifest
`emdash2/tmp/probes/api_inverse_action_current_qualification_manifest.json`
binds all seven current successful receipts, the complete 219-input union,
27-definition audit, staged controls, source pins and authoring/audit files.
SHA-256: `fdb2775a8ce4e8057cd7c5966745f7d8879011b447270878d3ee83c7e477678e`.
Detailed warning records are `api_postcomp_warning_delta.json`,
`api_postcomp_broad_warning_delta.json` and
`api_postcomp_warning_locations.json` beside it.

The immutable receipts retain exact input blobs and checker/runner/settings
identity. Authoring scripts record the experiment sequence; they are not yet
a clean-checkout production integration recipe. No earlier native/CAS/all-path
receipt is relabelled for this changed core.

Next audit the remaining higher postcomposition owner, then continue the
complete relative/displayed action and rho construction. Production cut
retirement, downstream requalification, TypeScript and final integration
gates remain required by the parent plan.
