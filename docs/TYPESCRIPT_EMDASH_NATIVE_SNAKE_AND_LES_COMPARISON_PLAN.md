# Native Snake And LES Comparison

Date: 2026-09-15
Status: native connecting and six-term maps/zeros qualified; four comparison cokernel-zero proofs next

Parent: [native universality and homology plan](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_AND_HOMOLOGY_PLAN.md).

## Scope And Mathematical Boundary

The existing general snake interface is `AbelianSnakeTriple`: an arbitrary
triple A ─a→ B ─b→ X ─c→ D with c∘b∘a=0. The original
[owner](../emdash2/emdash3_2_abelian_snake_lemma.lp) derives
α:A→K(c) and γ:Q(a)→D with κ_c∘α=b∘a and γ∘π_a=c∘b.
Its six terms are K(α), K(b), K(γ), Q(α), Q(b), Q(γ).
Neither a monic nor c epic is an input. Preserve this generality.

Two short exact rows alone do not immediately recover that full scope.
Replacing A by Im(a) and D by Im(c) changes α and γ. Such a route would need
the comparisons at all six terms, including the outer kernel-cover and
cokernel-inclusion comparisons. Do not silently strengthen the hypothesis
or qualify only the middle connecting arrow as the general snake theorem.

The native implementation will use the same general triple as whole
transformations over an arbitrary parameter category K. Its primary zero
datum is the existing coherent input h:J∘A⇒Arr(c∘b), with a recovered by
the existing whole source observation. A whole triple-zero path may enter
through the existing native input constructor. No caller supplies naturality
squares or ordinary kernel/cokernel factor records.

Use whole P/Q and their mate functors directly. C1, the original additive
structure, terminal/initial capabilities, and fixed-comparison normality
remain explicit at their existing scope. No new universality or exactness
axiom, choice of inverse, global strictness rule or foundation is authorized.

## Native Construction And Sign

The native connecting construction uses the following descent through the
existing whole kernel/cokernel owners:

1. Form E=K(γ∘π_a), retaining its inclusion E→B and the induced
   ρ:E→K(γ). The existing quotient-cokernel-zero theorem and kernel
   precomposition cover theorem should supply the whole cover evidence.
2. Lift b on E into K(c), then compose with π_α to obtain θ:E→Q(α).
   Prove that θ kills the original kernel of ρ using whole reconstruction.
3. Descend θ through that cover to ∂:K(γ)⇒Q(α), with ∂∘ρ=θ.

All three stages are implemented below. This route retains the general
triple without requiring a new whole category of complexes or a conversion
to old ordinary universal records.

Fix the positive sign by that reconstruction. The existing CAP-style snake
owner uses q₂∘∂∘p₁=q₁∘b∘p₂. Comparison maps must retain their original
kernel embeddings and quotient projections, so an independent sign choice
cannot be hidden in an endpoint isomorphism. The native LES comparison must
check its own ∂/δ reconstruction under these same oriented maps.

## Execution Ledger

| Row | State | Required outcome |
| --- | --- | --- |
| NUH-6A | qualified in the current tranche | General whole input, α and γ through original P/Q, with whole reconstruction and no monic/epic assumption on a/c |
| NUH-6B | qualified: θ∘κ_ρ=0 and whole ∂ with reconstruction/uniqueness derived | Original whole descent, with no additional annihilation or connecting assumption |
| NUH-6C | maps, four zeros, native exact inputs/comparisons and their zero kernel inclusions qualified; four cokernel-zero proofs remain | Prove invertibility of all four actual interior comparisons and retain the full six-term sequence |
| NUH-6D | pending 6B/6C | Whole LES specialization/comparison on the common short-exact inputs, fixed sign, and comparison with the general reference snake preserving its full scope |
| NUH-6E | pending 6C/6D | Focused formal/concrete qualification and documentation; no statement of a general homology normalization theorem |

First experiment: instantiate the existing native lift/descent on h and
derive their whole reconstruction equations. A failure requiring ordinary
factor records, pointwise naturality fields or stronger triple hypotheses
rejects the proposed interface. Whole transforms and their generic action
must remain available; point observations alone do not qualify this row.

The earlier goal turn is progress at `c7662eac`: original input-pair
observations qualify, while the combined CAS exactness certificate remains
unqualified. NUH-6 uses the completed general NUH-4 construction and can
advance independently. NUH-5N2G3B2 integration remains required before NUH-7
and goal completion. Op/profile integration, spectra/stabilization and the
optional endpoint/projection investigations remain deferred.

## Validation And Recovery

Use the dedicated existing goal worktree and local green checkpoints.
Follow the current AGENTS/SOP and localized validation policy. New semantic
definitions require focused typed consumers, diagnostic controls, LHS audit,
catalog/health synchronization and exact diff review. Use the serial
90s/2GiB guard; any time extension needs a measured target and recorded reason.
No repository aggregate, checker patch or memory-limit bypass is planned.

Baseline: the current native window connecting owner checks with warnings
enabled in `emdash2/logs/probes/emdash3_2_one_cat_native_homology_window_connecting-20260915-065702.log`.
Both staged and unstaged state were clean; all 62 worktrees were inspected,
and baseline `cbef77e7` remains an ancestor of `c7662eac`.

## Qualified Native Input, Factors, Cover And Covered Map

The [input owner](../emdash2/emdash3_2_native_snake_inputs.lp) defines
`NativeSnakeInput` as the existing whole transformation h:J∘A⇒Arr(c∘b).
Its original source observation and incoming-arrow family are retained.
The existing native input constructor accepts a whole c∘b∘a=0 path, and
whole source recovery returns the original arbitrary a. It selects no K/Q.
The first reviewer includes arbitrary a and b with c=0; no monic/epic
hypothesis is added to form or use that input.

The [factor owner](../emdash2/emdash3_2_one_cat_native_snake_factors.lp)
constructs α:A⇒K(c) and γ:Q(a)⇒D through the original native whole lift
and descent. Their whole ambient reconstructions are κ_c∘α=b∘a and
γ∘π_a=c∘b. These operations require the existing preadditive/OneCat
setting and P/Q, not old W/V records, Abelian normality or caller naturality
fields. Their component types remain observations of the same whole terms.

The [cover owner](../emdash2/emdash3_2_one_cat_native_snake_cover.lp)
retains the actual γ diagram, π_a, E=K(γ∘π_a), its inclusion j:E⇒B,
and ρ:E⇒K(γ). The existing kernel-precomposition theorem gives
κ_γ∘ρ=π_a∘j. The original Q-unit theorem proves the needed zero
cokernel of π_a; the existing Abelian kernel-precomposition cover theorem
then supplies ΩAlong on the actual Coim(ρ)⇒K(γ) comparison.
This is a cover certificate, not an inverse or a chosen section of ρ.
Native coimage-cover cancellation consumes that exact certificate and
derives u∘ρ=v∘ρ ⇒ u=v for arbitrary whole u,v.

The [covered-map owner](../emdash2/emdash3_2_one_cat_native_snake_covered_map.lp)
derives c∘b∘j=0 from γ's reconstruction and E's original annihilation.
Native lifting gives ℓ:E⇒K(c), with κ_c∘ℓ=b∘j, and the original
Q unit gives θ=π_α∘ℓ:E⇒Q(α). θ's component composition computes
through the existing generic transfor rule. This fixes the positive covered
formula while retaining the original kernel and quotient.

The four owners add 23 definitions, no primitive, rule or unifier. Their
interfaces do not require ordinary computational kernel/cokernel records.
Eight input, six factor, five covered-map and one cancellation assertions
pass. Final owner timings are 4.24s, 5.95s, 10.65s and 10.52s;
reviewers take 8.27s, 6.03s, 10.41s and 10.42s, all under 90s/2GiB.
The validation manifest and diagnostic comparisons are
`emdash2/tmp/probes/nuh6ab_conformance.json`, `nuh6ab_controls.json`,
`nuh6ab_warnings.json` and `nuh6ab_qualification.json`. Strict LHS scans,
catalog/TOC, generated source-health and document hygiene are localized.
No TypeScript or repository aggregate ran.

Owner/reviewer diagnostic inventories match their exact import controls in
all eight comparisons: inputs/factors 1,208 critical-pair/159 pattern
reports, cover/covered map 1,484/169, and the input reviewer with its extra
zero-composition owner 1,381/159. Locations, term heads, rule families and
parser issues match as well. These are inherited diagnostics, not newly
introduced rules. The source-health snapshot covers 1,240 files without
running a repository aggregate.

The original combined global-symbol reviewer and its expanded Ω type
comparison exceeded 2GiB. The declarations alone passed. A whole
cancellation constructor consuming the actual cover proof checks; the final
reviewers separate the pre-Abelian covered map from Abelian cancellation
and use the latter in its parameter scope. The failed expanded/global
variants remain unqualified in `nuh6b_cover_reviewer_expanded.lp`,
`nuh6b_cover_positive.lp` and `nuh6b_cover_reviewer_reflect_global.lp` under
`emdash2/tmp/probes/`. No opacity, new assumption or memory-limit change
was used. This does not resolve the separate concrete NUH-5 certificate join.

At checkpoint `715932c9`, θ∘κ_ρ=0 and the final descent were still
required. They are now derived below. The earlier
`one_cat_native_snake_covered_zero` retains its separate c∘b∘j=0 type;
the new `one_cat_native_snake_theta_kernel_zero` supplies the final
annihilation used by ∂.

### NUH-6B Completion: Derived Annihilation And Whole ∂

The [image-family owner](../emdash2/emdash3_2_one_cat_image_family_covers.lp)
defines s_F as the original coimage quotient followed by the fixed
Coim→Im comparison. Whole quotient cancellation and the original normality
evidence prove cancellation through s_F. Reindexing the original kernel
inclusion and the existing coimage factorization gives κ_Im∘s_F=f.

The direct typed-reflexivity attempt comparing K(Arr(π_F)) with Im∘F
did not finish (`nuh6b_image_reindex-20260915-075400.log`). No new fold or
cast was introduced. The selected route instead uses the original diagram
Arr(π)∘F, on which the existing image is already K. Its differential is
the original family quotient by definition. Thus all later image lifts use
the same original K and Q, with no alternate kernel selection.

The [snake image owner](../emdash2/emdash3_2_one_cat_native_snake_image.lp)
derives v:Im(a)⇒K(c) from b∘κ_Im. Whole reconstruction gives
v∘s_a=α. Applying the original quotient π_α and cancelling s_a proves
π_α∘v=0. This uses normality; it is not an input annihilation premise.

The [kernel-annihilation owner](../emdash2/emdash3_2_one_cat_native_snake_kernel_annihilation.lp)
uses κ_γ∘ρ=π_a∘j and ρ∘κ_ρ=0 to lift j∘κ_ρ into that same
image. Native kernel reconstruction identifies ℓ∘κ_ρ with v followed
by this image lift. Consequently θ∘κ_ρ=0 follows from π_α∘v=0.
All compatibilities are derived whole paths; callers supply no additional
naturality square, factor record or output-exactness evidence.

The [connecting owner](../emdash2/emdash3_2_one_cat_native_snake_connecting.lp)
now applies the existing `one_cat_coimage_cover_descent` to the original θ,
its derived annihilation, and the already derived cover of ρ. This produces
the actual whole ∂:K(γ)⇒Q(α). Existing descent reconstruction proves
∂∘ρ=θ, and the same native cover cancellation proves uniqueness.
The sign is fixed by this positive formula. This does not yet prove the
comparison with the independently retained reference/LES constructions.

Four owners add 22 definitions and no primitive, rewrite or unifier.
Eleven reviewer assertions exercise image cancellation/factorization, the
actual image/kernel compatibilities, θ∘κ_ρ=0, whole ∂, reconstruction,
uniqueness, and a composed consumer which first builds h from arbitrary
a,b,c and a whole triple-zero path. No monic-a or epic-c assumption enters.
Final validation remains at 90s/2GiB per target; no TypeScript change,
repository aggregate, checker patch or memory-limit change was made.
Evidence is in `emdash2/tmp/probes/nuh6b_final_conformance.json`,
`nuh6b_final_controls.json`, `nuh6b_final_warnings.json` and
`nuh6b_final_qualification.json`, with the scoped LHS/catalog/TOC/health and
document checks recorded there.

Final owner checks take 6.44s, 11.09s, 11.01s and 10.96s; the three
reviewers take 6.75s, 10.99s and 13.68s. All seven diagnostic inventories
match their import controls, including locations, term heads, rule families
and parser results: the image-family owner/reviewer retain 1,208 critical-
pair/159 pattern reports; snake owners/reviewers retain 1,484/169. The
source-health snapshot covers 1,247 files with checking limited to the
affected owners and consumers.

The NUH-6C experiment after `ee072b47` formed the whole diagram maps
α→b from κ_c∘α=b∘a and b→γ from c∘b=γ∘π_a through the existing
`one_cat_square_family_transf`. Their square data are derived from the
previous reconstruction theorems, not caller fields. Original whole K/Q
action retains inclusion/projection reconstruction. The two outer zero
composites follow by native cancellation. The inner composites use a lift
from K(b) into the existing E and the original ∂∘ρ=θ equation, followed
dually by cancellation through ρ. These zero equations alone do not prove
exactness.

### NUH-6C1: Whole Six-Term Chain And Canonical Comparison Inputs

The [map owner](../emdash2/emdash3_2_one_cat_native_snake_six_term_maps.lp)
now defines the two whole diagram maps α→b→γ from the already derived
reconstruction paths. Original K and Q action gives four transformations:

```text
K(α) ─k₁→ K(b) ─k₂→ K(γ) ─∂→ Q(α) ─q₁→ Q(b) ─q₂→ Q(γ).
```

Four native reconstruction theorems retain a, π_a, κ_c and c as the
original source/target maps of those squares. No caller supplies square
proofs, new universal choices or an assumption that a/c are monic/epic.

The [outer-zero owner](../emdash2/emdash3_2_one_cat_native_snake_outer_zeros.lp)
derives k₂∘k₁=0 by original quotient annihilation and kernel cancellation,
and q₂∘q₁=0 by original kernel annihilation and quotient cancellation.
The [middle lift](../emdash2/emdash3_2_one_cat_native_snake_middle_lifts.lp)
maps K(b) into the existing E, with j∘lift=κ_b and ρ∘lift=k₂.
Kernel cancellation gives ℓ∘lift=0, hence θ∘lift=0.
The [inner-zero owner](../emdash2/emdash3_2_one_cat_native_snake_inner_zeros.lp)
then derives ∂∘k₂=0 from ∂∘ρ=θ. Dually, q₁∘∂ vanishes after ρ
by the original q₁ and ℓ reconstructions; native cover cancellation
derives q₁∘∂=0. All four zero equations concern the actual whole maps.

The [exact-input owner](../emdash2/emdash3_2_one_cat_native_snake_exact_inputs.lp)
uses those derived zero equations to form the four existing native kernel
inputs, then defines each actual canonical Im→Ker comparison. Its
`OneCatNativeSnake*Exactness` predicates are the existing fixed-forward
`OneCatAdjunctionExactFamily`; they are not supplied or inhabited by a new
axiom. The [comparison-kernel owner](../emdash2/emdash3_2_one_cat_native_snake_comparison_kernels.lp)
applies the existing general theorem to derive zero kernel inclusion for
each of the four comparisons. Their cokernel-zero proofs remain required;
none of the four exactness predicates is claimed proved at this milestone.

This tranche has 36 definitions and no primitive, rule or unifier.
Eight map/reconstruction, six zero/lift and eight comparison-predicate/kernel
assertions pass: 22 assertions in total. The six owner checks take 10.34s,
11.28s, 10.95s, 11.65s, 12.21s and 13.35s; the reviewers take 11.02s,
11.65s and 12.02s. No time/memory extension or semantic bypass was used.
Qualification is recorded in `emdash2/tmp/probes/nuh6c_conformance.json`,
`nuh6c_controls.json`, `nuh6c_warnings.json` and `nuh6c_qualification.json`.
Checks remain local, serial, at 90s/2GiB, with no TypeScript or repository
aggregate. The four named comparison kernels reduce the remaining
exactness obligations to their four actual cokernel projections, using the
existing inverse-from-universal-zeros criterion once these are proved.
All nine owner/reviewer diagnostic inventories match their import controls,
including locations, term heads, rule families and parser results. Strict
LHS and source-dependency scans pass; the catalog/TOC and generated health
snapshot are current. No older kernel, model or TypeScript owner changed.

**Next — NUH-6C2:** prove zero cokernel projection for each of the four
actual comparisons and derive its ΩAlong evidence. Retain the native
zero-pair inputs and original maps; no output-exactness premise is allowed.
General six-term exactness, the LES/reference sign comparison, concrete
NUH-6E checks, NUH-5N2G3B2 displayed integration and NUH-7 remain required.
