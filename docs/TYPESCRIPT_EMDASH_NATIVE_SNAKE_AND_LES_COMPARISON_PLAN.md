# Native Snake And LES Comparison

Date: 2026-09-15
Status: individual proofs and six-term construction/maps/native inputs qualified; comparison/witness observation gap retained; LES specialization next

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
| NUH-6C | constructor/maps/native inputs and individual exactness proofs qualified; large comparison/witness observations remain 6C3b | Retain and qualify the full six-term sequence with all four actual canonical comparison witnesses |
| NUH-6D | next, independent of the 6C3b observation check | Whole LES specialization/comparison on the common short-exact inputs, fixed sign, and comparison with the general reference snake preserving its full scope |
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

At `76babd56`, NUH-6C2 still required zero cokernel projection and ΩAlong
evidence for each of the four actual comparisons. The first is now
qualified below. The native zero-pair inputs and original maps remain;
no output-exactness premise is allowed. General six-term exactness, the
LES/reference sign comparison, concrete NUH-6E checks, NUH-5N2G3B2
displayed integration and NUH-7 remain required.

### NUH-6C2a: First Interior Exactness At K(b)

The [kernel-comparison owner](../emdash2/emdash3_2_one_cat_native_snake_first_kernel_comparison.lp)
uses the original κ_b∘κ_k₂ and π_a to lift K(k₂) into Im(a), then
into K(v), where v:Im(a)⇒K(c) is the already derived lift. Reverse
native lifts give η:K(v)⇒K(k₂). Original inclusion reconstruction and
kernel cancellation derive η∘χ=id_K(k₂). This section is constructed;
it is not a supplied splitness premise or a new equivalence choice.

The [cover owner](../emdash2/emdash3_2_one_cat_native_snake_first_cover.lp)
uses the previously derived s_a:A⇒Im(a). Image-source cancellation
proves its actual cokernel projection zero. Existing kernel-precomposition
stability gives the cover r_L:K(v∘s_a)⇒K(v) and whole cancellation.
Since v∘s_a=α, the original first projection lifts into K(α). All
reconstruction uses the same P/Q and the same original diagrams.

The [exactness owner](../emdash2/emdash3_2_one_cat_native_snake_first_exactness.lp)
uses the actual ε₁:Im(k₁)⇒K(k₂) and its native inclusion law.
Its source-image factorization and the original input recovery identify
the representatives η∘r_L with maps through ε₁. The original Q unit
therefore makes π_ε₁∘η∘r_L=0. Cover cancellation gives π_ε₁∘η=0,
and the derived η∘χ=id gives π_ε₁=0. Together with the already derived
zero kernel inclusion, the existing inverse-from-universal-zeros theorem
constructs `one_cat_native_snake_first_exact` in the original
`OneCatNativeSnakeFirstExactness` predicate. This is fixed-forward ΩAlong
evidence on ε₁, not an arbitrary isomorphism of its endpoints.

This qualified tranche has 28 definitions and no primitive, rewrite or unifier.
Its 11 reviewer assertions cover original kernel reconstructions/the derived retraction,
image-source cokernel zero, representative lifting/cover cancellation,
the actual comparison cover factorization, its cokernel-zero proof and
full first exactness. A composed consumer first forms the native h from
arbitrary a,b,c and a whole triple-zero path; no monic-a or epic-c
restriction is added. No ordinary universal record or output-exactness
assumption drives the construction.

Final scoped evidence is recorded in
`emdash2/tmp/probes/nuh6c2_first_conformance.json`,
`nuh6c2_first_controls.json`, `nuh6c2_first_warnings.json` and
`nuh6c2_first_qualification.json`. All targets use 90s/2GiB; TypeScript,
repository aggregates, checker patches and resource-limit changes are out
of this tranche.

The three owners pass in 13.49s, 13.58s and 16.28s; the three reviewers
pass in 13.70s, 13.76s and 14.26s. All six diagnostic inventories match
their exact import controls: 1,484 inherited critical-pair and 169 pattern
reports, with matching locations, term heads, rule families and no parser
issues. Strict LHS and dependency scans pass. The catalog/TOC and generated
health snapshot are current; the snapshot covers 1,262 files without
running their typechecks. No earlier kernel, model or TypeScript owner changed.

At `42c72f49`, only the first interior position was qualified. NUH-6C2b
continues the actual second, third and fourth comparison cokernel-zero
proofs and their fixed-forward exactness. The next experiment is below.

### NUH-6C2b1: Second Interior Exactness At K(γ)

The preceding turn made progress at `42c72f49`: first interior exactness is
qualified. The new baseline owner passes with warnings enabled in
`emdash2/logs/probes/emdash3_2_one_cat_native_snake_first_exactness-20260915-090251.log`.
All 62 worktrees were clean and the comparison baseline remains an ancestor.

For M=K(∂) with inclusion μ, the construction forms the existing whole
cospan kernel L of μ:M⇒K(γ) and ρ:E⇒K(γ). Its projection r:L⇒M is a derived cover;
write e:L⇒E for the other projection. The original reconstruction gives
θ∘e=0, hence ℓ∘e lifts into the original Im(α). A second existing cospan
kernel V compares that lift with the original source-image cover
s_α:A⇒Im(α). Write s:V⇒L and x:V⇒A for its projections; s is a
derived cover. Their whole compatibility gives ℓ∘e∘s=α∘x.

The original whole difference j∘e∘s−a∘x is therefore killed by b and
lifts into K(b). Kernel reconstruction identifies its k₂-image with
μ∘r∘s. The original source-image factor of k₂ then gives representatives
through the actual ε₂:Im(k₂)⇒K(∂). Applying its Q-unit and cancelling
the two derived covers proves π_ε₂=0; the already derived kernel-zero
proof then gives fixed-forward ΩAlong. No extra exactness, cover, section,
ordinary factor record or pointwise naturality premise is used.

The experiment's rejection criteria were a changed original diagram
selection, a new universality axiom, or failure of a whole consumer at those
endpoints. Its owner-position prototypes and focused reviewer assertions
now pass, using the same local diagnostic/static/document gates as NUH-6C2a.
Op/profile repair and the separate displayed-CAS certificate join remain
deferred from this experiment. The last two exactness positions remain
required until their actual proofs qualify.

The [cover owner](../emdash2/emdash3_2_one_cat_native_snake_second_covers.lp)
constructs both original whole cospan kernels, their maps and compatibility,
the image lift, and whole cancellation through both covers. The original
cokernel-zero proofs for ρ and s_α are derived from their existing cover
cancellation, not supplied as new hypotheses.

The [representative owner](../emdash2/emdash3_2_one_cat_native_snake_second_representatives.lp)
uses the original internal difference operation and whole bilinearity to
form w:V⇒K(b). The original quotient π_a kills its correction, and kernel
cancellation proves k₂∘w=μ∘r∘s. All transformations retain their whole
action; there is no pointwise assembly of naturality fields.

The [exactness owner](../emdash2/emdash3_2_one_cat_native_snake_second_exactness.lp)
uses the source-image map of k₂ on its original native input. The actual
comparison ε₂ then factors r∘s. Its original Q-unit annihilation and the
two derived cover cancellations prove π_ε₂=0. Together with the already
derived κ_ε₂=0, `one_cat_native_snake_second_exact` constructs the existing
`OneCatNativeSnakeSecondExactness` predicate on that same canonical ε₂.

The three prototypes pass: `nuh6c2_second_covers-20260915-090526.log`,
`nuh6c2_second_representatives-20260915-090706.log` and
`nuh6c2_second_exact-20260915-090828.log` under `emdash2/logs/probes/`.
The promoted tranche has 28 transparent definitions and no new primitive,
rewrite or unifier. Its 11 reviewer assertions include both whole cover
cancellation consumers, native reconstruction, the actual comparison and
the composed arbitrary-triple input constructor. Final qualification is
recorded in `emdash2/tmp/probes/nuh6c2_second_conformance.json`,
`nuh6c2_second_controls.json`, `nuh6c2_second_warnings.json` and
`nuh6c2_second_qualification.json`. Checks remain scoped at 90s/2GiB;
no TypeScript or repository aggregate is part of this tranche.

The owners pass in 13.85s, 14.31s and 16.76s; the reviewers pass in
17.57s, 16.26s and 15.90s. All six diagnostic inventories match their exact
import controls: 1,484 inherited critical-pair and 169 pattern reports,
with matching locations, term heads, rule families and no parser issues.
Strict LHS, dependency, prototype-body preservation and document-link
checks pass. The catalog/TOC and source-health snapshot are current; the
snapshot covers 1,268 files without running a repository typecheck.

NUH-6C2b1 is **qualified**. It adds no primitive, rule or output assumption
and preserves the full arbitrary-triple scope of the native six-term input.

At `ff71ab1a`, NUH-6C2b2 still required the actual third and fourth comparison
cokernel-zero proofs and their fixed-forward exactness. The third is
constructed below, retaining whole ∂ and the original diagram selections.

### NUH-6C2b2a: Third Interior Exactness At Q(α)

The preceding turn made progress at `ff71ab1a`: second interior exactness
is qualified. All 62 worktrees were clean; the comparison baseline remains
an ancestor. The second-exactness baseline owner passes with warnings in
`emdash2/logs/probes/emdash3_2_one_cat_native_snake_second_exactness-20260915-091755.log`.

For M=K(q₁) with inclusion μ, form the original whole cospan kernel L of
μ:M⇒Q(α) and π_α:K(c)⇒Q(α). Its projection r:L⇒M is a derived cover;
write p:L⇒K(c) for the other projection. From q₁μ=0 and the original
q₁π_α=π_bκ_c reconstruction, π_bκ_cp=0. Lift κ_cp through the original
Im(b), then form a second cospan kernel V along s_b:B⇒Im(b). Its first
projection s:V⇒L is a derived cover; its second x:V⇒B satisfies
bx=κ_cps. Thus cbx=0, and the original γπ_a=cb reconstruction lifts
x into the same E used by ∂. Kernel cancellation gives ℓw=ps,
then ∂ρw=μrs. The actual third comparison factors rs through
its original source-image map; two cover cancellations prove its
cokernel projection zero and hence its fixed-forward ΩAlong evidence.

This direct whole construction uses the original P/Q, additive structure
and normality, with no Op migration, pointwise naturality records or output
assumptions. The experiment's rejection criteria were a change of original
diagram selection or failure of a whole consumer requiring such an
assumption. Its scoped 90s/2GiB checks pass. The later tentative memory
review of the separate displayed CAS certificate does not change these limits.

The [cover owner](../emdash2/emdash3_2_one_cat_native_snake_third_covers.lp)
constructs the two original cospan kernels and their whole cancellation.
The first cover uses the existing theorem that π_α has zero cokernel;
the second derives that property for the source-image map of b. Their
compatibility and the original q₁ reconstruction lift κ_cp into the
original image kernel on the Q-arrow of b.

The [representative owner](../emdash2/emdash3_2_one_cat_native_snake_third_representatives.lp)
derives bx=κ_cps and uses γπ_a=cb to lift x into the original E.
Its inclusion reconstructs x. Kernel cancellation gives ℓw=ps, and
the original connecting reconstruction then gives ∂ρw=μrs. No duality
transport, new cover choice or pointwise naturality field enters this proof.

The [exactness owner](../emdash2/emdash3_2_one_cat_native_snake_third_exactness.lp)
retains the third native input and its actual ε₃:Im(∂)⇒K(q₁).
Its original source-image factorization and the representative equation
derive a factor of rs through ε₃. The Q-unit and both derived cover
cancellations prove π_ε₃=0; the existing kernel-zero proof then constructs
`one_cat_native_snake_third_exact` in `OneCatNativeSnakeThirdExactness`.

The three prototypes pass: `nuh6c2_third_covers-20260915-092034.log`,
`nuh6c2_third_representatives-20260915-092139.log` and
`nuh6c2_third_exact-20260915-092256.log` under `emdash2/logs/probes/`.
The promoted tranche has 26 transparent definitions and no new primitive,
rewrite or unifier. Eleven reviewer assertions exercise both original
covers, native reconstruction, ∂, the actual canonical comparison and a
consumer built from arbitrary a,b,c and c∘b∘a=0. Final qualification is in
`emdash2/tmp/probes/nuh6c2_third_conformance.json`,
`nuh6c2_third_controls.json`, `nuh6c2_third_warnings.json` and
`nuh6c2_third_qualification.json`. All checks remain local at 90s/2GiB;
no TypeScript or repository aggregate is part of this tranche.

The owners pass in 13.63s, 15.88s and 15.71s; the reviewers pass in
13.39s, 13.75s and 18.56s. All six diagnostic inventories match their exact
import controls: 1,484 inherited critical-pair and 169 pattern reports,
with matching locations, term heads, rule families and no parser issues.
Strict LHS, dependency and prototype-body preservation checks pass, and
the catalog/TOC and source-health snapshot are current. The snapshot covers
1,274 files without a repository typecheck. NUH-6C2b2a is **qualified**;
the third predicate is proved on its actual comparison at the original
arbitrary-triple scope.

At `a44393cb`, fourth exactness at Q(b) remained. The direct construction
below uses three original covers and a native difference representative,
with every cover condition derived.

### NUH-6C2b2b: Fourth Interior Exactness At Q(b)

The preceding turn made progress at `a44393cb`: third interior exactness is
qualified. All 62 worktrees were clean; the comparison baseline remains an
ancestor. The third-exactness baseline owner passes with warnings in
`emdash2/logs/probes/emdash3_2_one_cat_native_snake_third_exactness-20260915-093056.log`.

Let M=K(q₂), with inclusion μ. The original cospan kernel L of μ and π_b
has a derived cover r:L⇒M and p:L⇒X. The original q₂π_b=π_γc
reconstruction gives π_γcp=0, so cp lifts into the original Im(γ).
A second cospan kernel V along the source-image cover of γ supplies
s:V⇒L and x:V⇒Q(a), with γx=cps. A third cospan kernel W along
π_a supplies u:W⇒V and y:W⇒B, with xu=π_ay; u is a derived cover.
Consequently c(psu)=cby. The original whole difference psu−by lifts
into K(c). Following its lift by π_α gives z:W⇒Q(α) with
q₁z=μrsu, since π_b kills by. The original fourth comparison
then factors rsu. Cancellation through all three derived covers proves
its cokernel projection zero and fixed-forward ΩAlong.

The construction retains the actual q₁/q₂ and their native inputs, with no
Op transport or caller naturality/factor records. The rejection criterion
was a missing whole consumer requiring a new cover or output-exactness
assumption. Its scoped 90s/2GiB qualification passes; the later memory and
opacity suggestions remain tentative and outside this experiment.

The [cover owner](../emdash2/emdash3_2_one_cat_native_snake_fourth_covers.lp)
constructs the original three cospan kernels, their compatibility and whole
cancellation. The first and third use the original quotient-cokernel-zero
theorem. The second derives that property for the source-image cover of γ.
Original q₂ reconstruction and native image lifting retain the same γ and
its original Q-arrow family throughout.

The [representative owner](../emdash2/emdash3_2_one_cat_native_snake_fourth_representatives.lp)
derives γx=cps. Original γπ_a=cb then makes psu−by a c-cycle.
The native K(c) mate constructs its lift, with original inclusion
reconstruction. The original π_b annihilation removes the correction by;
following the K(c) lift by π_α gives the whole z with q₁z=μrsu.

The [exactness owner](../emdash2/emdash3_2_one_cat_native_snake_fourth_exactness.lp)
uses the fourth native input and its actual ε₄:Im(q₁)⇒K(q₂).
Its original source-image factorization and the representative equation
make ε₄ factor rsu. The Q-unit and the three derived cover cancellations
prove π_ε₄=0; the existing kernel-zero proof then constructs
`one_cat_native_snake_fourth_exact` in `OneCatNativeSnakeFourthExactness`.

The prototypes pass in `emdash2/logs/probes/`:
`nuh6c2_fourth_covers-20260915-093321.log`,
`nuh6c2_fourth_representatives-20260915-093432.log` and
`nuh6c2_fourth_exact-20260915-093547.log`. The promoted tranche has 33
transparent definitions and no new primitive, rewrite or unifier. Twelve
reviewer assertions exercise all three whole cover cancellations, original
reconstruction, the actual q₁/comparison and the arbitrary-triple consumer.
Final qualification is in `emdash2/tmp/probes/nuh6c2_fourth_conformance.json`,
`nuh6c2_fourth_controls.json`, `nuh6c2_fourth_warnings.json` and
`nuh6c2_fourth_qualification.json`. Checks remain local at 90s/2GiB;
no TypeScript or repository aggregate is part of this tranche.

The owners pass in 16.10s, 14.86s and 15.67s; the reviewers pass in
14.64s, 16.83s and 15.61s. All six diagnostic inventories match their exact
import controls: 1,484 inherited critical-pair and 169 pattern reports,
with matching locations, term heads, rule families and no parser issues.
Strict LHS, dependency and prototype-body preservation checks pass; the
catalog/TOC and source-health snapshot are current. The snapshot covers
1,280 files without a repository typecheck. NUH-6C2b2b is **qualified**:
all four original interior comparisons now have derived fixed-forward
exactness witnesses at the original arbitrary-triple scope.

**Next — NUH-6C3:** assemble the original five whole maps and four native
exactness witnesses into one computing six-term result. Keep its generic
parameter category and the arbitrary a,b,c scope; compare the assembled
observations with the original maps and actual comparisons. LES/reference
sign comparison, concrete NUH-6E checks, NUH-5N2G3B2 displayed integration
and NUH-7 remain required.

### NUH-6C3 Experiment: Native Exact Six-Term Result

The preceding turn made progress at `c7d190c2`: all four original interior
comparisons now have qualified exactness proofs. All 62 worktrees were clean
and the comparison baseline remains an ancestor. The fourth-exactness
baseline owner passes in
`emdash2/logs/probes/emdash3_2_one_cat_native_snake_fourth_exactness-20260915-094531.log`.

Use the existing `FiniteArrowTail` in `Functor_cat K C`, beginning at k₁
and retaining k₂, ∂, q₁ and q₂ as its four further arrows. Its adjacent-pair
annotation will retain the original whole native input h, the existing
whole path identifying h's incoming observation with the stored incoming
map, and `OneCatAdjunctionExactFamily` on that same h. This is transparent
result data using the existing Sigma/Product and fixed-forward Ω evidence,
not a new universality or equivalence notion. The link to the incoming map
is derived by native input reconstruction; callers supply no naturality
proof or ordinary universal record.

Construct all four annotations from the original native inputs, their
already derived reconstruction paths and their exactness theorems. The
finite tail must retain the original maps literally, with no reselected
endpoints. Check the assembled input/comparison/evidence projections and
derive the stored adjacent-zero views from native input, rather than
substituting a separate list of exactness facts unrelated to the tail.
Reject a representation whose exactness does not apply to its actual stored
pair, or which requires an output-exactness assumption. Keep qualification
local and bounded at 90s/2GiB; no new primitive/rule or category of complexes
is planned.

Initial NUH-6C3 evidence: the seven-definition generic native exact-pair
annotation passes (`nuh6c3_pairs-20260915-094910.log`). The first inline
four-annotation/five-arrow result fails with allocation failure under the
2GiB guard (`nuh6c3_result-20260915-095119.log`). An import-only control
containing all four exactness owners passes
(`nuh6c3_all_imports-20260915-095304.log`). The import union is therefore
not itself the demonstrated failure. Isolate the annotations from the
tail constructor, then test named transparent suffixes if construction is
the expensive boundary. Preserve the failed inline source and keep all
original maps, inputs and witnesses; no new primitive, opacity or output
assumption is authorized by this failure.

The annotation/result-type prefix also fails under the memory guard
(`nuh6c3_steps-20260915-095417.log`); its process handle expired, and the
terminal log confirms allocation failure after the imports completed.
The first and second annotations each pass separately
(`nuh6c3_first_step-20260915-095722.log`,
`nuh6c3_second_step-20260915-095950.log`). The prefix still included the
`FiniteArrowTail` result type, so it does not by itself identify an
annotation failure. Separate all four annotations from that higher-order
result-type application before choosing a representation change.

Further isolation: the result type alone passes
(`nuh6c3_tail_type_only-20260915-100053.log`). A symbol-printing progress
probe passes the first two annotations and fails constructing the third
(`nuh6c3_steps_printed-20260915-100318.log`), while that third annotation
passes alone (`nuh6c3_third_step-20260915-100452.log`). Separate modules
reach the same third-annotation boundary
(`nuh6c3_modular_result-20260915-100700.log`); direct existing Σ/Product
construction also fails (`nuh6c3_annotations_direct-20260915-100852.log`).
The earlier type-query marker variant failed only because a bare implicitly
parameterized symbol required more arguments; it supplies no semantic result.

The next single runtime control uses the unchanged original source with
`OCAMLRUNPARAM=o=20,v=1024`, retaining the 90s/2GiB/64MiB/serial guard.
The installed OCaml `gc.mli` documents default `space_overhead=120` and
more eager collection at smaller values; the installed `ocamlrun.1` maps
this field to `o` and exit statistics to `v=1024`. This tests collection
overhead before changing representation. It changes no proof term, checker
logic, primitive, opacity or resource ceiling, and does not reopen the
separate displayed-CAS certificate investigation.

The unchanged inline constructor passes at 2GiB with that GC profile
(`nuh6c3_result-20260915-101024.log`). This establishes that construction
does not require changing the Sigma representation or hiding proof data.
At the user's explicit request, the same source also passes a temporary
4GiB/default-collection comparison (`nuh6c3_result-20260915-101437.log`,
22.735s). `nuh6c3_memory_4g.json` records the exact source/guard hashes and
verified restoration of the original guard bytes. The default remains 2GiB.

The general procedure is documented in the root guidance and the Lambdapi
SOP's resource section. The new scoped six-term runner uses `o=20` by default,
logs the effective setting and retains all ordinary guard limits. Explicit
caller settings are retained. The checker-metrics identity now records both
OCaml runtime environment variables and the scoped runner's hash, so changed
profiles are not silently reused as the same performance evidence.

Promotion keeps the original seven annotation definitions and six snake
result definitions. The two owners, five generic projection/zero assertions
and six complete-result/map assertions pass under `o=20` at 2GiB. The initial
eight-input reviewer fails at both `o=20` and `o=10`. Threading the tail's
actual projected endpoints/arrows into the dependent observation calls
instead of forcing repeated comparisons with separately written endpoint
copies passes all eight input/zero observations
(`nuh6c3_inputs_shared-20260915-103325.log`). This is a consumer-presentation
change only; the recovered native inputs are still compared with the
original ones. The remaining comparison/evidence reviewer is retained as 6C3b;
its first combined shared-endpoint attempt still exceeds 2GiB. Do not yet
qualify all result observations or claim NUH-6 complete.

### NUH-6C3a: Qualified Construction And Input Observations

The [native annotation owner](../emdash2/emdash3_2_one_cat_native_exact_arrow_pairs.lp)
has seven transparent definitions. Each annotation stores the original h,
its incoming-map reconstruction and `OneCatAdjunctionExactFamily` on that
same h. Generic constructor/projection β checks retain h, its path, the
canonical comparison formula and the original witness. The zero view is
derived from native input annihilation. No primitive, rule or ordinary
universal-record prerequisite is added.

The [six-term owner](../emdash2/emdash3_2_one_cat_native_snake_six_term_result.lp)
has six definitions: four original annotations, the finite-tail result type,
and its constructor. The first edge is fixed by the tail index; the remaining
edges and endpoints are stored by its constructors. All entries are whole
functors/transformations in `Functor_cat K C`. The constructor applies the
four original exactness theorems, not supplied output evidence. Its composed
consumer retains arbitrary a,b,c and cba=0, without monic-a or epic-c inputs.

Thirteen definitions, five generic projection/zero assertions, six complete
result/map assertions and eight native-input/zero assertions are qualified:
19 assertions total. Input consumers thread the actual projected endpoints
and arrows through the dependent accessors and recover the original h at
every position. Five scoped runner/profile tests also pass. The runner,
examples dispatcher and metrics use the measured GC profile for these
targets only. No global GC default, memory ceiling, checker patch or opacity
change is installed.

The owner checks take 8.99s and 36.34s; the generic, map and input reviewers
take 8.74s, 36.06s and 29.65s. All five diagnostic inventories match their
import controls, including locations, term heads, rule families and parser
results: annotation owner/reviewer retain 1,208 critical-pair and 159 pattern
reports; result/map/input checks retain 1,484/169. No new rule is introduced.
Strict LHS, source/snapshot audits, catalog/TOC and source-health checks pass.
The health snapshot covers 1,285 files without a repository typecheck.
Evidence is recorded in `emdash2/tmp/probes/nuh6c3_conformance.json`,
`nuh6c3_controls.json`, `nuh6c3_warnings.json` and `nuh6c3_qualification.json`.

### NUH-6C3b: Required Observation Gap And Changed Work Order

The first bare comparison of a concretely extracted Im→Ker map with its
standalone presentation exceeds 2GiB. Typed reflexivity, Σ elimination
before reconstruction and direct Σ/Product construction do not resolve it.
The unchanged reviewer also fails at 4GiB; at 6GiB it reaches the 90-second
limit and logs allocation failure. The normal guard is restored after each
temporary experiment. `o=1` spends the deadline in imports.

Fresh exact-source compilation checks the parent and produces 174 `.lpo`
files, but the dependent review exhausts 2GiB while importing them. An
isolated post-proof opacity test on the four adjacent-zero laws checks the
parent, then fails the same reviewer. No opacity is promoted. The existing
`OmegaArrowData` carrier admits a generic observer, but its combined concrete
comparison/inverse review is not qualified either. These are resource
results, not mathematical counterexamples.

The [resumption bundle](../emdash2/audits/native-six-term-observation-boundary/README.md)
preserves the failed reviewer, relevant variants and measurement manifests.
They are not positive library examples. The original comparison/witness
observation obligation remains required before NUH-7. The user permits
progressing independent skeleton/mathematics and returning later to these
gaps. Advance NUH-6D using the qualified whole maps, individual exactness
proofs and ∂ρ=θ; this observation check is not its prerequisite.

The initial LES-specialization candidate takes the four-row window
Bm→B0→B1→B2 and forms a=[bm,i0]:Bm⊕A0⇒B0, b=b0, and
c=⟨b1,p1⟩:B1⇒B2⊕D1. Existing whole product/coproduct operations,
the two middle-column zero pairs and row-map reconstruction should derive
cba=0. Native universal comparisons should then identify K(γ) with upper
right H and Q(α) with lower left H, retaining the original selections.
Compare ∂ρ=θ with the native δ reconstruction to fix the sign. This candidate
still requires owner-level review and typed consumers; it is not implemented
or a completed sign comparison.
