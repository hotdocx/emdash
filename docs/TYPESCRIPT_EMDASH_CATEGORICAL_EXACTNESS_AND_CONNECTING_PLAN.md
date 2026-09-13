# Categorical Exactness And Connecting: Native Owner Plan

Date: 2026-09-13

Status: NUH-4C1 whole Coim/Im implemented; NUH-4C2 canonical comparison next; not a completed exactness/connecting theorem

Parent: [native universality and homology plan](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_AND_HOMOLOGY_PLAN.md)

## Direction And Scope

The user asks that connecting and exactness use the categorical universal
kernel/cokernel formulation directly. This supersedes making the ordinary
record bridge the primary continuation. Keep that checked bridge as optional
compatibility evidence. Do not make HasComputationalKernels/Cokernels,
IsContr factor records or the old point algorithms prerequisites for the
new primary connecting/exactness program, even when those records are
derived from whole P/Q.

Work in the current ordinary/OneCat abelian setting. Keep hom_int/homd_int
and the existing native diagram carriers. This plan introduces no external
relative-Hom foundation, new spectrum/derived-category project or Op repair.
All proposed functors and transformations must be actual internal terms
with computing whole/point/higher action. A mathematical outline or a new
opaque inhabitant labelled exactness is not implementation evidence.

## Whole Coimage, Image And Abelian Structure

Write D = Functor_cat(WalkingArrow_cat,C). Existing whole structures give
K,Q:D→C and transformations κ:K⇒ev₀ and q:ev₁⇒Q. Using the existing
transformation-to-arrow-diagram functor, define whole functors

```text
Coim = Q ∘ Arr(κ)       Im = K ∘ Arr(q)       : D → C.
```

Here Arr is owned by `transf_arrow_diagram_func`, not a new arrow-data
record. Its application to the existing κ/q retains parameter and higher
action. Composition is `comp_cat_fapp0`.

Construct the canonical whole comparison a:Coim⇒Im from the existing
units/counits and mate operations. Abelian structure requires invertibility
of this actual comparison. Kernel/cokernel existence alone does not imply
that condition. This is the usual coimage/image criterion in
[Stacks, Definition 12.5.1](https://stacks.math.columbia.edu/tag/00ZX).

Attach existing categorical invertibility evidence to the canonical map,
and obtain its inverse from that structure. Choose the actual strength
explicitly: OmegaEquivAlong has equality-valued inverse laws; DefIso has
judgmental inverse cuts. Do not infer one from the other without a qualified
construction, introduce a duplicate equivalence grammar, or choose a second
independent inverse merely to make a later comparison typecheck.

The required native assembly includes whole rotations of zero-triangle
data and whole mate action. A useful concrete route to test is transposing
the walking-arrow square of a unit/counit through the existing internal
argument-exchange owners. In the ordinary target this rotates the same
commuting square. It must be qualified at its actual endpoints and action;
do not replace it by extracting an equation at each object and rebuilding
an unrelated pointwise cone family.

## Exactness At The Actual Comparison

For A─f→B─g→D with its native zero-composite datum, construct the canonical
comparison

```text
e(f,g) : Im(f) → K(g).
```

Exactness at B is invertibility of e(f,g). It is essential to retain this
specific comparison, including its structural maps into B. An arbitrary
isomorphism between the two objects is not the exactness condition. This
expresses the usual image/kernel definition categorically, without an
object-equality cast. In the abelian setting it is equivalently expressed
by the actual H(f,g)=Q(β(f,g)) being a zero object.

For a coherent family, construct e as a whole transformation. Exactness
evidence for a family/LES position must apply to that whole comparison;
ordinary per-position predicates can be derived observations. Use existing
native zero-pair/window data and whole K/Q, not a separate cone grammar.
Short exact rows can similarly retain both canonical mate comparisons
A→K(p) and Q(i)→C as invertible: a categorical kernel-cokernel pair.

The LES exactness theorem must derive these comparison isomorphisms from
the short-exact input and Abelian structure. It must not postulate their
invertibility or assume the theorem through an exactness capability.

## Connecting As Whole Universal Descent

For a short exact sequence of complexes in the ordinary abelian setting,
the usual connecting map has a categorical construction. One useful
whole-program specification is the following, with every object/map varying
internally over the existing short-exact-window input.

1. Form Pₙ = Bₙ ×_{Cₙ} K(d⁽ᶜ⁾ₙ) categorically. The pullback can be obtained
   from whole biproduct and kernel operations; no element lift or splitting
   of Bₙ→Cₙ is selected.
2. Construct the canonical epic cover ρ:Pₙ→Hₙ(C) and the covered map
   θ:Pₙ→Hₙ₋₁(A) using the differential, row comparison inverses and whole
   kernel/cokernel mates. Derive the native cell expressing that θ kills Kρ
   from the original window data.
3. Let kρ:Kρ→Pₙ and let cρ:Q(kρ)→Hₙ(C) be the canonical coimage-to-target
   comparison. Abelian normality and epicity of ρ make cρ invertible.
4. Apply the whole cokernel mate to θ, producing θ̄:Q(kρ)→Hₙ₋₁(A), and set

```text
δₙ = θ̄ ∘ cρ⁻¹.
```

The familiar δₙ∘ρ=θ is then a universal reconstruction observation, not an
additional caller proof field. Naturality comes from the whole functors,
transformations and inverse/mate operations used in this term. The
construction does not assume a split exact sequence or require the snake
lemma as its primary owner. The ordinary existence and functoriality result
is [Stacks, Lemma 12.13.6](https://stacks.math.columbia.edu/tag/0111).

This is a semantic construction specification. The required whole cover,
covered map, annihilation cell, comparison inverse and their computations
are implementation obligations. Generic naturality must not be replaced
with caller-supplied squares or construction-specific naturality rules.

## Current Code And Next Tranche

`homology_window_connecting_transf` is already declared as a whole
transformation, but its component rule calls the retained ordinary record
construction. Preserve it as reference evidence; that declaration alone
does not complete the direct whole-universal program described here.
The ordinary exact-window package likewise remains a reference consumer.

NUH-4C1 now constructs Coim/Im and their structural maps as whole native
functors/transformations using current κ/q, in
[the image/coimage owner](../emdash2/emdash3_2_image_coimage_adjunction_families.lp).
Six transparent definitions and sixteen reviewer assertions retain the
original whole structures, diagram-map components and next Hom action.
No new rule, primitive or ordinary factor input is added. The
[owner ledger](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_OWNER_LEDGER.md)
records the exact local qualification and warning comparison.

The next bounded tranche qualifies the whole comparison a and the
zero-triangle/mate assemblies needed for it. A preliminary square-transpose
probe computes all four corners and both column components, but does not
yet identify its whole column endpoint functors with the required
evaluation whiskerings. Resolve that owner-level comparison or use a
better existing native assembly; do not turn component equations into
caller-supplied naturality data. The terminal/initial universal comparison
for each unit/counit's zero-end column is a further whole obligation.
Use these owners to formulate normality and exactness before migrating the
connecting program. Keep all source transformations, signs and actual H
selections explicit. Do not expand this into the deferred indexing/debugging
or strictness/duality projects.

Qualification must cover actual whole/point computations, a nonidentity
input map, retained next Hom action, and the relevant inverse cuts. Then
compare the new δ/exactness observations against the retained direct/CAS
implementation, including the nonzero connecting example. Follow the
parent plan's localized serial ≤90-second checks and exact warning audits.

The temporary `nuh4c_category_views.lp` and its checked dependency join
remain optional ordinary-view prototypes. They are not promoted source
and are not the next primary implementation step.
