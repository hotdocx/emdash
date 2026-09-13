# Categorical Exactness And Connecting: Native Owner Plan

Date: 2026-09-13

Status: C2c2 whole family formula agreement and inverse reconstruction qualified; whole evaluation and canonical Coim⇒Im remain; not a completed exactness/connecting theorem

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
data and whole mate action. The current route transposes
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

## Whole Terminal/Initial Presentation Boundary

The retained TerminalObject interface supplies a whole canonical arrow
transformation and pointwise IsContr uniqueness. C2b now adds a one-way
[native family-universality extension](../emdash2/emdash3_2_one_cat_terminal_family_universality.lp)
with two primitive ordinary-target operations of the existing DefIso type,
for F:B→C:

```text
h:F⇒const_t   ↦   Arr(h) ≅ J∘F       when t is terminal;
h:const_t⇒F   ↦   Arr(h) ≅ I∘F       when t is initial.
```

Both directions have identity components at both walking-arrow endpoints.
Use the selected inverse from DefIso, with its existing inverse cuts; do
not invent another equivalence type or a separate inverse choice. Each
instance requires OneCat(C) and the corresponding original terminal/initial
capability. It does not assert this stronger presentation for arbitrary
directed higher categories from groupoidal pointwise contractibility.

Semantically, ordinary terminal/initial uniqueness makes the original and
canonical arrows equal at every parameter. Identity endpoint maps then give
the unique comparison of arrow diagrams, and their naturality follows from
the original whole transformations. This is the usual ordinary
[arrow-isomorphism construction](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Comma/Arrow.html#CategoryTheory.Arrow.isoMk)
specialized to identity endpoint isomorphisms. This mathematical explanation
is not a derivation in the current Lambdapi interface.

The promoted normalizers are an explicit computational universality
extension beyond the current β interface, not derived theorems from the
old pointwise contractibility operations. Their primitive status, eight
identity endpoint rules and model interpretation are recorded in the owner
ledger. The presentation remains revisitable under the same
computational/internal criterion as the retained reconstruction law.
This is terminal/initial universality, not an axiom for the canonical
Coim⇒Im map, Abelian normality, connecting or exactness. Those constructions
and their required comparisons must still be implemented and qualified.

### Deferred generalization: categorical terminality and univalence

User clarification (2026-09-13): the current OneCat presentation is
acceptable for now, but the original terminal/initial interface should
eventually be reviewed for a primary general categorical formulation.
This is a deferred foundational refinement, not a prerequisite for C2c.

OneCat(C) is a current qualification guard, not a mathematical restriction
on terminality. The existing contractibility field reads
IsContr(Hom C x t) = IsContr(Obj(Hom_cat C x t)). That field by itself
contracts the object/core groupoid; it does not account for noninvertible
higher arrows of the Hom category. Object-univalence identifies paths with
equivalences, not arbitrary directed arrows. For example, the one-object
category with endomorphism monoid (ℕ,+) has only the identity isomorphism,
so its object/core groupoid is contractible and it satisfies ordinary
object-univalence, while the category is not equivalent to Terminal_cat.
The relevant distinction follows the standard
[univalent-category definition](https://arxiv.org/abs/1303.0584).

The appropriate categorical contraction is equivalence of the whole
category D to Terminal_cat. A proposed native expression is
OmegaEquivAlong(Cat_cat,D,Terminal_cat,Terminal_func(D)), keeping the
canonical forward functor. Equivalently, choose d and a whole natural
equivalence between id_D and const_d; an objectwise groupoidal Σ/Π of
equivalences is insufficient. Under the appropriate universe/functor-category
univalence, this can be read as D=Terminal_cat. It is not the assertion
IsContr(Obj D). The current OmegaEquivAlong has equality-valued inverse
laws, so their higher interpretation must be qualified at the corresponding
functor-category level.

Apply categorical contraction to Hom_cat(C,x,t), coherently in the native
Hom family, rather than to C itself. A Došen-style primary formulation is
the higher/coherent adjunction Terminal_func(C) ⊣ Obj_func(C,t), with the
dual adjunction for initiality. Preserve hom_int/homd_int as owners. The
existing whole terminal transformation may already supply some required
coherence under an appropriate strict/pseudo profile; no claim that the
entire present TerminalObject package is insufficient is established here.
Univalence alone does not qualify that profile or turn lax comparison cells
into equivalences.

When the relevant Hom categories are already groupoidal, ordinary IsContr
is the appropriate contraction condition; this can apply beyond OneCat(C).
The later review should make categorical universality primary and derive
the current pointwise/ordinary views and family normalizers where justified.
Equivalence/equality presentations must remain distinct from DefIso's
chosen judgmental inverse cuts: univalence does not supply those rewrite
laws automatically. Keep the current code and C1 guards until that general
construction and its computation have actually been qualified.

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

NUH-4C2a resolves the earlier transpose-alignment boundary. The
[ordinary-target transpose owner](../emdash2/emdash3_2_one_cat_diagram_transpose.lp)
first exchanges h, introduces its arrow family in Functor_cat(B,C), and
exchanges the remaining arguments. Columns are observations of that one
whole functor. The
[unit/counit instances](../emdash2/emdash3_2_one_cat_kernel_cokernel_transposes.lp)
now retain the actual Arr(κ)/Arr(q) endpoints. Two whole evaluation folds
and three narrow proof-time comparisons supply the required computation;
no new primitive or naturality-square input is introduced. The transpose
interface explicitly takes OneCat(C), without claiming arbitrary lax/oplax
interchange.

NUH-4C2b now [specializes the universal comparisons](../emdash2/emdash3_2_one_cat_adjunction_zero_columns.lp)
at the original zero-end columns ZP/ZQ. Their identity components retain
the nonzero endpoints. Composing with the original transposed cells gives
actual whole mate inputs Arr(κ)⇒I∘ev₁ and J∘ev₀⇒Arr(q), without casts or
caller square equations.

The [whole cokernel-family mate](../emdash2/emdash3_2_cokernel_adjunction_families.lp)
is defined by ε∘Q(h). Together with the existing whole kernel-family mate,
it defines [two canonical whole factors](../emdash2/emdash3_2_one_cat_image_coimage_factors.lp):

```text
v:Coim⇒ev₁       u:ev₀⇒Im.
```

At every original d, the native mate reconstruction laws prove
v_d∘π_d = d[0→1] and ι_d∘u_d = d[0→1]. These are derived reviewer
observations; the direct runtime conversion assertion for reconstruction
did not pass. The primary programs contain no ordinary factor dictionaries
or equation-proof operations. Do not advertise the observations as new
judgmental reconstruction cuts.

Next NUH-4C2c must construct a:Coim⇒Im and its whole factorization data.
The two pointwise reconstruction observations do not themselves construct
the required coherent annihilation/mate input. Keep the existing whole
units, counits and comparisons as program data; do not rebuild pointwise
cones or add a primitive comparison/exactness inhabitant. Abelian
invertibility of a remains genuine subsequent input structure.

C2c1 now supplies the [structural family adjunction](../emdash2/emdash3_2_one_cat_adjunction_families.lp)
(F∘−)⊣(G∘−), retaining the existing postcomposition functors. This is the
ordinary [whiskering of an adjunction](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Adjunction/Whiskering.html).
Two explicit structural primitives supply the lifted adjunction and the
OneCat profile of a functor category with ordinary target. The current
opaque classifiers have no constructors deriving these operations from
their β interface. Record them as primitive/model obligations.

Two whole unit/counit rules route to existing tele-postcomposition of the
original cells. Components and further action are projections of those
whole owners; separate component rules and caller naturality squares are
unnecessary. Defined forward/backward mate functors reuse the existing
Hom comparison and inverse cuts. Cancellation of whole transformations,
whole mate functors and their next Hom projections checks at the native
postcomposition endpoints. The original normalized C2b inputs yield the
expected Coim/Im endpoint types, and both inverse operations recover the
entire original coherent input, including its component at any diagram.

C2c2 now resolves the whole formula comparison in an optional
[family-view extension](../emdash2/emdash3_2_one_cat_adjunction_family_views.lp).
Three proof-time helpers compare two compositions of Cat horizontal actions,
the horizontal actions themselves, and mixed represented/raw associativity.
Corresponding operands and endpoints must compare; this asserts no
mathematical injectivity of composition. Guarding both horizontal-action
heads preserves the existing generic associativity rule. The earlier
unguarded congruence candidate shadowed that rule and was rejected.

Four defined paths prove the whole native/raw mate agreement in each
direction and reconstruct the entire original input by applying the same
inverse mate to the raw formula. These paths use the original adjunction
Hom comparison, equality action and native inverse cuts. They add no
universality primitive or runtime rewrite. The actual K/Q formulas and both
published Coim/Im factors pass, including component and whole Hom-action
comparisons and rejection of unrelated inputs. Original H and factor bodies
remain unchanged. Raw-formula reconstruction is a proved equality, while
the original native mate pair retains its judgmental cancellation.

Next C2c3 must connect these whole input equations to their whole evaluation
observations, then assemble the coherent annihilation input and canonical
a:Coim⇒Im. A focused probe of the normalized cokernel-unit input stops at
`sym_transf_tapp0_transf` when compared with `diagram_evaluation_transf`.
Its existing component-at-each-diagram check is not a whole evaluation
proof. Start with the existing evaluation/postwhiskering comparison and
retain the original normalized input and terminal-family comparison.
Qualify any missing whole projection at that actual owner; do not replace
it with a pointwise cone reconstruction or a primitive a/exactness witness.
The final comparison's components and higher observations must come from
that same constructed term. The terminality/profile generalization and the
old LES endpoint-checker investigation remain deferred.

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
