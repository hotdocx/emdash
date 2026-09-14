# Categorical Exactness And Connecting: Native Owner Plan

Date: 2026-09-13

Status: C6e2c all three native-window exactness comparisons qualified; model/reifier next; Op/duality deferred

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

The canonical whole comparison a:Coim⇒Im is now constructed from the existing
units/counits and mate operations in C2c4 below. Abelian structure requires
invertibility of this actual comparison. Kernel/cokernel existence alone does not imply
that condition. This is the usual coimage/image criterion in
[Stacks, Definition 12.5.1](https://stacks.math.columbia.edu/tag/00ZX).

Attach existing categorical invertibility evidence to the canonical map,
and obtain its inverse from that structure. Choose the actual strength
explicitly: OmegaEquivAlong has equality-valued inverse laws; DefIso has
judgmental inverse cuts. Do not infer one from the other without a qualified
construction, introduce a duplicate equivalence grammar, or choose a second
independent inverse merely to make a later comparison typecheck.

C3 now implements [fixed-comparison normality](../emdash2/emdash3_2_one_cat_adjunction_normality.lp):

```text
Normality(P,Q) = OmegaEquivAlong(a)    in Functor_cat(D,C)
a⁻¹ = left_inv(N) : Im ⇒ Coim
a⁻¹∘a = id_Coim                     a∘a⁻¹ = id_Im.
```

The existing `omega_equiv_left_as_right_law` derives the second equation
for the same selected inverse from the original left/right candidates.
The whole `IsoEvidence` view retains a literally as its forward arrow.
These are ordinary equation witnesses, not new DefIso judgmental cuts.
Precomposition by a whole diagram family F:B→D transports fixed-a evidence
using the existing generic functor action. The inverse of the restriction
computes to the restriction of that same whole inverse. Components and
further Hom action remain native observations, with no caller square proof.

The [native Abelian adjunction structure](../emdash2/emdash3_2_one_cat_abelian_adjunctions.lp)
is indexed by the original AdditiveCategory A (including selected whole
binary products and terminal t), OneCat(C), and the original initial
presentation at t. It stores P, Q and Normality(P,Q) in dependent Sigma.
Projections retain these actual structures and the same whole H program.
The additive hypothesis is required by the standard Abelian criterion;
K/Q existence and comparison invertibility alone do not supply binary
products. The nine definitions introduce no new classifier primitive,
rewrite, unifier or ordinary universal dictionary. The initial prototype's
inverse-law proof duplicated an existing library lemma and was not promoted.

Normality remains supplied Abelian structure. The package constructor does
not infer it from K/Q or build a closed concrete Freyd model. Concrete
construction and comparison with the old normality providers remain later
model obligations. This is the native condition and its computational
consumer, not a proof that every whole pre-Abelian presentation is Abelian.

C4b now constructs the
[canonical comparison](../emdash2/emdash3_2_one_cat_image_kernel_comparison.lp).
For whole h:J∘A⇒D over B, let f be the original source observation of h and
F=Arr(f). Both are [defined before universal selection](../emdash2/emdash3_2_zero_arrow_family_observations.lp).
Keep β as the existing whole H boundary `kernel_adjunction_family_boundary_transf`.
The original counit, whole prewhiskering of zero and native mate faithfulness
derive β∘κ_F=0, with the actual restricted kernel-arrow family. Then

```text
β̄ = cokernel descent of β : Coim∘F ⇒ K∘D
e = β̄ ∘ (a restricted to F)⁻¹ : Im∘F ⇒ K∘D
e∘a_F = β̄.
```

The original Q is evaluated at Arr(κ)∘F; no reconstructed kernel arrow or
new universal selection supplies the source of descent. Native inverse
mating of β̄, and of e∘a_F, reconstructs the original whole β. Its kernel
inverse-mate projection reconstructs f. Whole reconstruction through a_F
determines e uniquely. These are defined paths and native cuts, with
component, arbitrary base-arrow and next Hom observations; no caller
pointwise cone or naturality dictionary enters the program.

`OneCatAdjunctionExactFamily` is existing OmegaEquivAlong on this actual e
in Functor_cat(B,C). It is a condition on the chosen coherent family, not
an automatically supplied inhabitant. The whole specialization to the
existing ZeroArrowCone category uses its existing tautological transformation;
it does not assert that every zero pair is exact. Generic evaluation derives
point evidence from supplied whole exactness evidence. The LES must still
prove the condition at its own output positions from the short-exact input.

The current comparison follows the planned Abelian coimage route and takes
the original normality N. Its four proof-time comparisons are required by
actual native/whole consumers: shape-arrow reindexing, constant precomposition,
congruence of a composite of two shape observations, and represented outer
associativity. The congruence guards both operands and compares complete
maps/endpoints; it asserts no injectivity. Cat-specific action views preserve
the raw observation signatures while native indices remain inside inverse
and evidence eliminations. No runtime head is merged, no new primitive or
naturality rewrite is supplied, and the general lax/oplax profile boundary
is unchanged. The owner ledger records failures, refinements and exact checks.

C4a now provides [whole original-family inputs](../emdash2/emdash3_2_one_cat_cokernel_family_inputs.lp)
and [cokernel descent with characterization](../emdash2/emdash3_2_one_cat_cokernel_family_descent.lp).
For D:B→Arr(C), u:E₁D⇒Y and one whole annihilation cell z:u∘∂D=0:

```text
ρ_D : D ⇒ Arr(∂D)
h(D,u,z) : D ⇒ I∘Y
desc(D,u,z) = untranspose_Q(h(D,u,z)) : Q∘D ⇒ Y
transpose_Q(desc(D,u,z)) ≡ h(D,u,z)
E₁(transpose_Q(desc(D,u,z))) = u.
```

The canonical zero is the whole composite through const_t, using the
original terminal/initial arrow families. An introduced-diagram input comes
from one native square in Functor_cat(B,C), exchange, and the initial-family
normalizer. For an arbitrary D, apply the existing reconstruction inverse
to Sym(D) in Functor_cat(B,C) and exchange back to ρ_D. Its whole endpoints
are identities; compose the introduced input with ρ_D. This leaves D itself
as the argument of Q, so no reconstructed diagram or replacement universal
selection becomes the result's endpoint. Input formation and both target
observations depend only on the diagram/terminal-family interfaces; the
cokernel structure enters at descent, not during input formation.

The native inverse mate recovers this entire coherent input. Whole evaluation
recovers u, and the existing projected mate faithfulness gives uniqueness:
E₁(transpose_Q(b))=u ⇒ b=desc(D,u,z). These are internal whole paths, not
caller per-object cone/naturality premises. Generic raw-formula agreement
retains components, arbitrary parameter maps and the next Hom functor.
The original C2c4 comparison input and its target-view proof now call the
same introduced constructor; exact comparison with their old bodies passes.
The original a, its normality data and H selections therefore keep their
computational owners. No new primitive, runtime rule or unifier is added.

C5 now constructs the
[whole cokernel row comparison and kernel-cokernel pair](../emdash2/emdash3_2_one_cat_short_exact_families.lp).
Generic ordinary naturality of the exchanged h and initial-family uniqueness
derive g∘f=0 as one whole path. The existing descent at F=Arr(f) gives

```text
γ : Q∘F ⇒ E₁D         E₁(transpose_Q(γ)) = g
β : A ⇒ K∘D           (the original whole H boundary)
ShortExactFamily(h) = OmegaEquivAlong(β) × OmegaEquivAlong(γ).
```

Both comparison maps are defined before their invertibility is supplied.
The kernel inverse is a whole K(g)⇒A; the cokernel inverse is a whole
E₁D⇒Q(f). The latter is not a section into the middle term E₀D. Existing
inverse-candidate laws give both equations for each selected inverse, and
generic action gives component and further Hom observations. There is no
new equivalence grammar, ordinary factor dictionary, primitive, rewrite or
unifier. The construction does not need global normality merely to express
a kernel-cokernel pair; the connecting theorem retains the original Abelian
normality where required.

This is the whole short-exact input interface, not an output exactness proof
or a concrete model constructor. The LES still has to derive its actual
comparison invertibility. Formal comparisons with the retained ordinary
row/exactness views remain obligations at their actual consumers.

C6 next constructs the whole fibre-product family and its projections used
by the connecting cover. Start from the existing whole categorical products
and universal operations, with the original P/Q selections. Derive the
required whole maps and compatibility cells internally; do not rebuild
per-object cones or silently assume a whole additive/fibre-product interface
that the current owners do not provide. Then construct the cover, covered
map and coimage descent below and prove output exactness from the original
short-exact-family data and Abelian structure.

C6a resolves the whole-product prerequisite. BinaryProducts already retained
the original whole P and projection transformations, but its represented
pairing only varied the source with the two targets fixed. The
[ordinary Δ⊣P presentation](../emdash2/emdash3_2_one_cat_product_adjunction.lp)
and [whole family mates](../emdash2/emdash3_2_one_cat_product_families.lp) now give

    pair : Transf(X,F) × Transf(X,G) → Transf(X,P∗(F,G))
    unpair : Transf(X,P∗(F,G)) → Transf(X,F) × Transf(X,G).

These are whole internal functors with computing inverse composites and
retained higher action. Native endpoint annotations stay inside mate
applications. Component agreement with the original selected pairing is
derived from the whole mate formula, the existing product action comparison
and its original cuts. Both original component projections recover f/g.
No caller naturality squares or new product selection are introduced.

The product-category ordinary profile and Δ⊣P at the same P/BP are two
explicit structural primitives. Today's opaque classifiers do not construct
them from their β interface; they remain model interpretation obligations.
Two structure-specific runtime rules retain the original whole counit
(π₁,π₂) and original diagonal unit components. Nine proof-time views handle
literal-diagonal projections, existing composite/constant normal forms and
paired components. They preserve runtime owners and all relevant data.
The earlier runtime diagonal folds, which introduced eight overlaps, were
not promoted. Thirty-seven assertions and exact unchanged-dependency
warning comparisons qualify this ordinary presentation.

PreadditiveCategory still supplies ordinary Hom-group operations without a
whole varying-family addition transfor. PullbackStructure remains a separate
coherent slice-base-change capability, not yet constructed from this native
Abelian package. C6b must now construct the whole fibre-product family and
its projections through the original product/K/Q owners, then the cover,
covered map and descent for δ. Do not silently supply either missing
capability or turn the new exactness predicate into an assumed theorem.

Current C6b refinement: the actual connecting pullback has a kernel
inclusion as its right leg. For p:B→C and d:C→D, construct its carrier as
K(d∘p), with κ(d∘p) to B and the native kernel mate to K(d). The semantic
reason is K(d)=C×_D0 and pullback associativity, giving
B×_C K(d)≅B×_D0. This is an application of
[the represented-functor/pasting description of fibre products](https://stacks.math.columbia.edu/tag/001U),
not a new general PullbackStructure assumption. It addresses precisely the
pullback needed for the original cover. The maps, ambient reconstruction
and native cartesian universal comparison are now constructed below.

C6b1 now [implements whole kernel lifting](../emdash2/emdash3_2_one_cat_kernel_family_lift.lp)
at an arbitrary original D, with whole input reconstruction, source recovery
and uniqueness. The annihilation witness does not change the resulting
whole lift. Its kernel-independent input owner also forms Arr(d∘p) directly
from the original whole d and p.

The [precomposition owner](../emdash2/emdash3_2_one_cat_kernel_precomposition.lp)
constructs L=K(d∘p), a=κ(d∘p):L⇒B and r:L⇒K(d). The existing kernel
annihilation gives d∘p∘a=0; r is the native lift into the original D.
If Γ_D is source evaluation after the native kernel inverse mate, the
checked reconstruction is Γ_D(r)=p∘a. All 14 operations are definitions;
22 assertions pass without new primitive or rule.

C6b2a now [defines Γ_D as a first-class internal functor](../emdash2/emdash3_2_one_cat_kernel_family_projection_paths.lp).
Its native Hom endpoints remain literal inside composition and application,
so source evaluation after inverse mating computes. Existing rigid Hom_func
factorizations provide the whole whiskering comparison. Four sufficient
proof-time views cover the next-Hom factorizations, raw Cat composition and
the identity-middle projection order. Runtime owners are unchanged.

The [reconstruction owner](../emdash2/emdash3_2_one_cat_kernel_family_reconstruction.lp)
proves Γ_D(v)=κ_D∘v for an entire transformation v, reconstructs the original
k after lifting, and derives equality reflection through κ_D. Specializing
to r gives the actual whole equation κ(d)∘r=p∘a. Both original inclusions
and the same K/D are retained. Fifteen definitions and 22 assertions add
no primitive or runtime rule. The proved Γ equation is an observation
on whole transformations; a separate whole natural comparison in the test
variable is not silently assumed.

C6b2b now [constructs the cartesian universal comparison](../emdash2/emdash3_2_one_cat_kernel_pullback_universality.lp).
Write 𝒞=Functor_cat(B,C), Y=E₀D and a:𝒞/X. Its actual forward functor is

```text
Φₐ : Hom_(𝒞/X)(a,κ_(d∘p)) → Hom_(𝒞/Y)(Σ_p(a),κ_d).
```

The target is the existing pullback_cone_cat, which takes no
PullbackStructure argument. Φₐ composes native Σ_p Hom action with
postcomposition by the already proved square. The original two inclusion
objects require only their original K/diagram data.

The [inverse object program](../emdash2/emdash3_2_one_cat_kernel_pullback_lifts.lp)
reads the native slice cell in a genuine zero-Hom, derives one whole
annihilation path and applies the original whole kernel mate. Its first
leg recovers the original test arrow; original kernel equality reflection
recovers the second leg. This supplies no caller naturality square.

[Native slice equality](../emdash2/emdash3_2_one_cat_slice_paths.lp) is derived
by Sigma elimination with equality in the actual native Hom as the motive.
The triangle fibre is proposition-valued at OneCat(C); no arbitrary Sigma
eta or classifier cast is introduced. Existing constructor action similarly
derives arbitrary-input preservation of the slice domain arrow.

The genuine zero-Hom profiles let the existing core inverse and Path_map
[internalize the inverse object program](../emdash2/emdash3_2_groupoidal_object_maps.lp).
Core reflection gives propositional agreement with that original program.
The existing set-target whole transformation assembly then derives both
whole functor paths Iₐ∘Φₐ=id and Φₐ∘Iₐ=id. Existing OmegaEquivAlong packages
these laws, selecting the same constructed Iₐ in both inverse slots.
The actual inverse also exposes both recovered ambient legs directly.
No new judgmental point or inverse-composition beta is installed.

The two explicit structural/model primitives are
OneCat(C)→OneCat(C/X) and IsDiscreteCat(B)→IsDiscreteCat(Functor_cat(A,B)).
These extend the current opaque profile interface with standard closure in
the ordinary/discrete interpretation. They supply neither the comparison's
inverse nor its universal law. Thirty-four definitions, two primitives and
38 assertions qualify this ordinary cartesian comparison without new
runtime/unification rules or a general coherent PullbackStructure.

C6c1 now [derives the original whole cokernel target observation](../emdash2/emdash3_2_one_cat_cokernel_family_projection_paths.lp).
Target evaluation after the native transpose is an actual Hom functor;
its application computes and its whole ambient path is Λ_D(v)=v∘q_D.
[Reconstruction and equality reflection](../emdash2/emdash3_2_one_cat_cokernel_family_reconstruction.lp)
retain the original D/Q and whole input u. Descent does not depend on which
annihilation witness was supplied.

The [whole short-exact row reconstruction](../emdash2/emdash3_2_one_cat_short_exact_family_cancellation.lp)
gives κ_D∘β=i and γ∘q_F=g at the original maps. Kernel and quotient
reflection, followed by cancellation using the original fixed-forward
β/γ inverse laws, prove incoming and outgoing whole row cancellation.
The reconstruction lemmas require only their respective K or Q; the row
cancellation consumers retain the original combined row evidence.

The [canonical map ρ=q_H∘r](../emdash2/emdash3_2_one_cat_homology_cover_maps.lp)
is now constructed. Its original q_H is Q's projection at the same whole
boundary diagram used by H. It has whole quotient cancellation and retains
component/further-Hom action. The present map interface takes the original
coherent right-column h and p; native window assembly and epicity of r/ρ
remain obligations. Nineteen definitions and 23 assertions add no primitive,
runtime rewrite or unifier. No cover property is assumed by the constructor.

C6c2 now [assembles the native window maps](../emdash2/emdash3_2_one_cat_native_homology_window_maps.lp).
Four original row functors Rₘ,R₀,R₁,R₂:B→ZeroArrowCone_cat and three whole
transformations supply all vertices and maps. The two middle-column
chain-zero laws are whole mathematical input. Each row's short-exactness
is the existing fixed-map β/γ evidence at its original whole zero datum;
no new window carrier, opaque constructor or ordinary factor dictionary
is introduced.

[Whole postcomposition-family action](../emdash2/emdash3_2_one_cat_family_naturality_paths.lp)
gives the two commuting row squares. [Native row observations](../emdash2/emdash3_2_one_cat_zero_cone_row_families.lp)
retain the original row functor before K/Q selection. Incoming cancellation
at the last row derives the left column zero; outgoing cancellation at
the first row derives the right column zero. The
[column input constructors](../emdash2/emdash3_2_one_cat_zero_cone_column_inputs.lp)
then call the existing whole kernel-input builder. The
[native incoming observation](../emdash2/emdash3_2_one_cat_kernel_input_observation_paths.lp)
recovers the original whole differential in each column.

The [whole row lift](../emdash2/emdash3_2_one_cat_short_exact_family_lifts.lp)
is a native Hom functor: the original K transpose followed by β⁻¹
postcomposition. Its original-diagram input and reconstruction remain
whole. Applied to the covered middle differential, it gives λ:L⇒A₁ with
i₁∘λ=d_B∘a_L. The next row's incoming cancellation and the middle chain
law show d_A∘λ=0. The original left kernel gives v:L⇒K(d_A), with
κ_A∘v=λ, and the [covered map](../emdash2/emdash3_2_one_cat_homology_covered_maps.lp)
is θ=q_A∘v. The first row lift requires only its two adjacent rows and
next-row β evidence; the following row and chain law enter when making
it a left cycle.

The assembly returns ρ:L⇒H_C and θ:L⇒H_A with the same literal
L=K(d_C∘p₀). H_C and H_A are the original H constructions at the derived
native column inputs; no object cast or new selection aligns their types.
The original short-exactness evidence E₀ for R₀ remains in the window
interface for the upcoming cover-epicity proof; map construction does not
yet consume it.

Two [proof-time comparisons](../emdash2/emdash3_2_diagram_reindex_views.lp)
resolve actual owner-presentation gaps: accumulated evaluation versus
composition with the evaluator, and the same whole h observed under
native/raw composed parents. Both retain every original functor, point,
target and transformation. They add no runtime fold. Source recovery is
staged while h is a variable, then instantiated at the actual input;
that is necessary for compound column functors. Forty-two definitions,
two unifiers and 41 assertions qualify this stage without a new primitive,
runtime rule or edit of an earlier LP owner.

Next C6c3 derives r/ρ epicity and θ∘κ_ρ=0 from the original short-exact
rows and Abelian normality. Check which whole additive and further cover
operations this proof actually needs; construct them before use. C6a's
product-family pairing is available; C6c3a below supplies whole copairing
and addition. Signed whole laws and general coherent PullbackStructure
are not assumed merely from the previous kernel-square proof. Then apply
the original coimage/cokernel descent for δ and prove its reconstruction.
Output exactness, concrete model/reifier construction and snake comparison
remain required.

C6c3a now supplies [whole copairing](../emdash2/emdash3_2_one_cat_copair_families.lp)
and [whole addition](../emdash2/emdash3_2_one_cat_additive_families.lp).
The native transpose/untranspose pair of Prod⊣Δ gives both whole inverse
cuts and higher action. Precomposition with the existing product-family
diagonal gives addition. Derived component paths recover the original
additive copairing and sum, with no caller pointwise naturality fields.

The [ordinary Prod⊣Δ presentation](../emdash2/emdash3_2_one_cat_biproduct_adjunction.lp)
is one explicit structural/model primitive at the same original Prod/t/A
and supplied original T0. Its whole unit is the pair of injections already
constructed by Δ⊣Prod; counit components are the original codiagonal.
Today's opaque Adjunction classifier does not assemble this from point
laws. This model obligation and its two runtime coupling rules are explicit;
the other 16 operations are definitions, with no new unifier or earlier LP
edit. The owner ledger records qualification and the native-parent staging.

C6c3b now [constructs the whole shear and its inverse](../emdash2/emdash3_2_one_cat_shear_families.lp),
then [whole negation](../emdash2/emdash3_2_one_cat_negative_families.lp) and
[subtraction](../emdash2/emdash3_2_one_cat_difference_families.lp). The whole
S(x,y)=(x,x+y) is formed before its scalar inverse is proved. Existing
fixed-forward pointwise-to-whole ΩAlong assembly then gives S⁻¹, preserving
the literal original scalar inverse. Extract −id=(π₂∘S⁻¹)∘ι₁ and restrict
that universal transfor through generic whiskering/postcomposition.
Whole naturality proves both signed composition laws. Product_map_func
constructs subtraction's signed input at addition's native Hom endpoint.

All 41 operations are definitions, with no new primitive, rewrite, unifier,
product selection, caller naturality square or Q argument. Native
unpair(id) supplies whole projections; Sigma elimination and the forward
mate cut derive their original component readbacks. No raw projection or
counit metadata fold is needed. The owner ledger records the resolved
experiments and final qualification.

C6c3c1 now proves [whole addition bilinearity](../emdash2/emdash3_2_one_cat_additive_family_bilinearity.lp)
and [whole subtraction bilinearity](../emdash2/emdash3_2_one_cat_difference_family_bilinearity.lp)
on both sides of composition. Original native mate naturality gives whole
product projection β, pair/copair distribution and diagonal naturality at
the same selected product-family endpoints. No pointwise equality assembly
or whole additive-functor-category capability is supplied.

Thirty-one definitions and five proof-time comparisons add no primitive,
runtime rule or earlier LP edit. Native diagonal Hom action and identity
application, native projected composition, and unchanged whole composites
under endpoint presentations are the qualified comparison boundaries.
Both actual arrows are repeated in the composite view; existing
associativity remains available. Literal native Sigma parameters matter
inside observations. General Sigma β/η experiments are not promoted.
The owner ledger records the consumers, controls and warning evidence.

C6c3c2 now proves [whole additive inverse laws](../emdash2/emdash3_2_one_cat_additive_family_inverse.lp)
and [cancellation](../emdash2/emdash3_2_one_cat_additive_family_cancellation.lp).
The original shear gives id+N=0. Checked restriction of the original
mate/pair/copair/addition programs transfers this to the existing N_X,
yielding f+(−f)=0 and f−f=0. The shear cancels a common left summand;
fixed-forward invertibility of original whole N gives negation reflection.
Together they prove f−g=0 ⇒ f=g. Equal pre/postcomposites yield zero
composed differences, and direct-shear N agrees with universal restriction.

Thirty-eight definitions and eight proof-time views add no primitive,
runtime rule, operation reselection or earlier LP edit. Whole action,
original endpoints/inputs and native inverse cuts remain the owners.
Two unused comparison experiments are not promoted. This does not supply
a full additive capability on the functor category or unstated unit laws.

C6c3e1 now derives the [auxiliary categorical difference cover](../emdash2/emdash3_2_one_cat_difference_covers.lp).
For D=f∘π₁−p∘π₂ with p the original short-exact row's outgoing map,
whole pairing and difference cancellation imply q_Dp=0, hence q_D=0.
Lifting id through the original K(q_D) makes the image inclusion
invertible. Original Coim⇒Im normality then makes the existing Coim(D)⇒Z
factor invertible. The original factor agrees with ι∘a by native/raw mate
reconstruction and whole quotient cancellation. Twenty-six definitions add
no primitive, runtime rule or unifier.

C6c3e2 now [derives the original r cover](../emdash2/emdash3_2_one_cat_kernel_precomposition_covers.lp).
K(κ_d∘π₁−p∘π₂) maps into the original L=K(d∘p), with both projection
comparisons. Descending coker(r)∘π₁ through the auxiliary cover, then
using the second and first injections, proves coker(r)=0. Original q_H
cancellation then proves coker(ρ)=0. The existing native window obtains
both results from its original row E0 and supplied normality; no separate
cover or epicity argument is present.

The new [whole coimage-cover descent](../emdash2/emdash3_2_one_cat_coimage_cover_descent.lp)
retains the original Q at the original kernel-arrow diagram. It reconstructs
u after the original differential and uses the same selected cover inverse.
Thirty-five definitions add no primitive, runtime rule or unifier.
C6d1 now [constructs δ at the original native window](../emdash2/emdash3_2_one_cat_native_homology_window_connecting.lp)
by two universal descents: first θ through r to γ, then γ through the
original q_C after proving γβ_C=0. The original upper middle differential
provides the lift used in the second proof. Whole reconstruction gives
δρ=θ, hence θκ_ρ=0; the existing ρ cover gives uniqueness. The single
coimage descent along ρ agrees as a whole map. Twenty-eight definitions
add no primitive, rewrite or unifier. Output exactness, concrete
model/reifier work and snake comparison remain open.

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

For a coherent family, e is now a constructed whole transformation. Exactness
evidence for a family/LES position must apply to that whole comparison;
ordinary per-position predicates can be derived observations. Use existing
native zero-pair/window data and whole K/Q, not a separate cone grammar.
Short exact rows can similarly retain both canonical mate comparisons
A→K(p) and Q(i)→C as invertible: a categorical kernel-cokernel pair.

The LES exactness theorem must derive these comparison isomorphisms from
the short-exact input and Abelian structure. It must not postulate their
invertibility or assume the theorem through an exactness capability.

C6e1 now constructs the adjacent whole H(i)/H(p) maps using original K/Q
functor action on native whole boundary-diagram maps. Existing row naturality
supplies their compatibility, and original quotient laws characterize the
induced cycle maps. The middle-column input precedes K/Q selection.
All three zero composites H(p)H(i), δH(p) and H(i)δ are proved. The
[native-window exactness inputs](../emdash2/emdash3_2_one_cat_native_homology_window_exact_inputs.lp)
now form the actual Im⇒K comparisons at all three positions. C6e2 must
still construct their inverses from the original short-exact input; no
output exactness inhabitant has been supplied. Fifty-two definitions and
two guarded unit comparisons add no primitive or runtime rewrite.

C6e2a now proves zero kernel inclusions for all three actual native-window
comparisons. The generic identity κ_g e=ι_f and original image-kernel
cancellation give this result. The
[native inverse criterion](../emdash2/emdash3_2_one_cat_image_kernel_exactness.lp)
constructs an inverse of e when the original quotient of β:A⇒K(g) is
proved zero, using original Q/K cancellation and normality. An original
short-exact row derives this premise through its β equivalence. The three
LES instances must still derive their own boundary-quotient zeros from the
window; no such zero or output exactness witness is assumed. Seventeen
definitions add no primitive, rewrite or unifier.

C6e2b1 now derives [whole cycle and boundary representatives](../emdash2/emdash3_2_one_cat_homology_representatives.lp)
after categorical covers, using the original quotient and normality.
Applied to the actual K(H(p)), three covers produce w=b−β_Mb₀ with
K(p)w=0. The [original left cycle lift](../emdash2/emdash3_2_one_cat_middle_homology_cycles.lp)
gives K(i)a=w, and all three cover-cancellation instances are derived.
The equivalences certify the original Coim(r)⇒target factors, not splittings
or inverses of the cover maps r. Fifty-six definitions add no new primitive,
rewrite or unifier. C6e2b2 completes this middle proof below.

C6e2b2 derives [whole additive unit laws](../emdash2/emdash3_2_one_cat_additive_family_units.lp)
from the original coproduct injection and native mate cuts. They give
q_Mw=q_Mb. Original K reconstruction and the H(i) quotient law identify
β_H(q_Aa)=r₁r₂r₃. Original Q annihilation and three cover cancellations
prove the actual boundary quotient zero, so the existing criterion gives
an inverse of the [original middle comparison](../emdash2/emdash3_2_one_cat_middle_homology_exactness.lp).
Its native-window specialization retains the literal original row-triple
diagram. Twenty-eight definitions and six proof-time reindexing views add
no primitive or runtime rewrite. C6e2c below completes the H(p),δ and
δ,H(i) positions; model/reifier and snake comparison work follow.

C6e2c uses the following two constructions through the same representative
programs and original inverse criterion:

1. For H(p),δ, cover the actual K(δ) through the original ρ:L⇒H_C.
   Since δρ=θ, its lifted left cycle has zero H_A class. The existing
   boundary-representative cover gives a left boundary. Subtract its image
   from the original middle lift, use the whole difference laws to obtain
   a middle cycle, and reconstruct the original right class through H(p).
   Original kernel cancellation and the covers must force the actual
   boundary quotient zero.
2. For δ,H(i), cover the actual K(H(i)) through the original q_A. Its
   induced middle cycle has zero middle homology class, so the existing
   boundary-representative program gives a middle boundary representative.
   Its original row projection is a right cycle. Lift that same middle
   representative into the original L and use δρ=θ to reconstruct the
   original left class. Cancel the covers to obtain the actual boundary
   quotient zero, then certify the original comparison.

C6e2c now implements both sketches through the original whole operations.
The source and target boundary quotients are proved zero, and the original
Im(H(p))⇒K(δ) and Im(δ)⇒K(H(i)) comparisons have derived inverses.
All three native-window positions are therefore proved in the stated
ordinary setting. The [source proof](../emdash2/emdash3_2_one_cat_connecting_source_exactness.lp)
and [target proof](../emdash2/emdash3_2_one_cat_connecting_target_exactness.lp)
retain the original H, L, ρ, θ and inverse selections. Sixty-one definitions
add no primitive, rewrite, unifier or earlier LP edit. Supported model/reifier
realization, snake comparison and final qualification remain required.

## Connecting As Whole Universal Descent

For a short exact sequence of complexes in the ordinary abelian setting,
the implemented primary program uses the two native descents described
above. The following single-descent expression is a proved whole comparison
view of that program, with every object/map varying internally over the
existing short-exact-window input.

1. Form Pₙ = Bₙ ×_{Cₙ} K(d⁽ᶜ⁾ₙ) categorically. For this kernel leg, use
   K(d⁽ᶜ⁾ₙ∘pₙ) and derive its cartesian comparison through native mates;
   no element lift or splitting of Bₙ→Cₙ is selected.
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

The whole cover, covered map, connecting map, annihilation and comparison
are now implemented under their recorded ordinary/profile assumptions.
Their agreement is an equality of whole transformations, not an asserted
judgmental identity. Output exactness remains a further proof obligation.
Generic naturality is supplied by the existing whole operations, without
caller-supplied squares or construction-specific naturality rules.

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

The C2b milestone left a:Coim⇒Im and its whole factorization data to C2c,
now completed through C2c4 below.
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

C2c3 now proves the two whole evaluation observations. Write ∂ for the
original `diagram_evaluation_transf` of the walking-arrow generator, and
Eᵢ for the whole evaluator on diagram families. At the original normalized
inputs h_Q:J∘ev₀⇒Arr(q) and h_P:Arr(κ)⇒I∘ev₁:

```text
E₀(h_Q) = ∂       E₁(h_P) = ∂.
```

The [whole evaluator](../emdash2/emdash3_2_diagram_evaluation.lp) is defined
as value evaluation after the existing argument exchange. The old component
alias delegates to it with the same normal form. Its ordinary composition
observation is an instance of the existing generic `fapp1_comp_path`;
no constructor-specific functoriality rule or caller square is supplied.

Two nucleus projection rules complete double exchange for the whole
transformation and its already-projected component. This follows the
ordinary [functorial flipping](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/Currying.html#CategoryTheory.Functor.flipping)
interpretation. The qualification here does not establish arbitrary
lax/oplax interchange or integrate the deferred profile migration.
Eight whole endpoint rules complete the same terminal/initial normalizer
presentation at `sym_transf_tapp0_transf`: the result is the identity of F
or const_t, including its whole parameter action. The original eight
point clauses remain because the earlier direct component consumers need
them. Both typed projection orders meet at the same endpoint identity.
These are computational clauses for the existing OneCat presentation;
its primitives, C1 guards and initial/terminal inputs are unchanged.

The [actual zero-column views](../emdash2/emdash3_2_one_cat_adjunction_zero_column_views.lp)
derive the displayed whole equations by the generic evaluator composition
path and those projection computations. They do not import the optional
mate-formula views or ordinary universal records. Whole, component,
Hom-functor and arbitrary diagram-map observations check. The equations
are proved whole paths; they are not new direct runtime rules for ∂.

C2c4 now constructs the
[canonical whole comparison](../emdash2/emdash3_2_one_cat_image_coimage_comparison.lp)
and proves its native whole factorization and uniqueness. The construction
uses the following derived whole observations, with OneCat(C) explicit:

```text
E₀(unmate_P(u)) = ∂        ∂∘κ = 0        u∘κ = 0
h_a : Arr(κ) ⇒ I∘Im       E₁(h_a) = u
a = untranspose_Q(h_a) : Coim ⇒ Im
transpose_Q(a) ≡ h_a.
```

Whole terminal/initial-family uniqueness and diagram-map reflection give
faithfulness of the projected inverse mates. Precomposition and zero
compatibility then derive u∘κ=0 from the original counit. An existing native
square in Functor_cat(D,C) uses that internally derived whole cell; realize
it as a walking-arrow map there, exchange back, and apply the existing
initial-family normalizer. This gives h_a at the original native Im and
Arr(κ) endpoints. No per-object naturality or cone dictionary is supplied.
The comparison itself is the original cokernel family mate applied to h_a.

For an arbitrary whole b:Coim⇒Im, the transparent observation

```text
fact(b) = E₀(unmate_P(E₁(transpose_Q(b))))
fact(a) = ∂                  fact(b) = ∂ ⇒ b = a
```

retains both whole adjunctions. This is a function on whole transformations,
not a separately packaged internal functor in b. Its factorization and
uniqueness are derived paths; only the original native mate cancellation
above is judgmental. No ordinary factor records, comparison axiom or new
universality primitive enters the construction. Existing accepted shape,
terminal-family and lifted-adjunction primitives remain explicit model
obligations; this result does not derive them from their old β interface.

The implementation adds five one-way modules with 24 definitions, four
introduced-arrow evaluation clauses and two proof-time comparisons. The
four clauses compute E₀/E₁ after postcomposition by Arr(η), including the
object-first route. They do not install a general evaluator/postcomposition
fold or constructor-specific naturality. A generic fold was rejected by
its identity-postcomposition corner. The comparisons retain all supplied
operands and indices; they add no runtime normalization or injectivity law.

Whole/native reconstruction, actual component and diagram-map action, the
next Hom functor with its original endpoints, and unrelated-input rejection
are qualified by localized reviewers. The owner ledger records exact warning
comparisons, inference-slot audits and the rejected alternatives.

C3 above now attaches existing invertibility evidence to this actual a.
C4b constructs the canonical Im(f)→K(g) at native zero data and uses its
invertibility as the exactness condition. This is additional Abelian/exactness
structure, not a consequence of K/Q existence or of the two reconstruction
paths. Continue to whole
universal descent for δ; do not run the old ordinary-record program as the
primary implementation.

The terminality generalization, old LES endpoint-checker work, strictness
migration and duality repair remain deferred.

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
