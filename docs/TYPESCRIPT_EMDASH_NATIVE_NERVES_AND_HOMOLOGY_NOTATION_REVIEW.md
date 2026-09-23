# Native Nerves And Homology Notation: Review And Completion Boundaries

Date: 2026-09-23
Status: source review and exposition corrections complete; nerve completion stages below are proposed, not implemented
Baseline: main `44f50587`
Parent: [foundations/DevOps reassessment](TYPESCRIPT_EMDASH_FOUNDATIONS_DEVOPS_AND_CONTINUATION_REVIEW.md)

The user asks to consolidate the simplicial/cubical interpretation and its
unfinished comparisons, and clarify Arr, family versus component data, and
parameter categories in both forms of EMAIL.md. The native Hom owners remain
foundational. This review does not merge the profile branch, repair Op, claim
an unproved nerve equivalence or resume unrelated spectral work. No production
LP source changes are needed for the homological notation corrections.

## Main Assessment

The intended mathematical comparison is useful on both sides: an intrinsic
presentation should be related by whole internal maps to the corresponding
geometric mapping presentation. It should then respect the same index action.
These are genuine representability/coherence results about the current
constructions, not compatibility obligations with a retired algorithm.

However, a recursion on objects or an object decoder does not already give
an equivalence of categories or nerves. Three additional choices matter:
which earlier boundaries may vary, which functor/transformation profile the
mapping category carries, and which face/degeneracy maps belong to the index.
The current simplex and cube developments have reached different stages.

| Layer | Main's actual implementation | Unfinished result |
| --- | --- | --- |
| Flagged native simplexes | PathOut recursion; variable intrinsic codes, mapped decoding, nonempty faces and ordinal-source observations | Directed total category varying the earlier flags |
| Geometric simplex levels | CoherentNerveLevel_cat(C,n)=Functor_cat(DirectedSimplex_cat(n),C); generic nonempty face realization | Whole index-functor assembly and compatible reconstruction |
| Native simplicial nerve | No single whole native nerve yet | Native levels, coherent face action, comparison of whole nerves; degeneracies for full Δ |
| Native cubes | CubicalLevel_cat(C,n), profiled recursive face action, whole semicubical_nerve_func(C) | Further geometric comparison and later richer index operations |
| Gray cube comparison | Uniform object decoder from StrictFunctor(GrayCubePos_R(n),C) to Obj(CubicalLevel_cat(C,n+1)) | Whole decoder, inverse, whole equivalence and face compatibility |

## 1. Simplexes: A Flagged Category Is Not Yet The Total Level

The precise native recursion is

```text
S₀(C) = C
S₁(C;x₀) = PathOut_C(x₀)
S₂(C;x₀,e₀₁) = PathOut_{S₁(C;x₀)}(e₀₁)
S₃(C;x₀,e₀₁,t₀₁₂) = PathOut_{S₂(C;x₀,e₀₁)}(t₀₁₂).
```

Thus an object of S₂ is a triangle with the initial edge already fixed.
Its Hom category varies the remaining triangle data over that fixed flag;
it is not the Hom category of arbitrary moving triangles. A category of
all n-simplexes must also describe arrows that move the earlier vertices,
edges and faces, retaining the corresponding directed higher action.

Current owners:

- [dependent_simplex_native_dimensions](../emdash2/emdash3_2_dependent_simplex_native_dimensions.lp) defines S₀ through S₃ and the whole maps induced by F:C→D; dimension4 adds the next flagged stage.
- [dependent_simplex_codes](../emdash2/emdash3_2_dependent_simplex_codes.lp) records a flag and its already-native decoded category; it does not reimplement homd semantics.
- [dependent_simplex_faces](../emdash2/emdash3_2_dependent_simplex_faces.lp) interprets nonempty FaceCode values as whole functors between the appropriate decoded categories.
- [dependent_simplex_ordinal_recursive](../emdash2/emdash3_2_dependent_simplex_ordinal_recursive.lp) constructs the canonical source uniformly in n, maps it through a supplied ordinal diagram, and observes its faces.

DependentSimplexObservation(C,n), at the
[ordinal adequacy owner](../emdash2/emdash3_2_dependent_simplex_ordinal_adequacy.lp),
is the groupoidal package Σ(code), Obj(decode(code)). It retains objects and
their intrinsic category indices. It does not furnish the directed maps
between all flags. Taking its Path_cat would only provide groupoidal paths,
not those missing noninvertible maps.

A naive covariant Sigma over the first vertex is also insufficient: even
x↦Hom_C(x,y) is contravariant in x. The assembly must use the existing native
mixed-variance Hom/total machinery with the selected transformation profile.
This is the same kind of issue already addressed by the derived lax-arrow
total at dimension one. It is not a reason to replace hom_int/homd_int with
external records of squares.

### Geometric Levels And Indexing

[CoherentNerveLevel_cat](../emdash2/emdash3_2_coherent_nerve_levels.lp) already
names Functor_cat(DirectedSimplex_cat(n),C). The source shapes are the
join-built Δ[n], with n+1 vertices. The index
[SemiDeltaPlus_cat](../emdash2/emdash3_2_semisimplicial_index.lp) instead uses
vertex counts and monotone injections. Consequently

```text
a p-face of an n-simplex: FaceCode(p+1,n+1)
nonempty level at index n+1: dimension n.
```

The augmented shape at index zero is already defined as the empty path
category. A native augmented level would need its corresponding empty-simplex
interpretation; alternatively, first work on the nonempty part. It must not
silently identify dimension zero with the empty ordinal.

[face_realize_func](../emdash2/emdash3_2_face_realization.lp) already realizes
arbitrary nonempty face codes. The missing part is whole coherent assembly:
its all-keep form stops at join_map(id,id), and generic composite realization
needs the join identity/composition comparisons. The
[join mapping owner](../emdash2/emdash3_2_join_mapping_recursion.lp) has object
observation/extension and whole branch restrictions; a full category of its
mapping data and reconstruction remain separate. Later join-cross
compatibility work supplies more than the old beta-only checkpoint, but not
the whole desired equivalence. Do not repeat old statements that generic
face realization or the variable-dimensional ordinal source are absent.

### The Comparison Must Specify Its Mapping Profile

A native triangle contains α:p₁₂∘p₀₁⇒p₀₂. An ordinary strict functor from
the ordinary ordinal [2] into a strict 2-category forces the direct edge to
be the composite and does not encode an arbitrary such 2-cell. Therefore an
unqualified identification with strictly commuting ordinal diagrams would
be wrong for the intended higher native triangles.

A lax/coherent mapping interpretation, with the correct higher coherence and
orientation, is the relevant candidate. The familiar bicategorical example
is the Duskin nerve: strictly unital lax maps [n]→C retain these triangle
cells; degeneracies use the unit structure. This is a profile check, not a
proposal to replace the native calculus with manually supplied squares.
[Kerodon, Construction 2.3.1.1 and Remark 2.3.1.11](https://kerodon.net/tag/009T).

In the strict ω-categorical presentation, Street's nerve instead uses the
orientals Oₙ, with generating cells for simplex faces, as a cosimplicial
family of shapes. This reinforces the need to identify the actual shape and
mapping profile; the recursion “join with 1” alone is not a comparison
theorem with that construction. [Ara–Lafont–Métayer, introduction](https://www.normalesup.org/~ara/files/orientals.pdf).

Main's Functor_cat is the project's richer internal mapping calculus, not a
license to interpret every use as the classical strict mapping category.
The currently documented higher profile qualifications remain relevant.
At the ordinary target specialization the distinction contracts appropriately;
that does not automatically prove the higher statement.

A future comparison should therefore have the following selected form:
actual whole functors between independently defined native and geometric
levels, retained inverse/coherence data, and compatibility with the face
operators as a whole transformation between nerves. Choosing the existing
DefIso/OmegaEquivAlong interface depends on the proved comparison strength.
Pointwise equivalence of object packages is not sufficient. Defining the
native category to be Functor_cat(Δ[n],C) would make this particular
comparison circular and abandon the intended intrinsic presentation.

## 2. Cubes: Whole Native Nerve, Object-Level Gray Decoder

The native [CubicalLevel_cat](../emdash2/emdash3_2_cubical_levels.lp) is already
an unflagged category at every n:

```text
Cube_C(0)=C
Cube_C(n+1)=LaxArrow(Cube_C(n)).
```

Unlike Sₙ with chosen flags, LaxArrow already packages both endpoints. Its
arrows retain the two side arrows and directed square cell. The present
opposite/Sigma expression is the existing syntactic implementation; a fully
qualified higher interpretation still depends on the recorded Op/profile
work. This review does not change those primitives or their variance.

[semicubical_nerve_func](../emdash2/emdash3_2_semicubical_nerve.lp) is a
whole declared functor SemiCubePlus_catᵒᵖ→Cat_cat with an object rewrite to
CubicalLevel_cat. Its arrow observation is a declared path to the recursive
[cube_face_action_func](../emdash2/emdash3_2_semicubical_face_action.lp).
This is an explicit assembly interface; the entire nerve is not a derived
body from the face recursion alone. The standalone action retains the pseudo
capability needed to lift a square through another LaxArrow step.

Consequently, further functoriality in the target C must respect that profile.
A family of fixed-C nerves is not automatically one whole functor on every
ambient lax map C→D. Existing IsPseudoFunctor or stronger selected evidence
must be retained where the cubical lift consumes it.

The geometric source has a different current boundary:

```text
GrayCubePos_R(0)=I
GrayCubePos_R(n+1)=I⊗_R GrayCubePos_R(n)
Obj(GrayHom_lax(GrayCubePos_R(n),C))
  = StrictFunctor(GrayCubePos_R(n),C).
```

[gray_cube_observation](../emdash2/emdash3_2_gray_cube_decoder.lp) produces a native
(n+1)-cube from such a strict diagram by internal Nat recursion. Its selected
higher operations and dimensions one through three are exercised, but it is
not yet a whole functor on the full Gray mapping category with an inverse.
The dimension-two comparison also fixes a coordinate swap needed to match
the selected interchanger direction; an equivalence of nerves must retain
that convention, including its face correspondence.

A complete comparison on the current face-only index needs:

1. A whole degree-one mapping comparison with the correct lax/oplax profile.
2. A whole recursive decoder and encoder at the chosen fixed bracketing,
   retaining transformations, modifications and inverse data.
3. A zero-dimensional geometric level and coherent selected Gray coface maps.
4. Whole compatibility of the level comparisons with those cofaces, giving a
   comparison of functors on the same index.

This does not require proving all possible tensor associators or changing
bracketings first. It does require more than the current opaque tensor on
objects and the object decoder. The existing ordinary walking-arrow
reconstruction is useful evidence but is guarded by OneCat(C); repeatedly
applying LaxArrow to a higher C does not justify dropping that guard.

The source category of a geometric cubical nerve must be stated. The current
{L,R,*} codes describe only coordinate faces. They are not the full category
of all strict maps between Gray cubes. For example, Campion's density theorem
uses that full subcategory, so it does not directly prove adequacy/density of
this face-only nerve. Restrict a geometric nerve to the same chosen face index
before comparing it with the native one. [Campion, abstract](https://arxiv.org/abs/2209.09376).

### Two Specific Path/Whole-Owner Review Sites

The existing Gray decoder uses cubical_level_shift_path to identify
Cube_{LaxArrow(C)}(n+1) with Cube_C(n+2), then path_to_hom to obtain a functor.
This is a concrete operational category transport. Its finite observations
check, but a future whole decoder should review whether a shared iteration
owner or actual recursively constructed comparison with inverse gives more
useful higher computation. No performance failure is established here.

The native nerve's declared action path also reflects the old conflict with
global strict cuts. Profile integration is the appropriate time to reassess
its whole assembly and computational observation. Do not replace it with
caller-provided face naturality proofs, or assume that a pointwise path
automatically supplies a whole index comparison.

## 3. Arr Is An Existing Defined Operation

Let I be WalkingArrow_cat and D_C=Functor_cat(I,C). For F,G:ℬ→C,

```text
Arr_{ℬ,C;F,G}: Transf(F,G) → Functor(ℬ,D_C).
```

Here the arrow denotes an operation on supplied terms with implicit endpoint
functors. The literal [definition](../emdash2/emdash3_2_arrow_diagram_families.lp) is

```text
symbol transf_arrow_diagram_func
  [K C : Cat] [F G : τ (Functor K C)] (eta : τ (@Transf K C F G))
  : τ (Functor K (Functor_cat WalkingArrow_cat C))
≔ @sym_func WalkingArrow_cat K C
    (@walking_arrow_func (Functor_cat K C) F G eta);
```

First regard eta as an arrow F→G in Functor_cat(K,C). The existing walking-arrow
introduction produces I→Functor_cat(K,C). The whole exchange operation then
produces K→Functor_cat(I,C). At b, the endpoints are F(b),G(b), and the walking
generator maps to eta_b. At a base arrow, its endpoint actions and mixed cell
come from F,G and eta themselves. The reviewer checks these observations and
retained higher action; no separate naturality-square record is supplied.

Arr is not a new primitive, nor does this signature itself assert a whole
mapping-category equivalence LaxArrow(Functor_cat(K,C))≃Functor_cat(K,D_C).
If a consumer needs whole action in eta and both endpoint functors as a
single source category, that has to be provided by the appropriate whole
owner and profile. The current homology consumer needs the whole returned
functor and already has it.

## 4. Universal Family Data And Its Component Are Different Types

Use ℬ for an arbitrary parameter category and χ for the whole input:

```text
U:ℬ→C,  D:ℬ→D_C,  χ:J∘U⇒D
η:id_C⇒K∘J
K[χ]:K∘J∘U⇒K∘D
β_χ=K[χ]∘(η whiskered by U):U⇒K∘D
H_χ=Q∘Arr(β_χ):ℬ→C.
```

At b, χ_b is an arrow of D_C, hence itself a transformation between two
walking-arrow diagrams. There are two levels of components: χ_b selects a
whole diagram map; its component at the walking-arrow source is the incoming
differential. Its internal diagram naturality gives the zero composite in
the ordinary additive setting. Naturality over ℬ describes variation of this
whole input. The caller does not supply a second family of square proofs.

Now put Z_C=(J↓id_D_C), using the existing native represented-comma total.
Write a point as z=(A,d,ξ), where ξ:J(A)⇒d. There are whole projections and
one universal transformation:

```text
U_Z:Z_C→C,  D_Z:Z_C→D_C,  χ_Z:J∘U_Z⇒D_Z
U_Z(z)=A,  D_Z(z)=d,  (χ_Z)_z=ξ.
```

These are zero_arrow_cone_first_func, zero_arrow_cone_diagram_func, and
[zero_arrow_cone_universal_transf](../emdash2/emdash3_2_one_cat_zero_cones.lp).
The latter's ordinary-target assembly is declared once, and its displayed
component law rewrites to the actual stored ξ. Thus the global functor is
literally the same family construction specialized to this data:

```text
H_C := H_{χ_Z}:Z_C→C
β_Z(z)=K[ξ]∘η_A:A→K(d).
```

The [global H definition](../emdash2/emdash3_2_zero_arrow_cone_adjunction_homology.lp)
performs exactly that substitution. Nothing asks for a separately supplied
whole χ_Z when the object z only carries ξ. For a general family, the newer
Γ/H comparison relates H_χ to H_C∘Γ through actual maps with inverse data;
its qualification is in the completed universality audit, not an asserted
literal equality of arbitrary presentations.

Use another base 𝒲 for a window family. Its right and degree-shifted left
column functors V_R,V_L⁻:𝒲→Z_C yield

```text
δ:H_C∘V_R⇒H_C∘V_L⁻.
```

The superscript minus denotes the degree shift, not inversion. This removes
both the reuse of B (also a middle complex) and the reuse of H for a generic
family and the global native functor. 𝒲 can later specialize to a chosen
parameter category without silently identifying it with ℬ or Z_C.

## 5. Proposed Completion Order And Acceptance

The user has identified real unfinished nerve work. Completing it should be
an explicit sequence, rather than silently reopening every historical
simplicial/cubical research topic.

| Stage | Required outcome | Qualification |
| --- | --- | --- |
| NN-0: terminology/profile specification | Fixed-flag versus whole levels; same index conventions; shape and transformation profiles; orientation at degrees 1–3 | This source review identifies the choices; general higher profile semantics remains tied to the existing integration/Op plans |
| NN-1: reusable mapping universality | Whole walking-arrow and join mapping comparisons with coherent mixed-variance action and retained inverses | Reuse ordinary reconstruction where its guards apply; audit higher claims under the selected profiles |
| NN-2S: native simplex levels | Independently constructed category of all flags at each n, whole faces and coherent assembly | Do not define it as the geometric mapping category; preserve noninvertible triangle/top cells and next Hom action |
| NN-2C: whole Gray decoder | Whole fixed-bracketing geometric/native maps and inverse, including dimension zero | Respect strict-object/lax-arrow profiles, pseudo evidence and the coordinate convention |
| NN-3: comparisons of seminerve functors | Level comparisons compatible with whole index action, selected inverse and coherence | Native face then compare agrees with compare then geometric restriction; no caller square list |
| NN-4: full index extensions | Degeneracies, and selected cubical connections/permutations only if part of the requested index | Extend the index and retain unit/profile behavior; do not advertise a full nerve from faces alone |

The completed profile branch at 114dc19f still documents no inverse Gray cube
decoder or mapping-category equivalence; it does not secretly finish NN-2C.
It supplies relevant prerequisite work. Its integration and the separate
Op/Homd repair should remain explicit rather than being smuggled into a
nerve patch. Formal development before those integrations can still review
ordinary consumers or isolate the proposed interfaces, but cannot claim the
unrestricted higher theorem using the current qualified encodings.

General Kan filling, Segal/Rezk characterizations, alternate bracketings and
a full Gray monoidal theory are distinct theorem families. They are not all
necessary to complete the fixed-index comparisons above, and do not hold for
arbitrary directed input merely because its native nerve exists. In
particular, “finish deferred work” should not mean postulating all of them.

## Validation And Editing Boundary

Both forms of EMAIL.md now give the Arr type/definition, χ versus ξ,
U_Z/D_Z and the universal component law, H_χ versus H_C, and the separate
window base. Their nerve passages separate object algorithms, whole category
assembly, mapping profiles and index action. No library symbol or rule was
changed; generated book/PDF artifacts were not hand-edited. The same notation
clarifications can be incorporated at the next owning book update.

Fresh serial source checks, all at 2GiB/90s with o=20, warnings and subject
reduction enabled:

| Reviewer | Assertions | Log |
| --- | ---: | --- |
| arrow_diagram_families | 24 | arrow_diagram_families-20260923-121502.log |
| zero_arrow_cone_adjunction_homology | 5 | zero_arrow_cone_adjunction_homology-20260923-121213.log |
| dependent_simplex_ordinal_recursive | 7 | dependent_simplex_ordinal_recursive-20260923-121546.log |
| gray_cube_decoder | 15 | gray_cube_decoder-20260923-121740.log |

All four pass. Logs are under emdash2/logs/probes. They check the existing
operations, not the proposed equivalences. This is 51 focused assertions,
not a new whole-repository CI or a new higher-semantic consistency claim.
