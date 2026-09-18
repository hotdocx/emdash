# Categorical Universality: Current Inventory And Follow-Up Review

Date: 2026-09-17
Status: complete under the accepted scope — ordinary interfaces and consumers qualified; higher-terminality/product reviews, final audit and local book 0.9.2-dev verified
Baseline: `79237a008eff872832b20105b088f432fc24d8a1`
Plan-ID: TS-EMDASH-CATEGORICAL-UNIVERSALITY-ASSEMBLY
Implementation worktree: `/home/user1/emdash1-categorical-core-v1`
Implementation branch: `goal/categorical-core-consolidation-v3.2`

The new goal continues in the existing isolated worktree/branch. The completed
consolidation and published main checkpoint remain immutable comparison
anchors; no additional branch/worktree mutation is needed. Local green
checkpoints follow the session's existing authorization and Git workflow.
Main integration, push and publication are not part of this new launch.

Execution evidence belongs in the
[universality assembly ledger](TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_ASSEMBLY_LEDGER.md).
The [final audit](TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_FINAL_AUDIT.md)
maps every tranche to current source and validation, including the retained
qualifications and locally generated book artifacts. Main integration and
publication remain separate future actions.
User acceptance follows archived response 0120 in Infinity Codex session
`2026-09-12_01a096616c4a`; the accepted content and subsequent user clarification
are incorporated here, so the archive is only recovery evidence.

This review answers the post-consolidation questions about Γ, higher
terminality, and the several presentations of universal constructions.
The [completed consolidation audit](TYPESCRIPT_EMDASH_CATEGORICAL_CORE_CONSOLIDATION_FINAL_AUDIT.md)
remains valid. This document does not reactivate its completed goal or the
separately deferred Op/profile and six-term experiments.

The inventory is organized by semantic interface families, with exact owner
links and principal declarations. It covers the reusable universality layers
and their homological applications, rather than listing every projection or
every domain-specific ring/localization presentation as a separate theory.

## Findings And Recommendation

There is a shared computational core: whole internal functors, transformations,
represented Hom/profunctor comparisons, existing inverse data and adjunction
cuts. The library also has several presentation levels around that core.
They differ in whole versus single-input scope, equality versus computational
inverse laws, and supplied versus derived structure. They should not all be
identified or all retained as equally primary interfaces.

Whole universal data now assemble at their existing owners: the ordinary
Hom-comparison extension constructs η/ε and introduces Adjunction with scoped
input agreement and retained native cuts. Several ordinary instances still
explicitly declare their assembly. Replacing one of those instances requires
its whole comparison input to be built independently; repackaging its own
existing adjunction comparison does not reduce that structural assumption.

Γ is a separate meaningful application: classify coherent family inputs as
one native comma functor, then obtain a whole H comparison. It should keep its
own bounded consumer and action tests. Higher terminality is not an established
prerequisite for Γ, and a terminal-arrow normalization change would not resolve
Γ's recorded Σ/base-change target-action gap by itself.

## What “!ₜ Remains Separate From idₜ” Actually Means

The statement concerns conversion in the current implementation. It does not
assert two mathematically different terminal endomorphisms.

[TerminalObject](../emdash2/emdash3_2_terminal_objects.lp) currently supplies:

- one whole !:id_C⇒const_t, with selected components !ₐ:A→t;
- the runtime terminal cut !ᵦ∘h ↪ !ₐ;
- IsContr(Hom C A t), where Hom C A t is Obj(Hom_cat(C,A,t));
- derived paths f=!ₐ and !ₜ=idₜ.

The [reviewer](../emdash2/examples/terminal_objects.lp) explicitly checks the
path and separately asserts that !ₜ and idₜ do not currently convert. Thus
“intentionally separate” meant a documented choice to preserve those normal
forms during consolidation. It is not an immutable mathematical requirement.

The user's clarification is specifically about these schematic candidates:

```text
rule $f ↪ !ₐ
unif_rule $f ≡ !ₐ ↪ [tt ≡ tt]
```

The rewrite has no defined-symbol head. In the other orientation, !ₐ↪$f,
$f is not determined by the left-hand match. This is different from ordinary
β cuts such as π₁∘⟨f,g⟩↪f: returning a variable already matched on the left
is allowed. The official [Lambdapi rule documentation](https://lambdapi.readthedocs.io/en/latest/commands.html#rule)
includes precisely that kind of variable-valued RHS.

The unification candidate is a separate issue. A fresh isolated probe of
exactly `unif_rule $f ≡ @terminal_arrow_fapp0 $C $t $T $A ↪ [tt ≡ tt]`
**succeeds on the installed Lambdapi**. For arbitrary C,t,T,A,f:A→t, it accepts
`eq_refl f` at the expected equality f=!ₐ. The identical control with the
unifier removed fails at that assertion with “Cannot solve !ₐ≡f”. In the
successful probe, `assertnot` confirms that f and !ₐ still do not convert
at runtime. Thus the blanket claim that this unifier cannot work was too
strong.

Unification rules rewrite comparison problems, not runtime terms. The local
Lambdapi source wraps the two sides in the unification-equivalence head and
adds both orientations. This explains why a variable on one side is not the
same syntax problem as a variable-headed ordinary rewrite. The solver does
also dispatch some rigid cases before trying these rules, so this positive
case is not a general audit of every context or interaction.

The candidate merits consideration as proof-time terminal-uniqueness
convenience: its intended equation is already a theorem of TerminalObject.
But it does not itself construct whole functors, inverse data or higher
coherence, and it does not solve the runtime overlap below. Promotion would
need bounded inference/overlap and actual-consumer checks under the current
SOP. The probe is outside the library; no global unifier was installed.

There is a concrete reason not to add only !ₜ↪idₜ to the current rules. For
an arbitrary f:A→t, consider the same term !ₜ∘f:

```text
!ₜ∘f ↪ !ₐ                    existing terminal cut
!ₜ∘f ↪ idₜ∘f ↪ f             proposed !ₜ fold, then identity
```

The results are propositionally equal, but a free f has no rewrite to !ₐ in
the existing system. This introduces precisely the terminal-uniqueness
normalization problem again. Reversing the special rule idₜ↪!ₜ does not
remove that overlap with the identity law. This is a conversion/normalization
issue, not a mathematical counterexample or an Empty argument.

Likewise, folding the new adjunction unit directly to the old whole ! would
couple the adjunction triangle cuts to the old terminal cut. In p:C→1 ⊣ t:1→C,
the right triangle specializes to the identity at t; its off-diagonal form
also involves arbitrary maps A→t. The old ! action normalizes these to the
selected !ₐ. The consolidation therefore kept the actual native unit/counit
and compared their arrow families categorically instead of installing that
fold. The [ordinary adjunction reviewer](../emdash2/examples/one_cat_terminal_adjunctions.lp)
checks both the existing inverse cuts and retention of the old normal forms.

An ideal future implementation can reconsider the policy. Options include
keeping uniqueness as a derived categorical/equality observation while cuts
compute at explicit universal operations, or designing a broader typed
terminal-eta conversion mechanism. The latter needs an actual checker and
normal-form design; it is not one harmless extra local rewrite. Neither
option requires a ban on equations throughout the mathematics.

## Higher Terminality Is A Different, Related Question

The intended higher universal content is a whole coherent comparison between
the represented Hom family at t and the terminal family. Schematically:

```text
R_t(x) = Hom_cat(C,x,t)
R_t ≃ const₁, coherently in the native represented family
```

The corresponding adjunction presentation is p:C→1 ⊣ t:1→C, with the dual
presentation for initiality. These formulas specify the desired categorical
content; they are not new declarations in this review. The native hom_int,
hom_con and homd_int owners must continue to carry the varying action.

Contractibility of Obj(D) alone does not make a directed category D equivalent
to 1: a one-object category can have nontrivial noninvertible endomorphisms.
Univalence relates suitable paths and equivalences; it does not identify
arbitrary directed arrows with invertible ones.

However, it would also be wrong to describe the existing TerminalObject as
*only* its IsContr field. It already includes a whole ! and its action/cuts.
A proper review must establish what that complete package implies under the
intended naturality profile. With sufficiently strong naturality, whole unit
and identity-at-t data can supply substantially more than objectwise
contractibility. Under a lax profile the comparison cells and their
invertibility must be accounted for. The isolated one-object example does
not disprove the full TerminalObject interface.

Thus the higher review should ask which existing whole data suffice, which
assembly constructor is missing, and which computational laws should be
primary. It should not simply replace IsContr everywhere, drop OneCat guards,
or claim that a normal-form distinction caused the higher semantic question.
The existing Ω interface has equality-valued inverse laws between whole maps;
its intended higher interpretation must itself be specified at that level.

The completed [higher terminality review](TYPESCRIPT_EMDASH_HIGHER_TERMINALITY_REVIEW.md)
now supplies the detailed decision. It audits the full ! package, proves the
2-categorical strict/pseudo implication, and gives an explicit lax separation
example satisfying the visible point/core data. Six conditional native checks
observe supplied terminal/initial adjunctions and their whole inverse data
without OneCat(C); they do not construct those adjunctions from the old T.
Keep the qualified ordinary primary family API and existing selected cuts.
The general upgrade requires the specified whole naturality/invertibility
and family-comparison data at the deferred profile/duality qualification.
This completes the present review without promoting an unqualified higher
replacement or resuming that separate migration.

## Inventory: Shared Foundations And Comparison Strength

Legend: **definition** means an existing term/body supplies the operation;
**declaration** means the interface explicitly supplies structure. A definition
of a classifier does not construct an inhabitant for every category.

| Interface and principal symbols | Current owner and meaning | Relation to other versions |
| --- | --- | --- |
| `IsoEvidence`, `OmegaEquivAlong`, `OmegaEquiv`, `DefIso` | [Nucleus](../emdash2/emdash3_2.lp). Ordinary inverse evidence, fixed-forward Ω evidence, and computational isomorphism respectively. | DefIso has selected maps and judgmental inverse cuts; it forgets to IsoEvidence. Ω retains actual inverse maps and equality-valued laws. Ordinary inverse evidence is not automatically a new DefIso computation. |
| `Adjunction(F,G)`, `unit_adj_transf`, `counit_adj_transf` | [Nucleus](../emdash2/emdash3_2.lp), declared relation on the already selected F,G, whole unit/counit and triangle cuts. | This remains the shared adjunction owner. The ordinary Hom-comparison introduction below reuses it. A separate general unit/counit constructor is not implemented. |
| `one_cat_hom_comparison_unit`, `one_cat_hom_comparison_counit`, whole triangle laws | [Hom-comparison data](../emdash2/emdash3_2_one_cat_hom_comparison_data.lp): definitions extracting the whole data from the original comparison and inverse. | Component and action formulas are ordinary law observations. No operational functor is constructed by path transport and no caller supplies naturality squares. |
| `one_cat_adjunction_from_hom_comparison`, input/unit/counit agreement | [Ordinary introduction](../emdash2/emdash3_2_one_cat_adjunction_introduction.lp): one structural constructor with seven scoped proof-time views and derived agreement laws. | Preserves the native mate and triangle runtime heads. The generic input law supports a supplied comparison already projected from another adjunction; direct reflexivity at that special input hits injectivity decomposition. |
| `Adjunction_hom_prof_comparison`; `adjunction_transpose_func`, `adjunction_untranspose_func` | The nucleus declares the whole represented-Hom comparison; [mates](../emdash2/emdash3_2_adjunction_mates.lp) define its evaluated forward/inverse functors and formula observations. | The comparison is ProfComparison, hence DefIso-based. The unit/counit formula views are related to these existing selected maps; no independent inverse is chosen. |
| `ProfComparison` | [Nucleus](../emdash2/emdash3_2.lp): definition as DefIso in the profunctor category. | It is a named view of the same comparison calculus. `prof_comparison_evidence` forgets its computational structure to ordinary isomorphism evidence. |
| `IsRepresentedBy_iso`, `Representation_iso`, `WeightedCone_prof`, `IsWeightedLimit_cov_iso`, `IsWeightedLimit_cov_comp` | [Nucleus](../emdash2/emdash3_2.lp): representability and weighted limits as whole profunctor comparisons. The chosen representing functor is supplied/retained. | The iso form uses IsoEvidence; the comp form uses ProfComparison. They differ in computational strength, not in the intended ordinary universal property. Whole push/pull operations reindex the one comparison. |
| `WeightedColimit_con`, preservation of limits/colimits by adjoints | [Nucleus](../emdash2/emdash3_2.lp). Colimits are defined through the existing opposite weighted-limit interface; preservation constructions are derived from the mate/comparison calculus. | Direct colimit projection vocabulary is limited. This inherited duality-based route keeps its existing higher-variance qualification; it is not a completed new Op design. |
| `one_cat_postcomp_adjunction`, `one_cat_functor_category` | [Whole family adjunctions](../emdash2/emdash3_2_one_cat_adjunction_families.lp): explicit ordinary structural declarations; unit/counit are the original cells whiskered by a family. | F⊣G gives (F∘−)⊣(G∘−). Whole family mates are definitions from that declared lift. No caller supplies pointwise naturality squares. |
| `one_cat_modification`, `one_cat_transf_identity_path` | [Ordinary modifications](../emdash2/emdash3_2_one_cat_modifications.lp): one structural primitive assembles a native modification between two existing whole transformations into OneCat(C), with computing component projections. The staged unit-law path is a definition. | The component cells are proposition-valued, so their remaining coherence is unique. The introduction extends the old beta interface; it does not assemble arbitrary pointwise families into functors or transformations. This Γ/H support owner is promoted in UA-4j. The original whole-comparison assertions are retained across the current private-input and imported-H replays. |
| `Product_cat`, `Terminal_cat`, `Sigma_cat`, `Pi_cat`, `Pullback_catd` | [Nucleus](../emdash2/emdash3_2.lp): category/type formers, native dependent sum/product and family substitution. | These are not chosen internal products/terminal objects/pullbacks in an arbitrary C. In particular Pullback_catd(E,F) is substitution E∘F, not a categorical pullback supplied by PullbackStructure. |

## Inventory: Products, Terminality And Coproducts

| Interface and principal symbols | Current formulation | Implemented relationship and remaining boundary |
| --- | --- | --- |
| `TerminalObject(C,t)`; whole ! and `terminal_hom_contr` | [Terminal objects](../emdash2/emdash3_2_terminal_objects.lp): declared selected capability, whole canonical arrow and cuts, object/core Hom contraction. | General C occurs in the signature, but a general higher terminality equivalence is not established merely by that fact. f=!ₐ and !ₜ=idₜ are derived paths. |
| Initial object usage | The existing selected capability is `TerminalObject(Op_cat C,t)`; [additive categories](../emdash2/emdash3_2_additive_categories.lp) also derive initial-Hom contraction from preadditivity and a terminal object. | There is no second generic `InitialObject` classifier here. Derived point contraction is not automatically an inhabitant of the whole selected opposite-terminal capability; several native consumers retain it explicitly. |
| `CatContraction(D)`, `CatdContraction(E)` | [Categorical contractions](../emdash2/emdash3_2_categorical_contractions.lp): definitions using Ω along the canonical whole terminal map. | They retain whole inverse functors. Family evaluation derives a fibre contraction; object/core IsContr is downstream. Terminality concerns contraction of the represented Hom family, not contraction of C itself. |
| `one_cat_terminal_adjunction`, `one_cat_initial_adjunction` | [Ordinary terminal adjunctions](../emdash2/emdash3_2_one_cat_terminal_adjunctions.lp): two declared assemblies from the original selected capability and OneCat(C). | Supply p⊣t and t⊣p; evaluated Hom DefIso/Ω and uniqueness observations are derived. The selected mate into 1 is retained rather than cast to another functor. |
| `terminal_category_groupoidal`, `terminal_category_discrete`, `terminal_category_one_cat` | [Literal terminal category profile](../emdash2/emdash3_2_terminal_category_profile.lp): closed definitions with an explicit constant inverse to the core inclusion. | One new ground proof-time eta instance identifies the canonical constant endofunctor of 1 with id₁. Runtime functor heads remain distinct; no arbitrary endofunctor or general terminal-object uniqueness unifier is installed. |
| `one_cat_terminal_adjunction_family_*`, `one_cat_initial_adjunction_family_*` | [Direct family universality](../emdash2/emdash3_2_one_cat_terminal_adjunction_families.lp): definitions from the supplied p⊣t or t⊣p and OneCat(C), using the closed terminal profile. | Whole Hom DefIso, invertible modification and diagram IsoEvidence are derived. Default presentations use the original unit/counit; an optional whole arrow presentation preserves an existing selected embedding. No old TerminalObject or caller square proof is required by this primary API. |
| `one_cat_terminal_arrow_family_evidence`, `one_cat_initial_arrow_family_evidence` | [Whole family universality](../emdash2/emdash3_2_one_cat_terminal_family_universality.lp): derived ordinary IsoEvidence adapters from the existing selected-terminal adjunction instances. | Arr(h)≅J∘F for h:F⇒const_t; dually Arr(h)≅I∘F. Both actual maps retain computing point endpoints and proved whole endpoint/inverse laws. The two former primitive DefIso normalizers and their sixteen rules are retired. Their raw inverse cuts are not asserted for the derived evidence. |
| `BinaryProducts(C,P)` | [Triangular products](../emdash2/emdash3_2_triangular_binary_products.lp): whole P:C×C→C, whole projections/pairing, Došen-style cuts and an action comparison. | Both pairing/unpairing functors and point inverse paths exist. The original file alone does not assemble the corresponding whole inverse certificate. |
| `IsBinaryProduct_comp`, `BinaryProductPresentation(C,x,y)` | [Finite limits](../emdash2/emdash3_2_finite_limits.lp): definitions specializing computational weighted limits to the discrete two-object diagram. | This selects one product with a whole universal cone comparison. Unrelated choices at each pair do not automatically supply one coherent P. |
| `BinaryProductsWeightedComp` | [Product/weighted bridge](../emdash2/emdash3_2_triangular_binary_products_finite_limits.lp): additional supplied weighted witnesses and projection agreements. | Defines weighted presentations at the original P(x,y). It is explicitly not a derivation of those witnesses from BinaryProducts alone. The newer ordinary adjunction offers a concrete direction for investigating this bridge, not an already implemented replacement. |
| `one_cat_binary_product_adjunction`, `one_cat_product_category` | [Ordinary product adjunction](../emdash2/emdash3_2_one_cat_product_adjunction.lp): declared Δ⊣P and ordinary product-category closure. | Retains the original P, projections and diagonal pairing. [Whole family pairing/unpairing](../emdash2/emdash3_2_one_cat_product_families.lp) is derived through the lifted adjunction. |
| `CartesianCategory(C,P,t)` | [Cartesian categories](../emdash2/emdash3_2_cartesian_categories.lp): definition pairing BinaryProducts and TerminalObject. | Thin package, no further choice or computation. |
| `AdditiveCategory(C,P,t)`; `additive_copair_fapp0` | [Additive categories](../emdash2/emdash3_2_additive_categories.lp): preadditive plus Cartesian data; injections/copairing and their ordinary laws are derived. | The same P is a biproduct at the ordinary mathematical level. No independent coproduct choice is introduced. |
| `one_cat_biproduct_adjunction`; whole copairing | [Biproduct adjunction](../emdash2/emdash3_2_one_cat_biproduct_adjunction.lp): declared P⊣Δ over the same additive P, with OneCat and the selected initial capability. | [Whole copairing](../emdash2/emdash3_2_one_cat_copair_families.lp) is derived from the existing family mates. A standalone coherent arbitrary-C binary-coproduct package is not implemented by this additive result; weighted colimits provide the general existing route. |

## Inventory: Pullbacks, Dependent Products And Homology

| Interface and principal symbols | Current formulation | Implemented relationship and remaining boundary |
| --- | --- | --- |
| `PullbackStructure(C)`, `SliceBaseChange_catd`, `slice_base_change_adjunction` | [Pullbacks](../emdash2/emdash3_2_pullbacks.lp): a whole chosen contravariant slice family with Σ_f⊣f*. The covariant Σ_f comes from the native comma/Hom family. | Internal slice Homs are the cone classifiers. Lifting and recovery use the existing adjunction, not a new record of manually supplied squares. Higher profiles/variance remain qualified as in the existing foundation. |
| `DependentProductStructure(C,PB)`, `SliceDependentProduct_catd`, `slice_dependent_product_adjunction` | [Slice dependent products](../emdash2/emdash3_2_slice_dependent_products.lp): whole Π_f and f*⊣Π_f, over the same selected pullbacks. | Gives Σ_f⊣f*⊣Π_f. Beck–Chevalley, Frobenius, slice-exponential assembly and a general LCCC package are not supplied merely by the present declaration. It is distinct from the native Pi_cat former. |
| `ComputationalWeakKernel`, `ComputationalKernel`, `ComputationalCokernel`, `HasComputationalKernels/Cokernels` | [Weak kernels](../emdash2/emdash3_2_weak_kernels.lp) and [ordinary kernels/cokernels](../emdash2/emdash3_2_kernels_cokernels.lp): internal Hom-fibre factor data; genuine records require IsContr factor spaces. | These remain ordinary reference/provider interfaces. Propositionally truncated Kernel/Cokernel express existence. They are not the primary native whole universality API. |
| `KernelPresentation`, `CokernelPresentation` | [Kernel presentation](../emdash2/emdash3_2_kernel_adjunction_presentations.lp) and [cokernel presentation](../emdash2/emdash3_2_cokernel_adjunction_presentations.lp): supplied coherence over old selected operations W/V. | Their whole functors and adjunctions yield native structures. W/V alone do not automatically yield these presentations. These are retained reference adapters, not native model prerequisites. |
| `KernelAdjunctionStructure`, `CokernelAdjunctionStructure` | [Primary whole K/Q](../emdash2/emdash3_2_kernel_cokernel_adjunctions.lp): definitions packaging a whole functor with J⊣K or Q⊣I, where J(A)=(A→0), I(A)=(0→A). | No old W/V dictionary is input. Whole inclusion/projection, mates and family lifts/descents are derived. Existence is still supplied; preadditivity alone does not construct K/Q. |
| `kernel_adjunction_record`, `cokernel_adjunction_record` | [Native ordinary record views](../emdash2/emdash3_2_one_cat_adjunction_records.lp): definitions under OneCat using the actual native objects, structural arrows and mate centres. | Derive the old-shaped ComputationalKernel/Cokernel records as downstream observations; this does not reintroduce their old selection algorithms. Separate `kernel_adjunction_records`/`cokernel_adjunction_records` files serve the older presentation route. |
| `one_cat_kernel_pullback_comparison_equiv` | [Kernel/pullback universality](../emdash2/emdash3_2_one_cat_kernel_pullback_universality.lp): constructs the inverse of the actual native slice-Hom comparison from whole kernel lifts. | Proves a specific kernel/precomposition pullback square universally, using the existing cone classifier. It does not manufacture an entire PullbackStructure(C) or identify every independently chosen pullback. |
| `ComputationalFiberProduct`, `ComputationalPushout` | [Additive fibre products](../emdash2/emdash3_2_computational_fiber_products.lp) and [pushouts](../emdash2/emdash3_2_computational_pushouts.lp): definitions using kernel of [f,−g] or cokernel of the dual biproduct difference. | Retained ordinary algebra/provider constructions. A generic whole pushout-family/adjunction interface and automatic assembly of all these objects into the chosen slice family are not asserted here. |
| Whole H, Coim⇒Im, `OneCatAdjunctionNormality`, `OneCatAbelianAdjunctionStructure` | [H families](../emdash2/emdash3_2_homology_adjunction_families.lp), [normality](../emdash2/emdash3_2_one_cat_adjunction_normality.lp), [Abelian package](../emdash2/emdash3_2_one_cat_abelian_adjunctions.lp). | H is derived through the same K/Q. Normality is Ω evidence along the actual whole Coim⇒Im map, retaining its inverse. Native δ/exactness and their finite ordinary/CAS observations use this primary route. |
| `one_cat_diagram_reconstruction_iso` | [Diagram reconstruction](../emdash2/emdash3_2_one_cat_diagram_reconstruction.lp): declared ordinary D∘E≅id on the walking-arrow diagram category. | Derived faithfulness and actual inverse diagram maps support the universal-operation consumers. This is a shape-comparison assembly, not a new kernel universality or an unrestricted equivalence with higher LaxArrow(C). |
| `one_cat_arrow_family_comparison_evidence`, `one_cat_diagram_family_reconstruction_evidence` | [Arrow-family isomorphisms](../emdash2/emdash3_2_one_cat_arrow_family_isomorphisms.lp) and [family reconstruction](../emdash2/emdash3_2_one_cat_diagram_family_reconstruction.lp): fully defined whole maps and inverse-law evidence. | [Generic reflection](../emdash2/emdash3_2_one_cat_diagram_family_reflection.lp) and the two original reconstruction maps have independent owners; their moved signatures/bodies are unchanged. IsoEvidence laws are not advertised as additional DefIso runtime cuts. |
| Γ and the whole H comparison | [Public Γ/projection owner](../emdash2/emdash3_2_represented_comma_families.lp), [ordinary triangle](../emdash2/emdash3_2_one_cat_zero_arrow_family_classification.lp), and [whole H comparison](../emdash2/emdash3_2_one_cat_homology_family_comparison.lp); [private controls](../emdash2/audits/categorical-family-introduction-boundary/README.md) remain an audit. | Γ classifies A,D,h:J∘A⇒D into RepresentedComma(J), retaining whole source IsoEvidence and ordinary target OmegaEquivAlong. Public inputs and the actual whole H import consumer check with original inverses and point observations. Stronger direct D[θ] runtime normalization remains unqualified and was unnecessary for this consumer. |

## The Actual Relation Map

### Product/Weighted Consumer Review

UA-5's current-source inventory finds BinaryProductsWeightedComp and its four
adapter operations only in their owning bridge module, its focused reviewer
and the integrated diagnostics. There are no callers in the active native
homology modules or the TypeScript workbench/package sources. Their tests
explicitly supply K; they do not derive its weighted comparison.

The meaningful native consumers instead use one_cat_product_family_pair_func
and its inverse, through the existing ordinary Δ⊣P and postcomposition lift.
This route is used by the biproduct family distribution and reindexing owners
and preserves the same selected P and projections.

Decision: keep the assumption-explicit weighted adapter unchanged in this
goal. A future derived adapter would need a whole comparison from the actual
WeightedCone_prof for the binary diagram to the product-category represented
Hom family, followed by the existing Δ⊣P comparison, with the two selected
projection agreements. Point pairing identities or repackaging the already
declared product adjunction do not supply that missing implemented bridge.
There is no current consumer requiring this extra assembly. This is the
plan's explicit no-change outcome, not a mathematical impossibility claim or
an added compatibility obligation on native homology.

In the qualified ordinary portions, the main equations describe one reuse
pattern:

```text
F⊣G  →  whole Hom mate comparison  →  transpose / untranspose
     →  (F∘−)⊣(G∘−)              →  whole family operations

Δ⊣P                 product pairing
P⊣Δ                 additive coproduct pairing, same P
p⊣t / t⊣p           terminal / initial universality
Σ_f⊣f*⊣Π_f          slice sums / pullbacks / dependent products
J⊣K and Q⊣I         kernels / cokernels → H, Coim⇒Im, δ, exactness
```

Some arrows in this diagram are implemented **structural declarations**, not
unconditional derived constructors. The tables identify them. In the reverse
direction, a collection of pointwise products or kernels is not by itself a
whole internal functor and its higher action. Ordinary mathematics can often
assemble such choices using uniqueness; the native interface must still
represent and compute that assembly.

Of the twelve structural symbols added during the two preceding goals, ten
remain declared after UA-3e:

| Role | Symbols |
| --- | --- |
| Ordinary/discrete profile closure | `discrete_functor_category`, `one_cat_functor_category`, `one_cat_product_category`, `one_cat_slice_category` |
| Whole adjunction lift | `one_cat_postcomp_adjunction` |
| Product / biproduct assembly | `one_cat_binary_product_adjunction`, `one_cat_biproduct_adjunction` |
| Diagram reconstruction | `one_cat_diagram_reconstruction_iso` |
| Terminal/initial adjunction assembly | `one_cat_terminal_adjunction`, `one_cat_initial_adjunction` |

This is the recent added structural boundary, not a count of every primitive
in the whole kernel. The older Adjunction, DefIso, TerminalObject,
BinaryProducts and slice-structure owners are additional existing interfaces.
None of these ten asserts homological output exactness. The two former
terminal/initial family-comparison primitives are replaced by definitions
using the existing adjunctions and reconstruction. This reduces that specific
structural boundary; it does not derive the remaining ten declarations.

## Accepted Bounded Continuation

1. **Review generic assembly first.** Specify an introduction into the existing
   Adjunction interface from a whole represented-Hom comparison, with retained
   forward/inverse maps, identity-derived unit/counit and observable cuts.
   Separate the DefIso computational version from any weaker Ω version.
   Test the existing ordinary postcomposition lift as a real consumer. Do
   not invent a second adjunction calculus or require hand-written naturality
   squares. If present higher profiles prevent this assembly, record that
   exact boundary rather than silently assuming them.
2. **Choose primary terminality and its computation together.** Audit the
   complete current ! package. State the intended whole represented-Hom
   universality and identify which parts can be derived at existing owners.
   Decide whether old terminal cuts remain primary, become derived views,
   or need a separate normalization migration. Use an actual whole terminal
   family consumer to justify changes. General higher terminality must not be
   claimed merely because the ordinary adapter exists.
3. **Resume Γ as its own consumer-led task.** Keep the existing comma and
   hom_int/homd_int foundations; qualify the recorded target action and next
   Hom/triangle data, then an actual whole H comparison. No primary K/Q/H/δ
   should be rebuilt from records. Separately supplied finite CAS
   interpretations remain real input contracts. A terminality redesign is
   not an automatic prerequisite.
4. **Unify additional presentations only where useful.** The ordinary
   Δ⊣P-to-weighted-product bridge is a concrete candidate now that the whole
   mate exists. Likewise, kernel/pullback comparisons already demonstrate
   reuse. Require a real consumer and retain the original choices; do not
   impose a new compatibility campaign for every retired formulation.

The user accepted this continuation and requested a new persistent goal on
2026-09-17. Its objective delegates evolving specifics to this plan and the
linked ledger. Op/duality repair, integration of the action-profile branch,
six-term/old endpoint experiments and spectral/stabilization research remain
deferred. Γ is now authorized as the bounded separate application below.

The successful terminal unifier is a positive design fact from now on. Do not
rebuild an architecture around its supposed impossibility. Prefer two rigid
heads by default, but that preference does not veto a theorem-backed,
qualified variable-sided unifier. Conversely, the one successful typed use
does not by itself qualify all inference interactions or change runtime
normal forms. Retain the no-unifier control and runtime-negative observation.

## Execution Tranches And Completion Gates

The mathematical Γ consumer is a coherent family of the current native
homology inputs. For an ordinary additive C with the supplied whole K/Q,
write J(X)=(X→0), and take A:B→C, D:B→Diag(C), h:J∘A⇒D. The existing native
input category Z(C) has objects (X,d,u:J(X)→d), with projections p,q and
universal transformation τ:J∘p⇒q. The classifier should be one internal
functor Γ:B→Z(C), Γ(b)=(A(b),D(b),h_b), retaining all action already supplied
by A,D,h; callers provide no additional naturality squares.

Its mathematical projection laws are p∘Γ=A and q∘Γ=D, with τ along Γ
recovering h. These equations describe the classification property; the
formal interface may use canonical whole comparisons compatible with τ.
Do not demand a stronger global functor eta/normalization theorem unless an
actual consumer requires it. Point formulas alone still do not establish
the needed whole comparisons.

The family construction forms β=K(h)∘η_A and H_family=Q∘Arr(β). The same
construction at p,q,τ gives the current H_native:Z(C)→C. The desired output
is an actual whole natural isomorphism H_family≅H_native∘Γ with retained
inverse data. Both sides use the same current native K/Q. This classification
and reuse result is additional to the already whole H/maps/δ interface; it
does not eliminate the separately supplied finite CAS interpretation contracts.

| Tranche | Required result | State |
| --- | --- | --- |
| UA-0 | Integrate accepted review, persist the terminal-unifier evidence and controls, establish current source/validation baseline and start the new goal. | Qualified |
| UA-1 | Derive whole unit/counit and retained component/action observations from a supplied whole represented-Hom comparison. Preserve native Hom owners and the original F/G and inverse maps. Distinguish ordinary mathematical semantics from unrestricted higher interpretation. | Qualified ordinary public owner: 42 definitions, fifteen public operations, original comparison/inverse, whole η/ε, component/action observations and both whole triangle laws. The supporting clauses are at their core/arrow owners. Sixteen extraction checks, five curry controls, affected reviewers, integrated diagnostics and all 94 nonsplit assertions pass |
| UA-2 | Qualify an introduction at the existing Adjunction owner and use an actual whole-family/postcomposition consumer. Derive suitable existing structural instances where the data allow it; record any necessary new structural constructor honestly. | Qualified public ordinary introduction: one structural constructor, seven scoped proof-time views, derived whole η/ε comparisons, 33 public assertions, native Došen/mate cuts and whole-family consumption. Existing consumer imports, integrated diagnostics and all 94 nonsplit assertions pass. The postcomposition lift remains the existing structural instance; no additional Freyd-model entry point is selected |
| UA-3 | Review the complete terminal ! package, formulate primary whole terminal/initial universality and qualify a genuine family consumer. Reconsider the exact working uniqueness unifier with bounded inference/overlap checks; separate proof-time convenience from runtime terminal eta. | Qualified ordinary family migration and bounded uniqueness audit; full higher review completed with conditional native observations and explicit profile-dependent prerequisites. No generic uniqueness unifier or unrestricted higher replacement is installed. The later upgrade remains with the user-deferred profile/duality work |
| UA-4 | Resume the existing Γ candidate: qualify target and next Hom/triangle action, then the actual whole native H comparison with its existing observations downstream. Terminality redesign is not an assumed prerequisite. | The ordinary candidate checks H_family≅H_native∘Γ with original endpoint functors, selected maps/inverses and whole laws. The private-input and imported-H replays preserve both projections, triangle compatibility and the original point-input observation. No new primitive/rule was needed after UA-4h. The supporting rules now have positive owners and fresh joint qualification, including all 94 nonsplit assertions. Γ, its whole projections, triangle and H comparisons now have public owners. Qualified: public inverse/point observations, the existing Freyd-model specialization, integrated diagnostics and all 94 nonsplit assertions pass with the new comparison modules loaded. Direct higher target normalization is unqualified and was unnecessary for this consumer |
| UA-5 | Assess the ordinary product-adjunction→weighted-product bridge against a concrete consumer; implement if useful, or record a precise no-change conclusion. Preserve selected products and avoid new retired-formulation compatibility obligations. | Reviewed: no current consumer requires a new bridge. The supplied-weighted-witness adapter remains accurately labelled; native homology uses whole pairing from Δ⊣P. No extra comparison/compatibility requirement is introduced |
| UA-6 | Audit changed structural assumptions, rules, imports, actual native consumers and documentation/book impact; carry forward unchanged checks and update affected exposition. | Complete: source/trust/import audit, synchronized overviews and unsent email, book 0.9.2-dev with 187 evidence claims, 415-page validated PDF, visual inspection, byte-identical independent export and local artifact promotion |

UA-1 through UA-4 require implemented qualified outcomes or a concrete
mathematical/profile/owner prerequisite recorded with evidence and an explicit
scope decision; a failed exploratory assertion is not completion. Do not mark
the goal complete merely because a constructor types or a point formula works.
Current native K/Q/H/δ and nonsplit proof–CAS computations must remain qualified.
General higher terminality or unrestricted higher adjunction equivalence must
not be claimed from an ordinary-target test or by simply deleting guards.

Validation is localized. Begin with exact affected owners/consumers, then
owner-position warning/SR comparisons for changed rules, relevant negative
cases, and catalog/health synchronization under AGENTS. No long repo-wide
TypeScript checks are part of the routine loop. Keep the serial LP guard:
90s/2GiB by default, explicit measured profile exceptions only under existing
session authorization. Preserve whole computational/inverse data; do not hide
it behind opacity to make a check pass. Compiled-parent and GC controls remain
available for measured resource questions.

The authoring premise is computational-and-internal universality. Callers
must not reconstruct naturality/functoriality by carrying manual square
proofs. Ordinary equations and truncated observation evidence remain valid
views. hom_int/homd_int are foundations, not targets for replacement.

The execution queue is complete under the accepted scope. The qualified Γ/H tranche's
whole source comparison p∘Γ≅A, target comparison q∘Γ≃D and triangle
modification T∘τΓ≅h∘J(S) retain the original A,D,h and their action. The
actual boundary-diagram isomorphism and original Q then give
H_family≅H_native∘Γ, with its point view at the unchanged
zero_arrow_family_point_input. Every operational map and inverse is
categorical; paths remain laws or cells in discrete modification categories.
Direct D[θ] runtime normalization remains unqualified and was unnecessary
for this actual consumer.

UA-4j promotes the ordinary modification introduction and staged unit lemma.
UA-4k places the remaining structural rules at their original core,
varying-Sigma projection, zero-cone and adjunction-family-view owners. The
Γ/H replays import all of them without duplicate rules;
the separate first-arrow and higher-source computations also pass. These
selected whole projection views extend the former component interface;
they are not all derivations from its old β rules. The native
hom_int/homd_int, runtime heads and original inverse choices remain.
The postcomposition view is guarded by its actual composite argument:
integration exposed that its broader form intercepts the existing paired
product-family comparison. The guarded version passes both actual consumers.

UA-4l moves the internal graph derivation and whole projection comparisons
into emdash3_2_represented_comma_families.lp, retaining its helpers as protected
and exposing seven public classifier/projection/comparison operations.
emdash3_2_transfor_whiskering.lp owns four derived whole-whiskering operations.
The 24-assertion public reviewer and the actual 38-assertion triangle/H import
consumer pass without protected names or a graph source copy. The 64 private
controls remain an owner-position audit. No primitive or rule changes.

The ledger records owner-position/SR and five-part warning comparisons,
focused consumer checks and native/CAS qualification. UA-4m gives the retained triangle, actual boundary-diagram/H comparison and
downstream point view public definition owners. Their private proof stages
remain protected. Public imports retain whole inverse laws and components;
the Freyd reviewer uses the existing P/Q and literal original model H.
The original nonsplit artifact bodies are also replayed with the new comparison
modules loaded. This adds no model contract or closed-model construction. The inherited compiled-import
Pi reviewer boundary remains separately recorded, without a broad eta fix
or a claimed full-repository green aggregate. The subsequent UA-1/2/3/5
results and UA-6 closure are recorded below and in the final audit.

The [identity-image extraction](../emdash2/audits/adjunction-identity-image-extraction/README.md)
now reuses Γ's projection comparisons with a supplied whole internal Hom
action. It constructs both η and ε without a new introduction primitive and
proves the component formulas using existing identity laws. Two canonical
curry/Hom proof-time views and one scoped universal-arrow identity observation
now belong to their original core/arrow owners. Broader product runtime clauses were
rejected; ordinary component equations do not define a transported functor.
The public definition owner and sixteen-check reviewer replace the former
compressed candidate; Git retains that history. Original native naturality cells and selected inverse
laws now give nonidentity action equations and both whole triangle
modifications/equations through the existing ordinary modification interface.
No additional runtime rule is used for those laws. UA-1e factors the graph
at the existing comma owner, with original Γ signatures as specializations.
UA-1f promotes extraction and the three qualified owner clauses. All 94
nonsplit artifacts' assertions pass with the new module loaded. The separate UA-2h owner now supplies the qualified ordinary introduction.

The earlier constructor experiment was held because it had no identified
production caller with independently built whole comparison data and did not
remove an existing structural assumption. The user's subsequent Φ/Γ input
agreement proposal clarified the interface to qualify: introduction from
supplied whole data, with proof-time agreement that preserves canonical
computation heads. This is related to the prior
[adjunction-usability plan](ADJUNCTION_USABILITY_V3_2_PLAN.md), whose host APIs
assume a witness and register named-operation agreement. The new public owner
instead introduces the witness from the supplied whole ProfComparison.

Adjunction_hom_prof_comparison and adjunction_transpose_func/untranspose_func
already supply the comparison and both mate functors. Their actual stable
heads are the selected DefIso projections. The new ordinary constructor uses
those owners and seven scoped unif_rules; no parallel Φ/Γ API or runtime
comparison-erasure rule is introduced. Actual evaluation endpoints are kept
in projection residuals because the omitted-RHS experiment was unqualified.

UA-2h now promotes this interface with thirty-three public assertions, including
input/mate agreement, scope controls, whole unit/counit comparison proofs,
both Došen rectangles and whole-family inverse cuts. Existing native consumers
and all 94 nonsplit assertions pass with the constructor module loaded.
The two generic identity-image laws are factored at the original mate owner;
the seven constructor comparison definitions reuse them. The
[introduction audit](../emdash2/audits/adjunction-from-hom-comparison/README.md)
now routes to active owners and reviewers; older compressed variants remain
only in Git history.

The constructor is one new structural introduction, not a body derived from
the old opaque Adjunction classifier. Its mathematical input includes the
whole inverse/coherence data. It does not construct a closed Freyd model,
remove the existing postcomposition lift, or derive product/terminal providers
without independently available whole comparisons. Primary terminality and Γ
remain independently implemented; neither was made to depend on this
constructor. The public family consumer uses the existing lift after
constructing J and qualifies that interoperability explicitly.

A possible make_adjunction_from_unit_counit would instead accept whole η, ε
and both triangle laws, with naturality retained in the transformation types.
It is a related introduction into the same Adjunction classifier, not another
notion of adjunction. Keep it as an option rather than an additional current
deliverable without a concrete need. The Hom-comparison route has priority.

UA-2g now derives the native unit/counit identity-image laws from the existing
mate/semantic functor comparisons. After the seven scoped input-agreement
views specialize those laws to the supplied comparison, the public extraction's
component formulas and existing ordinary modification interface yield whole
η/ε agreement. This requires no new unit/counit agreement primitive or unifier.
The earlier direct whole-unit unifier experiment left expanded curry/Hom
constraints unresolved and is not selected. The public owners retain all eight derived proof bodies; the thirty-three-check
reviewer covers both native Došen rectangles and both point and whole inverse
cuts on arbitrary functor families through the existing postcomposition lift.
That lift is consumed, not derived or replaced.

The [primary terminality consumer audit](../emdash2/audits/terminal-primary-family-boundary/README.md)
now identifies the concrete zero-column and kernel/cokernel family-input
users. Starting directly with J:Adjunction(p,t), a checked definition maps
the unique terminal arrow through J's retained inverse Hom functor to obtain
c(f,g):f⇒g, its inverse and both IsoEvidence laws. Ordinary walking-arrow
realization gives the comparison at the original !ₓ with four computing
identity endpoints. No new structural primitive, path-transported functor,
or caller-supplied naturality square is needed for those constructions.

The source now computes Transf_cat(B,Terminal_cat,F,G) to Terminal_cat.
This narrower terminal-target rule closes the right-hand category in the
existing lifted comparison `[B,C](F,t∘V)≅[B,1](p∘F,V)` without a new structure
primitive. Both terminal and initial lifted Hom inverse cuts check. The
follow-up prototype constructs the whole Arr(h)⇄Arr(k), four computing whole
identity endpoints, and both whole IsoEvidence inverse laws. It retains the
actual maps; equality is used in law evidence rather than to transport a
functor. The earlier component-only boundary is therefore resolved for this
whole introduced-family comparison.

The direct ordinary API now takes J:p⊣t or J:t⊣p itself and uses a closed
Terminal_cat profile. Its chosen-presentation operation constructs a whole
IsoEvidence from Arr(h) to the actual composed arrow family, preserving the
original diagram through categorical reconstruction. Both native zero-column
constructors check in its reviewer without caller-supplied terminal-profile
or square evidence. The constant-postcomposition view is now at its existing
family-view owner, with a failing no-view control and negative scope tests.

The closed terminal profile uses one deliberately added ground proof-time
eta law, id₁≡const₍*₎. Its inverse functor is an explicit constant functor;
the core-target inverse law uses the genuinely discrete Path(Unit) assembly.
This is not a claim that the profile follows from the former beta rules or
that objectwise contractibility suffices for arbitrary directed categories.

Production kernel-counit and cokernel-unit zero-column mate inputs now use
the derived comparison maps. Their existing whole differential observations
use proved endpoint equations from the categorical evaluation laws. The
runtime factor/reconstruction and native connecting tests pass without
weakening their assertions. The two old zero-column DefIso wrappers are
removed. UA-3e also migrates every remaining family-normalizer user and
removes the two primitive declarations and their sixteen rules. Selected-choice
adapters use the primary family interface; canonical kernel/cokernel inputs
use original-D reconstruction directly. Whole ordinary uniqueness is observed
from an actual modification through hom_to_path in the genuinely discrete
functor-category Hom. It neither defines nor transports an operational functor.

All eight unchanged nonsplit proof–CAS artifacts pass again (94 assertions),
including both displayed certificates. The selected-family reviewer checks
point endpoint computation, next-Hom action, whole endpoint laws and both
inverse-law types. The former DefIso-specific wrapper API and raw inverse-cut
tests are explicitly retired with the axioms, not relabelled as computations
of IsoEvidence. Required native computations and original diagrams are
preserved. The broader higher-terminality interpretation remains open.

UA-3f's [bounded unifier audit](../emdash2/audits/terminal-uniqueness-unification/README.md#bounded-inference-audit-ua-3f)
passes typed arbitrary-arrow, composite, identity, two-provider and omitted-
source uses. Runtime nonconversion and unrelated-arrow controls remain
negative; incompatible endpoints and an omitted terminal witness are rejected.
The seven inherited critical pairs are unchanged; the exact candidate adds
five replaceable-variable diagnostics at its own line. This extends the
positive feasibility evidence without installing a rule. The current native
consumers need no such rule, so promotion remains conditional on a concrete
consumer and its import-context audit. No general higher terminality or
all-inference guarantee is inferred.

## Review Evidence

Source review covered the linked active owners, their current reviewers,
current SOP/canonical notation, and the two completed goal audits/ledger.
Lambdapi's installed `parsing/scope.ml`, `handle/command.ml` and `core/unif.ml`
confirm the distinction between a symbol-headed runtime rule and a unification
rule on the wrapped comparison. The upstream command manual was also checked.
The fresh isolated terminal-unifier probe described above succeeds; no
compiler fix or library rule promotion is claimed.

Three unchanged focused reviewers pass with warnings and subject reduction
enabled at the normal serial 2GiB/90s profile, `OCAMLRUNPARAM=o=20`:

- `examples/terminal_objects.lp` — selected cut, uniqueness path and negative
  conversion assertion;
- `examples/one_cat_terminal_adjunctions.lp` — whole mate/inverse observations,
  retained old terminal normal form and distinct unit;
- `examples/categorical_contractions.lp` — existing whole inverse and derived
  contraction observations.

Logs are `terminal_objects-20260917-104339.log`,
`one_cat_terminal_adjunctions-20260917-104343.log` and
`categorical_contractions-20260917-104348.log` under the main worktree's
`emdash2/logs/probes/`. No formal source, rule, unifier, model contract or CAS
code was changed; no repo-wide typecheck or Γ/Op experiment was run.

The isolated whole-terminal-owner copy plus the user's unifier is
`tmp/probes/terminal_uniqueness_bare_unif_review.lp`; it checks a typed
`eq_refl` consumer and a negative runtime-conversion observation. Its log is
`terminal_uniqueness_bare_unif_review-20260917-105204.log`. This is actual
proof-time evidence, not merely successful parsing. The unifier is not
registered as a library owner or positive regression suite.

The no-unifier control is `tmp/probes/terminal_uniqueness_no_unif_control.lp`;
its expected failure is recorded in
`terminal_uniqueness_no_unif_control-20260917-105334.log`. The failure is the
specific unsolved terminal-arrow comparison, not a timeout or import failure.
Both runs used the same unchanged terminal owner, ordinary probe resource
profile, warnings and typing checks. No broad inference or overlap audit of
the prospective unifier has been performed.
