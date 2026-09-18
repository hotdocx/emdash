# EMDASH v3.2 Current Status And SOP

Date: 2026-05-26
Last consolidated: 2026-09-16
Status: living current-state and kernel-development authority

The active kernel and the nested [AGENTS.md](../AGENTS.md) own semantics and
editing policy. This report retains the source catalogue, architecture and
SOP below. Dated implementation narratives and obsolete validation totals
are preserved in the [consolidated history](REPORT_EMDASH_V3_2_CONSOLIDATED_HISTORY_2026-09-16.md),
with their source links and decisions. Their “next” statements are historical.

The current native homological interface is whole J⊣K and Q⊣I, whole H and
direct δ, canonical categorical exactness, and the native snake with its
LES/sign comparison. Both nonsplit displayed proof–CAS certificates are
qualified under explicit model, normality and interpretation contracts.
Output exactness is derived. See the
[native final audit](../../docs/TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_FINAL_AUDIT.md)
and [book Chapter 31](../book/chapters/31-additive-abelian-and-homological-computation.md).

The [consolidation plan](../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_CORE_CONSOLIDATION_REVIEW.md)
records the current source separation and retirement: shared raw inputs and
ordinary H records have independent owners; obsolete model/connecting wrappers
are removed; useful CAS/provider algorithms and the ordinary iterator remain
explicit references. Native operations do not depend on those old wrappers.
The [consolidation final audit](../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_CORE_CONSOLIDATION_FINAL_AUDIT.md)
records completion, the two new structural declarations and the final-kernel
94-assertion native proof–CAS replay.

Reusable categorical additions remain at their own owners: ordinary adjunction
family lifting, diagram reconstruction, terminal-family comparisons, and
product/biproduct operations. [Whole contractions](../emdash3_2_categorical_contractions.lp)
use existing Ω data; [ordinary terminal/initial adjunctions](../emdash3_2_one_cat_terminal_adjunctions.lp)
add two explicit structural presentations. The original terminal normal forms
and selected inverses remain. General higher terminality replacement is not
claimed. Chapters 12 and 30 distinguish declarations from derived operations.

Two displayed-identity projection clauses now infer equivalent family
presentations from the identity head. Their focused reviewer, the nucleus
diagnostics and affected native consumers pass; the plan contains the exact
resource and warning receipts. This does not repair the separate Op/profile
qualifications. The [whole input/H-comparison candidate](../audits/categorical-family-introduction-boundary/README.md)
is meaningful but unqualified; the user selected retaining it as follow-up
while finishing consolidation. Op/duality, action-profile integration and the
large six-term comparison remain deferred.

The initial main/Pages publication was df9b4778. The user subsequently
authorized completed consolidation c3792b67 and book 0.9.1-dev for main/Pages;
both are published, with the live PDF matching the checked artifact. See the
[publication receipt](../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_CORE_CONSOLIDATION_LEDGER.md#post-completion-main-integration-and-pages-publication).

## Sources Of Truth

- `emdash3_2.lp`: active kernel definitions and runtime/proof-time behavior,
  including the reusable equality-local skeleton, restricted `Core₁`, and
  computational `CoreInclTransf` infrastructure.
- `emdash3_2_presheaves.lp`: one-way Cat-valued presheaf standard-library
  facade. It imports the kernel, exposes runtime object/hom projections to
  `Catd_cat(K^op)`, compares the two category heads only at proof time, and
  derives restriction from `Pullback_catd_func(Op_func(F))`. Transparent
  aliases additionally expose Yoneda, restriction-oriented arrow totals,
  conventional slices, and Cat-valued higher sieves through existing owners.
- `emdash3_2_eq1_hom_action.lp`: one-way derived native equality-valued
  hom-action, groupoidality, and structured-transport layer; it imports the
  kernel and is imported by diagnostics/examples, never by the kernel.
- `emdash3_2_eq1_evidence_property.lp`: one-way transparent native
  equality-valued evidence-property, retract-truncation, and finite-`NCat`
  object-truncation layer; it imports the kernel and hom-action extension,
  never conversely.
- `emdash3_2_sieves.lp`: downstream one-way native subterminal-category and
  ordinary-sieve layer. It imports the presheaf and equality-evidence modules,
  packages ordinary sieves as pointwise-subterminal higher sieves, and
  preserves them under the existing pullback action. It declares neither
  `Omega` nor topology.
- `emdash3_2_sites.lp`: downstream one-way direct ordinary-sieve topology
  layer. It exposes membership, a canonical maximal sieve, proposition-valued
  sieve coverages, maximality/pullback/local-character laws, named topology
  projections, and the chaotic topology. It declares no `Omega`, generated
  coverage saturation, sheafification, or descent.
- `emdash3_2_generated_topologies.lp`: downstream one-way, rule-free
  generated-topology layer. Type-valued sieve generators retain their
  presentation witnesses, while generated coverhood is the
  proposition-valued intersection of every Grothendieck topology accepting
  them. Maximality, pullback stability, and local character are inherited
  pointwise; generator inclusion and leastness compute by application. The
  module provides no inductive cover derivations, truncation/HIT, decision
  procedure, affine specialization, sheafification, or scheme.
- `emdash3_2_strict_pointwise_equivalences.lp`: generic strict
  pointwise-to-whole fixed-forward equivalence assembly for ordinary and
  displayed transformations. The forward transformation already owns
  naturality internally. Rigid inverse transformations compute to the
  selected pointwise inverse arrows, and whole cancellation paths complete
  `OmegaEquivAlong` in the corresponding functor category. The module does
  not assemble incoherent arrow families, invert arbitrary lax
  transformations, or add generic functor extensionality.
- `emdash3_2_one_cat_modifications.lp`: ordinary-target modification
  introduction between two already whole transformations. OneCat makes its
  native component cells and remaining coherence proposition-valued; the
  structural primitive exposes the supplied cells through the existing
  component/evaluation Hom action and its Cat-valued specialization. The
  staged transfor identity path is a definition using the original unit cut.
  This extends the ordinary introduction interface without replacing
  hom_int/homd_int or changing any Op signature. The complete Γ/H audit is
  its concrete consumer; the remaining Γ/H promotion is tracked separately.
- `emdash3_2_monads.lp`: monad-primary, opposite-dual computational layer.
  `Monad(T)` is indexed by a whole endofunctor with stable full unit and
  multiplication observations. Whole extension retains higher action, while
  ordinary ambient `comp_fapp0` owns Došen beta and accumulation. Kleisli cut
  is transparent derived notation. `Comonad(D)` is the transparent
  `Monad(D^op)` classifier. Stable counit, comultiplication, and point
  coextension heads supply the narrow runtime mirror needed by ambient dual
  beta, accumulation, counit-extension identity, and the comultiplication
  bridge. Whole coextension transparently reuses endpoint-swapped monadic
  whole extension; no whole unifier or equality bridge remains. Existing
  adjunctions construct both structural instances. The module claims neither
  an explicit Kleisli category, free syntax, nor a global decision procedure.
- `emdash3_2_triangular_binary_products.lp`: enhanced triangular selected-
  binary-products layer. `BinaryProducts(C,P)` is indexed by one whole
  `P : C × C ⊢ C`; its projections and represented-family pairing are whole
  transfors, while stable component/off-diagonal heads retain Došen's
  `K1a`, `K2a`, pairing beta/distribution/eta, direct post-`K(id)` projection
  betas, and both selected section-6.4 normalizations. Canonical
  `Struct_sigma`, not the reducible `Product_pair` alias, owns rule matching.
  One direct proof-time unifier compares generic `P` action with the
  triangular map; projection paths derive by congruence and direct beta while
  runtime forms remain distinct. Eta/distribution derive ordinary hom-level
  uniqueness. A transparent whole unpair functor retains higher action and
  carries both pointwise inverse paths. Equality of the whole pair/unpair
  functors remains an explicit assembly boundary, so no `OmegaEquivAlong` is
  claimed.
- `emdash3_2_terminal_objects.lp`: whole selected terminal-object layer.
  `TerminalObject(C,t)` exposes `! : id_C => Const_t`, stable components,
  computing off-diagonal point action and canonical cuts, and retained full
  hom action. Every `Hom_C(A,t)` is contractible and recentered at `!_A`, so
  arbitrary `f = !_A` and `!_t = id_t` are derived paths. Arbitrary arrows and
  `!_t` remain runtime-distinct; there is no variable-headed rewrite or
  bare-variable unifier.
- `emdash3_2_cartesian_categories.lp`: transparent rule-free pairing of
  `BinaryProducts(C,P)` and `TerminalObject(C,t)`. It adds no duplicate
  product or terminal computation.
- `emdash3_2_triangular_binary_products_finite_limits.lp`: assumption-explicit
  bridge to the existing per-pair `BinaryProductPresentation`. A supplied
  `BinaryProductsWeightedComp` carries each strict `DefIso`-based weighted
  witness and paths identifying both weighted projections with the triangular
  projections. It adds no automatic `DefIso`, rule, unifier, or reverse global
  assembly.
- `emdash3_2_pullbacks.lp`: chosen computational/internal pullbacks as one
  whole contravariant slice family. `SliceSigma_catd(C)` reuses the existing
  covariant comma family for `Σ_f:C/X→C/Y`; `SliceBaseChange_catd(PB)` has
  exact `C/X` fibres and supplies `f*:C/Y→C/X`, with every internal base
  arrow carrying the existing adjunction `Σ_f⊣f*`. Stable whole mate
  functors and point heads retain the two triangle cuts after projection;
  narrow proof-time rules and non-opaque typed-reflexivity paths relate them
  to explicit unit/counit semantics while runtime stays distinct. The generic
  adjunction profunctor comparison owns the whole varying-endpoint Hom
  presentation. Body-unfolded canonical whole unifiers identify the stable
  mate functors with their semantic bodies at proof time. Exact raw-Hom-guarded
  `comp_fapp0 Cat_cat` rules reduce both stable whole composites to identity;
  the wildcard-only version is rejected because it reconstructed the wrong
  endpoint after `Op`. No additional `OmegaEquivAlong` package is required. Generic
  arbitrary-object/arrow Sigma observations replace the former slice-specific
  record surface. Stable whole `f*`, object, unit, and counit observations
  retain the declaration indices; their `tapp1` projections are Došen's
  `γᶜ`/`φᵃ`, with both full `(ac)` rectangles and identity component triangles
  computing at exact post-`Op` shapes. Generic composed-functor object and
  identity-action rules own `(f*∘Σ_f)[a]`, `Σ_f(id)`, and `f*(id)`; no
  pullback-specific copies remain. Canonical represented postcomposition computes the
  `Σ_f` domain and structure arrow without equality transport. The pullback
  object, projections, derived directed square, exact Hom cone category,
  universal lift, and uniqueness are derived from that adjunction. No
  pullback-specific cone constructor accepts a square witness. Raw ambient
  projection composites do not collapse to bare arrows in an arbitrary higher
  category: the first law is a retained directed slice cell and the second
  computes through whole Hom recovery.
  Generic family substitution `Pullback_catd` remains a separate owner;
  explicit pseudo invertibility, products-in-slices, weighted pullbacks,
  pushout duality, general `Pi_along_func`, Beck–Chevalley, and Frobenius are
  later assumption-explicit consumers. The selected slice `Π_u` is active in
  the immediately following module.
- `emdash3_2_slice_dependent_products.lp`: selected coherent dependent
  products indexed by `PB : PullbackStructure(C)`. One whole covariant family
  has exact fibre `C/X` and action `Π_u:C/X→C/Y`; each internal arrow carries
  the existing second adjunction `u*⊣Π_u`. Generic unit/counit observations are
  the actual whole transfors. Their `tapp1` observations compute to stable
  `γΠᶜ`/`φΠᵃ` heads, and both full post-opposite Došen rectangles plus
  component triangles compute. No composite-point unifier or specialized
  identity-action rule is added. Transparent semantic mate functors retain
  higher action, and the named whole Hom comparison is the generic adjunction
  `ProfComparison`. `Pi_cat`, general proposed `Pi_along_func`, and slice
  `Π_u` remain distinct; Beck–Chevalley, Frobenius, exponentials, and the thin
  convention-sensitive LCCC name remain later layers. The transparent
  `SliceDependentProducts(C)` total pairs only the selected pullbacks and their
  indexed dependent-product structure.
- `emdash3_2_direct_cover_completion_locality.lp`: downstream conventional
  comparison for the direct whole-presheaf cover-completion HIT. A derived
  retained-member theorem is projected through one whole transformation
  `restriction o glue => id`; strict pointwise closure supplies the second
  functor equality. Together with the HIT's whole silent law, this constructs
  `IsTopologyLocalPsh(DirectCoverCompletionPsh)`. The module does not yet
  identify the syntactic direct-cover sheaf with the rigid `Sheaf_cat` facade,
  assemble the reflector/adjunction, lift to CommRing values, or prove left
  exactness. Whole Hom universality lives in the subsequent module.
- `emdash3_2_direct_cover_completion_universality.lp`: whole
  seed-functoriality and categorical-HIT uniqueness for the direct-cover
  completion recursor. Its object projection computes to the deployed
  recursor; whole unit beta and topology-local eta are higher equality
  evidence. These assemble precomposition by the HIT unit into an
  `OmegaEquivAlong Cat_cat` on Hom categories into every topology-local
  target. The eta law is not generalized to arbitrary maps into an
  independently selected one-sided cover algebra. The module does not yet
  assemble the fixed-site reflector/adjunction, identify the rigid
  `Sheaf_cat` facade, lift to CommRing values, or prove left exactness.
- `emdash3_2_ringed_sites.lp`: downstream one-way, rule-free supplied
  reflective-sheafification layer. A rigid topology- and value-category-indexed
  sheaf classifier is paired with a transparent capability carrying whole
  inclusion and reflector functors, their adjunction, and fixed-counit
  `OmegaEquivAlong` evidence. Generic adjunction owners derive whole internal
  mate/glue maps. Its `ReflectiveCommRingedSite` specialization exposes the
  selected structure sheaf as a whole CommRing-valued presheaf through the
  inclusion. It does not construct canonical sheafification, generated
  saturation, descent or left exactness, impose a local-ring condition, or
  define a scheme.
- `emdash3_2_site_basis.lp`: downstream transparent, rule-free whole
  sheaf-basis layer. Opposite precomposition supplies restriction of
  `V`-valued presheaves along a selected base functor. A supplied sheaf
  restriction is tied to it by one `IsoEvidence` between whole composites,
  and comparison-lemma strength is retained as `OmegaEquivAlong Cat_cat`.
  Generic functor/transformation owners retain action and naturality. A
  proof-time path and derived `IsoEvidence` compare generic precomposition's
  cut normal form with direct composition without adding a runtime rule. It
  does not construct topology, continuity, sheafification, an induced slice, a
  Beck--Chevalley mate, a local-exactness witness, component squares, or a raw
  base-category equivalence.
- `emdash3_2_commutative_algebra_ringed_space_covers.lp`: downstream one-way,
  rule-free global-cover substrate. It retains a reflective CommRinged site,
  a distinguished object of its base category, and an ordinary sieve covering
  that object in the retained topology. The existing Grothendieck-stability
  owner derives covering pullbacks along every arrow, while selected sieve
  members expose their actual restriction arrows. It does not assert that a
  cover is finite or affine, impose locally-ringed support, store overlap or
  cocycle fields, define a scheme, or construct gluing.
- `emdash3_2_commutative_algebra_binary_covers.lp`: downstream transparent,
  rule-free binary cover-generation layer. Every arrow of the retained
  covering sieve carries an executable Boolean-selected chart, an actual
  factor map, and its triangle. Since both charts are already sieve members,
  these witnesses say that the two selected charts generate the retained
  covering sieve. The module constructs no second sieve, rule, unifier,
  external restriction/coherence field, affine label, locally-ringed
  condition, scheme, or gluing operation.
- `emdash3_2_commutative_algebra_ringed_space_restrictions.lp`: downstream
  one-way, rule-free whole chart-slice restriction substrate. It exposes the
  whole conventional slice-domain functor, restricts CommRing-valued
  presheaves by generic composition, and retains a supplied reflective site
  on the actual slice with one whole computational `DefIso` to the ambient
  restriction. It does not derive an induced topology or reflector, add a
  site-morphism/continuity calculus, assert affineness or locally-ringed
  support, define a scheme, or construct gluing.
- `emdash3_2_nat_arithmetic.lp`: one-way reusable Nat arithmetic/sethood
  module. It owns `nat_add`, the canonical `NatSucc_func`, the associativity
  theorem, the Unit/Empty proposition witnesses, and `nat_is_set` without
  importing the walking-HIT surface.
- `emdash3_2_finite_families.lp`: one-way reusable Nat/Sigma finite-family
  layer. It owns the right-associated length-indexed classifier,
  nil/cons/head/tail and singleton/pair observations, pointwise map, dependent
  pointwise evidence, and sethood. It declares no `Fin`, lookup,
  list/Sum/inductive interface, append, permutation quotient, rule, unifier,
  or package eta.
- `emdash3_2_commutative_algebra.lp`: one-way set-carrier commutative-ring
  object module. It separates operation data from eight sufficient law
  fields, exposes readable carrier/operation/law projections, and constructs
  the one-element zero ring. It adds no rewrite/unification rule and declares
  no ring morphism category, localization, finite-family, power, or polynomial
  interface.
- `emdash3_2_commutative_algebra_category.lp`: one-way structured morphism and
  ordinary-category layer. It proves morphism laws proposition-valued,
  morphisms set-valued, and pointwise carrier equality sufficient for full
  structured-map equality; `CommRing_cat` retains generic whole-arrow owners,
  while localization and empty-variable polynomial consumers select stable
  pointwise composition and identity comparisons. The whole invertibility-
  sieve consumer selects a carrier functor with a full Path-map hom action and
  no competing direct capped-action rule.
- `emdash3_2_commutative_algebra_finite.lp`: one-way rule-free finite-algebra
  layer. It owns finite sums/dot products, their structured-map preservation
  theorems, retained coefficient presentations of the unit ideal, and
  base-change-stable algebraic Zariski-cover presentations. It declares no
  `Spec`, localization family, coverage/topology, powers/radicals, fraction,
  polynomial, quotient, or propositional-truncation interface.
- `emdash3_2_commutative_algebra_finite_modules.lp`: downstream one-way,
  rule-free finite-presentation layer. It reuses `FiniteFamily` for finite free
  vectors and for column-oriented matrices, defines transparent vector
  arithmetic, matrix action, zero, and composition, and classifies explicit
  presentation agreement, matrix syzygies, and adjacent composite-zero
  equations. A rows-by-columns matrix acts from `R^columns` to `R^rows`.
  Presentation agreement retains coefficients and an equation; the module
  declares no quotient module, module category, exactness, homology, rewrite,
  or unification rule.
- `emdash3_2_commutative_algebra_presentations.lp`: downstream one-way,
  rule-free fixed-ring presentation-morphism layer. It adds transparent matrix
  addition/negation/subtraction, packages generator rank, relation rank, and
  relation matrix, and retains relation-preserving maps as `F`, `W`, and
  `R_Q o W = F o R_P`. Representative agreement retains `H` and
  `R_Q o H = F-G`; one exact classifier exposes a chain-map component square.
  These are explicit matrix equations, not quotient-module equality, a formal
  presentation category, exactness, or homology.
- `emdash3_2_commutative_algebra_bounded_free_complexes.lp`: downstream
  one-way, rule-free bounded free-complex layer. A boundary-indexed Nat/Sigma
  tail stores every next rank, differential, genuine adjacent-zero law, and
  rest. Length zero is one rank; positive length stores `rank0`, `rank1`,
  `d1`, then the tail, avoiding a redundant nonjudgmental `0 o d1` law.
- `emdash3_2_commutative_algebra_bounded_free_chain_maps.lp`: downstream
  one-way, rule-free chain-map layer over two independently packaged complex
  tails. Zero length is one matrix; positive length stores `F0`, `F1`, the
  first exact square, and a tail that recursively stores later components and
  squares. Neither module claims presented-module quotients, a formal complex
  category, exactness, or homology.
- `emdash3_2_commutative_algebra_finite_free_category.lp`: downstream
  finite-free matrix-category facade. Objects are ranks and Homs are path
  categories of column matrices. Generic category identity/composition remain
  runtime owners; rigid pointwise matrix heads meet them through proof-time
  usability rules and expose constructor-level columns. Runtime identity and a
  runtime composition fold to the rigid head check, but the latter leaves
  twenty genuine higher-action joins. Reducing generic composition directly
  to transparent `comm_ring_matrix_comp` exceeds the bounded check while
  expanding its strict-functoriality overlap. A body-unfolded whole
  rigid/transparent unifier also does not solve; Nat recursion now supplies
  the whole propositional comparison instead.
- `emdash3_2_commutative_algebra_derived_laws.lp`: low-level rule-free
  consequences of the retained commutative-ring basis. It derives left
  additive unit/inverse, right distributivity, multiplication by zero, and
  negation of zero for reuse below localization-specific constructions.
- `emdash3_2_commutative_algebra_presentation_operations.lp`: downstream raw
  presentation-operation layer. The constructed rigid/transparent comparison
  transports generic category units and associativity to transparent matrix
  laws. A reusable five-step matrix-square pasting path then constructs raw
  presentation identity and composition, retaining both generator/relation
  matrices and deriving the composite relation square.
- `emdash3_2_commutative_algebra_matrix_additive_laws.lp`: rule-free
  Nat-recursive additive/bilinear theorem layer. It derives finite-family
  extensional assembly, vector additive/scalar laws, matrix-action linearity,
  matrix additive-group laws, zero composition, and both matrix-composition
  distributivity paths.
- `emdash3_2_commutative_algebra_matrix_subtractive_laws.lp`: derives inverse
  uniqueness, involutive negation, negation of sums/subtractions, subtraction
  chaining/additivity, and preservation of subtraction by both sides of
  composition. It is theorem-level and rule-free.
- `emdash3_2_commutative_algebra_presentation_additive_operations.lp`:
  completes the raw presentation surface with zero and addition on both stored
  matrices. Their relation squares are constructed from the matrix zero and
  bilinearity paths; no opaque square or runtime algebra rule is introduced.
- `emdash3_2_commutative_algebra_presentation_subtractive_operations.lp`:
  negates generator and relation matrices together and derives the resulting
  relation square from matrix composition/negation paths.
- `emdash3_2_commutative_algebra_presentation_agreement_operations.lp`:
  constructs reflexive, symmetric, transitive, additive, precomposition, and
  postcomposition operations on explicit target-factorization agreement. The
  postcomposition witness uses the relation matrix retained by the outer raw
  map; no manually entered square is added.
- `emdash3_2_commutative_algebra_freyd_presentations.lp`: homwise quotient and
  Freyd-category skeleton. Raw presentation morphisms and target-factorization
  agreements form fixed-endpoint categories; existing `Groupoidify` and
  `0`-truncation produce higher and ordinary quotient Homs. The Freyd category
  has presentation objects and those Hom sets; elements are represented by Hom
  from the relation-free rank-one presentation. This skeleton itself stops
  before operations; the downstream operations/usability modules now supply
  raw-class descent and generic identity/composition comparison. The further
  preadditive modules now supply full arbitrary-quotient laws; weak kernels and
  Abelian structure remain separate gates.
- `emdash3_2_commutative_algebra_freyd_operations.lp`: whole quotient-operation
  layer. Fixed raw operands act by whole functors on agreement categories;
  whole representation transfors feed groupoidification extension; nested
  `0`-truncation recursion gives composition and addition on ordinary quotient
  Homs. Raw-class betas compute. Direct inner fapp1 runtime action times out and
  is proof-time; two outer runtime actions add six classified identity
  overlaps.
- `emdash3_2_commutative_algebra_freyd_usability.lp`: sequential usability
  bridge. Generic Freyd identity/composition first meet rigid heads through
  typed proof-time unifiers; only afterward do rigid-head runtime folds expose
  the raw identity class and descended composition. No rule is headed by
  generic `id` or `comp_fapp0`.
- `emdash3_2_commutative_algebra_freyd_preadditive_class_laws.lp`: packages
  quotient-Hom zero/addition/negation and proves additive-group plus bilateral
  distributivity laws on every generating raw class. It remains the explicit
  generating-data layer used by the full descent.
- `emdash3_2_set_path_pointwise_transformation.lp` and
  `emdash3_2_groupoidification_set_extensionality.lp`: a pointwise path family
  between functors into `Path(S)` assembles into one whole transformation when
  `S` is a set. Whole groupoidification extension and its existing eta then
  prove that maps out of `Groupoidify(C)` into `S` are determined by the unit.
  The restriction point comparison is derived from its whole path; no generic
  precomposition rule, dependent eliminator, source action, or adjunction is
  added.
- `emdash3_2_truncation_set_path_induction.lp`: rule-free unary, binary, and
  ternary set-valued path induction derived from `trunc_ind_ambient`, exactly
  for the arities used by the Freyd laws.
- `emdash3_2_preadditive_categories.lp`: generic set-valued abelian-group Hom
  structures and bilateral composition distributivity over the existing
  `comp_fapp0` grammar.
- `emdash3_2_commutative_algebra_freyd_preadditive_laws.lp` and
  `emdash3_2_commutative_algebra_freyd_preadditive.lp`: promote every class law
  through groupoidification and `0`-truncation, then construct the checked
  `PreadditiveCategory(CommRingFreydPresentation_cat(R))` instance. Generic
  composition is connected by explicit existing usability paths.
- `emdash3_2_finite_family_sums.lp`, the matrix-block modules, and the
  finite-free/presentation direct-sum modules: construct flattened append and
  split operations, general and diagonal block matrices, whole finite-free
  sums, the zero presentation, presentation sums, and computed raw/agreement
  operations without a second block carrier or manually supplied square.
- `emdash3_2_commutative_algebra_freyd_direct_sums.lp` and
  `emdash3_2_commutative_algebra_freyd_binary_products.lp`: descend pairing
  and direct sum through groupoidification/truncation, retain the whole sum
  functor and Hom action, and select the generic triangular
  `BinaryProducts` surface. Proof-time rigid comparisons expose concrete
  quotient projections/pairing while generic Došen beta/eta remains primary.
- `emdash3_2_commutative_algebra_finite_free_preadditive.lp`: packages each
  column-matrix Hom as a set-valued abelian group and transports both matrix
  distributivity paths through the existing generic/transparent composition
  comparison. Generic `comp_fapp0` remains the runtime owner; the module adds
  no rule or second matrix operation.
- `emdash3_2_commutative_algebra_finite_free_binary_products.lp`,
  `emdash3_2_commutative_algebra_finite_free_terminal_zero.lp`,
  `emdash3_2_commutative_algebra_finite_free_cartesian.lp`, and
  `emdash3_2_commutative_algebra_finite_free_additive.lp`: select the whole
  block-direct-sum functor and rank zero. Stable observations expose the
  canonical matrix projections, vertical pairing, and zero-row arrow, while
  generic triangular and terminal owners retain whole action. The final
  additive package transparently reuses finite-free preadditivity. The shared
  zero-row uniqueness lemma now lives at its lower matrix owner.
- `emdash3_2_commutative_algebra_freyd_terminal_zero.lp` and
  `emdash3_2_commutative_algebra_freyd_cartesian.lp`: derive terminality from
  zero-row matrix uniqueness and quotient descent, then transparently pair the
  selected product and terminal capabilities.
- `emdash3_2_additive_categories.lp` and
  `emdash3_2_commutative_algebra_freyd_additive.lp`: derive zero composition,
  initiality, injections, copairing, both beta laws, eta, and the diagonal
  biproduct identity from `PreadditiveCategory + CartesianCategory`, then
  instantiate the formal Freyd `AdditiveCategory`. No primitive coproduct,
  weak-kernel, or Abelian claim is added.
- **Primary categorical homology.**
  [Kernel/cokernel adjunctions](../emdash3_2_kernel_cokernel_adjunctions.lp)
  own whole J⊣K and Q⊣I. [Homology families](../emdash3_2_homology_adjunction_families.lp)
  derive whole H from those choices. The native connecting, exact-window and
  snake modules use these operations and their selected inverses directly.
  [Native δ](../emdash3_2_one_cat_native_connecting.lp),
  [canonical pair exactness](../emdash3_2_one_cat_native_exact_arrow_pairs.lp),
  [exact diagrams](../emdash3_2_one_cat_native_exact_diagrams.lp), and the
  [native snake result](../emdash3_2_one_cat_native_snake_six_term_result.lp)
  are current entry points. The snake–LES comparison concerns these two native
  constructions, not compatibility with a retired reference implementation.
- **Shared input vocabulary.** [Chain-pair data](../emdash3_2_chain_pair_data.lp),
  [raw presentation chain inputs](../emdash3_2_commutative_algebra_presentation_chain_inputs.lp)
  and [native boundary data](../emdash3_2_homology_adjunction_input_data.lp)
  have independent owners. Native raw adapters do not import the former
  homology algorithms merely to obtain their input classifiers.
- **Ordinary observations.** [Homology records](../emdash3_2_homology_records.lp),
  [family records](../emdash3_2_homology_family_records.lp) and
  [native record data](../emdash3_2_homology_adjunction_record_data.lp)
  expose optional views. The categorical H point comparison applies whole Q
  to an actual boundary-diagram map and retains inverse data. Ordinary
  equations at fixed inputs are legitimate downstream observations; the
  stronger whole Γ/H comparison remains an unqualified follow-up.
- **Native proof–CAS contracts and certificates.**
  [Native inputs](../emdash3_2_commutative_algebra_freyd_native_inputs.lp),
  [native maps](../emdash3_2_commutative_algebra_freyd_native_maps.lp),
  [displayed LES exactness](../emdash3_2_commutative_algebra_freyd_native_diagram_exactness.lp),
  [LES certificate views](../emdash3_2_commutative_algebra_freyd_native_les_certificate_views.lp)
  and [displayed snake exactness](../emdash3_2_commutative_algebra_freyd_native_snake_exactness.lp)
  connect the current whole constructions to selected computational data.
  Model, universal-provider, normality and interpretation contracts remain
  explicit. Output exactness is derived. The frontend assembles the nonsplit
  examples under those contracts; it does not close every supplied model.
- **Retained ordinary reference mathematics.**
  [Weak kernels](../emdash3_2_weak_kernels.lp),
  [ordinary kernels/cokernels](../emdash3_2_kernels_cokernels.lp),
  [computational homology](../emdash3_2_computational_homology.lp),
  [ordinary homology families](../emdash3_2_homology_families.lp) and
  [finite arrow tails](../emdash3_2_finite_arrow_tails.lp) remain explicit
  references and support the selected ordinary iterator. They are not the
  primary native universal API. Their continued existence imposes no new
  native/reference compatibility obligation.
- **Shared algebra and CAS computation.** The Freyd presentation, additive,
  weak-kernel, kernel/cokernel, image, polynomial-provider and bounded-complex
  owners remain available for their genuine consumers. The TypeScript
  `src/v3_2/algebra_*` modules retain exact rational/polynomial arithmetic,
  presentation algorithms, bounded H/maps/δ computation and native artifact
  assembly. Computed matrix equations and supplied universal/model semantics
  are distinct contracts. No production computation is replaced by a test
  oracle or by an opaque inverse.
- **Retirement and recovery.** Superseded snake-derived connecting owners,
  old homology model wrappers and their unused reviewers/TypeScript facades
  were deleted from the active graph in the recorded consolidation tranches.
  Git checkpoints and the [execution ledger](../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_CORE_CONSOLIDATION_LEDGER.md)
  retain the inventory and recovery route. The former chronological source
  catalogue is preserved in [history](REPORT_EMDASH_V3_2_CONSOLIDATED_HISTORY_2026-09-16.md#earlier-homological-source-catalogue);
  it is not an active import or implementation list.
- `emdash3_2_commutative_algebra_polynomial.lp`: one-way rule-free
  universal-property layer for free commutative `R`-algebras on a variable
  classifier. It packages contractible structured extensions of base maps and
  valuations, without monomial/coefficient/quotient syntax, a concrete
  positive-variable representation, finite-index facade, unifier, or eta.
- `emdash3_2_commutative_algebra_localization.lp`: one-way localization/unit
  layer. It proves explicit inverse evidence
  proposition-valued, owns path transport and preservation by structured
  maps, and packages localization at one element by contractible pointwise
  factorization. Its universal total-element family exposes Path-valued unit
  evidence at literal ring elements, without concrete fraction, finite-family,
  polynomial, or Zariski syntax.
- `emdash3_2_commutative_algebra_localization_unit.lp`: one-way rule-free
  identity-localization layer. It constructs canonical unit evidence for one,
  proves the factorization space through the pointwise identity contractible,
  and therefore constructs the identity localization of any already-unit
  element. In particular, every ring has a selected localization at one whose
  target and carrier action compute to that ring and the identity. It adds no
  fraction representation, topology, `Spec`, or scheme.
- `emdash3_2_commutative_algebra_localization_zero.lp`: one-way rule-free
  empty-basic-open layer. It derives multiplication and negation at zero,
  proves that invertible zero forces `0=1` and contracts the carrier, and
  constructs the zero ring as the universal localization `R[1/0]`. This is a
  degenerate but computing non-identity-shaped model, not a nondegenerate
  fraction, presheaf, topology, overlap, `Spec`, or scheme interface.
- `emdash3_2_commutative_algebra_localization_idempotent.lp`: one-way
  rule-free fixed-image layer. For `e^2=e`, it constructs the set-valued ring
  `eR={x:R | e*x=x}`, makes its zero/one/addition/negation/multiplication
  compute through the subtype, and proves that `x |-> e*x` has the full
  localization universal property. The selected factor applies the original
  map to the retained underlying fixed point. This is quotient-free and may
  be nondegenerate for a supplied nontrivial idempotent.
- `emdash3_2_commutative_algebra_product.lp`: one-way rule-free componentwise
  product layer. It constructs product rings and componentwise structured maps
  with whole identity/composition paths, while leaving a primitive product
  functor facade consumer-gated.
- `emdash3_2_commutative_algebra_f2.lp`: one-way rule-free closed
  two-element-ring layer on `Bool_grpd`, with all laws proved by internal
  Boolean elimination.
- `emdash3_2_commutative_algebra_localization_split.lp`: one-way rule-free
  split-idempotent consumer. It selects `(1,0)` in a product, builds its
  fixed-image localization and affine arrow, and proves the closed `F2 x F2`
  idempotent differs from zero and one while restriction computes as
  `(x,y) |-> (x,0)`. Matching/descent, `Spec`, and schemes remain downstream.
- `emdash3_2_commutative_algebra_localization_comparison.lp`: one-way rule-free
  overlap layer. It derives unit multiplication/factor extraction, packages
  localization first at `f` and then at the image of `g`, and constructs
  canonical forward/reverse factors against localization at `f*g`. It asserts
  neither equality of chosen localization packages nor inverse laws for the
  comparison maps.
- `emdash3_2_commutative_algebra_localization_overlap.lp`: one-way rule-free
  whole-comparison layer. Contractible localization-factor uniqueness proves
  both cancellation paths for the product/iterated comparison and packages
  the forward map as `OmegaEquivAlong CommRing_cat` and `OmegaEquiv
  CommRing_cat`, without fraction syntax or package equality.
- `emdash3_2_commutative_algebra_presheaves.lp`: one-way CommRing-presheaf
  layer. It exposes transparent values, structured
  restriction maps, carrier application, explicit pointwise
  identity/composition paths, and proposition-valued invertibility support
  closed under further restriction. Pullback and Sigma-totalization through
  the selected carrier/unit families assemble that support as both a higher
  sieve and an ordinary sieve whose literal-arrow membership computes. One
  shaped proof-time represented-family comparison crosses the variance
  presentation boundary without runtime collapse. It declares no topology,
  sheaf, or ringed-site package.
- `emdash3_2_commutative_algebra_locality.lp`: one-way locality
  bridge. It views the existing semantic invertibility sieve as a cover in a
  supplied topology and uses literal membership plus a chosen localization to
  select the universal structured factor into each presheaf value, retaining
  the pointwise factor triangle. PSSS-08c0C packages those factors as one
  internal ordinary transformation over the category of support elements;
  its single component rule exposes the selected factor and generic `tapp1`
  owns naturality. Contractible-factor uniqueness separately derives the
  objectwise restriction equation as a construction audit. It claims no
  limiting/descent comparison, sheaf, ringed-site package, generated topology,
  `Spec`, or scheme.
- `emdash3_2_commutative_algebra_local_ringed_sites.lp`: downstream
  transparent, rule-free topology-local local-ring presentation. The literal
  empty sieve computes to `Empty` membership; invertible zero makes it cover.
  An invertible sum selects a covering sieve and a Boolean unit branch for
  every retained member. This witness-rich interface avoids both a raw sieve
  union and propositional truncation while retaining executable choices. It
  does not assert sheafhood, construct the automatic support laws, compare
  with stalks, classify open immersions, or define schemes.
- `emdash3_2_commutative_algebra_matching.lp`: one-way computational
  matching-family layer. It pulls the selected Path-valued carrier family over
  the category of invertibility-support elements and forms its Pi category.
  Every localization element selects one internally coherent section whose
  literal component applies the corresponding universal factor. PathLift
  supplies equality-path action. The single component rule uses the existing
  full fibre-covariance owner and adds no external naturality field. It
  supplies no inverse/glue, descent equivalence, sheafhood, limiting claim,
  generated topology, `Spec`, or scheme.
- `emdash3_2_commutative_algebra_glue.lp`: one-way rule-free whole
  Cartier-locality layer. It retains the earlier genuine glue functor and its
  point/component observations, then fixes the already-computing restriction
  functor as an `OmegaEquivAlong Cat_cat`. The selected left inverse is one
  whole glue functor with both whole composite-functor paths; evaluating those
  paths derives the earlier compatibility package. At a literal support
  member, the component endpoint observes the selected localization factor
  applied to the glued element. Generic functor action owns matching-arrow
  action; no external naturality family is stored. The sieve `D(s)` need not
  cover, so this is not ordinary covering-sieve sheaf descent or a
  stalk-local-ring theorem; generated topology, `Spec`, and schemes remain
  downstream.
- `emdash3_2_commutative_algebra_affine_glue.lp`: one-way rule-free derived
  affine consumer. For the identity CommRing presheaf on
  `Op_cat CommRing_cat`, it evaluates coherent matching sections at the
  localization-map support centre. Contractible factor uniqueness derives
  the left component law, while the universal factor to each support member
  supplies a whole Sigma arrow whose internal Pi-section action derives the
  Cartier component law. The complete selected-glue package is constructed
  for every chosen affine localization, including the closed split-idempotent
  model; equality of whole functors and ordinary sheaf descent remain open.
- `emdash3_2_commutative_algebra_affine_spec.lp`: one-way rule-free
  computational affine-chart facade. It exposes the conventional big slice
  over `Spec(R)`, its CommRing-valued coordinate presheaf, arbitrary
  structured charts and internal chart arrows, selected basic opens, and the
  product/iterated-localization overlap in both geometric directions.
  Coordinate restriction computes through the generic Sigma projection to
  the existing whole ring maps. This is not yet a small Zariski site, sheaf,
  locally ringed space, or complete scheme.
- `emdash3_2_commutative_algebra_affine_zariski.lp`: one-way rule-free
  generated-topology specialization on the big affine slice. For every
  literal chart `R -> S`, it lifts each selected localization in a finite
  Zariski presentation to a whole slice arrow, retains containment of those
  arrows as witness-rich generator data, and applies the generic
  impredicative-intersection owner. The resulting topology is lawful and least
  among topologies accepting those generators. Its exact internal composite
  endpoint makes the chart triangle reflexive, and coordinate restriction
  computes to the existing whole localization map. It introduces no Sigma
  eta, external naturality or triangle field, coverhood rule, localization
  choice, sheafification, small-site comparison, or scheme.
- `emdash3_2_commutative_algebra_affine_ringed_sites.lp`: one-way rule-free,
  assumption-explicit affine structure-sheaf layer. It consumes the exact
  internally generated big-affine Zariski topology, retains a supplied
  reflective CommRing-valued sheafification capability and one sheaf object,
  and requires a whole `DefIso` from the included structure presheaf to the
  computing affine coordinate presheaf. Readable chart components project
  the two whole transformations; they do not replace internal action or
  naturality with object-only fields. The module does not construct
  sheafification, prove localization locality or a stalk-local-ring theorem,
  compare with the small site, or package a scheme.
- `emdash3_2_commutative_algebra_affine_locality.lp`: one-way rule-free,
  assumption-explicit affine coordinate-locality layer. It requires the
  generic fixed-forward whole localization locality for every object of the
  big affine slice, every coordinate section, and every supplied localization
  package. Literal chart endpoints reduce to the retained ring and chosen
  localization, and a transparent compatibility projection serves the
  earlier component-view glue consumers. It makes no global localization
  choice, does not construct locality, and does not claim covering-sieve
  sheaf descent, stalk-local-ring structure, small-site comparison, or a
  scheme.
- `emdash3_2_commutative_algebra_affine_schemes.lp`: one-way rule-free thin
  computational affine-scheme presentation. It pairs the whole reflective
  structure-sheaf presentation with whole coordinate-localization locality;
  the base ring continues to own the big affine slice and generated topology,
  while finite atlases remain consumer data. Transparent projections expose
  the existing ringed site, whole coordinate `DefIso`, and selected locality.
  It does not construct either capability, duplicate chart/cover/overlap
  action, define general non-affine gluing, compare with the small site,
  construct stalks, or assert a stalk-local-ring theorem.
- `emdash3_2_commutative_algebra_affine_basis.lp`: downstream transparent,
  rule-free whole affine-chart realization layer. A selected whole functor
  from the big affine slice into the actual ambient slice carries the generic
  sheaf-basis equivalence, while direct presheaf restriction retains the
  computing ambient structure presheaf and one whole `DefIso` identifies it
  with an existing affine-scheme presentation. Generic `DefIso` composition
  yields the coordinate comparison. It does not construct those inputs,
  assert raw category equivalence, store local-exact/component coherence,
  transport generic glue, define a general scheme, or impose a stalk-local
  ring condition.
- `emdash3_2_commutative_algebra_affine_cover_charts.lp`: downstream
  transparent, rule-free realization of an actual global cover chart. It
  retains a supplied reflective slice, coordinate ring, existing affine
  presentation, whole affine-basis functor, and the existing whole
  `AffineBasisRealizationAlong`; the coordinate `DefIso` is derived. Readable
  observations are exposed, while dependent projection types stay at literal
  nested-Sigma endpoints and require no package eta, rule, or unifier. It
  stores no overlap/cocycle family and claims no locally-ringed scheme.
- `emdash3_2_commutative_algebra_affine_cover_presentations.lp`: downstream
  transparent, rule-free global-first binary affine-cover layer. It combines
  two charts generating the retained covering sieve with their two whole
  affine realizations. Pullbacks, overlaps, and repeated restrictions remain
  derived at the global and generic composition owners. It is a computational
  cover presentation, not a locally-ringed scheme certificate or atlas-first
  gluing constructor.
- `emdash3_2_commutative_algebra_affine_cover_refinements.lp`: downstream
  transparent, rule-free CS-07 usability consumer. For any retained sieve
  member, generation returns the existing Boolean-selected factorization;
  its side derives the selected affine generator, already-owned whole affine
  realization, and coordinate ring. It deliberately adds no duplicate
  refinement package, rule, unifier, external coherence, claim that the
  refinement itself is affine, global realization, or scheme classifier.
- `emdash3_2_commutative_algebra_locally_ringed_space_presentations.lp`:
  downstream transparent, rule-free whole-object consumer. A supplied
  reflective slice on `K/X` retains topology, sheaf semantics, and one whole
  `DefIso` to the computing ambient restriction; topology-local ring
  computation is attached to that target. Pairing it with the existing binary
  affine atlas produces the fibrewise
  `BinaryLocallyRingedAffineCoverPresentation` certificate. The supplied site
  determines admissible chart geometry; the layer adds no overlap/cocycle
  field, gluing constructor, classical-open comparison, or semantic scheme
  category.
- `emdash3_2_commutative_algebra_site_relative_schemes.lp`: downstream
  transparent, rule-free global usability layer. Its dependent total retains
  one `ReflectiveCommRingedSpaceCover` and the existing locally-ringed binary
  affine-cover certificate. Structure presheaf, restriction, selected cover,
  chart realizations, overlap compatibility, and cocycle behavior remain at
  existing whole owners. This is a site-relative computational scheme
  presentation, not atlas-first gluing, an unqualified classical or Zeuner
  scheme, or a representation-independent `Scheme_cat`.
- `emdash3_2_commutative_algebra_affine_points.lp`: one-way rule-free affine
  functor-of-points/basic-open layer. The existing Yoneda presheaf represents
  `Spec(R)`, the semantic identity-presheaf invertibility sieve is `D(f)`, and
  localization contractibility constructs a `TypeEquiv` between maps
  `R[1/f]->S` and `D(f)`-points at every test ring. Both presheaf actions stay
  at generic owners; there is no external naturality family, whole-presheaf
  equality, univalence principle, topology, sheafhood, or general scheme.
- `emdash3_2_commutative_algebra_affine_atlas.lp`: one-way rule-free concrete
  atlas layer. Complementary idempotents in `R x S` retain their selected
  binary Zariski-cover family, and their orthogonal overlap is represented by
  the computing zero localization. Internal affine chart arrows expose whole
  coordinate restrictions to the zero ring. The closed `F2 x F2` consumer is
  an atlas/glue presentation, not a sheaf theorem, locally ringed space, or
  general scheme record.
- `emdash3_2_commutative_algebra_zariski.lp`: one-way rule-free presented
  affine-Zariski layer. It retains a selected localization package for each
  generator of an algebraic cover presentation, exposes chosen basic-open
  arrows, and derives elementwise base-change factors, pointwise triangles,
  Sigma arrows, and returned pulled-back sieve membership. It makes no global
  localization choice and declares no propositional coverage/topology,
  subcanonicity, `Spec`, or scheme.
- `emdash3_2_walking_end_hit.lp`: one-way opaque one-dimensional walking-
  endomorphism directed-HIT module. It owns the opaque category/base/loop,
  explicit dimension evidence, contextual `Functord` eliminator, derived
  section/recursor views, transparent Code/power/decoder construction, the
  explicit-κ restricted-CoreIncl two-factor spiral specialization, Hom--Nat carrier
  packages, sethood, directed negative consequences, and a separate `BNat`
  consistency model. It contains no generated-word Hom or WalkingEnd-specific
  identity/composition rule.
- `emdash3_2_integer_localization.lp`: transparent rule-free Integer facade
  over the set-truncated telescope localization of Nat successor. It exposes
  zero, nonnegative and negative representatives, inverse successor and
  predecessor actions, sethood, and the set-targeted induction consumed by
  the Circle proof.
- `emdash3_2_circle_hit.lp`: one-way opaque groupoidal Circle HIT. It owns the
  base and generating equality loop, explicit one-dimensional evidence,
  unrestricted dependent elimination, judgmental point computation,
  judgmental dependent `PathOver` loop computation through the stable
  `eq_apd` owner, the universal Integer cover, and the complete encode/decode
  proof. Its ordinary `eq_ap` loop equation remains propositional. Its based
  loop type and the corresponding categorical Hom are explicitly `TypeEquiv`
  to Integer.
- `emdash3_2_groupoidal_interval_hit.lp`: one-way opaque groupoidal interval
  HIT. It owns two distinct endpoint constructors and one generating path,
  with judgmental computation at both points and on the dependent segment
  through the stable `eq_apd` owner. Constant-family recursion inherits those
  dependent betas; its ordinary `eq_ap` segment observation remains
  propositional.
- `emdash3_2_walking_interval_comparison.lp`: concrete comparison from the
  existing join-derived `WalkingArrow_cat` to `Path_cat(Interval_grpd)`. A
  whole profunctor cross cell carries `interval_seg`, the join eliminator
  gives the structural presentation, and one stable deployed unit computes at
  both endpoints while retaining first and next hom action. Generator
  agreement is scoped propositional rather than a generic join-arrow rule.
- `emdash3_2_walking_interval_restriction.lp`: transparent whole restriction
  of interval functions along that deployed unit. Endpoint readings and the
  endpoint-dependent generator `PathOver` derive from one whole functor path,
  and ordinary precomposition retains first hom action.
- `emdash3_2_walking_interval_extension.lp`: whole inverse candidate on
  WalkingArrow representations into `Path_cat(G)`. Interval recursion uses
  the two endpoint images and the selected generator; endpoint observations
  compute judgmentally, ordinary generator beta remains propositional, and
  the primitive whole owner retains first and next action.
- `emdash3_2_walking_interval_universality.lp`: rule-free whole
  mapping-object equivalence against every groupoidal target. Scoped
  categorical-HIT uniqueness supplies both whole cancellation paths and
  packages restriction as `OmegaEquivAlong Cat_cat`; point, endpoint,
  segment, and source-generator readings remain dependent projections. This
  is the completed non-endomorphism source-shape theorem reused by the generic
  recovery below.
- `emdash3_2_groupoidification_hit.lp`: category-indexed free
  groupoidification HIT. `Groupoidify(C) : Grpd` has one whole unit
  `C -> Path(Groupoidify(C))`; its recursor computes judgmentally at every
  represented source object and through `eq_apd` on every represented source
  arrow. Whole extension in the path-valued representation retains first and
  next hom action. This is formation/elimination, not source functoriality.
- `emdash3_2_groupoidification_universality.lp`: transparent whole
  restriction along the generic unit, scoped categorical-HIT beta/eta, and
  the resulting `OmegaEquivAlong Cat_cat` between groupoidal maps and
  path-valued functors for arbitrary `C : Cat` and `G : Grpd`. It declares no
  `Groupoidify_func` or adjunction.
- `emdash3_2_groupoidification_composition.lp`: rule-free explicit generic
  unit compositor for arbitrary composable arrows, recovered from the
  existing internal-action owner. The whole transformation retains one next
  action, and the compositor remains nonidentity even where historical strict
  cuts make its endpoints convertible.
- `emdash3_2_groupoidification_interval_recovery.lp`: derives mutually inverse
  maps between `Groupoidify(WalkingArrow_cat)` and `Interval_grpd` from the
  generic and completed Interval beta/eta laws. Both whole cancellations,
  pointwise quasi-inverse data, and a `TypeEquiv` are explicit; the two HIT
  classifiers are not definitionally identified.
- `emdash3_2_walking_circle_completion.lp`: transparent rule-free concrete
  comparison from WalkingEnd to Circle. It sends the directed generator and
  every Nat power to the Circle generator and its nonnegative powers, and the
  direct Circle encoder agrees with the route through WalkingEnd's Nat
  normal form. It is not a generic groupoidification reflector.
- `emdash3_2_walking_circle_restriction.lp`: transparent rule-free whole
  restriction of Circle functions along the comparison. Its stable
  precomposition owner retains first hom action; base evaluation and the
  generator `PathOver` are derived from one whole comparison.
- `emdash3_2_walking_circle_extension.lp`: whole inverse candidate on
  WalkingEnd representations into `Path_cat(G)`. Its single object rule
  computes to Circle recursion on the selected base and generator. Loop and
  first-arrow agreement remain propositional, while generic hom action stays
  iterable one dimension higher.
- `emdash3_2_walking_circle_universality.lp`: rule-free whole mapping-object
  equivalence. Two scoped categorical-HIT uniqueness paths make extension and
  restriction inverse as whole functors and package restriction as an
  `OmegaEquivAlong Cat_cat`. Dependent projections expose point and generator
  observations without adding a Circle loop rewrite.
- `emdash3_2_walking_circle_monodromy.lp`: rule-free universe-valued consumer.
  A self-equivalence supplies a univalence loop, the whole inverse builds the
  corresponding Circle family, restriction recovers the original WalkingEnd
  representation, and loop transport applies the equivalence's forward map.
  This is not a generic `Groupoidify` construction.
- `emdash3_2_groupoidal_closure.lp`: transparent rule-free representative
  closure for products. The canonical core-inclusion comparison is identity
  on objects and a split/join `TypeEquiv` on every hom carrier. Product path
  transport agrees with both sequential coordinate orders, the resulting
  diamond is coherent, and existing structured transport and `PathOut`
  induction agree with the same primitive right-`J` transport. No category-
  head rewrite, second `J`, proof-time unifier, or Gray tensor is introduced.
- `emdash3_2_path_pseudo_laxity.lp`: transparent rule-free Path realization
  of the generic normal-lax compositor. For `path_map_func(h)`, the existing
  `fapp1_compositor` is an equality between paths and `eq_sym` supplies its
  reverse. Its formal represented-action endpoints compare propositionally
  with the usual `eq_ap`/`eq_trans` formula, and its whole transformation
  retains a next-hom functor between paths-between-paths. The module adds no
  Path-specific runtime fold, proof-time rule, pseudofunctor classifier,
  inverse record, or complete coherence claim.
- `emdash3_2_gray_profiles.lp`: semantic `IsStrictFunctor` evidence, the exact
  `StrictFunctor(A,B) = Sigma(F,IsStrictFunctor(F))` package, its stable
  evidence-bearing ambient view, and the selected `GrayHom_lax`
  strict-object/lax-arrow profile. The property constrains the already
  extracted compositor by an endpoint path and equality-induced arrow; it
  adds no second functor grammar or compositor and does not reflect arbitrary
  evidence to literal identity. Homs and every higher action reuse the
  ambient `Transf_cat` tower. Historical global endpoint cuts remain pending
  a separate profile-local migration.
- `emdash3_2_walking_arrow.lp`: transparent walking-arrow interface derived
  from `Join_cat(Terminal_cat,Terminal_cat)`. Both endpoints, the generator,
  and its next hom action are projections of existing join owners.
- `emdash3_2_gray_right_closure.lp`: one profiled right-closed slice with an
  opaque `GrayTensor_R`, whole curry/uncurry maps paired with supplied
  `IsStrictFunctor` evidence, equality-valued beta/eta packaged by
  `OmegaEquivAlong Cat_cat`, and identity-derived coevaluation/evaluation. It
  does not claim the mirror closure or full Crans--Gray monoidal structure.
- `emdash3_2_gray_walking_square.lp`: transparent `I tensor I` boundary whose
  four vertices and both coordinate directions derive from coevaluation and
  the retained walking generator; no tensor object or arrow is postulated.
- `emdash3_2_gray_interchanger.lp`: rule-free directed interchanger. The named
  cell is the identity component of the active whole post/left laxity owner,
  its next `tapp1_func` action remains public, and the resulting direction
  confirms the `GrayHom_lax` convention. It adds no standalone square,
  endpoint bridge, rewrite, or unifier.
- `emdash3_2_gray_interchanger_orientation.lp` and
  `emdash3_2_gray_transformation_graph.lp`: the selected interchanger has
  checked direction `v o a ==> b o u`; exchanging the coordinate roles gives
  the native lax-square orientation. Every transformation yields an iterable
  stable whole functor `B -> LaxArrow_cat(C)`. Objects compute to component
  edges; capped arrows compute to the standard square with literal sides
  `F[g]` and `G[g]`, with filler extracted from the existing post/left internal
  action. Generic `fapp1_func` retains the next action. Its identity overlap
  with the historical global strict-functor cut is deliberately accepted
  pending the planned profile-local cut migration; the transparent
  represented-Sigma/opposite construction remains protected evidence.
- `emdash3_2_gray_cubes.lp`,
  `emdash3_2_gray_transformation_graph_profile.lp`,
  `emdash3_2_gray_cube_decoder.lp`, and
  `emdash3_2_gray_cube_dimension2.lp`: fixed-bracketing positive Gray cubes,
  their selected strict graph profile, and a genuine arbitrary-`n` object
  decoder. The predecessor index `n` denotes dimension `n+1`. Successor
  decoding curries, takes the walking generator, recursively decodes its graph
  in `LaxArrow`, and applies the Nat-derived level shift. For strict endpoint
  packages, the public graph is paired with supplied `IsStrictFunctor`
  evidence over its already-extracted compositor; carrier and evidence
  projections compute, and no graph-specific compositor or identity rule is
  added.
  Dimensions one through three, the exact `I tensor_R I`
  interchanger, four square edges, six cube faces, and retained next action are
  checked. No tensor unit, alternate-bracketing coherence, inverse decoder, or
  mapping-category equivalence is claimed.
- `emdash3_2_cubical_dependent_hom.lp`: transparent two-sided cross-corner
  dependent hom for `E : K1^op -> Catd(K2)`. It transports the source in the
  second coordinate and the target in the first, then forms one hom in the
  common fibre. Its identity-Hom instance computes to
  `Hom_{Hom_C(x1,y2)}(b o u,v o a)` and retains both side-arrow actions without
  a primitive square, rule, or unifier.
- `emdash3_2_cubical_square_total.lp`: fixed-vertical-boundary nested-Sigma
  total of `homdc_`. Square objects are `(a,(b,alpha))`; top, bottom, left, and
  right remain whole, and the next hom exposes the two endpoint squares plus
  four side faces. The fixed sides compute to identities and bottom remains a
  dependent section action. Its generic varying-Sigma projection now computes
  both point components and constructor-visible displayed arrow action,
  including pointwise opposite; it adds no cubical filler rule or unifier.
- `emdash3_2_cubical_internalization.lp`: transparent variance-correct whole
  cubical internalization. It forms the inner edge family by ordinary Sigma,
  takes its pointwise opposite, defines `homdc_int` as the existing
  `homd_int` of that family, and derives
  `homdc_total_cat = Op(Sigma(Op K1,D_E))`. Its `LaxArrow_cat` specialization,
  visible edge/square constructors, and whole source/target functors add no
  primitive category, square, two-sided Sigma, rule, or unifier.
- `emdash3_2_cubical_arrow.lp` and
  `emdash3_2_cubical_arrow_composition.lp`: compatibility/readability layer.
  `CubicalArrow_cat`, edge/square constructors, and source/target are
  transparent aliases of the derived lax-arrow theory. The older explicit
  identity and whisker/paste terms remain well typed, but their two competing
  runtime rules are retired; generic nested-Sigma identity/composition owns
  category structure and computes the expected endpoint boundaries.
- `emdash3_2_readable_pseudofunctors.lp` and
  `emdash3_2_cubical_arrow_functor.lp`: selected coherent lifting boundary.
  Transparent paths reframe the existing internal compositor to one readable
  post cell; the profile supplies fixed-forward `OmegaEquivAlong` for that
  cell, and the pre/right reverse adjustment is derived from a selected native
  inverse plus the existing endpoint comparison. The source ladder is a
  documented adapter for the temporary global strict-composition cut and does
  not claim noncollapsed lax endpoints.
  `CubicalArrow_func` maps a filler by that cell, generic next-hom action, then
  the derived reverse adjustment. Source, target, and every recursive lift
  retain profiles. A general constructor accepts an explicit family of
  fixed-forward omega-equivalence evidence; identity/composition and cubical
  structural instances remain honestly supplied pending extracted
  unit/composite coherence. Arbitrary normal-lax carriers are intentionally
  not lifted.
- `emdash3_2_cubical_square_level.lp` and `emdash3_2_cubical_levels.lp`:
  first six-face cube boundary and genuine Nat-indexed iteration. Level zero
  is `C`, successor is `CubicalArrow` of the previous level, and dimensions
  one through three classify edges, squares, and cubes. Four whole edge-face
  functors beside the two endpoint squares remain independently varying.
- `emdash3_2_semicubical_face_codes.lp` and
  `emdash3_2_semicubical_index.lp`: intrinsically indexed `{L,R,*}` words and
  the augmented semicube category. Raw substitution is structural; public
  codes are set-classified, Homs are discrete path categories, and visible
  identity/composition compute without a proof-time unifier.
- `emdash3_2_semicubical_face_action.lp`,
  `emdash3_2_semicubical_nerve.lp`, and
  `emdash3_2_semicubical_frames.lp`: variable-dimensional native restriction
  action, whole `SemiCubePlus_cat^op -> Cat_cat` nerve, and recursive `2n`
  boundary. `L/R` use source/target; star uses the profiled arrow lift. The
  nerve object beta computes, while its arrow observation is propositional to
  avoid competing with generic strict cuts. Restricted truncation supplies
  public composition laws; a finite family exposes new `L/R` followed by all
  star-lifted older faces.
- `emdash3_2_semicubical_representables.lp`: Yoneda standard semicubes and a
  whole arbitrary-`p,n` decoder from representable face codes to native
  restriction functors. The existing nerve-action path reaches the computing
  `{L,R,*}` action and another Hom action remains. `emdash3_2_cubical.lp` is
  the rule-free import facade for the resulting layer. Degeneracies,
  connections, Kan operations, and Gray/parameterized-hom comparisons remain
  future work.
- `emdash3_2_truncation_reflector.lp`: classified computational homotopy-
  truncation reflector. It realizes `NType_cat(n)` through the existing
  `TruncGrpdU(n)` retained-evidence package, supplies point-computing
  restricted induction and recursion, derives map identity/composition by
  that induction, and uses the existing `path_map_func` for its iterable whole
  Hom action.
- `emdash3_2_semisimplicial_face_codes.lp`: set-classified augmented
  semi-simplex face-map codes. A native indexed skip/keep family owns raw
  structural composition; its public 0-truncation supplies sethood while
  constructors, identities, and composition still compute through the
  existing restricted recursor. It adds no proof-time unifier, internal
  semi-simplex category, join realization, representable, sieve, or Kan
  claim.
- `emdash3_2_semisimplicial_index.lp`: internal augmented semi-simplex
  category. Objects compute to finite vertex counts and Homs to discrete path
  categories of face codes. Identity is the all-keep code; category
  composition reduces at visible public truncation points through
  `face_comp`, while arbitrary composition retains the generic owner. It adds
  no unifier, degeneracy, join realization, representable, sieve, or Kan
  claim.
- `emdash3_2_simplex_shapes.lp`: ordinary Nat-indexed simplex shapes, generic
  whole join-map action, strict-profile join inclusions/maps, and the selected
  five cofaces through dimension two. Its cross datum is the target join's
  existing cross cell reindexed along both inputs; code and whole-functor
  coface equations compute without an external naturality family. It adds no
  augmented-empty realization, arbitrary face decoder, degeneracy,
  representable, sieve, or Kan claim.
- `emdash3_2_coherent_nerve_levels.lp`: variable-dimension ordinal mapping
  categories `Functor_cat(DirectedSimplex_cat(n),C)`. Its separate augmented
  vertex-count shape is empty at zero and recovers the ordinary dimension
  shape at successor levels. Generic Functor/Transf hom action remains
  iterable; no face action, whole semisimplicial nerve, recursive dependent-
  cell bridge, rule, or unifier is added.
- `emdash3_2_tetrahedron_faces.lp`: four selected strict-profile triangle
  cofaces of the ordinal tetrahedron. All six shared edges compute through
  face-code composition. The three edges inside the old triangle also agree
  as composite whole functors; the three edges involving the newly joined
  vertex remain distinct whole-functor presentations pending generic
  join-map composition. It adds no rule, unifier, generic decoder, or top
  tetrahedral cell.
- `emdash3_2_join_mapping_recursion.lp`: first-stage whole observation and
  object-level extension for maps out of `Join_cat(A,B)`. The two branch
  restrictions retain generic transfor action, and the cross observation is
  derived internally from `Prof_func_hom`, reindexing, and
  `join_cross_transf`. The explicit `JoinMapObjectData` classifier records
  only objects; a Cat-valued total of mixed-variance coherent squares,
  action-derived-cross compatibility, and scoped join eta remain named
  prerequisites rather than hidden equations.
- `emdash3_2_face_realization.lp`: variable-dimension realization of every
  nonempty raw/public face code into a whole functor between join-built
  directed simplex shapes. `skip` computes by the left join inclusion and
  `keep` by `join_map_func`; a curated sethood witness for the finite raw
  syntax permits descent through public `FaceCode`. This is a generic decoder,
  not yet a functor on `SemiDeltaPlus_cat`: all-keep and the first new-vertex
  composite expose the still-missing scoped join identity/composition laws.
- `emdash3_2_dependent_simplex_bridge.lp`: transparent recursive triangle and
  tetrahedron presentation through the existing `homd_`/Sigma action. The
  fixed-endpoint triangle classifier exposes whole base-arrow and transported
  target-fibre-action functors. Their hom actions give two boundary readings
  while retaining another action; because the total endpoint is fixed, these
  are not by themselves the public `023` and `123` cofaces. Their product
  pairing is one whole fixed-endpoint boundary functor whose projections
  recover both components. The
  triangle map is exactly the first hom action of `Sigma(FF)`; its next hom
  action preserves a visible base cell and computes the dependent component
  through `fdapp1_int_hom_fapp0`, while retaining another hom action. The
  ordinary specialization recovers `fapp1_compositor`. No standalone higher
  cell, rule, unifier, `homd_con_int`, or whole nerve equivalence is added.
  The focused profile reviewer keeps the generic compositor noncollapsed,
  checks semantic `IsStrictFunctor` evidence at dimension two, and reads
  Path-valued triangle and tetrahedron components as invertible equalities;
  no parallel simplex classifier or unscoped higher strictness claim is made.
- `emdash3_2_dependent_simplex_path_associator.lp`: rule-free groupoidal
  source-coherence adapter for the recursive bridge. The ordinary generic
  compositor of `Rep_catd_func(Z)` is retained first as one whole displayed
  transformation; its component at a fourth object/arrow and its next hom
  action remain generic in `Z`. Typed stable-owner paths compare its formal
  endpoints with both raw bracketings for arbitrary `Z`, and equality-induced
  arrows conjugate the cell to a generic directed associator at those
  endpoints. For `Z = Path_cat(A)`, that cell exposes the readable orientation
  `(h o g) o f -> h o (g o f)`, and equality symmetry supplies inversion.
  The source check remains green with the global associativity unifier removed
  and `comp_assoc` opaque. No runtime rule, proof-time unifier, generic
  reassociation, proof-irrelevance principle, or equality with the separate
  direct-J proof is added.
- `emdash3_2_dependent_simplex_represented_source.lp`: rule-free
  constructor-visible source consumer for the recursive bridge. A three-edge
  Sigma spine retains its two raw bracketings; the generic represented cell
  projects to the native `(kappa,lambda)` dependent tetrahedron, and the
  existing whole next action preserves the base component, maps the fibre
  component through `fdapp1_int_hom_fapp0`, and retains another hom action.
  No Sigma eta, runtime rule, proof-time unifier, complete boundary telescope,
  or uniform code universe is added.
- `emdash3_2_dependent_simplex_native_dimensions.lp`: rule-free flagged native
  classifiers through dimension three. The tower starts with `C` and iterates
  `PathOut_cat` after fixing the initial vertex, edge, and triangle. The
  derived `pathout_map_func` and its iterations give whole ordinary-functor
  action and retain another hom action. Visible dimension-two and
  dimension-three constructors expose every edge/face and top dependent
  filler; the last represented source is moved to literal composition by
  typed equality-induced conjugation. It adds no global all-simplex category,
  variable dimension, ordinal equivalence, code grammar, rule, or unifier.
- `emdash3_2_dependent_simplex_dimension4.lp`: rule-free fourth flagged
  acceptance level. It adds one more `PathOut_cat`, derives whole map action,
  retains another hom action, and exposes faces 0124/0134 directly and 0234
  through the typed readable Hom(Sigma) split. Its remaining dependent frame
  contains face 1234 and the top filler; a durable full-constructor negative
  shows that recursively carried readable lower endpoints are required before
  flattening it. No eta, endpoint rewrite, rule, unifier, or global category
  of all simplices is added.
- `emdash3_2_dependent_simplex_codes.lp`: curated intrinsic flag codes indexed
  by ambient `C`, dimension `n`, and decoded category `K`. Zero is indexed by
  `C`; successor stores `x : Obj(K)` and is indexed by `PathOut_K(x)`. The
  public Sigma package decodes by category projection, selected codes recover
  native dimensions zero through four, existing `FaceCode` is reused for
  boundary references, and endpoint-view data retains formal/readable
  comparisons. It adds no generic Cat syntax, set quotient, mapped decoder,
  user inductive declaration facility, or proof-time unifier.
- `emdash3_2_dependent_simplex_code_map.lp`: functorial mapped decoding of
  intrinsic flag codes. It recursively returns a target code together with a
  whole functor between decoded categories; zero returns the supplied functor
  and successor reuses `pathout_map_func`. Selected codes compute to the
  existing native maps through dimension four, another hom action remains
  iterable, and endpoint views map through ordinary `eq_ap`. It adds no
  duplicate native-map rule, proof-time unifier, arbitrary category syntax,
  or face action.
- `emdash3_2_dependent_simplex_faces.lp`: variable-dimensional whole action of
  existing nonempty `FaceCode`s on intrinsic dependent-simplex codes. Skip
  selects a constant face of the fixed flag; `keep(skip ...)` composes the
  recursive target face with `Sigma_proj1_func`; `keep(keep ...)` reuses
  `pathout_map_func`. All three visible triangle edges compute, another hom
  action remains iterable, and selected public composition agrees on target
  codes and visible observations. Its whole target-line/base-line pair makes
  the native triangle category explicitly doubly fibred: ordinary endpoints
  are tetrahedron faces `012` and `013`, while the paired hom action exposes
  `023` and `123`. It adds no duplicate face syntax, broad functor-
  extensionality, whole-composition rewrite, or proof-time unifier.
- `emdash3_2_shaped_pathout.lp`: generic fixed-source realization of a shaped
  unit-profunctor cell as a whole `PathOut` functor. Its object action sends
  `(x,p)` to `(G[x],r[p])`, its next hom action remains at `fapp1_func`, and a
  rule-free first-class path compares stable Cat-valued precomposition with
  ordinary functor composition. The two fixed-source family comparisons are
  late proof-time rules; no hot evaluator rewrite or simplex-specific
  endpoint rule is added.
- `emdash3_2_pathout_transformation_reframing.lp`: rule-free source
  comparison for the outgoing-path lift of an ordinary transformation. It
  connects stable Sigma postcomposition to the formal pre/right
  internal-action source by composing existing typed paths through raw
  composition, general precomposition, the Cat-valued telescope, and whole
  Functord transport; it does not identify the lax endpoints.
- `emdash3_2_pathout_transformation_lift.lp`: generic whole successor on
  outgoing-path categories. At fixed source `x`, it lifts
  `epsilon : F => G`; the component over `(y,p)` is a Sigma arrow with base
  `epsilon[y]` and fibre the existing pre/right laxity cell. One
  constructor-visible component beta computes and generic `tapp1_func`
  remains available. No core edit, endpoint normalization, or unifier is
  added.
- `emdash3_2_ordinal_join_pathout_successor.lp`: generic identity-join
  successor for `A * 1`. It packages the observed/primitive shaped cross
  comparison as one transformation between outgoing-path maps at any fixed
  old object. The result is generic in `A` and immediately iterable through
  `pathout_transf_lift`; it adds no dimension-specific simplex data.
- `emdash3_2_dependent_simplex_ordinal_adequacy.lp`: relative
  ordinal/dependent comparison at the strongest current boundary. Dimension
  zero is a whole pointwise retraction; dimension one observes the walking
  arrow's endpoints and generator. Generic core join-eliminator point betas
  make the three restricted triangle edges share vertices. It retains the
  explicit-filler interface consumed by the constructive continuation and
  adds no global total, broad eta, or unifier.
- `emdash3_2_join_cross_compatibility.lp`: whole propositional
  higher-constructor beta relating the cross observed from a join extension to
  its primitive supplied cross. The equality-induced displayed transformation
  projects to endpoint and arbitrary shaped components and retains generic
  `tdapp1_int_cell` base-arrow action. It adds no runtime rule, opaque simplex
  filler, Cat-valued coherent-square total, broad join eta, or unifier.
- `emdash3_2_join_generator_compatibility.lp`: whole walking-generator
  refinement. A propositional component law for `Prof_reindex_transf` and a
  whole observation/ordinary-hom-action comparison combine with the existing
  extension cross beta to derive `join_map_generator_beta`. Equality-induced
  cells retain higher action; no runtime rule, independent generator axiom,
  or unifier is added.
- `emdash3_2_dependent_simplex_ordinal_filler.lp`: constructed ordinal
  dimension-two adequacy. One profiled source join-cross naturality cell is
  conjugated to the selected 02/12 edges, packaged as the existing native
  two-simplex, mapped by `dependent_simplex2_map(H)`, and projected to obtain
  `ordinal_dependent_simplex2_canonical_filler(H)`. The observation is
  unconditional and one next action remains public. Dimension four and a
  mapping-category equivalence remain separate work; no filler constant,
  rule, or unifier is added.
- `emdash3_2_dependent_simplex_ordinal_dimension3.lp`: constructive ordinal
  adequacy in dimension three. A shaped fixed-source `PathOut` map turns the
  whole join-cross comparison into two successive outgoing-path actions; the
  generic post/left laxity cell supplies their dependent top, which is paired
  with its native face-023 base to form one actual
  `DependentSimplex3_cat` source object. `dependent_simplex3_map(H)` maps that
  one source under arbitrary `H : Functor(Delta[3],C)`. Public projections
  expose faces 012, 013, 023, and 123, the top component, and another whole
  hom action. Wrong-endpoint and noncollapse reviewers are active. A Path
  target accepts the same recursive object; direct `eq_sym` remains available
  at the existing generic visible-Path-fibre profile rather than through a new
  nested-`PathOut` normalization. No opaque filler, runtime rule, or unifier is
  added.
- `emdash3_2_dependent_simplex_ordinal_dimension4.lp`: constructive ordinal
  adequacy in dimension four. Starting from the generic identity-join
  comparison for `Delta[3] * 1`, two `pathout_transf_lift` applications and
  one component evaluation construct a native fourth-level cell from the
  canonical source tetrahedron. The resulting source maps under every
  `H : Functor(Delta[4],C)`; five named coface codes use the existing generic
  face action, while native projections retain the recursive readable frame
  and top component. Strict/Path profiles, wrong-endpoint rejection,
  noncollapse, and another action are checked. No opaque filler, endpoint
  rule, broad eta, or unifier is added.
- `emdash3_2_dependent_simplex_ordinal_recursive.lp`: Nat-indexed canonical
  ordinal-source construction. `OrdinalJoinLiftStage` folds a nonzero raw
  intrinsic flag code into a target code, two whole maps, and their
  transformation. The one-flag clause is the generic identity-join
  comparison; each later flag applies `pathout_transf_lift`. The zero/nonzero
  successor rules construct `step(d,F[s])` with source `(G[s],epsilon[s])`,
  and `nat_elim` produces `ordinal_dependent_simplex_source(n)`. Arbitrary
  mapping and faces reuse the existing code-map and face owners. Dimensions
  zero through four, wrong-index rejection, noncollapse, and retained action
  are checked; no parallel code grammar or unifier is added.
- `emdash3_2_prof_reindex_terminal_normalization.lp`: generic whole
  normalization of the terminal-right action in a reindexed unit profunctor.
  An explicit path `G[id_*]=id` supports both the retained whole family path
  and a directed source comparison whose component computes to the existing
  rigid two-endpoint Hom action. The associated displayed normalizer has one
  computational fibre projection and retains `functord_laxity_transf` and all
  subsequent hom action. The two narrowly guarded projection rules add no
  ordinal dimension, face-specific conversion, filler, or proof-time unifier.
- `emdash3_2_semisimplicial_diagrams.lp`: standard Yoneda semisimplices,
  groupoid-valued semisimplicial diagrams, and their levelwise path-category
  realization. Whole postcomposition remains at the raw functor-category
  owner; realized objects and maps pass through the distinct public
  `Psh_cat` projections. It adds no rule, unifier, representability claim for
  arbitrary diagrams, boundary, horn, or Kan data.
- `emdash3_2_simplex2_sieves.lp`: boundary and three horns of the standard
  two-simplex. Three omission bits compute from raw face codes and descend
  through set truncation; one kind-indexed higher-sieve owner retains generic
  action, ordinary pullback, fibrewise extension, and whole inclusion. It
  adds no generic-dimensional sieve family, degeneracy, spine, Kan condition,
  or filler.
- `emdash3_2_path_groupoid_2horn_fillers.lp`: bounded algebraic 2-nerve of a
  path groupoid. Its three horn restrictions and fillers use path
  composition/inverses, J-derived cancellation, whole function section paths,
  and iterable Path-map lifts. It also exposes generic presheaf-facing horn
  restriction, but does not identify the algebraic carriers with full mapping
  categories or claim an all-dimensional nerve/Kan theorem.
- `emdash3_2_semisimplicial_decalage.lp`: categorical decalage through the
  vertex-appending endofunctor of the internal semi-simplex category. Whole
  base and cone-tip transformations retain generic naturality; presheaf
  restriction shifts levels, and a fixed-tip levelwise `HFiber` has an
  iterable Path-map to its opposite base. A varying-`HFiber` Catd/total
  Path-family owner is not yet active, so no whole displayed semisimplicial
  object or `homd_` comparison is claimed.
- `emdash3_2_circle_connectedness.lp`: transparent rule-free propositional-
  truncation consumer. It constructs
  `Pi x:S1, ||circle_base=x||_{-1}` by dependent Circle induction; the retained
  proposition evidence supplies the generating-loop `PathOver`, so the result
  proves mere connectedness without choosing an untruncated global based path.
  Restricted elimination first turns each merely inhabited based-path fibre
  into a path in `Trunc_grpd(0,Circle_grpd)` and then contracts every point of
  that set truncation. The resulting `IsContr` evidence does not rewrite the
  carrier to `Unit_grpd`. The exact current cross-module health boundary is
  recorded in the validation section below; the focused plans retain their
  historical warning, rule-audit, catalog, and snapshot evidence.
- `emdash3_2_checks.lp`: executable diagnostics and regressions.
- `EMDASH_FOUNDATIONS.md`: mathematical reading guide.
- `REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`: notation
  authority for comments, examples, and future parser work.
- `INDEX.md`: active plans, completed decision records, audits, and generated
  reports.
- `../../docs/TYPESCRIPT_ELABORATOR_V3_2_MASTER_PLAN.md`: active cross-layer
  implementation ledger for the TypeScript elaborator/candidate product
  kernel. It is subordinate to these mathematical sources for every active
  owner and rule.
- `../../docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`: repository-wide
  checkpoint and recovery workflow for explicitly authorized long-running
  implementation goals. It does not relax this SOP.
- `../book/book.json` and `../book/evidence.json`: book source
  ordering/metadata and prose-to-check traceability. They govern the book
  artifact but never override active Lambdapi declarations.
- `REPORT_EMDASH_V3_2_FUNCTORIAL_TYPE_THEORY_BOOK_ARCHITECTURE_PLAN_2026-07-20.md`:
  completed book architecture and implementation ledger.
- `../../docs/EMDASH_BOOK_V3_2_GROUPOIDAL_REALIZATION_EXPANSION_PLAN_2026-08-18.md`:
  completed fourth-spiral book/article and local-release ledger.
- `../../docs/EMDASH_BOOK_AND_ARTICLE_DEPENDENT_SIMPLEX_EXPANSION_PLAN_2026-08-21.md`:
  completed fifth-spiral book/article ledger and corrected `0.6.1-dev`
  publication record.
- `../../docs/EMDASH_BOOK_V3_2_CARTESIAN_AND_INDEXED_STRUCTURE_EXPANSION_PLAN_2026-08-29.md`:
  completed sixth-spiral book ledger for adjunction-generated monads, finite
  cartesian structure, slice base change, and `Sigma_u |- u* |- Pi_u`. It owns
  the locally promoted 374-page draft `0.7.0-dev` release and its deterministic
  PDF/visual gate; no remote publication occurred.
- `REPORT_EMDASH_V3_2_FOUNDATIONAL_DOCUMENTATION_SOP_AND_REGISTRY_MAINTENANCE_PLAN_2026-08-30.md`:
  completed corrective authority/registry maintenance ledger for the
  integrated `0e61a79` baseline. It changes no Lambdapi semantics and excludes
  the in-flight global strictness migration.
- `REPORT_EMDASH_V3_2_AUTONOMOUS_MAINTENANCE_AND_EVOLUTION_PLAN_2026-07-22.md`:
  completed reusable predecessor ledger for cross-project maintenance,
  triage, and evolution. The 2026-08-30 child above owns the current reopen.
- `REPORT_EMDASH_CHECK_CATALOG.md`: generated map of the diagnostic suite.
- `REPORT_EMDASH_HEALTH.md`: generated source metrics and bounded timings.

The active source outranks every report if they disagree. Correct the report
as part of the same maintenance task rather than preserving a known stale
description.

Ignored `.scratchpad/` material is historical recovery data, not a normal
authority. Use the v2 retirement audit when an obsolete-baseline summary is
needed.

## Validated Current Baseline

Current source counts and check-content identity are generated in
[the health report](REPORT_EMDASH_HEALTH.md); diagnostic coverage is indexed in
[the check catalogue](REPORT_EMDASH_CHECK_CATALOG.md). A source-only health
refresh does not assert fresh checking of every registered target.

The consolidation ledger records the exact affected checks: complete native
nonsplit LES/snake workflow replays with 94 emitted assertions, focused
retirement/import controls, categorical-interface reviewers, and the final
identity-projection nucleus check. Keep source and resource identities with
those receipts. Do not turn their scoped results into a repository-wide
consistency or normalization claim.

The unsuffixed equality-valued interfaces remain the sole native API. The old
D0/D1 and decoder compatibility layers are retired. Their older qualification
narrative is retained in the history report rather than presented as today's
validation totals.

## Historical Checkpoint Appendix

The full dated appendix is preserved in the
[consolidated history](REPORT_EMDASH_V3_2_CONSOLIDATED_HISTORY_2026-09-16.md#earlier-checkpoint-appendix).
It records earlier measurements and rejected candidates. New receipts belong
in the active task ledger; current architecture follows below.

## Current Architecture

### Sections 0–3: kernel foundations

The kernel begins with the groupoid/type universe, equality/path induction,
encoded Sigma/Pi/product object layers, and the core category interface.

Active equality/equivalence staging includes:

- decoded elementary H0 classifiers `Empty_grpd`, `Unit_grpd`, `Bool_grpd`,
  and `Nat_grpd`, with native Empty/Unit/Bool/Nat carriers, dependent
  eliminator facades, constructor beta, and a Bool conversion-level
  anti-collapse diagnostic; visible Unit, Boolean, and Nat constructor
  equality additionally compute to Unit, Empty, or predecessor equality while
  generic `eq_refl` retains runtime provenance and open endpoints retain
  primitive equality. Generic J repeats its category and endpoint as
  subject-reduction guards, so a foreign/component proof with the same reduced
  classifier cannot trigger reflexive computation. Remaining elementary
  observational identity, broader no-confusion, higher action for other
  formers, canonicity, and categorical universal properties remain separate.
  The transparent `nat_succ_ind_eqr` facade routes successor-indexed motives
  through predecessor J and computes only at component reflexivity; outer
  reflexivity and open predecessor paths keep their existing runtime
  boundaries. `NatSucc_func` is the ordinary canonical successor functor. The
  comparison-only selected-action basis and its two proof-time rules are
  retired. The isolated Sum former/action experiment is absent pending a
  future consumer-led redesign;
- `Path_cat_func`/`path_map_func` own the canonical iterable action of every
  raw groupoid function: the capped action computes to `eq_ap`, while the
  generic `fapp*` calculus retains every higher action. This is the sole
  nondependent action interface; there is no selected-action registry or
  parallel first-path channel. Canonical nested versus composite action
  remains related propositionally by `eq_ap_comp` where it is not
  judgmentally identical. `PathOut` is a distinct structured groupoidal-J
  owner consuming an already functorial `Catd` motive.
  `path_record_witness_action` uses direct `eq_apd`; any genuine iterable
  dependent replacement is a displayed-functor/section problem;
- the named dependent `PathRecord_grpd(A)` representative, implemented by a
  parametrized one-constructor native carrier with direct source, target, and
  dependent witness projections plus a generated-induction facade; its active
  observational path view, stable shaped reflexivity, projection betas, and
  reflexive specialized J are described below, while runtime record eta,
  arbitrary structural action, and additional arbitrary-constructor J remain
  deliberately absent;
- native `TruncLevel` codes beginning at -2, recursive
  `IsTruncGrpd(n,A)`, and transparent proposition/set/ordinary-groupoid views;
  the successor equation makes equality lowering computational, while the
  decoder-owned ordinary `TypeEquiv` invariance package transports truncation
  evidence in both directions and computes on reflexivity;
- the named one-constructor package `TruncGrpdU(n)`, with computing carrier
  and retained-evidence projections and the aliases `PropU_grpd`,
  `SetU_grpd`, and `GroupoidU_grpd`; carrier/evidence path views, carrier-path
  reconstruction, propositional inverse laws, and the resulting path
  `TypeEquiv` are active; composing with the canonical ambient decoder gives
  restricted equivalence between package equality and carrier `TypeEquiv`,
  while no package eta, proof erasure, or same-level universe theorem is
  selected; `is_trunc_type_equiv` and `is_trunc_grpd_universe` prove the
  expected successor universe level through this restricted equivalence;
- truncation monotonicity, evidence property-valuedness, arbitrary-level
  dependent-Pi closure, and same-level dependent-Sigma closure are active;
  restricted package univalence and the expected universe-level truncation
  theorem are active; truncation reflectors and the representation prerequisite
  for recursive omega-equivalence evidence remain separately statused;
  general `TypeEquiv` invariance and its fixed-map categorical object consumer
  are active;
- `TypeEquiv` with forward/inverse maps and inverse paths, plus identity,
  symmetry, and categorical-order composition with derived `IsEquivMap`
  closure evidence;
- the finite `GrpdPathView(A,B)` universe identity view, with canonical
  reflexivity, decoder-owned encode/decode, propositional inverse laws and
  transport agreement, Product/Pi/Sigma consumers, and no direct public
  universe-equality rule or duplicated univalence body;
- direct rigid Cat/Grpd universe identity to the native
  `OmegaEquiv` facade, with retained generic-reflexivity provenance and
  explicit packages for observer computation. The D0-backed `CatPathView`,
  decoder round trips, Product action, and D0b next-hom package are retired,
  not alternate library interfaces;
- path views for encoded Sigma and Pi types;
- arbitrary propositional Sigma path encode/decode round trips and transparent
  named PathRecord round trips, with constructor-reflexive computation and no
  open runtime eta;
- ordinary `PiHapply`/`PiFunext` over the related-input Pi view, with
  pointwise runtime beta, generic-J propositional eta, an explicitly
  classified proof-time reflexive basis, and contractible-fibre
  `pi_happly_type_equiv`; arbitrary structured-Pi J computation and
  computational fibrancy remain separate;
- the repaired path-category composition boundary: generic `comp_fapp0` owns
  runtime composition, two narrow `eq_refl` unit bridges join both projection
  orders, and `path_comp_eq_trans` proves J-derived propositional agreement;
  `Op_cat(Path_cat(A))` remains a genuine opposite head, while the oriented
  post/pre action heads retain distinct runtime forms and compare with shared
  composition only at proof time; `Path_sym_func(A)` owns path reversal from
  the genuine opposite, generic functoriality owns anti-composition, and
  `path_sym_agrees_eq_sym`, `path_sym_invol`, and
  `path_sym_core_incl_agreement` provide propositional coherence without open
  runtime folds;
- the first Path-realized pseudo-laxity consumer: the formal whole source and
  target remain the generic `functord_transport_*_func` owners,
  `path_map_compositor_path` is the existing `fapp1_compositor` decoded as an
  equality between paths, and `path_map_compositor_inverse` is its `eq_sym`.
  A named two-step propositional comparison—generic represented
  postcomposition to shared composition, then `path_comp_eq_trans`—gives the
  readable `eq_ap`/`eq_trans` endpoints without making them runtime-convertible.
  `path_map_compositor_higher_func` retains one off-diagonal next-hom action as
  a whole functor and therefore leaves generic higher iteration available;
- a semantic strict-object/lax-arrow Gray profile and one right-closed
  consumer: `IsStrictFunctor` constrains the existing compositor,
  `StrictFunctor` is its exact carrier/evidence Sigma package, and the stable
  `strict_functor` view selects the strict object boundary without duplicating
  the ambient action hierarchy; `GrayHom_lax` reuses `Transf_cat` homs;
  `GrayTensor_R` has whole curry/uncurry maps paired with supplied strictness
  evidence and equality-valued beta/eta; `WalkingArrow_cat` is
  transparently `Join_cat(1,1)`; and the four-object walking square and its
  nonidentity directed interchanger derive from coevaluation and the existing
  whole post/left laxity owner. `gray_interchanger_next_func` retains one next
  action. The raw boundary composites are readable presentations, not a new
  endpoint normal form. Mirror closure, full monoidal coherence, and migration
  of the historical global strict cuts remain outside this tranche;
- `GrpdUnivalence` and decoder-based groupoid-univalence capabilities, with
  named decoder round trips, a canonical contractible-fibre capability
  selecting `grpd_equiv_path`, a propositional decoder transport square, and
  a Pi-universe action consumer; arbitrary legacy `ua_grpd` agreement and
  direct universe identity remain absent;
- `IsoEvidence` for ordinary categorical isomorphism data;
- the general `CatIsoUnivalence` capability type with no global kernel
  inhabitant, ordinary `idtoiso_cat`, and the direct native ordinary-iso lift
  `iso_evidence_omega_along`/`iso_evidence_omega_equiv`;
- native fixed-map categorical object-path/object-`TypeEquiv` construction and
  object-truncation invariance through
  `omega_equiv_along_obj_path` and
  `is_obj_trunc_cat_equiv_type_equiv`. Explicit native reflexivity retains
  its stable facade/package provenance rather than collapsing to a raw path;
- no D0/D0b/D1 compatibility module, decoder facade, reverse alias, or
  self-only compatibility example. Unsuffixed omega-equivalence names denote
  the native equality-valued representation exclusively;
- exact `IsDiscreteCat` Product data with native groupoidality, plus native-
  extension-owned core homwise evidence, `hom_to_path`, both coherent round
  trips, and a recursive cell consumer.
- independent object truncation, native directed-dimension codes, recursive
  `IsNCat`, evidence-retaining `NCat`/`ZeroCat`/`OneCat` packages, and a
  `OneCat` next-hom core-adequacy consumer. The obsolete conditional D0
  evidence-property/object-truncation experiment is retired. The downstream
  native equality-valued module proves unrestricted fixed-arrow
  evidence property, arbitrary truncation under retractions, and unconditional
  finite-`NCat` object truncation with computing base/successor equations. The
  one-way native ordinary-iso lift is active. The compatibility-scoped decoder
  round trips, selected-inverse comparison, reconstruction, and named OneCat
  `TypeEquiv` are retired; a fully native two-sided analogue is optional future
  work rather than a formation or cleanup dependency.
- direct canonical nondependent action through `path_map_func`, with dependent
  witness-field transport through `eq_apd` and no additional
  arbitrary-constructor J.

These are explicit kernel interfaces and checked computation skeletons. They
do not claim that every future univalence/coherence theorem is already
internalized.

### Finite dependent-record convention

Ordinary finite named structures use a parametrized one-constructor native
inductive carrier when later fields depend on earlier ones. A decoded
`*_grpd` classifier owns the public type; named projections are manual semantic
symbols with constructor beta rules, and public projection/eliminator
signatures retain the decoded classifier rather than exposing only the raw
carrier. Use the generated dependent induction principle directly or through
a thin reviewed facade when its raw parameter/motive surface is inconvenient.

Projection rules infer non-discriminating inductive parameters as `_` when
subject reduction and the strict LHS audit permit. Do not add runtime record
eta by default. A small map-plus-property existential may remain an encoded
Sigma; a structure with several stable field names or downstream structural
equality uses the record convention. The active `PathRecord_grpd` is the
executable representative: its original formation/elimination owner-position
and nested-Sigma comparison are warning-neutral, while the record supplies
direct named access and a direct three-field eliminator instead of nested
`sigma_Fst`/`sigma_Snd` chains. This decision is about the public API and
equality telescope, not a claim that nested Sigma is computationally invalid.

### Shaped PathRecord equality

`PathRecordPathView(A,r,s)` reads the named record structurally as
`Σ src : A, Σ dst : A, src = dst` and reuses the existing dependent Sigma
path view. The public equality rule for `PathRecord_grpd(A)` exposes that view
directly. `PathRecordPathRefl(A,r)` is the stable runtime reflexivity head;
`path_record_path_src` and `path_record_path_tail` expose its source and
dependent-tail components. Their beta clauses are ordered separately because
the tail result is indexed by the already-reduced source component.

The generic `ind_eqr` owner remains available for every equality. One narrow
former-specific clause restores its literal-reflexivity beta after record
reflexivity has reduced to the stable head. The same closed-registry policy is
used for generic consumers whose literal `eq_refl` pattern would otherwise be
erased: shared path units, `Path_sym_func`, `Core_incl_func`, `idtoiso_cat`,
and `idtoequiv_cat`. Do not extend this registry mechanically. Inventory a
real literal-reflexivity consumer, place the candidate at its owner, and test
both reduction orders and warning families. In particular, the active slice
does not make raw `sigma_path_refl` compute through J or PathSym; those steps
still depend on structural action and the separate fibrancy/dependent-J
architecture.

### Structural Sigma and PathRecord round trips

`sigma_path_decode_encode(p)` and `sigma_path_encode_decode(w)` prove the two
arbitrary path-characterization composites propositionally through generic J.
They are not open runtime eta rules. Constructor-exposed reflexivity computes
through the existing Sigma eliminator. Keep
`sigma_path_encode_decode_eq_refl` as the literal-reflexivity J base rather
than trying to reuse the stable `sigma_path_refl` theorem inside the nested
decode term: current proof-time unification does not propagate that comparison
transitively.

`PathRecord` needs no second Sigma normalization because its public equality
already reduces to `PathRecordPathView`. Its public encode/decode names are
transparent identity views, so both named round trips, shaped reflexivity, and
the dependent-tail observer compute directly and iterate through a nested
record. Preserve this distinction. Do not infer global eta, arbitrary
structural action, fibrancy, or additional structured-J computation from the
round-trip surface.

### Pi happly/funext equivalence

`PiPointwisePath(A,B,f,g)` is the diagonal family `Π x:A, f(x)=g(x)`.
`PiHapply(p)` observes a `PiPathView` path at `(x,x,refl_x)`, and
`PiFunext(h)` reconstructs its arbitrary related-input action by `ind_eqr` on
the base path. Point application of `PiHapply(PiFunext(h))` reduces to `h(x)`;
the whole functions do not receive a second eta-like runtime rule.

`pi_funext_eta(p)` derives `PiFunext(PiHapply(p))=p` with retained generic J.
Its reflexive base uses one two-rigid-head proof-time equation. Classify this
as a generic semantically justified structural law: the transparent lambda
presentation computes to the same reflexive term, whereas typed `eq_refl`
only confirms that the stable-head rule fires. Keep a conversion-negative
check and an arbitrary structured-Pi J negative check whenever this owner is
changed.

`pi_happly_by_inverse` supplies both propositional round trips explicitly.
The transparent theorem `is_equiv_map_by_inverse` converts such data into the
active contractible-fibre `IsEquivMap`. It constructs the contraction through
left-oriented J and half-adjoint coherence, then re-centres it at
`(g(b),right(b))`. This makes `type_equiv_from` and `type_equiv_right` compute
for `pi_happly_type_equiv`, while the contraction path remains propositional
and does not duplicate `pi_funext_eta`. Do not infer a generic runtime eta,
arbitrary structured J, or fibrancy from this package.

### Ordinary TypeEquiv algebra

`type_equiv_refl(A)`, `type_equiv_sym(e)`, and
`type_equiv_comp(eBC,eAB)` form the ordinary identity/inverse/composition
surface. Composition is in categorical order: its forward map is
`eBC.to(eAB.to(a))`. Symmetry and composition construct explicit
`EquivByInverse` values from `type_equiv_left`/`type_equiv_right` and route
their contractible-fibre evidence through `is_equiv_map_by_inverse`.

Keep these public packages transparent. Their forward maps and the generic
theorem's selected fibre centre make the inverse and right-path projections
compute without extra rules. The contraction proof is transparent but remains
propositional structure, so the derived left projection is only typed, not
identified by conversion with the separately constructed inverse law. Unit
and associativity compute on forward maps; do not promote package eta,
double-symmetry cancellation, or univalence-decoder coherence into this owner.

### Groupoid decoder coherence

`grpd_univalence_by_decoder(A,B)` is the proof authority for the two named
round trips `grpd_equiv_path_idtoequiv` and
`idtoequiv_grpd_equiv_path`. `grpd_univalence_from_decoder` converts that
specified-inverse package to the contractible-fibre `GrpdUnivalence` surface.
Its selected inverse, `grpd_univalence_selected_path`, computes to
`grpd_equiv_path`; this is the canonical capability agreement. Do not infer or
postulate the same agreement for an arbitrary legacy `ua_grpd(U,e)`.

`coe_grpd_idtoequiv` is generic-J transport coherence. Compose it with the
decoder right round trip to obtain the propositional
`grpd_equiv_path_coe(e,a)` square; `grpd_equiv_path_pi_action` is its first
pointwise Pi-universe consumer. Keep this square propositional until each
constructor path has a joining transport owner. The measured broad runtime
orientation competes with Product decoding: decoder-first produces
`coe(product_grpd_path(...))`, for which no component transport rule exists.
Do not promote that fold or disguise the missing Product branch with a
proof-time equation.

The category universe satisfies the directed-universe principle:

```text
Obj(Cat_cat) = Cat
Hom_cat Cat_cat A B = Functor_cat A B.
```

`Catd_cat K`, `Functord_cat`, and `Transfd_cat` are stable displayed facades
for the ordinary Cat-valued functor, transfor, and next-hom presentations.
Their category equalities are proof-time comparisons. Runtime computation
crosses the boundary through documented `Obj` and `Hom_cat` projections, so
neither ordinary nor displayed category heads are erased prematurely.

Generic identity, composition, functor action, and naturality are owned by the
global `id`, `comp_fapp0`, `fapp*`, and `tapp*` calculus. Specialized
`id_func`, `id_funcd`, `id_transfd`, `comp_cat_fapp0`, and
`comp_catd_fapp0` spellings are transparent public views or specialization
surfaces, not parallel owners. No separate ordinary `id_transf` constructor
exists.

### Section 4: ordinary internal hom and variance-separated actions

The represented covariant family is:

```text
hom_(F,W)[y] = Hom_A(W,F[y]).
```

Its postcomposition action is owned by the `hom_postcomp_*` hierarchy:

```text
(F[p])_*(g) = F[p] o g.
```

The represented contravariant family is primitive:

```text
hom_con(W,F)[y] = Hom_A(F[y],W).
```

Its precomposition action is owned by `hom_precomp_along_*`:

```text
(F[p])^*(h) = h o F[p].
```

`hom_int(F)` internalizes the represented source object; `hom_con_int(F)` is
the target-internalized mirror. Both expose their off-diagonal actions through
the rigid two-endpoint hom action:

```text
Hom_func(g,f)[h] = Hom_fapp0(g,f,h) = f o h o g.
```

Runtime normalization preserves the postcomposition, precomposition, and
rigid-`Hom` provenance. Opposite/identity presentations, independently
factored pre/post cuts, and one-inactive-endpoint degenerations are related by
narrow two-rigid-head `unif_rule`s. They are not global runtime folds.

Section 7f retains stable ordinary target-internalized action owners.
`tapp1_con_int_fapp0_transf(epsilon)` and its identity-specialized
`fapp1_con_int_transf(F)` compare proof-time with the ordinary action of
`Op_transf(epsilon)` and `Op_func(F)`. Their fixed-target projections are
also stable. In particular,

```text
tapp1_con_at_transf(epsilon,Y)
  : Hom_A(-,Y) => Hom_B(F[-],G[Y])
```

computes at `X` to `tapp1_func(epsilon,X,Y)`. The identity-specialized owners
are `fapp1_con_int_transf(F)` and `fapp1_con_at_transf(F,Y)`. Whole projection
and identity specialization compute within this four-owner ladder. The
opposite comparisons are four constraint-style unifiers, not runtime
orientation of one variance into the other. Applying the
active whole displayed laxity extractor to this fixed-target transfor yields
the pre/right witness through `fdapp1_int_cell`; no independent ordinary
naturality square is postulated. A functor varying higher arrows between
`epsilon`s remains consumer-gated.

The source-only owner change is selectively ported from `20c6dd2e`, without
its gray-profile classifier changes or the parallel strictness migration.
The new reviewer `examples/contravariant_action_owners.lp` checks all four
proof-time bridges, runtime observations/identities, retained next action and
noncollapse. The dependent `homd_con_*` / `fdapp1_con_*` / `tdapp1_con_*`
inventory and current homology consumer remain in the living variance audit.

Section 18zz now packages both ordinary variance directions without adding a
second coherence calculus:

```text
tapp1_post_laxity_transf(epsilon,X,g)
  : G[g] o epsilon[-] ==> epsilon[g o -]

tapp1_pre_laxity_transf(epsilon,Y,h)
  : epsilon[-] o F[h] ==> epsilon[- o h].
```

The capped `tapp1_post_laxity_cell` and `tapp1_pre_laxity_cell` unfold through
`tapp0_fapp0` to the corresponding `fdapp1_int_cell`. The transparent
`fapp1_compositor(F,g,f)` is the post/left component of the identity transfor,
so it reads `F[g] o F[f] ==> F[g o f]` while retaining the same internal-action
source. Their formal endpoint types stay at the two
`functord_transport_*_func` owners. Readable raw-composition endpoints are
already connected by the existing whole strict-naturality paths; do not add a
duplicate pointwise pre/post unification rule merely to restate them.

`Hom_tele_func`, `Hom_func`, and `Hom_fapp0` retain focused runtime identity
and composition joins because projection can hide the literal generic
functor-action pattern.

`DefIso(C,x,y)` is the computational isomorphism package whose inverse cuts
cancel under the stable hom-action owner. `IsoEvidence` is its ordinary
propositional view.

### Sections 5–7: products, transfors, curry, and adjunctions

`emdash3_2_terminal_category_profile.lp` constructs the literal terminal
category's discrete/ordinary profiles, retaining an explicit inverse to its
core inclusion. Its ground proof-time id₁/constant-point view is an explicit
terminal eta extension, not a global functor or terminal-arrow eta rewrite.
`emdash3_2_one_cat_terminal_adjunction_families.lp` defines ordinary whole
terminal/initial comparisons directly from an Adjunction witness, with the
closed terminal profile used internally. Its optional whole arrow presentation
retains an existing selected embedding. Results use actual maps/inverses and
proved IsoEvidence laws. Production kernel/cokernel zero-column mate inputs
use these derived maps and categorical endpoint observations. All remaining
family-normalizer users are migrated: selected-choice adapters use the primary
interface, canonical family inputs use original-D reconstruction directly,
and ordinary uniqueness is a downstream observation of the actual modification.
The two former primitive DefIso normalizers and their sixteen rules are
retired. The ordinary adjunction providers and diagram reconstruction remain
explicit structural declarations; IsoEvidence laws add no runtime inverse cuts.

Generic whole diagram reflection, reconstruction and invertible-modification
action have independent owners in `one_cat_diagram_family_reflection`,
`one_cat_diagram_family_reconstruction` and `one_cat_arrow_family_isomorphisms`.
The three relocated observations retain their exact signatures and bodies.
These derived modules introduce no new universal structure primitive.

The literal terminal-target transformation category computes to Terminal_cat:
`Transf_cat(A,Terminal_cat,F,G) ↪ Terminal_cat`. The ordinary functor-category
Hom rule and iterated terminal Hom rule expose the same result. Original
functor objects and arbitrary nonterminal targets retain their existing
owners. The focused `terminal_target_transformations` reviewer includes the
whole Hom comparison of a lifted terminal adjunction and both inverse cuts.

The product architecture includes:

- `Product_cat`, componentwise homs, projections, pairing, and symmetry;
- product-valued functor/transfor projection ladders;
- `Product_cat_func` for internalized product formation;
- `Product_map_func` for componentwise endpoint maps;
- `Eval_func`, fixed-object evaluation, semantic curry, and semantic uncurry;
- ordinary weakening, exchange, and contraction packages;
- an indexed `Adjunction(F,G)` relation with transparent left/right
  compatibility views, stable unit/counit observations, both component-level
  triangle cut-elimination laws, opposite-index swapping, and mate consumers.

The additive monad layer follows the same indexed-observation boundary. For
`M : Monad(T)`, `unit_monad_transf(M)` and `mult_monad_transf(M)` are stable
whole transformations. `kleisli_extend_func(M,X,Y)` retains hom action. Its
point projection and ordinary ambient composition compute as

```text
g* o eta^c(f) -> g o f
g* o f*       -> (g* o f)*
(eta_X)*      -> id_TX
mu_X          -> (id_TX)*.
```

The second rule is the exact monadic dual of Došen's
`Delta(f2) o Delta(f1) -> Delta(f2 o Delta(f1))`. Došen's separately defined
delta/Kleisli composition is not the §5.8.3 ambient normalization owner.
Accordingly `kleisli_cut_func` and `kleisli_cut_fapp0` are transparent views of
`g* o f`, not primitive heads.

The evidence classifier remains transparently
`Comonad_A(D)=Monad_(A^op)(D^op)`. Opposite normalization can erase heads that
runtime laws must discriminate on, but this justifies only a narrow
computational mirror, not a duplicate comonad theory. Stable dual heads are
retained for counit, comultiplication, and point coextension because those
exact heads occur in active triangular rewrite LHSs. Whole coextension does
not occur in such an LHS and is transparently the endpoint-swapped primary
monadic whole extension. Generic `fapp0` projection followed by the surviving
`Op_func(D)` point fold reaches the stable point, while primary whole higher
action remains available. There is no whole coextension unifier or opaque
duality equality evidence. Ambient composition computes

```text
epsilon^a(f2) o Delta(f1) -> f2 o f1
Delta(f2) o Delta(f1)     -> Delta(f2 o Delta(f1)).
```

Coextension of the standard counit is identity, and standard
comultiplication compiles to coextension of `id_DX`. Co-Kleisli cut is also
transparent derived notation.

For the adjunction-induced witness, the formal/computational Monad layer and
the source adjunction spelling now follow the established usability boundary.
Canonical `unit_monad_transf(adjunction_monad(J))` remains available to the
generic triangular runtime rules. The adjunction unit is related to it by one
SOP-minimal proof-time agreement and remains runtime-nonconvertible. Whole
`mult_monad_transf(adjunction_monad(J))` is instead semantic: it reduces to the
transparent checked `G epsilon F` construction. Its component-first branch
uses the generic compilation into triangular extension; a non-axiomatic path
propositionally joins that endpoint with the whole-first semantic component
without changing runtime preference. This is a direct Lambdapi correction;
TypeScript usability automation remains deferred. Both unit-agreement
orientations, canonical beta/unit-extension, transparent multiplication
projection, the component path, and raw unit/name nonclaims are executable
diagnostics.

Historical checkpoint `ad46632` records 52 focused central checks, 14 reviewer
statements, a 2,260-check catalog with zero unclassified entries, the
`1116/159` base and `1140/159` monad-module warning inventories, fresh 270-file
health, and a green 1,802.847-second full CI. The post-checkpoint
transparent-whole correction removes the unnecessary whole projection rule
and whole proof-time equation while retaining all focused computations and an
empty strict module LHS audit; checkpoint `e90ce3c` preserves that correction.
Its warning inventory, 2,260-check catalog, and fresh 270-target health are
synchronized. The subsequent direct-usability correction passes the module,
2,268-check central suite, reviewer example, derived multiplication-component
join, empty strict module LHS audit, `1139/159` warning inventory, catalog, and
authority checks. Under the user's
scoped-validation instruction it does not claim a new health or full-CI run;
exact evidence is recorded in the living monad/comonad plan.
Free monad/comonad syntax, a commuting decision procedure, explicit
Kleisli/Eilenberg--Moore categories, and a TypeScript declaration surface
remain separate consumer-led work.

Cat-valued horizontal action is expressed through the generic
`comp_prod_fapp1_func` / `comp_prod_fapp1_fapp0` owner and its projection
ladder. Remaining `comp_cat_cov_*` / `comp_cat_con_*` names are transparent
readability or Cat-only projection surfaces where they expose transfor
structure; they do not own a duplicate functor law.

The same generic owner, specialized at `Catd_cat K`, also owns fixed-head
pre- and postwhiskering of displayed transformations. Given closed displayed
functors `L`, `F`, `G`, and `H`, and `eta : Transfd(F,G)`, the two inputs
`(eta,id_H)` and `(id_L,eta)` construct the whole transformations `H eta` and
`eta L`. Their fibre component is exposed by one evaluator beta at the
existing `tdapp0_fapp0` and `comp_prod_fapp1_fapp0` heads; it reduces to the
ordinary horizontal action in the fibre. This rule adds no symbol or second
action owner. `tdapp1_int_cell` continues to observe the whole result and
therefore retains its base-arrow and higher-cell action internally. The
identity-specialized full, capped, and base action clauses used by the
TypeScript runtime are pre-existing generic Lambdapi rules, not new
constructor-specific coherence.

This closure supports the bounded contextual surface bodies
`lambda^nd a. H(eta[a])` and `lambda^nd a. eta[L[a]]`. It does not construct a
classifier whose endpoints themselves vary over another context, and it does
not add the currently absent `Transf_catd_func`. Such a constructor remains a
consumer-led question rather than a prerequisite for fixed-head whiskering.

### Sections 8–10: directed Cat-valued families, Sigma/Pi, and mixed variance

Active family constructors include fibre notation, pullback/reindexing,
constant/terminal/opposite families, displayed composition, section
categories, and internalized Pi over varying bases.

```text
Pi_cat(E) =proof-time Functord_cat(Terminal_catd K,E)
Pi_cat(Const_catd K A) ≃ Functor_cat K A  (proof-time comparison).
```

`piapp0_func` and `piapp0` remain semantic definitions over terminal-source
component evaluation; they are not parallel primitive heads. Their full hom
action projects through the generic `tdapp0_func` owner and caps through
`tdapp0_fapp0`, so `pi_hom_fapp0` computes without a Pi-specific bridge.
When that capped component has already hidden a literal generic
`fapp1_fapp0`, four documented projection-order joins recover the two
ordinary naturality orientations and their `tapp1(epsilon,id) ->
tapp0(epsilon)` degenerations. They accumulate to the existing
`tapp1_fapp0` normal form; they do not add a second naturality calculus.
These joins can share the inferred outer category with their surviving
ordinary `tapp1`/`tapp0` operand. Vertical composition is handled separately
as evaluator projection beta: a composite displayed transfor under
`tdapp0_fapp0` expands to the pointwise composite of its displayed
components. This is the same orientation as ordinary `tapp0_fapp0`; it joins
the path where generic `fapp1_fapp0(tapp0_func)` strictness accumulates first
with the path where both operands project first. It does not introduce a
second functoriality calculus.
Likewise, `piapp1_func` remains the terminal-source specialization of
`fdapp1_int_presheaf_arrow`; its first next action reaches
`fdapp1_int_hom_fapp0`, preserving the iterated-hom tower. Runtime evaluation
of a constant-family section still computes through `piapp0` to ordinary
`fapp0`. The hom action of the constant-section constructor is owned by
`Const_transfd_func` / `Const_transfd`, rather than by an ordinary transfor
category fold.

Sigma total objects are dependent pairs. A total arrow consists of a base
arrow and a fibre arrow:

```text
(p,alpha) : (x,u) -> (y,v)
alpha : E[p](u) -> v.
```

`sigma_arrow` and `sigma_transport_arrow` are defined through this hom
characterization. `sigma_map_func` uses the displayed internal-hom projection
ladder for its fibre action; `sigma_map_transf` exposes the next generic hom
action as an ordinary transfor between total maps. Arbitrary displayed
functors are lax rather than silently strict/cartesian.

Asymmetric family reindexing now has its general total-category map. For
`F : A -> K` and `D : Catd K`,

```text
sigma_pullback_total_func(F,D)
  : Sigma_cat(Pullback_catd D F) -> Sigma_cat D
(a,u)       |-> (F[a],u)
(p,alpha)   |-> (F[p],alpha).
```

This owner was added only after auditing `Sigma_func`, `sigma_map_func`,
`Pullback_catd`, `Pullback_catd_func`, and the section/Sigma-introduction
surfaces and finding no existing owner of this base-changing map. It is the
Grothendieck totalization of the existing asymmetric family pullback, not a
generic pullback constructor for arbitrary total functors. Contextual pairing
uses `sigma_pullback_total_func(F,D) ∘ section_total_func(F*D,s)` for a whole
section s of the pulled-back family. The section-total Hom functor totalizes
the existing `piapp1_func` section. First projection and total base change
retain their first Hom heads and compute their next Hom actions recursively
through the same Sigma owners, with constructor-visible capped joins. The
`sigma_recursive_hom_action` reviewer checks the base projection through
third-level cells, both first-Hom identity observations and section evaluation.
No new carrier, universal-structure primitive or arbitrary arrow eta is added.
The direct arrow action of `sigma_intro_tapp0_func` and a whole-functor
first-projection beta remain separate.

The primitive `section_postcomp_sec` now has a proof-time associativity view:
mapping by FF and then GG compares with mapping by GG∘FF. Its runtime
component, arrow and identity rules are unchanged. Its head is noninjective
for unification, allowing this comparison without equating the intermediate
families. The six-assertion `section_postcomposition_views` reviewer covers
explicit/inferred maps, constant-target functors and negative runtime/section
controls. This does not identify arbitrary sections or add functor eta.

Independent Cat-valued displayed siblings reuse the ordinary product
semantics rather than a new `Product_catd` head. For `B,C : Catd K`, the
transparent family

```text
uncurry(Product_cat_func) o Product_pair(B,C)
```

computes its fibre at `k` to `Product_cat(B[k],C[k])` and its transport over
one shared base arrow `p` to `Product_map_func(B[p],C[p])`. The active closure
adds only the missing Cat-valued postcomposition capped-arrow projection and
the narrow same-literal-base product fold. Two unrelated parallel arrows do
not trigger the fold.

The fixed-base universal property is also active without introducing a
product-family head. The three injective owners

```text
Product_projL_funcd(B,C) : Functord(P(B,C),B)
Product_projR_funcd(B,C) : Functord(P(B,C),C)
Product_pair_funcd(FF,GG) : Functord(E,P(B,C))
```

have point, full-action, and capped-action projections, and pairing satisfies
both whole displayed-composition betas. The full and capped results remain
first-class functors, so a next-cell consumer can project them again. The two
beta rules deliberately retain `Catd_cat K` as a subject-reduction guard;
replacing that source classifier by `_` is ill typed. Displayed swap and
diagonal are transparent pairing composites with the displayed projections
and `id_funcd`, not additional primitive owners.

The internalized capped cell of displayed pairing is now componentwise at the
existing generic owner:

```text
fdapp1_int_cell(Product_pair_funcd(FF,GG),p,u)
  -> Product_pair(
       fdapp1_int_cell(FF,p,u),
       fdapp1_int_cell(GG,p,u)).
```

This is one runtime rule and zero new symbols. It closes the next-cell
observation of the already-existing pairing owner; it is not a new product
family, binder, laxity connective, or second functoriality calculus. A
positive conversion and opaque-cell noncollapse assertion live in
`emdash3_2_checks.lp`. Warning-enabled validation retains exactly 1179
warnings—1020 critical pairs and 159 replaceable pattern variables—and strict
LHS audit finds zero unreviewed candidates.

The root-only TypeScript `fibred-displayed-chain-2a` consumer uses this rule
for the exact mixed telescope

```text
k : K; a : A[k]; b : B[(k,a)], c : C[(k,a)];
d : D[((k,a),(b,c))].
```

It keeps the existing recursive `displayedDependentContextLambda` frontend,
derives the independent middle siblings, and transfers three existing
signatures plus nine checked runtime entries through the generic LF engines.
This is bounded elaborator evidence; it does not make arbitrary telescope
depth, general `:^nd`, or parsed surface syntax part of the active kernel.

For frontend reindexing, grouped siblings are canonicalized before Core
emission:

```text
P(B,C)[F]  elaborates as  P(Pullback_catd(B,F),Pullback_catd(C,F)).
```

The raw kernel term `Pullback_catd(P(B,C),F)` still does not convert to that
canonical presentation. No kernel reindexing rule, `Product_catd` head,
global displayed-functor/product conversion, universe-level product
projection, generic total pullback, or full family base-two-cell action is
implied.

`Functor_catd`, `Hom_catd`, and `Transf_catd` are mixed-variance family
constructors. Pointwise formulas do not replace their required base-arrow
actions.

The active constant-middle composition owner is the variance-qualified
displayed lift of ordinary functor composition. For `A : Catd(Op K)`,
`B : Catd K`, and an ordinary category `X`, it has the form

```text
Functor_comp_pair_funcd(A;X;B)
  : Functord(
      P(Functor_catd(A,Const_catd(K,X)),
        Functor_catd(Const_catd(Op K,X),B)),
      Functor_catd(A,B)).
```

At `k`, it maps a pair `(F,G)` to the existing ordinary composite
`Functor_comp_pair_func(F,G)`. Its full and capped base actions reuse the
target `Functor_catd(A,B)` action and remain whole functors, so the generic
`fdapp1_int_cell` and next-hom action can observe them. The rigid mixed
endpoint action remains owned by `Functor_catd` and ultimately by
`Unit_prof`; this package adds no duplicate identity, composition,
naturality, or `Unit_prof` rule.

The ordinary middle `X` is essential. The positive family
`Const_catd(K,X)` and negative family `Const_catd(Op K,X)` have the same
fibre `X`, but a general family over `K` cannot also be used as a family over
`Op K`. Accordingly this owner is a direct application/composition
combinator for bodies such as `G[k](c)(F[k](c)(a))`, not a mixed-curry
principle or a collapse of positive and negative classifiers. Nested binder
introduction remains the direct construction
`lambda^n k. lambda^f c. lambda^f a. t`; neither a total-context section nor
the auxiliary curry packages are prerequisites.

The durable diagnostic area contains seven checks covering the owner point,
constant-family fibre conversion, direct paired object and inner-arrow
computation, capped base action, generic internal cell/next-cell iteration,
and source/target non-collapse. At that owner's recorded checkpoint, warning
comparison was exactly 1,079 critical pairs and 159 replaceable pattern
variables, strict LHS audit was zero/53/33, the catalog contained 1,801
classified checks across 69 areas with zero unclassified checks, and the one
semantic-promotion CI passed all 41 kernel/example targets and
repository-integrity gates. The current combined boundary is recorded below.

The constant-domain displayed-evaluation closure is now active. For
`A : Cat`, `B : Catd K`, and
`S(A,B) = Functor_catd(Const_catd(Op_cat K,A),B)`, the two new reusable
owners are:

```text
Eval_funcd(B)     : Functord(P(S(A,B),Const_catd(K,A)),B)
Terminal_funcd(E) : Functord(E,Const_catd(K,Terminal_cat)).
```

Each has exactly one `tapp0_fapp0` point-component rule:

```text
Eval_funcd(B)[k]     -> Eval_func(A,B[k])
Terminal_funcd(E)[k] -> Terminal_func(E[k]).
```

The second owner composes with `const_section_func` to derive a coherent
fixed argument, so there is no third fixed-argument evaluator. Varying
subject/varying argument and varying subject/fixed argument are both
recursive TypeScript contextual-compiler consumers. The nested consumer
`H[e](G[d])` confirms recursion through both subject and argument
subexpressions rather than a whole-body recognizer.

The global `fapp`/`tapp` calculus remains the sole generic owner of
identity, composition, base-arrow action, and higher naturality. The two
component rules add two intentional critical-pair diagnostics but do not add
constructor-specific coherence rules. The specialization is deliberately
constant-domain: arbitrary mixed-domain evaluation, polarity-directed
contravariant lowering, arbitrary dependent-chain abstraction, and general
displayed-transfor coherence remain separate. The TypeScript frontend now has
bounded one-edge and exact `a; b,c; d` dependent-chain consumers; those
consumer profiles do not imply a general kernel binder.

### Sections 11–17: representables, dependent hom, and displayed action

The dependent-hom architecture is shared by Sigma homs, fibre transport, and
section action. Important owners are:

```text
Rep_catd
Edge_catd_func / HomPresheaf_catd_func
homd_ / homd_int
homd_src_func / homd_src_sec / homd_tgt_func
fib_cov_int / fib_cov_transf
tdapp1_int_func_transfd / fdapp1_int_transfd
fdapp1_int_* / tdapp1_int_*
```

The Sigma-map fibre projection ladder ends at:

```text
fdapp1_int_hom_fapp0(FF,p,u,alpha)
```

with the transported-identity specialization:

```text
fdapp1_int_hom_fapp0(FF,p,u,id) -> fdapp1_int_cell(FF,p,u).
```

This is the component-level displayed laxity normal form. The late section
18zz now promotes it to the whole transformation

```text
functord_laxity_transf(FF,p)
  : D[p] o FF[x] => FF[y] o E[p].
```

The implementation projects the arbitrary whole internal action through the
existing `tdapp0_fapp0`, `tapp0_fapp0`, `pi_hom_fapp0`, dependent-hom, and
self-comma identity-section owners. Its component reduces back to
`fdapp1_int_cell`, and its retained source-fibre arrow action computes through
one `tapp1_func` owner and capped `tapp1_fapp0` projection. No independent
naturality square is postulated, and this concrete consumer did not require a
primitive redesign of the transparent `piapp*` aliases. The section is late
because its identity-section action needs the completed cross-section
normalization environment; an earlier owner-position probe fails before those
dependencies are available.

The first two-sided/cubical consumer now sits beside this one-sided dependent
hom architecture. For `E : K1^op -> Catd(K2)`, `homdc_` packages

```text
(a,b) |-> Hom_{E[x1][y2]}(E[x1][b](u),E[a^op][y2](v))
```

as one functor covariant in `a` and contravariant in `b`. The construction is
transparent through `fib_cov_tapp0_func`, the outer action of `E`, component
evaluation, and `hom_con_int`. At `E=hom_int(id_C)` it is the ordinary directed
square classifier `Hom_{Hom_C(x1,y2)}(b o u,v o a)`.

`emdash3_2_cubical_square_total.lp` totalizes these two side coordinates at a
fixed vertical boundary. The four line observations remain whole, and their
actions on a next-hom object expose a bounded six-face cube; the two fixed
vertical sides reduce to identities.

The nondegenerate continuation is now derived from the same internal-hom/Sigma
calculus. For

```text
EdgeFamily_E[x1] = Sigma(x2:K2), E[x1][x2]
D_E              = Op_catd(EdgeFamily_E),
```

the whole mixed-variance owner is

```text
homdc_int(E) = homd_int(id_D_E).
```

Its canonical target-edge-first projection at `a:x1->y1` is
`Hom_{EdgeFamily_E[x1]}((x2,u),EdgeFamily_E[a^op](y2,v))`; ordinary Sigma-Hom
computation exposes `(b,alpha)` with the expected cross-fibre type. The total

```text
homdc_total_cat(E) = Op(Sigma(x1:K1^op),D_E[x1])
```

therefore internalizes both endpoints and side arrows without a new
parameterized-`homd_int` primitive. `LaxArrow_cat(C)` specializes this at
`hom_int(id_C)`, and `CubicalArrow_cat(C)` is its transparent readability
name. A selected readable pseudofunctor profile constrains the existing
compositor with fixed-forward `OmegaEquivAlong`; a selected native inverse
supplies the reverse boundary adjustment, making the operation functorial and
recursively iterable. Its endpoint reframe remains explicitly approximate
under the temporary global strict cut. Nat recursion then constructs
`CubicalLevel_cat(C,n)`.

The associated `{L,R,*}` code grammar is independent of Gray semantics and of
the separate generic assignment `FF |-> homd_int(FF)`. It forms the locally
discrete `SemiCubePlus_cat`, acts by source/target/profiled lift, and assembles
a whole opposite-indexed Cat-valued nerve. Public code action and whole nerve
action are joined by typed paths rather than a runtime arrow beta, because the
former retains recursive profile histories while generic functor cuts retain
their selected strict normal forms. Immediate faces form a recursive finite
family: two new endpoints plus every older face under star. This supplies a
fully variable native semicubical tower. Yoneda on `SemiCubePlus_cat` now
defines `StandardSemicube(n)`; the whole Hom action of the native nerve decodes
its `p`-faces into restriction functors and compares them with the computing
code action at arbitrary `p,n`.

The subsequent adequacy layer now supplies both requested object readings.
`cubical_yoneda_section` sends a native cube to its coherent code-indexed face
family, and evaluation at the identity face returns it along the existing
whole nerve identity path. Independently,

```text
GrayCubePos_R(0)       = WalkingArrow
GrayCubePos_R(succ n)  = WalkingArrow tensor_R GrayCubePos_R(n)
```

defines the fixed-bracketing geometric shapes. A selected strict realization
decodes by one Nat recursion uniform in the target category. The successor
uses right curry, the walking generator, the stable whole transformation graph,
and a proved cubical-level shift. Its capped arrow has literal sides `F[g]` and
`G[g]`; its filler is
`tapp1_post_laxity_cell(epsilon,g,id_x)`, derived from the whole internal
action rather than independently postulated. The selected two-dimensional
identity realization recovers the existing coevaluation data; its target side
is the inner-target arrow and its filler is definitionally the established
coordinate-swapped interchanger. The existing
immediate-frame family gives four edges and six faces at dimensions two and
three and remains variable-dimensional.

This is object-level semantic adequacy, not a full equivalence between Gray
mapping categories and native cubical levels. Tensor action in parameters,
unit/associativity/symmetry data, inverse decoding, degeneracies, connections,
and Kan structure remain separate future consumers.

Section 17 contains generic Sigma/Pi introduction/evaluation, constant
sections, ordinary structural logic, generic functor hom-action, section
pullback, and internal Pi action. Ordinary weakening `Const_func_func` is a
stable ordinary owner separate from the proof-time-only displayed
`const_section_func` facade.

On 2026-08-03 the unused contextual/mixed-curry experiment formerly in
sections 17f/17g was retired under D-DTTLF-USABILITY-083. No TypeScript,
book, or public-surface consumer selected those opaque packages after direct
nested `lambda^n`/`lambda^f`, compact `lambda^fd`, and compact/expanded
`lambda^nd` introduction graduated. Generic Sigma/Pi, pullback,
totalization, product/action, section-action, `Unit_prof`, `Hom_catd`,
`Functor_catd`, `Transf_catd`, and direct-binder owners remain active. The
retired code and checks remain recoverable at their recorded Git checkpoints;
retirement is a trusted-surface cleanup, not a mathematical impossibility
claim. At that retirement checkpoint, warning comparison decreased only
retired-rule interactions, from 1,097 to 1,086 unjoinable critical pairs,
while replaceable-pattern warnings remained 159 and the strict LHS audit
remained zero unreviewed clauses.

### Section 18: Cat-valued profunctors and computational comparison

`Prof_cat(A,B)` is the primitive fixed-endpoint category of Cat-valued
profunctors on `A^op × B`; `Prof(A,B)` is its object classifier and `ProfMap`
is its fixed-endpoint vertical hom.

Active infrastructure includes:

- primitive `Unit_prof(A)` with direct rigid `Hom_*` base action;
- `Prof_reindex` through `Product_map_func(Op_func(F),G)`, with the component
  of `Prof_reindex_transf` computing to the original whole fibre functor at
  that mapped base point; this preserves its next Hom action;
- readable representables `Hom_prof_along`, `Hom_prof`, `Companion_prof`, and
  `Conjoint_prof`;
- shaped cells/elements and internalized reindexing;
- primitive profunctor tensor and fixed-endpoint co-Yoneda maps;
- covariant and contravariant profunctor implication;
- fixed-endpoint eval/lambda inverse pairs;
- weighted cone/limit comparison and the dual weighted-colimit presentation;
- adjunction mate comparison and preservation of weighted limits/colimits;
- primitive directed join and its internally natural cross cell.

`ProfComparison(P,Q)` is a transparent compatibility name for
`DefIso(Prof_cat(A,B),P,Q)`. Its push/pull and evidence APIs route through the
generic `DefIso` and hom-action owners; it is not an independent eliminator
theory.

`Prof_tensor` and implication objects are symbolic primitives where the
current kernel lacks a general coend/coinserter quotient. Their checked beta,
reindexing, and closed-core interfaces state the active computational scope.

### One-way presheaf, sieve, topology, and CommRing-presheaf libraries

The kernel's Catd machinery now has a one-way standard-library facade:

```text
Psh_cat(K) =proof-time Catd_cat(K^op)
Obj(Psh_cat(K)) -> Obj(Catd_cat(K^op))
Hom_Psh(K)(P,Q) -> Functord_cat(K^op,P,Q)
F^* = Psh_pullback_func(F)
    : Psh_cat(B) -> Psh_cat(A).
y_K = yoneda_psh_func(K) : K -> Psh_cat(K)
y_K(U)[V] -> Hom_K(V,U)
Into_restr_cat(U) -> Sigma_(V:K^op) Hom_K(V,U)
Slice_cat(U) -> Op_cat(Into_restr_cat(U))
HigherSieveClassifier(K)[U]
    -> Catd_cat(Into_restr_cat(U)).
IsSubterminalCat(C)
    = Sigma(IsPropGrpd(Obj(C)), IsGroupoidalCat(C)).
Sieve(U)
    = Sigma(S : HigherSieve(U), IsOrdinarySieve(S)).
sieve_pullback(p) : Sieve(U) -> Sieve(V).
SieveMembership(R,(V,f)) -> Obj(R(V,f)).
SieveCoverage(K) -> Pi U, Sieve(U) -> PropU.
GrothTopology(K)
    -> coverage plus maximality, pullback stability, and local character.
CommRingPsh_cat(K) -> Functor_cat(K^op,CommRing_cat).
comm_ring_psh_restrict(O,f,s) -> O[f](s).
CommRingPshInvertibleAlong(O,s,f)
    -> CommRingUnitEvidence(O(V),O[f](s)).
Matching_O(s)
    -> Pi_(V,f,m in D_O(s)) Path_cat(|O(V)|).
restrict_ell : Path_cat(|O(U)[1/s]_ell|) -> Matching_O(s).
restrict_ell(x)[V,f,m] -> factor(ell,f,m)(x).
glue_ell : Matching_O(s) -> Path_cat(|O(U)[1/s]_ell|).
glue_ell(restrict_ell(x)) = x.
factor(ell,f,m)(glue_ell(a)) = a[V,f,m].
```

The category heads do not runtime-collapse. Restriction's object action is
the existing `Pullback_catd(P,Op_func(F))`; ordinary map action and laws remain
generic. Yoneda action is existing represented-hom postcomposition, slice
construction is existing Sigma totalization plus opposite, and higher-sieve
restriction is existing Catd pullback. The higher name is literal. A separate
downstream module selects ordinary sieves by pointwise native subterminality
and preserves that evidence under the same pullback action. It does not prove
the ordinary-sieve carrier set-valued and does not declare `Omega`, descent,
or topology. A further rule-free module packages direct proposition-valued
sieve topologies and the chaotic model without binding `Omega` or itself
adding generated coverhood or sheafification. Downstream one-way modules now
construct the least topology accepting witness-rich generators and the
fixed-site Cat-valued direct-cover reflector described under “Constructed
Cat-Valued Sheafification Status” below. The later CommRing-valued affine and
scheme packages retain supplied structure-sheaf/locality capabilities; they
are not derived silently from that Cat-valued reflector.

The CommRing-valued classifier is transparent rather than a second rigid
presheaf facade. Explicit restriction applies the retained structured-map
function. Identity and composite restriction laws are theorem-level paths
through the selected pointwise ring-map comparisons; generic whole arrows
retain their negative carrier-computation boundaries. Arrowwise unit support
is a property and is closed under further restriction. The downstream carrier
and unit-evidence families assemble it as a whole ordinary sieve, the locality
module packages its selected localization factors as one internal cone, and
the matching module applies those factors to localization elements as
internally coherent Pi sections with equality-path action. The selected glue
module supplies the converse as a genuine functor plus both Path-valued
component observations. It is computational basic-open locality over `D(s)`,
not ordinary sheaf descent; no native whole equivalence is asserted.

### Section 19: PathOut, path induction, and Eckmann–Hilton

For fixed `x : Z`:

```text
PathOut_Z(x) = Sigma (y : Z), Hom_Z(x,y).
```

The canonical arrow from `(x,id_x)` to `(y,p)` is the generic Sigma transport
arrow for the representable family. The primary path-induction package is the
telescope theorem `PathInd_transfd(Z)`; `PathInd_funcd(Z)` is derived by
`Sigma_transfd_funcd`.

The transitivity benchmark computes to ordinary composition. Nested telescope
terms stress the mixed-variance surface.

The first Eckmann–Hilton slice defines 2-endomorphisms of an identity 1-cell,
vertical and represented horizontal composition, the common-middle
equalities, and commutativity `EH_comm`.

## Core Ownership Invariants

### Runtime computation versus proof-time comparison

A rewrite rule selects a runtime normal form and participates in critical
pairs. A `unif_rule` helps elaboration/proof construction when neither side is
chosen as the runtime normal form.

Use:

```text
assert t ≡ u
```

for runtime conversion, and a typed reflexive equality:

```text
eq_refl(t) : τ(t = u)
```

to exercise a proof-time unification comparison. Do not infer runtime
joinability from a successful typed `eq_refl` probe.

### Displayed facade tower

The first three displayed heads remain stable:

```text
Catd_cat K
Functord_cat K E D
Transfd_cat K E D FF GG.
```

They compare at proof time with `Functor_cat K Cat_cat`,
`Transf_cat K Cat_cat E D`, and the corresponding ordinary iterated hom.
Their `Obj` projections compute toward the ordinary presentations, while their
`Hom_cat` projections expose the next displayed rung. Add direct comparisons
at every represented rung; do not rely on unification-rule transitivity.

`Pi_cat K E` is the stable section-category facade over the terminal-source
displayed rung. It compares directly at proof time with both
`Functord_cat K (Terminal_catd K) E` and the corresponding ordinary
`Transf_cat`, while its `Obj` and `Hom_cat` projections expose section objects
and the `Transfd_cat` next hom. The constant-family comparison with
`Functor_cat K A` is also direct; do not rely on comparison transitivity.

For sections over `Sigma_proj1_pullback_catd`, the distinct `Pi_cat` and
`Functord_cat` heads now support a direct proof-time uncurrying comparison.
Runtime subject reduction for `path_ind_sec -> fib_cov_transf` crosses the
general Pi/displayed object ladder and one measured join between ordinary
`Obj(Transf_cat)` classifiers. A direct specialized displayed-`Obj` rule is
redundant. The next `Transfd_cat` projection is retained for iterability.

The stable projection-pullback family is now an explicit runtime selection,
not the automatic reduct of either
`comp_cat_fapp0(D,Sigma_proj1_func(R))` or
`Pullback_catd(D,Sigma_proj1_func(R))`.  Both generic presentations compare
with `Sigma_proj1_pullback_catd(R,D)` through narrowly typed `unif_rule`s.
This keeps generic represented-family reindex accumulation as the selected
runtime cut and removes the competing generic-versus-stable normal form.
Consumers requiring the projection ladder name the stable family directly.

Recursive dependent-variable weakening consequently uses the explicit whole
displayed functor

```text
section_weaken_funcd(R,E,s) : R ->_K E
section_weaken_funcd(R,E,s)[k] = const_{R[k]}(s[k]).
```

Its base-arrow action is the already-internal action of `s` and is independent
of the new source-fibre object.  `sigma_functord_sec` then uncurries this
displayed functor when a section over `Sigma(R)` is needed.  Generic
`section_pullback_sec(F,E,s)` remains available and computes at literal base
objects; it is no longer overloaded as the stable displayed weakening owner.

The displayed-evaluation computation now follows those same whole/point/cell
owners. A leading `Eval_funcd ∘ FF` exposes evaluation after FF; pairing keeps
both displayed actions; identity acts as identity; an explicitly constant
weakened section acts constantly at the appropriate identity. Opposite
presentations have the same selected projections at their native Hom
endpoints. The whole mixed Eval functor and its next Hom action remain
available, not merely the component formula `eta[i]`.

Transported-identity cells have explicit structural joins where the generic
identity recognizer otherwise erases the whole/point discriminator. The
terminal-source unit fold is restricted to a constant section of a constant
family; its original whole/point/cell projections also compute after the
weakening head disappears. There is no general section eta fold, arbitrary
laxity-to-identity rule, unrestricted displayed-composite expansion or new
primitive. The dedicated reviewer is
[`displayed_evaluation.lp`](../examples/displayed_evaluation.lp); the
[pilot ledger](../../docs/TYPESCRIPT_EMDASH_STRICT_INTERNAL_HOMOLOGY_PILOT_PLAN.md#qualified-structural-evaluation-tranche)
records guards, competing projection orders and warning qualification.

The concrete consumer is the whole edge observation of a varying triangle:
an actual transformation `eta : T0 ⇒ PathOut(a) ∘ T1` is evaluated to
`(a,eta[i])`. The local computation is independently checked using ordinary
Eval and does not manufacture an inverse arrow. The hybrid triangle remains
a prototype until its strict zero restriction and coherent maps are
qualified; general op/Sigma repair is still deferred.

The uncurrying operation is functorial at one whole owner:

```text
sigma_functord_sec_func(R,D)
  : Functor(Functord_cat(R,D),Pi_cat(Sigma(R),pi1^*D)).
```

Its object action selects `sigma_functord_sec(FF)`.  Its generic arrow action
already carries displayed-transformation naturality internally, while one
narrow runtime projection restores the component beta hidden by the stable
section facade:

```text
sigma_functord_sec_func[eta][(k,r)]
  -> Const_transf(eta[k][r]).
```

Do not describe this projection beta as a theorem of naturality alone.  It is
the defining observation of the functorial uncurrying lift; generic naturality
states that these observations commute along arrows of `Sigma(R)`.  Do not add
a second named transformation head merely to restate the same intermediate
action unless an independent consumer needs that head and its warning/owner
audit justifies it.

### One generic owner for ordinary laws

The global `fapp*`/`tapp*` calculus is the sole owner of ordinary identity,
composition, functoriality, and naturality. A constructor-specific rule whose
only content is one of those laws indicates a missing internalized
functor/transfor owner or a detached projection.

Do distinguish a duplicate structural law from projection beta. Once a
stable evaluator head such as `tapp0_fapp0` or `tdapp0_fapp0` has erased the
literal generic evaluation-action pattern, a rule exposing the component of a
composite is the next rung of the evaluator ladder:

```text
tapp0(x,eta o epsilon)
  -> tapp0(x,eta) o tapp0(x,epsilon)
tdapp0(x,eta o epsilon)
  -> tdapp0(x,eta) o tdapp0(x,epsilon).
```

This pointwise expansion coexists with the generic strict-functor cut
`F[g] o F[f] -> F[g o f]` because the rules operate at different heads and
must be tested as a joining projection diamond.

The generic higher-component rung is now explicit:

```text
Theta : eta -> eta'
tapp0_hom_fapp0(Y,Theta) : eta[Y] -> eta'[Y].
```

It is the capped hom action of `tapp0_func(Y)`, with computational identity
and vertical-composition projections. Its `Cat_cat` specialization reduces to
the pre-existing `tdapp0_fapp0` stable head; the former direct Cat-only capped
rule is retired, while `fapp1_func(tapp0_func(Y))` still exposes the whole
`tdapp0_func(Y)` action. The owner-position diagnostic delta is exactly
`+30` critical pairs (`25` composition, `3` identity, and `2`
specialization/evaluator interactions), with no replaceable-LHS growth or
subject-reduction failure. Treat this classified delta as projection evidence,
not as permission to add reverse joins mechanically.

A specialized projection-order bridge is exceptional but legitimate when:

1. a stable projection erases the literal generic-owner pattern;
2. an outer generic cut competes with that projection;
3. the two paths do not already join;
4. a focused owner-position probe establishes one canonical orientation.

Never install both orientations or generate such bridges mechanically.

### Hom variance and Došen cuts

When a term is already expressed through a stable hom-action owner, fold
consecutive actions to the one action indexed by the composite arrow:

```text
(F q)_*((F p)_*(g)) -> (F(q o p))_*(g)
(F p)^*((F q)^*(g)) -> (F(q o p))^*(g).
```

The second formula reflects contravariance: `q o p` first traverses `p`, then
`q`, while the induced precomposition actions are encountered in the reverse
endpoint order. These are the current runtime accumulation orientations.

Raw expanded compositions should normally remain `comp_fapp0` terms. Use the
existing proof-time bridges when a theorem compares them with stable hom-action
syntax. Add a raw runtime bridge only for a concrete consumer after testing
owner-first and projection-first reductions.

### Omega-friendly structure

Prefer functor-level folds over capped object rules when later hom action is
needed. A RHS that computes one selected cell can lose the functor object
required for the next dimension.

A formula `E[x] = ...` is only the object part of a directed family. A formula
`eta[x] = ...` is only a transfor component. Identify the base-arrow action and
off-diagonal/naturality action or explicitly record them as deferred.

## Before Editing The Kernel

1. Identify the semantic owner and whether the desired result is runtime or
   proof-time.
2. Search current declarations, rules, checks, examples, and the relevant plan
   with `rg`.
3. Decide whether a missing projection, transparent alias, or canonical
   endpoint fixes the problem before introducing a stable head.
4. Write the mathematical formula and the intended normal form.
5. Probe the candidate in a temporary full-file copy at its owning position.
6. Add a focused conversion assertion or typed `eq_refl` consumer.
7. Run a bounded quiet check; enable warnings when interactions are unclear.
8. Promote the smallest working change and add a durable diagnostic/example.
9. Update the task report when the architecture or a rejected orientation
   matters beyond the local rule.

## Rewrite And LHS Hygiene

### Minimal inferred slots

Keep reconstructible source/target/category/family arguments as `_` on rule
LHSs unless they are:

- the actual constructor discriminator;
- a composition-interface guard;
- required for subject reduction;
- a measured decision-tree/performance guard.

Observational classifier equations can make identity types with distinct
categories or endpoints decode to the same classifier. Whenever such an
equation is added, re-audit every beta whose LHS matches a proof constructor
while leaving those indices inferred. A quiet full check is insufficient:
instantiate a proof-dependent injective motive, compute the candidate term,
and verify that its normal form still inhabits the declared result. The generic
`ind_eqr` beta therefore repeats both its category and reflexive endpoint; this
is a subject-reduction guard, not optional overspecification. A proof-time
`unif_rule` cannot repair an ill-typed runtime beta.

Compound reducible inferred terms such as `fapp0 F x`, `Functor_catd ...`,
`Op_cat(Hom_cat ...)`, or transparent readability aliases can cause brittle
matching and conversion explosions.

Audit candidates with:

```bash
python3 scripts/audit_rule_lhs.py --show-kept
make audit-rules
```

Do not apply the scanner mechanically. Probe each `_` replacement. Mark a
measured exception immediately above the rule:

```text
// lhs-audit: keep SLOT[,SLOT] -- reason
```

The rule applies at rewrite-family scale, not only one slot at a time. Match on
the true stable discriminee and do not copy surrounding presentation wrappers
across sibling rules. For example, when `Op_func(_,_,F)` selects the case,
extra `Op_cat A`, `Op_cat B`, product-functor, or transparent-alias endpoints
should remain inferred unless the theorem genuinely distinguishes those
wrappers. A surface pattern that works for a variable endpoint may otherwise
stop matching when that endpoint normalizes to a product or functor category.

### Explicitness depends on the surface

Do not apply LHS minimality as a blind whole-file formatting rule. The four
main surfaces have different needs:

1. **Rewrite and unification patterns:** keep the stable discriminator
   explicit and reconstructible endpoint/category/family slots implicit.
   Apply this discipline to both sides of a `unif_rule`.
2. **Rule RHSs and defined-symbol bodies:** omit only arguments that are
   syntactically recoverable from the visible data. A fixed parameter that is
   not determined by the remaining arguments must stay visible even if an
   expected type happens to recover it in one probe.
3. **Theorem-style examples:** prefer the compact mathematical formula;
   projectionwise product/Sigma statements are often clearer and more robust
   than raw dependent-constructor equality.
4. **Diagnostic assertions:** keep canonical source/target endpoints explicit
   when the purpose is to expose the full `fapp1_func`, `fapp1_fapp0`, product,
   or displayed-action shape. Compactness must not turn a regression into a
   test of accidental endpoint inference.

This distinction preserves readability without erasing the information needed
for matching, subject reduction, or a stable diagnostic.

### Outer eliminators over active cuts

Treat an LHS such as:

```text
sigma_Fst(comp_fapp0(...))
sigma_Snd(fapp0(specialized_func,...))
```

as a high-risk commuting conversion. The outer projection and inner cut can
reduce in competing orders. Prefer:

1. an existing generic projection ladder;
2. a constructor beta rule;
3. a stable intermediate component;
4. an equation at the functor/transfor owner;
5. propositional evidence when judgmental computation is unnecessary.

A new commuting conversion requires a concrete consumer, focused checks for
both paths, an owner-position full-file probe, and warning classification.

### Canonical types and expected-type probes

Prefer reduced declared types and canonical endpoints:

```text
τ(Functord E D)
Hom_cat Z x y
Functord_cat E D
```

Use unreduced types only when the exact projection route is intentional and
document why.

A bare `assert t ≡ u` lets Lambdapi infer both sides independently. When a real
consumer supplies an expected type, test that typed shape explicitly before
concluding that conversion fails: first check the raw term at the intended
type `T` (or bind it with a temporary helper returning `T`), then test
conversion or typed reflexivity using that term. Keep a bare conversion
assertion only when both sides are expected to elaborate without contextual
type information.

Do not introduce decoded `*_TYPE` or parallel classifier heads merely to make
binders shorter. Such a head needs to join the existing category/classifier
reductions and can create a second semantic layer. Keep ownership at canonical
heads such as `Transf_cat`, `Functord_cat`, and `Product_cat`; use narrow
`Obj(...)` elaboration aids only when a measured consumer requires them.

### Constants and unification limits

A `constant` cannot head a rewrite LHS. Changing it to `injective` is a global
normal-form migration requiring full downstream, subject-reduction, warning,
and decision-tree review.

Unification rules are experimental and not reliably transitive. Prefer two
rigid heads or a stable intermediary. Apply inferred-slot hygiene to both sides
of a `unif_rule`.

### Stable heads and semantic equivalences

Add a stable head only when later rules need a visible constructor or a focused
probe establishes a real discrimination/performance boundary that a smaller
projection or canonical endpoint cannot solve. A surface-readable name alone
is not enough; transparent aliases should normally remain definitions.

Notation-only heads such as `Fibre_cat(E,k) = fapp0(E,k)` should not receive
broad injectivity or inversion rules: equality of two fibres must not generally
recover the entire family and index.

Likewise, familiar equivalences for maps out of the terminal category are not
global runtime computation by default:

```text
Functor_cat(1,A) ≃ A
Transf_cat(const(u),const(v)) ≃ Hom_A(u,v).
```

Prefer a consumer-local projection/fold through the existing section and
component owners. Promote a global terminal-source rewrite only after a
concrete consumer, both reduction orders, and the warning/subject-reduction
effects have been measured.

## Identity Normal Forms

Identity may appear as `@id`, the transparent `id_func`, `id_funcd`, or
`id_transfd` views, or a specialized projected identity. There is no separate
ordinary `id_transf` constructor. A rule for the generic surface does not
automatically match every proof-time-comparable category presentation.

Prefer narrow typed consumer rules or a coherent small specialization package
over broad global identity rewrites. The current middle-constrained generic
composition identity rules keep the shared middle object as the true cut
interface while inferring outer endpoints. Competing runtime identity
spellings are joined through the typed pre/post proof-time bridge; that
proof-time joinability is the selected criterion for this measured overlap.
Across the ordinary/displayed first-hom facade, identity-specialized
`tdapp1_int_*` consumers explicitly accept generic `id` at both
`Functord_cat(E,D)` and `Transf_cat(K,Cat,E,D)`. This is a typed façade package,
not a global rewrite between the two identity terms.

## Comment And Layout SOP

Put a brief comment immediately above most semantic symbols and nontrivial
rule families:

- public constructor: mathematical name/formula and primitive/defined status;
- stable head: projection formula and generic owner;
- transparent alias: explicitly label it an alias/view;
- rewrite: label beta, projection, cut, accumulation, or confluence join;
- unification: state that it is proof-time only;
- evidence symbol: state the proposition witnessed.

One comment may cover a cohesive `rule ... with ...` command.

Use compact horizontal layout for simple stable-head rules. Keep vertical
layout for nested endpoint formulas, deliberate explicit guards, and
diagnostic assertions that expose canonical endpoints.

Do not duplicate a semantic body in a readability helper. Route aliases
through the named semantic constructor.

## Development And Validation Workflow

### Persistent goals and Git checkpoints

A long-running Codex `/goal` must recover the current authority, active plan,
owner positions, worktree list, staged and unstaged diffs, and bounded baseline
on every continuation. A baseline commit is comparison evidence; do not reset
a descendant implementation to it.

Persistence alone does not authorize Git mutations. When the user or the
task's launch prompt explicitly authorizes local checkpoint commits, use the
repository workflow in
`../../docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`. A kernel checkpoint is
eligible only after the smallest owner-position experiment has a typed
positive consumer and relevant negative/non-collapse evidence, proportional
warning and rule audits are complete, affected diagnostics/catalog/health and
plan ledgers are synchronized, and the staged diff contains no unrelated work.

Checkpoint authorization never weakens the semantic promotion procedure and,
unless separately requested, never includes push, merge, rebase, amend, reset,
publication, branch deletion, or worktree removal. Correct failed experiments
with new reviewable evidence/commits or compare explicit experiment branches;
do not erase the decision trail.

### Bounded checks

```bash
EMDASH_TYPECHECK_TIMEOUT=90s make check
timeout 90s lambdapi check emdash3_2.lp
make check-warnings
```

The 90-second value is the default per-file limit for focused probes, warning
checks, registered aggregates, and health traversals. The native-universality
goal's 2026-09-14 user direction permits measured extensions; the guard accepts
an explicit limit up to 300 seconds while preserving memory/file bounds and
serial execution. Its model/reifier subplan records the selected target and
evidence. The central diagnostics
and several focused consumers now have measured green runs near 60 seconds, so
the older split limits could classify the same valid import path differently.
This is a timeout ceiling, not permission to run broad aggregates for
reassurance. If a quiet check times out or hides the interaction, rerun the
smallest target with warnings enabled before changing the architecture.
Resumable health evidence continues to require exact checked-content and
environment identity, including the timeout.

### Focused probes

```bash
scripts/probe.sh tmp/probes/name.lp
scripts/explain_failure.py logs/probes/name.log
```

Ordinary experiments belong under ignored `tmp/probes/`. Move durable
reviewer-facing computations to `examples/`.

### Warning and decision-tree diagnosis

```bash
make warning-summary
scripts/explain_failure.py --warning logs/warnings/latest.log
scripts/decision_tree.sh SYMBOL
scripts/decision_tree.sh --png /tmp/tree.png SYMBOL
```

The compact warning summary reports both overlap-term heads and unordered
pairs of the two participating rewrite-rule heads. Its strict structural
parser rejects a critical-pair block that lacks one term head or exactly two
participants, preventing a changed Lambdapi warning format from silently
dropping families. This is a completeness check on the inventory, not a
semantic classification of joinability; the raw stream remains authoritative.

Use the smallest Lambdapi debug flag set: `u` unification, `c` conversion, `q`
rewriting, `w` weak-head normalization, `s` subject reduction, `k` local
confluence, `d` decision-tree compilation, and `i` typing. Never use
`--no-sr-check` for promoted code.

### Catalog, examples, CI, and health

```bash
make examples
make catalog
make toc
make ci
make health
```

`make catalog` can be non-strict during exploration; `make ci` requires a fresh
catalog and zero unclassified checks. `make toc` requires the header source map
to match every formal section/subsection heading exactly and is also part of
CI. Run `make health` after meaningful architecture/check changes.

### Type-aware search

Use `rg` for ordinary discovery and:

```bash
scripts/lambdapi_search.sh 'name = hom_int'
scripts/lambdapi_search.sh 'type >= Prof_imply_cov'
```

for normalization/type-aware search.

## Constructed Cat-Valued Sheafification Status

The direct cover-completion program now reaches the existing supplied
fixed-site capability. `emdash3_2_direct_cover_completion_universality.lp`
provides the whole seed-functorial recursor, higher unit beta, topology-local
eta/uniqueness, and the resulting Hom `OmegaEquivAlong`. The subsequent
`emdash3_2_direct_cover_sheafification.lp` realizes only
`Sheaf_cat(K,T,Cat_cat)` as pairs `(P,IsTopologyLocalPsh(P))`; arbitrary value
categories remain opaque.

One whole inclusion forgets locality, and one whole reflector maps `P` to its
local direct cover completion. The indexed adjunction is declared at the raw
`Functor_cat(Op_cat(K),Cat_cat)` boundary required by the generic package,
while a scoped proof-time comparison preserves rigid `Psh_cat(K)` as the
computational owner. Its unit and counit compute to the HIT unit and the
identity-seeded recursor. Recursor beta and topology-local eta derive both
cancellation laws, giving the exact fixed-counit `OmegaEquivAlong` and a term
of the existing `SheafificationCapability(K,T,Cat_cat)`.

The facade's runtime composition projection exposes twelve additional
`comp_fapp0`/generic-naturality warning blocks: the imported baseline is
1,017 critical pairs plus 159 replaceable-pattern advisories, and the
integrated module reports 1,029 plus 159. A proof-time-only stable-composition
alternative was rejected because dependent endpoints still required the same
category projection while adding indirection. The direct rule is retained as
the honest inherited category operation; strict LHS audit is clean. These
warnings remain measured diagnostic evidence, not a claim of global
confluence.

After integration of the completed TypeScript-elaborator, PSSS,
internal-laxity, profiled-Gray, WalkingEnd--Circle, groupoidification,
monad/Cartesian, cubical/property-profile, pullback, and
slice-dependent-product histories, plus the rule-free finite-presentation,
presentation-morphism, bounded-free-complex/chain-map, and finite-free/Freyd
presentation extensions, the active kernel warning boundary remains
1,274 diagnostics: 1,117 unjoinable critical pairs and 157
replaceable-pattern advisories. Downstream module-specific additions and
projection-order classifications remain in their dated implementation plans;
there is no fabricated single warning total for every possible import
closure. The strict kernel LHS audit has zero unreviewed clauses, 63 annotated
slots, and 38 intentional clauses; every changed rule-bearing extension also
has zero strict findings. The generated catalog contains 2,359 classified
checks across 116 areas with zero legacy or unclassified entries.

The current registered health report is deliberately an honest no-check
source snapshot over 358 maintained owner/reviewer files. It records no exit
or timing claim, because the integration follows the user's scoped-validation
boundary rather than launching a repository-wide health sweep. The relevant
changed kernel/module/diagnostic/reviewer targets passed their proportional
90-second-per-target gates in their owning tranches. The source-metrics
snapshot is
`sha256:75fa60a58c5433ca3312d323cef0ac9154cb8d94d9a3b9cbf3234029f39a48ba`
and the check-content snapshot is
`sha256:e2889d195dbfd6fe3f75557beac504fffc674f65a8f15beaadfd10208e6c9cd7`.
The newly registered finite-module owner and reviewer pass their focused
bounded checks, its strict LHS audit is empty, and emitted membership,
syzygy, and adjacent-zero Core targets pass a live Lambdapi probe. The
warning-enabled owner check adds no local diagnostic because the extension
declares no rule or unifier.
The downstream presentation-morphism owner and reviewer likewise pass their
focused checks with zero local warning diagnostics and an empty strict LHS
audit. Live emitted-Core checking accepts its relation-preservation,
representative-agreement, and chain-square equations. These are proportional
target results, not a repository-wide timing claim.
The recursive bounded-free-complex and chain-map owners plus both reviewers
pass their focused checks with zero local warning diagnostics and empty strict
LHS audits. Live emitted-Core checking accepts the selected adjacent-zero and
component-square laws; whole negative composites remain TypeScript
observations. These results add no quotient, exactness, or homology claim.
The finite-free and Freyd-presentation owners plus their reviewers pass their
focused checks with zero local warning diagnostics and strict LHS findings.
The formal Hom quotient uses existing groupoidification and `0`-truncation;
explicit agreement paths and representable elements check. Downstream named
usability paths now connect generic Freyd identity/composition to the semantic
class operations without changing their generic runtime owners.
The downstream raw presentation-operation owner and reviewer also pass focused
checks. Identity and composition retain both matrices and construct their
relation squares from transparent unit/associativity and the reusable square-
pasting path. The extension adds no rewrite or unification rule and therefore
no local warning family.
The derived-ring, matrix-additive, and raw-presentation-additive owners plus
their two focused reviewers also pass. They construct zero, addition,
bilinearity, and both raw additive square laws without runtime rules or opaque
equality constants; all three strict LHS audits are empty.
The matrix-subtractive and presentation-agreement owners plus the focused
agreement reviewer pass as well. Agreement now has explicit equivalence,
additive, and pre/postcomposition operations; both new strict LHS audits are
empty and no local warning family is introduced.
The Freyd operations/usability owners and both focused reviewers pass. Raw and
truncated composition/addition compute on classes, and named paths connect
generic category identity/composition to their semantic operations. The two
outer fapp1 action rules contribute six classified identity overlaps; the two
inner action comparisons are proof-time and add no runtime family.
The raw-negation and class-preadditive owners plus their focused reviewers pass
as well. Negation computes on raw/truncated classes, and packaged class laws
cover additive unit/associativity/commutativity/inverse and both
distributivity orientations.
The set-target groupoidification, truncation-path, full-law, and generic/Freyd
preadditive owners now pass their focused checks and strict LHS audits. They
promote those equations to arbitrary quotient points and construct the formal
`PreadditiveCategory` instance. The prior class-law target and the completed
target each report 1,300 warning instances, so the rule-free descent/package
adds no diagnostic family; the one set-pointwise component beta likewise left
its focused groupoidification count unchanged at 1,274.
The direct polynomial Freyd model computes zero/addition/negation, zero and
direct-sum presentations, canonical biproduct maps, and block-diagonal arrow
action. Its registry binds and qualifies every inherited
`additive-category` role, and its categorical compiler lowers those operations
to the TypeScript reference engine. Focused TypeScript tests, typechecking,
targeted lint, and the formal reviewers pass. The one full TypeScript boundary
run passed workspace/typecheck/lint and retained only unrelated existing
kernel/article source-pin failures in the consolidated suite; those orthogonal
audits are not rewritten by this additive tranche.

The successor polynomial provider now computes complete original-column
syzygies, weak-kernel matrices, and selected lifts with checked annihilation
and reconstruction. A genuine additive finite-free category facade registers
whole/object/morphism/lift operations, compiler lowerings, and reference
execution, and qualifies the computational-weak-kernel doctrine. Singular
compares generated submodules bidirectionally as an oracle. The explicit-Core
bridge replays whole/lift computation and permits explicit adoption of named
`F o K = 0` and `K o U = H` equations; its live Lambdapi probe passes. A
ring-wide formal factor provider and the Freyd-to-Abelian theorem remain later
capability-indexed work.

The next native construction now computes unconditional polynomial Freyd
cokernels by adjoining morphism columns to target relations. It retains the
zero-composite agreement consumed by each colift and checks annihilation,
reconstruction, and quotient uniqueness of competing colifts. Formal raw
presentation/projection data are the next consumer; a closed quotient-level
universal package remains gated because the current truncation API maps raw
agreement to equality but does not decode arbitrary quotient equality back to
the witness required by the colift algorithm.

The formal witnessed counterpart is now active: it constructs the enlarged
presentation and projection from matrix block laws, accepts the explicit
zero-composite agreement, builds the horizontal relation witness for the
colift, and produces quotient paths for annihilation, reconstruction, and
uniqueness. It deliberately preserves the effectiveness boundary above.

The native polynomial Freyd kernel now follows Construction 3.10 literally.
It weak-pullbacks the morphism datum against target relations, then weak-
pullbacks the first projection against source relations. The second first
projection is the kernel relation map and the first first projection is the
embedding datum. A retained zero-composite agreement supplies the first lift;
the test's relation witness supplies the second. The implementation checks the
embedding square, annihilation, lift square, reconstruction, and quotient
uniqueness of competing lifts.

The formal witnessed construction now matches it: an explicit base
weak-kernel capability constructs both weak pullbacks, conventional
compatibility supplies the embedding square, and explicit zero/reconstruction
agreements feed both lift stages and the uniqueness factor through the second
weak pullback. Quotient paths expose the resulting equations without claiming
a capability for arbitrary rings.

The field-polynomial category/CAS provider now registers complete kernel and
cokernel role families on the unchanged Freyd carrier. Whole constructions
are primitive computation owners; object, embedding/projection, and
lift/colift are derived category methods with compiler lowerings and reference-
engine execution. `PREABELIAN_DOCTRINE` requires all eight usable roles, and
the provider qualifies only after every inherited additive and universal role
is plannable. Non-field coefficient providers are rejected; no Abelian claim
is made.

The native polynomial Freyd snake operation follows the nonsplit CAP
fiber-product/pushout algorithm and retains every selected universal result,
stability witness, normal factor, and reconstruction agreement. Its
ring-indexed reference surface exposes whole triple and connecting operations
plus canonical serialization of the complete result. Direct and two-node
graph execution agree byte-for-byte on the nonsplit `R -> R/(x)` consumer; no
projection section or external CAS process is used.

The polynomial Freyd snake category model registers whole fiber-product and
pushout roles, their projections/injections and factor/cofactor operations, a
witness-rich short-exact triple, the snake triple, and the connecting
morphism. Its connecting method records the CAP dependency order through the
existing universal and normal-factor operations. Every role lowers to a
matching native operation, and a retained two-node triple/connecting program
agrees canonically with direct category execution. The category carrier and
Abelian doctrine are unchanged; no matrix algorithm is duplicated above the
lowering boundary.

The selected snake proof–CAS bundle replays that same whole native operation
and reifies 25 exact morphism/agreement claims spanning the input zero,
kernel/cokernel stages, fiber/pushout compatibility, both projection and both
injection reconstructions, property witnesses, normal tests, and final
reconstructions. Canonical output drift or a different goal is rejected before
adoption. Focused workflow tests and one generated live Lambdapi probe pass;
the bridge adds no Core owner and makes no CAS correctness or closed formal
capability claim.

The non-authoritative field differential independently executes the CAP
kernel/cokernel, fiber/pushout, and one-sided-inverse chain over rational
quotient coordinates. It matches the constant-ring polynomial Freyd induced
map `[-1]` and separately checks CAP's displayed 2-by-2 representative
`[[0,0],[0,-1]]`. Its profile explicitly records field splitting and excludes
it from the general module authority; it performs no external I/O.

## Book And Renderer Workflow

The book is a first-class exposition artifact under `book/`. Its
chapter files are authoring sources; the ignored
`print/public/emdash-book.md` file is deterministic generated input for
the renderer. Book theorem-like claims use the four statuses defined in
`book/STYLE.md` and checked claims cite `book/evidence.json`.

The current checked distribution book is the draft expanded development
edition `0.8.3-dev`, dated 2026-09-11: 46 ordered sources, 184 cited evidence
claims, 3,397 mathematical spans, 409 tagged Letter pages and 19 embedded
fonts. Its PDF SHA-256 is
`3bf4c6173cb96e1e7c1e80cbce59c574cf7361f243eb271e54fb22f3e52dbd54`.
The overview is `0.3.1-dev`, also dated 2026-09-11, with 19 tagged Letter
pages, 14 embedded fonts and PDF SHA-256
`bd42f3a9a8e519e24339bf5f8c253c6b00b4e8272d8b205763f501a23415c152`.
Both have byte-identical repeated exports and checked promoted copies in
the root `docs/` distribution paths. Both now contain the book self-reference,
Book DOI and Code links in opening material and bibliography/references.

The overview's 18-page ceiling was explicitly removed by the user.
`pageBudget.maximum = null` disables only that ceiling; lower-bound sanity,
resource limits, metadata, nonblank pages, links, fonts and rendering checks
remain. Numeric maxima still constrain bounded article profiles. The
publication/registry tests exercise both policies. Visual review corrected
two stranded article headings with existing full-width source groups and
split two overwide equations; no renderer CSS change was retained.

Chapter 31 and its appendices explain
the coherent K/Q presentations, derived whole H, direct and whole connecting
interfaces, three checked window interiors, finite iterator and retained
proof-CAS model interpretation. A worked nonsplit two-degree example now
traces the retained matrices, zero-composite witness and whole-H/model
bindings; its exact matrices and presentations have a focused native
regression. Source, browser, PDF and affected-page visual checks pass; earlier
draft artifacts remain preserved. The final symbolic zero-endpoint attachment remains
explicitly user-deferred, separate from the checked finite iterator and the
complete native endpoint calculations. Supplied model normality and trusted
presentation semantics are distinguished from computed matrix equations.
The [final boundary audit](../../docs/TYPESCRIPT_EMDASH_HOMOLOGY_FINAL_BOUNDARY_AUDIT.md)
records closure of the requested remainder and the inherited foundational
qualification; this book update is not a consistency certificate.
The [publication continuation](../../docs/TYPESCRIPT_EMDASH_BOUNDED_LONG_EXACT_HOMOLOGY_AND_BOOK_PLAN.md#documentation-and-publication-continuation)
records the user's GitHub authorization, exact artifact identities and
delivery verification. It does not create a new Zenodo deposit or npm release.

```bash
./scripts/pnpmw run book:assemble
./scripts/pnpmw run book:typography
./scripts/pnpmw run book:check
./scripts/pnpmw run book:render
```

Run these commands from the Git root. A fresh checkout or worktree is prepared
with `./scripts/bootstrap-worktree.sh`.

`book:typography` rejects TeX commands hidden in Markdown code spans,
suspicious bare TeX control words in math, raw TeX in prose, and strict KaTeX
parse failures. `book:check` verifies that typography gate together with
source order, attribution/provenance, anchors and links, evidence
declarations/reviewers, generated freshness, and embedded diagram schemas.
`book:render` adds a local-asset, bounded browser
pagination check. Renderer implementation and optional local upstream-package
instructions live in `print/README.md`; prose style and licensing live
in `book/STYLE.md`, `book/CREDITS.md`, and
`book/LICENSE.md`.

The book must describe `BNat` as a separate model and present the
directed normalization cell before the hom-discreteness equality. A physical
split of `emdash3_2.lp` is not a prerequisite for book development.

## Current Deferred Boundaries

The following remain explicit future work rather than hidden assumptions:

- full general dependent adjunctions `Sigma_F ⊣ F^* ⊣ Pi_F` along an arbitrary
  functor `F`, including the planned comma/right-Kan `Pi_along_func`
  infrastructure. The selected slice chain `Sigma_u ⊣ u* ⊣ Pi_u` is already
  active and is not this deferred general construction;
- remaining displayed structural logic and product/curry compatibility; the
  transparent Cat-valued sibling product now has fixed-base
  projection/pairing, derived swap/diagonal, point/full/capped action, both
  universal-property betas, and same-base `Product_map_func` transport, while
  universe-level projection transfors, raw kernel pullback stability, a
  global `Functord_cat` product conversion, dependent-chain exchange, and
  full family base-two-cell action remain open;
- a named `section_total` presentation facade and packaged projection laws;
  its transparent expression and the general
  `sigma_pullback_total_func(F,D)` base-change totalization are active;
- semantic uncurry action on arbitrary transfors;
- a named public facade varying higher arrows between ordinary transfors, and
  a complete recursive simplicial/omega interface beyond the active whole
  post/left and pre/right surfaces. The existing second `homd_`/Sigma internal
  action has already passed one current-source, no-associativity tetrahedral
  probe, so that validated generic action is not itself an open gap;
- the arrow action of `sigma_intro_tapp0_func`;
- off-diagonal `tapp1_*` projections for `sigma_map_transf` beyond its current
  point-component computation;
- a fully internalized general coend/coinserter semantics for profunctor tensor;
- general tensor associativity/coherence and complete co-Yoneda equivalences;
- dependent elimination and semantic collage construction for primitive join;
- CommRing lifting and left exactness of the now-constructed fixed-site
  Cat-valued direct-cover reflector, together with slice transport and
  locally ringed scheme packaging; the rigid Cat-valued `Sheaf_cat` facade
  and existing `SheafificationCapability` are already instantiated;
- an inductive/HIT presentation of generated topology with derivation
  induction or executable cover normal forms. The active impredicative
  intersection already supplies proposition-valued least generated topology,
  including the direct big-affine Zariski specialization, without truncating
  witness-rich presentations;
- specialized higher `fapp1*` projections of `Hom_tele_func` beyond current
  demand;
- raw unreified-path observer computation, reverse pointwise-to-coherent-core
  assembly, and consumer-led core-universe inclusion functors. A fully native
  two-sided OneCat object-equality/ordinary-isomorphism equivalence remains
  optional future work; the former compatibility decoder, its theorem, and
  its reviewer clients are already deleted and are not prerequisites;
- generic abstraction of the completed walking-endomorphism presentation,
  full functor-category initiality, a displayed dependent path-action/section
  construction, source action for the now-active category-indexed
  `Groupoidify(C)`, the resulting `Groupoidify_func`/`Path_cat_func`
  adjunction, and general higher-inductive categories or pushouts. The generic
  formation, whole unit/recursor, arbitrary-target mapping equivalence,
  compositor observation, and WalkingArrow--Interval recovery are already
  active. Ordinary raw-function `path_map_func` is the complete canonical
  nondependent action. A future exceptional former may add a local comparison
  theorem, and a future dependent consumer may motivate the displayed
  construction, but neither reinstates a generic selected-action registry by
  default;
- a finalized parser/surface language;
- module splitting of the single kernel file after comment/section boundaries
  stabilize.

Consult `INDEX.md` for the active plan owning a deferred item. Do not copy a
constructor-local law from an older plan without first rechecking the current
generic owner.

## Retirement And Recovery Policy

The v3.1 and v2 baselines are retired from normal checking and design work.
Their surviving lessons are represented in the active source, this SOP,
Foundations, canonical syntax, current plans, and the v2 retirement audit.

Infinity Codex uses the Git-root `.codex/hooks.json` and shared
`scripts/infinity_codex.py` for launches from either the repository root or
this package. There is intentionally no nested `emdash2/.codex/hooks.json`,
because Codex would run both matching layers. Response archives remain under
this package's ignored `tmp/ai-responses/` for continuity and are recovery
evidence only. Authority remains:

```text
active code/SOP -> active plan and side-task ledger
                -> explicitly linked decision responses -> raw archive.
```

After compaction/interruption, re-read the active authorities and task plan,
inspect staged/unstaged diffs, relocate symbols with `rg`, and run a bounded
baseline check before continuing.
