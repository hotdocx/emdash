/*
  Supplied reflective sheaf theories and commutative-ringed sites.

  A bare Grothendieck topology does not construct a sheaf category or a
  sheafification functor.  This module instead exposes the assumption-explicit
  capability needed by the computational scheme MVP:

    include  : Sheaf(K,T,V) -> Functor(K^op,V)
    sheafify : Functor(K^op,V) -> Sheaf(K,T,V)
    sheafify -| include.

  The adjunction is required to be reflective at its exact counit components.
  This faithfully replaces the historical strict
  `mod_smod(smod_mod R) -> R` fold without installing a global rewrite.

  The existing adjunction/profunctor mate comparison supplies whole internal
  glue and unglue operations for arbitrary diagram shapes.  Their action,
  naturality, and cancellation remain at the generic Adjunction,
  ProfComparison, and DefIso owners.  A reflective commutative-ringed site
  then packages one CommRing-valued sheaf together with that stronger
  capability and exposes its underlying whole presheaf through the supplied
  inclusion functor.  The unqualified weaker notion remains available for a
  later consumer that should not carry chosen sheafification.

  This rule-free module does not construct sheafification from a topology,
  prove descent or left exactness, generate a topology, assert local-ring
  stalks, or define a scheme.
*/

require open emdash.emdash3_2_sites;
require open emdash.emdash3_2_commutative_algebra_presheaves;

// Topology- and value-category-indexed category of supplied sheaves.
injective symbol Sheaf_cat
  [K : Cat]
  (T : τ (@GrothTopology K))
  (V : Cat)
  : Cat;

// Transparent adjunction data before the reflector condition is imposed.
symbol SheafAdjunctionData
  [K : Cat]
  (T : τ (@GrothTopology K))
  (V : Cat)
  : Grpd
≔ `Σ_ include : τ (@Functor
      (@Sheaf_cat K T V)
      (@Functor_cat (Op_cat K) V)),
   `Σ_ sheafify : τ (@Functor
      (@Functor_cat (Op_cat K) V)
      (@Sheaf_cat K T V)),
      @Adjunction
        (@Functor_cat (Op_cat K) V)
        (@Sheaf_cat K T V)
        sheafify
        include;

// Constructor for the transparent adjunction package.
symbol sheaf_adjunction_intro
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (include : τ (@Functor
      (@Sheaf_cat K T V)
      (@Functor_cat (Op_cat K) V)))
  (sheafify : τ (@Functor
      (@Functor_cat (Op_cat K) V)
      (@Sheaf_cat K T V)))
  (adjunction : τ (@Adjunction
      (@Functor_cat (Op_cat K) V)
      (@Sheaf_cat K T V)
      sheafify
      include))
  : τ (@SheafAdjunctionData K T V)
≔ @Struct_sigma
    (@Functor
      (@Sheaf_cat K T V)
      (@Functor_cat (Op_cat K) V))
    (λ i : τ (@Functor
        (@Sheaf_cat K T V)
        (@Functor_cat (Op_cat K) V)),
      `Σ_ a : τ (@Functor
          (@Functor_cat (Op_cat K) V)
          (@Sheaf_cat K T V)),
        @Adjunction
          (@Functor_cat (Op_cat K) V)
          (@Sheaf_cat K T V)
          a
          i)
    include
    (@Struct_sigma
      (@Functor
        (@Functor_cat (Op_cat K) V)
        (@Sheaf_cat K T V))
      (λ a : τ (@Functor
          (@Functor_cat (Op_cat K) V)
          (@Sheaf_cat K T V)),
        @Adjunction
          (@Functor_cat (Op_cat K) V)
          (@Sheaf_cat K T V)
          a
          include)
      sheafify
      adjunction);

// Whole inclusion functor selected by the adjunction data.
symbol sheaf_adjunction_include
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafAdjunctionData K T V))
  : τ (@Functor
      (@Sheaf_cat K T V)
      (@Functor_cat (Op_cat K) V))
≔ sigma_Fst S;

// Whole sheafification functor selected by the adjunction data.
symbol sheaf_adjunction_sheafify
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafAdjunctionData K T V))
  : τ (@Functor
      (@Functor_cat (Op_cat K) V)
      (@Sheaf_cat K T V))
≔ sigma_Fst (sigma_Snd S);

// Existing indexed adjunction evidence for the two selected whole functors.
symbol sheaf_adjunction_evidence
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafAdjunctionData K T V))
  : τ (@Adjunction
      (@Functor_cat (Op_cat K) V)
      (@Sheaf_cat K T V)
      (@sheaf_adjunction_sheafify K T V S)
      (@sheaf_adjunction_include K T V S))
≔ sigma_Snd (sigma_Snd S);

// Exact counit component a(include(R)) -> R at a supplied sheaf object.
symbol sheaf_adjunction_counit_at
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafAdjunctionData K T V))
  (R : τ (Obj (@Sheaf_cat K T V)))
  : τ (Hom
      (@Sheaf_cat K T V)
      (@fapp0
        (@Functor_cat (Op_cat K) V)
        (@Sheaf_cat K T V)
        (@sheaf_adjunction_sheafify K T V S)
        (@fapp0
          (@Sheaf_cat K T V)
          (@Functor_cat (Op_cat K) V)
          (@sheaf_adjunction_include K T V S)
          R))
      R)
≔ @tapp0_fapp0
    (@Sheaf_cat K T V)
    (@Sheaf_cat K T V)
    (@comp_cat_fapp0
      (@Sheaf_cat K T V)
      (@Functor_cat (Op_cat K) V)
      (@Sheaf_cat K T V)
      (@sheaf_adjunction_sheafify K T V S)
      (@sheaf_adjunction_include K T V S))
    (@id_func (@Sheaf_cat K T V))
    R
    (@counit_adj_transf
      (@Functor_cat (Op_cat K) V)
      (@Sheaf_cat K T V)
      (@sheaf_adjunction_sheafify K T V S)
      (@sheaf_adjunction_include K T V S)
      (@sheaf_adjunction_evidence K T V S));

/*
  Reflector property.

  Fixing the forward arrow to the actual counit component prevents an
  unrelated equivalence between the same endpoints from masquerading as the
  reflection law.  OmegaEquivAlong supplies internal inverse arrows and both
  cancellation paths without demanding a strict object rewrite.
*/
symbol IsSheafificationReflector
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafAdjunctionData K T V))
  : Grpd
≔ @Pi_grpd
    (Obj (@Sheaf_cat K T V))
    (λ R : τ (Obj (@Sheaf_cat K T V)),
      @OmegaEquivAlong
        (@Sheaf_cat K T V)
        (@fapp0
          (@Functor_cat (Op_cat K) V)
          (@Sheaf_cat K T V)
          (@sheaf_adjunction_sheafify K T V S)
          (@fapp0
            (@Sheaf_cat K T V)
            (@Functor_cat (Op_cat K) V)
            (@sheaf_adjunction_include K T V S)
            R))
        R
        (@sheaf_adjunction_counit_at K T V S R));

// Supplied sheafification is adjunction data plus its reflector property.
symbol SheafificationCapability
  [K : Cat]
  (T : τ (@GrothTopology K))
  (V : Cat)
  : Grpd
≔ `Σ_ S : τ (@SheafAdjunctionData K T V),
    @IsSheafificationReflector K T V S;

// Constructor for a supplied reflective sheafification capability.
symbol sheafification_capability_intro
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafAdjunctionData K T V))
  (reflects : τ (@IsSheafificationReflector K T V S))
  : τ (@SheafificationCapability K T V)
≔ @Struct_sigma
    (@SheafAdjunctionData K T V)
    (λ A : τ (@SheafAdjunctionData K T V),
      @IsSheafificationReflector K T V A)
    S reflects;

// Underlying whole adjunction data of a supplied sheafification capability.
symbol sheafification_adjunction_data
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafificationCapability K T V))
  : τ (@SheafAdjunctionData K T V)
≔ sigma_Fst S;

// Reflector evidence at the exact counit components.
symbol sheafification_reflector
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafificationCapability K T V))
  : τ (@IsSheafificationReflector
      K T V (@sheafification_adjunction_data K T V S))
≔ sigma_Snd S;

// Whole inclusion functor of a supplied sheafification capability.
symbol sheaf_include_func
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafificationCapability K T V))
  : τ (@Functor
      (@Sheaf_cat K T V)
      (@Functor_cat (Op_cat K) V))
≔ @sheaf_adjunction_include
    K T V (@sheafification_adjunction_data K T V S);

// Whole reflector functor of a supplied sheafification capability.
symbol sheafify_func
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafificationCapability K T V))
  : τ (@Functor
      (@Functor_cat (Op_cat K) V)
      (@Sheaf_cat K T V))
≔ @sheaf_adjunction_sheafify
    K T V (@sheafification_adjunction_data K T V S);

// Indexed adjunction evidence of the supplied reflective capability.
symbol sheafification_adjunction
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafificationCapability K T V))
  : τ (@Adjunction
      (@Functor_cat (Op_cat K) V)
      (@Sheaf_cat K T V)
      (@sheafify_func K T V S)
      (@sheaf_include_func K T V S))
≔ @sheaf_adjunction_evidence
    K T V (@sheafification_adjunction_data K T V S);

// Exact reflective counit component exposed through the full capability.
symbol sheafification_counit_at
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafificationCapability K T V))
  (R : τ (Obj (@Sheaf_cat K T V)))
  : τ (Hom
      (@Sheaf_cat K T V)
      (@fapp0
        (@Functor_cat (Op_cat K) V)
        (@Sheaf_cat K T V)
        (@sheafify_func K T V S)
        (@fapp0
          (@Sheaf_cat K T V)
          (@Functor_cat (Op_cat K) V)
          (@sheaf_include_func K T V S)
          R))
      R)
≔ @sheaf_adjunction_counit_at
    K T V (@sheafification_adjunction_data K T V S) R;

/*
  Whole internal sheafification mate.

  For M:I->Psh and H:J->Sheaf, this is

    Hom_Sheaf(sheafify M,H) ~= Hom_Psh(M,include H).

  Arbitrary I, J, and incoming profunctor P retain diagram action and
  naturality internally.  No objectwise naturality field is introduced.
*/
symbol sheafification_mate
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafificationCapability K T V))
  [I J : Cat]
  (M : τ (@Functor I (@Functor_cat (Op_cat K) V)))
  (H : τ (@Functor J (@Sheaf_cat K T V)))
  : τ (ProfComparison
      (@Hom_prof_along
        I J
        (@Sheaf_cat K T V)
        (@comp_cat_fapp0
          I
          (@Functor_cat (Op_cat K) V)
          (@Sheaf_cat K T V)
          (@sheafify_func K T V S)
          M)
        H)
      (@Hom_prof_along
        I J
        (@Functor_cat (Op_cat K) V)
        M
        (@comp_cat_fapp0
          J
          (@Sheaf_cat K T V)
          (@Functor_cat (Op_cat K) V)
          (@sheaf_include_func K T V S)
          H)))
≔ @Adjunction_hom_prof_comparison_along
    (@Functor_cat (Op_cat K) V)
    (@Sheaf_cat K T V)
    (@sheafify_func K T V S)
    (@sheaf_include_func K T V S)
    (@sheafification_adjunction K T V S)
    I J M H;

// Glue a whole profunctor map by pulling it through the adjunction mate.
symbol sheafification_glue
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafificationCapability K T V))
  [I J : Cat]
  (M : τ (@Functor I (@Functor_cat (Op_cat K) V)))
  (H : τ (@Functor J (@Sheaf_cat K T V)))
  [P : τ (Prof I J)]
  (r : τ (ProfMap
      P
      (@Hom_prof_along
        I J
        (@Functor_cat (Op_cat K) V)
        M
        (@comp_cat_fapp0
          J
          (@Sheaf_cat K T V)
          (@Functor_cat (Op_cat K) V)
          (@sheaf_include_func K T V S)
          H))))
  : τ (ProfMap
      P
      (@Hom_prof_along
        I J
        (@Sheaf_cat K T V)
        (@comp_cat_fapp0
          I
          (@Functor_cat (Op_cat K) V)
          (@Sheaf_cat K T V)
          (@sheafify_func K T V S)
          M)
        H))
≔ @prof_comparison_pull
    I J
    _ _
    (@sheafification_mate K T V S I J M H)
    P r;

// Forget/unglue by pushing a whole map through the same mate comparison.
symbol sheafification_unglue
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafificationCapability K T V))
  [I J : Cat]
  (M : τ (@Functor I (@Functor_cat (Op_cat K) V)))
  (H : τ (@Functor J (@Sheaf_cat K T V)))
  [P : τ (Prof I J)]
  (r : τ (ProfMap
      P
      (@Hom_prof_along
        I J
        (@Sheaf_cat K T V)
        (@comp_cat_fapp0
          I
          (@Functor_cat (Op_cat K) V)
          (@Sheaf_cat K T V)
          (@sheafify_func K T V S)
          M)
        H)))
  : τ (ProfMap
      P
      (@Hom_prof_along
        I J
        (@Functor_cat (Op_cat K) V)
        M
        (@comp_cat_fapp0
          J
          (@Sheaf_cat K T V)
          (@Functor_cat (Op_cat K) V)
          (@sheaf_include_func K T V S)
          H)))
≔ @prof_comparison_push
    I J
    _ _
    (@sheafification_mate K T V S I J M H)
    P r;

/*
  Commutative-ringed site on a fixed category K.

  The nested Sigma retains the chosen topology, its supplied reflective
  CommRing-valued sheaf theory, and one structure-sheaf object.  A locally
  ringed condition and affine atlas remain separate scheme-layer data.
*/
symbol ReflectiveCommRingedSite (K : Cat) : Grpd
≔ `Σ_ T : τ (@GrothTopology K),
   `Σ_ S : τ (@SheafificationCapability K T CommRing_cat),
      Obj (@Sheaf_cat K T CommRing_cat);

// Constructor for a reflective commutative-ringed site on K.
symbol reflective_comm_ringed_site_intro
  [K : Cat]
  (T : τ (@GrothTopology K))
  (S : τ (@SheafificationCapability K T CommRing_cat))
  (O : τ (Obj (@Sheaf_cat K T CommRing_cat)))
  : τ (@ReflectiveCommRingedSite K)
≔ @Struct_sigma
    (@GrothTopology K)
    (λ J : τ (@GrothTopology K),
      `Σ_ A : τ (@SheafificationCapability K J CommRing_cat),
        Obj (@Sheaf_cat K J CommRing_cat))
    T
    (@Struct_sigma
      (@SheafificationCapability K T CommRing_cat)
      (λ A : τ (@SheafificationCapability K T CommRing_cat),
        Obj (@Sheaf_cat K T CommRing_cat))
      S O);

// Selected Grothendieck topology of a reflective commutative-ringed site.
symbol reflective_comm_ringed_site_topology
  [K : Cat]
  (X : τ (@ReflectiveCommRingedSite K))
  : τ (@GrothTopology K)
≔ sigma_Fst X;

// Selected reflective CommRing-valued sheaf theory.
symbol reflective_comm_ringed_site_sheafification
  [K : Cat]
  (X : τ (@ReflectiveCommRingedSite K))
  : τ (@SheafificationCapability
      K
      (@reflective_comm_ringed_site_topology K X)
      CommRing_cat)
≔ sigma_Fst (sigma_Snd X);

// Selected structure-sheaf object in the supplied sheaf category.
symbol reflective_comm_ringed_site_structure_sheaf
  [K : Cat]
  (X : τ (@ReflectiveCommRingedSite K))
  : τ (Obj (@Sheaf_cat
      K
      (@reflective_comm_ringed_site_topology K X)
      CommRing_cat))
≔ sigma_Snd (sigma_Snd X);

// Underlying whole CommRing-valued presheaf of the structure sheaf.
symbol reflective_comm_ringed_site_underlying_psh
  [K : Cat]
  (X : τ (@ReflectiveCommRingedSite K))
  : τ (@CommRingPsh K)
≔ @fapp0
    (@Sheaf_cat
      K
      (@reflective_comm_ringed_site_topology K X)
      CommRing_cat)
    (@CommRingPsh_cat K)
    (@sheaf_include_func
      K
      (@reflective_comm_ringed_site_topology K X)
      CommRing_cat
      (@reflective_comm_ringed_site_sheafification K X))
    (@reflective_comm_ringed_site_structure_sheaf K X);
