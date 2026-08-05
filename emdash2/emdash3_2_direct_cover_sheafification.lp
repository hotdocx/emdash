/*
  Constructed Cat-valued sheafification from direct cover completion.

  At Cat_cat, the existing rigid Sheaf_cat facade is realized as topology-local
  Cat-valued presheaves.  Its inclusion forgets locality, while the direct
  cover-completion reflector lands back in the same facade.  Whole Hom
  universality supplies the indexed adjunction; its unit computes to the HIT
  return map and its counit computes to recursion from the identity seed.
  The recursor beta and topology-local eta laws derive both counit
  cancellations and hence the existing fixed-counit SheafificationCapability.

  Arbitrary value categories remain opaque.  The raw
  Functor_cat(Op_cat(K),Cat_cat) index appears only at the generic supplied-
  capability boundary; Psh_cat(K) remains the rigid computational owner.
*/

require open emdash.emdash3_2_direct_cover_completion_universality;
require open emdash.emdash3_2_ringed_sites;

// Proof-time only: direct comparison required by the generic sheaf capability.
unif_rule
  @Psh_cat $K
  ≡ @Functor_cat $K0 Cat_cat
  ↪ [ (Op_cat $K) ≡ $K0 ];

symbol CatValuedSheafData
  [K : Cat]
  (T : τ (@GrothTopology K))
  : Grpd
≔ `Σ_ P : τ (@Psh K), @IsTopologyLocalPsh K T P;

symbol cat_valued_sheaf_intro
  [K : Cat]
  [T : τ (@GrothTopology K)]
  (P : τ (@Psh K))
  (local : τ (@IsTopologyLocalPsh K T P))
  : τ (@CatValuedSheafData K T)
≔ Struct_sigma P local;

symbol cat_valued_sheaf_carrier
  [K : Cat]
  [T : τ (@GrothTopology K)]
  (X : τ (@CatValuedSheafData K T))
  : τ (@Psh K)
≔ sigma_Fst X;

symbol cat_valued_sheaf_local
  [K : Cat]
  [T : τ (@GrothTopology K)]
  (X : τ (@CatValuedSheafData K T))
  : τ (@IsTopologyLocalPsh K T (@cat_valued_sheaf_carrier K T X))
≔ sigma_Snd X;

// Cat-valued specialization of the existing sheaf facade.
rule Obj (@Sheaf_cat $K $T Cat_cat)
  ↪ @CatValuedSheafData $K $T;

rule Hom_cat (@Sheaf_cat $K $T Cat_cat) $X $Y
  ↪ Hom_cat
      (@Psh_cat $K)
      (@cat_valued_sheaf_carrier $K $T $X)
      (@cat_valued_sheaf_carrier $K $T $Y);

rule @id (@Sheaf_cat $K $T Cat_cat) $X
  ↪ @id
      (@Psh_cat $K)
      (@cat_valued_sheaf_carrier $K $T $X);

// lhs-audit: keep 2,3,4 -- the carrier projections are required on the RHS.
rule @comp_fapp0
      (@Sheaf_cat $K $T Cat_cat) $X $Y $Z $g $f
  ↪ @comp_fapp0
      (@Psh_cat $K)
      (@cat_valued_sheaf_carrier $K $T $X)
      (@cat_valued_sheaf_carrier $K $T $Y)
      (@cat_valued_sheaf_carrier $K $T $Z)
      $g $f;

// Concrete Cat-valued inclusion into the public Psh facade.
injective symbol cat_valued_sheaf_include_psh_func
  [K : Cat]
  (T : τ (@GrothTopology K))
  : τ (@Functor (@Sheaf_cat K T Cat_cat) (@Psh_cat K));

rule @fapp0 _ _
      (@cat_valued_sheaf_include_psh_func $K $T) $X
  ↪ @cat_valued_sheaf_carrier $K $T $X;

constant symbol cat_valued_sheaf_include_psh_hom_action
  [K : Cat]
  (T : τ (@GrothTopology K))
  (X Y : τ (Obj (@Sheaf_cat K T Cat_cat)))
  : τ (@=
      (Obj (@Functor_cat
        (Hom_cat (@Sheaf_cat K T Cat_cat) X Y)
        (Hom_cat
          (@Psh_cat K)
          (@cat_valued_sheaf_carrier K T X)
          (@cat_valued_sheaf_carrier K T Y))))
      (@fapp1_func
        (@Sheaf_cat K T Cat_cat)
        (@Psh_cat K)
        (@cat_valued_sheaf_include_psh_func K T)
        X Y)
      (@id_func
        (Hom_cat
          (@Psh_cat K)
          (@cat_valued_sheaf_carrier K T X)
          (@cat_valued_sheaf_carrier K T Y))));

// Completion lands directly in the existing Cat-valued sheaf facade.
injective symbol direct_cover_sheafification_func
  [K : Cat]
  (T : τ (@GrothTopology K))
  : τ (@Functor (@Psh_cat K) (@Sheaf_cat K T Cat_cat));

rule @fapp0 _ _ (@direct_cover_sheafification_func $K $T) $P
  ↪ @cat_valued_sheaf_intro
      $K $T
      (@DirectCoverCompletionPsh $K $T $P)
      (@direct_cover_completion_is_topology_local $K $T $P);

symbol direct_cover_sheafification_unit_postcomp_func
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P Q : τ (@Psh K))
  : τ (@Functor
      (Hom_cat (@Psh_cat K) P Q)
      (Hom_cat
        (@Psh_cat K) P (@DirectCoverCompletionPsh K T Q)))
≔ @hom_postcomp_func
    (@Psh_cat K)
    (@Psh_cat K)
    (@id_func (@Psh_cat K))
    P Q
    (@DirectCoverCompletionPsh K T Q)
    (@direct_cover_completion_unit K T Q);

symbol direct_cover_sheafification_selected_hom_func
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P Q : τ (@Psh K))
  : τ (@Functor
      (Hom_cat (@Psh_cat K) P Q)
      (Hom_cat
        (@Psh_cat K)
        (@DirectCoverCompletionPsh K T P)
        (@DirectCoverCompletionPsh K T Q)))
≔ @comp_cat_fapp0
    (Hom_cat (@Psh_cat K) P Q)
    (Hom_cat (@Psh_cat K) P (@DirectCoverCompletionPsh K T Q))
    (Hom_cat
      (@Psh_cat K)
      (@DirectCoverCompletionPsh K T P)
      (@DirectCoverCompletionPsh K T Q))
    (@direct_cover_completion_rec_func
      K T P
      (@DirectCoverCompletionPsh K T Q)
      (@topology_local_direct_cover_algebra
        K T
        (@DirectCoverCompletionPsh K T Q)
        (@direct_cover_completion_is_topology_local K T Q)))
    (@direct_cover_sheafification_unit_postcomp_func K T P Q);

constant symbol direct_cover_sheafification_hom_action
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P Q : τ (@Psh K))
  : τ (@=
      (Obj (@Functor_cat
        (Hom_cat (@Psh_cat K) P Q)
        (Hom_cat
          (@Psh_cat K)
          (@DirectCoverCompletionPsh K T P)
          (@DirectCoverCompletionPsh K T Q))))
      (@fapp1_func
        (@Psh_cat K)
        (@Sheaf_cat K T Cat_cat)
        (@direct_cover_sheafification_func K T)
        P Q)
      (@direct_cover_sheafification_selected_hom_func K T P Q));

// The whole Hom universal property supplies the indexed adjunction theorem.
constant symbol direct_cover_sheafification_adjunction
  [K : Cat]
  (T : τ (@GrothTopology K))
  : τ (@Adjunction
      (@Functor_cat (Op_cat K) Cat_cat)
      (@Sheaf_cat K T Cat_cat)
      (@direct_cover_sheafification_func K T)
      (@cat_valued_sheaf_include_psh_func K T));

// The same owners instantiate the existing generic adjunction-data package.
symbol direct_cover_sheafification_adjunction_data
  [K : Cat]
  (T : τ (@GrothTopology K))
  : τ (@SheafAdjunctionData K T Cat_cat)
≔ @sheaf_adjunction_intro
    K T Cat_cat
    (@cat_valued_sheaf_include_psh_func K T)
    (@direct_cover_sheafification_func K T)
    (@direct_cover_sheafification_adjunction K T);

// The adjunction unit component is the categorical-HIT return map.
rule @tapp0_fapp0 _ _ _ _ $P
      (@unit_adj_transf
        (@Functor_cat (Op_cat $K) Cat_cat)
        (@Sheaf_cat $K $T Cat_cat)
        (@direct_cover_sheafification_func $K $T)
        (@cat_valued_sheaf_include_psh_func $K $T)
        (@direct_cover_sheafification_adjunction $K $T))
  ↪ @direct_cover_completion_unit $K $T $P;

// At a local sheaf, the adjunction counit is recursion from the identity seed.
rule @tapp0_fapp0 _ _ _ _ $Y
      (@counit_adj_transf
        (@Functor_cat (Op_cat $K) Cat_cat)
        (@Sheaf_cat $K $T Cat_cat)
        (@direct_cover_sheafification_func $K $T)
        (@cat_valued_sheaf_include_psh_func $K $T)
        (@direct_cover_sheafification_adjunction $K $T))
  ↪ @direct_cover_completion_rec
      $K $T
      (@cat_valued_sheaf_carrier $K $T $Y)
      (@cat_valued_sheaf_carrier $K $T $Y)
      (@topology_local_direct_cover_algebra
        $K $T
        (@cat_valued_sheaf_carrier $K $T $Y)
        (@cat_valued_sheaf_local $K $T $Y))
      (@id
        (@Psh_cat $K)
        (@cat_valued_sheaf_carrier $K $T $Y));
symbol direct_cover_sheafification_counit_at
  [K : Cat]
  (T : τ (@GrothTopology K))
  (Y : τ (Obj (@Sheaf_cat K T Cat_cat)))
  : τ (Hom
      (@Psh_cat K)
      (@DirectCoverCompletionPsh
        K T (@cat_valued_sheaf_carrier K T Y))
      (@cat_valued_sheaf_carrier K T Y))
≔ @tapp0_fapp0
    (@Sheaf_cat K T Cat_cat)
    (@Sheaf_cat K T Cat_cat)
    (@comp_cat_fapp0
      (@Sheaf_cat K T Cat_cat)
      (@Functor_cat (Op_cat K) Cat_cat)
      (@Sheaf_cat K T Cat_cat)
      (@direct_cover_sheafification_func K T)
      (@cat_valued_sheaf_include_psh_func K T))
    (@id_func (@Sheaf_cat K T Cat_cat))
    Y
    (@counit_adj_transf
      (@Functor_cat (Op_cat K) Cat_cat)
      (@Sheaf_cat K T Cat_cat)
      (@direct_cover_sheafification_func K T)
      (@cat_valued_sheaf_include_psh_func K T)
      (@direct_cover_sheafification_adjunction K T));

// Evaluate the whole categorical-HIT eta law at one completion map.
symbol direct_cover_completion_rec_eta_local_at
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (local : τ (@IsTopologyLocalPsh K T Y))
  (h : τ (Hom
      (@Psh_cat K)
      (@DirectCoverCompletionPsh K T P)
      Y))
  : τ (@=
      (Hom
        (@Psh_cat K)
        (@DirectCoverCompletionPsh K T P)
        Y)
      (@fapp0
        (Hom_cat
          (@Psh_cat K)
          (@DirectCoverCompletionPsh K T P)
          Y)
        (Hom_cat
          (@Psh_cat K)
          (@DirectCoverCompletionPsh K T P)
          Y)
        (@comp_cat_fapp0
          (Hom_cat
            (@Psh_cat K)
            (@DirectCoverCompletionPsh K T P)
            Y)
          (Hom_cat (@Psh_cat K) P Y)
          (Hom_cat
            (@Psh_cat K)
            (@DirectCoverCompletionPsh K T P)
            Y)
          (@direct_cover_completion_rec_func
            K T P Y (@topology_local_direct_cover_algebra K T Y local))
          (@direct_cover_completion_unit_precomp_func K T P Y))
        h)
      h)
≔ @eq_ap
    (Obj (@Functor_cat
      (Hom_cat
        (@Psh_cat K)
        (@DirectCoverCompletionPsh K T P)
        Y)
      (Hom_cat
        (@Psh_cat K)
        (@DirectCoverCompletionPsh K T P)
        Y)))
    (Hom
      (@Psh_cat K)
      (@DirectCoverCompletionPsh K T P)
      Y)
    (λ F : τ (@Functor
        (Hom_cat
          (@Psh_cat K)
          (@DirectCoverCompletionPsh K T P)
          Y)
        (Hom_cat
          (@Psh_cat K)
          (@DirectCoverCompletionPsh K T P)
          Y)),
      @fapp0
        (Hom_cat
          (@Psh_cat K)
          (@DirectCoverCompletionPsh K T P)
          Y)
        (Hom_cat
          (@Psh_cat K)
          (@DirectCoverCompletionPsh K T P)
          Y)
        F h)
    _ _
    (@direct_cover_completion_rec_eta_local_func K T P Y local);

// The exact counit cancels the HIT unit by its runtime return beta.
symbol direct_cover_sheafification_counit_right_law
  [K : Cat]
  (T : τ (@GrothTopology K))
  (Y : τ (Obj (@Sheaf_cat K T Cat_cat)))
  : τ (@=
      (Hom
        (@Psh_cat K)
        (@cat_valued_sheaf_carrier K T Y)
        (@cat_valued_sheaf_carrier K T Y))
      (@comp_fapp0
        (@Psh_cat K)
        (@cat_valued_sheaf_carrier K T Y)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@cat_valued_sheaf_carrier K T Y)
        (@direct_cover_sheafification_counit_at K T Y)
        (@direct_cover_completion_unit
          K T (@cat_valued_sheaf_carrier K T Y)))
      (@id
        (@Psh_cat K)
        (@cat_valued_sheaf_carrier K T Y)))
≔ @direct_cover_completion_rec_beta_unit
    K T
    (@cat_valued_sheaf_carrier K T Y)
    (@cat_valued_sheaf_carrier K T Y)
    (@topology_local_direct_cover_algebra
      K T
      (@cat_valued_sheaf_carrier K T Y)
      (@cat_valued_sheaf_local K T Y))
    (@id
      (@Psh_cat K)
      (@cat_valued_sheaf_carrier K T Y));

// Proof-time presentation of precomposition by the unit as raw composition.
symbol direct_cover_sheafification_counit_precomp_raw_path
  [K : Cat]
  (T : τ (@GrothTopology K))
  (Y : τ (Obj (@Sheaf_cat K T Cat_cat)))
  : τ (@=
      (Hom
        (@Psh_cat K)
        (@cat_valued_sheaf_carrier K T Y)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y)))
      (@hom_precomp_along_fapp0
        (@Psh_cat K)
        (@Psh_cat K)
        (@id_func (@Psh_cat K))
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@cat_valued_sheaf_carrier K T Y)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@direct_cover_completion_unit
          K T (@cat_valued_sheaf_carrier K T Y))
        (@comp_fapp0
          (@Psh_cat K)
          (@DirectCoverCompletionPsh
            K T (@cat_valued_sheaf_carrier K T Y))
          (@cat_valued_sheaf_carrier K T Y)
          (@DirectCoverCompletionPsh
            K T (@cat_valued_sheaf_carrier K T Y))
          (@direct_cover_completion_unit
            K T (@cat_valued_sheaf_carrier K T Y))
          (@direct_cover_sheafification_counit_at K T Y)))
      (@comp_fapp0
        (@Psh_cat K)
        (@cat_valued_sheaf_carrier K T Y)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@comp_fapp0
          (@Psh_cat K)
          (@DirectCoverCompletionPsh
            K T (@cat_valued_sheaf_carrier K T Y))
          (@cat_valued_sheaf_carrier K T Y)
          (@DirectCoverCompletionPsh
            K T (@cat_valued_sheaf_carrier K T Y))
          (@direct_cover_completion_unit
            K T (@cat_valued_sheaf_carrier K T Y))
          (@direct_cover_sheafification_counit_at K T Y))
        (@direct_cover_completion_unit
          K T (@cat_valued_sheaf_carrier K T Y))))
≔ @eq_refl
    (Hom
      (@Psh_cat K)
      (@cat_valued_sheaf_carrier K T Y)
      (@DirectCoverCompletionPsh
        K T (@cat_valued_sheaf_carrier K T Y)))
    (@hom_precomp_along_fapp0
      (@Psh_cat K)
      (@Psh_cat K)
      (@id_func (@Psh_cat K))
      (@DirectCoverCompletionPsh
        K T (@cat_valued_sheaf_carrier K T Y))
      (@cat_valued_sheaf_carrier K T Y)
      (@DirectCoverCompletionPsh
        K T (@cat_valued_sheaf_carrier K T Y))
      (@direct_cover_completion_unit
        K T (@cat_valued_sheaf_carrier K T Y))
      (@comp_fapp0
        (@Psh_cat K)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@cat_valued_sheaf_carrier K T Y)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@direct_cover_completion_unit
          K T (@cat_valued_sheaf_carrier K T Y))
        (@direct_cover_sheafification_counit_at K T Y)));

// Reassociate `(unit o counit) o unit` around the counit-unit beta redex.
symbol direct_cover_sheafification_counit_precomp_assoc_path
  [K : Cat]
  (T : τ (@GrothTopology K))
  (Y : τ (Obj (@Sheaf_cat K T Cat_cat)))
  : τ (@=
      (Hom
        (@Psh_cat K)
        (@cat_valued_sheaf_carrier K T Y)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y)))
      (@comp_fapp0
        (@Psh_cat K)
        (@cat_valued_sheaf_carrier K T Y)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@comp_fapp0
          (@Psh_cat K)
          (@DirectCoverCompletionPsh
            K T (@cat_valued_sheaf_carrier K T Y))
          (@cat_valued_sheaf_carrier K T Y)
          (@DirectCoverCompletionPsh
            K T (@cat_valued_sheaf_carrier K T Y))
          (@direct_cover_completion_unit
            K T (@cat_valued_sheaf_carrier K T Y))
          (@direct_cover_sheafification_counit_at K T Y))
        (@direct_cover_completion_unit
          K T (@cat_valued_sheaf_carrier K T Y)))
      (@comp_fapp0
        (@Psh_cat K)
        (@cat_valued_sheaf_carrier K T Y)
        (@cat_valued_sheaf_carrier K T Y)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@direct_cover_completion_unit
          K T (@cat_valued_sheaf_carrier K T Y))
        (@comp_fapp0
          (@Psh_cat K)
          (@cat_valued_sheaf_carrier K T Y)
          (@DirectCoverCompletionPsh
            K T (@cat_valued_sheaf_carrier K T Y))
          (@cat_valued_sheaf_carrier K T Y)
          (@direct_cover_sheafification_counit_at K T Y)
          (@direct_cover_completion_unit
            K T (@cat_valued_sheaf_carrier K T Y)))))
≔ @eq_sym
    (Hom
      (@Psh_cat K)
      (@cat_valued_sheaf_carrier K T Y)
      (@DirectCoverCompletionPsh
        K T (@cat_valued_sheaf_carrier K T Y)))
    _ _
    (@comp_assoc
      (@Psh_cat K)
      (@cat_valued_sheaf_carrier K T Y)
      (@DirectCoverCompletionPsh
        K T (@cat_valued_sheaf_carrier K T Y))
      (@cat_valued_sheaf_carrier K T Y)
      (@DirectCoverCompletionPsh
        K T (@cat_valued_sheaf_carrier K T Y))
      (@direct_cover_completion_unit
        K T (@cat_valued_sheaf_carrier K T Y))
      (@direct_cover_sheafification_counit_at K T Y)
      (@direct_cover_completion_unit
        K T (@cat_valued_sheaf_carrier K T Y)));

// Replace the inner counit-unit composite by the identity.
symbol direct_cover_sheafification_counit_precomp_beta_path
  [K : Cat]
  (T : τ (@GrothTopology K))
  (Y : τ (Obj (@Sheaf_cat K T Cat_cat)))
  : τ (@=
      (Hom
        (@Psh_cat K)
        (@cat_valued_sheaf_carrier K T Y)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y)))
      (@comp_fapp0
        (@Psh_cat K)
        (@cat_valued_sheaf_carrier K T Y)
        (@cat_valued_sheaf_carrier K T Y)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@direct_cover_completion_unit
          K T (@cat_valued_sheaf_carrier K T Y))
        (@comp_fapp0
          (@Psh_cat K)
          (@cat_valued_sheaf_carrier K T Y)
          (@DirectCoverCompletionPsh
            K T (@cat_valued_sheaf_carrier K T Y))
          (@cat_valued_sheaf_carrier K T Y)
          (@direct_cover_sheafification_counit_at K T Y)
          (@direct_cover_completion_unit
            K T (@cat_valued_sheaf_carrier K T Y))))
      (@direct_cover_completion_unit
        K T (@cat_valued_sheaf_carrier K T Y)))
≔ @eq_ap
    (Hom
      (@Psh_cat K)
      (@cat_valued_sheaf_carrier K T Y)
      (@cat_valued_sheaf_carrier K T Y))
    (Hom
      (@Psh_cat K)
      (@cat_valued_sheaf_carrier K T Y)
      (@DirectCoverCompletionPsh
        K T (@cat_valued_sheaf_carrier K T Y)))
    (λ q : τ (Hom
        (@Psh_cat K)
        (@cat_valued_sheaf_carrier K T Y)
        (@cat_valued_sheaf_carrier K T Y)),
      @comp_fapp0
        (@Psh_cat K)
        (@cat_valued_sheaf_carrier K T Y)
        (@cat_valued_sheaf_carrier K T Y)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@direct_cover_completion_unit
          K T (@cat_valued_sheaf_carrier K T Y))
        q)
    _ _
    (@direct_cover_sheafification_counit_right_law K T Y);

// The two previous paths show that precomposition of the candidate composite
// is the unit seed selected by the local-target recursor.
symbol direct_cover_sheafification_counit_precomp_path
  [K : Cat]
  (T : τ (@GrothTopology K))
  (Y : τ (Obj (@Sheaf_cat K T Cat_cat)))
  : τ (@=
      (Hom
        (@Psh_cat K)
        (@cat_valued_sheaf_carrier K T Y)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y)))
      (@hom_precomp_along_fapp0
        (@Psh_cat K)
        (@Psh_cat K)
        (@id_func (@Psh_cat K))
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@cat_valued_sheaf_carrier K T Y)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@direct_cover_completion_unit
          K T (@cat_valued_sheaf_carrier K T Y))
        (@comp_fapp0
          (@Psh_cat K)
          (@DirectCoverCompletionPsh
            K T (@cat_valued_sheaf_carrier K T Y))
          (@cat_valued_sheaf_carrier K T Y)
          (@DirectCoverCompletionPsh
            K T (@cat_valued_sheaf_carrier K T Y))
          (@direct_cover_completion_unit
            K T (@cat_valued_sheaf_carrier K T Y))
          (@direct_cover_sheafification_counit_at K T Y)))
      (@direct_cover_completion_unit
        K T (@cat_valued_sheaf_carrier K T Y)))
≔ eq_trans
    (@direct_cover_sheafification_counit_precomp_raw_path K T Y)
    (eq_trans
      (@direct_cover_sheafification_counit_precomp_assoc_path K T Y)
      (@direct_cover_sheafification_counit_precomp_beta_path K T Y));

// HIT uniqueness at the local completion makes the unit the other inverse.
symbol direct_cover_sheafification_counit_left_law
  [K : Cat]
  (T : τ (@GrothTopology K))
  (Y : τ (Obj (@Sheaf_cat K T Cat_cat)))
  : τ (@=
      (Hom
        (@Psh_cat K)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y)))
      (@comp_fapp0
        (@Psh_cat K)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@cat_valued_sheaf_carrier K T Y)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@direct_cover_completion_unit
          K T (@cat_valued_sheaf_carrier K T Y))
        (@direct_cover_sheafification_counit_at K T Y))
      (@id
        (@Psh_cat K)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))))
≔ eq_trans
    (eq_sym
      (@direct_cover_completion_rec_eta_local_at
        K T
        (@cat_valued_sheaf_carrier K T Y)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@direct_cover_completion_is_topology_local
          K T (@cat_valued_sheaf_carrier K T Y))
        (@comp_fapp0
          (@Psh_cat K)
          (@DirectCoverCompletionPsh
            K T (@cat_valued_sheaf_carrier K T Y))
          (@cat_valued_sheaf_carrier K T Y)
          (@DirectCoverCompletionPsh
            K T (@cat_valued_sheaf_carrier K T Y))
          (@direct_cover_completion_unit
            K T (@cat_valued_sheaf_carrier K T Y))
          (@direct_cover_sheafification_counit_at K T Y))))
    (eq_trans
      (@eq_ap
        (Hom
          (@Psh_cat K)
          (@cat_valued_sheaf_carrier K T Y)
          (@DirectCoverCompletionPsh
            K T (@cat_valued_sheaf_carrier K T Y)))
        (Hom
          (@Psh_cat K)
          (@DirectCoverCompletionPsh
            K T (@cat_valued_sheaf_carrier K T Y))
          (@DirectCoverCompletionPsh
            K T (@cat_valued_sheaf_carrier K T Y)))
        (λ seed : τ (Hom
            (@Psh_cat K)
            (@cat_valued_sheaf_carrier K T Y)
            (@DirectCoverCompletionPsh
              K T (@cat_valued_sheaf_carrier K T Y))),
          @fapp0
            (Hom_cat
              (@Psh_cat K)
              (@cat_valued_sheaf_carrier K T Y)
              (@DirectCoverCompletionPsh
                K T (@cat_valued_sheaf_carrier K T Y)))
            (Hom_cat
              (@Psh_cat K)
              (@DirectCoverCompletionPsh
                K T (@cat_valued_sheaf_carrier K T Y))
              (@DirectCoverCompletionPsh
                K T (@cat_valued_sheaf_carrier K T Y)))
            (@direct_cover_completion_rec_func
              K T
              (@cat_valued_sheaf_carrier K T Y)
              (@DirectCoverCompletionPsh
                K T (@cat_valued_sheaf_carrier K T Y))
              (@topology_local_direct_cover_algebra
                K T
                (@DirectCoverCompletionPsh
                  K T (@cat_valued_sheaf_carrier K T Y))
                (@direct_cover_completion_is_topology_local
                  K T (@cat_valued_sheaf_carrier K T Y))))
            seed)
        _ _
        (@direct_cover_sheafification_counit_precomp_path K T Y))
      (@direct_cover_completion_rec_eta_local_at
        K T
        (@cat_valued_sheaf_carrier K T Y)
        (@DirectCoverCompletionPsh
          K T (@cat_valued_sheaf_carrier K T Y))
        (@direct_cover_completion_is_topology_local
          K T (@cat_valued_sheaf_carrier K T Y))
        (@id
          (@Psh_cat K)
          (@DirectCoverCompletionPsh
            K T (@cat_valued_sheaf_carrier K T Y)))));
symbol direct_cover_sheafification_reflected_object
  [K : Cat]
  (T : τ (@GrothTopology K))
  (Y : τ (Obj (@Sheaf_cat K T Cat_cat)))
  : τ (Obj (@Sheaf_cat K T Cat_cat))
≔ @fapp0
    (@Psh_cat K)
    (@Sheaf_cat K T Cat_cat)
    (@direct_cover_sheafification_func K T)
    (@fapp0
      (@Sheaf_cat K T Cat_cat)
      (@Psh_cat K)
      (@cat_valued_sheaf_include_psh_func K T)
      Y);

symbol direct_cover_sheafification_counit_inverse_at
  [K : Cat]
  (T : τ (@GrothTopology K))
  (Y : τ (Obj (@Sheaf_cat K T Cat_cat)))
  : τ (Hom
      (@Sheaf_cat K T Cat_cat)
      Y
      (@direct_cover_sheafification_reflected_object K T Y))
≔ @direct_cover_completion_unit
    K T (@cat_valued_sheaf_carrier K T Y);

// The derived left cancellation, viewed at the exact generic endpoints.
symbol direct_cover_sheafification_exact_left_law
  [K : Cat]
  (T : τ (@GrothTopology K))
  (Y : τ (Obj (@Sheaf_cat K T Cat_cat)))
  : τ (@=
      (Hom
        (@Sheaf_cat K T Cat_cat)
        (@direct_cover_sheafification_reflected_object K T Y)
        (@direct_cover_sheafification_reflected_object K T Y))
      (@comp_fapp0
        (@Sheaf_cat K T Cat_cat)
        (@direct_cover_sheafification_reflected_object K T Y)
        Y
        (@direct_cover_sheafification_reflected_object K T Y)
        (@direct_cover_sheafification_counit_inverse_at K T Y)
        (@direct_cover_sheafification_counit_at K T Y))
      (@id
        (@Sheaf_cat K T Cat_cat)
        (@direct_cover_sheafification_reflected_object K T Y)))
≔ @direct_cover_sheafification_counit_left_law K T Y;

// The runtime return beta, viewed at the exact generic endpoints.
symbol direct_cover_sheafification_exact_right_law
  [K : Cat]
  (T : τ (@GrothTopology K))
  (Y : τ (Obj (@Sheaf_cat K T Cat_cat)))
  : τ (@=
      (Hom
        (@Sheaf_cat K T Cat_cat)
        Y Y)
      (@comp_fapp0
        (@Sheaf_cat K T Cat_cat)
        Y
        (@direct_cover_sheafification_reflected_object K T Y)
        Y
        (@direct_cover_sheafification_counit_at K T Y)
        (@direct_cover_sheafification_counit_inverse_at K T Y))
      (@id (@Sheaf_cat K T Cat_cat) Y))
≔ @direct_cover_sheafification_counit_right_law K T Y;

// The exact adjunction counit is an equivalence in the realized sheaf facade.
// The exact adjunction counit is an equivalence in the realized sheaf facade.
symbol direct_cover_sheafification_reflector_at
  [K : Cat]
  (T : τ (@GrothTopology K))
  (Y : τ (Obj (@Sheaf_cat K T Cat_cat)))
  : τ (@OmegaEquivAlong
      (@Sheaf_cat K T Cat_cat)
      (@direct_cover_sheafification_reflected_object K T Y)
      Y
      (@direct_cover_sheafification_counit_at K T Y))
≔ @omega_equiv_along_intro
    (@Sheaf_cat K T Cat_cat)
    (@direct_cover_sheafification_reflected_object K T Y)
    Y
    (@direct_cover_sheafification_counit_at K T Y)
    (@direct_cover_sheafification_counit_inverse_at K T Y)
    (@direct_cover_sheafification_counit_inverse_at K T Y)
    (@direct_cover_sheafification_exact_left_law K T Y)
    (@direct_cover_sheafification_exact_right_law K T Y);
symbol direct_cover_sheafification_reflector
  [K : Cat]
  (T : τ (@GrothTopology K))
  : τ (@IsSheafificationReflector
      K T Cat_cat
      (@sheaf_adjunction_intro
        K T Cat_cat
        (@cat_valued_sheaf_include_psh_func K T)
        (@direct_cover_sheafification_func K T)
        (@direct_cover_sheafification_adjunction K T)))
≔ λ Y : τ (Obj (@Sheaf_cat K T Cat_cat)),
    @direct_cover_sheafification_reflector_at K T Y;

// The constructed fixed-site Cat-valued reflector inhabits the existing API.
symbol direct_cover_sheafification_capability
  [K : Cat]
  (T : τ (@GrothTopology K))
  : τ (@SheafificationCapability K T Cat_cat)
≔ @sheafification_capability_intro
    K T Cat_cat
    (@sheaf_adjunction_intro
      K T Cat_cat
      (@cat_valued_sheaf_include_psh_func K T)
      (@direct_cover_sheafification_func K T)
      (@direct_cover_sheafification_adjunction K T))
    (@direct_cover_sheafification_reflector K T);
