/*
  Fixed-ring finite presentations, morphisms, and representative agreement.

  Presentation maps retain the generator matrix F, a relation-coefficient
  matrix W, and the membership-oriented equation R_Q o W = F o R_P.
  Representative agreement similarly retains H with R_Q o H = F - G.
  These are explicit computational data, not quotient-module equality or a
  formal category of presentations.
*/

require open emdash.emdash3_2_commutative_algebra_finite_modules;

// Componentwise addition of matrix columns.
symbol comm_ring_matrix_add
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A B : τ (@CommRingMatrix R rows columns))
  : τ (@CommRingMatrix R rows columns)
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Function_grpd
        (@CommRingMatrix R rows columns0)
        (@Function_grpd
          (@CommRingMatrix R rows columns0)
          (@CommRingMatrix R rows columns0)))
    (λ _ : τ (@CommRingMatrix R rows zero),
      λ _ : τ (@CommRingMatrix R rows zero),
        @finite_family_nil (@CommRingVector R rows))
    (λ columns0 : τ Nat_grpd,
      λ rec : τ (@Function_grpd
        (@CommRingMatrix R rows columns0)
        (@Function_grpd
          (@CommRingMatrix R rows columns0)
          (@CommRingMatrix R rows columns0))),
      λ As : τ (@CommRingMatrix R rows (succ columns0)),
      λ Bs : τ (@CommRingMatrix R rows (succ columns0)),
        @finite_family_cons
          (@CommRingVector R rows) columns0
          (@comm_ring_vector_add R rows
            (@finite_family_head
              (@CommRingVector R rows) columns0 As)
            (@finite_family_head
              (@CommRingVector R rows) columns0 Bs))
          (rec
            (@finite_family_tail
              (@CommRingVector R rows) columns0 As)
            (@finite_family_tail
              (@CommRingVector R rows) columns0 Bs)))
    columns) A B;

// Componentwise additive inverse of matrix columns.
symbol comm_ring_matrix_neg
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows columns))
  : τ (@CommRingMatrix R rows columns)
≔ @finite_family_map
    (@CommRingVector R rows)
    (@CommRingVector R rows)
    (λ column : τ (@CommRingVector R rows),
      @comm_ring_vector_neg R rows column)
    columns A;

symbol comm_ring_matrix_sub
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A B : τ (@CommRingMatrix R rows columns))
  : τ (@CommRingMatrix R rows columns)
≔ @comm_ring_matrix_add R rows columns A
    (@comm_ring_matrix_neg R rows columns B);

// A finite presentation is generator rank, relation rank, and relation matrix.
symbol CommRingPresentation
  (R : τ CommRing)
  : Grpd
≔ `Σ_ generators : τ Nat_grpd,
    `Σ_ relations : τ Nat_grpd,
      @CommRingMatrix R generators relations;

symbol comm_ring_presentation_intro
  [R : τ CommRing]
  (generators relations : τ Nat_grpd)
  (matrix : τ (@CommRingMatrix R generators relations))
  : τ (@CommRingPresentation R)
≔ @Struct_sigma
    Nat_grpd
    (λ generators0 : τ Nat_grpd,
      `Σ_ relations0 : τ Nat_grpd,
        @CommRingMatrix R generators0 relations0)
    generators
    (@Struct_sigma
      Nat_grpd
      (λ relations0 : τ Nat_grpd,
        @CommRingMatrix R generators relations0)
      relations matrix);

symbol comm_ring_presentation_generators
  [R : τ CommRing]
  (P : τ (@CommRingPresentation R))
  : τ Nat_grpd
≔ sigma_Fst P;

symbol comm_ring_presentation_relations
  [R : τ CommRing]
  (P : τ (@CommRingPresentation R))
  : τ Nat_grpd
≔ sigma_Fst (sigma_Snd P);

symbol comm_ring_presentation_matrix
  [R : τ CommRing]
  (P : τ (@CommRingPresentation R))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P))
≔ sigma_Snd (sigma_Snd P);

/*
  A relation-preserving map P -> Q.

  The visible equation follows columnwise module-membership orientation:
  R_Q o W = F o R_P.  W is retained constructive data rather than an
  externally supplied commutative-square proof.
*/
symbol CommRingPresentationMorphism
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : Grpd
≔ `Σ_ F : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)),
    `Σ_ W : τ (@CommRingMatrix R
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R P)),
      @= (@CommRingMatrix R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R P))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_relations R P)
          (@comm_ring_presentation_matrix R Q)
          W)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_relations R P)
          F
          (@comm_ring_presentation_matrix R P));

symbol comm_ring_presentation_morphism_intro
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (F : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)))
  (W : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R P)))
  (law : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R P))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_matrix R Q)
      W)
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      F
      (@comm_ring_presentation_matrix R P))))
  : τ (@CommRingPresentationMorphism R P Q)
≔ @Struct_sigma
    (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))
    (λ F0 : τ (@CommRingMatrix R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)),
      `Σ_ W0 : τ (@CommRingMatrix R
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_relations R P)),
        @= (@CommRingMatrix R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_relations R P))
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_relations R Q)
            (@comm_ring_presentation_relations R P)
            (@comm_ring_presentation_matrix R Q)
            W0)
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_relations R P)
            F0
            (@comm_ring_presentation_matrix R P)))
    F
    (@Struct_sigma
      (@CommRingMatrix R
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R P))
      (λ W0 : τ (@CommRingMatrix R
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_relations R P)),
        @= (@CommRingMatrix R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_relations R P))
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_relations R Q)
            (@comm_ring_presentation_relations R P)
            (@comm_ring_presentation_matrix R Q)
            W0)
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_relations R P)
            F
            (@comm_ring_presentation_matrix R P)))
      W law);

symbol comm_ring_presentation_morphism_map
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))
≔ sigma_Fst f;

symbol comm_ring_presentation_morphism_witness
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R P))
≔ sigma_Fst (sigma_Snd f);

symbol comm_ring_presentation_morphism_law
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R P))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_presentation_morphism_witness R P Q f))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_matrix R P)))
≔ sigma_Snd (sigma_Snd f);

// Explicit evidence that two matrices induce the same target presentation map.
symbol CommRingPresentationMorphismAgreement
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (F G : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)))
  : Grpd
≔ `Σ_ H : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P)),
    @= (@CommRingMatrix R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_matrix R Q)
        H)
      (@comm_ring_matrix_sub R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        F G);

symbol comm_ring_presentation_morphism_agreement_intro
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [F G : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))]
  (H : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P)))
  (law : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_matrix R Q)
      H)
    (@comm_ring_matrix_sub R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      F G)))
  : τ (@CommRingPresentationMorphismAgreement R P Q F G)
≔ @Struct_sigma
    (@CommRingMatrix R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P))
    (λ H0 : τ (@CommRingMatrix R
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)),
      @= (@CommRingMatrix R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_matrix R Q)
          H0)
        (@comm_ring_matrix_sub R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          F G))
    H law;

// Exact differential square for one selected chain-map degree.
symbol CommRingChainMapSquare
  (R : τ CommRing)
  (source_prev source_now target_prev target_now : τ Nat_grpd)
  (d : τ (@CommRingMatrix R source_prev source_now))
  (e : τ (@CommRingMatrix R target_prev target_now))
  (F_prev : τ (@CommRingMatrix R target_prev source_prev))
  (F_now : τ (@CommRingMatrix R target_now source_now))
  : Grpd
≔ @= (@CommRingMatrix R target_prev source_now)
    (@comm_ring_matrix_comp R
      target_prev target_now source_now e F_now)
    (@comm_ring_matrix_comp R
      target_prev source_prev source_now F_prev d);

symbol comm_ring_chain_map_square_intro
  [R : τ CommRing]
  [source_prev source_now target_prev target_now : τ Nat_grpd]
  [d : τ (@CommRingMatrix R source_prev source_now)]
  [e : τ (@CommRingMatrix R target_prev target_now)]
  [F_prev : τ (@CommRingMatrix R target_prev source_prev)]
  [F_now : τ (@CommRingMatrix R target_now source_now)]
  (law : τ (@= (@CommRingMatrix R target_prev source_now)
    (@comm_ring_matrix_comp R
      target_prev target_now source_now e F_now)
    (@comm_ring_matrix_comp R
      target_prev source_prev source_now F_prev d)))
  : τ (@CommRingChainMapSquare R
      source_prev source_now target_prev target_now
      d e F_prev F_now)
≔ law;
