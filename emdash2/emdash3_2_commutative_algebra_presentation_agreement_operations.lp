/*
  Algebra and functorial transport of presentation-map agreement.

  Explicit target-factorization witnesses are reflexive, symmetric, transitive,
  additive, and stable under pre- and postcomposition. Every law is constructed
  from the matrix subtractive/bilinear layer and the retained square of the
  postcomposing raw map. No quotient collapse, runtime rule, or opaque equality
  witness is introduced.
*/

require open emdash.emdash3_2_commutative_algebra_matrix_subtractive_laws;
require open emdash.emdash3_2_commutative_algebra_presentation_additive_operations;

symbol comm_ring_presentation_agreement_witness
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [F G : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))]
  (a : τ (@CommRingPresentationMorphismAgreement R P Q F G))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P))
≔ sigma_Fst a;

symbol comm_ring_presentation_agreement_law
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [F G : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))]
  (a : τ (@CommRingPresentationMorphismAgreement R P Q F G))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_presentation_agreement_witness R P Q F G a))
    (@comm_ring_matrix_sub R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      F G))
≔ sigma_Snd a;

symbol comm_ring_presentation_agreement_refl
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (F : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)))
  : τ (@CommRingPresentationMorphismAgreement R P Q F F)
≔ @comm_ring_presentation_morphism_agreement_intro R P Q F F
    (@comm_ring_matrix_zero R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P))
    (@eq_trans
      (@CommRingMatrix R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P))
      _ _ _
      (@comm_ring_matrix_comp_zero_right_path R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_matrix R Q))
      (@eq_sym
        (@CommRingMatrix R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P))
        (@comm_ring_matrix_sub R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P) F F)
        (@comm_ring_matrix_zero R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P))
        (@comm_ring_matrix_sub_refl_path R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P) F)));

symbol comm_ring_presentation_agreement_sym
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [F G : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))]
  (a : τ (@CommRingPresentationMorphismAgreement R P Q F G))
  : τ (@CommRingPresentationMorphismAgreement R P Q G F)
≔ @comm_ring_presentation_morphism_agreement_intro R P Q G F
    (@comm_ring_matrix_neg R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_agreement_witness R P Q F G a))
    (@eq_trans
      (@CommRingMatrix R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P))
      _ _ _
      (@comm_ring_matrix_comp_neg_right_path R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_presentation_agreement_witness R P Q F G a))
      (@eq_trans
        (@CommRingMatrix R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P))
        _ _ _
        (@eq_ap
          (@CommRingMatrix R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R P))
          (@CommRingMatrix R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R P))
          (λ X : τ (@CommRingMatrix R
              (@comm_ring_presentation_generators R Q)
              (@comm_ring_presentation_generators R P)),
            @comm_ring_matrix_neg R
              (@comm_ring_presentation_generators R Q)
              (@comm_ring_presentation_generators R P) X)
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_relations R Q)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_matrix R Q)
            (@comm_ring_presentation_agreement_witness R P Q F G a))
          (@comm_ring_matrix_sub R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R P) F G)
          (@comm_ring_presentation_agreement_law R P Q F G a))
        (@comm_ring_matrix_neg_sub_swap_path R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P) F G)));

symbol comm_ring_presentation_agreement_trans
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [F G H : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))]
  (a : τ (@CommRingPresentationMorphismAgreement R P Q F G))
  (b : τ (@CommRingPresentationMorphismAgreement R P Q G H))
  : τ (@CommRingPresentationMorphismAgreement R P Q F H)
≔ @comm_ring_presentation_morphism_agreement_intro R P Q F H
    (@comm_ring_matrix_add R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_agreement_witness R P Q F G a)
      (@comm_ring_presentation_agreement_witness R P Q G H b))
    (@eq_trans
      (@CommRingMatrix R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P))
      _ _ _
      (@comm_ring_matrix_comp_add_right_path R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_presentation_agreement_witness R P Q F G a)
        (@comm_ring_presentation_agreement_witness R P Q G H b))
      (@eq_trans
        (@CommRingMatrix R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P))
        _ _ _
        (@comm_ring_matrix_add_congr_path R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          _ _ _ _
          (@comm_ring_presentation_agreement_law R P Q F G a)
          (@comm_ring_presentation_agreement_law R P Q G H b))
        (@comm_ring_matrix_sub_chain_path R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P) F G H)));

symbol comm_ring_presentation_agreement_add
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [F F' G G' : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))]
  (a : τ (@CommRingPresentationMorphismAgreement R P Q F F'))
  (b : τ (@CommRingPresentationMorphismAgreement R P Q G G'))
  : τ (@CommRingPresentationMorphismAgreement R P Q
      (@comm_ring_matrix_add R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P) F G)
      (@comm_ring_matrix_add R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P) F' G'))
≔ @comm_ring_presentation_morphism_agreement_intro R P Q
    (@comm_ring_matrix_add R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P) F G)
    (@comm_ring_matrix_add R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P) F' G')
    (@comm_ring_matrix_add R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_agreement_witness R P Q F F' a)
      (@comm_ring_presentation_agreement_witness R P Q G G' b))
    (@eq_trans
      (@CommRingMatrix R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P))
      _ _ _
      (@comm_ring_matrix_comp_add_right_path R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_presentation_agreement_witness R P Q F F' a)
        (@comm_ring_presentation_agreement_witness R P Q G G' b))
      (@eq_trans
        (@CommRingMatrix R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P))
        _ _ _
        (@comm_ring_matrix_add_congr_path R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          _ _ _ _
          (@comm_ring_presentation_agreement_law R P Q F F' a)
          (@comm_ring_presentation_agreement_law R P Q G G' b))
        (@eq_sym
          (@CommRingMatrix R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R P))
          _ _
          (@comm_ring_matrix_sub_add_path R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R P)
            F G F' G'))));

// Agreement is preserved by precomposition with an arbitrary generator map.
symbol comm_ring_presentation_agreement_precomp
  [R : τ CommRing]
  [O P Q : τ (@CommRingPresentation R)]
  [F F' : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))]
  (a : τ (@CommRingPresentationMorphismAgreement R P Q F F'))
  (K : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R O)))
  : τ (@CommRingPresentationMorphismAgreement R O Q
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R O) F K)
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R O) F' K))
≔ @comm_ring_presentation_morphism_agreement_intro R O Q
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R O) F K)
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R O) F' K)
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R O)
      (@comm_ring_presentation_agreement_witness R P Q F F' a) K)
    (@eq_trans
      (@CommRingMatrix R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R O))
      _ _ _
      (@comm_ring_matrix_comp_assoc_path R
        (@comm_ring_presentation_generators R O)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_presentation_agreement_witness R P Q F F' a)
        K)
      (@eq_trans
        (@CommRingMatrix R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R O))
        _ _ _
        (@eq_ap
          (@CommRingMatrix R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R P))
          (@CommRingMatrix R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R O))
          (λ X : τ (@CommRingMatrix R
              (@comm_ring_presentation_generators R Q)
              (@comm_ring_presentation_generators R P)),
            @comm_ring_matrix_comp R
              (@comm_ring_presentation_generators R Q)
              (@comm_ring_presentation_generators R P)
              (@comm_ring_presentation_generators R O) X K)
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_relations R Q)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_matrix R Q)
            (@comm_ring_presentation_agreement_witness R P Q F F' a))
          (@comm_ring_matrix_sub R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R P) F F')
          (@comm_ring_presentation_agreement_law R P Q F F' a))
        (@comm_ring_matrix_comp_sub_left_path R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R O)
          F F' K)));

// Postcomposition uses the relation witness retained by the outer raw map.
symbol comm_ring_presentation_agreement_postcomp
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  [F F' : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))]
  (a : τ (@CommRingPresentationMorphismAgreement R P Q F F'))
  (g : τ (@CommRingPresentationMorphism R Q S))
  : τ (@CommRingPresentationMorphismAgreement R P S
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R S)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_morphism_map R Q S g) F)
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R S)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_morphism_map R Q S g) F'))
≔ @comm_ring_presentation_morphism_agreement_intro R P S
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R S)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_morphism_map R Q S g) F)
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R S)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_morphism_map R Q S g) F')
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_relations R S)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_morphism_witness R Q S g)
      (@comm_ring_presentation_agreement_witness R P Q F F' a))
    (@eq_trans
      (@CommRingMatrix R
        (@comm_ring_presentation_generators R S)
        (@comm_ring_presentation_generators R P))
      _ _ _
      (@comm_ring_matrix_comp_assoc_path R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R S)
        (@comm_ring_presentation_generators R S)
        (@comm_ring_presentation_matrix R S)
        (@comm_ring_presentation_morphism_witness R Q S g)
        (@comm_ring_presentation_agreement_witness R P Q F F' a))
      (@eq_trans
        (@CommRingMatrix R
          (@comm_ring_presentation_generators R S)
          (@comm_ring_presentation_generators R P))
        _ _ _
        (@eq_ap
          (@CommRingMatrix R
            (@comm_ring_presentation_generators R S)
            (@comm_ring_presentation_relations R Q))
          (@CommRingMatrix R
            (@comm_ring_presentation_generators R S)
            (@comm_ring_presentation_generators R P))
          (λ X : τ (@CommRingMatrix R
              (@comm_ring_presentation_generators R S)
              (@comm_ring_presentation_relations R Q)),
            @comm_ring_matrix_comp R
              (@comm_ring_presentation_generators R S)
              (@comm_ring_presentation_relations R Q)
              (@comm_ring_presentation_generators R P) X
              (@comm_ring_presentation_agreement_witness R P Q F F' a))
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R S)
            (@comm_ring_presentation_relations R S)
            (@comm_ring_presentation_relations R Q)
            (@comm_ring_presentation_matrix R S)
            (@comm_ring_presentation_morphism_witness R Q S g))
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R S)
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_relations R Q)
            (@comm_ring_presentation_morphism_map R Q S g)
            (@comm_ring_presentation_matrix R Q))
          (@comm_ring_presentation_morphism_law R Q S g))
        (@eq_trans
          (@CommRingMatrix R
            (@comm_ring_presentation_generators R S)
            (@comm_ring_presentation_generators R P))
          _ _ _
          (@eq_sym
            (@CommRingMatrix R
              (@comm_ring_presentation_generators R S)
              (@comm_ring_presentation_generators R P))
            (@comm_ring_matrix_comp R
              (@comm_ring_presentation_generators R S)
              (@comm_ring_presentation_generators R Q)
              (@comm_ring_presentation_generators R P)
              (@comm_ring_presentation_morphism_map R Q S g)
              (@comm_ring_matrix_comp R
                (@comm_ring_presentation_generators R Q)
                (@comm_ring_presentation_relations R Q)
                (@comm_ring_presentation_generators R P)
                (@comm_ring_presentation_matrix R Q)
                (@comm_ring_presentation_agreement_witness R P Q F F' a)))
            (@comm_ring_matrix_comp R
              (@comm_ring_presentation_generators R S)
              (@comm_ring_presentation_relations R Q)
              (@comm_ring_presentation_generators R P)
              (@comm_ring_matrix_comp R
                (@comm_ring_presentation_generators R S)
                (@comm_ring_presentation_generators R Q)
                (@comm_ring_presentation_relations R Q)
                (@comm_ring_presentation_morphism_map R Q S g)
                (@comm_ring_presentation_matrix R Q))
              (@comm_ring_presentation_agreement_witness R P Q F F' a))
            (@comm_ring_matrix_comp_assoc_path R
              (@comm_ring_presentation_generators R P)
              (@comm_ring_presentation_relations R Q)
              (@comm_ring_presentation_generators R Q)
              (@comm_ring_presentation_generators R S)
              (@comm_ring_presentation_morphism_map R Q S g)
              (@comm_ring_presentation_matrix R Q)
              (@comm_ring_presentation_agreement_witness R P Q F F' a)))
          (@eq_trans
            (@CommRingMatrix R
              (@comm_ring_presentation_generators R S)
              (@comm_ring_presentation_generators R P))
            _ _ _
            (@eq_ap
              (@CommRingMatrix R
                (@comm_ring_presentation_generators R Q)
                (@comm_ring_presentation_generators R P))
              (@CommRingMatrix R
                (@comm_ring_presentation_generators R S)
                (@comm_ring_presentation_generators R P))
              (λ X : τ (@CommRingMatrix R
                  (@comm_ring_presentation_generators R Q)
                  (@comm_ring_presentation_generators R P)),
                @comm_ring_matrix_comp R
                  (@comm_ring_presentation_generators R S)
                  (@comm_ring_presentation_generators R Q)
                  (@comm_ring_presentation_generators R P)
                  (@comm_ring_presentation_morphism_map R Q S g) X)
              (@comm_ring_matrix_comp R
                (@comm_ring_presentation_generators R Q)
                (@comm_ring_presentation_relations R Q)
                (@comm_ring_presentation_generators R P)
                (@comm_ring_presentation_matrix R Q)
                (@comm_ring_presentation_agreement_witness R P Q F F' a))
              (@comm_ring_matrix_sub R
                (@comm_ring_presentation_generators R Q)
                (@comm_ring_presentation_generators R P) F F')
              (@comm_ring_presentation_agreement_law R P Q F F' a))
            (@comm_ring_matrix_comp_sub_right_path R
              (@comm_ring_presentation_generators R S)
              (@comm_ring_presentation_generators R Q)
              (@comm_ring_presentation_generators R P)
              (@comm_ring_presentation_morphism_map R Q S g)
              F F')))));
