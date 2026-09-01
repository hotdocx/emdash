/*
  Formal zero and addition of relation-preserving presentation maps.

  Both generator and relation matrices are combined componentwise. Their
  stored squares are derived from matrix zero/bilinearity and the input square
  laws. This rule-free layer completes the raw preadditive operations before
  agreement and quotient-Hom descent.
*/

require open emdash.emdash3_2_commutative_algebra_matrix_additive_laws;

// The two zero composites agree through the common zero matrix.
symbol comm_ring_presentation_zero_law
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R P))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_matrix_zero R
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R P)))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_matrix_zero R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P))
      (@comm_ring_presentation_matrix R P)))
≔ @eq_trans
    (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R P))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_matrix_zero R
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R P)))
    (@comm_ring_matrix_zero R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R P))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_matrix_zero R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P))
      (@comm_ring_presentation_matrix R P))
    (@comm_ring_matrix_comp_zero_right_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_matrix R Q))
    (@eq_sym
      (@CommRingMatrix R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R P))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_matrix_zero R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P))
        (@comm_ring_presentation_matrix R P))
      (@comm_ring_matrix_zero R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R P))
      (@comm_ring_matrix_comp_zero_left_path R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_matrix R P)));

symbol comm_ring_presentation_morphism_zero
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : τ (@CommRingPresentationMorphism R P Q)
≔ @comm_ring_presentation_morphism_intro R P Q
    (@comm_ring_matrix_zero R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))
    (@comm_ring_matrix_zero R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R P))
    (@comm_ring_presentation_zero_law R P Q);

symbol comm_ring_presentation_morphism_add_map
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f g : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))
≔ @comm_ring_matrix_add R
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_morphism_map R P Q g);

symbol comm_ring_presentation_morphism_add_witness
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f g : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R P))
≔ @comm_ring_matrix_add R
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_relations R P)
    (@comm_ring_presentation_morphism_witness R P Q f)
    (@comm_ring_presentation_morphism_witness R P Q g);

symbol comm_ring_presentation_morphism_add_law
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f g : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R P))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_presentation_morphism_add_witness R P Q f g))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_morphism_add_map R P Q f g)
      (@comm_ring_presentation_matrix R P)))
≔ @eq_trans
    (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R P))
    _ _ _
    (@comm_ring_matrix_comp_add_right_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_presentation_morphism_witness R P Q f)
      (@comm_ring_presentation_morphism_witness R P Q g))
    (@eq_trans
      (@CommRingMatrix R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R P))
      _ _ _
      (@comm_ring_matrix_add_congr_path R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R P)
        _ _ _ _
        (@comm_ring_presentation_morphism_law R P Q f)
        (@comm_ring_presentation_morphism_law R P Q g))
      (@eq_sym
        (@CommRingMatrix R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R P))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_relations R P)
          (@comm_ring_presentation_morphism_add_map R P Q f g)
          (@comm_ring_presentation_matrix R P))
        _
        (@comm_ring_matrix_comp_add_left_path R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_relations R P)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_presentation_morphism_map R P Q g)
          (@comm_ring_presentation_matrix R P))));

symbol comm_ring_presentation_morphism_add
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f g : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentationMorphism R P Q)
≔ @comm_ring_presentation_morphism_intro R P Q
    (@comm_ring_presentation_morphism_add_map R P Q f g)
    (@comm_ring_presentation_morphism_add_witness R P Q f g)
    (@comm_ring_presentation_morphism_add_law R P Q f g);
