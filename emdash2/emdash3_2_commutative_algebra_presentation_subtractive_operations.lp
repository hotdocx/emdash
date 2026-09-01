/*
  Additive inverse of relation-preserving presentation maps.

  Generator and relation matrices are negated together. The relation square is
  constructed from preservation of negation by matrix composition and the
  input square; no new runtime algebra rule or opaque path is introduced.
*/

require open emdash.emdash3_2_commutative_algebra_matrix_subtractive_laws;
require open emdash.emdash3_2_commutative_algebra_presentation_additive_operations;

symbol comm_ring_presentation_morphism_neg_map
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))
≔ @comm_ring_matrix_neg R
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_morphism_map R P Q f);

symbol comm_ring_presentation_morphism_neg_witness
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R P))
≔ @comm_ring_matrix_neg R
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_relations R P)
    (@comm_ring_presentation_morphism_witness R P Q f);

symbol comm_ring_presentation_morphism_neg_law
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
      (@comm_ring_presentation_morphism_neg_witness R P Q f))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_morphism_neg_map R P Q f)
      (@comm_ring_presentation_matrix R P)))
≔ @eq_trans
    (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R P))
    _ _ _
    (@comm_ring_matrix_comp_neg_right_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_presentation_morphism_witness R P Q f))
    (@eq_trans
      (@CommRingMatrix R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R P))
      _ _ _
      (@eq_ap
        (@CommRingMatrix R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R P))
        (@CommRingMatrix R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R P))
        (λ X : τ (@CommRingMatrix R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_relations R P)),
          @comm_ring_matrix_neg R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_relations R P) X)
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
          (@comm_ring_presentation_matrix R P))
        (@comm_ring_presentation_morphism_law R P Q f))
      (@eq_sym
        (@CommRingMatrix R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R P))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_relations R P)
          (@comm_ring_presentation_morphism_neg_map R P Q f)
          (@comm_ring_presentation_matrix R P))
        _
        (@comm_ring_matrix_comp_neg_left_path R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_relations R P)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_presentation_matrix R P))));

symbol comm_ring_presentation_morphism_neg
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentationMorphism R P Q)
≔ @comm_ring_presentation_morphism_intro R P Q
    (@comm_ring_presentation_morphism_neg_map R P Q f)
    (@comm_ring_presentation_morphism_neg_witness R P Q f)
    (@comm_ring_presentation_morphism_neg_law R P Q f);
