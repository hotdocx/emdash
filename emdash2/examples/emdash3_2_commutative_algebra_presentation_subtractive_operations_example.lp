/* Reviewer-facing raw presentation negation consumer. */

require open emdash.emdash3_2_commutative_algebra_presentation_subtractive_operations;

assert
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_presentation_morphism_map R P Q
      (@comm_ring_presentation_morphism_neg R P Q f)
  ≡ @comm_ring_matrix_neg R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_morphism_map R P Q f);

symbol presentation_neg_square_reviewer
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
≔ @comm_ring_presentation_morphism_neg_law R P Q f;

assertnot
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_presentation_morphism_neg_map R P Q f
  ≡ @comm_ring_presentation_morphism_map R P Q f;
