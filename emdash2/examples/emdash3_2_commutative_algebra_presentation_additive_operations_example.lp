/* Reviewer-facing raw presentation zero/addition consumer. */

require open emdash.emdash3_2_commutative_algebra_presentation_additive_operations;

assert
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  ⊢ @comm_ring_presentation_morphism_map R P Q
      (@comm_ring_presentation_morphism_zero R P Q)
  ≡ @comm_ring_matrix_zero R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P);

assert
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f g : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_presentation_morphism_map R P Q
      (@comm_ring_presentation_morphism_add R P Q f g)
  ≡ @comm_ring_matrix_add R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_morphism_map R P Q g);

symbol presentation_additive_square_reviewer
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
≔ @comm_ring_presentation_morphism_add_law R P Q f g;

assertnot
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f g : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_presentation_morphism_add_map R P Q f g
  ≡ @comm_ring_presentation_morphism_map R P Q f;
