/* Reviewer-facing raw presentation identity/composition consumer. */

require open emdash.emdash3_2_commutative_algebra_presentation_operations;

assert
  (R : τ CommRing)
  (P : τ (@CommRingPresentation R))
  ⊢ @comm_ring_presentation_morphism_map R P P
      (@comm_ring_presentation_morphism_identity R P)
  ≡ @comm_ring_finite_free_id_matrix R
      (@comm_ring_presentation_generators R P);

assert
  (R : τ CommRing)
  (P : τ (@CommRingPresentation R))
  ⊢ @comm_ring_presentation_morphism_witness R P P
      (@comm_ring_presentation_morphism_identity R P)
  ≡ @comm_ring_finite_free_id_matrix R
      (@comm_ring_presentation_relations R P);

assert
  (R : τ CommRing)
  (P Q S : τ (@CommRingPresentation R))
  (g : τ (@CommRingPresentationMorphism R Q S))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_presentation_morphism_map R P S
      (@comm_ring_presentation_morphism_comp R P Q S g f)
  ≡ @comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R S)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_morphism_map R Q S g)
      (@comm_ring_presentation_morphism_map R P Q f);

symbol presentation_composite_square_reviewer
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (g : τ (@CommRingPresentationMorphism R Q S))
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R S)
      (@comm_ring_presentation_relations R P))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R S)
      (@comm_ring_presentation_relations R S)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_matrix R S)
      (@comm_ring_presentation_morphism_comp_witness R P Q S g f))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R S)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_morphism_comp_map R P Q S g f)
      (@comm_ring_presentation_matrix R P)))
≔ @comm_ring_presentation_morphism_comp_law R P Q S g f;

assertnot
  (R : τ CommRing)
  (P Q S : τ (@CommRingPresentation R))
  (g : τ (@CommRingPresentationMorphism R Q S))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (A : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R S)
      (@comm_ring_presentation_generators R P)))
  ⊢ @comm_ring_presentation_morphism_comp_map R P Q S g f
  ≡ A;
