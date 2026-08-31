/* Reviewer-facing finite-presentation morphism consumer. */

require open emdash.emdash3_2_commutative_algebra_presentations;

symbol presentation_scalar_matrix
  (R : τ CommRing)
  (a : τ (@comm_ring_carrier R))
  : τ (@CommRingMatrix R (succ zero) (succ zero))
≔ @finite_family_singleton
    (@CommRingVector R (succ zero))
    (@finite_family_singleton (@comm_ring_carrier R) a);

assert
  (R : τ CommRing)
  (a b : τ (@comm_ring_carrier R))
  ⊢ @comm_ring_matrix_add R (succ zero) (succ zero)
      (@presentation_scalar_matrix R a)
      (@presentation_scalar_matrix R b)
  ≡ @presentation_scalar_matrix R (@comm_ring_add R a b);

assert
  (R : τ CommRing)
  (a b : τ (@comm_ring_carrier R))
  ⊢ @comm_ring_matrix_sub R (succ zero) (succ zero)
      (@presentation_scalar_matrix R a)
      (@presentation_scalar_matrix R b)
  ≡ @presentation_scalar_matrix R
      (@comm_ring_add R a (@comm_ring_neg R b));

symbol presentation_scalar
  (R : τ CommRing)
  (a : τ (@comm_ring_carrier R))
  : τ (@CommRingPresentation R)
≔ @comm_ring_presentation_intro R
    (succ zero) (succ zero)
    (@presentation_scalar_matrix R a);

assert
  (R : τ CommRing)
  (a : τ (@comm_ring_carrier R))
  ⊢ @comm_ring_presentation_generators R (@presentation_scalar R a)
  ≡ succ zero;

assert
  (R : τ CommRing)
  (a : τ (@comm_ring_carrier R))
  ⊢ @comm_ring_presentation_relations R (@presentation_scalar R a)
  ≡ succ zero;

assert
  (R : τ CommRing)
  (a : τ (@comm_ring_carrier R))
  ⊢ @comm_ring_presentation_matrix R (@presentation_scalar R a)
  ≡ @presentation_scalar_matrix R a;

symbol presentation_morphism_example
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
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
≔ @comm_ring_presentation_morphism_intro R P Q F W law;

symbol presentation_agreement_example
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (F G : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)))
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
≔ @comm_ring_presentation_morphism_agreement_intro R P Q F G H law;

symbol chain_square_example
  (R : τ CommRing)
  (source_prev source_now target_prev target_now : τ Nat_grpd)
  (d : τ (@CommRingMatrix R source_prev source_now))
  (e : τ (@CommRingMatrix R target_prev target_now))
  (F_prev : τ (@CommRingMatrix R target_prev source_prev))
  (F_now : τ (@CommRingMatrix R target_now source_now))
  (law : τ (@= (@CommRingMatrix R target_prev source_now)
    (@comm_ring_matrix_comp R
      target_prev target_now source_now e F_now)
    (@comm_ring_matrix_comp R
      target_prev source_prev source_now F_prev d)))
  : τ (@CommRingChainMapSquare R
      source_prev source_now target_prev target_now
      d e F_prev F_now)
≔ @comm_ring_chain_map_square_intro R
    source_prev source_now target_prev target_now
    d e F_prev F_now law;

// A visible nonzero column is not collapsed by matrix subtraction.
assertnot
  (R : τ CommRing)
  (a b : τ (@comm_ring_carrier R))
  ⊢ @comm_ring_matrix_sub R (succ zero) (succ zero)
      (@presentation_scalar_matrix R a)
      (@presentation_scalar_matrix R b)
  ≡ @comm_ring_matrix_zero R (succ zero) (succ zero);
