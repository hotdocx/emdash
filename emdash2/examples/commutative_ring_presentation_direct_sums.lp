/* Reviewer-facing zero and binary sums of finite presentations. */

require open emdash.emdash3_2_commutative_algebra_presentation_direct_sums;

assert (R : τ CommRing) ⊢
  @comm_ring_zero_presentation R
  : τ (@CommRingPresentation R);

assert (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R)) ⊢
  @comm_ring_presentation_generators R
    (@comm_ring_presentation_direct_sum R P Q)
  ≡ @nat_add
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q);

assert (R : τ CommRing)
  (P0 P1 Q0 Q1 : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P0 Q0))
  (g : τ (@CommRingPresentationMorphism R P1 Q1)) ⊢
  @comm_ring_presentation_morphism_direct_sum R P0 P1 Q0 Q1 f g
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_presentation_direct_sum R P0 P1)
      (@comm_ring_presentation_direct_sum R Q0 Q1));

assert (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R)) ⊢
  @comm_ring_presentation_proj1 R P Q
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_presentation_direct_sum R P Q) P);

assert (R : τ CommRing)
  (X P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R X P))
  (g : τ (@CommRingPresentationMorphism R X Q)) ⊢
  @comm_ring_presentation_pair R X P Q f g
  : τ (@CommRingPresentationMorphism R X
      (@comm_ring_presentation_direct_sum R P Q));

assertnot (R : τ CommRing)
  (X P Q : τ (@CommRingPresentation R))
  (f f' : τ (@CommRingPresentationMorphism R X P))
  (g : τ (@CommRingPresentationMorphism R X Q)) ⊢
  @comm_ring_presentation_morphism_map R X
    (@comm_ring_presentation_direct_sum R P Q)
    (@comm_ring_presentation_pair R X P Q f g)
  ≡ @comm_ring_presentation_morphism_map R X
    (@comm_ring_presentation_direct_sum R P Q)
    (@comm_ring_presentation_pair R X P Q f' g);
