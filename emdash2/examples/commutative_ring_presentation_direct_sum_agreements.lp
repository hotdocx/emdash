/* Reviewer-facing agreement compatibility of presentation direct sums. */

require open emdash.emdash3_2_commutative_algebra_presentation_direct_sum_agreements;

assert (R : τ CommRing)
  (P0 P1 Q0 Q1 : τ (@CommRingPresentation R))
  (f f' : τ (@CommRingPresentationMorphism R P0 Q0))
  (g g' : τ (@CommRingPresentationMorphism R P1 Q1))
  (a : τ (@CommRingPresentationMorphismAgreement R P0 Q0
      (@comm_ring_presentation_morphism_map R P0 Q0 f)
      (@comm_ring_presentation_morphism_map R P0 Q0 f')))
  (b : τ (@CommRingPresentationMorphismAgreement R P1 Q1
      (@comm_ring_presentation_morphism_map R P1 Q1 g)
      (@comm_ring_presentation_morphism_map R P1 Q1 g'))) ⊢
  @comm_ring_presentation_direct_sum_agreement
    R P0 P1 Q0 Q1 f f' g g' a b
  : τ (@CommRingPresentationMorphismAgreement R
      (@comm_ring_presentation_direct_sum R P0 P1)
      (@comm_ring_presentation_direct_sum R Q0 Q1)
      (@comm_ring_presentation_morphism_direct_sum_map
        R P0 P1 Q0 Q1 f g)
      (@comm_ring_presentation_morphism_direct_sum_map
        R P0 P1 Q0 Q1 f' g'));

assert (R : τ CommRing)
  (X P Q : τ (@CommRingPresentation R))
  (f f' : τ (@CommRingPresentationMorphism R X P))
  (g g' : τ (@CommRingPresentationMorphism R X Q))
  (a : τ (@CommRingPresentationMorphismAgreement R X P
      (@comm_ring_presentation_morphism_map R X P f)
      (@comm_ring_presentation_morphism_map R X P f')))
  (b : τ (@CommRingPresentationMorphismAgreement R X Q
      (@comm_ring_presentation_morphism_map R X Q g)
      (@comm_ring_presentation_morphism_map R X Q g'))) ⊢
  @comm_ring_presentation_pair_agreement R X P Q f f' g g' a b
  : τ (@CommRingPresentationMorphismAgreement R X
      (@comm_ring_presentation_direct_sum R P Q)
      (@comm_ring_presentation_morphism_map R X
        (@comm_ring_presentation_direct_sum R P Q)
        (@comm_ring_presentation_pair R X P Q f g))
      (@comm_ring_presentation_morphism_map R X
        (@comm_ring_presentation_direct_sum R P Q)
        (@comm_ring_presentation_pair R X P Q f' g')));
