/* Reviewer-facing whole Freyd quotient-operation consumer. */

require open emdash.emdash3_2_commutative_algebra_freyd_operations;

assert
  (R : τ CommRing)
  (P Q S : τ (@CommRingPresentation R))
  (g : τ (@CommRingPresentationMorphism R Q S))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_freyd_raw_comp R P Q S
      (@comm_ring_freyd_raw_groupoid_class R Q S g)
      (@comm_ring_freyd_raw_groupoid_class R P Q f)
  ≡ @comm_ring_freyd_raw_groupoid_class R P S
      (@comm_ring_presentation_morphism_comp R P Q S g f);

assert
  (R : τ CommRing)
  (P Q S : τ (@CommRingPresentation R))
  (g : τ (@CommRingPresentationMorphism R Q S))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_freyd_comp R P Q S
      (@comm_ring_freyd_hom_class R Q S g)
      (@comm_ring_freyd_hom_class R P Q f)
  ≡ @comm_ring_freyd_hom_class R P S
      (@comm_ring_presentation_morphism_comp R P Q S g f);

assert
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f g : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_freyd_add R P Q
      (@comm_ring_freyd_hom_class R P Q f)
      (@comm_ring_freyd_hom_class R P Q g)
  ≡ @comm_ring_freyd_hom_class R P Q
      (@comm_ring_presentation_morphism_add R P Q f g);

assert
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_freyd_neg R P Q
      (@comm_ring_freyd_hom_class R P Q f)
  ≡ @comm_ring_freyd_hom_class R P Q
      (@comm_ring_presentation_morphism_neg R P Q f);

symbol freyd_whole_postcomp_functor_reviewer
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (g : τ (@CommRingPresentationMorphism R Q S))
  : τ (@Functor
      (@CommRingPresentationAgreement_cat R P Q)
      (@CommRingPresentationAgreement_cat R P S))
≔ @comm_ring_presentation_postcomp_agreement_func R P Q S g;

symbol freyd_identity_class_reviewer
  (R : τ CommRing)
  (P : τ (@CommRingPresentation R))
  : τ (@CommRingFreydHomSet R P P)
≔ @comm_ring_freyd_identity_class R P;

symbol freyd_zero_class_reviewer
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : τ (@CommRingFreydHomSet R P Q)
≔ @comm_ring_freyd_zero_class R P Q;

assertnot
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f g : τ (@CommRingFreydHomSet R P Q))
  ⊢ @comm_ring_freyd_add R P Q f g
  ≡ f;
