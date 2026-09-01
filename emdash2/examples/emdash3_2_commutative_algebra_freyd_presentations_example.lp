/* Reviewer-facing homwise quotient and representable-element consumer. */

require open emdash.emdash3_2_commutative_algebra_freyd_presentations;

assert
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  ⊢ Obj (@CommRingPresentationAgreement_cat R P Q)
  ≡ @CommRingPresentationMorphism R P Q;

assert
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f g : τ (@CommRingPresentationMorphism R P Q))
  ⊢ Hom_cat (@CommRingPresentationAgreement_cat R P Q) f g
  ≡ Path_cat (@CommRingPresentationMorphismAgreement R P Q
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_morphism_map R P Q g));

assert
  (R : τ CommRing)
  ⊢ Obj (@CommRingFreydPresentation_cat R)
  ≡ @CommRingPresentation R;

assert
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  ⊢ Hom_cat (@CommRingFreydPresentation_cat R) P Q
  ≡ Path_cat (@CommRingFreydHomSet R P Q);

symbol freyd_agreement_example
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f g : τ (@CommRingPresentationMorphism R P Q))
  (agreement : τ (@CommRingPresentationMorphismAgreement R P Q
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_morphism_map R P Q g)))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_hom_class R P Q f)
      (@comm_ring_freyd_hom_class R P Q g))
≔ @comm_ring_freyd_agreement_path R P Q f g agreement;

assert
  (R : τ CommRing)
  (P : τ (@CommRingPresentation R))
  ⊢ @CommRingFreydElement R P
  ≡ @CommRingFreydHomSet R (@comm_ring_free_one_presentation R) P;

assertnot
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f g : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_freyd_hom_class R P Q f
  ≡ @comm_ring_freyd_hom_class R P Q g;
