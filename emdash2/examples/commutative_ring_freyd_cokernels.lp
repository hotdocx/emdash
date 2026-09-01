/* Reviewer-facing witness-enriched formal Freyd cokernel consumers. */

require open emdash.emdash3_2_commutative_algebra_freyd_cokernels;

assert
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_freyd_cokernel_projection R P Q f
  : τ (@CommRingFreydHomSet R Q
      (@comm_ring_freyd_cokernel_presentation R P Q f));

// The formal projection annihilates the represented morphism in the quotient.
assert
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_freyd_cokernel_annihilation_path R P Q f
  : τ (@= (@CommRingFreydHomSet R P
      (@comm_ring_freyd_cokernel_presentation R P Q f))
      (@comm_ring_freyd_comp R P Q
        (@comm_ring_freyd_cokernel_presentation R P Q f)
        (@comm_ring_freyd_cokernel_projection R P Q f)
        (@comm_ring_freyd_hom_class R P Q f))
      (@comm_ring_freyd_zero_class R P
        (@comm_ring_freyd_cokernel_presentation R P Q f)));

// A retained zero-composite agreement constructs the raw/quotient colift.
assert
  (R : τ CommRing)
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (h : τ (@CommRingPresentationMorphism R Q T))
  (a : τ (@CommRingPresentationMorphismAgreement R P T
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_comp R P Q T h f))
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_zero R P T))))
  ⊢ @comm_ring_freyd_cokernel_colift R P Q T f h a
  : τ (@CommRingFreydHomSet R
      (@comm_ring_freyd_cokernel_presentation R P Q f) T);

assert
  (R : τ CommRing)
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (h : τ (@CommRingPresentationMorphism R Q T))
  (a : τ (@CommRingPresentationMorphismAgreement R P T
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_comp R P Q T h f))
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_zero R P T))))
  ⊢ @comm_ring_freyd_cokernel_reconstruction_path R P Q T f h a
  : τ (@= (@CommRingFreydHomSet R Q T)
      (@comm_ring_freyd_comp R Q
        (@comm_ring_freyd_cokernel_presentation R P Q f) T
        (@comm_ring_freyd_cokernel_colift R P Q T f h a)
        (@comm_ring_freyd_cokernel_projection R P Q f))
      (@comm_ring_freyd_hom_class R Q T h));

// A reconstructing competing raw colift is quotient-equal to the selected one.
assert
  (R : τ CommRing)
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (h : τ (@CommRingPresentationMorphism R Q T))
  (a : τ (@CommRingPresentationMorphismAgreement R P T
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_comp R P Q T h f))
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_zero R P T))))
  (k : τ (@CommRingPresentationMorphism R
    (@comm_ring_freyd_cokernel_presentation R P Q f) T))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R Q T
    (@comm_ring_presentation_morphism_map R Q T
      (@comm_ring_presentation_morphism_comp R Q
        (@comm_ring_freyd_cokernel_presentation R P Q f) T
        k (@comm_ring_freyd_cokernel_projection_raw R P Q f)))
    (@comm_ring_presentation_morphism_map R Q T h)))
  ⊢ @comm_ring_freyd_cokernel_uniqueness_path
      R P Q T f h a k reconstructs
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_freyd_cokernel_presentation R P Q f) T)
      (@comm_ring_freyd_hom_class R
        (@comm_ring_freyd_cokernel_presentation R P Q f) T k)
      (@comm_ring_freyd_cokernel_colift R P Q T f h a));
