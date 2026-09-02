/* Reviewer-facing witnessed formal Freyd image/coimage consumers. */

require open emdash.emdash3_2_commutative_algebra_freyd_images;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_freyd_coimage_image_comparison_raw R W P Q f
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f));

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_freyd_image_factorization_path R W P Q f
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_hom_class R P Q
        (@comm_ring_freyd_image_factorization_raw R W P Q f))
      (@comm_ring_freyd_hom_class R P Q f));

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (b : τ (@CommRingFreydComparisonBimorphismWitness R W P Q f))
  ⊢ @comm_ring_freyd_comparison_inverse_candidates_path R W P Q f b
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_presentation R W P Q f))
      (@comm_ring_freyd_comparison_inverse_from_epi R W P Q f b)
      (@comm_ring_freyd_comparison_inverse_from_mono R W P Q f b));

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (b : τ (@CommRingFreydComparisonBimorphismWitness R W P Q f))
  ⊢ @comm_ring_freyd_coimage_image_iso R W P Q f b
  : τ (@IsoEvidence (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f));
