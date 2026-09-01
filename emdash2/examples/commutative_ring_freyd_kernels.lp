/* Reviewer-facing witness-enriched formal Freyd kernel consumers. */

require open emdash.emdash3_2_commutative_algebra_freyd_kernels;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_freyd_kernel_embedding R W P Q f
  : τ (@CommRingFreydHomSet R
      (@comm_ring_freyd_kernel_presentation R W P Q f) P);

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_freyd_kernel_annihilation_path R W P Q f
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_freyd_kernel_presentation R W P Q f) Q)
      (@comm_ring_freyd_comp R
        (@comm_ring_freyd_kernel_presentation R W P Q f) P Q
        (@comm_ring_freyd_hom_class R P Q f)
        (@comm_ring_freyd_kernel_embedding R W P Q f))
      (@comm_ring_freyd_zero_class R
        (@comm_ring_freyd_kernel_presentation R W P Q f) Q));

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  ⊢ @comm_ring_freyd_kernel_reconstruction_path R W P Q T f tau a
  : τ (@= (@CommRingFreydHomSet R T P)
      (@comm_ring_freyd_comp R T
        (@comm_ring_freyd_kernel_presentation R W P Q f) P
        (@comm_ring_freyd_kernel_embedding R W P Q f)
        (@comm_ring_freyd_kernel_lift R W P Q T f tau a))
      (@comm_ring_freyd_hom_class R T P tau));

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  (k : τ (@CommRingPresentationMorphism R T
    (@comm_ring_freyd_kernel_presentation R W P Q f)))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T P
    (@comm_ring_presentation_morphism_map R T P
      (@comm_ring_presentation_morphism_comp R T
        (@comm_ring_freyd_kernel_presentation R W P Q f) P
        (@comm_ring_freyd_kernel_embedding_raw R W P Q f) k))
    (@comm_ring_presentation_morphism_map R T P tau)))
  ⊢ @comm_ring_freyd_kernel_uniqueness_path
      R W P Q T f tau a k reconstructs
  : τ (@= (@CommRingFreydHomSet R T
      (@comm_ring_freyd_kernel_presentation R W P Q f))
      (@comm_ring_freyd_hom_class R T
        (@comm_ring_freyd_kernel_presentation R W P Q f) k)
      (@comm_ring_freyd_kernel_lift R W P Q T f tau a));
