/* Reviewer: reconstructed competitors equal the selected lift. */

require open emdash.emdash3_2_commutative_algebra_freyd_selected_kernel_uniqueness;

assert (R : τ CommRing) (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  (k : τ (@CommRingPresentationMorphism R T
    (@comm_ring_freyd_selected_kernel_presentation R P Q f K)))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T P
    (@comm_ring_presentation_morphism_map R T P
      (@comm_ring_presentation_morphism_comp R T
        (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
        (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K) k))
    (@comm_ring_presentation_morphism_map R T P tau)))
  ⊢ @comm_ring_freyd_selected_kernel_uniqueness_path R P Q T f K tau a k reconstructs
  : τ (@= (@CommRingFreydHomSet R T
    (@comm_ring_freyd_selected_kernel_presentation R P Q f K))
    (@comm_ring_freyd_hom_class R T
      (@comm_ring_freyd_selected_kernel_presentation R P Q f K) k)
    (@comm_ring_freyd_selected_kernel_lift R P Q T f K tau a));

// The explicit equality witness has the selected second rank, without a cast.
assert (R : τ CommRing) (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  (k : τ (@CommRingPresentationMorphism R T
    (@comm_ring_freyd_selected_kernel_presentation R P Q f K)))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T P
    (@comm_ring_presentation_morphism_map R T P
      (@comm_ring_presentation_morphism_comp R T
        (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
        (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K) k))
    (@comm_ring_presentation_morphism_map R T P tau)))
  ⊢ @comm_ring_freyd_selected_kernel_uniqueness_witness R P Q T f K tau a k reconstructs
  : τ (@CommRingMatrix R
    (@comm_ring_freyd_selected_kernel_relation_rank R P Q f K)
    (@comm_ring_presentation_generators R T));
