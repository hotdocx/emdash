/* Reviewer: selected raw embedding, literal matrix, and quotient annihilation. */

require open emdash.emdash3_2_commutative_algebra_freyd_selected_kernel_embedding;

assert (R : τ CommRing) (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  ⊢ @comm_ring_freyd_selected_kernel_embedding_raw R P Q f K
  : τ (@CommRingPresentationMorphism R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P);

assert (R : τ CommRing) (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  ⊢ @comm_ring_presentation_morphism_map R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
      (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K)
    ≡ @comm_ring_freyd_selected_kernel_projection R P Q f K;

assert (R : τ CommRing) (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  ⊢ @comm_ring_freyd_selected_kernel_annihilation_path R P Q f K
  : τ (@= (@CommRingFreydHomSet R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) Q)
    (@comm_ring_freyd_comp R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P Q
      (@comm_ring_freyd_hom_class R P Q f)
      (@comm_ring_freyd_hom_class R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
        (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K)))
    (@comm_ring_freyd_zero_class R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) Q));
