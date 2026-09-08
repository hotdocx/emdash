/* Reviewer: all-test raw lifts, reconstruction, and retained factor matrices. */

require open emdash.emdash3_2_commutative_algebra_freyd_selected_kernel_lifting;

assert (R : τ CommRing) (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  ⊢ @comm_ring_freyd_selected_kernel_lift_raw R P Q T f K tau a
  : τ (@CommRingPresentationMorphism R T
    (@comm_ring_freyd_selected_kernel_presentation R P Q f K));

// Its quotient composite reconstructs the original test.
assert (R : τ CommRing) (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  ⊢ @comm_ring_freyd_selected_kernel_reconstruction_path R P Q T f K tau a
  : τ (@= (@CommRingFreydHomSet R T P)
    (@comm_ring_freyd_comp R T
      (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
      (@comm_ring_freyd_selected_kernel_embedding R P Q f K)
      (@comm_ring_freyd_selected_kernel_lift R P Q T f K tau a))
    (@comm_ring_freyd_hom_class R T P tau));

// The two selected factor matrices are retained without rank transport.
assert (R : τ CommRing) (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  ⊢ @comm_ring_presentation_morphism_map R T
    (@comm_ring_freyd_selected_kernel_presentation R P Q f K)
    (@comm_ring_freyd_selected_kernel_lift_raw R P Q T f K tau a)
    ≡ @comm_ring_freyd_selected_kernel_first_lift R P Q T f K tau a;
