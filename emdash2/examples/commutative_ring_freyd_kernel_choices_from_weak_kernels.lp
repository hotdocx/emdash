/* Reviewer: the W adapter returns the original selected presentation and map. */

require open emdash.emdash3_2_commutative_algebra_freyd_kernel_choices_from_weak_kernels;

// Original-W selection returns the very same existing presentation and projection.
assert (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_freyd_selected_kernel_presentation R P Q f
      (@comm_ring_freyd_kernel_choices_from_weak_kernels R W P Q f)
    ≡ @comm_ring_freyd_kernel_presentation R W P Q f;

assert (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_freyd_selected_kernel_projection R P Q f
      (@comm_ring_freyd_kernel_choices_from_weak_kernels R W P Q f)
    ≡ @comm_ring_freyd_kernel_first_proj1 R W P Q f;
