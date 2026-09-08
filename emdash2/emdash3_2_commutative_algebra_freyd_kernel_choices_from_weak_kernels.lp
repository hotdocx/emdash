/*
  Compatibility selector from the existing global weak-kernel capability.

  The original kernel construction and the per-choice interface remain
  upstream of this adapter. Both selected packages are retained verbatim.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_kernel_choices;
require open emdash.emdash3_2_commutative_algebra_freyd_kernels;

// Compatibility wrapper: select the original two packages from W verbatim.
symbol comm_ring_freyd_kernel_choices_from_weak_kernels [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingFreydKernelChoices R P Q f)
≔ @comm_ring_freyd_kernel_choices_intro R P Q f
    (@comm_ring_freyd_kernel_first_weak_pullback R W P Q f)
    (@comm_ring_freyd_kernel_second_weak_pullback R W P Q f);
