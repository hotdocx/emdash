/*
  Reviewer: the legacy selector API reduces through one selected proof core.
  Full raw constructor checks retain both factor matrices and the original
  qualified law names, not merely equality of the ambient maps.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_kernel_choices_from_weak_kernels;

// The local selector and downstream adapter select exactly the same pair.
assert (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_freyd_kernel_selected_choices R W P Q f
    ≡ @comm_ring_freyd_kernel_choices_from_weak_kernels R W P Q f;

// The first rank remains a projection of the first package alone.
assert (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_freyd_kernel_first_object R W P Q f
    ≡ @comm_ring_freyd_kernel_first_choice_rank R P Q f
      (@comm_ring_freyd_kernel_first_weak_pullback R W P Q f);

// The complete raw embedding retains its legacy constructor presentation.
assert (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_freyd_kernel_embedding_raw R W P Q f
    ≡ @comm_ring_presentation_morphism_intro R
      (@comm_ring_freyd_kernel_presentation R W P Q f) P
      (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
      (@comm_ring_freyd_kernel_second_proj2 R W P Q f)
      (@comm_ring_freyd_kernel_embedding_law R W P Q f);

// Both APIs use the same selected raw embedding, including its relation law.
assert (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @comm_ring_freyd_kernel_embedding_raw R W P Q f
    ≡ @comm_ring_freyd_selected_kernel_embedding_raw R P Q f
      (@comm_ring_freyd_kernel_selected_choices R W P Q f);

// The complete lifted raw arrow retains both chosen factor matrices.
assert (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  ⊢ @comm_ring_freyd_kernel_lift_raw R W P Q T f tau a
    ≡ @comm_ring_presentation_morphism_intro R T
      (@comm_ring_freyd_kernel_presentation R W P Q f)
      (@comm_ring_freyd_kernel_first_lift R W P Q T f tau a)
      (@comm_ring_freyd_kernel_second_lift R W P Q T f tau a)
      (@comm_ring_freyd_kernel_lift_law R W P Q T f tau a);

// Reconstruction is the same proof operation at the same retained choices.
assert (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels (@CommRingFiniteFree_cat R)
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
    ≡ @comm_ring_freyd_selected_kernel_reconstruction_path R P Q T f
      (@comm_ring_freyd_kernel_selected_choices R W P Q f) tau a;

// Competing lifts use the shared selected-choice uniqueness operation.
assert (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels (@CommRingFiniteFree_cat R)
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
  ⊢ @comm_ring_freyd_kernel_uniqueness_path R W P Q T f tau a k reconstructs
    ≡ @comm_ring_freyd_selected_kernel_uniqueness_path R P Q T f
      (@comm_ring_freyd_kernel_selected_choices R W P Q f) tau a k reconstructs;
