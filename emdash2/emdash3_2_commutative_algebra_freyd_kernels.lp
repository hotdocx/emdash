/*
  Backward-compatible selector API for witnessed formal Freyd kernels.

  The two weak-pullback stages remain independently selected from the
  finite-free weak-kernel capability. Only after both stages exist is their
  whole choice package formed. Public proof operations below delegate to
  the shared selected-choice core, retaining every original signature.
*/

require open emdash.emdash3_2_computational_weak_pullback_cones;
require open emdash.emdash3_2_commutative_algebra_finite_free_additive;
require open emdash.emdash3_2_commutative_algebra_freyd_cokernels;
require open emdash.emdash3_2_commutative_algebra_freyd_selected_kernel_uniqueness;

symbol comm_ring_freyd_kernel_first_weak_pullback
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@ComputationalWeakPullback
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero
      (@comm_ring_finite_free_additive R)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_matrix R Q))
≔ @computational_weak_pullback_of_weak_kernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero
    (@comm_ring_finite_free_additive R)
    W
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_matrix R Q);

symbol comm_ring_freyd_kernel_first_object
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ Nat_grpd
≔ @computational_weak_pullback_object
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_matrix R Q)
    (@comm_ring_freyd_kernel_first_weak_pullback R W P Q f);

symbol comm_ring_freyd_kernel_first_proj1
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_freyd_kernel_first_object R W P Q f))
≔ @computational_weak_pullback_proj1
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_matrix R Q)
    (@comm_ring_freyd_kernel_first_weak_pullback R W P Q f);

symbol comm_ring_freyd_kernel_first_proj2
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_freyd_kernel_first_object R W P Q f))
≔ @computational_weak_pullback_proj2
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_matrix R Q)
    (@comm_ring_freyd_kernel_first_weak_pullback R W P Q f);

symbol comm_ring_freyd_kernel_second_weak_pullback
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@ComputationalWeakPullback
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero
      (@comm_ring_finite_free_additive R)
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
      (@comm_ring_presentation_matrix R P))
≔ @computational_weak_pullback_of_weak_kernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero
    (@comm_ring_finite_free_additive R)
    W
    (@comm_ring_freyd_kernel_first_object R W P Q f)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_relations R P)
    (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
    (@comm_ring_presentation_matrix R P);

symbol comm_ring_freyd_kernel_second_object
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ Nat_grpd
≔ @computational_weak_pullback_object
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_freyd_kernel_first_object R W P Q f)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_relations R P)
    (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
    (@comm_ring_presentation_matrix R P)
    (@comm_ring_freyd_kernel_second_weak_pullback R W P Q f);

symbol comm_ring_freyd_kernel_second_proj1
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingMatrix R
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_freyd_kernel_second_object R W P Q f))
≔ @computational_weak_pullback_proj1
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_freyd_kernel_first_object R W P Q f)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_relations R P)
    (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
    (@comm_ring_presentation_matrix R P)
    (@comm_ring_freyd_kernel_second_weak_pullback R W P Q f);

symbol comm_ring_freyd_kernel_second_proj2
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R P)
      (@comm_ring_freyd_kernel_second_object R W P Q f))
≔ @computational_weak_pullback_proj2
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_freyd_kernel_first_object R W P Q f)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_relations R P)
    (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
    (@comm_ring_presentation_matrix R P)
    (@comm_ring_freyd_kernel_second_weak_pullback R W P Q f);

// Select the whole pair only after both independent selector stages exist.
symbol comm_ring_freyd_kernel_selected_choices [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingFreydKernelChoices R P Q f)
≔ @comm_ring_freyd_kernel_choices_intro R P Q f
    (@comm_ring_freyd_kernel_first_weak_pullback R W P Q f)
    (@comm_ring_freyd_kernel_second_weak_pullback R W P Q f);

symbol comm_ring_freyd_kernel_presentation
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentation R)
≔ @comm_ring_freyd_selected_kernel_presentation R P Q f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f);

// Transparent matrix square for the kernel embedding.
symbol comm_ring_freyd_kernel_embedding_law
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R
        (@comm_ring_freyd_kernel_presentation R W P Q f)))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_relations R
          (@comm_ring_freyd_kernel_presentation R W P Q f))
        (@comm_ring_presentation_matrix R P)
        (@comm_ring_freyd_kernel_second_proj2 R W P Q f))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R
          (@comm_ring_freyd_kernel_presentation R W P Q f))
        (@comm_ring_presentation_relations R
          (@comm_ring_freyd_kernel_presentation R W P Q f))
        (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
        (@comm_ring_presentation_matrix R
          (@comm_ring_freyd_kernel_presentation R W P Q f))))
≔ @comm_ring_freyd_selected_kernel_embedding_law R P Q f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f);

symbol comm_ring_freyd_kernel_embedding_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_kernel_presentation R W P Q f) P)
≔ @comm_ring_freyd_selected_kernel_embedding_raw R P Q f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f);

symbol comm_ring_freyd_kernel_embedding
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingFreydHomSet R
      (@comm_ring_freyd_kernel_presentation R W P Q f) P)
≔ @comm_ring_freyd_selected_kernel_embedding R P Q f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f);

// Generic form of one raw presentation morphism's retained square.
symbol comm_ring_presentation_morphism_generic_law
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R P))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_presentation_morphism_witness R P Q f))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_presentation_matrix R P)))
≔ @comm_ring_presentation_morphism_finite_free_law R P Q f;

symbol comm_ring_freyd_kernel_annihilation_map
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_freyd_kernel_first_object R W P Q f))
≔ @comm_ring_freyd_selected_kernel_annihilation_map R P Q f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f);

symbol comm_ring_freyd_kernel_annihilation_zero
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_freyd_kernel_first_object R W P Q f))
≔ @comm_ring_freyd_selected_kernel_annihilation_zero R P Q f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f);

// The first weak pullback's conventional compatibility supplies annihilation.
symbol comm_ring_freyd_kernel_annihilation_agreement
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentationMorphismAgreement R
      (@comm_ring_freyd_kernel_presentation R W P Q f) Q
      (@comm_ring_freyd_kernel_annihilation_map R W P Q f)
      (@comm_ring_freyd_kernel_annihilation_zero R W P Q f))
≔ @comm_ring_freyd_selected_kernel_annihilation_agreement R P Q f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f);

symbol comm_ring_freyd_kernel_annihilation_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_freyd_kernel_presentation R W P Q f) Q)
      (@comm_ring_freyd_comp R
        (@comm_ring_freyd_kernel_presentation R W P Q f) P Q
        (@comm_ring_freyd_hom_class R P Q f)
        (@comm_ring_freyd_kernel_embedding R W P Q f))
      (@comm_ring_freyd_zero_class R
        (@comm_ring_freyd_kernel_presentation R W P Q f) Q))
≔ @comm_ring_freyd_selected_kernel_annihilation_path R P Q f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f);

// Decode an explicit zero agreement into alpha o tau = R_Q o H.
symbol comm_ring_freyd_kernel_zero_compatibility_path
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R T))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_presentation_morphism_map R T P tau))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_presentation_agreement_witness R T Q
          (@comm_ring_presentation_morphism_map R T Q
            (@comm_ring_presentation_morphism_comp R T P Q f tau))
          (@comm_ring_presentation_morphism_map R T Q
            (@comm_ring_presentation_morphism_zero R T Q))
          a)))
≔ @comm_ring_presentation_zero_agreement_finite_free_path R P Q T f tau a;

symbol comm_ring_freyd_kernel_first_cone
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@WeakPullbackCone
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero (@comm_ring_finite_free_additive R)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_presentation_generators R T))
≔ @comm_ring_freyd_selected_kernel_first_cone R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a;

symbol comm_ring_freyd_kernel_first_lift
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@CommRingMatrix R
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_presentation_generators R T))
≔ @comm_ring_freyd_selected_kernel_first_lift R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a;

symbol comm_ring_freyd_kernel_source_relations_after_first_lift
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@CommRingMatrix R
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_presentation_relations R T))
≔ @comm_ring_freyd_selected_kernel_source_relations_after_first_lift R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a;

symbol comm_ring_freyd_kernel_second_compatibility_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R T))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_freyd_kernel_first_object R W P Q f)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
        (@comm_ring_freyd_kernel_source_relations_after_first_lift
          R W P Q T f tau a))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_matrix R P)
        (@comm_ring_presentation_morphism_witness R T P tau)))
≔ @comm_ring_freyd_selected_kernel_second_compatibility_path R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a;

symbol comm_ring_freyd_kernel_second_cone
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@WeakPullbackCone
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero (@comm_ring_finite_free_additive R)
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
      (@comm_ring_presentation_matrix R P)
      (@comm_ring_presentation_relations R T))
≔ @comm_ring_freyd_selected_kernel_second_cone R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a;

symbol comm_ring_freyd_kernel_second_lift
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@CommRingMatrix R
      (@comm_ring_freyd_kernel_second_object R W P Q f)
      (@comm_ring_presentation_relations R T))
≔ @comm_ring_freyd_selected_kernel_second_lift R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a;

symbol comm_ring_freyd_kernel_lift_law
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R
        (@comm_ring_freyd_kernel_presentation R W P Q f))
      (@comm_ring_presentation_relations R T))
      (@comm_ring_matrix_comp R
        (@comm_ring_freyd_kernel_first_object R W P Q f)
        (@comm_ring_freyd_kernel_second_object R W P Q f)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_matrix R
          (@comm_ring_freyd_kernel_presentation R W P Q f))
        (@comm_ring_freyd_kernel_second_lift R W P Q T f tau a))
      (@comm_ring_matrix_comp R
        (@comm_ring_freyd_kernel_first_object R W P Q f)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_freyd_kernel_first_lift R W P Q T f tau a)
        (@comm_ring_presentation_matrix R T)))
≔ @comm_ring_freyd_selected_kernel_lift_law R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a;

symbol comm_ring_freyd_kernel_lift_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@CommRingPresentationMorphism R T
      (@comm_ring_freyd_kernel_presentation R W P Q f))
≔ @comm_ring_freyd_selected_kernel_lift_raw R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a;

symbol comm_ring_freyd_kernel_lift
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@CommRingFreydHomSet R T
      (@comm_ring_freyd_kernel_presentation R W P Q f))
≔ @comm_ring_freyd_selected_kernel_lift R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a;

symbol comm_ring_freyd_kernel_reconstruction_map_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R T))
      (@comm_ring_presentation_morphism_map R T P
        (@comm_ring_presentation_morphism_comp R T
          (@comm_ring_freyd_kernel_presentation R W P Q f) P
          (@comm_ring_freyd_kernel_embedding_raw R W P Q f)
          (@comm_ring_freyd_kernel_lift_raw R W P Q T f tau a)))
      (@comm_ring_presentation_morphism_map R T P tau))
≔ @comm_ring_freyd_selected_kernel_reconstruction_map_path R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a;

symbol comm_ring_freyd_kernel_reconstruction_agreement
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@CommRingPresentationMorphismAgreement R T P
      (@comm_ring_presentation_morphism_map R T P
        (@comm_ring_presentation_morphism_comp R T
          (@comm_ring_freyd_kernel_presentation R W P Q f) P
          (@comm_ring_freyd_kernel_embedding_raw R W P Q f)
          (@comm_ring_freyd_kernel_lift_raw R W P Q T f tau a)))
      (@comm_ring_presentation_morphism_map R T P tau))
≔ @comm_ring_freyd_selected_kernel_reconstruction_agreement R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a;

symbol comm_ring_freyd_kernel_reconstruction_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@= (@CommRingFreydHomSet R T P)
      (@comm_ring_freyd_comp R T
        (@comm_ring_freyd_kernel_presentation R W P Q f) P
        (@comm_ring_freyd_kernel_embedding R W P Q f)
        (@comm_ring_freyd_kernel_lift R W P Q T f tau a))
      (@comm_ring_freyd_hom_class R T P tau))
≔ @comm_ring_freyd_selected_kernel_reconstruction_path R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a;

symbol comm_ring_freyd_kernel_competing_difference
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  (k : τ (@CommRingPresentationMorphism R T
    (@comm_ring_freyd_kernel_presentation R W P Q f)))
  : τ (@CommRingMatrix R
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_presentation_generators R T))
≔ @comm_ring_freyd_selected_kernel_competing_difference R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a k;

symbol comm_ring_freyd_kernel_uniqueness_compatibility_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
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
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R T))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_freyd_kernel_first_object R W P Q f)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
        (@comm_ring_freyd_kernel_competing_difference
          R W P Q T f tau a k))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_matrix R P)
        (@comm_ring_presentation_agreement_witness R T P
          (@comm_ring_presentation_morphism_map R T P
            (@comm_ring_presentation_morphism_comp R T
              (@comm_ring_freyd_kernel_presentation R W P Q f) P
              (@comm_ring_freyd_kernel_embedding_raw R W P Q f) k))
          (@comm_ring_presentation_morphism_map R T P tau)
          reconstructs)))
≔ @comm_ring_freyd_selected_kernel_uniqueness_compatibility_path R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a k reconstructs;

symbol comm_ring_freyd_kernel_uniqueness_cone
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
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
  : τ (@WeakPullbackCone
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero (@comm_ring_finite_free_additive R)
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
      (@comm_ring_presentation_matrix R P)
      (@comm_ring_presentation_generators R T))
≔ @comm_ring_freyd_selected_kernel_uniqueness_cone R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a k reconstructs;

symbol comm_ring_freyd_kernel_uniqueness_witness
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
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
  : τ (@CommRingMatrix R
      (@comm_ring_freyd_kernel_second_object R W P Q f)
      (@comm_ring_presentation_generators R T))
≔ @comm_ring_freyd_selected_kernel_uniqueness_witness R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a k reconstructs;

symbol comm_ring_freyd_kernel_uniqueness_agreement
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
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
  : τ (@CommRingPresentationMorphismAgreement R T
      (@comm_ring_freyd_kernel_presentation R W P Q f)
      (@comm_ring_presentation_morphism_map R T
        (@comm_ring_freyd_kernel_presentation R W P Q f) k)
      (@comm_ring_freyd_kernel_first_lift R W P Q T f tau a))
≔ @comm_ring_freyd_selected_kernel_uniqueness_agreement R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a k reconstructs;

symbol comm_ring_freyd_kernel_uniqueness_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
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
  : τ (@= (@CommRingFreydHomSet R T
      (@comm_ring_freyd_kernel_presentation R W P Q f))
      (@comm_ring_freyd_hom_class R T
        (@comm_ring_freyd_kernel_presentation R W P Q f) k)
      (@comm_ring_freyd_kernel_lift R W P Q T f tau a))
≔ @comm_ring_freyd_selected_kernel_uniqueness_path R P Q T f
    (@comm_ring_freyd_kernel_selected_choices R W P Q f)
    tau a k reconstructs;
