/*
  Selected-choice raw Freyd kernel lifts and reconstruction.

  An explicit zero agreement forms the first cone; the test's relation law
  forms the second. The retained universal factor operations construct both
  matrices of a genuine raw presentation morphism. Projection reconstruction
  gives the original test in the Freyd quotient, without a rank transport.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_selected_kernel_embedding;

symbol comm_ring_freyd_selected_kernel_first_cone
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
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
≔ @weak_pullback_cone_intro
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_generators R T)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_matrix R Q)
    (@comm_ring_presentation_morphism_map R T P tau)
    (@comm_ring_presentation_agreement_witness R T Q
      (@comm_ring_presentation_morphism_map R T Q
        (@comm_ring_presentation_morphism_comp R T P Q f tau))
      (@comm_ring_presentation_morphism_map R T Q
        (@comm_ring_presentation_morphism_zero R T Q))
      a)
    (@comm_ring_presentation_zero_agreement_finite_free_path R P Q T f tau a);

symbol comm_ring_freyd_selected_kernel_first_lift
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@CommRingMatrix R
      (@comm_ring_freyd_selected_kernel_rank R P Q f K)
      (@comm_ring_presentation_generators R T))
≔ @computational_weak_pullback_lift
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_matrix R Q)
    (@comm_ring_freyd_kernel_choices_first R P Q f K)
    (@comm_ring_presentation_generators R T)
    (@comm_ring_freyd_selected_kernel_first_cone R P Q T f K tau a);

symbol comm_ring_freyd_selected_kernel_source_relations_after_first_lift
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@CommRingMatrix R
      (@comm_ring_freyd_selected_kernel_rank R P Q f K)
      (@comm_ring_presentation_relations R T))
≔ @comp_fapp0 (@CommRingFiniteFree_cat R)
    (@comm_ring_presentation_relations R T)
    (@comm_ring_presentation_generators R T)
    (@comm_ring_freyd_selected_kernel_rank R P Q f K)
    (@comm_ring_freyd_selected_kernel_first_lift R P Q T f K tau a)
    (@comm_ring_presentation_matrix R T);

symbol comm_ring_freyd_selected_kernel_second_compatibility_path
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
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
        (@comm_ring_freyd_selected_kernel_rank R P Q f K)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_selected_kernel_projection R P Q f K)
        (@comm_ring_freyd_selected_kernel_source_relations_after_first_lift
          R P Q T f K tau a))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_matrix R P)
        (@comm_ring_presentation_morphism_witness R T P tau)))
≔ @eq_trans _ _
    (@comp_fapp0 (@CommRingFiniteFree_cat R)
      (@comm_ring_presentation_relations R T)
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_generators R P)
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_freyd_selected_kernel_rank R P Q f K)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_selected_kernel_projection R P Q f K)
        (@comm_ring_freyd_selected_kernel_first_lift R P Q T f K tau a))
      (@comm_ring_presentation_matrix R T))
    _
    (@comp_assoc (@CommRingFiniteFree_cat R)
      (@comm_ring_presentation_relations R T)
      (@comm_ring_presentation_generators R T)
      (@comm_ring_freyd_selected_kernel_rank R P Q f K)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_freyd_selected_kernel_projection R P Q f K)
      (@comm_ring_freyd_selected_kernel_first_lift R P Q T f K tau a)
      (@comm_ring_presentation_matrix R T))
    (@eq_trans _ _
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_morphism_map R T P tau)
        (@comm_ring_presentation_matrix R T))
      _
      (@eq_ap
        (@CommRingMatrix R
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R T))
        (@CommRingMatrix R
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_relations R T))
        (λ u : τ (@CommRingMatrix R
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_generators R T)),
          @comp_fapp0 (@CommRingFiniteFree_cat R)
            (@comm_ring_presentation_relations R T)
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_generators R P)
            u (@comm_ring_presentation_matrix R T))
        _ _
        (@computational_weak_pullback_lift_proj1_path
          (@CommRingFiniteFree_cat R)
          (@comm_ring_finite_free_direct_sum_func R)
          zero (@comm_ring_finite_free_additive R)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_kernel_choices_first R P Q f K)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_freyd_selected_kernel_first_cone R P Q T f K tau a)))
      (@eq_sym _ _ _
        (@comm_ring_presentation_morphism_finite_free_law R T P tau)));

symbol comm_ring_freyd_selected_kernel_second_cone
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
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
      (@comm_ring_freyd_selected_kernel_rank R P Q f K)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_freyd_selected_kernel_projection R P Q f K)
      (@comm_ring_presentation_matrix R P)
      (@comm_ring_presentation_relations R T))
≔ @weak_pullback_cone_intro
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_freyd_selected_kernel_rank R P Q f K)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_relations R P)
    (@comm_ring_presentation_relations R T)
    (@comm_ring_freyd_selected_kernel_projection R P Q f K)
    (@comm_ring_presentation_matrix R P)
    (@comm_ring_freyd_selected_kernel_source_relations_after_first_lift
      R P Q T f K tau a)
    (@comm_ring_presentation_morphism_witness R T P tau)
    (@comm_ring_freyd_selected_kernel_second_compatibility_path
      R P Q T f K tau a);

symbol comm_ring_freyd_selected_kernel_second_lift
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@CommRingMatrix R
      (@comm_ring_freyd_selected_kernel_relation_rank R P Q f K)
      (@comm_ring_presentation_relations R T))
≔ @computational_weak_pullback_lift
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_freyd_selected_kernel_rank R P Q f K)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_relations R P)
    (@comm_ring_freyd_selected_kernel_projection R P Q f K)
    (@comm_ring_presentation_matrix R P)
    (@comm_ring_freyd_kernel_choices_second R P Q f K)
    (@comm_ring_presentation_relations R T)
    (@comm_ring_freyd_selected_kernel_second_cone R P Q T f K tau a);

symbol comm_ring_freyd_selected_kernel_lift_law
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R
        (@comm_ring_freyd_selected_kernel_presentation R P Q f K))
      (@comm_ring_presentation_relations R T))
      (@comm_ring_matrix_comp R
        (@comm_ring_freyd_selected_kernel_rank R P Q f K)
        (@comm_ring_freyd_selected_kernel_relation_rank R P Q f K)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_matrix R
          (@comm_ring_freyd_selected_kernel_presentation R P Q f K))
        (@comm_ring_freyd_selected_kernel_second_lift R P Q T f K tau a))
      (@comm_ring_matrix_comp R
        (@comm_ring_freyd_selected_kernel_rank R P Q f K)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_freyd_selected_kernel_first_lift R P Q T f K tau a)
        (@comm_ring_presentation_matrix R T)))
≔ @eq_trans _ _
    (@comp_fapp0 (@CommRingFiniteFree_cat R)
      (@comm_ring_presentation_relations R T)
      (@comm_ring_freyd_selected_kernel_relation_rank R P Q f K)
      (@comm_ring_freyd_selected_kernel_rank R P Q f K)
      (@comm_ring_presentation_matrix R
        (@comm_ring_freyd_selected_kernel_presentation R P Q f K))
      (@comm_ring_freyd_selected_kernel_second_lift R P Q T f K tau a))
    _
    (@eq_sym _ _ _
      (@comm_ring_finite_free_comp_fapp0_transparent_path R
        (@comm_ring_presentation_relations R T)
        (@comm_ring_freyd_selected_kernel_relation_rank R P Q f K)
        (@comm_ring_freyd_selected_kernel_rank R P Q f K)
        (@comm_ring_presentation_matrix R
          (@comm_ring_freyd_selected_kernel_presentation R P Q f K))
        (@comm_ring_freyd_selected_kernel_second_lift R P Q T f K tau a)))
    (@eq_trans _ _
      (@comm_ring_freyd_selected_kernel_source_relations_after_first_lift
        R P Q T f K tau a)
      _
      (@computational_weak_pullback_lift_proj1_path
        (@CommRingFiniteFree_cat R)
        (@comm_ring_finite_free_direct_sum_func R)
        zero (@comm_ring_finite_free_additive R)
        (@comm_ring_freyd_selected_kernel_rank R P Q f K)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_freyd_selected_kernel_projection R P Q f K)
        (@comm_ring_presentation_matrix R P)
        (@comm_ring_freyd_kernel_choices_second R P Q f K)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_freyd_selected_kernel_second_cone R P Q T f K tau a))
      (@comm_ring_finite_free_comp_fapp0_transparent_path R
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_freyd_selected_kernel_rank R P Q f K)
        (@comm_ring_freyd_selected_kernel_first_lift R P Q T f K tau a)
        (@comm_ring_presentation_matrix R T)));

// The all-test construction returns a genuine relation-preserving raw arrow.
symbol comm_ring_freyd_selected_kernel_lift_raw
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@CommRingPresentationMorphism R T
      (@comm_ring_freyd_selected_kernel_presentation R P Q f K))
≔ @comm_ring_presentation_morphism_intro R T
    (@comm_ring_freyd_selected_kernel_presentation R P Q f K)
    (@comm_ring_freyd_selected_kernel_first_lift R P Q T f K tau a)
    (@comm_ring_freyd_selected_kernel_second_lift R P Q T f K tau a)
    (@comm_ring_freyd_selected_kernel_lift_law R P Q T f K tau a);

symbol comm_ring_freyd_selected_kernel_lift
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@CommRingFreydHomSet R T
      (@comm_ring_freyd_selected_kernel_presentation R P Q f K))
≔ @comm_ring_freyd_hom_class R T
    (@comm_ring_freyd_selected_kernel_presentation R P Q f K)
    (@comm_ring_freyd_selected_kernel_lift_raw R P Q T f K tau a);

symbol comm_ring_freyd_selected_kernel_reconstruction_map_path
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
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
          (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
          (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K)
          (@comm_ring_freyd_selected_kernel_lift_raw R P Q T f K tau a)))
      (@comm_ring_presentation_morphism_map R T P tau))
≔ @eq_trans _ _
    (@comp_fapp0 (@CommRingFiniteFree_cat R)
      (@comm_ring_presentation_generators R T)
      (@comm_ring_freyd_selected_kernel_rank R P Q f K)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_freyd_selected_kernel_projection R P Q f K)
      (@comm_ring_freyd_selected_kernel_first_lift R P Q T f K tau a))
    (@comm_ring_presentation_morphism_map R T P tau)
    (@eq_sym _ _ _
      (@comm_ring_finite_free_comp_fapp0_transparent_path R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_freyd_selected_kernel_rank R P Q f K)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_selected_kernel_projection R P Q f K)
        (@comm_ring_freyd_selected_kernel_first_lift R P Q T f K tau a)))
    (@computational_weak_pullback_lift_proj1_path
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero (@comm_ring_finite_free_additive R)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_freyd_kernel_choices_first R P Q f K)
      (@comm_ring_presentation_generators R T)
      (@comm_ring_freyd_selected_kernel_first_cone R P Q T f K tau a));

symbol comm_ring_freyd_selected_kernel_reconstruction_agreement
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@CommRingPresentationMorphismAgreement R T P
      (@comm_ring_presentation_morphism_map R T P
        (@comm_ring_presentation_morphism_comp R T
          (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
          (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K)
          (@comm_ring_freyd_selected_kernel_lift_raw R P Q T f K tau a)))
      (@comm_ring_presentation_morphism_map R T P tau))
≔ @comm_ring_presentation_agreement_of_map_path R T P
    (@comm_ring_presentation_morphism_map R T P
      (@comm_ring_presentation_morphism_comp R T
        (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
        (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K)
        (@comm_ring_freyd_selected_kernel_lift_raw R P Q T f K tau a)))
    (@comm_ring_presentation_morphism_map R T P tau)
    (@comm_ring_freyd_selected_kernel_reconstruction_map_path
      R P Q T f K tau a);

symbol comm_ring_freyd_selected_kernel_reconstruction_path
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@= (@CommRingFreydHomSet R T P)
      (@comm_ring_freyd_comp R T
        (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
        (@comm_ring_freyd_selected_kernel_embedding R P Q f K)
        (@comm_ring_freyd_selected_kernel_lift R P Q T f K tau a))
      (@comm_ring_freyd_hom_class R T P tau))
≔ @comm_ring_freyd_agreement_path R T P
    (@comm_ring_presentation_morphism_comp R T
      (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
      (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K)
      (@comm_ring_freyd_selected_kernel_lift_raw R P Q T f K tau a))
    tau
    (@comm_ring_freyd_selected_kernel_reconstruction_agreement R P Q T f K tau a);
