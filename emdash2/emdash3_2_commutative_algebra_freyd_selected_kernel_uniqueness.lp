/*
  Uniqueness of selected-choice Freyd kernel lifts.

  A competitor's reconstruction agreement turns its difference from the
  selected lift into a cone for the retained second weak pullback. Its factor
  supplies a raw equality witness, followed by the original quotient path.
  No arbitrary quotient-path decoding or unique base factor is assumed.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_selected_kernel_lifting;

symbol comm_ring_freyd_selected_kernel_competing_difference
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
  (k : τ (@CommRingPresentationMorphism R T
    (@comm_ring_freyd_selected_kernel_presentation R P Q f K)))
  : τ (@CommRingMatrix R
      (@comm_ring_freyd_selected_kernel_rank R P Q f K)
      (@comm_ring_presentation_generators R T))
≔ @comm_ring_matrix_sub R
    (@comm_ring_freyd_selected_kernel_rank R P Q f K)
    (@comm_ring_presentation_generators R T)
    (@comm_ring_presentation_morphism_map R T
      (@comm_ring_freyd_selected_kernel_presentation R P Q f K) k)
    (@comm_ring_freyd_selected_kernel_first_lift R P Q T f K tau a);

symbol comm_ring_freyd_selected_kernel_uniqueness_compatibility_path
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
  (k : τ (@CommRingPresentationMorphism R T
    (@comm_ring_freyd_selected_kernel_presentation R P Q f K)))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T P
    (@comm_ring_presentation_morphism_map R T P
      (@comm_ring_presentation_morphism_comp R T
        (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
        (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K) k))
    (@comm_ring_presentation_morphism_map R T P tau)))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R T))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_freyd_selected_kernel_rank R P Q f K)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_selected_kernel_projection R P Q f K)
        (@comm_ring_freyd_selected_kernel_competing_difference
          R P Q T f K tau a k))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_matrix R P)
        (@comm_ring_presentation_agreement_witness R T P
          (@comm_ring_presentation_morphism_map R T P
            (@comm_ring_presentation_morphism_comp R T
              (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
              (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K) k))
          (@comm_ring_presentation_morphism_map R T P tau)
          reconstructs)))
≔ @eq_trans _ _
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_freyd_selected_kernel_rank R P Q f K)
      (@comm_ring_presentation_generators R T)
      (@comm_ring_freyd_selected_kernel_projection R P Q f K)
      (@comm_ring_freyd_selected_kernel_competing_difference
        R P Q T f K tau a k))
    _
    (@comm_ring_finite_free_comp_fapp0_transparent_path R
      (@comm_ring_presentation_generators R T)
      (@comm_ring_freyd_selected_kernel_rank R P Q f K)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_freyd_selected_kernel_projection R P Q f K)
      (@comm_ring_freyd_selected_kernel_competing_difference
        R P Q T f K tau a k))
    (@eq_trans _ _
      (@comm_ring_matrix_sub R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R P)
          (@comm_ring_freyd_selected_kernel_rank R P Q f K)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_freyd_selected_kernel_projection R P Q f K)
          (@comm_ring_presentation_morphism_map R T
            (@comm_ring_freyd_selected_kernel_presentation R P Q f K) k))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R P)
          (@comm_ring_freyd_selected_kernel_rank R P Q f K)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_freyd_selected_kernel_projection R P Q f K)
          (@comm_ring_freyd_selected_kernel_first_lift R P Q T f K tau a)))
      _
      (@comm_ring_matrix_comp_sub_right_path R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_selected_kernel_rank R P Q f K)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_freyd_selected_kernel_projection R P Q f K)
        (@comm_ring_presentation_morphism_map R T
          (@comm_ring_freyd_selected_kernel_presentation R P Q f K) k)
        (@comm_ring_freyd_selected_kernel_first_lift R P Q T f K tau a))
      (@eq_trans _ _
        (@comm_ring_matrix_sub R
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_morphism_map R T P
            (@comm_ring_presentation_morphism_comp R T
              (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
              (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K) k))
          (@comm_ring_presentation_morphism_map R T P tau))
        _
        (@eq_ap
          (@CommRingMatrix R
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_generators R T))
          (@CommRingMatrix R
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_generators R T))
          (λ z : τ (@CommRingMatrix R
              (@comm_ring_presentation_generators R P)
              (@comm_ring_presentation_generators R T)),
            @comm_ring_matrix_sub R
              (@comm_ring_presentation_generators R P)
              (@comm_ring_presentation_generators R T)
              (@comm_ring_presentation_morphism_map R T P
                (@comm_ring_presentation_morphism_comp R T
                  (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
                  (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K) k)) z)
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R P)
            (@comm_ring_freyd_selected_kernel_rank R P Q f K)
            (@comm_ring_presentation_generators R T)
            (@comm_ring_freyd_selected_kernel_projection R P Q f K)
            (@comm_ring_freyd_selected_kernel_first_lift R P Q T f K tau a))
          (@comm_ring_presentation_morphism_map R T P tau)
          (@comm_ring_freyd_selected_kernel_reconstruction_map_path
            R P Q T f K tau a))
        (@eq_trans _ _
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_relations R P)
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_matrix R P)
            (@comm_ring_presentation_agreement_witness R T P
              (@comm_ring_presentation_morphism_map R T P
                (@comm_ring_presentation_morphism_comp R T
                  (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
                  (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K) k))
              (@comm_ring_presentation_morphism_map R T P tau)
              reconstructs))
          _
          (@eq_sym _ _ _
            (@comm_ring_presentation_agreement_law R T P
              (@comm_ring_presentation_morphism_map R T P
                (@comm_ring_presentation_morphism_comp R T
                  (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
                  (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K) k))
              (@comm_ring_presentation_morphism_map R T P tau)
              reconstructs))
          (@eq_sym _ _ _
            (@comm_ring_finite_free_comp_fapp0_transparent_path R
              (@comm_ring_presentation_generators R T)
              (@comm_ring_presentation_relations R P)
              (@comm_ring_presentation_generators R P)
              (@comm_ring_presentation_matrix R P)
              (@comm_ring_presentation_agreement_witness R T P
                (@comm_ring_presentation_morphism_map R T P
                  (@comm_ring_presentation_morphism_comp R T
                    (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
                    (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K) k))
                (@comm_ring_presentation_morphism_map R T P tau)
                reconstructs))))));

symbol comm_ring_freyd_selected_kernel_uniqueness_cone
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
  (k : τ (@CommRingPresentationMorphism R T
    (@comm_ring_freyd_selected_kernel_presentation R P Q f K)))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T P
    (@comm_ring_presentation_morphism_map R T P
      (@comm_ring_presentation_morphism_comp R T
        (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
        (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K) k))
    (@comm_ring_presentation_morphism_map R T P tau)))
  : τ (@WeakPullbackCone
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero (@comm_ring_finite_free_additive R)
      (@comm_ring_freyd_selected_kernel_rank R P Q f K)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_freyd_selected_kernel_projection R P Q f K)
      (@comm_ring_presentation_matrix R P)
      (@comm_ring_presentation_generators R T))
≔ @weak_pullback_cone_intro
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_freyd_selected_kernel_rank R P Q f K)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_relations R P)
    (@comm_ring_presentation_generators R T)
    (@comm_ring_freyd_selected_kernel_projection R P Q f K)
    (@comm_ring_presentation_matrix R P)
    (@comm_ring_freyd_selected_kernel_competing_difference R P Q T f K tau a k)
    (@comm_ring_presentation_agreement_witness R T P
      (@comm_ring_presentation_morphism_map R T P
        (@comm_ring_presentation_morphism_comp R T
          (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
          (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K) k))
      (@comm_ring_presentation_morphism_map R T P tau)
      reconstructs)
    (@comm_ring_freyd_selected_kernel_uniqueness_compatibility_path
      R P Q T f K tau a k reconstructs);

symbol comm_ring_freyd_selected_kernel_uniqueness_witness
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
  (k : τ (@CommRingPresentationMorphism R T
    (@comm_ring_freyd_selected_kernel_presentation R P Q f K)))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T P
    (@comm_ring_presentation_morphism_map R T P
      (@comm_ring_presentation_morphism_comp R T
        (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
        (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K) k))
    (@comm_ring_presentation_morphism_map R T P tau)))
  : τ (@CommRingMatrix R
      (@comm_ring_freyd_selected_kernel_relation_rank R P Q f K)
      (@comm_ring_presentation_generators R T))
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
    (@comm_ring_presentation_generators R T)
    (@comm_ring_freyd_selected_kernel_uniqueness_cone
      R P Q T f K tau a k reconstructs);

symbol comm_ring_freyd_selected_kernel_uniqueness_agreement
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
  (k : τ (@CommRingPresentationMorphism R T
    (@comm_ring_freyd_selected_kernel_presentation R P Q f K)))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T P
    (@comm_ring_presentation_morphism_map R T P
      (@comm_ring_presentation_morphism_comp R T
        (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
        (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K) k))
    (@comm_ring_presentation_morphism_map R T P tau)))
  : τ (@CommRingPresentationMorphismAgreement R T
      (@comm_ring_freyd_selected_kernel_presentation R P Q f K)
      (@comm_ring_presentation_morphism_map R T
        (@comm_ring_freyd_selected_kernel_presentation R P Q f K) k)
      (@comm_ring_freyd_selected_kernel_first_lift R P Q T f K tau a))
≔ @comm_ring_presentation_morphism_agreement_intro R T
    (@comm_ring_freyd_selected_kernel_presentation R P Q f K)
    (@comm_ring_presentation_morphism_map R T
      (@comm_ring_freyd_selected_kernel_presentation R P Q f K) k)
    (@comm_ring_freyd_selected_kernel_first_lift R P Q T f K tau a)
    (@comm_ring_freyd_selected_kernel_uniqueness_witness
      R P Q T f K tau a k reconstructs)
    (@eq_trans _ _
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_freyd_selected_kernel_relation_rank R P Q f K)
        (@comm_ring_freyd_selected_kernel_rank R P Q f K)
        (@comm_ring_freyd_selected_kernel_relation_matrix R P Q f K)
        (@comm_ring_freyd_selected_kernel_uniqueness_witness
          R P Q T f K tau a k reconstructs))
      (@comm_ring_freyd_selected_kernel_competing_difference R P Q T f K tau a k)
      (@eq_sym _ _ _
        (@comm_ring_finite_free_comp_fapp0_transparent_path R
          (@comm_ring_presentation_generators R T)
          (@comm_ring_freyd_selected_kernel_relation_rank R P Q f K)
          (@comm_ring_freyd_selected_kernel_rank R P Q f K)
          (@comm_ring_freyd_selected_kernel_relation_matrix R P Q f K)
          (@comm_ring_freyd_selected_kernel_uniqueness_witness
            R P Q T f K tau a k reconstructs)))
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
        (@comm_ring_presentation_generators R T)
        (@comm_ring_freyd_selected_kernel_uniqueness_cone
          R P Q T f K tau a k reconstructs)));

// A reconstructed competitor equals the selected lift in the actual quotient.
symbol comm_ring_freyd_selected_kernel_uniqueness_path
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
  (k : τ (@CommRingPresentationMorphism R T
    (@comm_ring_freyd_selected_kernel_presentation R P Q f K)))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T P
    (@comm_ring_presentation_morphism_map R T P
      (@comm_ring_presentation_morphism_comp R T
        (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
        (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K) k))
    (@comm_ring_presentation_morphism_map R T P tau)))
  : τ (@= (@CommRingFreydHomSet R T
      (@comm_ring_freyd_selected_kernel_presentation R P Q f K))
      (@comm_ring_freyd_hom_class R T
        (@comm_ring_freyd_selected_kernel_presentation R P Q f K) k)
      (@comm_ring_freyd_selected_kernel_lift R P Q T f K tau a))
≔ @comm_ring_freyd_agreement_path R T
    (@comm_ring_freyd_selected_kernel_presentation R P Q f K)
    k
    (@comm_ring_freyd_selected_kernel_lift_raw R P Q T f K tau a)
    (@comm_ring_freyd_selected_kernel_uniqueness_agreement
      R P Q T f K tau a k reconstructs);
