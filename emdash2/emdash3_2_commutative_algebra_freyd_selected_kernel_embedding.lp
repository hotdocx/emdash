/*
  Raw kernel embedding and annihilation at two retained weak-pullback choices.

  The second compatibility path supplies relation preservation; the first
  supplies annihilation modulo target relations. All data refer to the actual
  selected ranks and presentation. The global weak-kernel selector is absent.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_kernel_choices;
require open emdash.emdash3_2_commutative_algebra_freyd_kernel_compatibility;

// The second weak pullback's other projection preserves source relations.
symbol comm_ring_freyd_selected_kernel_relation_witness [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)] [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  : τ (@CommRingMatrix R (@comm_ring_presentation_relations R P)
    (@comm_ring_freyd_selected_kernel_relation_rank R P Q f K))
≔ @comm_ring_finite_free_weak_pullback_proj2 R
    (@comm_ring_freyd_selected_kernel_rank R P Q f K)
    (@comm_ring_presentation_generators R P) (@comm_ring_presentation_relations R P)
    (@comm_ring_freyd_selected_kernel_projection R P Q f K)
    (@comm_ring_presentation_matrix R P)
    (@comm_ring_freyd_kernel_choices_second R P Q f K);

// R_P o second.proj2 = first.proj1 o second.proj1.
symbol comm_ring_freyd_selected_kernel_embedding_law [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)] [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  : τ (@= (@CommRingMatrix R (@comm_ring_presentation_generators R P)
    (@comm_ring_freyd_selected_kernel_relation_rank R P Q f K))
    (@comm_ring_matrix_comp R (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P) (@comm_ring_freyd_selected_kernel_relation_rank R P Q f K)
      (@comm_ring_presentation_matrix R P) (@comm_ring_freyd_selected_kernel_relation_witness R P Q f K))
    (@comm_ring_matrix_comp R (@comm_ring_presentation_generators R P)
      (@comm_ring_freyd_selected_kernel_rank R P Q f K)
      (@comm_ring_freyd_selected_kernel_relation_rank R P Q f K)
      (@comm_ring_freyd_selected_kernel_projection R P Q f K)
      (@comm_ring_freyd_selected_kernel_relation_matrix R P Q f K)))
≔ @eq_sym _ _ _ (@comm_ring_finite_free_weak_pullback_matrix_compatibility R
    (@comm_ring_freyd_selected_kernel_rank R P Q f K)
    (@comm_ring_presentation_generators R P) (@comm_ring_presentation_relations R P)
    (@comm_ring_freyd_selected_kernel_projection R P Q f K)
    (@comm_ring_presentation_matrix R P)
    (@comm_ring_freyd_kernel_choices_second R P Q f K));

symbol comm_ring_freyd_selected_kernel_embedding_raw [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)] [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  : τ (@CommRingPresentationMorphism R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P)
≔ @comm_ring_presentation_morphism_intro R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
    (@comm_ring_freyd_selected_kernel_projection R P Q f K)
    (@comm_ring_freyd_selected_kernel_relation_witness R P Q f K)
    (@comm_ring_freyd_selected_kernel_embedding_law R P Q f K);

symbol comm_ring_freyd_selected_kernel_embedding [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)] [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  : τ (@CommRingFreydHomSet R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P)
≔ @comm_ring_freyd_hom_class R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
    (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K);

// The first weak pullback's other projection witnesses annihilation modulo R_Q.
symbol comm_ring_freyd_selected_kernel_annihilation_witness [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)] [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  : τ (@CommRingMatrix R (@comm_ring_presentation_relations R Q)
    (@comm_ring_freyd_selected_kernel_rank R P Q f K))
≔ @comm_ring_finite_free_weak_pullback_proj2 R
    (@comm_ring_presentation_generators R P) (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_morphism_map R P Q f) (@comm_ring_presentation_matrix R Q)
    (@comm_ring_freyd_kernel_choices_first R P Q f K);

symbol comm_ring_freyd_selected_kernel_annihilation_map [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)] [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  : τ (@CommRingMatrix R (@comm_ring_presentation_generators R Q)
    (@comm_ring_freyd_selected_kernel_rank R P Q f K))
≔ @comm_ring_matrix_comp R (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_generators R P) (@comm_ring_freyd_selected_kernel_rank R P Q f K)
    (@comm_ring_presentation_morphism_map R P Q f) (@comm_ring_freyd_selected_kernel_projection R P Q f K);

// Selected zero matrix used by the annihilation agreement.
symbol comm_ring_freyd_selected_kernel_annihilation_zero [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)] [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  : τ (@CommRingMatrix R (@comm_ring_presentation_generators R Q)
    (@comm_ring_freyd_selected_kernel_rank R P Q f K))
≔ @comm_ring_matrix_zero R (@comm_ring_presentation_generators R Q)
    (@comm_ring_freyd_selected_kernel_rank R P Q f K);

symbol comm_ring_freyd_selected_kernel_annihilation_agreement [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)] [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  : τ (@CommRingPresentationMorphismAgreement R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) Q
    (@comm_ring_freyd_selected_kernel_annihilation_map R P Q f K)
    (@comm_ring_matrix_zero R (@comm_ring_presentation_generators R Q)
      (@comm_ring_freyd_selected_kernel_rank R P Q f K)))
≔ @comm_ring_presentation_morphism_agreement_intro R
    (@comm_ring_freyd_selected_kernel_presentation R P Q f K) Q
    (@comm_ring_freyd_selected_kernel_annihilation_map R P Q f K)
    (@comm_ring_matrix_zero R (@comm_ring_presentation_generators R Q)
      (@comm_ring_freyd_selected_kernel_rank R P Q f K))
    (@comm_ring_freyd_selected_kernel_annihilation_witness R P Q f K)
    (@eq_trans _ _ (@comm_ring_freyd_selected_kernel_annihilation_map R P Q f K) _
      (@eq_sym _ _ _ (@comm_ring_finite_free_weak_pullback_matrix_compatibility R
        (@comm_ring_presentation_generators R P) (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_morphism_map R P Q f) (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_kernel_choices_first R P Q f K)))
      (@eq_sym _ _ _ (@comm_ring_freyd_cokernel_sub_zero_path R
        (@comm_ring_presentation_generators R Q) (@comm_ring_freyd_selected_kernel_rank R P Q f K)
        (@comm_ring_freyd_selected_kernel_annihilation_map R P Q f K))));

symbol comm_ring_freyd_selected_kernel_annihilation_path [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)] [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  : τ (@= (@CommRingFreydHomSet R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) Q)
    (@comm_ring_freyd_comp R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P Q
      (@comm_ring_freyd_hom_class R P Q f)
      (@comm_ring_freyd_hom_class R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P
        (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K)))
    (@comm_ring_freyd_zero_class R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) Q))
≔ @comm_ring_freyd_agreement_path R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) Q
    (@comm_ring_presentation_morphism_comp R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) P Q
      f (@comm_ring_freyd_selected_kernel_embedding_raw R P Q f K))
    (@comm_ring_presentation_morphism_zero R (@comm_ring_freyd_selected_kernel_presentation R P Q f K) Q)
    (@comm_ring_freyd_selected_kernel_annihilation_agreement R P Q f K);
