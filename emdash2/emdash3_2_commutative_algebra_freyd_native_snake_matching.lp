/* Endpoint matching for the original native and raw complete-arrow observations. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_snake_observations;
require open emdash.emdash3_2_commutative_algebra_freyd_observation_coherence;

symbol freyd_native_snake_first_pair_matching [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (@= (@CommRingPresentation R)
    (@freyd_arrow_observation_target R (@freyd_raw_native_snake_kernel_first_observation R M A B X D a b c z))
  (@freyd_arrow_observation_source R (@freyd_raw_native_snake_kernel_second_observation R M A B X D a b c z)))
≔ @eq_refl (@CommRingPresentation R) (@fapp0 Terminal_cat (@CommRingFreydPresentation_cat R)
  (@kernel_adjunction_family_func Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R)
  B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) Terminal_obj);

symbol freyd_native_snake_second_pair_matching [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (@= (@CommRingPresentation R)
    (@freyd_arrow_observation_target R (@freyd_raw_native_snake_kernel_second_observation R M A B X D a b c
  z)) (@freyd_arrow_observation_source R (@freyd_raw_native_snake_connecting_observation R M N A B X D a b c
  z)))
≔ @eq_refl (@CommRingPresentation R) (@fapp0 Terminal_cat (@CommRingFreydPresentation_cat R)
  (@kernel_adjunction_family_func Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_kernels R M) (@one_cat_native_snake_gamma_diagram
  Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))) Terminal_obj);

symbol freyd_native_snake_third_pair_matching [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (@= (@CommRingPresentation R)
    (@freyd_arrow_observation_target R (@freyd_raw_native_snake_connecting_observation R M N A B X D a b c z))
  (@freyd_arrow_observation_source R (@freyd_raw_native_snake_cokernel_first_observation R M A B X D a b c
  z)))
≔ @eq_refl (@CommRingPresentation R) (@fapp0 Terminal_cat (@CommRingFreydPresentation_cat R)
  (@cokernel_adjunction_family_func Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@one_cat_native_snake_alpha_diagram Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))) Terminal_obj);

symbol freyd_native_snake_fourth_pair_matching [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (@= (@CommRingPresentation R)
    (@freyd_arrow_observation_target R (@freyd_raw_native_snake_cokernel_first_observation R M A B X D a b c
  z)) (@freyd_arrow_observation_source R (@freyd_raw_native_snake_cokernel_second_observation R M A B X D a b
  c z)))
≔ @eq_refl (@CommRingPresentation R) (@fapp0 Terminal_cat (@CommRingFreydPresentation_cat R)
  (@cokernel_adjunction_family_func Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@transf_arrow_diagram_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) Terminal_obj);
