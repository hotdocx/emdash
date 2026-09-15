/* Original exactness inputs, their two observed arrows and public-pair alignment. */
require open emdash.emdash3_2_one_cat_kernel_input_pair_observations;
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_normality;
require open emdash.emdash3_2_one_cat_native_snake_exact_inputs;
require open emdash.emdash3_2_commutative_algebra_freyd_native_snake_observations;

symbol freyd_native_snake_first_input_pair [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D)))) : τ
  (ArrowPairObservation (@CommRingFreydPresentation_cat R))
≔ (@zero_arrow_family_pair_at Terminal_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@kernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_kernels R M) (@one_cat_native_snake_alpha_diagram Terminal_cat
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
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@transf_arrow_diagram_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))))
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
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@one_cat_native_snake_kernel_second
  Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z)))
  (@one_cat_native_snake_first_exact_input Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))
  Terminal_obj);

symbol freyd_native_snake_first_public_pair [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D)))) : τ
  (ArrowPairObservation (@CommRingFreydPresentation_cat R))
≔ Struct_sigma (@freyd_raw_native_snake_kernel_first_observation R M A B X D a b c z)
  (@freyd_raw_native_snake_kernel_second_observation R M A B X D a b c z);

symbol freyd_native_snake_first_public_pair_path [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (@= (ArrowPairObservation (@CommRingFreydPresentation_cat R)) (@freyd_native_snake_first_input_pair R M
  N A B X D a b c z)
    (@freyd_native_snake_first_public_pair R M N A B X D a b c z))
≔ (@one_cat_kernel_input_pair_path Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@kernel_adjunction_family_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_kernels R M) (@one_cat_native_snake_alpha_diagram Terminal_cat
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
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@kernel_adjunction_family_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))))
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
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@one_cat_native_snake_kernel_first
  Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))
  (@one_cat_native_snake_kernel_second Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input Terminal_cat R
  (@freyd_adjunction_model_initial R M) A B X D a b c z)) (@one_cat_native_snake_kernel_pair_zero Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))
  Terminal_obj);

symbol freyd_native_snake_second_input_pair [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D)))) : τ
  (ArrowPairObservation (@CommRingFreydPresentation_cat R))
≔ (@zero_arrow_family_pair_at Terminal_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@kernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) (@transf_arrow_diagram_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_kernels R M) (@one_cat_native_snake_gamma_diagram Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@cokernel_adjunction_family_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@one_cat_native_snake_alpha_diagram Terminal_cat (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input Terminal_cat R
  (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@one_cat_native_snake_connecting_transf
  Terminal_cat (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z)))
  (@one_cat_native_snake_second_exact_input Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))
  Terminal_obj);

symbol freyd_native_snake_second_public_pair [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D)))) : τ
  (ArrowPairObservation (@CommRingFreydPresentation_cat R))
≔ Struct_sigma (@freyd_raw_native_snake_kernel_second_observation R M A B X D a b c z)
  (@freyd_raw_native_snake_connecting_observation R M N A B X D a b c z);

symbol freyd_native_snake_second_public_pair_path [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (@= (ArrowPairObservation (@CommRingFreydPresentation_cat R)) (@freyd_native_snake_second_input_pair R M
  N A B X D a b c z)
    (@freyd_native_snake_second_public_pair R M N A B X D a b c z))
≔ (@one_cat_kernel_input_pair_path Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@kernel_adjunction_family_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))))
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
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@cokernel_adjunction_family_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@one_cat_native_snake_alpha_diagram Terminal_cat (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input Terminal_cat R
  (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@one_cat_native_snake_kernel_second Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))
  (@one_cat_native_snake_connecting_transf Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))
  (@one_cat_native_snake_connecting_kernel_zero Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))
  Terminal_obj);

symbol freyd_native_snake_third_input_pair [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D)))) : τ
  (ArrowPairObservation (@CommRingFreydPresentation_cat R))
≔ (@zero_arrow_family_pair_at Terminal_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@kernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_kernels R M) (@one_cat_native_snake_gamma_diagram Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@transf_arrow_diagram_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@one_cat_native_snake_alpha_diagram Terminal_cat (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input Terminal_cat R
  (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@cokernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@transf_arrow_diagram_func Terminal_cat (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))))
  (@one_cat_native_snake_cokernel_first Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input Terminal_cat R
  (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@one_cat_native_snake_third_exact_input
  Terminal_cat (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))
  Terminal_obj);

symbol freyd_native_snake_third_public_pair [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D)))) : τ
  (ArrowPairObservation (@CommRingFreydPresentation_cat R))
≔ Struct_sigma (@freyd_raw_native_snake_connecting_observation R M N A B X D a b c z)
  (@freyd_raw_native_snake_cokernel_first_observation R M A B X D a b c z);

symbol freyd_native_snake_third_public_pair_path [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (@= (ArrowPairObservation (@CommRingFreydPresentation_cat R)) (@freyd_native_snake_third_input_pair R M
  N A B X D a b c z)
    (@freyd_native_snake_third_public_pair R M N A B X D a b c z))
≔ (@one_cat_kernel_input_pair_path Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@kernel_adjunction_family_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_kernels R M) (@one_cat_native_snake_gamma_diagram Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@cokernel_adjunction_family_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@one_cat_native_snake_alpha_diagram Terminal_cat (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input Terminal_cat R
  (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@cokernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@transf_arrow_diagram_func Terminal_cat (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))))
  (@one_cat_native_snake_connecting_transf Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))
  (@one_cat_native_snake_cokernel_first Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input Terminal_cat R
  (@freyd_adjunction_model_initial R M) A B X D a b c z)) (@one_cat_native_snake_cokernel_connecting_zero
  Terminal_cat (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))
  Terminal_obj);

symbol freyd_native_snake_fourth_input_pair [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D)))) : τ
  (ArrowPairObservation (@CommRingFreydPresentation_cat R))
≔ (@zero_arrow_family_pair_at Terminal_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@cokernel_adjunction_family_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@one_cat_native_snake_alpha_diagram Terminal_cat (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input Terminal_cat R
  (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@transf_arrow_diagram_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@transf_arrow_diagram_func Terminal_cat (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))))
  (@cokernel_adjunction_family_func Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@one_cat_native_snake_gamma_diagram Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z)))
  (@one_cat_native_snake_cokernel_second Terminal_cat (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z)))
  (@one_cat_native_snake_fourth_exact_input Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))
  Terminal_obj);

symbol freyd_native_snake_fourth_public_pair [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D)))) : τ
  (ArrowPairObservation (@CommRingFreydPresentation_cat R))
≔ Struct_sigma (@freyd_raw_native_snake_cokernel_first_observation R M A B X D a b c z)
  (@freyd_raw_native_snake_cokernel_second_observation R M A B X D a b c z);

symbol freyd_native_snake_fourth_public_pair_path [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (@= (ArrowPairObservation (@CommRingFreydPresentation_cat R)) (@freyd_native_snake_fourth_input_pair R M
  N A B X D a b c z)
    (@freyd_native_snake_fourth_public_pair R M N A B X D a b c z))
≔ (@one_cat_kernel_input_pair_path Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@cokernel_adjunction_family_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@one_cat_native_snake_alpha_diagram Terminal_cat (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input Terminal_cat R
  (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@cokernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@transf_arrow_diagram_func Terminal_cat (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))))
  (@cokernel_adjunction_family_func Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@one_cat_native_snake_gamma_diagram Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z)))
  (@one_cat_native_snake_cokernel_first Terminal_cat (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input Terminal_cat R
  (@freyd_adjunction_model_initial R M) A B X D a b c z)) (@one_cat_native_snake_cokernel_second Terminal_cat
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))
  (@one_cat_native_snake_cokernel_pair_zero Terminal_cat (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))
  Terminal_obj);
