/* Actual five-arrow projections, reconstruction and native input/Hom action. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_snake_observations;

symbol K : Cat;
symbol i : τ (Obj K);
symbol j : τ (Obj K);
symbol test_map : τ (Hom K i j);
symbol R : τ CommRing;
symbol M : τ (FreydAdjunctionModel R);
symbol N : τ (@FreydAdjunctionModelNormality R M);
symbol A : τ (@CommRingPresentation R);
symbol B : τ (@CommRingPresentation R);
symbol X : τ (@CommRingPresentation R);
symbol D : τ (@CommRingPresentation R);
symbol a : τ (@CommRingPresentationMorphism R A B);
symbol b : τ (@CommRingPresentationMorphism R B X);
symbol c : τ (@CommRingPresentationMorphism R X D);
symbol z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D)));


assert ⊢ sigma_Fst (@freyd_raw_native_snake_kernel_first_observation R M A B X D a b c z) ≡ @fapp0
  Terminal_cat (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M)
  (@one_cat_native_snake_alpha_diagram Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R
  M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))) Terminal_obj;

assert ⊢ sigma_Fst (sigma_Snd (@freyd_raw_native_snake_kernel_first_observation R M A B X D a b c z)) ≡ @fapp0
  Terminal_cat (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R)
  B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) Terminal_obj;

assert ⊢ sigma_Snd (sigma_Snd (@freyd_raw_native_snake_kernel_first_observation R M A B X D a b c z)) ≡
  @tapp0_fapp0 Terminal_cat (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M)
  (@one_cat_native_snake_alpha_diagram Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R
  M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@kernel_adjunction_family_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M)
  (@transf_arrow_diagram_func Terminal_cat (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))))
  Terminal_obj (@one_cat_native_snake_kernel_first Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R
  M) (@freyd_adjunction_model_cokernels R M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z));

assert ⊢ sigma_Fst (@freyd_raw_native_snake_kernel_second_observation R M A B X D a b c z) ≡ @fapp0
  Terminal_cat (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R)
  B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) Terminal_obj;

assert ⊢ sigma_Fst (sigma_Snd (@freyd_raw_native_snake_kernel_second_observation R M A B X D a b c z)) ≡
  @fapp0 Terminal_cat (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M)
  (@one_cat_native_snake_gamma_diagram Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels
  R M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))) Terminal_obj;

assert ⊢ sigma_Snd (sigma_Snd (@freyd_raw_native_snake_kernel_second_observation R M A B X D a b c z)) ≡
  @tapp0_fapp0 Terminal_cat (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R)
  B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))))
  (@kernel_adjunction_family_func Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_kernels R M) (@one_cat_native_snake_gamma_diagram Terminal_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z)))
  Terminal_obj (@one_cat_native_snake_kernel_second Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R
  M) (@freyd_adjunction_model_cokernels R M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z));

assert ⊢ sigma_Fst (@freyd_raw_native_snake_connecting_observation R M N A B X D a b c z) ≡ @fapp0
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
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))) Terminal_obj;

assert ⊢ sigma_Fst (sigma_Snd (@freyd_raw_native_snake_connecting_observation R M N A B X D a b c z)) ≡ @fapp0
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
  (@freyd_adjunction_model_initial R M) A B X D a b c z))) Terminal_obj;

assert ⊢ sigma_Snd (sigma_Snd (@freyd_raw_native_snake_connecting_observation R M N A B X D a b c z)) ≡
  @tapp0_fapp0 Terminal_cat (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func Terminal_cat
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
  (@freyd_adjunction_model_initial R M) A B X D a b c z))) Terminal_obj
  (@one_cat_native_snake_connecting_transf Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z));

assert ⊢ sigma_Fst (@freyd_raw_native_snake_cokernel_first_observation R M A B X D a b c z) ≡ @fapp0
  Terminal_cat (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M)
  (@one_cat_native_snake_alpha_diagram Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R
  M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))) Terminal_obj;

assert ⊢ sigma_Fst (sigma_Snd (@freyd_raw_native_snake_cokernel_first_observation R M A B X D a b c z)) ≡
  @fapp0 Terminal_cat (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M) (@transf_arrow_diagram_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R)
  B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) Terminal_obj;

assert ⊢ sigma_Snd (sigma_Snd (@freyd_raw_native_snake_cokernel_first_observation R M A B X D a b c z)) ≡
  @tapp0_fapp0 Terminal_cat (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M)
  (@one_cat_native_snake_alpha_diagram Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R
  M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@cokernel_adjunction_family_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@transf_arrow_diagram_func Terminal_cat (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))))
  Terminal_obj (@one_cat_native_snake_cokernel_first Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R
  M) (@freyd_adjunction_model_cokernels R M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z));

assert ⊢ sigma_Fst (@freyd_raw_native_snake_cokernel_second_observation R M A B X D a b c z) ≡ @fapp0
  Terminal_cat (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M) (@transf_arrow_diagram_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R)
  B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) Terminal_obj;

assert ⊢ sigma_Fst (sigma_Snd (@freyd_raw_native_snake_cokernel_second_observation R M A B X D a b c z)) ≡
  @fapp0 Terminal_cat (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M)
  (@one_cat_native_snake_gamma_diagram Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels
  R M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z))) Terminal_obj;

assert ⊢ sigma_Snd (sigma_Snd (@freyd_raw_native_snake_cokernel_second_observation R M A B X D a b c z)) ≡
  @tapp0_fapp0 Terminal_cat (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func Terminal_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M) (@transf_arrow_diagram_func
  Terminal_cat (@CommRingFreydPresentation_cat R) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R)
  B) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) X) (@Const_transf Terminal_cat
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))))
  (@cokernel_adjunction_family_func Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@one_cat_native_snake_gamma_diagram Terminal_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z)))
  Terminal_obj (@one_cat_native_snake_cokernel_second Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R
  M) (@freyd_adjunction_model_cokernels R M) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z));

// Reconstruction at an actual point for map 1.
assert ⊢ @eq_ap (@Transf K (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M)
  (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@Const_func K (@CommRingFreydPresentation_cat
  R) B)) (@Hom (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M)
  (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) i) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) B) i)) (λ h, @tapp0_fapp0 K
  (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_kernels R M) (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat
  R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R
  M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B)
  (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf
  K (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) i h) _ _ (@one_cat_native_snake_kernel_first_reconstruction K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z)) : τ (@= (@Hom (@CommRingFreydPresentation_cat R)
  (@fapp0 K (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M)
  (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) i) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) B) i)) (@comp_fapp0 (@CommRingFreydPresentation_cat R)
  (@fapp0 K (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M)
  (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) i) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M)
  (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) i) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) B) i) (@tapp0_fapp0 K
  (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) (@Const_func
  K (@CommRingFreydPresentation_cat R) B) i (@kernel_adjunction_family_inclusion_transf K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b))))) (@tapp0_fapp0 K (@CommRingFreydPresentation_cat R)
  (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M)
  (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@kernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)))) i (@freyd_raw_native_snake_kernel_first_transf K R M A B X D a b c
  z))) (@comp_fapp0 (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M)
  (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) i) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) A) i) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) B) i) (@tapp0_fapp0 K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) i
  (@native_snake_incoming K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) (@tapp0_fapp0 K (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M)
  (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@Const_func K (@CommRingFreydPresentation_cat
  R) A) i (@kernel_adjunction_family_inclusion_transf K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_kernels R M) (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat
  R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R
  M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B)
  (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf
  K (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R M) A B X D a b c z))))));

// Reconstruction at an actual point for map 2.
assert ⊢ @eq_ap (@Transf K (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)))) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat
  R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@native_snake_incoming_diagram K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z)))) (@Hom (@CommRingFreydPresentation_cat R)
  (@fapp0 K (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)))) i) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@native_snake_incoming_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i)) (λ h, @tapp0_fapp0 K (@CommRingFreydPresentation_cat R)
  (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M)
  (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))))
  (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@native_snake_incoming_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i h) _ _ (@one_cat_native_snake_kernel_second_reconstruction K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z)) : τ (@= (@Hom (@CommRingFreydPresentation_cat R)
  (@fapp0 K (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)))) i) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@native_snake_incoming_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i)) (@comp_fapp0 (@CommRingFreydPresentation_cat R) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) i) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_kernels R M) (@one_cat_native_snake_gamma_diagram K (@CommRingFreydPresentation_cat
  R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels
  R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R)
  B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf
  K (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) i) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@native_snake_incoming_diagram K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) i) (@tapp0_fapp0 K
  (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_kernels R M) (@one_cat_native_snake_gamma_diagram K (@CommRingFreydPresentation_cat
  R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels
  R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R)
  B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf
  K (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R M) A B X D a b c z)))
  (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@native_snake_incoming_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i (@kernel_adjunction_family_inclusion_transf K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_kernels R M) (@one_cat_native_snake_gamma_diagram K (@CommRingFreydPresentation_cat
  R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels
  R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R)
  B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf
  K (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R M) A B X D a b c z)))) (@tapp0_fapp0 K
  (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))))
  (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M)
  (@one_cat_native_snake_gamma_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) i (@freyd_raw_native_snake_kernel_second_transf
  K R M A B X D a b c z))) (@comp_fapp0 (@CommRingFreydPresentation_cat R) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) i) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) B) i) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@native_snake_incoming_diagram K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) i) (@tapp0_fapp0 K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) B)
  (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@native_snake_incoming_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i (@cokernel_adjunction_family_projection_transf K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@native_snake_incoming_diagram K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z)))) (@tapp0_fapp0 K
  (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) (@Const_func
  K (@CommRingFreydPresentation_cat R) B) i (@kernel_adjunction_family_inclusion_transf K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)))))));

// Reconstruction at an actual point for map 3.
assert ⊢ @eq_ap (@Transf K (@CommRingFreydPresentation_cat R) (@one_cat_native_snake_cover_source K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z)) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M)
  (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z)))) (@Hom (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@one_cat_native_snake_cover_source K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z)) i) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@one_cat_native_snake_alpha_diagram K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B)
  (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf
  K (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) i)) (λ h,
  @tapp0_fapp0 K (@CommRingFreydPresentation_cat R) (@one_cat_native_snake_cover_source K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z)) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M)
  (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i h) _ _ (@one_cat_native_snake_connecting_reconstruction K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z)) : τ (@= (@Hom (@CommRingFreydPresentation_cat R)
  (@fapp0 K (@CommRingFreydPresentation_cat R) (@one_cat_native_snake_cover_source K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z)) i) (@fapp0 K (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i)) (@comp_fapp0 (@CommRingFreydPresentation_cat R) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@one_cat_native_snake_cover_source K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z)) i) (@fapp0 K (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_kernels R M) (@one_cat_native_snake_gamma_diagram K (@CommRingFreydPresentation_cat
  R) (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) i) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@one_cat_native_snake_alpha_diagram K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B)
  (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf
  K (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) i) (@tapp0_fapp0
  K (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_kernels R M)
  (@one_cat_native_snake_gamma_diagram K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M)
  (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i (@freyd_raw_native_snake_connecting_transf K R M N A B X D a b c z)) (@tapp0_fapp0 K
  (@CommRingFreydPresentation_cat R) (@one_cat_native_snake_cover_source K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z)) (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_kernels R M)
  (@one_cat_native_snake_gamma_diagram K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i (@one_cat_native_snake_cover_transf K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z)))) (@tapp0_fapp0 K (@CommRingFreydPresentation_cat R)
  (@one_cat_native_snake_cover_source K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z)) (@cokernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i (@one_cat_native_snake_covered_transf K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))));

// Reconstruction at an actual point for map 4.
assert ⊢ @eq_ap (@Transf K (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)))) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat
  R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))))) (@Hom
  (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M)
  (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)))) i) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) i)) (λ h,
  @tapp0_fapp0 K (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)))) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat
  R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) i h) _ _
  (@one_cat_native_snake_cokernel_first_reconstruction K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R
  M) (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func
  K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z)) : τ (@= (@Hom (@CommRingFreydPresentation_cat R) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D)
  (@Const_transf K (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)))) i) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) i))
  (@comp_fapp0 (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M)
  (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)))) i) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@one_cat_native_snake_alpha_diagram K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i) (@fapp0 K (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M) (@transf_arrow_diagram_func K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)))) i) (@tapp0_fapp0 K (@CommRingFreydPresentation_cat R)
  (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive
  R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@cokernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M) (@transf_arrow_diagram_func K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)))) i (@freyd_raw_native_snake_cokernel_first_transf K R M A B X D a b c
  z)) (@tapp0_fapp0 K (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)))) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat
  R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@one_cat_native_snake_alpha_diagram K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i (@cokernel_adjunction_family_projection_transf K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@one_cat_native_snake_alpha_diagram K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))))) (@comp_fapp0 (@CommRingFreydPresentation_cat R) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D)
  (@Const_transf K (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)))) i) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) X) i) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) i)
  (@tapp0_fapp0 K (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) X)
  (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) i
  (@cokernel_adjunction_family_projection_transf K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))))
  (@tapp0_fapp0 K (@CommRingFreydPresentation_cat R) (@kernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)))) (@Const_func K (@CommRingFreydPresentation_cat R) X) i
  (@kernel_adjunction_family_inclusion_transf K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D)
  (@Const_transf K (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)))))));

// Reconstruction at an actual point for map 5.
assert ⊢ @eq_ap (@Transf K (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat
  R) X) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive
  R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels
  R M) (@one_cat_native_snake_gamma_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive
  R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z)))) (@Hom (@CommRingFreydPresentation_cat R)
  (@fapp0 K (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) X) i) (@fapp0
  K (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@one_cat_native_snake_gamma_diagram K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i)) (λ h, @tapp0_fapp0 K (@CommRingFreydPresentation_cat R) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@one_cat_native_snake_gamma_diagram K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i h) _ _ (@one_cat_native_snake_cokernel_second_reconstruction K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z)) : τ (@= (@Hom (@CommRingFreydPresentation_cat R)
  (@fapp0 K (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) X) i) (@fapp0
  K (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@one_cat_native_snake_gamma_diagram K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i)) (@comp_fapp0 (@CommRingFreydPresentation_cat R) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) X) i) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) i) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@one_cat_native_snake_gamma_diagram K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i) (@tapp0_fapp0 K (@CommRingFreydPresentation_cat R)
  (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))))
  (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@one_cat_native_snake_gamma_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive
  R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) i
  (@freyd_raw_native_snake_cokernel_second_transf K R M A B X D a b c z)) (@tapp0_fapp0 K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) X)
  (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)))) i
  (@cokernel_adjunction_family_projection_transf K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R)
  (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))))))
  (@comp_fapp0 (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) i) (@fapp0 K (@CommRingFreydPresentation_cat R) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) i) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@one_cat_native_snake_gamma_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive
  R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) i) (@tapp0_fapp0 K
  (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) D)
  (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@one_cat_native_snake_gamma_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive
  R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) i
  (@cokernel_adjunction_family_projection_transf K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@one_cat_native_snake_gamma_diagram K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z)))) (@tapp0_fapp0 K (@CommRingFreydPresentation_cat R) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) i (@Const_transf
  K (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)))));

// Actual component recovery retains the original raw class a.
symbol recovered_at : τ (@= (@CommRingFreydHomSet R A B)
  (@tapp0_fapp0 K (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) A)
  (@Const_func K (@CommRingFreydPresentation_cat R) B) i (@native_snake_incoming K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B)
  (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf
  K (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R M) A B X D a b c z)))
  (@comm_ring_freyd_hom_class R A B a))
≔ @eq_ap (@Transf K (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) A)
  (@Const_func K (@CommRingFreydPresentation_cat R) B)) (@CommRingFreydHomSet R A B)
    (λ h, @tapp0_fapp0 K (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R)
  A) (@Const_func K (@CommRingFreydPresentation_cat R) B) i h) _ _ (@freyd_raw_native_snake_incoming_path K R
  (@freyd_adjunction_model_initial R M) A B X D a b c z);
assert ⊢ @eq_sym _ _ _ recovered_at : τ (@= (@CommRingFreydHomSet R A B)
  (@comm_ring_freyd_hom_class R A B a) (@tapp0_fapp0 K (@CommRingFreydPresentation_cat R) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) i
  (@native_snake_incoming K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))));


assert ⊢ @tapp0_fapp0 WalkingArrow_cat (@CommRingFreydPresentation_cat R) (@fapp0 K (@Functor_cat
  WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@native_snake_incoming_diagram K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B)
  (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf
  K (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R M) A B X D a b c z)) i) (@fapp0 K
  (@Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@native_snake_incoming_diagram K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B)
  (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf
  K (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R M) A B X D a b c z)) j)
  walking_arrow_src (@fapp1_fapp0 K (@Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
  (@native_snake_incoming_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z)) i j test_map) ≡ @id (@CommRingFreydPresentation_cat R) A;

assert ⊢ @tapp0_fapp0 WalkingArrow_cat (@CommRingFreydPresentation_cat R) (@fapp0 K (@Functor_cat
  WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@native_snake_incoming_diagram K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B)
  (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf
  K (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R M) A B X D a b c z)) i) (@fapp0 K
  (@Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@native_snake_incoming_diagram K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B)
  (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf
  K (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R M) A B X D a b c z)) j)
  walking_arrow_tgt (@fapp1_fapp0 K (@Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
  (@native_snake_incoming_diagram K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z)) i j test_map) ≡ @id (@CommRingFreydPresentation_cat R) B;


// Off-diagonal Hom action of the same positive reconstruction.
assert ⊢ @eq_ap (@Transf K (@CommRingFreydPresentation_cat R) (@one_cat_native_snake_cover_source K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z)) (@cokernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M)
  (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z)))) (@Hom (@CommRingFreydPresentation_cat R)
  (@fapp0 K (@CommRingFreydPresentation_cat R) (@one_cat_native_snake_cover_source K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z)) i) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) j))
  (λ h, @tapp1_fapp0 K (@CommRingFreydPresentation_cat R) (@one_cat_native_snake_cover_source K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z)) (@cokernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M)
  (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) i j h test_map) _ _
  (@one_cat_native_snake_connecting_reconstruction K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func
  K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))
  : τ (@= (@Hom (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@one_cat_native_snake_cover_source K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z)) i) (@fapp0 K (@CommRingFreydPresentation_cat R) (@cokernel_adjunction_family_func K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R M)
  (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) j)) (@tapp1_fapp0 K
  (@CommRingFreydPresentation_cat R) (@one_cat_native_snake_cover_source K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R
  M) (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func
  K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z)) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R)
  (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@one_cat_native_snake_alpha_diagram K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i j (@comp_fapp0 (@Functor_cat K (@CommRingFreydPresentation_cat R))
  (@one_cat_native_snake_cover_source K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z)) (@kernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_kernels R M) (@one_cat_native_snake_gamma_diagram K (@CommRingFreydPresentation_cat
  R) (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels
  R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R)
  B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D)
  (@Const_transf K (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf
  K (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R M) A B X D a b c z)))
  (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_cokernels R
  M) (@one_cat_native_snake_alpha_diagram K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@Const_func K
  (@CommRingFreydPresentation_cat R) A) (@Const_func K (@CommRingFreydPresentation_cat R) B) (@Const_func K
  (@CommRingFreydPresentation_cat R) X) (@Const_func K (@CommRingFreydPresentation_cat R) D) (@Const_transf K
  (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K
  (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input
  K R (@freyd_adjunction_model_initial R M) A B X D a b c z))) (@freyd_raw_native_snake_connecting_transf K R
  M N A B X D a b c z) (@one_cat_native_snake_cover_transf K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R
  M) (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func
  K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) test_map) (@tapp1_fapp0 K (@CommRingFreydPresentation_cat R)
  (@one_cat_native_snake_cover_source K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z)) (@cokernel_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R)
  (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_cokernels R M) (@one_cat_native_snake_alpha_diagram K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z))) i j (@one_cat_native_snake_covered_transf K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R
  M) (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func
  K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z)) test_map));
