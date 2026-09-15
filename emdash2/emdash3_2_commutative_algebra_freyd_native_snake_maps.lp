/* Five existing native whole snake maps at the original supplied Freyd model. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_snake_inputs;
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_normality;
require open emdash.emdash3_2_one_cat_native_snake_six_term_maps;
require open emdash.emdash3_2_one_cat_native_snake_connecting;

// The result remains a whole transformation over arbitrary K.
symbol freyd_raw_native_snake_kernel_first_transf [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
≔ (@one_cat_native_snake_kernel_first K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z));

// The result remains a whole transformation over arbitrary K.
symbol freyd_raw_native_snake_kernel_second_transf [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
≔ (@one_cat_native_snake_kernel_second K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z));

// The result remains a whole transformation over arbitrary K.
symbol freyd_raw_native_snake_connecting_transf [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
≔ (@one_cat_native_snake_connecting_transf K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func
  K (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z));

// The result remains a whole transformation over arbitrary K.
symbol freyd_raw_native_snake_cokernel_first_transf [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel
  R))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
≔ (@one_cat_native_snake_cokernel_first K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z));

// The result remains a whole transformation over arbitrary K.
symbol freyd_raw_native_snake_cokernel_second_transf [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel
  R))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
≔ (@one_cat_native_snake_cokernel_second K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R (@freyd_adjunction_model_initial R
  M) A B X D a b c z));
