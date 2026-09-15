/* Four original native exactness comparisons and proofs on the raw Freyd snake input. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_snake_inputs;
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_normality;

require open emdash.emdash3_2_one_cat_native_snake_first_exactness;
require open emdash.emdash3_2_one_cat_native_snake_second_exactness;
require open emdash.emdash3_2_one_cat_native_snake_third_exactness;
require open emdash.emdash3_2_one_cat_native_snake_fourth_exactness;

symbol freyd_native_snake_first_exact_comparison [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
≔ (@one_cat_native_snake_first_exact_comparison Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z));

symbol FreydNativeSnakeFirstExactness [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D)))) : Grpd
≔ @OmegaEquivAlong (Functor_cat Terminal_cat (@CommRingFreydPresentation_cat R)) _ _
  (@freyd_native_snake_first_exact_comparison R M N A B X D a b c z);

symbol freyd_native_snake_first_exact_evidence [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (@FreydNativeSnakeFirstExactness R M N A B X D a b c z)
≔ (@one_cat_native_snake_first_exact Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z));

symbol freyd_native_snake_second_exact_comparison [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
≔ (@one_cat_native_snake_second_exact_comparison Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z));

symbol FreydNativeSnakeSecondExactness [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D)))) : Grpd
≔ @OmegaEquivAlong (Functor_cat Terminal_cat (@CommRingFreydPresentation_cat R)) _ _
  (@freyd_native_snake_second_exact_comparison R M N A B X D a b c z);

symbol freyd_native_snake_second_exact_evidence [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (@FreydNativeSnakeSecondExactness R M N A B X D a b c z)
≔ (@one_cat_native_snake_second_exact Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z));

symbol freyd_native_snake_third_exact_comparison [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
≔ (@one_cat_native_snake_third_exact_comparison Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z));

symbol FreydNativeSnakeThirdExactness [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D)))) : Grpd
≔ @OmegaEquivAlong (Functor_cat Terminal_cat (@CommRingFreydPresentation_cat R)) _ _
  (@freyd_native_snake_third_exact_comparison R M N A B X D a b c z);

symbol freyd_native_snake_third_exact_evidence [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (@FreydNativeSnakeThirdExactness R M N A B X D a b c z)
≔ (@one_cat_native_snake_third_exact Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z));

symbol freyd_native_snake_fourth_exact_comparison [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
≔ (@one_cat_native_snake_fourth_exact_comparison Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z));

symbol FreydNativeSnakeFourthExactness [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D)))) : Grpd
≔ @OmegaEquivAlong (Functor_cat Terminal_cat (@CommRingFreydPresentation_cat R)) _ _
  (@freyd_native_snake_fourth_exact_comparison R M N A B X D a b c z);

symbol freyd_native_snake_fourth_exact_evidence [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (@FreydNativeSnakeFourthExactness R M N A B X D a b c z)
≔ (@one_cat_native_snake_fourth_exact Terminal_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) A)
  (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) B) (@Const_func Terminal_cat
  (@CommRingFreydPresentation_cat R) X) (@Const_func Terminal_cat (@CommRingFreydPresentation_cat R) D)
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) B X (@comm_ring_freyd_hom_class R B X b))
  (@Const_transf Terminal_cat (@CommRingFreydPresentation_cat R) X D (@comm_ring_freyd_hom_class R X D c))
  (@freyd_raw_native_snake_input Terminal_cat R (@freyd_adjunction_model_initial R M) A B X D a b c z));
