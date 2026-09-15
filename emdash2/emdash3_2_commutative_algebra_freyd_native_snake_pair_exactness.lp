/* Exactness indexed by the pair actually observed from its original native input. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_snake_pairs;
require open emdash.emdash3_2_commutative_algebra_freyd_native_snake_exactness;

symbol FreydNativeSnakeFirstExactAt [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  (edge0 edge1 : τ (FreydArrowObservation R)) : Grpd
≔ @Product_grpd (@FreydNativeSnakeFirstExactness R M N A B X D a b c z) (@= (ArrowPairObservation
  (@CommRingFreydPresentation_cat R)) (@freyd_native_snake_first_input_pair R M N A B X D a b c z)
  (Struct_sigma edge0 edge1));

// Only the observation path is transported; the original Ω witness is retained.
symbol freyd_native_snake_first_exact_at [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  (u : τ (@FreydNativeSnakeFirstExactness R M N A B X D a b c z)) [edge0 edge1 : τ (FreydArrowObservation R)]
  (p : τ (@= (FreydArrowObservation R) (@freyd_raw_native_snake_kernel_first_observation R M A B X D a b c z)
  edge0))
  (q : τ (@= (FreydArrowObservation R) (@freyd_raw_native_snake_kernel_second_observation R M A B X D a b c z)
  edge1))
  : τ (@FreydNativeSnakeFirstExactAt R M N A B X D a b c z edge0 edge1)
≔ Product_pair_grpd u
    (@eq_trans (ArrowPairObservation (@CommRingFreydPresentation_cat R)) (@freyd_native_snake_first_input_pair
  R M N A B X D a b c z) (@freyd_native_snake_first_public_pair R M N A B X D a b c z) (Struct_sigma edge0
  edge1)
      (@freyd_native_snake_first_public_pair_path R M N A B X D a b c z)
      (@arrow_pair_observation_path (@CommRingFreydPresentation_cat R)
  (@freyd_raw_native_snake_kernel_first_observation R M A B X D a b c z)
  (@freyd_raw_native_snake_kernel_second_observation R M A B X D a b c z) edge0 edge1 p q));

symbol FreydNativeSnakeSecondExactAt [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  (edge0 edge1 : τ (FreydArrowObservation R)) : Grpd
≔ @Product_grpd (@FreydNativeSnakeSecondExactness R M N A B X D a b c z) (@= (ArrowPairObservation
  (@CommRingFreydPresentation_cat R)) (@freyd_native_snake_second_input_pair R M N A B X D a b c z)
  (Struct_sigma edge0 edge1));

// Only the observation path is transported; the original Ω witness is retained.
symbol freyd_native_snake_second_exact_at [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  (u : τ (@FreydNativeSnakeSecondExactness R M N A B X D a b c z)) [edge0 edge1 : τ (FreydArrowObservation R)]
  (p : τ (@= (FreydArrowObservation R) (@freyd_raw_native_snake_kernel_second_observation R M A B X D a b c z)
  edge0))
  (q : τ (@= (FreydArrowObservation R) (@freyd_raw_native_snake_connecting_observation R M N A B X D a b c z)
  edge1))
  : τ (@FreydNativeSnakeSecondExactAt R M N A B X D a b c z edge0 edge1)
≔ Product_pair_grpd u
    (@eq_trans (ArrowPairObservation (@CommRingFreydPresentation_cat R))
  (@freyd_native_snake_second_input_pair R M N A B X D a b c z) (@freyd_native_snake_second_public_pair R M N
  A B X D a b c z) (Struct_sigma edge0 edge1)
      (@freyd_native_snake_second_public_pair_path R M N A B X D a b c z)
      (@arrow_pair_observation_path (@CommRingFreydPresentation_cat R)
  (@freyd_raw_native_snake_kernel_second_observation R M A B X D a b c z)
  (@freyd_raw_native_snake_connecting_observation R M N A B X D a b c z) edge0 edge1 p q));

symbol FreydNativeSnakeThirdExactAt [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  (edge0 edge1 : τ (FreydArrowObservation R)) : Grpd
≔ @Product_grpd (@FreydNativeSnakeThirdExactness R M N A B X D a b c z) (@= (ArrowPairObservation
  (@CommRingFreydPresentation_cat R)) (@freyd_native_snake_third_input_pair R M N A B X D a b c z)
  (Struct_sigma edge0 edge1));

// Only the observation path is transported; the original Ω witness is retained.
symbol freyd_native_snake_third_exact_at [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  (u : τ (@FreydNativeSnakeThirdExactness R M N A B X D a b c z)) [edge0 edge1 : τ (FreydArrowObservation R)]
  (p : τ (@= (FreydArrowObservation R) (@freyd_raw_native_snake_connecting_observation R M N A B X D a b c z)
  edge0))
  (q : τ (@= (FreydArrowObservation R) (@freyd_raw_native_snake_cokernel_first_observation R M A B X D a b c
  z) edge1))
  : τ (@FreydNativeSnakeThirdExactAt R M N A B X D a b c z edge0 edge1)
≔ Product_pair_grpd u
    (@eq_trans (ArrowPairObservation (@CommRingFreydPresentation_cat R)) (@freyd_native_snake_third_input_pair
  R M N A B X D a b c z) (@freyd_native_snake_third_public_pair R M N A B X D a b c z) (Struct_sigma edge0
  edge1)
      (@freyd_native_snake_third_public_pair_path R M N A B X D a b c z)
      (@arrow_pair_observation_path (@CommRingFreydPresentation_cat R)
  (@freyd_raw_native_snake_connecting_observation R M N A B X D a b c z)
  (@freyd_raw_native_snake_cokernel_first_observation R M A B X D a b c z) edge0 edge1 p q));

symbol FreydNativeSnakeFourthExactAt [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  (edge0 edge1 : τ (FreydArrowObservation R)) : Grpd
≔ @Product_grpd (@FreydNativeSnakeFourthExactness R M N A B X D a b c z) (@= (ArrowPairObservation
  (@CommRingFreydPresentation_cat R)) (@freyd_native_snake_fourth_input_pair R M N A B X D a b c z)
  (Struct_sigma edge0 edge1));

// Only the observation path is transported; the original Ω witness is retained.
symbol freyd_native_snake_fourth_exact_at [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  (u : τ (@FreydNativeSnakeFourthExactness R M N A B X D a b c z)) [edge0 edge1 : τ (FreydArrowObservation R)]
  (p : τ (@= (FreydArrowObservation R) (@freyd_raw_native_snake_cokernel_first_observation R M A B X D a b c
  z) edge0))
  (q : τ (@= (FreydArrowObservation R) (@freyd_raw_native_snake_cokernel_second_observation R M A B X D a b c
  z) edge1))
  : τ (@FreydNativeSnakeFourthExactAt R M N A B X D a b c z edge0 edge1)
≔ Product_pair_grpd u
    (@eq_trans (ArrowPairObservation (@CommRingFreydPresentation_cat R))
  (@freyd_native_snake_fourth_input_pair R M N A B X D a b c z) (@freyd_native_snake_fourth_public_pair R M N
  A B X D a b c z) (Struct_sigma edge0 edge1)
      (@freyd_native_snake_fourth_public_pair_path R M N A B X D a b c z)
      (@arrow_pair_observation_path (@CommRingFreydPresentation_cat R)
  (@freyd_raw_native_snake_cokernel_first_observation R M A B X D a b c z)
  (@freyd_raw_native_snake_cokernel_second_observation R M A B X D a b c z) edge0 edge1 p q));
