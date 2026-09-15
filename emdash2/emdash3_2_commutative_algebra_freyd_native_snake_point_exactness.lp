/* Evaluation of the original whole exactness evidence; no inverse is reselected. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_snake_exactness;
require open emdash.emdash3_2_commutative_algebra_freyd_arrow_equivalence_observations;

symbol freyd_native_snake_first_point_exact_data [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  (u : τ (@FreydNativeSnakeFirstExactness R M N A B X D a b c z)) : τ (FreydOmegaArrowObservation R)
≔ @omega_arrow_data_at Terminal_cat (@CommRingFreydPresentation_cat R)
    (@omega_arrow_data (Functor_cat Terminal_cat (@CommRingFreydPresentation_cat R)) _ _
  (@freyd_native_snake_first_exact_comparison R M N A B X D a b c z) u) Terminal_obj;

symbol freyd_native_snake_second_point_exact_data [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  (u : τ (@FreydNativeSnakeSecondExactness R M N A B X D a b c z)) : τ (FreydOmegaArrowObservation R)
≔ @omega_arrow_data_at Terminal_cat (@CommRingFreydPresentation_cat R)
    (@omega_arrow_data (Functor_cat Terminal_cat (@CommRingFreydPresentation_cat R)) _ _
  (@freyd_native_snake_second_exact_comparison R M N A B X D a b c z) u) Terminal_obj;

symbol freyd_native_snake_third_point_exact_data [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  (u : τ (@FreydNativeSnakeThirdExactness R M N A B X D a b c z)) : τ (FreydOmegaArrowObservation R)
≔ @omega_arrow_data_at Terminal_cat (@CommRingFreydPresentation_cat R)
    (@omega_arrow_data (Functor_cat Terminal_cat (@CommRingFreydPresentation_cat R)) _ _
  (@freyd_native_snake_third_exact_comparison R M N A B X D a b c z) u) Terminal_obj;

symbol freyd_native_snake_fourth_point_exact_data [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  (u : τ (@FreydNativeSnakeFourthExactness R M N A B X D a b c z)) : τ (FreydOmegaArrowObservation R)
≔ @omega_arrow_data_at Terminal_cat (@CommRingFreydPresentation_cat R)
    (@omega_arrow_data (Functor_cat Terminal_cat (@CommRingFreydPresentation_cat R)) _ _
  (@freyd_native_snake_fourth_exact_comparison R M N A B X D a b c z) u) Terminal_obj;
