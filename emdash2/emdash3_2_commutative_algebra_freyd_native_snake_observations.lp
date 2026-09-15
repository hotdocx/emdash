/* Complete-arrow observations of the five actual whole native snake maps. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_snake_maps;
require open emdash.emdash3_2_commutative_algebra_freyd_arrow_observations;

symbol freyd_raw_native_snake_kernel_first_observation [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (FreydArrowObservation R)
≔ @lax_edge (@CommRingFreydPresentation_cat R) _ _ (@tapp0_fapp0 Terminal_cat (@CommRingFreydPresentation_cat
  R) _ _ Terminal_obj (@freyd_raw_native_snake_kernel_first_transf Terminal_cat R M A B X D a b c z));

symbol freyd_raw_native_snake_kernel_second_observation [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (FreydArrowObservation R)
≔ @lax_edge (@CommRingFreydPresentation_cat R) _ _ (@tapp0_fapp0 Terminal_cat (@CommRingFreydPresentation_cat
  R) _ _ Terminal_obj (@freyd_raw_native_snake_kernel_second_transf Terminal_cat R M A B X D a b c z));

symbol freyd_raw_native_snake_connecting_observation [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (FreydArrowObservation R)
≔ @lax_edge (@CommRingFreydPresentation_cat R) _ _ (@tapp0_fapp0 Terminal_cat (@CommRingFreydPresentation_cat
  R) _ _ Terminal_obj (@freyd_raw_native_snake_connecting_transf Terminal_cat R M N A B X D a b c z));

symbol freyd_raw_native_snake_cokernel_first_observation [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (FreydArrowObservation R)
≔ @lax_edge (@CommRingFreydPresentation_cat R) _ _ (@tapp0_fapp0 Terminal_cat (@CommRingFreydPresentation_cat
  R) _ _ Terminal_obj (@freyd_raw_native_snake_cokernel_first_transf Terminal_cat R M A B X D a b c z));

symbol freyd_raw_native_snake_cokernel_second_observation [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (FreydArrowObservation R)
≔ @lax_edge (@CommRingFreydPresentation_cat R) _ _ (@tapp0_fapp0 Terminal_cat (@CommRingFreydPresentation_cat
  R) _ _ Terminal_obj (@freyd_raw_native_snake_cokernel_second_transf Terminal_cat R M A B X D a b c z));
