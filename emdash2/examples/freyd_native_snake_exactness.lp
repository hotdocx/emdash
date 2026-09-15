/* Original comparison, derived point evidence and retained inverse data. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_snake_point_exactness;

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

symbol first_data : τ (FreydOmegaArrowObservation R) ≔ (@freyd_native_snake_first_point_exact_data R M N A B X
  D a b c z (@freyd_native_snake_first_exact_evidence R M N A B X D a b c z));
assert ⊢ @freyd_omega_arrow_observation R first_data
  ≡ @lax_edge (@CommRingFreydPresentation_cat R) _ _ (@tapp0_fapp0 Terminal_cat
  (@CommRingFreydPresentation_cat R) _ _ Terminal_obj (@freyd_native_snake_first_exact_comparison R M N A B X
  D a b c z));
assert ⊢ @freyd_omega_arrow_evidence R first_data
  : τ (FreydArrowOmegaEvidence R (@freyd_omega_arrow_observation R first_data));
assert ⊢ @omega_equiv_along_left_inv (@CommRingFreydPresentation_cat R)
  (sigma_Fst (@freyd_omega_arrow_observation R first_data))
  (sigma_Fst (sigma_Snd (@freyd_omega_arrow_observation R first_data)))
  (sigma_Snd (sigma_Snd (@freyd_omega_arrow_observation R first_data)))
  (@freyd_omega_arrow_evidence R first_data)
  : τ (Hom (@CommRingFreydPresentation_cat R) (sigma_Fst (sigma_Snd (@freyd_omega_arrow_observation R
  first_data)))
    (sigma_Fst (@freyd_omega_arrow_observation R first_data)));


symbol second_data : τ (FreydOmegaArrowObservation R) ≔ (@freyd_native_snake_second_point_exact_data R M N A B
  X D a b c z (@freyd_native_snake_second_exact_evidence R M N A B X D a b c z));
assert ⊢ @freyd_omega_arrow_observation R second_data
  ≡ @lax_edge (@CommRingFreydPresentation_cat R) _ _ (@tapp0_fapp0 Terminal_cat
  (@CommRingFreydPresentation_cat R) _ _ Terminal_obj (@freyd_native_snake_second_exact_comparison R M N A B X
  D a b c z));
assert ⊢ @freyd_omega_arrow_evidence R second_data
  : τ (FreydArrowOmegaEvidence R (@freyd_omega_arrow_observation R second_data));
assert ⊢ @omega_equiv_along_left_inv (@CommRingFreydPresentation_cat R)
  (sigma_Fst (@freyd_omega_arrow_observation R second_data))
  (sigma_Fst (sigma_Snd (@freyd_omega_arrow_observation R second_data)))
  (sigma_Snd (sigma_Snd (@freyd_omega_arrow_observation R second_data)))
  (@freyd_omega_arrow_evidence R second_data)
  : τ (Hom (@CommRingFreydPresentation_cat R) (sigma_Fst (sigma_Snd (@freyd_omega_arrow_observation R
  second_data)))
    (sigma_Fst (@freyd_omega_arrow_observation R second_data)));


symbol third_data : τ (FreydOmegaArrowObservation R) ≔ (@freyd_native_snake_third_point_exact_data R M N A B X
  D a b c z (@freyd_native_snake_third_exact_evidence R M N A B X D a b c z));
assert ⊢ @freyd_omega_arrow_observation R third_data
  ≡ @lax_edge (@CommRingFreydPresentation_cat R) _ _ (@tapp0_fapp0 Terminal_cat
  (@CommRingFreydPresentation_cat R) _ _ Terminal_obj (@freyd_native_snake_third_exact_comparison R M N A B X
  D a b c z));
assert ⊢ @freyd_omega_arrow_evidence R third_data
  : τ (FreydArrowOmegaEvidence R (@freyd_omega_arrow_observation R third_data));
assert ⊢ @omega_equiv_along_left_inv (@CommRingFreydPresentation_cat R)
  (sigma_Fst (@freyd_omega_arrow_observation R third_data))
  (sigma_Fst (sigma_Snd (@freyd_omega_arrow_observation R third_data)))
  (sigma_Snd (sigma_Snd (@freyd_omega_arrow_observation R third_data)))
  (@freyd_omega_arrow_evidence R third_data)
  : τ (Hom (@CommRingFreydPresentation_cat R) (sigma_Fst (sigma_Snd (@freyd_omega_arrow_observation R
  third_data)))
    (sigma_Fst (@freyd_omega_arrow_observation R third_data)));


symbol fourth_data : τ (FreydOmegaArrowObservation R) ≔ (@freyd_native_snake_fourth_point_exact_data R M N A B
  X D a b c z (@freyd_native_snake_fourth_exact_evidence R M N A B X D a b c z));
assert ⊢ @freyd_omega_arrow_observation R fourth_data
  ≡ @lax_edge (@CommRingFreydPresentation_cat R) _ _ (@tapp0_fapp0 Terminal_cat
  (@CommRingFreydPresentation_cat R) _ _ Terminal_obj (@freyd_native_snake_fourth_exact_comparison R M N A B X
  D a b c z));
assert ⊢ @freyd_omega_arrow_evidence R fourth_data
  : τ (FreydArrowOmegaEvidence R (@freyd_omega_arrow_observation R fourth_data));
assert ⊢ @omega_equiv_along_left_inv (@CommRingFreydPresentation_cat R)
  (sigma_Fst (@freyd_omega_arrow_observation R fourth_data))
  (sigma_Fst (sigma_Snd (@freyd_omega_arrow_observation R fourth_data)))
  (sigma_Snd (sigma_Snd (@freyd_omega_arrow_observation R fourth_data)))
  (@freyd_omega_arrow_evidence R fourth_data)
  : τ (Hom (@CommRingFreydPresentation_cat R) (sigma_Fst (sigma_Snd (@freyd_omega_arrow_observation R
  fourth_data)))
    (sigma_Fst (@freyd_omega_arrow_observation R fourth_data)));
