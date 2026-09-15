/* Original Ω data remains accessible under opaque model-interpretation paths. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_snake_diagram_exactness;

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





symbol v0 : τ (FreydArrowObservation R);
symbol p0 : τ (@= (FreydArrowObservation R) (@freyd_raw_native_snake_kernel_first_observation R M A B X D a b
  c z) v0);

symbol v1 : τ (FreydArrowObservation R);
symbol p1 : τ (@= (FreydArrowObservation R) (@freyd_raw_native_snake_kernel_second_observation R M A B X D a b
  c z) v1);

symbol v2 : τ (FreydArrowObservation R);
symbol p2 : τ (@= (FreydArrowObservation R) (@freyd_raw_native_snake_connecting_observation R M N A B X D a b
  c z) v2);

symbol v3 : τ (FreydArrowObservation R);
symbol p3 : τ (@= (FreydArrowObservation R) (@freyd_raw_native_snake_cokernel_first_observation R M A B X D a
  b c z) v3);

symbol v4 : τ (FreydArrowObservation R);
symbol p4 : τ (@= (FreydArrowObservation R) (@freyd_raw_native_snake_cokernel_second_observation R M A B X D a
  b c z) v4);

symbol e0 : τ (@FreydNativeSnakeFirstExactAt R M N A B X D a b c z v0 v1) ≔
  (@freyd_native_snake_first_exact_at R M N A B X D a b c z (@freyd_native_snake_first_exact_evidence R M N A
  B X D a b c z) v0 v1 p0 p1);
assert ⊢ sigma_Fst e0 ≡ (@freyd_native_snake_first_exact_evidence R M N A B X D a b c z);
assert ⊢ sigma_Snd e0 : τ (@= (ArrowPairObservation (@CommRingFreydPresentation_cat R))
  (@freyd_native_snake_first_input_pair R M N A B X D a b c z) (Struct_sigma v0 v1));


symbol e1 : τ (@FreydNativeSnakeSecondExactAt R M N A B X D a b c z v1 v2) ≔
  (@freyd_native_snake_second_exact_at R M N A B X D a b c z (@freyd_native_snake_second_exact_evidence R M N
  A B X D a b c z) v1 v2 p1 p2);
assert ⊢ sigma_Fst e1 ≡ (@freyd_native_snake_second_exact_evidence R M N A B X D a b c z);
assert ⊢ sigma_Snd e1 : τ (@= (ArrowPairObservation (@CommRingFreydPresentation_cat R))
  (@freyd_native_snake_second_input_pair R M N A B X D a b c z) (Struct_sigma v1 v2));


symbol e2 : τ (@FreydNativeSnakeThirdExactAt R M N A B X D a b c z v2 v3) ≔
  (@freyd_native_snake_third_exact_at R M N A B X D a b c z (@freyd_native_snake_third_exact_evidence R M N A
  B X D a b c z) v2 v3 p2 p3);
assert ⊢ sigma_Fst e2 ≡ (@freyd_native_snake_third_exact_evidence R M N A B X D a b c z);
assert ⊢ sigma_Snd e2 : τ (@= (ArrowPairObservation (@CommRingFreydPresentation_cat R))
  (@freyd_native_snake_third_input_pair R M N A B X D a b c z) (Struct_sigma v2 v3));


symbol e3 : τ (@FreydNativeSnakeFourthExactAt R M N A B X D a b c z v3 v4) ≔
  (@freyd_native_snake_fourth_exact_at R M N A B X D a b c z (@freyd_native_snake_fourth_exact_evidence R M N
  A B X D a b c z) v3 v4 p3 p4);
assert ⊢ sigma_Fst e3 ≡ (@freyd_native_snake_fourth_exact_evidence R M N A B X D a b c z);
assert ⊢ sigma_Snd e3 : τ (@= (ArrowPairObservation (@CommRingFreydPresentation_cat R))
  (@freyd_native_snake_fourth_input_pair R M N A B X D a b c z) (Struct_sigma v3 v4));


symbol matching : τ (@FreydArrowMatchingTail R v0 (succ (succ (succ (succ zero)))) (@finite_family_cons
  (FreydArrowObservation R) (succ (succ (succ zero))) v1 (@finite_family_cons (FreydArrowObservation R) (succ
  (succ zero)) v2 (@finite_family_cons (FreydArrowObservation R) (succ zero) v3 (@finite_family_cons
  (FreydArrowObservation R) zero v4 (@finite_family_nil (FreydArrowObservation R)))))));
symbol displayed : τ (@FreydNativeSnakeDiagramExactness R M N A B X D a b c z (@freyd_arrow_diagram_intro R
  (succ (succ (succ (succ zero)))) v0 (@finite_family_cons (FreydArrowObservation R) (succ (succ (succ zero)))
  v1 (@finite_family_cons (FreydArrowObservation R) (succ (succ zero)) v2 (@finite_family_cons
  (FreydArrowObservation R) (succ zero) v3 (@finite_family_cons (FreydArrowObservation R) zero v4
  (@finite_family_nil (FreydArrowObservation R)))))) matching))
≔ (@freyd_native_snake_exact_diagram_intro R M N A B X D a b c z v0 v1 v2 v3 v4 matching e0 e1 e2 e3);
assert ⊢ sigma_Fst displayed ≡ e0;
assert ⊢ sigma_Snd (sigma_Snd displayed) ≡ Product_pair_grpd e2 e3;
