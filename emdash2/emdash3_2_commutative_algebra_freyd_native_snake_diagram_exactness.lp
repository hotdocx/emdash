/* A single native exactness certificate indexed by the displayed five-arrow diagram. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_snake_pair_exactness;
require open emdash.emdash3_2_commutative_algebra_freyd_diagram_observations;

symbol FreydNativeSnakeDiagramExactness [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  (d : τ (FreydArrowObservationDiagram R (succ (succ (succ (succ zero)))))) : Grpd
≔ (@Product_grpd (@FreydNativeSnakeFirstExactAt R M N A B X D a b c z (@finite_family_head
  (FreydArrowObservation R) (succ (succ (succ (succ zero)))) (@freyd_arrow_diagram_arrows R (succ (succ (succ
  (succ zero)))) d)) (@finite_family_head (FreydArrowObservation R) (succ (succ (succ zero)))
  (@finite_family_tail (FreydArrowObservation R) (succ (succ (succ (succ zero)))) (@freyd_arrow_diagram_arrows
  R (succ (succ (succ (succ zero)))) d)))) (@Product_grpd (@FreydNativeSnakeSecondExactAt R M N A B X D a b c
  z (@finite_family_head (FreydArrowObservation R) (succ (succ (succ zero))) (@finite_family_tail
  (FreydArrowObservation R) (succ (succ (succ (succ zero)))) (@freyd_arrow_diagram_arrows R (succ (succ (succ
  (succ zero)))) d))) (@finite_family_head (FreydArrowObservation R) (succ (succ zero)) (@finite_family_tail
  (FreydArrowObservation R) (succ (succ (succ zero))) (@finite_family_tail (FreydArrowObservation R) (succ
  (succ (succ (succ zero)))) (@freyd_arrow_diagram_arrows R (succ (succ (succ (succ zero)))) d)))))
  (@Product_grpd (@FreydNativeSnakeThirdExactAt R M N A B X D a b c z (@finite_family_head
  (FreydArrowObservation R) (succ (succ zero)) (@finite_family_tail (FreydArrowObservation R) (succ (succ
  (succ zero))) (@finite_family_tail (FreydArrowObservation R) (succ (succ (succ (succ zero))))
  (@freyd_arrow_diagram_arrows R (succ (succ (succ (succ zero)))) d)))) (@finite_family_head
  (FreydArrowObservation R) (succ zero) (@finite_family_tail (FreydArrowObservation R) (succ (succ zero))
  (@finite_family_tail (FreydArrowObservation R) (succ (succ (succ zero))) (@finite_family_tail
  (FreydArrowObservation R) (succ (succ (succ (succ zero)))) (@freyd_arrow_diagram_arrows R (succ (succ (succ
  (succ zero)))) d)))))) (@FreydNativeSnakeFourthExactAt R M N A B X D a b c z (@finite_family_head
  (FreydArrowObservation R) (succ zero) (@finite_family_tail (FreydArrowObservation R) (succ (succ zero))
  (@finite_family_tail (FreydArrowObservation R) (succ (succ (succ zero))) (@finite_family_tail
  (FreydArrowObservation R) (succ (succ (succ (succ zero)))) (@freyd_arrow_diagram_arrows R (succ (succ (succ
  (succ zero)))) d))))) (@finite_family_head (FreydArrowObservation R) zero (@finite_family_tail
  (FreydArrowObservation R) (succ zero) (@finite_family_tail (FreydArrowObservation R) (succ (succ zero))
  (@finite_family_tail (FreydArrowObservation R) (succ (succ (succ zero))) (@finite_family_tail
  (FreydArrowObservation R) (succ (succ (succ (succ zero)))) (@freyd_arrow_diagram_arrows R (succ (succ (succ
  (succ zero)))) d))))))))));

symbol freyd_native_snake_exact_diagram_intro [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  (v0 v1 v2 v3 v4 : τ (FreydArrowObservation R))
  (matching : τ (@FreydArrowMatchingTail R v0 (succ (succ (succ (succ zero)))) (@finite_family_cons
  (FreydArrowObservation R) (succ (succ (succ zero))) v1 (@finite_family_cons (FreydArrowObservation R) (succ
  (succ zero)) v2 (@finite_family_cons (FreydArrowObservation R) (succ zero) v3 (@finite_family_cons
  (FreydArrowObservation R) zero v4 (@finite_family_nil (FreydArrowObservation R))))))))
  (e0 : τ (@FreydNativeSnakeFirstExactAt R M N A B X D a b c z v0 v1))
  (e1 : τ (@FreydNativeSnakeSecondExactAt R M N A B X D a b c z v1 v2))
  (e2 : τ (@FreydNativeSnakeThirdExactAt R M N A B X D a b c z v2 v3))
  (e3 : τ (@FreydNativeSnakeFourthExactAt R M N A B X D a b c z v3 v4))
  : τ (@FreydNativeSnakeDiagramExactness R M N A B X D a b c z (@freyd_arrow_diagram_intro R (succ (succ (succ
  (succ zero)))) v0 (@finite_family_cons (FreydArrowObservation R) (succ (succ (succ zero))) v1
  (@finite_family_cons (FreydArrowObservation R) (succ (succ zero)) v2 (@finite_family_cons
  (FreydArrowObservation R) (succ zero) v3 (@finite_family_cons (FreydArrowObservation R) zero v4
  (@finite_family_nil (FreydArrowObservation R)))))) matching))
≔ (@Product_pair_grpd _ _ e0 (@Product_pair_grpd _ _ e1 (@Product_pair_grpd _ _ e2 e3)));
