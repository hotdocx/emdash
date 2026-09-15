/* Raw matrix agreements feed whole native snake input; no universal data is selected. */
require open emdash.emdash3_2_one_cat_constant_snake_inputs;
require open emdash.emdash3_2_commutative_algebra_freyd_zero_cones;
require open emdash.emdash3_2_commutative_algebra_freyd_preadditive;

symbol freyd_raw_snake_zero_path [R : τ CommRing]
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (@= (@CommRingFreydHomSet R A D)
    (@comp_fapp0 (@CommRingFreydPresentation_cat R) A X D (@comm_ring_freyd_hom_class R X D c) (@comp_fapp0
  (@CommRingFreydPresentation_cat R) A B X (@comm_ring_freyd_hom_class R B X b) (@comm_ring_freyd_hom_class R
  A B a)))
    (@comm_ring_freyd_zero_class R A D))
≔ @eq_trans _ _ _ _
    (@eq_ap (@CommRingFreydHomSet R A X) (@CommRingFreydHomSet R A D)
      (λ u, @comp_fapp0 (@CommRingFreydPresentation_cat R) A X D (@comm_ring_freyd_hom_class R X D c) u) _ _
      (@comm_ring_freyd_comp_usability_path R A B X (@comm_ring_freyd_hom_class R B X b)
  (@comm_ring_freyd_hom_class R A B a)))
    (@eq_trans _ _ _ _
      (@comm_ring_freyd_comp_usability_path R A X D (@comm_ring_freyd_hom_class R X D c)
  (@comm_ring_freyd_hom_class R A X (@comm_ring_presentation_morphism_comp R A B X b a)))
      (@comm_ring_freyd_agreement_path R A D (@comm_ring_presentation_morphism_comp R A X D c
  (@comm_ring_presentation_morphism_comp R A B X b a)) (@comm_ring_presentation_morphism_zero R A D) z));

symbol freyd_raw_native_snake_input [K : Cat] [R : τ CommRing]
  (T0 : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R)))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (@NativeSnakeInput K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)))
≔ @one_cat_constant_native_snake_input K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) T0
    A B X D (@comm_ring_freyd_hom_class R A B a) (@comm_ring_freyd_hom_class R B X b)
  (@comm_ring_freyd_hom_class R X D c) (@freyd_raw_snake_zero_path R A B X D a b c z);

symbol freyd_raw_native_snake_incoming_path [K : Cat] [R : τ CommRing]
  (T0 : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R)))
  [A B X D : τ (@CommRingPresentation R)]
  (a : τ (@CommRingPresentationMorphism R A B))
  (b : τ (@CommRingPresentationMorphism R B X))
  (c : τ (@CommRingPresentationMorphism R X D))
  (z : τ (@CommRingPresentationMorphismAgreement R A D (@comm_ring_presentation_morphism_map R A D
  (@comm_ring_presentation_morphism_comp R A X D c (@comm_ring_presentation_morphism_comp R A B X b a)))
  (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_zero R A D))))
  : τ (@= (@Transf K (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) A)
  (@Const_func K (@CommRingFreydPresentation_cat R) B))
    (@native_snake_incoming K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@Const_func K (@CommRingFreydPresentation_cat R) A) (@Const_func K
  (@CommRingFreydPresentation_cat R) B) (@Const_func K (@CommRingFreydPresentation_cat R) X) (@Const_func K
  (@CommRingFreydPresentation_cat R) D) (@Const_transf K (@CommRingFreydPresentation_cat R) B X
  (@comm_ring_freyd_hom_class R B X b)) (@Const_transf K (@CommRingFreydPresentation_cat R) X D
  (@comm_ring_freyd_hom_class R X D c)) (@freyd_raw_native_snake_input K R T0 A B X D a b c z))
    (@Const_transf K (@CommRingFreydPresentation_cat R) A B (@comm_ring_freyd_hom_class R A B a)))
≔ @one_cat_constant_native_snake_incoming_path K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) T0
    A B X D (@comm_ring_freyd_hom_class R A B a) (@comm_ring_freyd_hom_class R B X b)
  (@comm_ring_freyd_hom_class R X D c) (@freyd_raw_snake_zero_path R A B X D a b c z);
