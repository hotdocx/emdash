/* Exactness at Q(α) for the original Im(∂)⇒K(q₁) comparison. */
require open emdash.emdash3_2_one_cat_native_snake_third_representatives;
require open emdash.emdash3_2_one_cat_inverse_from_universal_zeros;

// The original third comparison and its source-image map reconstruct ∂ under μ.
symbol one_cat_native_snake_third_comparison_source_path [K C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
    Prod t Add) T0 P Q))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t (@additive_terminal_object C Prod t Add) A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat
  C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add)
  T0 P Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))))) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D b c h))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h) (@one_cat_image_family_source_transf K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h))) (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h))) (λ v : τ (@Transf K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C)
  C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0
  P Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h))), (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) v (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))))) _ _ (@one_cat_image_kernel_ambient_inclusion_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h) N)) (@eq_trans _ _ _ _ (@one_cat_image_family_source_factor_path K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@one_cat_kernel_family_input_source_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cokernel_connecting_zero K C C1 Prod t Add T0 P Q N A B X D b c h)))));

// Original kernel cancellation factors rs through the actual ε₃ using the original connecting representative.
symbol one_cat_native_snake_third_comparison_covers_path [K C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
    Prod t Add) T0 P Q))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t (@additive_terminal_object C Prod t Add) A B X D b c))
  : τ (@= (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat
  C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add)
  T0 P Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@one_cat_native_snake_third_connecting_representative K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_cover_projection K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat
  C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add)
  T0 P Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@one_cat_native_snake_third_connecting_representative K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_cover_projection K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0
  P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))) (@Transf K C
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h))) (λ v : τ (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C
  C1 Prod t Add T0 P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) v))
  _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h) (@one_cat_image_family_source_transf K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@one_cat_native_snake_third_connecting_representative K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod
  t Add T0 P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h) (@one_cat_image_family_source_transf K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h)))) (@one_cat_native_snake_third_connecting_representative K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h))) (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod
  t Add T0 P Q N A B X D b c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0
  Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))), (@comp_fapp0 (Functor_cat K
  C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) v
  (@one_cat_native_snake_third_connecting_representative K C C1 Prod t Add T0 P Q N A B X D b c h))) _ _
  (@one_cat_native_snake_third_comparison_source_path K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_third_connecting_representative_path K C C1 Prod t Add T0 P Q N A B X D b c h)))));

// The original Q-unit and derived b-image cover cancellation give π_ε₃r=0.
symbol one_cat_native_snake_third_cokernel_after_cover_zero [K C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
    Prod t Add) T0 P Q))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t (@additive_terminal_object C Prod t Add) A B X D b c))
  : τ (@= (@Transf K C (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h)))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0
  Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) (@one_cat_native_snake_third_cover_projection K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h)))))
≔ (@one_cat_native_snake_third_middle_cover_reflect_path K C C1 Prod t Add T0 P Q N A B X D b c h
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0
  Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) (@one_cat_native_snake_third_cover_projection K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h)))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0
  Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) (@one_cat_native_snake_third_cover_projection K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)))) (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1
  Prod t Add T0 P Q N A B X D b c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h)))) (λ v : τ (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0
  P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0
  Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) v)) _ _ (@eq_sym _ _ _ (@one_cat_native_snake_third_comparison_covers_path K C C1 Prod t Add
  T0 P Q N A B X D b c h))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h))) (@cokernel_adjunction_family_projection_transf K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h))) (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0
  P Q N A B X D b c h) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1
  Prod t Add T0 P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@one_cat_native_snake_third_connecting_representative K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h)))) (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C
  C1 Prod t Add T0 P Q N A B X D b c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h)))) (λ v : τ (@Transf K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h)))), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q)
  (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) v (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod
  t Add T0 P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@one_cat_native_snake_third_connecting_representative K C C1 Prod t Add T0 P Q N A B X D b c h))))
  _ _ (@one_cat_cokernel_family_annihilation_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h)))) (@eq_trans _ _ _ _ (@one_cat_zero_family_precompose_path K C C1 t
  (@additive_terminal_object C Prod t Add) T0 (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add
  T0 P Q N A B X D b c h) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q)
  (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat
  C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add)
  T0 P Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@one_cat_native_snake_third_connecting_representative K C C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_sym _
  _ _ (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h))) (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add
  T0 P Q N A B X D b c h)))))))));

// Cancellation through the original first cover gives the actual π_ε₃=0.
symbol one_cat_native_snake_third_comparison_cokernel_zero [K C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
    Prod t Add) T0 P Q))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t (@additive_terminal_object C Prod t Add) A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h)))) (@cokernel_adjunction_family_projection_transf K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h))) (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C
  Prod t Add) T0 (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h)))))
≔ (@one_cat_native_snake_third_cover_reflect_path K C C1 Prod t Add T0 P Q N A B X D b c h
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h))) (@cokernel_adjunction_family_projection_transf K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h))) (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C
  Prod t Add) T0 (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison
  K C C1 Prod t Add T0 P Q N A B X D b c h)))) (@eq_trans _ _ _ _
  (@one_cat_native_snake_third_cokernel_after_cover_zero K C C1 Prod t Add T0 P Q N A B X D b c h) (@eq_sym _ _
  _ (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) (@one_cat_native_snake_third_cover_projection K C C1 Prod t Add T0 P Q N A B X D b c h)))));

// Both original zero projections give ΩAlong on the actual third comparison.
symbol one_cat_native_snake_third_exact [K C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
    Prod t Add) T0 P Q))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t (@additive_terminal_object C Prod t Add) A B X D b c))
  : τ (@OneCatNativeSnakeThirdExactness K C C1 Prod t Add T0 P Q N A B X D b c h)
≔ (@one_cat_zero_kernel_cokernel_omega K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h)) N (@one_cat_native_snake_third_comparison_kernel_zero K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@one_cat_native_snake_third_comparison_cokernel_zero K C C1 Prod t Add T0 P Q N A B X D b c h));
