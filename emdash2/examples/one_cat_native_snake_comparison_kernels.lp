/* Exactness is the existing Ω predicate on each actual comparison; its kernel inclusion is derived zero.
   No assertion below provides the still-missing cokernel-zero or full exactness evidence. */
require open emdash.emdash3_2_one_cat_native_snake_comparison_kernels;

assert [K C : Cat]
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
  ⊢ (@OneCatNativeSnakeFirstExactness K C C1 Prod t Add T0 P Q N A B X D b c h) ≡ @OmegaEquivAlong (Functor_cat
    K C) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h);

assert [K C : Cat]
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
  ⊢ @one_cat_native_snake_first_comparison_kernel_zero K C C1 Prod t Add T0 P Q N A B X D b c h
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h))) (@comp_cat_fapp0 K
    (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h))))
    (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
    (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0
    P Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C
    C1 Prod t Add T0 P Q N A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h))) (@comp_cat_fapp0 K
    (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))));

assert [K C : Cat]
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
  ⊢ (@OneCatNativeSnakeSecondExactness K C C1 Prod t Add T0 P Q N A B X D b c h) ≡ @OmegaEquivAlong (Functor_cat
    K C) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
    Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C
    C1 Prod t Add T0 P Q N A B X D b c h)) (@one_cat_native_snake_second_exact_input K C C1 Prod t Add T0 P Q N
    A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
    C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
    C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@one_cat_native_snake_second_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h);

assert [K C : Cat]
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
  ⊢ @one_cat_native_snake_second_comparison_kernel_zero K C C1 Prod t Add T0 P Q N A B X D b c h
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
    Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C
    C1 Prod t Add T0 P Q N A B X D b c h)) (@one_cat_native_snake_second_exact_input K C C1 Prod t Add T0 P Q N
    A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
    C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
    C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@one_cat_native_snake_second_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h))) (@comp_cat_fapp0
    K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
    Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C
    C1 Prod t Add T0 P Q N A B X D b c h)) (@one_cat_native_snake_second_exact_input K C C1 Prod t Add T0 P Q N
    A B X D b c h)))) (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
    Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C
    C1 Prod t Add T0 P Q N A B X D b c h)) (@one_cat_native_snake_second_exact_input K C C1 Prod t Add T0 P Q N
    A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
    C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
    C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@one_cat_native_snake_second_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
    (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0
    P Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
    C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D b c h))
    (@one_cat_native_snake_second_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C
    C1 Prod t Add T0 P Q N A B X D b c h))) (@one_cat_native_snake_second_exact_comparison K C C1 Prod t Add T0
    P Q N A B X D b c h))) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q)
    (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
    C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D b c h))
    (@one_cat_native_snake_second_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))));

assert [K C : Cat]
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
  ⊢ (@OneCatNativeSnakeThirdExactness K C C1 Prod t Add T0 P Q N A B X D b c h) ≡ @OmegaEquivAlong (Functor_cat
    K C) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
    (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C
    C1 Prod t Add T0 P Q N A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
    (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h);

assert [K C : Cat]
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
  ⊢ @one_cat_native_snake_third_comparison_kernel_zero K C C1 Prod t Add T0 P Q N A B X D b c h
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
    (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C
    C1 Prod t Add T0 P Q N A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
    (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h))) (@comp_cat_fapp0 K
    (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
    (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C
    C1 Prod t Add T0 P Q N A B X D b c h)))) (@kernel_adjunction_family_inclusion_transf K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
    (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0
    P Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
    (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C
    C1 Prod t Add T0 P Q N A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
    (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
    (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0
    P Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@transf_arrow_diagram_func K C
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
    (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C
    C1 Prod t Add T0 P Q N A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
    (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_third_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h))) (@comp_cat_fapp0 K
    (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
    (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_third_exact_input K C
    C1 Prod t Add T0 P Q N A B X D b c h)))));

assert [K C : Cat]
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
  ⊢ (@OneCatNativeSnakeFourthExactness K C C1 Prod t Add T0 P Q N A B X D b c h) ≡ @OmegaEquivAlong (Functor_cat
    K C) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
    t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
    t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cokernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_fourth_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
    t Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive
    C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_fourth_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h);

assert [K C : Cat]
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
  ⊢ @one_cat_native_snake_fourth_comparison_kernel_zero K C C1 Prod t Add T0 P Q N A B X D b c h
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
    t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
    t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cokernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_fourth_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
    t Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive
    C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_fourth_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h))) (@comp_cat_fapp0
    K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
    t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
    t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cokernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_fourth_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h))))
    (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
    t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
    t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cokernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_fourth_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
    t Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive
    C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_fourth_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
    (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0
    P Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
    t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cokernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_fourth_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
    t Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive
    C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_fourth_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h))) (@comp_cat_fapp0
    K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
    t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
    t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cokernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_fourth_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))));
