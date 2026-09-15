/* Four whole adjacent-zero proofs and the actual lift into the original cover. */
require open emdash.emdash3_2_one_cat_native_snake_outer_zeros;
require open emdash.emdash3_2_one_cat_native_snake_inner_zeros;

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  ⊢ @one_cat_native_snake_kernel_pair_zero K C S C1 t T T0 P Q A B X D b c h
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_alpha_diagram K C S C1
    t T T0 P A B X D b c h)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K
    C S C1 t T T0 Q A B X D b c h))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
    (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) (@kernel_adjunction_family_func K C S
    t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
    (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second
    K C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_kernel_first K C S C1 t T T0 P Q A B X D b c h))
    (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
    (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))));

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  ⊢ @one_cat_native_snake_cokernel_pair_zero K C S C1 t T T0 P Q A B X D b c h
  : τ (@= (@Transf K C (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S
    C1 t T T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C S t T0 Q
    (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
    (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X
    D b c h)) (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C B X b))
    (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
    D b c h)) (@one_cat_native_snake_cokernel_second K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_cokernel_first K C S C1 t T T0 P Q A B X D b c h)) (@zero_arrow_family_zero_transf K
    C t T T0 (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0
    P A B X D b c h)) (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S
    C1 t T T0 Q A B X D b c h))));

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  ⊢ @one_cat_native_snake_middle_cover_second_path K C S C1 t T T0 P Q A B X D b c h
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c
    h) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
    D b c h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_middle_cover_lift K C S C1 t T T0 P Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h));

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  ⊢ @one_cat_native_snake_middle_theta_zero K C S C1 t T T0 P Q A B X D b c h
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X
    D b c h))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c
    h) (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B
    X D b c h)) (@one_cat_native_snake_covered_transf K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_middle_cover_lift K C S C1 t T T0 P Q A B X D b c h)) (@zero_arrow_family_zero_transf
    K C t T T0 (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X
    D b c h))));

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
  ⊢ @one_cat_native_snake_connecting_kernel_zero K C C1 Prod t Add T0 P Q N A B X D b c h
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C
    C1 Prod t Add T0 P Q N A B X D b c h) (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod
    t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@zero_arrow_family_zero_transf
    K C t (@additive_terminal_object C Prod t Add) T0 (@kernel_adjunction_family_func K C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))));

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
  ⊢ @one_cat_native_snake_cokernel_connecting_zero K C C1 Prod t Add T0 P Q N A B X D b c h
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
    Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@transf_arrow_diagram_func K C B X b))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
    C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C
    Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
    (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D b c h))
    (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))));
