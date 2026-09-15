/* The original whole native snake sequence with exactness on each stored adjacent pair. */
require open emdash.emdash3_2_one_cat_native_exact_arrow_pairs;
require open emdash.emdash3_2_finite_arrow_tails;
require open emdash.emdash3_2_one_cat_native_snake_first_exactness;
require open emdash.emdash3_2_one_cat_native_snake_second_exactness;
require open emdash.emdash3_2_one_cat_native_snake_third_exactness;
require open emdash.emdash3_2_one_cat_native_snake_fourth_exactness;

// Retain the original first native input, incoming reconstruction and exact comparison witness.
symbol one_cat_native_snake_six_term_first_step [K C : Cat]
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
  : τ (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q N (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
≔ (@one_cat_native_exact_arrow_pair_intro K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_kernel_family_input_source_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_kernel_pair_zero K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact K C C1 Prod
  t Add T0 P Q N A B X D b c h));

// Retain the original second native input, incoming reconstruction and exact comparison witness.
symbol one_cat_native_snake_six_term_second_step [K C : Cat]
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
  : τ (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q N (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X
  D b c h))
≔ (@one_cat_native_exact_arrow_pair_intro K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X
  D b c h) (@one_cat_native_snake_second_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_kernel_family_input_source_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_connecting_kernel_zero K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_second_exact K C C1 Prod t Add T0 P Q N A B X D b c h));

// Retain the original third native input, incoming reconstruction and exact comparison witness.
symbol one_cat_native_snake_six_term_third_step [K C : Cat]
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
  : τ (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q N (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P
  Q N A B X D b c h) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
≔ (@one_cat_native_exact_arrow_pair_intro K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P
  Q N A B X D b c h) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_third_exact_input K C C1
  Prod t Add T0 P Q N A B X D b c h) (@one_cat_kernel_family_input_source_path K C C1 t
  (@additive_terminal_object C Prod t Add) T0 (@kernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X
  D b c h) (@one_cat_native_snake_cokernel_connecting_zero K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_third_exact K C C1 Prod t Add T0 P Q N A B X D b c h));

// Retain the original fourth native input, incoming reconstruction and exact comparison witness.
symbol one_cat_native_snake_six_term_fourth_step [K C : Cat]
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
  : τ (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q N (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
≔ (@one_cat_native_exact_arrow_pair_intro K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N (@cokernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_fourth_exact_input K C
  C1 Prod t Add T0 P Q N A B X D b c h) (@one_cat_kernel_family_input_source_path K C C1 t
  (@additive_terminal_object C Prod t Add) T0 (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_cokernel_pair_zero K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_fourth_exact K C C1 Prod t Add T0 P Q N A B X D b c h));

// Existing finite-tail data in Functor(K,C), with native exact annotations.
symbol OneCatNativeSnakeSixTermResult [K C : Cat]
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
  : Grpd
≔ (@FiniteArrowTail (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ (succ zero))))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h));

// The original whole five-arrow snake sequence, with all four actual native exactness witnesses.
symbol one_cat_native_snake_six_term_result [K C : Cat]
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
  : τ (@OneCatNativeSnakeSixTermResult K C C1 Prod t Add T0 P Q N A B X D b c h)
≔ (@finite_arrow_tail_cons (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_first_step K C C1 Prod t Add T0 P Q N A B X D b c h) (@finite_arrow_tail_cons
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C C1
  Prod t Add T0 P Q N A B X D b c h) (@one_cat_native_snake_six_term_second_step K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@finite_arrow_tail_cons (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_third_step K C
  C1 Prod t Add T0 P Q N A B X D b c h) (@finite_arrow_tail_cons (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) zero
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_fourth_step K C C1 Prod t Add T0 P Q N A B X D b c h) (@finite_arrow_tail_nil
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))))));
